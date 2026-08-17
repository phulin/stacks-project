import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Opposite
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Defs

/-!
# Brauer groups, Chapter 2: Noncommutative algebras

The source introduces the usual conventions for algebras, right modules,
finite-dimensional algebras, skew fields, simple objects, central algebras,
and opposite algebras.  These notions already have canonical Mathlib
interfaces, so this file uses source-facing abbreviations only where they
make the conventions explicit; the underlying structures and predicates are
not duplicated.
-/

namespace Formalization.Books.Brauer.Unit02

noncomputable section

universe u v

/-! ## Conventions -/

/- A Mathlib `Algebra k A` is a ring homomorphism whose image commutes with
   `A` and which preserves one, exactly as in the source's convention. -/

theorem algebra_map_scalar_is_central
    (k A : Type*) [Field k] [Ring A] [Algebra k A]
    (r : k) (a : A) :
    algebraMap k A r * a = a * algebraMap k A r := by
  simpa using Algebra.commutes r a

/- The source uses right modules.  In Mathlib these are modules over the
   multiplicative opposite, and `Module` supplies the identity-action law. -/

/-- The source's right `A`-module convention, represented by `Aᵐᵒᵖ`-modules. -/
abbrev RightModule (A M : Type*) [Ring A] [AddCommGroup M] :=
  Module Aᵐᵒᵖ M

/-! ## Finite algebras -/

/- `FiniteDimensional` is Mathlib's canonical finite-dimensionality class;
   its definition is `Module.Finite`. -/

/-- The source's finite `k`-algebras, using Mathlib's canonical class. -/
abbrev FiniteAlgebra (k A : Type*) [Field k] [Ring A] [Algebra k A] :=
  FiniteDimensional k A

/- The source writes `[A : k]` for the dimension in the finite case.  The
   natural-number value used by Mathlib for this finite dimension is
   `Module.finrank`. -/

/-- The finite degree of a `k`-algebra, corresponding to `[A : k]`. -/
def algebraDegree (k A : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteAlgebra k A] : ℕ :=
  Module.finrank k A

/- The cardinal-valued rank records the source's condition `dimₖ A < ∞`
   without relying on the finite-dimensional class in the statement. -/

theorem finite_algebra_iff_dimension_lt_aleph0
    (k A : Type*) [Field k] [Ring A] [Algebra k A] :
    FiniteAlgebra k A ↔ Module.rank k A < Cardinal.aleph0 := by
  change Module.Finite k A ↔ Module.rank k A < Cardinal.aleph0
  exact (Module.rank_lt_aleph0_iff (R := k) (M := A)).symm

/-! ## Skew fields -/

/- Mathlib's `DivisionRing` is precisely a possibly noncommutative ring with
   one, nontriviality, and inverses for all nonzero elements. -/

/-- The source's skew fields, represented by Mathlib's `DivisionRing`. -/
abbrev SkewField (D : Type*) := DivisionRing D

/- Every division ring contains a prime field.  The source only needs the
   resulting existence of some field of scalars; the dependent choice of the
   characteristic-zero field `ℚ` or the prime-characteristic field `ZMod p`
   is recorded by this interface.  The instance field packages the dependent
   typeclass data that an existential statement about a field of scalars needs. -/

/-- A field and an algebra structure on a skew field, with the base field
chosen as dependent data. -/
structure FieldAlgebraWitness (D : Type*) [SkewField D] where
  k : Type
  [field : Field k]
  algebra : Algebra k D

/-- A skew field is an algebra over some field of scalars. -/
theorem skewField_is_algebra_over_some_field
    (D : Type*) [SkewField D] :
    Nonempty (FieldAlgebraWitness D) := by
  rcases CharP.char_is_prime_or_zero D (ringChar D) with hp | hp
  · let hprime : Fact (ringChar D).Prime := ⟨hp⟩
    exact ⟨@FieldAlgebraWitness.mk D _ (ZMod (ringChar D))
      (@ZMod.instField (ringChar D) hprime)
      (@ZMod.algebra D _ (ringChar D) (ringChar.charP D))⟩
  · let hchar : CharZero D := (CharP.ringChar_zero_iff_CharZero D).mp hp
    exact ⟨@FieldAlgebraWitness.mk D _ ℚ inferInstance
      (@DivisionRing.toRatAlgebra D _ hchar)⟩

/- The basis theorem for vector spaces over a division ring is already a
   Mathlib instance, so the source's Zorn-lemma assertion is available
   directly as `Module.Free`. -/

/-- Every left module over a skew field is free. -/
theorem skewField_module_is_free (D M : Type*) [SkewField D]
    [AddCommGroup M] [Module D M] :
    Module.Free D M := by
  infer_instance

/-- Every right module over a skew field is free. -/
theorem skewField_right_module_is_free (D M : Type*) [SkewField D]
    [AddCommGroup M] [RightModule D M] :
    Module.Free Dᵐᵒᵖ M := by
  infer_instance

/-! ## Simple and central algebras -/

/- `IsSimpleModule` uses the simple-order condition on submodules, which is
   equivalent here to being nonzero with only `0` and the whole module. -/

/-- A simple right module over `A`. -/
abbrev SimpleRightModule (A M : Type*) [Ring A] [AddCommGroup M]
    [RightModule A M] :=
  IsSimpleModule Aᵐᵒᵖ M

/- `IsSimpleRing` is the canonical two-sided-ideal predicate. -/

/-- A simple `k`-algebra, using Mathlib's two-sided-ideal predicate. -/
abbrev SimpleAlgebra (k A : Type*) [Field k] [Ring A] [Algebra k A] :=
  IsSimpleRing A

/- `Algebra.IsCentral` says that the center is contained in the bottom
   subalgebra, whose elements are exactly the scalar image. -/

/-- A central `k`-algebra, using Mathlib's canonical centrality class. -/
abbrev CentralAlgebra (k A : Type*) [Field k] [Ring A] [Algebra k A] :=
  Algebra.IsCentral k A

/-! ## Opposite algebras -/

/- The multiplicative opposite is the canonical type synonym reversing
   multiplication.  Mathlib supplies its `k`-algebra structure. -/

/-- The source's opposite `k`-algebra `Aᵒᵖ`, represented by `Aᵐᵒᵖ`. -/
abbrev OppositeAlgebra (k A : Type*) [Field k] [Ring A] [Algebra k A] :=
  Aᵐᵒᵖ

end

end Formalization.Books.Brauer.Unit02
