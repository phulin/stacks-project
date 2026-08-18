import Formalization.Books.Brauer.Unit02.NoncommutativeAlgebras
import Formalization.Books.Brauer.Unit03.Foundation

/-!
# Brauer groups, Chapter 3: Wedderburn's theorem

The source uses right modules.  The declarations below keep that convention
by viewing a right `A`-module as a module over `Aᵐᵒᵖ`.  The bicommutant and
finite Wedderburn--Artin constructions are reused from the earlier Brauer
formalization; the source-facing statements for the four simple-module facts
are recorded separately.
-/

namespace Formalization.Books.Brauer.Unit03

open Formalization.Books.Brauer.Unit02

universe u v

/-! ## The bicommutant lemma -/

/- `Formalization.Books.Brauer.Bicommutant` is the canonical endomorphism-ring
   construction for a right ideal, with the opposite ring restoring the right
   action. -/

/-- A simple ring is the bicommutant of each nonzero right ideal. -/
theorem rieffel_bicommutant (A : Type u) [Ring A] [IsSimpleRing A]
    (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Nonempty
      (A ≃+* Formalization.Books.Brauer.Bicommutant A M) := by
  exact Formalization.Books.Brauer.rieffel_bicommutant A M hM

/-! ## Simple modules over a finite algebra -/

/- The first item is represented by a simple submodule of the regular right
   module; its subtype is the asserted simple module. -/

/-- A nonzero finite algebra has a simple right module. -/
theorem finite_algebra_has_simple_right_module (k A : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A] [Nontrivial A] :
    ∃ S : Submodule Aᵐᵒᵖ A, IsSimpleModule Aᵐᵒᵖ S := by
  exact Formalization.Books.Brauer.finite_algebra_nonzero_module_has_simple_submodule k Aᵐᵒᵖ A

/-- Every nonzero right module over a finite algebra contains a simple submodule. -/
theorem finite_algebra_nonzero_right_module_has_simple_submodule
    (k A M : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [AddCommGroup M] [RightModule A M]
    [Nontrivial M] :
    ∃ S : Submodule Aᵐᵒᵖ M, IsSimpleModule Aᵐᵒᵖ S := by
  exact Formalization.Books.Brauer.finite_algebra_nonzero_module_has_simple_submodule k Aᵐᵒᵖ M

/-- A simple module over a finite algebra is finite-dimensional over the base field. -/
theorem simple_right_module_over_finite_algebra_is_finite_dimensional
    (k A M : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [AddCommGroup M] [RightModule A M]
    [Module k M] [IsScalarTower k Aᵐᵒᵖ M]
    [IsSimpleModule Aᵐᵒᵖ M] :
    FiniteDimensional k M := by
  exact Formalization.Books.Brauer.simple_module_over_finite_algebra_is_finite_dimensional k Aᵐᵒᵖ M

/-- The endomorphism ring of a simple right module is a skew field. -/
theorem simple_right_module_end_is_division_ring (A M : Type*) [Ring A]
    [AddCommGroup M] [RightModule A M]
    [IsSimpleModule Aᵐᵒᵖ M] :
    Nonempty (DivisionRing (Module.End Aᵐᵒᵖ M)) := by
  exact Formalization.Books.Brauer.simple_module_end_is_division_ring Aᵐᵒᵖ M

/-! ## The finite Wedderburn theorem -/

/-- A finite simple algebra is a matrix algebra over a finite skew field. -/
theorem finite_simple_algebra_is_matrix_over_finite_division_ring
    (k : Type v) (A : Type u) [Field k] [Ring A] [Algebra k A]
    [IsSimpleRing A] [FiniteDimensional k A] :
    ∃ (n : ℕ) (_ : NeZero n) (K : Type u) (_ : DivisionRing K)
      (_ : Algebra k K) (_ : FiniteDimensional k K),
      Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) K) := by
  exact Formalization.Books.Brauer.wedderburn_artin_finite k A

end Formalization.Books.Brauer.Unit03
