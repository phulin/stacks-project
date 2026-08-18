import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Central.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Defs

/-!
# Noncommutative algebras

This file formalizes the conventions and definitions in Section 2 of
*Brauer groups*.  The finite, central, simple, and opposite constructions
are the corresponding Mathlib APIs; in particular, no parallel predicates
are introduced here.
-/

namespace Formalization.Books.Brauer

/- The source's convention that the scalar image is central is built into
   `Algebra`; its right-module convention is represented by `Module` over
   the opposite ring.  The source's “finite” is exactly Mathlib's
   `FiniteDimensional`, and `[A : k]` is `Module.finrank k A`. -/

theorem algebra_map_scalar_is_central (k A : Type*) [CommSemiring k]
    [Semiring A] [Algebra k A] (r : k) (a : A) :
    algebraMap k A r * a = a * algebraMap k A r := by
  simpa using Algebra.commutes r a

/- `DivisionRing`, `IsSimpleModule`, `IsSimpleRing`, and `Algebra.IsCentral`
   are used directly below rather than shadowed by parallel textbook
   predicates. -/

theorem divisionRing_module_is_free (D M : Type*) [DivisionRing D]
    [AddCommGroup M] [Module D M] : Module.Free D M := by
  infer_instance

theorem divisionRing_right_module_is_free (D M : Type*) [DivisionRing D]
    [AddCommGroup M] [Module Dᵐᵒᵖ M] : Module.Free Dᵐᵒᵖ M := by
  infer_instance

theorem central_algebra_center_eq_bot (k A : Type*) [CommSemiring k] [Semiring A]
    [Algebra k A] [Algebra.IsCentral k A] :
    Subalgebra.center k A = ⊥ :=
  Algebra.IsCentral.center_eq_bot k A

theorem opposite_central (k A : Type*) [CommSemiring k] [Semiring A]
    [Algebra k A] [Algebra.IsCentral k A] : Algebra.IsCentral k Aᵐᵒᵖ := by
  infer_instance

theorem opposite_simple (A : Type*) [NonUnitalNonAssocRing A] [IsSimpleRing A] :
    IsSimpleRing Aᵐᵒᵖ := by
  infer_instance

end Formalization.Books.Brauer
