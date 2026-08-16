import Formalization.«Books.Brauer».Unit01.NoncommutativeAlgebras
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Wedderburn's theorem

The source's bicommutant statement is expressed using the canonical
endomorphism-ring construction.  The finite Wedderburn--Artin conclusion is
reused directly from Mathlib.
-/

namespace Formalization.Books.Brauer

universe u v

/- The right action of a ring `A` is represented by a left action of
   `Aᵐᵒᵖ`. -/
abbrev Bicommutant (A : Type u) [Ring A] (M : Submodule Aᵐᵒᵖ A) : Type u :=
  (Module.End (Module.End Aᵐᵒᵖ M) M)ᵐᵒᵖ

theorem rieffel_bicommutant (A : Type u) [Ring A] [IsSimpleRing A]
    (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Nonempty (A ≃+* Bicommutant A M) := by
  sorry

theorem finite_algebra_has_simple_submodule (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Nontrivial A] :
    ∃ S : Submodule A A, IsSimpleModule A S := by
  sorry

theorem finite_algebra_nonzero_module_has_simple_submodule (k A M : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [AddCommGroup M] [Module A M] [Nontrivial M] :
    ∃ S : Submodule A M, IsSimpleModule A S := by
  sorry

theorem simple_module_over_finite_algebra_is_finite_dimensional
    (k A M : Type*) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M] : FiniteDimensional k M := by
  sorry

theorem simple_module_end_is_division_ring (A M : Type*) [Ring A]
    [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Nonempty (DivisionRing (Module.End A M)) := by
  classical
  exact ⟨inferInstance⟩

theorem wedderburn_artin_finite (k : Type v) (A : Type u) [Field k] [Ring A]
    [Algebra k A] [IsSimpleRing A] [FiniteDimensional k A] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D)
      (_ : Algebra k D) (_ : FiniteDimensional k D),
      Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) := by
  let hA : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact @IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A _ _ _ _ hA _

end Formalization.Books.Brauer
