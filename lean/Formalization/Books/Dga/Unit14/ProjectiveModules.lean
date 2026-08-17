import Formalization.Books.Dga.Unit14.Core
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Differential Graded Algebra, Chapter 14: Projective modules over algebras

This file formalizes the first section of the source.  Right modules are
written as modules over the opposite algebra, as fixed in `Core`.
-/

namespace Formalization.Books.Dga.Unit14

open CategoryTheory

universe u v

/-! ## The regular module -/

/-- Evaluation at `1` identifies maps from the regular right module with the
underlying module.  The equivalence is left as a proposition-level interface;
its inverse sends `m` to right multiplication by `m`.
-/
theorem right_regular_hom_evaluation_equiv
    (A : Type u) [Ring A] (M : Type v) [AddCommGroup M]
    [Module Aᵐᵒᵖ M] :
    Nonempty ((A →ₗ[Aᵐᵒᵖ] M) ≃+ M) := by
  sorry

/-- The regular right module over an algebra is projective. -/
theorem right_regular_projective
    (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A] :
    RightModuleProjective A A := by
  sorry

/-! ## Lifting and enough projectives -/

/-- A map onto a projective right module admits a right inverse. -/
theorem right_projective_splits_surjective
    (A : Type u) [Ring A] {M P : Type v}
    [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [AddCommGroup P] [Module Aᵐᵒᵖ P]
    (f : M →ₗ[Aᵐᵒᵖ] P) (hf : Function.Surjective f)
    [RightModuleProjective A P] :
    ∃ s : P →ₗ[Aᵐᵒᵖ] M, f.comp s = LinearMap.id := by
  exact f.exists_rightInverse_of_surjective (LinearMap.range_eq_top_of_surjective f hf)

/-- The category of right `A`-modules has enough projectives. -/
theorem right_module_category_has_enough_projectives
    (A : Type u) [Ring A] [Small.{v} Aᵐᵒᵖ] :
    EnoughProjectives (ModuleCat.{v} Aᵐᵒᵖ) := by
  infer_instance

/-- Every right module is a quotient of a free right module, i.e. a direct sum
of copies of the regular right module. -/
theorem every_right_module_quotient_of_free
    (A : Type u) [Ring A] (M : Type v)
    [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    ∃ (I : Type v) (f : RightFreeModule A I →ₗ[Aᵐᵒᵖ] M),
      Function.Surjective f := by
  refine ⟨M, Finsupp.linearCombination (Aᵐᵒᵖ) (id : M → M), ?_⟩
  intro m
  exact ⟨Finsupp.single m 1, by simp⟩

/-! ## Direct summands -/

/-- A projective right module is a direct summand of a direct sum of regular
right modules. -/
theorem projective_right_module_is_direct_summand_of_free
    (A : Type u) [Ring A] (P : Type v)
    [AddCommGroup P] [Module Aᵐᵒᵖ P]
    (hP : RightModuleProjective A P) :
    ∃ (I : Type v) (i : P →ₗ[Aᵐᵒᵖ] RightFreeModule A I)
      (s : RightFreeModule A I →ₗ[Aᵐᵒᵖ] P),
      s.comp i = LinearMap.id := by
  rcases (Module.projective_def.mp hP) with ⟨s, hs⟩
  refine ⟨P, s, Finsupp.linearCombination (Aᵐᵒᵖ) (id : P → P), ?_⟩
  apply LinearMap.ext
  intro p
  exact hs p

end Formalization.Books.Dga.Unit14
