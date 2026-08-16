import Formalization.Books.Sdga.Unit01.Core

/-! # 4. Sheaves of graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

abbrev GradedModuleSheaf (S : RingedSite.{u,v} R) (A : GradedAlgebra S) :=
  GradedModule S A

abbrev LeftGradedModuleSheaf (S : RingedSite.{u,v} R) (A : GradedAlgebra S) :=
  LeftGradedModule S A

structure GradedModuleSections {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M : GradedModule S A) (U : S.Obj) where
  component : ∀ n : ℤ, M.component n U
  finite_support : Prop

structure GradedModuleCategoryProperties {S : RingedSite.{u,v} R}
    (A : GradedAlgebra S) where
  abelian : AbelianCategoryStatement (GradedModuleCategory S A)
  arbitrary_direct_sums : Prop
  arbitrary_colimits : Prop
  filtered_colimits_exact : Prop
  arbitrary_products : Prop
  arbitrary_limits : Prop
  term_functor_preserves_limits : Prop
  term_functor_preserves_colimits : Prop

def gradedModuleSections {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M : GradedModuleSheaf S A) (U : S.Obj) : ℤ → Type u :=
  fun n => M.component n U

def gradedModuleUnderlyingFamily {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M : GradedModuleSheaf S A) : GradedFamily S := M.component

theorem lemma_gm_abelian (S : RingedSite.{u,v} R) (A : GradedAlgebra S) :
    Nonempty (GradedModuleCategoryProperties A) := by
  sorry

end Sdga
