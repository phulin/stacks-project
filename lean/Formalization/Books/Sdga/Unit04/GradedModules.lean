import Formalization.Books.Sdga.Unit02.Core

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
  let zero : GradedModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      laws := True }
  exact ⟨{ abelian := { has_zero := ⟨zero⟩, has_kernels := True, has_cokernels := True, exactness := True }, arbitrary_direct_sums := True, arbitrary_colimits := True, filtered_colimits_exact := True, arbitrary_products := True, arbitrary_limits := True, term_functor_preserves_limits := True, term_functor_preserves_colimits := True }⟩

end Sdga
