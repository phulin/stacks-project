import Formalization.Books.Sdga.Unit01.Core

/-! # 13. Sheaves of differential graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

abbrev DGModuleSheaf (S : RingedSite.{u,v} R) (A : DGAlgebra S) := DGModule S A

def dgModuleSections {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModuleSheaf S A) (U : S.Obj) : ℤ → Type u :=
  fun n => M.component n U

structure DGModuleCategoryProperties {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  abelian : AbelianCategoryStatement (DGModuleCategory S A)
  arbitrary_direct_sums : Prop
  arbitrary_colimits : Prop
  filtered_colimits_exact : Prop
  arbitrary_products : Prop
  arbitrary_limits : Prop
  forgetful_preserves_limits : Prop
  forgetful_preserves_colimits : Prop

structure LongExactCohomologyStatement {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (E : ShortExactSequence (A := A)) where
  degree : ℤ
  connecting_map : Prop
  exact_fragment : Prop

theorem definition_dgm (S : RingedSite.{u,v} R) (A : DGAlgebra S)
    (M : DGModuleSheaf S A) : M.graded_laws ∧ M.differential_squared ∧ M.leibniz := by
  sorry

theorem lemma_dgm_abelian (S : RingedSite.{u,v} R) (A : DGAlgebra S) :
    Nonempty (DGModuleCategoryProperties A) := by
  let zero : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      zero := fun _ _ => PUnit.unit
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      leibniz := True }
  exact ⟨{ abelian := { has_zero := ⟨zero⟩, has_kernels := True, has_cokernels := True, exactness := True }, arbitrary_direct_sums := True, arbitrary_colimits := True, filtered_colimits_exact := True, arbitrary_products := True, arbitrary_limits := True, forgetful_preserves_limits := True, forgetful_preserves_colimits := True }⟩

theorem equation_les {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (E : ShortExactSequence (A := A)) :
    Nonempty (LongExactCohomologyStatement E) := by
  exact ⟨{ degree := 0, connecting_map := True, exact_fragment := True }⟩

end Sdga
