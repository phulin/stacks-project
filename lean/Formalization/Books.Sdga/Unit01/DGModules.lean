import Formalization.«Books.Sdga».Unit01.Core

/-! # 13. Sheaves of differential graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

abbrev DGModuleSheaf (S : RingedSite.{u,v} R) (A : DGAlgebra S) := DGModule S A

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
    {A : DGAlgebra S} (E : ShortExactSequence) where
  degree : ℤ
  exact_fragment : Prop

theorem definition_dgm (S : RingedSite.{u,v} R) (A : DGAlgebra S)
    (M : DGModuleSheaf S A) : M.graded_laws ∧ M.differential_squared ∧ M.leibniz := by
  sorry

theorem lemma_dgm_abelian (S : RingedSite.{u,v} R) (A : DGAlgebra S) :
    Nonempty (DGModuleCategoryProperties A) := by
  sorry

theorem equation_les {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (E : ShortExactSequence (A := A)) :
    Nonempty (LongExactCohomologyStatement E) := by
  sorry

end Sdga
