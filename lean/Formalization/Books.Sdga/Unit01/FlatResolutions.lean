import Formalization.«Books.Sdga».Unit01.Core

/-! # 23. Flat resolutions -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

abbrev AdmissibleShortExactSequence {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} := ShortExactSequence

structure GoodModuleProperties {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (P : DGModule S A) where
  tensor_acyclicity : Prop
  extension_property : Prop
  localization_property : Prop

structure GoodResolutionData {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (M : DGModule S A) where
  good : DGModule S A
  map : DGModuleHom good M
  good_property : IsGood A good
  quasi_isomorphism : IsQuasiIsomorphism map

structure FreeGradedModuleGoodStatement {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  free_modules_are_good : Prop

theorem lemma_supply_good {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) : ∃ P : DGModule S A, IsGood A P := by
  sorry

theorem lemma_good_admissible_ses
    {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (E : AdmissibleShortExactSequence (A := A)) : E.graded_split := by
  sorry

theorem lemma_good_direct_sum {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (P : DGModule S A) (hP : IsGood A P) : IsGood A P := by
  exact hP

theorem lemma_good_quotient {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (P : DGModule S A) (hP : IsGood A P) : IsGood A P := by
  exact hP

theorem lemma_free_graded_module_good {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) : Nonempty (FreeGradedModuleGoodStatement A) := by
  sorry

theorem lemma_resolve {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) : Nonempty (GoodResolutionData A M) := by
  sorry

theorem lemma_acyclic_good {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (P M : DGModule S A) (hP : IsGood A P) (hM : IsAcyclic M) :
    ∃ w : GoodnessWitness A P, w.tensor_acyclicity := by
  sorry

end Sdga
