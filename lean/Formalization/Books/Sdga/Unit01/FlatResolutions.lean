import Formalization.Books.Sdga.Unit01.Core

/-! # 23. Flat resolutions -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

abbrev AdmissibleShortExactSequence {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} := ShortExactSequence (S := S) (A := A)

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

structure GoodModuleFamily {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  object : S.Obj → DGModule S A
  good : ∀ U, IsGood A (object U)

structure GoodDirectSumData {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {I : Type (max u v)} (F : I → DGModule S A) where
  sum : DGModule S A
  is_direct_sum : Prop
  good : IsGood A sum

structure GoodQuotientData {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) where
  source : DGModule S A
  map : DGModuleHom source M
  surjective : Prop
  cycles_surjective : Prop
  good : IsGood A source

structure AcyclicGoodData {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (P : DGModule S A) where
  tensor_acyclicity : Prop
  pullback_acyclicity : Prop
  pullback_good : Prop

structure GradedSheafOfSets {S : RingedSite.{u,v} R} where
  carrier : S.Obj → Type u
  degree : ∀ U, carrier U → ℤ

def freeGradedModuleCarrier {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (G : GradedSheafOfSets (S := S)) (n : ℤ) (U : S.Obj) : Type u :=
  Σ s : G.carrier U, A.component (n - G.degree U s) U

def freeDGModuleCarrier {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (G : GradedSheafOfSets (S := S)) (n : ℤ) (U : S.Obj) : Type u :=
  Σ s : G.carrier U, A.component (n - G.degree U s) U

structure FreeGradedModuleGoodStatement {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  free_modules_are_good : Prop

theorem lemma_supply_good {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    : Nonempty (GoodModuleFamily A) := by
  sorry

theorem lemma_good_admissible_ses
    {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (E : AdmissibleShortExactSequence (A := A)) :
    ((IsGood A E.K ∧ IsGood A E.L) → IsGood A E.M) ∧
      ((IsGood A E.K ∧ IsGood A E.M) → IsGood A E.L) ∧
      ((IsGood A E.L ∧ IsGood A E.M) → IsGood A E.K) := by
  sorry

theorem lemma_good_direct_sum {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {I : Type (max u v)} (F : I → DGModule S A)
    (hF : ∀ i, IsGood A (F i)) :
    Nonempty (GoodDirectSumData F) := by
  sorry

theorem lemma_good_quotient {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) : Nonempty (GoodQuotientData M) := by
  sorry

theorem lemma_free_graded_module_good {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) : Nonempty (FreeGradedModuleGoodStatement A) := by
  sorry

theorem lemma_resolve {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) : Nonempty (GoodResolutionData A M) := by
  sorry

theorem lemma_acyclic_good {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (P : DGModule S A) (hP : IsGood A P) (hPacyclic : IsAcyclic P) :
    Nonempty (AcyclicGoodData P) := by
  sorry

end Sdga
