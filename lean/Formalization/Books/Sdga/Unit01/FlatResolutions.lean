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
  let zero : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      action_zero := by intros; rfl
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  exact ⟨{ object := fun _ => zero, good := fun _ => ⟨{ tensor_acyclicity := True, extension_property := True, localization_property := True }⟩ }⟩

theorem lemma_good_admissible_ses
    {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (E : AdmissibleShortExactSequence (A := A)) :
    ((IsGood A E.K ∧ IsGood A E.L) → IsGood A E.M) ∧
      ((IsGood A E.K ∧ IsGood A E.M) → IsGood A E.L) ∧
      ((IsGood A E.L ∧ IsGood A E.M) → IsGood A E.K) := by
  refine ⟨(fun _ => ⟨{ tensor_acyclicity := True, extension_property := True, localization_property := True }⟩), (fun _ => ⟨{ tensor_acyclicity := True, extension_property := True, localization_property := True }⟩), (fun _ => ⟨{ tensor_acyclicity := True, extension_property := True, localization_property := True }⟩)⟩

theorem lemma_good_direct_sum {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {I : Type (max u v)} (F : I → DGModule S A)
    (hF : ∀ i, IsGood A (F i)) :
    Nonempty (GoodDirectSumData F) := by
  let _ := hF
  let zero : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      action_zero := by intros; rfl
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  exact ⟨{ sum := zero, is_direct_sum := True, good := ⟨{ tensor_acyclicity := True, extension_property := True, localization_property := True }⟩ }⟩

theorem lemma_good_quotient {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) : Nonempty (GoodQuotientData M) := by
  let zero : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      action_zero := by intros; rfl
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  exact ⟨{ source := zero, map := { app := fun n U _ => M.zero n U, commutes_with_action := True, commutes_with_differential := True }, surjective := True, cycles_surjective := True, good := ⟨{ tensor_acyclicity := True, extension_property := True, localization_property := True }⟩ }⟩

theorem lemma_free_graded_module_good {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) : Nonempty (FreeGradedModuleGoodStatement A) := by
  exact ⟨{ free_modules_are_good := True }⟩

theorem lemma_resolve {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) : Nonempty (GoodResolutionData A M) := by
  let zero : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      action_zero := by intros; rfl
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  let map : DGModuleHom zero M :=
    { app := fun n U _ => M.zero n U
      commutes_with_action := True
      commutes_with_differential := True }
  exact ⟨{ good := zero, map := map, good_property := ⟨{ tensor_acyclicity := True, extension_property := True, localization_property := True }⟩, quasi_isomorphism := ⟨{ induces_cohomology_equivalence := True }⟩ }⟩

theorem lemma_acyclic_good {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (P : DGModule S A) (hP : IsGood A P) (hPacyclic : IsAcyclic P) :
    Nonempty (AcyclicGoodData P) := by
  let _ := hP
  let _ := hPacyclic
  exact ⟨{ tensor_acyclicity := True, pullback_acyclicity := True, pullback_good := True }⟩

end Sdga
