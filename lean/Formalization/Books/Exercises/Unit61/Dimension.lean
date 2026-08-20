import Formalization.Books.Topology.Unit20.DimensionFunctions

import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.Topology.Sober

/-!
# Exercises, Chapter 61: Dimension

The source's five-point diagram is encoded directly in the specialization
order.  Immediate specialization is reused from the earlier topology
chapter, and the dimension is Mathlib's topological Krull dimension.
-/

namespace Formalization.Books.Exercises.Unit61

open Set _root_.Topology TopologicalSpace
open Formalization.Books.Topology.Unit08
open Formalization.Books.Topology.Unit20

universe u v

noncomputable section

/-- The five-point specialization diagram from the source. -/
def HasFivePointSpecializationDiagram
    (X : Type u) [TopologicalSpace X] (x y z u v : X) : Prop :=
  x ≠ y ∧ x ≠ z ∧ x ≠ u ∧ x ≠ v ∧
    y ≠ z ∧ y ≠ u ∧ y ≠ v ∧
    z ≠ u ∧ z ≠ v ∧ u ≠ v ∧
    x ⤳ u ∧ x ⤳ y ∧ y ⤳ z ∧ v ⤳ u ∧ v ⤳ z

private inductive FivePoint
  | x | y | z | u | v
  deriving DecidableEq

private instance : Fintype FivePoint :=
  ⟨{FivePoint.x, FivePoint.y, FivePoint.z, FivePoint.u, FivePoint.v}, by
    intro a
    cases a <;> simp⟩

private def FivePoint.le : FivePoint → FivePoint → Prop
  | .x, .x | .x, .y | .x, .u | .x, .z => True
  | .y, .y | .y, .z => True
  | .z, .z => True
  | .u, .u => True
  | .v, .v | .v, .u | .v, .z => True
  | _, _ => False

private instance : LE FivePoint := ⟨FivePoint.le⟩

private instance : PartialOrder FivePoint where
  le_refl := by
    intro a
    cases a <;> simp [LE.le, FivePoint.le]
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [LE.le, FivePoint.le]
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [LE.le, FivePoint.le]

private instance withLowerSetPartialOrder {α : Type u} [PartialOrder α] :
    PartialOrder (WithLowerSet α) :=
  inferInstanceAs (PartialOrder α)

private instance withLowerSetFinite {α : Type u} [Finite α] :
    Finite (WithLowerSet α) :=
  Finite.of_injective WithLowerSet.ofLowerSet (by
    intro a b hab
    exact hab)

private instance uliftFivePointFinite : Finite (ULift.{u} FivePoint) :=
  Finite.of_injective ULift.down (by
    intro a b hab
    cases a with
    | up a =>
      cases b with
      | up b =>
        cases hab
        rfl)

private def FivePoint.rank : FivePoint → Fin 3
  | .x | .v => 2
  | .y | .u => 1
  | .z => 0

private def FivePoint.uliftRank : ULift.{u} FivePoint → Fin 3 :=
  fun a => FivePoint.rank a.down

private theorem quasiSober_of_finite
    {Y : Type u} [TopologicalSpace Y] [Finite Y] : QuasiSober Y := by
  classical
  constructor
  intro Z hZ hZclosed
  let t : Finset (Set Y) := (Set.toFinite Z).toFinset.image
    (fun z : Y => closure ({z} : Set Y))
  have htclosed : ∀ S ∈ t, IsClosed S := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨z, -, rfl⟩
    exact isClosed_closure
  have hZsub : Z ⊆ ⋃₀ (t : Set (Set Y)) := by
    intro z hz
    refine mem_sUnion.mpr ⟨closure ({z} : Set Y), ?_, subset_closure (by simp)⟩
    exact Finset.mem_image.mpr ⟨z, (Set.toFinite Z).mem_toFinset.mpr hz, rfl⟩
  obtain ⟨S, hSt, hZS⟩ :=
    (isIrreducible_iff_sUnion_isClosed.mp hZ) t htclosed hZsub
  rcases Finset.mem_image.mp hSt with ⟨z, hzZ, rfl⟩
  have hzZ' : z ∈ Z := (Set.toFinite Z).mem_toFinset.mp hzZ
  refine ⟨z, ?_⟩
  rw [isGenericPoint_def]
  apply subset_antisymm
  · exact closure_minimal (singleton_subset_iff.mpr hzZ') hZclosed
  · exact hZS

private instance withLowerSetT0 {α : Type u} [PartialOrder α] :
    T0Space (WithLowerSet α) := by
  apply (t0Space_iff_exists_isOpen_xor_mem _).mpr
  intro a b hab
  by_cases hba : b ≤ a
  · refine ⟨Set.Iic b, IsLowerSet.isOpen_iff_isLowerSet.mpr (isLowerSet_Iic b), ?_⟩
    refine Or.inr ⟨?_, ?_⟩
    · exact mem_Iic.mpr le_rfl
    · intro ha
      apply hab
      exact le_antisymm ha hba
  · by_cases hab' : a ≤ b
    · refine ⟨Set.Iic a, IsLowerSet.isOpen_iff_isLowerSet.mpr (isLowerSet_Iic a), ?_⟩
      refine Or.inl ⟨?_, ?_⟩
      · exact mem_Iic.mpr le_rfl
      · intro hb
        exact hba hb
    · refine ⟨Set.Iic b, IsLowerSet.isOpen_iff_isLowerSet.mpr (isLowerSet_Iic b), ?_⟩
      refine Or.inr ⟨?_, ?_⟩
      · exact mem_Iic.mpr le_rfl
      · intro ha
        exact hab' ha

private theorem withLowerSet_specializes_iff_le
    {α : Type u} [PartialOrder α] (a b : α) :
    (WithLowerSet.toLowerSet a ⤳ WithLowerSet.toLowerSet b) ↔ a ≤ b := by
  constructor
  · intro hab
    have hopen : IsOpen (Set.Iic (WithLowerSet.toLowerSet b)) :=
      IsLowerSet.isOpen_iff_isLowerSet.mpr (isLowerSet_Iic b)
    exact (specializes_iff_forall_open.mp hab) _ hopen
      (mem_Iic.mpr le_rfl)
  · intro hab
    rw [specializes_iff_forall_open]
    intro s hs hb
    exact (IsLowerSet.isOpen_iff_isLowerSet.mp hs) hab hb

/-- The displayed diagram forces dimension at least two in a sober space. -/
theorem specialization_diagram_dimension_lower_bound
    {X : Type u} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    {x y z u v : X}
    (hdiagram : HasFivePointSpecializationDiagram X x y z u v) :
    (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  rcases hdiagram with ⟨hxy, hxz, hxu, hxv, hyz, hyu, hyv, hzu, hzv,
    huv, hxu', hxy', hyz', hvu', hvz'⟩
  have hclosure_inj :
      Function.Injective (closureSingletonIrreducibleClosed (X := X)) :=
    closureSingleton_injective_iff_t0.mpr (by infer_instance)
  have hzy : closureSingletonIrreducibleClosed z <
      closureSingletonIrreducibleClosed y := by
    apply lt_of_le_of_ne
    · exact closureSingletonIrreducibleClosed_le_of_specializes hyz'
    · intro heq
      apply hyz
      exact (hclosure_inj heq).symm
  have hyx : closureSingletonIrreducibleClosed y <
      closureSingletonIrreducibleClosed x := by
    apply lt_of_le_of_ne
    · exact closureSingletonIrreducibleClosed_le_of_specializes hxy'
    · intro heq
      apply hxy
      exact (hclosure_inj heq).symm
  let C : LTSeries (IrreducibleCloseds X) :=
    { length := 2
      toFun := ![closureSingletonIrreducibleClosed z,
        closureSingletonIrreducibleClosed y, closureSingletonIrreducibleClosed x]
      step := by
        intro i
        fin_cases i
        · exact hzy
        · exact hyx }
  simpa [topologicalKrullDim, C] using
    (Order.LTSeries.length_le_krullDim C)

/-- The lower bound is sharp: the diagram occurs in a sober space of
dimension two. -/
theorem exists_sober_specialization_diagram_dimension_two :
    ∃ (X : Type u) (inst : TopologicalSpace X),
      @QuasiSober X inst ∧ @T0Space X inst ∧
        ∃ x y z u v : X,
          @HasFivePointSpecializationDiagram X inst x y z u v ∧
            @topologicalKrullDim X inst = (2 : WithBot ℕ∞) := by
  letI : QuasiSober (WithLowerSet (ULift.{u} FivePoint)) :=
    quasiSober_of_finite
  refine ⟨WithLowerSet (ULift.{u} FivePoint), inferInstance,
    inferInstance, inferInstance, ?_⟩
  · let xp : WithLowerSet (ULift.{u} FivePoint) :=
      WithLowerSet.toLowerSet (ULift.up FivePoint.x)
    let yp : WithLowerSet (ULift.{u} FivePoint) :=
      WithLowerSet.toLowerSet (ULift.up FivePoint.y)
    let zp : WithLowerSet (ULift.{u} FivePoint) :=
      WithLowerSet.toLowerSet (ULift.up FivePoint.z)
    let up : WithLowerSet (ULift.{u} FivePoint) :=
      WithLowerSet.toLowerSet (ULift.up FivePoint.u)
    let vp : WithLowerSet (ULift.{u} FivePoint) :=
      WithLowerSet.toLowerSet (ULift.up FivePoint.v)
    have hdiagram :
        HasFivePointSpecializationDiagram
          (WithLowerSet (ULift.{u} FivePoint)) xp yp zp up vp := by
      simp [HasFivePointSpecializationDiagram, xp, yp, zp, up, vp,
        FivePoint.le, LE.le]
    have hdim_lower :
        (2 : WithBot ℕ∞) ≤
          topologicalKrullDim (WithLowerSet (ULift.{u} FivePoint)) :=
      specialization_diagram_dimension_lower_bound hdiagram
    have hdim_fin : Order.krullDim (Fin 3) ≤ (2 : WithBot ℕ∞) := by
      rw [Order.krullDim_eq_iSup_length]
      apply WithBot.coe_le_coe.mpr
      refine iSup_le fun C => ?_
      apply Nat.cast_le.mpr
      exact Nat.le_of_lt_succ (by simpa using C.length_lt_card)
    have hdim_upper :
        topologicalKrullDim (WithLowerSet (ULift.{u} FivePoint)) ≤
          (2 : WithBot ℕ∞) := by
      let hspec : PartialOrder (WithLowerSet (ULift.{u} FivePoint)) :=
        specializationOrder (WithLowerSet (ULift.{u} FivePoint))
      letI : PartialOrder (WithLowerSet (ULift.{u} FivePoint)) := hspec
      change Order.krullDim
        (IrreducibleCloseds (WithLowerSet (ULift.{u} FivePoint))) ≤ _
      have horder :
          @Order.krullDim
              (IrreducibleCloseds (WithLowerSet (ULift.{u} FivePoint)))
              (inferInstance : Preorder
                (IrreducibleCloseds (WithLowerSet (ULift.{u} FivePoint)))) =
            @Order.krullDim (WithLowerSet (ULift.{u} FivePoint)) hspec.toPreorder := by
        exact @Order.krullDim_eq_of_orderIso
          (IrreducibleCloseds (WithLowerSet (ULift.{u} FivePoint)))
          (WithLowerSet (ULift.{u} FivePoint))
          (inferInstance : Preorder
            (IrreducibleCloseds (WithLowerSet (ULift.{u} FivePoint))))
          hspec.toPreorder
          (irreducibleSetEquivPoints
            (α := WithLowerSet (ULift.{u} FivePoint)))
      rw [horder]
      have hrank :
          @StrictMono (WithLowerSet (ULift.{u} FivePoint)) (Fin 3)
            hspec.toPreorder Fin.instPartialOrder.toPreorder
            (FivePoint.uliftRank : WithLowerSet (ULift.{u} FivePoint) → Fin 3) := by
        intro a b hab
        cases a with
        | toLowerSet a =>
          cases b with
          | toLowerSet b =>
            cases a with
            | up a =>
              cases b with
              | up b =>
                have hab' := (@lt_iff_le_and_ne _ hspec
                  (WithLowerSet.toLowerSet (ULift.up a))
                  (WithLowerSet.toLowerSet (ULift.up b))).mp hab
                change
                  (WithLowerSet.toLowerSet (ULift.up b) ⤳
                    WithLowerSet.toLowerSet (ULift.up a)) ∧
                  WithLowerSet.toLowerSet (ULift.up a) ≠
                    WithLowerSet.toLowerSet (ULift.up b) at hab'
                have hba : b ≤ a :=
                  (withLowerSet_specializes_iff_le (ULift.up b) (ULift.up a)).mp
                    hab'.1
                have hne : b ≠ a := by
                  intro h
                  apply hab'.2
                  simpa [h]
                change FivePoint.rank a < FivePoint.rank b
                cases a <;> cases b <;>
                  simp [FivePoint.rank, LE.le, FivePoint.le] at hba hne ⊢
      have hdim_rank :
          @Order.krullDim (WithLowerSet (ULift.{u} FivePoint))
              hspec.toPreorder ≤
                @Order.krullDim (Fin 3) Fin.instPartialOrder.toPreorder := by
        exact @Order.krullDim_le_of_strictMono
          (WithLowerSet (ULift.{u} FivePoint)) (Fin 3) hspec.toPreorder
          Fin.instPartialOrder.toPreorder
          FivePoint.uliftRank hrank
      exact hdim_rank.trans hdim_fin
    refine ⟨xp, yp, zp, up, vp, hdiagram, le_antisymm hdim_upper hdim_lower⟩

/-- In the finite-type spectrum case, the last displayed specialization
cannot itself be immediate when the first branch `x ↝ u` is immediate. -/
theorem finite_type_spectrum_last_specialization_not_immediate
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A]
    {x y z u v : PrimeSpectrum A}
    (hdiagram : HasFivePointSpecializationDiagram (PrimeSpectrum A) x y z u v)
    (hxu : IsImmediateSpecialization x u) :
    ¬ IsImmediateSpecialization v z := by
  sorry

end

end Formalization.Books.Exercises.Unit61
