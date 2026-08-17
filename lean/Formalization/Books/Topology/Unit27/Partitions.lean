import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructible
import Mathlib.Topology.Irreducible
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.NoetherianSpace

/-!
# Topology, Chapter 27: Partitions and stratifications

This file formalizes the definitions and theorem interfaces in the source
section on partitions and stratifications.  A partition is indexed by a type;
its parts are nonempty, pairwise disjoint, locally closed, and cover the
ambient space.  A refinement is represented by the assertion that every part
of the coarser partition is a union of parts of the finer one.
-/

namespace Formalization.Books.Topology.Unit27

open Set TopologicalSpace

universe u v w

variable {X : Type u} [TopologicalSpace X]

section Partitions

/-- A partition of `X` by nonempty locally closed subsets indexed by `ι`. -/
structure Partition (X : Type u) (ι : Type v) [TopologicalSpace X] where
  /-- The parts of the partition. -/
  parts : ι → Set X
  /-- Every part is locally closed. -/
  isLocallyClosed : ∀ i, IsLocallyClosed (parts i)
  /-- Every part is nonempty. -/
  nonempty : ∀ i, (parts i).Nonempty
  /-- Distinct parts are disjoint. -/
  pairwiseDisjoint : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (parts i) (parts j)
  /-- The parts cover the ambient space. -/
  iUnion_eq_univ : ⋃ i, parts i = (univ : Set X)

/-- A set is a union of selected parts of a partition. -/
def IsUnionOfParts {ι : Type v} (s : Set X) (P : Partition X ι) : Prop :=
  ∃ J : Set ι, s = ⋃ i ∈ J, P.parts i

namespace Partition

/-- `P` refines `Q` when every part of `Q` is a union of parts of `P`. -/
def Refines {ι : Type v} {κ : Type w} (P : Partition X ι) (Q : Partition X κ) : Prop :=
  ∀ j, IsUnionOfParts (Q.parts j) P

end Partition

/-- The canonical index type for connected components of a space. -/
def ConnectedComponentIndex (X : Type u) [TopologicalSpace X] :=
  {C : Set X // C ∈ Set.range (connectedComponent : X → Set X)}

/-- The partition of a space into its connected components. -/
def connectedComponentPartition : Partition X (ConnectedComponentIndex X) where
  parts C := C.1
  isLocallyClosed C := by
    rcases C.property with ⟨x, hC⟩
    rw [← hC]
    exact isClosed_connectedComponent.isLocallyClosed
  nonempty C := by
    rcases C.property with ⟨x, hC⟩
    rw [← hC]
    exact connectedComponent_nonempty
  pairwiseDisjoint := by
    intro C D hCD
    rcases C.property with ⟨x, hx⟩
    rcases D.property with ⟨y, hy⟩
    have hxy : connectedComponent x ≠ connectedComponent y := by
      intro hxy
      apply hCD
      apply Subtype.ext
      exact hx.symm.trans (hxy.trans hy)
    rw [← hx, ← hy]
    exact connectedComponent_disjoint hxy
  iUnion_eq_univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.2 ⟨⟨connectedComponent x, ⟨x, rfl⟩⟩, mem_connectedComponent⟩

/-- Every topological space has its canonical partition into connected components. -/
theorem exists_partition_into_connected_components :
    Nonempty (Partition X (ConnectedComponentIndex X)) :=
  ⟨connectedComponentPartition⟩

/-- The incidence part determined by a family of closed subsets. -/
def irreducibleComponentIncidencePart {ι : Type v} (Z : ι → Set X) (I : Set ι) : Set X :=
  (⋂ i ∈ I, Z i) \ (⋃ i ∈ Iᶜ, Z i)

/-- The indices of the nonempty incidence parts. -/
def IrreducibleComponentIncidenceIndex {ι : Type v} (Z : ι → Set X) :=
  {I : Set ι // (irreducibleComponentIncidencePart Z I).Nonempty}

/-- A finite family of closed sets has locally closed incidence parts. -/
theorem irreducibleComponentIncidencePart_isLocallyClosed
    {ι : Type v} [Finite ι] (Z : ι → Set X) (hZ : ∀ i, IsClosed (Z i)) (I : Set ι) :
    IsLocallyClosed (irreducibleComponentIncidencePart Z I) := by
  sorry

/-- The incidence partition associated to a finite enumeration of the irreducible components.

The subtype index omits the empty subsets among the subsets of the finite component index set,
as required by the nonempty-parts convention for `Partition`. -/
theorem irreducible_components_incidence_partition
    {ι : Type v} [Fintype ι] (Z : ι → Set X)
    (hZinj : Function.Injective Z)
    (hZrange : Set.range Z = irreducibleComponents X) :
    ∃ P : Partition X (IrreducibleComponentIncidenceIndex Z),
      (∀ I, P.parts I = irreducibleComponentIncidencePart Z I.1) ∧
        P.Refines connectedComponentPartition := by
  sorry

/-- Finitely many irreducible components admit an enumeration and hence an incidence partition. -/
theorem finite_irreducible_components_incidence_partition
    (hX : (irreducibleComponents X).Finite) :
    ∃ (ι : Type u) (_ : Fintype ι) (Z : ι → Set X),
      Function.Injective Z ∧ Set.range Z = irreducibleComponents X ∧
        ∃ P : Partition X (IrreducibleComponentIncidenceIndex Z),
          (∀ I, P.parts I = irreducibleComponentIncidencePart Z I.1) ∧
            P.Refines connectedComponentPartition := by
  sorry

/-- The relation induced by a good partition and closure. -/
def goodStratificationOrder {ι : Type v} (P : Partition X ι) (i j : ι) : Prop :=
  P.parts i ⊆ closure (P.parts j)

/-- A good stratification is a partition satisfying the source's incidence condition. -/
def IsGoodStratification {ι : Type v} (P : Partition X ι) : Prop :=
  ∀ i j, (P.parts i ∩ closure (P.parts j)).Nonempty →
    P.parts i ⊆ closure (P.parts j)

/-- The closure relation of a good stratification is a partial order. -/
theorem goodStratificationOrder_isPartialOrder
    {ι : Type v} (P : Partition X ι) (hP : IsGoodStratification P) :
    IsPartialOrder ι (goodStratificationOrder P) := by
  sorry

/-- The closure relation of a good stratification can be packaged as a Mathlib partial order. -/
theorem exists_partialOrder_of_goodStratification
    {ι : Type v} (P : Partition X ι) (hP : IsGoodStratification P) :
    ∃ o : PartialOrder ι,
      letI : PartialOrder ι := o
      ∀ i j, i ≤ j ↔ goodStratificationOrder P i j := by
  sorry

/-- The closure of a stratum in a good stratification is the union of the lower strata. -/
theorem goodStratification_closure_eq_belowUnion
    {ι : Type v} (P : Partition X ι) (hP : IsGoodStratification P) (j : ι) :
    closure (P.parts j) =
      ⋃ i, ⋃ (_ : goodStratificationOrder P i j), P.parts i := by
  sorry

/-- The union of the parts below an index in a partial order. -/
def belowUnion {ι : Type v} (o : PartialOrder ι) (E : ι → Set X) (i : ι) : Set X :=
  letI : PartialOrder ι := o
  ⋃ j, ⋃ (_ : j ≤ i), E j

/-- The union of the parts strictly below an index in a partial order. -/
def strictBelowUnion {ι : Type v} (o : PartialOrder ι) (E : ι → Set X) (i : ι) : Set X :=
  letI : PartialOrder ι := o
  ⋃ j, ⋃ (_ : j < i), E j

/-- The stratum obtained from a closed family by removing all strictly lower members. -/
def closedFamilyStratum {ι : Type v} (o : PartialOrder ι) (Z : ι → Set X) (i : ι) : Set X :=
  Z i \ strictBelowUnion o Z i

/-- The type of indices whose closed-family strata are nonempty. -/
def ClosedFamilyStratumIndex {ι : Type v} (o : PartialOrder ι) (Z : ι → Set X) :=
  {i : ι // (closedFamilyStratum o Z i).Nonempty}

/-- The order inherited by the nonempty-stratum index subtype. -/
@[instance_reducible]
def closedFamilyStratumIndexOrder {ι : Type v} (o : PartialOrder ι) (Z : ι → Set X) :
    PartialOrder (ClosedFamilyStratumIndex o Z) := by
  letI : PartialOrder ι := o
  exact PartialOrder.lift (fun i : ClosedFamilyStratumIndex o Z => i.1)
    Subtype.coe_injective

/-- A stratification packages a partition, a Mathlib partial order, and the closure condition. -/
structure Stratification (X : Type u) (ι : Type v) [TopologicalSpace X]
    (o : PartialOrder ι) extends Partition X ι where
  /-- The closure of every stratum is contained in the union of lower strata. -/
  closure_subset_below :
    ∀ j, closure (toPartition.parts j) ⊆ belowUnion o toPartition.parts j

namespace Stratification

def IsLocallyFinite (S : Stratification X ι o) : Prop :=
  LocallyFinite S.parts

def Refines {κ : Type w} (S : Stratification X ι o) (P : Partition X κ) : Prop :=
  S.toPartition.Refines P

end Stratification

/-- The canonical `LocallyFinite` predicate is equivalent to the source's open-neighborhood
formulation. -/
theorem locallyFinite_iff_open_neighborhood {ι : Type v} (E : ι → Set X) :
    LocallyFinite E ↔
      ∀ x, ∃ U, x ∈ U ∧ IsOpen U ∧ {i | (E i ∩ U).Nonempty}.Finite := by
  sorry

/-- A closed family satisfying the source's intersection identity. -/
def ClosedFamilyIntersectionIdentity {ι : Type v} (o : PartialOrder ι)
    (Z : ι → Set X) : Prop :=
  letI : PartialOrder ι := o
  ∀ i j, Z i ∩ Z j = ⋃ k, ⋃ (_ : k ≤ i ∧ k ≤ j), Z k

/-- A locally finite stratification yields a locally finite closed family of lower unions. -/
theorem Stratification.lowerUnion_isClosed
    {ι : Type v} (o : PartialOrder ι) (S : Stratification X ι o)
    (hfinite : S.IsLocallyFinite) :
    ∀ i, IsClosed (belowUnion o S.parts i) := by
  sorry

/-- Lower unions of a locally finite stratification satisfy the source's intersection identity. -/
theorem Stratification.lowerUnion_inter
    {ι : Type v} (o : PartialOrder ι) (S : Stratification X ι o)
    (hfinite : S.IsLocallyFinite) (i j : ι) :
    belowUnion o S.parts i ∩ belowUnion o S.parts j =
      ⋃ k, ⋃ (_ : k ≤ i ∧ k ≤ j), belowUnion o S.parts k := by
  sorry

/-- The converse construction from a locally finite closed family produces a stratification after
omitting empty strata. -/
theorem closed_family_stratification
    {ι : Type v} (o : PartialOrder ι) (Z : ι → Set X)
    (hclosed : ∀ i, IsClosed (Z i))
    (hcover : ⋃ i, Z i = (univ : Set X))
    (hfinite : LocallyFinite Z)
    (hinter : ClosedFamilyIntersectionIdentity o Z) :
    ∃ S : Stratification X (ClosedFamilyStratumIndex o Z) (closedFamilyStratumIndexOrder o Z),
      (∀ i, S.parts i = closedFamilyStratum o Z i.1) ∧
        S.IsLocallyFinite := by
  sorry

/-- A finite partition can be refined by a finite stratification. -/
theorem finite_partition_refined_by_finite_stratification
    {ι : Type v} (P : Partition X ι) [Finite ι] :
    ∃ (κ : Type v) (o : PartialOrder κ) (S : Stratification X κ o),
      Finite κ ∧ S.Refines P := by
  sorry

/-- A finite constructible cover admits a finite stratification by constructible strata refining it. -/
theorem constructible_cover_refined_by_constructible_stratification
    {n : ℕ} (T : Fin n → Set X)
    (hcover : ⋃ k, T k = (univ : Set X))
    (hT : ∀ k, Topology.IsConstructible (T k)) :
    ∃ (κ : Type v) (o : PartialOrder κ) (S : Stratification X κ o),
      Finite κ ∧
        (∀ i, Topology.IsConstructible (S.parts i)) ∧
          (∀ k, IsUnionOfParts (T k) S.toPartition) := by
  sorry

/-- In a Noetherian space, every finite partition has a finite good stratification refinement. -/
theorem noetherian_finite_partition_refined_by_finite_good_stratification
    [TopologicalSpace.NoetherianSpace X] {ι : Type v} (P : Partition X ι) [Finite ι] :
    ∃ (κ : Type v) (o : PartialOrder κ) (S : Stratification X κ o),
      Finite κ ∧ IsGoodStratification S.toPartition ∧ S.Refines P := by
  sorry

end Partitions

end Formalization.Books.Topology.Unit27
