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
  have hI : IsClosed (⋃ i ∈ Iᶜ, Z i) :=
    (toFinite Iᶜ).isClosed_biUnion fun i _ => hZ i
  refine ⟨(⋃ i ∈ Iᶜ, Z i)ᶜ, ⋂ i ∈ I, Z i, hI.isOpen_compl,
    isClosed_biInter fun i hi => hZ i, ?_⟩
  simp [irreducibleComponentIncidencePart, sdiff_eq, inter_comm]

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
  classical
  have hZclosed : ∀ i, IsClosed (Z i) := by
    intro i
    exact isClosed_of_mem_irreducibleComponents _ (hZrange ▸ ⟨i, rfl⟩)
  have hmem : ∀ (I : IrreducibleComponentIncidenceIndex Z) {x : X} (hx :
      x ∈ irreducibleComponentIncidencePart Z I.1) (i : ι),
      x ∈ Z i ↔ i ∈ I.1 := by
    intro I x hx i
    change x ∈ (⋂ i ∈ I.1, Z i) ∧ x ∉ (⋃ i ∈ I.1ᶜ, Z i) at hx
    constructor
    · intro hxi
      by_contra hi
      exact hx.2 (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hi, hxi⟩⟩)
    · intro hi
      exact mem_iInter.1 (mem_iInter.1 hx.1 i) hi
  have hcover : ∀ x : X, ∃ I : IrreducibleComponentIncidenceIndex Z,
      x ∈ irreducibleComponentIncidencePart Z I.1 := by
    intro x
    have hxcomp : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]
      exact mem_univ x
    rcases mem_sUnion.1 hxcomp with ⟨C, hC, hxC⟩
    have hCrange : C ∈ Set.range Z := hZrange.symm ▸ hC
    rcases hCrange with ⟨i, hi⟩
    let I : Set ι := {i | x ∈ Z i}
    have hxI : x ∈ irreducibleComponentIncidencePart Z I := by
      change x ∈ (⋂ i ∈ I, Z i) ∧ x ∉ (⋃ i ∈ Iᶜ, Z i)
      constructor
      · exact mem_iInter.2 fun i => mem_iInter.2 fun hi => hi
      · intro hx
        rcases mem_iUnion.1 hx with ⟨i, hx⟩
        rcases mem_iUnion.1 hx with ⟨hi, hxi⟩
        exact hi hxi
    exact ⟨⟨I, ⟨x, hxI⟩⟩, hxI⟩
  have hpart_subset_component :
      ∀ (I : IrreducibleComponentIncidenceIndex Z) (x : X),
        x ∈ irreducibleComponentIncidencePart Z I.1 →
          irreducibleComponentIncidencePart Z I.1 ⊆ connectedComponent x := by
    intro I x hx y hy
    have hxcomp : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]
      exact mem_univ x
    rcases mem_sUnion.1 hxcomp with ⟨C, hC, hxC⟩
    have hCrange : C ∈ Set.range Z := hZrange.symm ▸ hC
    rcases hCrange with ⟨k, hk⟩
    have hxZk : x ∈ Z k := hk.symm ▸ hxC
    have hkI : k ∈ I.1 := (hmem I hx k).1 hxZk
    have hkcomp : Z k ∈ irreducibleComponents X := by
      rw [← hZrange]
      exact ⟨k, rfl⟩
    have hZk : IsIrreducible (Z k) := hkcomp.1
    have hconn : IsConnected (Z k) := hZk.isConnected
    exact hconn.subset_connectedComponent hxZk ((hmem I hy k).2 hkI)
  let P : Partition X (IrreducibleComponentIncidenceIndex Z) :=
    { parts := fun I => irreducibleComponentIncidencePart Z I.1
      isLocallyClosed := fun I =>
        irreducibleComponentIncidencePart_isLocallyClosed Z hZclosed I.1
      nonempty := fun I => I.2
      pairwiseDisjoint := by
        intro I J hIJ
        refine Set.disjoint_left.2 ?_
        intro x hxI hxJ
        apply hIJ
        apply Subtype.ext
        ext i
        exact ⟨fun hi => (hmem J hxJ i).1 ((hmem I hxI i).2 hi),
          fun hi => (hmem I hxI i).1 ((hmem J hxJ i).2 hi)⟩
      iUnion_eq_univ := by
        apply eq_univ_of_forall
        intro x
        rcases hcover x with ⟨I, hx⟩
        exact mem_iUnion.2 ⟨I, hx⟩ }
  refine ⟨P, ?_, ?_⟩
  · intro I
    rfl
  · intro C
    rcases C.property with ⟨x, hxC⟩
    let J : Set (IrreducibleComponentIncidenceIndex Z) :=
      {I | P.parts I ⊆ C.1}
    refine ⟨J, ?_⟩
    apply Set.Subset.antisymm
    · intro y hyC
      change y ∈ C.1 at hyC
      rcases hcover y with ⟨I, hyI⟩
      have hycomp : connectedComponent y = C.1 := by
        have hyx : y ∈ connectedComponent x := hxC.symm ▸ hyC
        exact (connectedComponent_eq hyx).symm.trans hxC
      have hsub : P.parts I ⊆ C.1 := by
        exact (hpart_subset_component I y hyI).trans_eq hycomp
      exact mem_iUnion.2 ⟨I, mem_iUnion.2 ⟨show I ∈ J from hsub, hyI⟩⟩
    · intro y hy
      rcases mem_iUnion.1 hy with ⟨I, hy⟩
      rcases mem_iUnion.1 hy with ⟨hIJ, hy⟩
      exact hIJ hy

/-- Finitely many irreducible components admit an enumeration and hence an incidence partition. -/
theorem finite_irreducible_components_incidence_partition
    (hX : (irreducibleComponents X).Finite) :
    ∃ (ι : Type u) (_ : Fintype ι) (Z : ι → Set X),
      Function.Injective Z ∧ Set.range Z = irreducibleComponents X ∧
        ∃ P : Partition X (IrreducibleComponentIncidenceIndex Z),
          (∀ I, P.parts I = irreducibleComponentIncidencePart Z I.1) ∧
            P.Refines connectedComponentPartition := by
  classical
  let ι : Type u := {C : Set X // C ∈ irreducibleComponents X}
  letI : Fintype ι := by
    dsimp [ι]
    exact hX.fintype
  let Z : ι → Set X := fun C => C.1
  have hZinj : Function.Injective Z := by
    intro A B hAB
    exact Subtype.ext hAB
  have hZrange : Set.range Z = irreducibleComponents X := by
    ext C
    constructor
    · rintro ⟨A, rfl⟩
      exact A.property
    · intro hC
      exact ⟨⟨C, hC⟩, rfl⟩
  obtain ⟨P, hPparts, hPrefines⟩ :=
    irreducible_components_incidence_partition Z hZinj hZrange
  exact ⟨ι, inferInstance, Z, hZinj, hZrange, P, hPparts, hPrefines⟩

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
  refine { refl := ?_, trans := ?_, antisymm := ?_ }
  · intro i
    exact subset_closure
  · intro i j k hij hjk x hxi
    simpa only [closure_closure] using closure_mono hjk (hij hxi)
  · intro i j hij hji
    by_contra hne
    obtain ⟨x, hxi⟩ := P.nonempty i
    have hij' : P.parts i ⊆ closure (P.parts j) :=
      hP i j ⟨x, hxi, hij hxi⟩
    rcases P.isLocallyClosed i with ⟨U, Z, hU, hZ, hparts⟩
    have hsubZ : closure (P.parts i) ⊆ Z := by
      refine closure_minimal ?_ hZ
      intro y hy
      rw [hparts] at hy
      exact hy.2
    have hxU : x ∈ U := by
      rw [hparts] at hxi
      exact hxi.1
    obtain ⟨y, hyU, hyj⟩ := mem_closure_iff.mp (hij' hxi) U hU hxU
    have hyZ : y ∈ Z := hsubZ (hji hyj)
    have hyi : y ∈ P.parts i := by
      rw [hparts]
      exact ⟨hyU, hyZ⟩
    exact Set.disjoint_left.1 (P.pairwiseDisjoint hne) hyi hyj

/-- The closure relation of a good stratification can be packaged as a Mathlib partial order. -/
theorem exists_partialOrder_of_goodStratification
    {ι : Type v} (P : Partition X ι) (hP : IsGoodStratification P) :
    ∃ o : PartialOrder ι,
      letI : PartialOrder ι := o
      ∀ i j, i ≤ j ↔ goodStratificationOrder P i j := by
  let hrel : IsPartialOrder ι (goodStratificationOrder P) :=
    goodStratificationOrder_isPartialOrder P hP
  let o : PartialOrder ι :=
    { le := goodStratificationOrder P
      le_refl := hrel.refl
      le_trans := hrel.trans
      le_antisymm := hrel.antisymm }
  refine ⟨o, ?_⟩
  letI : PartialOrder ι := o
  intro i j
  rfl

/-- The closure of a stratum in a good stratification is the union of the lower strata. -/
theorem goodStratification_closure_eq_belowUnion
    {ι : Type v} (P : Partition X ι) (hP : IsGoodStratification P) (j : ι) :
    closure (P.parts j) =
      ⋃ i, ⋃ (_ : goodStratificationOrder P i j), P.parts i := by
  ext x
  constructor
  · intro hx
    have hxcover : x ∈ ⋃ i, P.parts i := by
      rw [P.iUnion_eq_univ]
      exact mem_univ x
    rcases mem_iUnion.1 hxcover with ⟨i, hxi⟩
    have hij : goodStratificationOrder P i j :=
      hP i j ⟨x, hxi, hx⟩
    exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hij, hxi⟩⟩
  · intro hx
    rcases mem_iUnion.1 hx with ⟨i, hx⟩
    rcases mem_iUnion.1 hx with ⟨hij, hxi⟩
    exact hij hxi

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
  constructor
  · intro hE x
    obtain ⟨t, htx, hfin⟩ := hE x
    obtain ⟨U, hUt, hU, hxU⟩ := mem_nhds_iff.mp htx
    refine ⟨U, hxU, hU, hfin.subset ?_⟩
    intro i hi
    exact hi.mono (inter_subset_inter_right _ hUt)
  · intro hE x
    obtain ⟨U, hxU, hU, hfin⟩ := hE x
    exact ⟨U, hU.mem_nhds hxU, hfin⟩

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
  letI : PartialOrder ι := o
  intro i
  have hloc : LocallyFinite (fun j : {j : ι // j ≤ i} => S.parts j.1) :=
    hfinite.comp_injective Subtype.val_injective
  have heq : belowUnion o S.parts i =
      ⋃ j : {j : ι // j ≤ i}, S.parts j.1 := by
    ext x
    simp [belowUnion]
  rw [heq]
  apply isClosed_of_closure_subset
  rw [LocallyFinite.closure_iUnion hloc]
  intro x hx
  rcases mem_iUnion.1 hx with ⟨j, hxj⟩
  have hbelow := S.closure_subset_below j.1 hxj
  change x ∈ ⋃ k, ⋃ (_ : k ≤ j.1), S.parts k at hbelow
  rcases mem_iUnion.1 hbelow with ⟨k, hbelow⟩
  rcases mem_iUnion.1 hbelow with ⟨hkj, hxk⟩
  exact mem_iUnion.2 ⟨⟨k, hkj.trans j.2⟩, hxk⟩

/-- Lower unions of a locally finite stratification satisfy the source's intersection identity. -/
theorem Stratification.lowerUnion_inter
    {ι : Type v} (o : PartialOrder ι) (S : Stratification X ι o)
    (hfinite : S.IsLocallyFinite) (i j : ι) :
    belowUnion o S.parts i ∩ belowUnion o S.parts j =
      ⋃ k, ⋃ (_ : k ≤ i ∧ k ≤ j), belowUnion o S.parts k := by
  letI : PartialOrder ι := o
  have hmono : ∀ {a b : ι}, a ≤ b →
      belowUnion o S.parts a ⊆ belowUnion o S.parts b := by
    intro a b hab x hx
    change x ∈ ⋃ k, ⋃ (_ : k ≤ a), S.parts k at hx
    change x ∈ ⋃ k, ⋃ (_ : k ≤ b), S.parts k
    rcases mem_iUnion.1 hx with ⟨k, hx⟩
    rcases mem_iUnion.1 hx with ⟨hka, hxk⟩
    exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨hka.trans hab, hxk⟩⟩
  ext x
  constructor
  · intro hx
    change (x ∈ ⋃ a, ⋃ (_ : a ≤ i), S.parts a) ∧
      x ∈ ⋃ b, ⋃ (_ : b ≤ j), S.parts b at hx
    rcases hx with ⟨hxi, hxj⟩
    rcases mem_iUnion.1 hxi with ⟨a, hxi⟩
    rcases mem_iUnion.1 hxi with ⟨hai, hxa⟩
    rcases mem_iUnion.1 hxj with ⟨b, hxj⟩
    rcases mem_iUnion.1 hxj with ⟨hbj, hxb⟩
    have hab : a = b := by
      by_contra hab
      exact Set.disjoint_left.1 (S.toPartition.pairwiseDisjoint hab) hxa hxb
    subst b
    have hxaBelow : x ∈ belowUnion o S.parts a := by
      change x ∈ ⋃ k, ⋃ (_ : k ≤ a), S.parts k
      exact mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨le_rfl, hxa⟩⟩
    exact mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨⟨hai, hbj⟩, hxaBelow⟩⟩
  · intro hx
    rcases mem_iUnion.1 hx with ⟨k, hxk⟩
    rcases mem_iUnion.1 hxk with ⟨hki, hxk⟩
    exact ⟨hmono hki.1 hxk, hmono hki.2 hxk⟩

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
  classical
  letI : PartialOrder ι := o
  let K : X → Set ι := fun x => {i | x ∈ Z i}
  have hKfinite : ∀ x, (K x).Finite := by
    intro x
    exact hfinite.point_finite x
  have hminimal_stratum : ∀ x : X, (K x).Nonempty →
      ∃ i, x ∈ closedFamilyStratum o Z i := by
    intro x hxK
    obtain ⟨i, hi⟩ := (hKfinite x).exists_minimal hxK
    refine ⟨i, ?_⟩
    change x ∈ Z i ∧ x ∉ ⋃ k, ⋃ (_ : k < i), Z k
    constructor
    · exact hi.1
    · intro hx
      rcases mem_iUnion.1 hx with ⟨k, hx⟩
      rcases mem_iUnion.1 hx with ⟨hki, hxk⟩
      exact (not_le_of_gt hki) (hi.2 hxk hki.le)
  have hminimal_below : ∀ (i : ι) (x : X), x ∈ Z i →
      ∃ j, j ≤ i ∧ x ∈ closedFamilyStratum o Z j := by
    intro i x hxi
    let L : Set ι := {j | x ∈ Z j ∧ j ≤ i}
    have hLfinite : L.Finite := (hKfinite x).subset (by
      intro j hj
      exact hj.1)
    have hLnonempty : L.Nonempty := ⟨i, hxi, le_rfl⟩
    obtain ⟨j, hj⟩ := hLfinite.exists_minimal hLnonempty
    refine ⟨j, hj.1.2, ?_⟩
    change x ∈ Z j ∧ x ∉ ⋃ k, ⋃ (_ : k < j), Z k
    constructor
    · exact hj.1.1
    · intro hx
      rcases mem_iUnion.1 hx with ⟨k, hx⟩
      rcases mem_iUnion.1 hx with ⟨hkj, hxk⟩
      exact (not_le_of_gt hkj) (hj.2 ⟨hxk, hkj.le.trans hj.1.2⟩ hkj.le)
  have hpoint : ∀ x : X, ∃ i : ClosedFamilyStratumIndex o Z,
      x ∈ closedFamilyStratum o Z i.1 := by
    intro x
    have hxK : (K x).Nonempty := by
      have hxunion : x ∈ ⋃ i, Z i := by
        rw [hcover]
        exact mem_univ x
      rcases mem_iUnion.1 hxunion with ⟨i, hxi⟩
      exact ⟨i, hxi⟩
    obtain ⟨i, hi⟩ := hminimal_stratum x hxK
    exact ⟨⟨i, ⟨x, hi⟩⟩, hi⟩
  have hstrict_closed : ∀ i, IsClosed (strictBelowUnion o Z i) := by
    intro i
    have hloc : LocallyFinite (fun j : {j : ι // j < i} => Z j.1) :=
      hfinite.comp_injective Subtype.val_injective
    have heq : strictBelowUnion o Z i = ⋃ j : {j : ι // j < i}, Z j.1 := by
      ext x
      simp [strictBelowUnion]
    rw [heq]
    exact LocallyFinite.isClosed_iUnion hloc (fun j => hclosed j.1)
  let κ := ClosedFamilyStratumIndex o Z
  letI : PartialOrder κ := closedFamilyStratumIndexOrder o Z
  let Q : Partition X κ :=
    { parts := fun i => closedFamilyStratum o Z i.1
      isLocallyClosed := by
        intro i
        refine ⟨(strictBelowUnion o Z i.1)ᶜ, Z i.1,
          (hstrict_closed i.1).isOpen_compl, hclosed i.1, ?_⟩
        rw [closedFamilyStratum, Set.sdiff_eq, inter_comm]
      nonempty := fun i => i.2
      pairwiseDisjoint := by
        intro I J hIJ
        refine Set.disjoint_left.2 ?_
        intro x hxI hxJ
        change x ∈ Z I.1 ∧ x ∉ ⋃ k, ⋃ (_ : k < I.1), Z k at hxI
        change x ∈ Z J.1 ∧ x ∉ ⋃ k, ⋃ (_ : k < J.1), Z k at hxJ
        have hxinter : x ∈ Z I.1 ∩ Z J.1 := ⟨hxI.1, hxJ.1⟩
        have hxunion : x ∈ ⋃ k, ⋃ (_ : k ≤ I.1 ∧ k ≤ J.1), Z k := by
          rw [← hinter I.1 J.1]
          exact hxinter
        rcases mem_iUnion.1 hxunion with ⟨k, hxunion⟩
        rcases mem_iUnion.1 hxunion with ⟨hki, hxk⟩
        have hkI : k = I.1 := by
          rcases eq_or_lt_of_le hki.1 with rfl | hki'
          · rfl
          · exact False.elim (hxI.2 (mem_iUnion.2
              ⟨k, mem_iUnion.2 ⟨hki', hxk⟩⟩))
        have hkJ : k = J.1 := by
          rcases eq_or_lt_of_le hki.2 with rfl | hkj'
          · rfl
          · exact False.elim (hxJ.2 (mem_iUnion.2
              ⟨k, mem_iUnion.2 ⟨hkj', hxk⟩⟩))
        apply hIJ
        apply Subtype.ext
        exact hkI.symm.trans hkJ
      iUnion_eq_univ := by
        apply eq_univ_of_forall
        intro x
        rcases hpoint x with ⟨i, hi⟩
        exact mem_iUnion.2 ⟨i, hi⟩ }
  let S : Stratification X κ (closedFamilyStratumIndexOrder o Z) :=
    { toPartition := Q
      closure_subset_below := by
        intro i
        intro x hx
        have hxZi : x ∈ Z i.1 := by
          apply (hclosed i.1).closure_subset
          exact (closure_mono sdiff_subset) hx
        obtain ⟨j, hji, hxj⟩ := hminimal_below i.1 x hxZi
        change x ∈ ⋃ j, ⋃ (_ : j ≤ i), closedFamilyStratum o Z j.1
        refine mem_iUnion.2 ⟨⟨j, ⟨x, hxj⟩⟩, ?_⟩
        exact mem_iUnion.2 ⟨hji, hxj⟩ }
  refine ⟨S, ?_, ?_⟩
  · intro i
    rfl
  · change LocallyFinite (fun i : κ => closedFamilyStratum o Z i.1)
    have hloc : LocallyFinite (fun i : κ => Z i.1) :=
      hfinite.comp_injective Subtype.val_injective
    exact hloc.subset fun i => sdiff_subset

/-- A finite partition can be refined by a finite stratification. -/
theorem finite_partition_refined_by_finite_stratification
    {ι : Type v} (P : Partition X ι) [Finite ι] :
    ∃ (κ : Type v) (o : PartialOrder κ) (S : Stratification X κ o),
      Finite κ ∧ S.Refines P := by
  classical
  let A := ι × Bool
  let κ := Set A
  let F : A → Set X := fun a =>
    if a.2 then closure (P.parts a.1)
    else (closure (P.parts a.1) \ P.parts a.1)
  let Z : κ → Set X := fun s => ⋂ a ∈ s, F a
  let o : PartialOrder κ :=
    { le := fun s t => t ⊆ s
      lt := fun s t => t ⊆ s ∧ ¬s ⊆ t
      le_refl := fun _ => subset_rfl
      le_trans := fun _ _ _ hst htu => htu.trans hst
      lt_iff_le_not_ge := by intros; rfl
      le_antisymm := fun s t hst hts => Set.Subset.antisymm hts hst }
  have hdelta_closed : ∀ i, IsClosed (closure (P.parts i) \ P.parts i) := by
    intro i
    simpa [coborder] using (P.isLocallyClosed i).isOpen_coborder.isClosed_compl
  have hFclosed : ∀ a, IsClosed (F a) := by
    rintro ⟨i, b⟩
    cases b
    · simpa [F] using hdelta_closed i
    · simpa [F] using isClosed_closure
  have hZclosed : ∀ s, IsClosed (Z s) := by
    intro s
    exact isClosed_biInter fun a _ => hFclosed a
  have hZcover : ⋃ s, Z s = (univ : Set X) := by
    apply eq_univ_of_forall
    intro x
    refine mem_iUnion.2 ⟨(∅ : κ), ?_⟩
    change x ∈ ⋂ a ∈ (∅ : Set A), F a
    simp only [mem_iInter]
    intro a ha
    exact False.elim (by simpa using ha)
  have hZfinite : LocallyFinite Z := locallyFinite_of_finite Z
  have hinter : ClosedFamilyIntersectionIdentity o Z := by
    letI : PartialOrder κ := o
    intro s t
    ext x
    constructor
    · intro hx
      have hxs0 : x ∈ Z s := hx.1
      have hxt0 : x ∈ Z t := hx.2
      have hxs : ∀ a, a ∈ s → x ∈ F a := by
        simpa only [Z, mem_iInter] using hxs0
      have hxt : ∀ a, a ∈ t → x ∈ F a := by
        simpa only [Z, mem_iInter] using hxt0
      refine mem_iUnion.2 ⟨s ∪ t, ?_⟩
      refine mem_iUnion.2 ⟨?_, ?_⟩
      · constructor
        · change s ⊆ s ∪ t
          exact subset_union_left
        · change t ⊆ s ∪ t
          exact subset_union_right
      · have hxu : ∀ a, a ∈ s ∪ t → x ∈ F a := by
          intro a ha
          rcases ha with ha | ha
          · exact hxs a ha
          · exact hxt a ha
        simpa only [Z, mem_iInter] using hxu
    · intro hx
      rcases mem_iUnion.1 hx with ⟨s', hx⟩
      rcases mem_iUnion.1 hx with ⟨hst, hxs'⟩
      rcases hst with ⟨hss', hts'⟩
      change s ⊆ s' at hss'
      change t ⊆ s' at hts'
      have hxs0 : x ∈ Z s' := hxs'
      have hxs' : ∀ a, a ∈ s' → x ∈ F a := by
        simpa only [Z, mem_iInter] using hxs0
      have hxs : ∀ a, a ∈ s → x ∈ F a := by
        intro a ha
        exact hxs' a (hss' ha)
      have hxt : ∀ a, a ∈ t → x ∈ F a := by
        intro a ha
        exact hxs' a (hts' ha)
      constructor
      · simpa only [Z, mem_iInter] using hxs
      · simpa only [Z, mem_iInter] using hxt
  obtain ⟨S, hSparts, hSfinite⟩ :=
    closed_family_stratification o Z hZclosed hZcover hZfinite hinter
  have hstratum_subset (j : ι) (s : κ) (x : X)
      (hxS : x ∈ closedFamilyStratum o Z s) (hxj : x ∈ P.parts j) :
      closedFamilyStratum o Z s ⊆ P.parts j := by
    letI : PartialOrder κ := o
    letI : LT κ := o.toPreorder.toLT
    change x ∈ Z s ∧ x ∉ ⋃ k, ⋃ (_ : k < s), Z k at hxS
    have hxZ : x ∈ Z s := hxS.1
    have hxZ' : ∀ a, a ∈ s → x ∈ F a := by
      simpa only [Z, mem_iInter] using hxZ
    have hT : Z s ⊆ closure (P.parts j) := by
      by_cases ha : (j, true) ∈ s
      · intro y hy
        have hy' : ∀ a, a ∈ s → y ∈ F a := by
          simpa only [Z, mem_iInter] using hy
        simpa [F] using hy' (j, true) ha
      · have hinsert : (insert (j, true) s : κ) < s := by
          change s ⊆ insert (j, true) s ∧ ¬insert (j, true) s ⊆ s
          constructor
          · exact subset_insert _ _
          · intro h
            exact ha (h (Set.mem_insert _ _))
        have hxinsert : x ∈ Z (insert (j, true) s) := by
          have hxin : ∀ a, a ∈ insert (j, true) s → x ∈ F a := by
            intro a ha'
            rcases ha' with rfl | ha'
            · simpa [F] using subset_closure hxj
            · exact hxZ' a ha'
          simpa only [Z, mem_iInter] using hxin
        have hxlower : x ∈ ⋃ k, ⋃ (_ : k < s), Z k :=
          mem_iUnion.2 ⟨insert (j, true) s,
            mem_iUnion.2 ⟨hinsert, hxinsert⟩⟩
        exact False.elim (hxS.2 hxlower)
    have hfalse : (j, false) ∉ s := by
      intro ha
      have hxDelta : x ∈ closure (P.parts j) \ P.parts j := by
        simpa [F] using hxZ' (j, false) ha
      exact hxDelta.2 hxj
    have hD : ∀ y, y ∈ closedFamilyStratum o Z s →
        y ∉ closure (P.parts j) \ P.parts j := by
      intro y hyS hyD
      change y ∈ Z s ∧ y ∉ ⋃ k, ⋃ (_ : k < s), Z k at hyS
      have hyZ : y ∈ Z s := hyS.1
      have hyZ' : ∀ a, a ∈ s → y ∈ F a := by
        simpa only [Z, mem_iInter] using hyZ
      have hinsert : (insert (j, false) s : κ) < s := by
        change s ⊆ insert (j, false) s ∧ ¬insert (j, false) s ⊆ s
        constructor
        · exact subset_insert _ _
        · intro h
          exact hfalse (h (Set.mem_insert _ _))
      have hyinsert : y ∈ Z (insert (j, false) s) := by
        have hyin : ∀ a, a ∈ insert (j, false) s → y ∈ F a := by
          intro a ha'
          rcases ha' with rfl | ha'
          · simpa [F] using hyD
          · exact hyZ' a ha'
        simpa only [Z, mem_iInter] using hyin
      exact hyS.2 (mem_iUnion.2 ⟨insert (j, false) s,
        mem_iUnion.2 ⟨hinsert, hyinsert⟩⟩)
    intro y hyS
    have hyT : y ∈ closure (P.parts j) := hT (by
      change y ∈ Z s ∧ y ∉ ⋃ k, ⋃ (_ : k < s), Z k at hyS
      exact hyS.1)
    by_contra hyj'
    exact hD y hyS ⟨hyT, hyj'⟩
  refine ⟨ClosedFamilyStratumIndex o Z, closedFamilyStratumIndexOrder o Z, S, ?_⟩
  constructor
  · letI : Finite (ClosedFamilyStratumIndex o Z) :=
      Finite.of_injective (fun i : ClosedFamilyStratumIndex o Z => i.1)
        Subtype.val_injective
    exact inferInstance
  · intro j
    let J : Set (ClosedFamilyStratumIndex o Z) :=
      {i | S.parts i ⊆ P.parts j}
    refine ⟨J, ?_⟩
    apply Set.Subset.antisymm
    · intro x hxj
      have hxcover : x ∈ ⋃ i, S.parts i := by
        rw [S.iUnion_eq_univ]
        exact mem_univ x
      rcases mem_iUnion.1 hxcover with ⟨i, hxi⟩
      have hxi' : x ∈ closedFamilyStratum o Z i.1 := by
        rw [← hSparts i]
        exact hxi
      have hsub := hstratum_subset j i.1 x hxi' hxj
      have hiJ : i ∈ J := by
        change S.parts i ⊆ P.parts j
        intro y hy
        apply hsub
        simpa only [hSparts i] using hy
      exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hiJ, hxi⟩⟩
    · intro x hx
      rcases mem_iUnion.1 hx with ⟨i, hx⟩
      rcases mem_iUnion.1 hx with ⟨hiJ, hxi⟩
      change S.parts i ⊆ P.parts j at hiJ
      exact hiJ hxi

/-- A finite constructible cover admits a finite stratification by constructible strata refining it. -/
theorem constructible_cover_refined_by_constructible_stratification
    {n : ℕ} (T : Fin n → Set X)
    (hcover : ⋃ k, T k = (univ : Set X))
    (hT : ∀ k, Topology.IsConstructible (T k)) :
    ∃ (κ : Type v) (o : PartialOrder κ) (S : Stratification X κ o),
      Finite κ ∧
        (∀ i, Topology.IsConstructible (S.parts i)) ∧
          (∀ k, IsUnionOfParts (T k) S.toPartition) := by
  classical
  let R : Set (Set X) := {U | IsOpen U ∧ IsRetrocompact U}
  have hR : IsSublattice R := by
    constructor
    · intro U hU V hV
      exact ⟨hU.1.union hV.1, hU.2.union hV.2⟩
    · intro U hU V hV
      exact ⟨hU.1.inter hV.1, hU.2.inter_isOpen hV.2 hV.1⟩
  have hRbot : (∅ : Set X) ∈ R := ⟨isOpen_empty, IsRetrocompact.empty⟩
  have hRtop : (univ : Set X) ∈ R := ⟨isOpen_univ, IsRetrocompact.univ⟩
  have hrep : ∀ k, ∃ d : Finset (R × R),
      T k = d.sup (fun p => (p.1 : Set X) \ p.2) := by
    intro k
    apply (BooleanSubalgebra.mem_closure_iff_sup_sdiff hR hRbot hRtop).mp
    simpa [Topology.IsConstructible, R] using hT k
  choose d hd using hrep
  let D : Finset (R × R) := (Finset.univ : Finset (Fin n)).biUnion d
  have hdD : ∀ k, d k ⊆ D := by
    intro k p hp
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hp⟩
  let e : (D : Set (R × R)) ≃ Fin D.card := D.equivFin
  let g : Fin D.card → R × R := fun q => (e.symm q).1
  have hgmem : ∀ q, g q ∈ D := by
    intro q
    exact (e.symm q).2
  let A := Fin D.card × Bool
  let κ := Set A
  let F : A → Set X := fun a =>
    if a.2 then ((g a.1).1 : Set X)ᶜ else ((g a.1).2 : Set X)ᶜ
  have hFclosed : ∀ a, IsClosed (F a) := by
    rintro ⟨q, b⟩
    cases b
    · exact (g q).2.2.1.isClosed_compl
    · exact (g q).1.2.1.isClosed_compl
  have hFconstructible : ∀ a, Topology.IsConstructible (F a) := by
    rintro ⟨q, b⟩
    cases b
    · exact (g q).2.2.2.isConstructible (g q).2.2.1 |>.compl
    · exact (g q).1.2.2.isConstructible (g q).1.2.1 |>.compl
  let Z : κ → Set X := fun s => ⋂ a ∈ s, F a
  have hZclosed : ∀ s, IsClosed (Z s) := by
    intro s
    exact isClosed_biInter fun a _ => hFclosed a
  have hZconstructible : ∀ s, Topology.IsConstructible (Z s) := by
    intro s
    exact Topology.IsConstructible.biInter (toFinite s) fun a _ => hFconstructible a
  have hZcover : ⋃ s, Z s = (univ : Set X) := by
    apply eq_univ_of_forall
    intro x
    refine mem_iUnion.2 ⟨(∅ : κ), ?_⟩
    change x ∈ ⋂ a ∈ (∅ : Set A), F a
    simp
  have hZfinite : LocallyFinite Z := locallyFinite_of_finite Z
  let o : PartialOrder κ :=
    { le := fun s t => t ⊆ s
      lt := fun s t => t ⊆ s ∧ ¬s ⊆ t
      le_refl := fun _ => subset_rfl
      le_trans := fun _ _ _ hst htu => htu.trans hst
      lt_iff_le_not_ge := by intros; rfl
      le_antisymm := fun s t hst hts => Set.Subset.antisymm hts hst }
  have hinter : ClosedFamilyIntersectionIdentity o Z := by
    letI : PartialOrder κ := o
    intro s t
    ext x
    constructor
    · intro hx
      have hxs0 : x ∈ Z s := hx.1
      have hxt0 : x ∈ Z t := hx.2
      have hxs : ∀ a, a ∈ s → x ∈ F a := by
        simpa only [Z, mem_iInter] using hxs0
      have hxt : ∀ a, a ∈ t → x ∈ F a := by
        simpa only [Z, mem_iInter] using hxt0
      refine mem_iUnion.2 ⟨s ∪ t, ?_⟩
      refine mem_iUnion.2 ⟨?_, ?_⟩
      · constructor
        · change s ⊆ s ∪ t
          exact subset_union_left
        · change t ⊆ s ∪ t
          exact subset_union_right
      · have hxu : ∀ a, a ∈ s ∪ t → x ∈ F a := by
          intro a ha
          rcases ha with ha | ha
          · exact hxs a ha
          · exact hxt a ha
        simpa only [Z, mem_iInter] using hxu
    · intro hx
      rcases mem_iUnion.1 hx with ⟨s', hx⟩
      rcases mem_iUnion.1 hx with ⟨hst, hxs'⟩
      rcases hst with ⟨hss', hts'⟩
      change s ⊆ s' at hss'
      change t ⊆ s' at hts'
      have hxs0 : x ∈ Z s' := hxs'
      have hxs' : ∀ a, a ∈ s' → x ∈ F a := by
        simpa only [Z, mem_iInter] using hxs0
      have hxs : ∀ a, a ∈ s → x ∈ F a := by
        intro a ha
        exact hxs' a (hss' ha)
      have hxt : ∀ a, a ∈ t → x ∈ F a := by
        intro a ha
        exact hxs' a (hts' ha)
      constructor
      · simpa only [Z, mem_iInter] using hxs
      · simpa only [Z, mem_iInter] using hxt
  obtain ⟨S, hSparts, hSfinite⟩ :=
    closed_family_stratification o Z hZclosed hZcover hZfinite hinter
  have hstratum_subset_open (q : Fin D.card) (s : κ) (x : X)
      (hxS : x ∈ closedFamilyStratum o Z s)
      (hxU : x ∈ ((g q).1 : Set X)) :
      closedFamilyStratum o Z s ⊆ ((g q).1 : Set X) := by
    letI : PartialOrder κ := o
    letI : LT κ := o.toPreorder.toLT
    change x ∈ Z s ∧ x ∉ ⋃ k, ⋃ (_ : k < s), Z k at hxS
    have hxZ : x ∈ Z s := hxS.1
    have hxZ' : ∀ a, a ∈ s → x ∈ F a := by
      simpa only [Z, mem_iInter] using hxZ
    have hqabsent : (q, true) ∉ s := by
      intro hq
      have hxcomp : x ∈ ((g q).1 : Set X)ᶜ := by
        simpa [F] using hxZ' (q, true) hq
      exact hxcomp hxU
    intro y hyS
    by_contra hyU
    change y ∈ Z s ∧ y ∉ ⋃ k, ⋃ (_ : k < s), Z k at hyS
    have hyZ : y ∈ Z s := hyS.1
    have hyZ' : ∀ a, a ∈ s → y ∈ F a := by
      simpa only [Z, mem_iInter] using hyZ
    have hinsert : (insert (q, true) s : κ) < s := by
      change s ⊆ insert (q, true) s ∧ ¬insert (q, true) s ⊆ s
      constructor
      · exact subset_insert _ _
      · intro h
        exact hqabsent (h (Set.mem_insert _ _))
    have hyinsert : y ∈ Z (insert (q, true) s) := by
      have hyin : ∀ a, a ∈ insert (q, true) s → y ∈ F a := by
        intro a ha
        rcases ha with rfl | ha
        · simpa [F] using hyU
        · exact hyZ' a ha
      simpa only [Z, mem_iInter] using hyin
    exact False.elim (hyS.2 (mem_iUnion.2 ⟨insert (q, true) s,
      mem_iUnion.2 ⟨hinsert, hyinsert⟩⟩))
  have hstratum_subset_compl (q : Fin D.card) (s : κ) (x : X)
      (hxS : x ∈ closedFamilyStratum o Z s) (hxV : x ∈ ((g q).2 : Set X)ᶜ) :
      closedFamilyStratum o Z s ⊆ ((g q).2 : Set X)ᶜ := by
    letI : PartialOrder κ := o
    letI : LT κ := o.toPreorder.toLT
    change x ∈ Z s ∧ x ∉ ⋃ k, ⋃ (_ : k < s), Z k at hxS
    have hxZ : x ∈ Z s := hxS.1
    have hxZ' : ∀ a, a ∈ s → x ∈ F a := by
      simpa only [Z, mem_iInter] using hxZ
    have hqmem : (q, false) ∈ s := by
      by_contra hq
      have hinsert : (insert (q, false) s : κ) < s := by
        change s ⊆ insert (q, false) s ∧ ¬insert (q, false) s ⊆ s
        constructor
        · exact subset_insert _ _
        · intro h
          exact hq (h (Set.mem_insert _ _))
      have hxinsert : x ∈ Z (insert (q, false) s) := by
        have hxin : ∀ a, a ∈ insert (q, false) s → x ∈ F a := by
          intro a ha
          rcases ha with rfl | ha
          · simpa [F] using hxV
          · exact hxZ' a ha
        simpa only [Z, mem_iInter] using hxin
      exact hxS.2 (mem_iUnion.2 ⟨insert (q, false) s,
        mem_iUnion.2 ⟨hinsert, hxinsert⟩⟩)
    intro y hyS
    change y ∈ Z s ∧ y ∉ ⋃ k, ⋃ (_ : k < s), Z k at hyS
    have hyZ : y ∈ Z s := hyS.1
    have hyZ' : ∀ a, a ∈ s → y ∈ F a := by
      simpa only [Z, mem_iInter] using hyZ
    simpa [F] using hyZ' (q, false) hqmem
  have hstratum_subset_component (q : Fin D.card) (s : κ) (x : X)
      (hxS : x ∈ closedFamilyStratum o Z s)
      (hxcomp : x ∈ ((g q).1 : Set X) \ (g q).2) :
      closedFamilyStratum o Z s ⊆ ((g q).1 : Set X) \ (g q).2 := by
    intro y hyS
    exact ⟨hstratum_subset_open q s x hxS hxcomp.1 hyS,
      hstratum_subset_compl q s x hxS hxcomp.2 hyS⟩
  have hstrictConstructible (i : κ) :
      Topology.IsConstructible (strictBelowUnion o Z i) := by
    letI : PartialOrder κ := o
    letI : LT κ := o.toPreorder.toLT
    have hinner : ∀ k : κ,
        Topology.IsConstructible (⋃ (_ : k < i), Z k) := by
      intro k
      by_cases hki : k < i
      · simpa [hki] using hZconstructible k
      · simpa [hki] using (Topology.IsConstructible.empty :
          Topology.IsConstructible (∅ : Set X))
    simpa only [strictBelowUnion] using
      (Topology.IsConstructible.iUnion
        (f := fun k : κ => ⋃ (_ : k < i), Z k) (fun k => hinner k))
  have hstratumConstructible : ∀ i : ClosedFamilyStratumIndex o Z,
      Topology.IsConstructible (S.parts i) := by
    intro i
    rw [hSparts i]
    simpa [closedFamilyStratum] using
      (hZconstructible i.1).sdiff (hstrictConstructible i.1)
  have hq_of_mem {p : R × R} (hp : p ∈ D) :
      ∃ q : Fin D.card, g q = p := by
    refine ⟨e ⟨p, hp⟩, ?_⟩
    simp [g]
  have hfinsetSup : ∀ (d : Finset (R × R)) (f : R × R → Set X),
      d.sup f = ⋃ p ∈ d, f p := by
    intro d f
    induction d using Finset.cons_induction with
    | empty => simp
    | cons a d ha ih =>
        simp [Finset.sup_cons, ih, sup_eq_union, ha]
  have hUnion : ∀ k, ∃ J : Set (ClosedFamilyStratumIndex o Z),
      T k = ⋃ i ∈ J, S.parts i := by
    intro k
    let J : Set (ClosedFamilyStratumIndex o Z) :=
      {i | S.parts i ⊆ T k}
    refine ⟨J, ?_⟩
    apply Set.Subset.antisymm
    · intro x hxk
      have hTk : T k = ⋃ p ∈ d k, (p.1 : Set X) \ p.2 :=
        (hd k).trans (hfinsetSup (d k) (fun p => (p.1 : Set X) \ p.2))
      rw [hTk] at hxk
      rcases mem_iUnion.1 hxk with ⟨p, hxk⟩
      rcases mem_iUnion.1 hxk with ⟨hp, hxp⟩
      obtain ⟨q, hq⟩ := hq_of_mem (hdD k hp)
      have hxcover : x ∈ ⋃ i, S.parts i := by
        rw [S.iUnion_eq_univ]
        exact mem_univ x
      rcases mem_iUnion.1 hxcover with ⟨i, hxi⟩
      have hxi' : x ∈ closedFamilyStratum o Z i.1 := by
        simpa only [hSparts i] using hxi
      have hxcomp : x ∈ ((g q).1 : Set X) \ (g q).2 := by
        simpa [hq] using hxp
      have hsub := hstratum_subset_component q i.1 x hxi' hxcomp
      have hiJ : i ∈ J := by
        change S.parts i ⊆ T k
        intro y hy
        have hy' : y ∈ closedFamilyStratum o Z i.1 := by
          simpa only [hSparts i] using hy
        have hycomp := hsub hy'
        rw [hTk]
        exact mem_iUnion.2 ⟨p, mem_iUnion.2 ⟨hp, by simpa [hq] using hycomp⟩⟩
      exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hiJ, hxi⟩⟩
    · intro x hx
      rcases mem_iUnion.1 hx with ⟨i, hx⟩
      rcases mem_iUnion.1 hx with ⟨hiJ, hxi⟩
      change S.parts i ⊆ T k at hiJ
      exact hiJ hxi
  let κ' := ULift.{v} (ClosedFamilyStratumIndex o Z)
  let o' : PartialOrder κ' := by
    letI : PartialOrder (ClosedFamilyStratumIndex o Z) :=
      closedFamilyStratumIndexOrder o Z
    exact PartialOrder.lift ULift.down ULift.down_injective
  let Q : Partition X κ' :=
    { parts := fun i => S.parts i.down
      isLocallyClosed := fun i => S.isLocallyClosed i.down
      nonempty := fun i => S.nonempty i.down
      pairwiseDisjoint := by
        intro I J hIJ
        apply S.pairwiseDisjoint
        intro h
        apply hIJ
        exact ULift.down_injective h
      iUnion_eq_univ := by
        apply eq_univ_of_forall
        intro x
        have hx : x ∈ ⋃ i, S.parts i := by
          rw [S.iUnion_eq_univ]
          exact mem_univ x
        rcases mem_iUnion.1 hx with ⟨i, hxi⟩
        exact mem_iUnion.2 ⟨ULift.up i, hxi⟩ }
  let S' : Stratification X κ' o' :=
    { toPartition := Q
      closure_subset_below := by
        letI : PartialOrder (ClosedFamilyStratumIndex o Z) :=
          closedFamilyStratumIndexOrder o Z
        letI : PartialOrder κ' := o'
        intro i
        change closure (S.parts i.down) ⊆
          ⋃ j, ⋃ (_ : j ≤ i), S.parts j.down
        intro x hx
        have hbelow := S.closure_subset_below i.down hx
        change x ∈ ⋃ j, ⋃ (_ : j ≤ i.down), S.parts j at hbelow
        rcases mem_iUnion.1 hbelow with ⟨j, hbelow⟩
        rcases mem_iUnion.1 hbelow with ⟨hji, hxj⟩
        have hji' : ULift.up j ≤ i := by
          change j ≤ i.down
          exact hji
        exact mem_iUnion.2 ⟨ULift.up j,
          mem_iUnion.2 ⟨hji', hxj⟩⟩ }
  refine ⟨κ', o', S', ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · letI : Finite (ClosedFamilyStratumIndex o Z) :=
      Finite.of_injective (fun i : ClosedFamilyStratumIndex o Z => i.1)
        Subtype.val_injective
    exact Finite.of_injective ULift.down ULift.down_injective
  · intro i
    change Topology.IsConstructible (S.parts i.down)
    exact hstratumConstructible i.down
  · intro k
    obtain ⟨J, hJ⟩ := hUnion k
    refine ⟨{i : κ' | i.down ∈ J}, ?_⟩
    rw [hJ]
    apply Set.Subset.antisymm
    · intro x hx
      rcases mem_iUnion.1 hx with ⟨i, hx⟩
      rcases mem_iUnion.1 hx with ⟨hi, hxi⟩
      exact mem_iUnion.2 ⟨ULift.up i,
        mem_iUnion.2 ⟨hi, hxi⟩⟩
    · intro x hx
      rcases mem_iUnion.1 hx with ⟨i, hx⟩
      rcases mem_iUnion.1 hx with ⟨hi, hxi⟩
      exact mem_iUnion.2 ⟨i.down,
        mem_iUnion.2 ⟨hi, hxi⟩⟩

/-- A partition of a closed subset, with all parts viewed as subsets of the ambient space. -/
private structure RelativePartition (W : Set X) (ι : Type v) where
  parts : ι → Set X
  isLocallyClosed : ∀ i, IsLocallyClosed (parts i)
  subset : ∀ i, parts i ⊆ W
  nonempty : ∀ i, (parts i).Nonempty
  pairwiseDisjoint : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (parts i) (parts j)
  iUnion_eq : ⋃ i, parts i = W

/-- A relative partition satisfying the good-stratification incidence condition. -/
private structure RelativeGoodPartition (W : Set X) (ι : Type v)
    extends RelativePartition W ι where
  good : ∀ i j, (parts i ∩ closure (parts j)).Nonempty →
    parts i ⊆ closure (parts j)

/-- In a Noetherian space, every finite partition has a finite good stratification refinement. -/
theorem noetherian_finite_partition_refined_by_finite_good_stratification
    [TopologicalSpace.NoetherianSpace X] {ι : Type v} (P : Partition X ι) [Finite ι] :
    ∃ (κ : Type v) (o : PartialOrder κ) (S : Stratification X κ o),
      Finite κ ∧ IsGoodStratification S.toPartition ∧ S.Refines P := by
  classical
  let hInd : ∀ (W : Closeds X) {ι : Type v} [Finite ι]
      (H : RelativePartition (W : Set X) ι),
        ∃ (κ : Type v) (Q : RelativeGoodPartition (W : Set X) κ) (c : κ → ι),
          Finite κ ∧ (∀ k, Q.parts k ⊆ H.parts (c k)) := by
    intro W
    apply wellFounded_lt.induction W
    intro W ih
    intro ι _ H
    by_cases hW : (W : Set X).Nonempty
    · letI : Fintype ι := Fintype.ofFinite ι
      obtain ⟨x, hxW⟩ := hW
      let y : W := ⟨x, hxW⟩
      let Z : Set W := irreducibleComponent y
      have hZmem : Z ∈ irreducibleComponents W := by
        exact irreducibleComponent_mem_irreducibleComponents y
      let E' : ι → Set W := fun i => Subtype.val ⁻¹' H.parts i
      have hZsub : Z ⊆ ⋃ i, closure (E' i) := by
        intro z hz
        have hzW : (z : X) ∈ (W : Set X) := z.property
        rw [← H.iUnion_eq] at hzW
        rcases mem_iUnion.1 hzW with ⟨i, hzi⟩
        exact mem_iUnion.2 ⟨i, subset_closure hzi⟩
      let T : Finset (Set W) := Finset.univ.image (fun i => closure (E' i))
      have hTclosed : ∀ C ∈ T, IsClosed C := by
        intro C hC
        rcases Finset.mem_image.mp hC with ⟨i, -, rfl⟩
        exact isClosed_closure
      have hZT : Z ⊆ ⋃₀ (T : Set (Set W)) := by
        intro z hz
        rcases mem_iUnion.1 (hZsub hz) with ⟨i, hzi⟩
        have hiT : closure (E' i) ∈ T := by
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        exact mem_sUnion_of_mem hzi hiT
      obtain ⟨C, hCT, hZC⟩ :=
        (isIrreducible_iff_sUnion_isClosed.mp hZmem.1) T hTclosed hZT
      rcases Finset.mem_image.mp hCT with ⟨i₀, -, hCi⟩
      have hZi₀ : Z ⊆ closure (E' i₀) := by
        exact hCi.symm ▸ hZC
      letI : NoetherianSpace W := NoetherianSpace.set (W : Set X)
      obtain ⟨o, hoopen, hone, hoZ⟩ :=
        NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZmem
      obtain ⟨z, hzo⟩ := hone
      obtain ⟨z, hzo, hzi₀⟩ :=
        mem_closure_iff.mp (hZi₀ (hoZ hzo)) o hoopen hzo
      have hE'i₀ : IsLocallyClosed (E' i₀) :=
        (H.isLocallyClosed i₀).preimage continuous_subtype_val
      rcases hE'i₀ with ⟨O, C₀, hO, hC₀, hEeq⟩
      have hzO : z ∈ O := by
        have hzEO : z ∈ O ∩ C₀ := hEeq ▸ hzi₀
        exact hzEO.1
      have hclC₀ : closure (E' i₀) ⊆ C₀ := by
        apply closure_minimal
        intro z hz
        rw [hEeq] at hz
        exact hz.2
        exact hC₀
      let o' : Set W := o ∩ O
      have ho'open : IsOpen o' := hoopen.inter hO
      have ho'nonempty : o'.Nonempty := ⟨z, ⟨hzo, hzO⟩⟩
      have ho'sub : o' ⊆ E' i₀ := by
        intro z hz
        rw [hEeq]
        exact ⟨hz.2, hclC₀ (hZi₀ (hoZ hz.1))⟩
      obtain ⟨O₀, hO₀, hO₀eq⟩ := isOpen_induced_iff.mp ho'open
      let U : Set X := O₀ ∩ (W : Set X)
      have hUsubW : U ⊆ (W : Set X) := by
        intro x hx
        exact hx.2
      have hUnonempty : U.Nonempty := by
        obtain ⟨z, hz⟩ := ho'nonempty
        have hzpre : z ∈ Subtype.val ⁻¹' O₀ := by
          rw [hO₀eq]
          exact hz
        exact ⟨z.1, ⟨hzpre, z.2⟩⟩
      have hUsub : U ⊆ H.parts i₀ := by
        intro x hx
        let z : W := ⟨x, hx.2⟩
        have hzpre : z ∈ Subtype.val ⁻¹' O₀ := hx.1
        have hzo' : z ∈ o' := by
          rw [← hO₀eq]
          exact hzpre
        exact ho'sub hzo'
      have hUlc : IsLocallyClosed U := by
        refine ⟨O₀, (W : Set X), hO₀, W.2, ?_⟩
        rfl
      let R : Set X := (W : Set X) \ U
      have hRclosed : IsClosed R := by
        have hReq : R = (W : Set X) ∩ O₀ᶜ := by
          ext x
          simp [R, U, and_assoc, and_left_comm, and_comm]
        rw [hReq]
        exact W.2.inter hO₀.isClosed_compl
      have hRstrict : (⟨R, hRclosed⟩ : Closeds X) < W := by
        change R ⊂ (W : Set X)
        refine ssubset_iff_subset_ne.mpr ⟨sdiff_subset, ?_⟩
        intro hEq
        obtain ⟨x, hxU⟩ := hUnonempty
        have hxW : x ∈ (W : Set X) := hUsubW hxU
        have hxR : x ∈ R := hEq.symm ▸ hxW
        exact hxR.2 hxU
      let A := ι × Bool
      let E₀ : A → Set X := fun a =>
        (H.parts a.1 ∩ R) ∩ if a.2 then closure U else (closure U)ᶜ
      let κ₀ := {a : A // (E₀ a).Nonempty}
      let E₁ : κ₀ → Set X := fun a => E₀ a.1
      letI : Finite κ₀ :=
        Finite.of_injective (fun a : κ₀ => a.1) Subtype.val_injective
      have hE₁lc : ∀ a, IsLocallyClosed (E₁ a) := by
        intro a
        have hfactor : IsLocallyClosed
            (if a.1.2 then closure U else (closure U)ᶜ) := by
          by_cases hb : a.1.2
          · simpa [hb] using isClosed_closure.isLocallyClosed
          · simpa [hb] using isClosed_closure.isOpen_compl.isLocallyClosed
        simpa [E₁, E₀] using
          ((H.isLocallyClosed a.1.1).inter hRclosed.isLocallyClosed).inter hfactor
      have hE₁subset : ∀ a, E₁ a ⊆ R := by
        intro a x hx
        have hx₀ : x ∈ E₀ a.1 := hx
        change x ∈ (H.parts a.1.1 ∩ R) ∩
          (if a.1.2 then closure U else (closure U)ᶜ) at hx₀
        exact hx₀.1.2
      have hE₁disjoint : ∀ ⦃a b : κ₀⦄, a ≠ b →
          Disjoint (E₁ a) (E₁ b) := by
        intro a b hab
        refine Set.disjoint_left.2 ?_
        intro x hxa hxb
        have hxa0 : x ∈ E₀ a.1 := hxa
        have hxb0 : x ∈ E₀ b.1 := hxb
        change x ∈ (H.parts a.1.1 ∩ R) ∩
          (if a.1.2 then closure U else (closure U)ᶜ) at hxa0
        change x ∈ (H.parts b.1.1 ∩ R) ∩
          (if b.1.2 then closure U else (closure U)ᶜ) at hxb0
        have hxa' : x ∈ H.parts a.1.1 ∩ R := hxa0.1
        have hxb' : x ∈ H.parts b.1.1 ∩ R := hxb0.1
        by_cases hparts : a.1.1 = b.1.1
        · have hbool : a.1.2 ≠ b.1.2 := by
            intro hbool
            apply hab
            apply Subtype.ext
            exact Prod.ext hparts hbool
          by_cases ha : a.1.2
          · have hb : ¬b.1.2 := by
              intro hb
              exact hbool (by simpa [ha, hb])
            have hxc : x ∈ closure U := by
              simpa [ha] using hxa0.2
            have hxn : x ∈ (closure U)ᶜ := by
              simpa [hb] using hxb0.2
            exact hxn hxc
          · have hb : b.1.2 := by
              by_contra hb
              exact hbool (by simpa [ha, hb])
            have hxn : x ∈ (closure U)ᶜ := by
              simpa [ha] using hxa0.2
            have hxc : x ∈ closure U := by
              simpa [hb] using hxb0.2
            exact hxn hxc
        · exact Set.disjoint_left.1 (H.pairwiseDisjoint hparts) hxa'.1 hxb'.1
      have hE₁cover : ⋃ a, E₁ a = R := by
        apply Set.Subset.antisymm
        · intro x hx
          rcases mem_iUnion.1 hx with ⟨a, hxa⟩
          exact hE₁subset a hxa
        · intro x hxR
          have hxW : x ∈ (W : Set X) := hxR.1
          rw [← H.iUnion_eq] at hxW
          rcases mem_iUnion.1 hxW with ⟨i, hxi⟩
          by_cases hxcl : x ∈ closure U
          · let a : A := (i, true)
            have hxa : x ∈ E₀ a := by
              change x ∈ (H.parts i ∩ R) ∩ closure U
              exact ⟨⟨hxi, hxR⟩, hxcl⟩
            exact mem_iUnion.2 ⟨⟨a, ⟨x, hxa⟩⟩, hxa⟩
          · let a : A := (i, false)
            have hxa : x ∈ E₀ a := by
              change x ∈ (H.parts i ∩ R) ∩ (closure U)ᶜ
              exact ⟨⟨hxi, hxR⟩, hxcl⟩
            exact mem_iUnion.2 ⟨⟨a, ⟨x, hxa⟩⟩, hxa⟩
      let H₁ : RelativePartition R κ₀ :=
        { parts := E₁
          isLocallyClosed := hE₁lc
          subset := hE₁subset
          nonempty := fun a => a.2
          pairwiseDisjoint := hE₁disjoint
          iUnion_eq := hE₁cover }
      obtain ⟨K, Q, c, hKfinite, hc⟩ := ih ⟨R, hRclosed⟩ hRstrict H₁
      let κ := Option K
      let c₀ : κ → ι := fun a =>
        match a with
        | none => i₀
        | some k => (c k).1.1
      have hcE₀ : ∀ k, Q.parts k ⊆ E₀ (c k).1 := by
        intro k x hx
        exact hc k hx
      let Q₀ : RelativeGoodPartition (W : Set X) κ :=
          { toRelativePartition :=
              { parts := fun a => match a with
                  | none => U
                  | some k => Q.parts k
                isLocallyClosed := by
                  intro a
                  cases a with
                  | none => exact hUlc
                  | some k => exact Q.isLocallyClosed k
                subset := by
                  intro a
                  cases a with
                  | none => exact hUsubW
                  | some k => exact (Q.subset k).trans sdiff_subset
                nonempty := by
                  intro a
                  cases a with
                  | none => exact hUnonempty
                  | some k => exact Q.nonempty k
                pairwiseDisjoint := by
                  intro a b hab
                  cases a with
                  | none =>
                      cases b with
                      | none => exact False.elim (hab rfl)
                      | some b =>
                          refine Set.disjoint_left.2 ?_
                          intro x hxu hxb
                          exact (Q.subset b hxb).2 hxu
                  | some a =>
                      cases b with
                      | none =>
                          refine Set.disjoint_left.2 ?_
                          intro x hxa hxu
                          exact (Q.subset a hxa).2 hxu
                      | some b =>
                          exact Q.pairwiseDisjoint (by
                            intro hab'
                            apply hab
                            exact congrArg some hab')
                iUnion_eq := by
                  apply Set.Subset.antisymm
                  · intro x hx
                    rcases mem_iUnion.1 hx with ⟨a, hxa⟩
                    cases a with
                    | none => exact hUsubW hxa
                    | some a => exact (Q.subset a hxa).1
                  · intro x hxW
                    by_cases hxu : x ∈ U
                    · exact mem_iUnion.2 ⟨none, hxu⟩
                    · have hxR : x ∈ R := ⟨hxW, hxu⟩
                      have hxR' : x ∈ ⋃ a, Q.parts a := by
                        rw [Q.iUnion_eq]
                        exact hxR
                      rcases mem_iUnion.1 hxR' with ⟨a, hxa⟩
                      exact mem_iUnion.2 ⟨some a, hxa⟩ }
            good := by
              intro a b hab
              cases a with
              | none =>
                  cases b with
                  | none => exact subset_closure
                  | some b =>
                      exfalso
                      rcases hab with ⟨x, hxu, hxb⟩
                      have hxO₀ : x ∈ O₀ := hxu.1
                      have hxcl : x ∉ closure (Q.parts b) := by
                        intro hxcl
                        obtain ⟨y, hyO₀, hyb⟩ :=
                          mem_closure_iff.mp hxcl O₀ hO₀ hxO₀
                        have hyR : y ∈ R := Q.subset b hyb
                        exact hyR.2 ⟨hyO₀, hyR.1⟩
                      exact hxcl hxb
              | some a =>
                  cases b with
                  | none =>
                      by_cases hbool : (c a).1.2
                      · intro x hx
                        have hxE₀ : x ∈ E₀ (c a).1 := hcE₀ a hx
                        change x ∈ (H.parts (c a).1.1 ∩ R) ∩
                          (if (c a).1.2 then closure U else (closure U)ᶜ) at hxE₀
                        simpa [hbool] using hxE₀.2
                      · exfalso
                        rcases hab with ⟨x, hxa, hxucl⟩
                        have hxE₀ : x ∈ E₀ (c a).1 := hcE₀ a hxa
                        change x ∈ (H.parts (c a).1.1 ∩ R) ∩
                          (if (c a).1.2 then closure U else (closure U)ᶜ) at hxE₀
                        have hxnot : x ∈ (closure U)ᶜ := by
                          simpa [hbool] using hxE₀.2
                        exact hxnot hxucl
                  | some b => exact Q.good a b hab }
      have hc₀subset : ∀ a, Q₀.parts a ⊆ H.parts (c₀ a) := by
        intro a x hx
        cases a with
        | none =>
            change x ∈ U at hx
            exact hUsub hx
        | some a =>
            change x ∈ Q.parts a at hx
            exact (hcE₀ a hx).1.1
      letI : Finite K := hKfinite
      exact ⟨κ, Q₀, c₀, inferInstance, hc₀subset⟩
    · have hWempty : (W : Set X) = ∅ := Set.not_nonempty_iff_eq_empty.mp hW
      let κ : Type v := ULift.{v} Empty
      let Q : RelativeGoodPartition (W : Set X) κ :=
        { toRelativePartition :=
            { parts := fun a => nomatch a.down
              isLocallyClosed := by intro a; exact nomatch a.down
              subset := by intro a; exact nomatch a.down
              nonempty := by intro a; exact nomatch a.down
              pairwiseDisjoint := by intro a; exact nomatch a.down
              iUnion_eq := by simpa [hWempty] }
          good := by intro a b; exact nomatch a.down }
      exact ⟨κ, Q, (fun a => nomatch a.down),
        Finite.of_injective ULift.down ULift.down_injective,
        by intro a; exact nomatch a.down⟩
  let H : RelativePartition (univ : Set X) ι :=
    { parts := P.parts
      isLocallyClosed := P.isLocallyClosed
      subset := by intro i; simp
      nonempty := P.nonempty
      pairwiseDisjoint := P.pairwiseDisjoint
      iUnion_eq := P.iUnion_eq_univ }
  obtain ⟨κ, Q, c, hκ, hc⟩ :=
    hInd ⟨(univ : Set X), isClosed_univ⟩ H
  let Rpart : Partition X κ :=
    { parts := Q.parts
      isLocallyClosed := Q.isLocallyClosed
      nonempty := Q.nonempty
      pairwiseDisjoint := Q.pairwiseDisjoint
      iUnion_eq_univ := by simpa using Q.iUnion_eq }
  have hgood : IsGoodStratification Rpart := by
    intro i j h
    exact Q.good i j h
  obtain ⟨o, ho⟩ := exists_partialOrder_of_goodStratification Rpart hgood
  letI : PartialOrder κ := o
  let S : Stratification X κ o :=
    { toPartition := Rpart
      closure_subset_below := by
        intro j x hx
        have hx' : x ∈
            ⋃ i, ⋃ (_ : goodStratificationOrder Rpart i j), Rpart.parts i := by
          rw [← goodStratification_closure_eq_belowUnion Rpart hgood j]
          exact hx
        rcases mem_iUnion.1 hx' with ⟨i, hxi⟩
        rcases mem_iUnion.1 hxi with ⟨hij, hxi⟩
        exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨(ho i j).2 hij, hxi⟩⟩ }
  have hRrefines : Rpart.Refines P := by
    intro j
    let J : Set κ := {k | c k = j}
    refine ⟨J, ?_⟩
    apply Set.Subset.antisymm
    · intro x hxj
      have hxcover : x ∈ ⋃ k, Rpart.parts k := by
        rw [Rpart.iUnion_eq_univ]
        exact mem_univ x
      rcases mem_iUnion.1 hxcover with ⟨k, hxk⟩
      have hxk' : x ∈ H.parts (c k) := hc k hxk
      have hck : c k = j := by
        by_contra hne
        have hxk'' : x ∈ P.parts (c k) := hxk'
        exact Set.disjoint_left.1 (P.pairwiseDisjoint hne) hxk'' hxj
      exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨hck, hxk⟩⟩
    · intro x hx
      rcases mem_iUnion.1 hx with ⟨k, hx⟩
      rcases mem_iUnion.1 hx with ⟨hJ, hxk⟩
      exact (hJ ▸ hc k hxk)
  refine ⟨κ, o, S, hκ, ?_, ?_⟩
  · exact hgood
  · exact hRrefines

end Partitions

end Formalization.Books.Topology.Unit27
