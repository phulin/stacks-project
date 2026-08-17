import Mathlib.Topology.Sober
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Constructions
import Mathlib.Data.Set.Card

/-!
# Topology, Chapter 8: Irreducible components

The source's irreducible spaces, irreducible subsets, and irreducible components
are represented by Mathlib's `IrreducibleSpace`, `IsIrreducible`, and
`irreducibleComponents`.  Generic points, quasi-sober spaces, and Kolmogorov
spaces use Mathlib's `IsGenericPoint`, `QuasiSober`, and `T0Space` APIs.  In
particular, the source's notion of a sober space is recorded as
`QuasiSober X ∧ T0Space X`, which is Mathlib's canonical formulation.
-/

namespace Formalization.Books.Topology.Unit08

open Set Function _root_.Topology TopologicalSpace

universe u v w

section IrreducibleComponents

variable {X : Type u} [TopologicalSpace X]

/-! ## Irreducible spaces and components -/

/- The source's definition of an irreducible space is Mathlib's canonical
   `IrreducibleSpace` class, and its definition of an irreducible component is
   the canonical set `irreducibleComponents X` of maximal irreducible subsets. -/

theorem irreducibleSpace_iff_isIrreducible_univ :
    IrreducibleSpace X ↔ IsIrreducible (Set.univ : Set X) :=
  irreducibleSpace_def X

theorem irreducibleSpace_is_connected [IrreducibleSpace X] : ConnectedSpace X := by
  infer_instance

theorem image_isIrreducible {Y : Type v} [TopologicalSpace Y] {f : X → Y}
    {E : Set X} (hE : IsIrreducible E) (hf : Continuous f) :
    IsIrreducible (f '' E) := by
  exact hE.image f hf.continuousOn

theorem closure_isIrreducible {T : Set X} (hT : IsIrreducible T) :
    IsIrreducible (closure T) := by
  exact hT.closure

theorem irreducibleComponent_isClosed {C : Set X}
    (hC : C ∈ irreducibleComponents X) : IsClosed C := by
  exact isClosed_of_mem_irreducibleComponents C hC

theorem exists_irreducibleComponent_superset {T : Set X} (hT : IsIrreducible T) :
    ∃ C ∈ irreducibleComponents X, T ⊆ C := by
  exact exists_mem_irreducibleComponents_subset_of_isIrreducible T hT

theorem irreducibleComponents_cover :
    ⋃₀ irreducibleComponents X = (Set.univ : Set X) := by
  exact sUnion_irreducibleComponents

/- The source's finite minimal-cover criterion is expressed for an arbitrary
   finite indexing type.  Equality with `Set.range Z` records both directions
   of the assertion that the displayed closed irreducible sets are exactly the
   irreducible components. -/
theorem irreducibleComponents_eq_range_of_finite_cover
    {ι : Type v} [Fintype ι] (Z : ι → Set X)
    (hcover : (⋃ i, Z i) = (Set.univ : Set X))
    (hirr : ∀ i, IsClosed (Z i) ∧ IsIrreducible (Z i))
    (hnored : ∀ i, ¬ Z i ⊆ ⋃ j : {j : ι // j ≠ i}, Z j.1) :
    Set.range Z = irreducibleComponents X := by
  sorry

theorem irreducibleComponents_ncard_le_of_surjective_continuous
    {Y : Type v} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) (hsurj : Surjective f)
    (hX : (irreducibleComponents X).Finite) :
    Set.ncard (irreducibleComponents Y) ≤ Set.ncard (irreducibleComponents X) := by
  sorry

theorem closure_singleton_isIrreducible_closed (x : X) :
    IsIrreducible (closure ({x} : Set X)) ∧ IsClosed (closure ({x} : Set X)) := by
  exact ⟨isIrreducible_singleton.closure, isClosed_closure⟩

/-! ## Generic points and sobriety -/

/- `IsGenericPoint x Z` is Mathlib's definition of a generic point of `Z`.
   The following map is the source's closure-singleton map, with its canonical
   target of irreducible closed subsets. -/

def closureSingletonIrreducibleClosed (x : X) : IrreducibleCloseds X :=
  ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩

theorem closureSingleton_isGenericPoint (x : X) :
    IsGenericPoint x (closure ({x} : Set X)) :=
  isGenericPoint_closure

theorem closureSingleton_injective_iff_t0 :
    Function.Injective (closureSingletonIrreducibleClosed (X := X)) ↔ T0Space X := by
  sorry

theorem closureSingleton_surjective_iff_quasiSober :
    Function.Surjective (closureSingletonIrreducibleClosed (X := X)) ↔ QuasiSober X := by
  sorry

theorem closureSingleton_bijective_iff_sober :
    Function.Bijective (closureSingletonIrreducibleClosed (X := X)) ↔
      QuasiSober X ∧ T0Space X := by
  sorry

theorem quasiSober_and_t0_iff_unique_genericPoint :
    QuasiSober X ∧ T0Space X ↔
      ∀ Z : Set X, IsIrreducible Z → IsClosed Z →
        ∃! x, IsGenericPoint x Z := by
  sorry

/-! ## Subspaces and local covers -/

theorem t0Space_subtype_of_t0 (Y : Set X) [T0Space X] : T0Space Y := by
  infer_instance

theorem quasiSober_subtype_of_isLocallyClosed {Y : Set X}
    (hY : IsLocallyClosed Y) [QuasiSober X] : QuasiSober Y := by
  sorry

theorem sober_subtype_of_isLocallyClosed {Y : Set X}
    (hY : IsLocallyClosed Y) [QuasiSober X] [T0Space X] :
    QuasiSober Y ∧ T0Space Y := by
  exact ⟨quasiSober_subtype_of_isLocallyClosed hY, inferInstance⟩

theorem t0Space_iff_of_locallyClosed_cover
    {ι : Type v} (U : ι → Set X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hU : ∀ i, IsLocallyClosed (U i)) :
    T0Space X ↔ ∀ i, T0Space (U i) := by
  sorry

theorem quasiSober_iff_of_open_cover
    {ι : Type v} (U : ι → Set X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hU : ∀ i, IsOpen (U i)) :
    QuasiSober X ↔ ∀ i, QuasiSober (U i) := by
  sorry

theorem sober_iff_of_open_cover
    {ι : Type v} (U : ι → Set X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hU : ∀ i, IsOpen (U i)) :
    (QuasiSober X ∧ T0Space X) ↔
      ∀ i, QuasiSober (U i) ∧ T0Space (U i) := by
  sorry

/-! ## Examples separating the conditions -/

theorem example_indiscrete_quasiSober_not_kolmogorov
    {A : Type u} [TopologicalSpace A] [IndiscreteTopology A]
    (hA : ¬ Subsingleton A) :
    QuasiSober A ∧
      ¬ T0Space A ∧
        (⋃ a : A, ({a} : Set A)) = (Set.univ : Set A) ∧
          ∀ a : A, DiscreteTopology ({a} : Set A) ∧ T0Space ({a} : Set A) := by
  sorry

theorem example_cofinite_kolmogorov_not_quasiSober
    (A : Type u) [Infinite A] :
    T0Space (CofiniteTopology A) ∧
      ¬ QuasiSober (CofiniteTopology A) ∧
        (⋃ a : CofiniteTopology A, ({a} : Set (CofiniteTopology A))) =
          (Set.univ : Set (CofiniteTopology A)) ∧
          ∀ a : CofiniteTopology A,
            DiscreteTopology ({a} : Set (CofiniteTopology A)) ∧
              QuasiSober ({a} : Set (CofiniteTopology A)) ∧
                T0Space ({a} : Set (CofiniteTopology A)) := by
  sorry

theorem example_sum_not_kolmogorov_not_quasiSober
    {A B : Type u} [TopologicalSpace A] [IndiscreteTopology A]
    [Infinite B] (hA : ¬ Subsingleton A) :
    ¬ T0Space (A ⊕ CofiniteTopology B) ∧
      ¬ QuasiSober (A ⊕ CofiniteTopology B) := by
  sorry

/- The following concrete topology has exactly the closed sets described in
   the source's sober-space example.  `generateFrom` supplies the real
   topological construction; the displayed open/closed characterizations below
   record that this generated topology is the intended one. -/

def soberSubspaceExampleOpenSets (Z : Type u) (z : Z) : Set (Set Z) :=
  {U | U = ∅ ∨ (z ∈ U ∧ (Uᶜ).Finite)}

abbrev soberSubspaceExampleTopology (Z : Type u) (z : Z) : TopologicalSpace Z :=
  TopologicalSpace.generateFrom (soberSubspaceExampleOpenSets Z z)

abbrev SoberSubspaceExample (Z : Type u) (z : Z) :=
  WithTopology Z (soberSubspaceExampleTopology Z z)

def soberSubspaceExamplePoint (Z : Type u) (z : Z) : SoberSubspaceExample Z z :=
  (WithTopology.equiv Z (soberSubspaceExampleTopology Z z)).symm z

theorem soberSubspaceExample_isOpen_iff
    (Z : Type u) (z : Z) {U : Set (SoberSubspaceExample Z z)} :
    IsOpen U ↔
      U = ∅ ∨
        (soberSubspaceExamplePoint Z z ∈ U ∧ (Uᶜ).Finite) := by
  sorry

theorem soberSubspaceExample_isClosed_iff
    (Z : Type u) (z : Z) {U : Set (SoberSubspaceExample Z z)} :
    IsClosed U ↔
      U = Set.univ ∨ U.Finite ∧ soberSubspaceExamplePoint Z z ∉ U := by
  sorry

theorem example_sober_subspace_not_quasiSober
    (Z : Type u) (z : Z) [Infinite Z] :
    (QuasiSober (SoberSubspaceExample Z z) ∧
        T0Space (SoberSubspaceExample Z z)) ∧
      ¬ QuasiSober
        {x : SoberSubspaceExample Z z // x ≠ soberSubspaceExamplePoint Z z} := by
  sorry

theorem hausdorff_iff_disjoint_open_neighborhoods :
    T2Space X ↔
      ∀ ⦃x y : X⦄, x ≠ y →
        ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := by
  constructor
  · intro h x y hxy
    let _ : T2Space X := h
    exact t2_separation hxy
  · intro h
    refine ⟨?_⟩
    intro x y hxy
    exact h hxy

theorem hausdorff_irreducible_iff_singleton [T2Space X] {E : Set X} :
    IsIrreducible E ↔ ∃ x, E = {x} :=
  isIrreducible_iff_singleton

theorem hausdorff_is_sober [T2Space X] :
    QuasiSober X ∧ T0Space X := by
  exact ⟨inferInstance, inferInstance⟩

/-! ## Irreducible fibres and components -/

theorem irreducibleSpace_of_open_map_dense_irreducible_fibres
    {Y : Type v} [TopologicalSpace Y] {f : X → Y}
    (hY : IrreducibleSpace Y) (hf : Continuous f) (hopen : IsOpenMap f)
    {D : Set Y} (hD : Dense D)
    (hfib : ∀ y ∈ D, IsIrreducible (f ⁻¹' ({y} : Set Y))) :
    IrreducibleSpace X := by
  sorry

def irreducibleComponents_equiv_of_open_map_irreducible_fibres
    {Y : Type v} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) (hopen : IsOpenMap f)
    (hfib : ∀ y : Y, IsIrreducible (f ⁻¹' ({y} : Set Y))) :
    irreducibleComponents Y ≃o irreducibleComponents X := by
  have hsurj : Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (hfib y).nonempty
    exact ⟨x, by simpa using hx⟩
  exact irreducibleComponentsEquivOfIsPreirreducibleFiber f hf hopen
    (fun y => (hfib y).isPreirreducible) hsurj

/-! ## Soberification -/

abbrev Soberification (X : Type u) [TopologicalSpace X] :=
  IrreducibleCloseds X

def soberificationOpen (U : Set X) : Set (Soberification X) :=
  {Z | ((Z : Set X) ∩ U).Nonempty}

def soberificationBasis : Set (Set (Soberification X)) :=
  Set.range (soberificationOpen (X := X))

instance soberification_topologicalSpace : TopologicalSpace (Soberification X) :=
  TopologicalSpace.generateFrom (soberificationBasis (X := X))

def soberificationMap : X → Soberification X :=
  fun x => ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩

@[simp] theorem soberificationMap_coe (x : X) :
    (soberificationMap (X := X) x : Set X) = closure ({x} : Set X) :=
  rfl

theorem soberificationMap_continuous :
    Continuous (soberificationMap (X := X)) := by
  sorry

theorem soberification_is_sober :
    QuasiSober (Soberification X) ∧ T0Space (Soberification X) := by
  sorry

def soberificationOpenComap :
    FrameHom (Opens (Soberification X)) (Opens X) :=
  Opens.comap
    ⟨soberificationMap (X := X), soberificationMap_continuous (X := X)⟩

theorem soberificationOpenComap_bijective :
    Function.Bijective (soberificationOpenComap (X := X)) := by
  sorry

theorem soberificationOpenComap_preserves_finite_intersections
    {ι : Type v} [Finite ι] (U : ι → Opens (Soberification X)) :
    soberificationOpenComap (X := X) (⨅ i, U i) =
      ⨅ i, soberificationOpenComap (X := X) (U i) := by
  sorry

theorem soberificationOpenComap_preserves_arbitrary_unions
    {ι : Type v} (U : ι → Opens (Soberification X)) :
    soberificationOpenComap (X := X) (⨆ i, U i) =
      ⨆ i, soberificationOpenComap (X := X) (U i) := by
  sorry

noncomputable def soberificationLift
    {Y : Type v} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) : Soberification X → Y :=
  fun Z => (Z.isIrreducible.image f hf.continuousOn).genericPoint

theorem soberificationLift_continuous
    {Y : Type v} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) :
    Continuous (soberificationLift f hf) := by
  sorry

theorem soberificationLift_comp_map
    {Y : Type v} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) :
    soberificationLift f hf ∘ soberificationMap = f := by
  sorry

theorem soberification_universal
    {Y : Type v} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) :
    ∃! g : Soberification X → Y,
      Continuous g ∧ g ∘ soberificationMap = f := by
  refine ⟨soberificationLift f hf,
    ⟨soberificationLift_continuous f hf, soberificationLift_comp_map f hf⟩, ?_⟩
  intro g hg
  sorry

def soberificationRange : Set (Soberification X) :=
  Set.range (soberificationMap (X := X))

def soberificationRangeMap : X → soberificationRange (X := X) :=
  Set.rangeFactorization (soberificationMap (X := X))

theorem soberificationRangeMap_continuous :
    Continuous (soberificationRangeMap (X := X)) :=
  (soberificationMap_continuous (X := X)).rangeFactorization

theorem soberificationRange_is_kolmogorov :
    T0Space (soberificationRange (X := X)) := by
  let _ : T0Space (Soberification X) := (soberification_is_sober (X := X)).2
  infer_instance

noncomputable def soberificationRangeLift
    {Y : Type v} [TopologicalSpace Y] [T0Space Y]
    (f : X → Y) (_hf : Continuous f) : soberificationRange (X := X) → Y :=
  f ∘ Set.rangeSplitting (soberificationMap (X := X))

theorem soberificationRangeLift_continuous
    {Y : Type v} [TopologicalSpace Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) :
    Continuous (soberificationRangeLift f hf) := by
  sorry

theorem soberificationRangeLift_comp_map
    {Y : Type v} [TopologicalSpace Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) :
    soberificationRangeLift f hf ∘ soberificationRangeMap = f := by
  sorry

theorem soberificationRange_universal
    {Y : Type v} [TopologicalSpace Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) :
    ∃! g : soberificationRange (X := X) → Y,
      Continuous g ∧ g ∘ soberificationRangeMap = f := by
  refine ⟨soberificationRangeLift f hf,
    ⟨soberificationRangeLift_continuous f hf, soberificationRangeLift_comp_map f hf⟩, ?_⟩
  intro g hg
  sorry

/-! ## Removing one component from a connected finite union -/

theorem exists_connected_sUnion_irreducibleComponents_sdiff_singleton
    [ConnectedSpace X] (hX : (irreducibleComponents X).Finite)
    (hn : 1 < Set.ncard (irreducibleComponents X)) :
    ∃ C ∈ irreducibleComponents X,
      IsConnected (⋃₀ (irreducibleComponents X \ {C})) := by
  sorry

end IrreducibleComponents

end Formalization.Books.Topology.Unit08
