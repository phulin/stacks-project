import Mathlib.Topology.Sober
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Constructions
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Lattice

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
  have hfinite : (Set.range Z).Finite := Set.finite_range Z
  have hfinite_cover : ∀ {T : Set X}, IsIrreducible T →
      T ⊆ ⋃₀ (Set.range Z) → ∃ i, T ⊆ Z i := by
    intro T hT hTcover
    obtain ⟨W, hW, hTW⟩ :=
      isIrreducible_iff_sUnion_isClosed.mp hT hfinite.toFinset
        (fun W hW => by
          obtain ⟨i, rfl⟩ := hfinite.mem_toFinset.mp hW
          exact (hirr i).1)
        (hfinite.coe_toFinset.symm ▸ hTcover)
    obtain ⟨i, rfl⟩ := hfinite.mem_toFinset.mp hW
    exact ⟨i, hTW⟩
  apply Set.Subset.antisymm
  · intro C hC
    obtain ⟨i, rfl⟩ := hC
    apply maximal_subset_iff'.2
    refine ⟨(hirr i).2, ?_⟩
    intro T hT hZiT
    obtain ⟨j, hTj⟩ := hfinite_cover hT (by
      rw [sUnion_range, hcover]
      exact subset_univ T)
    have hZij : Z i ⊆ Z j := hZiT.trans hTj
    by_cases hij : j = i
    · simpa [hij] using hTj
    · exact ((hnored i) (by
        intro x hx
        exact mem_iUnion.2 ⟨⟨j, hij⟩, hZij hx⟩)).elim
  · intro C hC
    obtain ⟨i, hCi⟩ := hfinite_cover hC.1 (by
      rw [sUnion_range, hcover]
      exact subset_univ C)
    exact ⟨i, (hC.eq_of_subset (hirr i).2 hCi).symm⟩

theorem irreducibleComponents_ncard_le_of_surjective_continuous
    {Y : Type v} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) (hsurj : Surjective f)
    (hX : (irreducibleComponents X).Finite) :
    Set.ncard (irreducibleComponents Y) ≤ Set.ncard (irreducibleComponents X) := by
  classical
  have hq : ∀ C : irreducibleComponents X, ∃ D ∈ irreducibleComponents Y,
      f '' (C : Set X) ⊆ D := by
    intro C
    exact exists_mem_irreducibleComponents_subset_of_isIrreducible
      (f '' (C : Set X)) (C.2.1.image f hf.continuousOn)
  choose q hqmem hqsub using hq
  let g : irreducibleComponents X → irreducibleComponents Y :=
    fun C => ⟨q C, hqmem C⟩
  have hqcover : ⋃₀ (Set.range q) = (Set.univ : Set Y) := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨C, hC, hxC⟩ := mem_sUnion.mp (by
      rw [sUnion_irreducibleComponents (X := X)]
      exact mem_univ x)
    exact mem_sUnion_of_mem (hqsub ⟨C, hC⟩ ⟨x, hxC, rfl⟩)
      ⟨⟨C, hC⟩, rfl⟩
  have hqfinite : (Set.range q).Finite :=
    @Set.finite_range _ _ q hX.fintype.finite
  have hg : Surjective g := by
    intro D
    have hD : (D : Set Y) ∈ Set.range q := by
      apply mem_of_subset_sUnion_irreducibleComponents (D : Set Y) D.2
        (Set.range q) hqfinite
      · intro E hE
        obtain ⟨C, rfl⟩ := hE
        exact hqmem C
      · rw [hqcover]
        exact subset_univ (D : Set Y)
    obtain ⟨C, hCD⟩ := hD
    refine ⟨C, ?_⟩
    exact Subtype.ext hCD
  have hcard : Nat.card (irreducibleComponents Y) ≤
      Nat.card (irreducibleComponents X) :=
    @Nat.card_le_card_of_surjective _ _ hX.fintype.finite g hg
  simpa only [Nat.card_coe_set_eq] using hcard

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
  constructor
  · intro h
    refine ⟨?_⟩
    intro x y hxy
    apply h
    apply TopologicalSpace.IrreducibleCloseds.ext
    change closure ({x} : Set X) = closure ({y} : Set X)
    exact inseparable_iff_closure_eq.mp hxy
  · intro h x y hxy
    have hcl : closure ({x} : Set X) = closure ({y} : Set X) := by
      have hc := congrArg (fun Z : IrreducibleCloseds X => (Z : Set X)) hxy
      simpa [closureSingletonIrreducibleClosed] using hc
    exact h.t0 (inseparable_iff_closure_eq.mpr hcl)

theorem closureSingleton_surjective_iff_quasiSober :
    Function.Surjective (closureSingletonIrreducibleClosed (X := X)) ↔ QuasiSober X := by
  constructor
  · intro h
    refine ⟨?_⟩
    intro S hS hC
    obtain ⟨x, hx⟩ := h ⟨S, hS, hC⟩
    refine ⟨x, ?_⟩
    change closure ({x} : Set X) = S
    have hc := congrArg (fun Z : IrreducibleCloseds X => (Z : Set X)) hx
    simpa [closureSingletonIrreducibleClosed] using hc
  · intro h Z
    obtain ⟨x, hx⟩ := h.sober Z.isIrreducible Z.isClosed
    exact ⟨x, TopologicalSpace.IrreducibleCloseds.ext hx.def⟩

theorem closureSingleton_bijective_iff_sober :
    Function.Bijective (closureSingletonIrreducibleClosed (X := X)) ↔
      QuasiSober X ∧ T0Space X := by
  constructor
  · intro h
    exact ⟨closureSingleton_surjective_iff_quasiSober.mp h.2,
      closureSingleton_injective_iff_t0.mp h.1⟩
  · rintro ⟨hQ, hT⟩
    exact ⟨closureSingleton_injective_iff_t0.mpr hT,
      closureSingleton_surjective_iff_quasiSober.mpr hQ⟩

theorem quasiSober_and_t0_iff_unique_genericPoint :
    QuasiSober X ∧ T0Space X ↔
      ∀ Z : Set X, IsIrreducible Z → IsClosed Z →
        ∃! x, IsGenericPoint x Z := by
  constructor
  · rintro ⟨hQ, hT⟩ Z hZ hC
    obtain ⟨x, hx⟩ := hQ.sober hZ hC
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact (t0Space_iff_inseparable X).mp hT y x
      (inseparable_iff_closure_eq.mpr (hy.def.trans hx.def.symm))
  · intro h
    refine ⟨⟨fun {Z} hZ hC => (h Z hZ hC).exists⟩, ?_⟩
    refine ⟨fun {x y} hxy => ?_⟩
    have hgen : IsGenericPoint y (closure ({x} : Set X)) := by
      change closure ({y} : Set X) = closure ({x} : Set X)
      exact (inseparable_iff_closure_eq.mp hxy).symm
    exact (h _ isIrreducible_singleton.closure isClosed_closure).unique
      isGenericPoint_closure hgen

/-! ## Subspaces and local covers -/

theorem t0Space_subtype_of_t0 (Y : Set X) [T0Space X] : T0Space Y := by
  infer_instance

theorem quasiSober_subtype_of_isLocallyClosed {Y : Set X}
    (hY : IsLocallyClosed Y) [QuasiSober X] : QuasiSober Y := by
  rcases hY with ⟨U, Z, hU, hZ, hYZ⟩
  subst Y
  let _ : QuasiSober U := Topology.IsOpenEmbedding.quasiSober hU.isOpenEmbedding_subtypeVal
  refine QuasiSober.of_subset (W := U) ?_ inter_subset_left
  rw [Subtype.preimage_coe_self_inter]
  exact hZ.preimage continuous_subtype_val

theorem sober_subtype_of_isLocallyClosed {Y : Set X}
    (hY : IsLocallyClosed Y) [QuasiSober X] [T0Space X] :
    QuasiSober Y ∧ T0Space Y := by
  exact ⟨quasiSober_subtype_of_isLocallyClosed hY, inferInstance⟩

theorem t0Space_iff_of_locallyClosed_cover
    {ι : Type v} (U : ι → Set X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hU : ∀ i, IsLocallyClosed (U i)) :
    T0Space X ↔ ∀ i, T0Space (U i) := by
  constructor
  · intro h i
    exact t0Space_subtype_of_t0 (U i)
  · intro h
    refine ⟨?_⟩
    intro x y hxy
    obtain ⟨i, hxi⟩ := hcover x
    obtain ⟨O, Z, hO, hZ, hUi⟩ := hU i
    have hxO : x ∈ O := hUi ▸ hxi |>.1
    have hxZ : x ∈ Z := hUi ▸ hxi |>.2
    have hyO : y ∈ O := by
      rcases
          (mem_closure_iff.mp (inseparable_iff_mem_closure.mp hxy).1 O hO hxO) with
        ⟨w, hwO, rfl⟩
      exact hwO
    have hclZ : closure ({x} : Set X) ⊆ Z :=
      hZ.closure_subset_iff.mpr (singleton_subset_iff.mpr hxZ)
    have hyZ : y ∈ Z :=
      hclZ (inseparable_iff_mem_closure.mp hxy).2
    have hyi : y ∈ U i := hUi ▸ ⟨hyO, hyZ⟩
    exact congrArg Subtype.val
      ((t0Space_iff_inseparable (U i)).mp (h i) ⟨x, hxi⟩ ⟨y, hyi⟩
        ((subtype_inseparable_iff _ _).2 hxy))

theorem quasiSober_iff_of_open_cover
    {ι : Type v} (U : ι → Set X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hU : ∀ i, IsOpen (U i)) :
    QuasiSober X ↔ ∀ i, QuasiSober (U i) := by
  let V : ι → Opens X := fun i => ⟨U i, hU i⟩
  have hV : TopologicalSpace.IsOpenCover V := by
    refine TopologicalSpace.IsOpenCover.of_sets hU ?_
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hxi⟩ := hcover x
    exact Set.mem_iUnion.2 ⟨i, hxi⟩
  change QuasiSober X ↔ ∀ i, QuasiSober (V i)
  exact hV.quasiSober_iff_forall

theorem sober_iff_of_open_cover
    {ι : Type v} (U : ι → Set X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hU : ∀ i, IsOpen (U i)) :
    (QuasiSober X ∧ T0Space X) ↔
      ∀ i, QuasiSober (U i) ∧ T0Space (U i) := by
  rw [quasiSober_iff_of_open_cover U hcover hU,
    t0Space_iff_of_locallyClosed_cover U hcover (fun i => (hU i).isLocallyClosed)]
  simp only [forall_and]

/-! ## Examples separating the conditions -/

theorem example_indiscrete_quasiSober_not_kolmogorov
    {A : Type u} [TopologicalSpace A] [IndiscreteTopology A]
    (hA : ¬ Subsingleton A) :
    QuasiSober A ∧
      ¬ T0Space A ∧
        (⋃ a : A, ({a} : Set A)) = (Set.univ : Set A) ∧
          ∀ a : A, DiscreteTopology ({a} : Set A) ∧ T0Space ({a} : Set A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    intro S hS hC
    rcases (IndiscreteTopology.isClosed_iff S).mp hC with rfl | rfl
    · exact hS.nonempty.elim fun x hx => hx.elim
    · obtain ⟨x⟩ := hS.nonempty
      exact ⟨x, closure_indiscrete (singleton_nonempty x)⟩
  · intro hT
    apply hA
    refine ⟨?_⟩
    intro x y
    exact (t0Space_iff_inseparable A).mp hT x y (Inseparable.all x y)
  · ext x
    simp
  · intro a
    let _ : Subsingleton ({a} : Set A) :=
      ⟨fun x y =>
        Subtype.ext
          ((Set.mem_singleton_iff.mp x.property).trans
            (Set.mem_singleton_iff.mp y.property).symm)⟩
    exact ⟨inferInstance, inferInstance⟩

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
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · intro hQ
    have hI : IsIrreducible (Set.univ : Set (CofiniteTopology A)) :=
      IrreducibleSpace.isIrreducible_univ _
    obtain ⟨x, hx⟩ := hQ.sober hI isClosed_univ
    have hfin : (Set.univ : Set (CofiniteTopology A)).Finite := by
      rw [← hx.def, closure_singleton]
      exact Set.toFinite _
    exact Set.infinite_univ hfin
  · ext x
    simp
  · intro a
    let _ : Subsingleton ({a} : Set (CofiniteTopology A)) :=
      ⟨fun x y =>
        Subtype.ext
          ((Set.mem_singleton_iff.mp x.property).trans
            (Set.mem_singleton_iff.mp y.property).symm)⟩
    exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem example_sum_not_kolmogorov_not_quasiSober
    {A B : Type u} [TopologicalSpace A] [IndiscreteTopology A]
    [Infinite B] (hA : ¬ Subsingleton A) :
    ¬ T0Space (A ⊕ CofiniteTopology B) ∧
      ¬ QuasiSober (A ⊕ CofiniteTopology B) := by
  constructor
  · intro hT
    apply hA
    let _ : T0Space (A ⊕ CofiniteTopology B) := hT
    let _ : T0Space A :=
      (Topology.IsEmbedding.inl (X := A) (Y := CofiniteTopology B)).t0Space
    exact ⟨fun x y =>
      (t0Space_iff_inseparable A).mp inferInstance x y (Inseparable.all x y)⟩
  · intro hQ
    let _ : QuasiSober (A ⊕ CofiniteTopology B) := hQ
    have hB : QuasiSober (CofiniteTopology B) :=
      Topology.IsOpenEmbedding.quasiSober
        (Topology.IsOpenEmbedding.inr (X := A) (Y := CofiniteTopology B))
    exact (example_cofinite_kolmogorov_not_quasiSober B).2.1 hB

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
  have hinter : ∀ {V W : Set Z},
      V ∈ soberSubspaceExampleOpenSets Z z →
        W ∈ soberSubspaceExampleOpenSets Z z →
          V ∩ W ∈ soberSubspaceExampleOpenSets Z z := by
    intro V W hV hW
    change V = ∅ ∨ (z ∈ V ∧ Vᶜ.Finite) at hV
    change W = ∅ ∨ (z ∈ W ∧ Wᶜ.Finite) at hW
    change V ∩ W = ∅ ∨ (z ∈ V ∩ W ∧ (V ∩ W)ᶜ.Finite)
    rcases hV with rfl | ⟨hzV, hVfin⟩
    · simp
    rcases hW with rfl | ⟨hzW, hWfin⟩
    · simp
    exact Or.inr ⟨⟨hzV, hzW⟩, by simpa only [compl_inter] using hVfin.union hWfin⟩
  have hsUnion : ∀ (𝒱 : Set (Set Z)),
      (∀ V ∈ 𝒱, V ∈ soberSubspaceExampleOpenSets Z z) →
        ⋃₀ 𝒱 ∈ soberSubspaceExampleOpenSets Z z := by
    intro 𝒱 h𝒱
    by_cases hnon : ∃ V ∈ 𝒱, V.Nonempty
    · obtain ⟨V, hV𝒱, hVne⟩ := hnon
      rcases h𝒱 V hV𝒱 with hVempty | ⟨hzV, hVfin⟩
      · exact ((not_nonempty_iff_eq_empty.2 rfl) (hVempty ▸ hVne)).elim
      · change ⋃₀ 𝒱 = ∅ ∨ (z ∈ ⋃₀ 𝒱 ∧ (⋃₀ 𝒱)ᶜ.Finite)
        exact Or.inr ⟨mem_sUnion_of_mem hzV hV𝒱,
          hVfin.subset (compl_subset_compl.mpr (subset_sUnion_of_mem hV𝒱))⟩
    · left
      rw [sUnion_eq_empty]
      intro V hV𝒱
      exact not_nonempty_iff_eq_empty.mp fun hVne => hnon ⟨V, hV𝒱, hVne⟩
  have hgen (V : Set Z) :
      IsOpen[soberSubspaceExampleTopology Z z] V ↔
        V = ∅ ∨ (z ∈ V ∧ Vᶜ.Finite) := by
    constructor
    · intro hV
      change TopologicalSpace.GenerateOpen (soberSubspaceExampleOpenSets Z z) V at hV
      induction hV with
      | basic V hV => exact hV
      | univ => exact Or.inr ⟨mem_univ _, by simp⟩
      | inter V W hV hW ihV ihW => exact hinter ihV ihW
      | sUnion 𝒱 h𝒱 ih => exact hsUnion 𝒱 (fun V hV𝒱 => ih V hV𝒱)
    · intro hV
      change TopologicalSpace.GenerateOpen (soberSubspaceExampleOpenSets Z z) V
      exact .basic V hV
  rw [WithTopology.isOpen_iff, hgen]
  constructor
  · rintro (hU | ⟨hzU, hUfin⟩)
    · left
      apply Set.Subset.antisymm
      · intro x hx
        have hxpre :
            WithTopology.ofTopology x ∈
              WithTopology.toTopology (soberSubspaceExampleTopology Z z) ⁻¹' U := by
          change WithTopology.toTopology (soberSubspaceExampleTopology Z z)
              (WithTopology.ofTopology x) ∈ U
          simpa only [WithTopology.toTopology_ofTopology] using hx
        have hxempty :
            WithTopology.ofTopology x ∈ (∅ : Set Z) := hU ▸ hxpre
        exact hxempty.elim
      · intro x hx
        exact hx.elim
    · right
      refine ⟨hzU, ?_⟩
      have hUfin' :
          (WithTopology.toTopology (soberSubspaceExampleTopology Z z) ⁻¹' Uᶜ).Finite := by
        simpa only [preimage_compl] using hUfin
      exact hUfin'.of_preimage
        (WithTopology.toTopology_surjective (soberSubspaceExampleTopology Z z))
  · rintro (hU | ⟨hzU, hUfin⟩)
    · left
      ext x
      constructor
      · intro hx
        rw [hU] at hx
        exact hx
      · intro hx
        exact hx.elim
    · right
      refine ⟨hzU, ?_⟩
      simpa only [preimage_compl] using
        Set.Finite.preimage
          (WithTopology.toTopology_injective (soberSubspaceExampleTopology Z z)).injOn hUfin

theorem soberSubspaceExample_isClosed_iff
    (Z : Type u) (z : Z) {U : Set (SoberSubspaceExample Z z)} :
    IsClosed U ↔
      U = Set.univ ∨ U.Finite ∧ soberSubspaceExamplePoint Z z ∉ U := by
  rw [← isOpen_compl_iff, soberSubspaceExample_isOpen_iff]
  simp [mem_compl_iff, and_comm]

theorem example_sober_subspace_not_quasiSober
    (Z : Type u) (z : Z) [Infinite Z] :
    (QuasiSober (SoberSubspaceExample Z z) ∧
        T0Space (SoberSubspaceExample Z z)) ∧
      ¬ QuasiSober
        {x : SoberSubspaceExample Z z // x ≠ soberSubspaceExamplePoint Z z} := by
  have hQ : QuasiSober (SoberSubspaceExample Z z) := by
    refine ⟨?_⟩
    intro S hS hC
    rcases (soberSubspaceExample_isClosed_iff Z z).mp hC with rfl | ⟨hSfin, hzp⟩
    · refine ⟨soberSubspaceExamplePoint Z z, ?_⟩
      apply Set.eq_univ_of_forall
      intro x
      rw [mem_closure_iff]
      intro V hV hxV
      rcases (soberSubspaceExample_isOpen_iff Z z).mp hV with hVempty | ⟨hpV, _⟩
      · exact (hVempty ▸ hxV).elim
      · exact ⟨soberSubspaceExamplePoint Z z, hpV, rfl⟩
    · have hSsub : S.Subsingleton := by
        intro a ha b hb
        by_contra hab'
        have hUa : IsOpen ((S \ {a})ᶜ) := by
          apply (soberSubspaceExample_isOpen_iff Z z).mpr
          refine Or.inr ⟨?_, ?_⟩
          · intro hpa
            exact hzp hpa.1
          · simpa only [compl_compl] using hSfin.subset sdiff_subset
        have hUb : IsOpen ((S \ {b})ᶜ) := by
          apply (soberSubspaceExample_isOpen_iff Z z).mpr
          refine Or.inr ⟨?_, ?_⟩
          · intro hpb
            exact hzp hpb.1
          · simpa only [compl_compl] using hSfin.subset sdiff_subset
        obtain ⟨c, hcS, hcUa, hcUb⟩ := hS.isPreirreducible
          ((S \ {a})ᶜ) ((S \ {b})ᶜ) hUa hUb
          ⟨a, ha, by
            change a ∉ S \ {a}
            intro ha'
            exact ha'.2 (by simp)⟩
          ⟨b, hb, by
            change b ∉ S \ {b}
            intro hb'
            exact hb'.2 (by simp)⟩
        change c ∉ S \ {a} at hcUa
        change c ∉ S \ {b} at hcUb
        have hca : c = a := by
          apply Set.mem_singleton_iff.mp
          by_contra hca'
          exact hcUa ⟨hcS, hca'⟩
        have hcb : c = b := by
          apply Set.mem_singleton_iff.mp
          by_contra hcb'
          exact hcUb ⟨hcS, hcb'⟩
        exact hab' (hca.symm.trans hcb)
      obtain ⟨x, hx⟩ := hS.nonempty
      have hS_eq : S = {x} :=
        Set.Subset.antisymm (fun y hy => hSsub hy hx) (singleton_subset_iff.mpr hx)
      have hxclosed : IsClosed ({x} : Set (SoberSubspaceExample Z z)) := by
        apply (soberSubspaceExample_isClosed_iff Z z).mpr
        refine Or.inr ⟨finite_singleton x, ?_⟩
        intro hpx
        apply hzp
        rw [Set.mem_singleton_iff] at hpx
        rw [hpx]
        exact hx
      refine ⟨x, ?_⟩
      rw [hS_eq]
      exact hxclosed.closure_eq
  have hT : T0Space (SoberSubspaceExample Z z) := by
    rw [t0Space_iff_exists_isOpen_xor_mem]
    intro x y hxy
    by_cases hy : y = soberSubspaceExamplePoint Z z
    · have hxne : x ≠ soberSubspaceExamplePoint Z z := by
        intro hx
        exact hxy (hx.trans hy.symm)
      have hpnot : soberSubspaceExamplePoint Z z ∉ ({x} : Set (SoberSubspaceExample Z z)) := by
        intro hpx
        exact hxne (Set.mem_singleton_iff.mp hpx).symm
      refine ⟨({x} : Set (SoberSubspaceExample Z z))ᶜ, ?_, ?_⟩
      · apply (soberSubspaceExample_isOpen_iff Z z).mpr
        exact Or.inr ⟨hpnot, by simpa only [compl_compl] using finite_singleton x⟩
      · refine Or.inr ⟨?_, ?_⟩
        · rw [hy]
          simpa only [mem_compl_iff] using hpnot
        · simp
    · have hpnot : soberSubspaceExamplePoint Z z ∉ ({y} : Set (SoberSubspaceExample Z z)) := by
        intro hpy
        exact hy (Set.mem_singleton_iff.mp hpy).symm
      refine ⟨({y} : Set (SoberSubspaceExample Z z))ᶜ, ?_, ?_⟩
      · apply (soberSubspaceExample_isOpen_iff Z z).mpr
        exact Or.inr ⟨hpnot, by simpa only [compl_compl] using finite_singleton y⟩
      · exact Or.inl ⟨by simpa only [mem_compl_iff, mem_singleton_iff] using hxy, by simp⟩
  refine ⟨⟨hQ, hT⟩, ?_⟩
  have hYne : ∃ q : SoberSubspaceExample Z z,
      q ≠ soberSubspaceExamplePoint Z z := by
    obtain ⟨q, -, hq⟩ := Set.infinite_univ.exists_notMem_finite
      (finite_singleton (soberSubspaceExamplePoint Z z))
    exact ⟨q, by
      intro hq'
      exact hq (by simp [hq'])⟩
  have hI : IsIrreducible
      (Set.univ : Set {x : SoberSubspaceExample Z z //
        x ≠ soberSubspaceExamplePoint Z z}) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨q, hq⟩ := hYne
      exact ⟨⟨q, hq⟩, mem_univ _⟩
    intro u v hu hv hu' hv'
    obtain ⟨U, hU, hUeq⟩ := (Topology.IsInducing.subtypeVal.isOpen_iff).mp hu
    obtain ⟨V, hV, hVeq⟩ := (Topology.IsInducing.subtypeVal.isOpen_iff).mp hv
    have hu_ne : u.Nonempty := by simpa only [univ_inter] using hu'
    have hv_ne : v.Nonempty := by simpa only [univ_inter] using hv'
    have hU_ne : U.Nonempty := by
      obtain ⟨x, hx⟩ := hu_ne
      refine ⟨x.1, ?_⟩
      have hx' : x ∈ Subtype.val ⁻¹' U := by
        exact hUeq.symm ▸ hx
      exact hx'
    have hV_ne : V.Nonempty := by
      obtain ⟨x, hx⟩ := hv_ne
      refine ⟨x.1, ?_⟩
      have hx' : x ∈ Subtype.val ⁻¹' V := by
        exact hVeq.symm ▸ hx
      exact hx'
    obtain ⟨hpU, hUfin⟩ :=
      ((soberSubspaceExample_isOpen_iff Z z).mp hU).resolve_left
        (Set.nonempty_iff_ne_empty.mp hU_ne)
    obtain ⟨hpV, hVfin⟩ :=
      ((soberSubspaceExample_isOpen_iff Z z).mp hV).resolve_left
        (Set.nonempty_iff_ne_empty.mp hV_ne)
    obtain ⟨q, hqU, hqnot⟩ := Set.infinite_univ.exists_notMem_finite
      ((finite_singleton (soberSubspaceExamplePoint Z z)).union
        (hUfin.union hVfin))
    have hqp : q ≠ soberSubspaceExamplePoint Z z := by
      intro hq
      apply hqnot
      simp [hq]
    have hqU' : q ∈ U := by
      by_contra hq
      apply hqnot
      simp [hq]
    have hqV' : q ∈ V := by
      by_contra hq
      apply hqnot
      simp [hq]
    let q' : {x : SoberSubspaceExample Z z //
        x ≠ soberSubspaceExamplePoint Z z} := ⟨q, hqp⟩
    have hq'u : q' ∈ u := by
      have hq'pre : q' ∈ Subtype.val ⁻¹' U := by
        change (q' : SoberSubspaceExample Z z) ∈ U
        simpa [q'] using hqU'
      exact hUeq ▸ hq'pre
    have hq'v : q' ∈ v := by
      have hq'pre : q' ∈ Subtype.val ⁻¹' V := by
        change (q' : SoberSubspaceExample Z z) ∈ V
        simpa [q'] using hqV'
      exact hVeq ▸ hq'pre
    exact ⟨q', ⟨mem_univ _, ⟨hq'u, hq'v⟩⟩⟩
  intro hY
  obtain ⟨x, hx⟩ := hY.sober hI isClosed_univ
  have hxclosed : IsClosed ({(x : SoberSubspaceExample Z z)} :
      Set (SoberSubspaceExample Z z)) := by
    apply (soberSubspaceExample_isClosed_iff Z z).mpr
    refine Or.inr ⟨finite_singleton (x : SoberSubspaceExample Z z), ?_⟩
    intro hpx
    exact x.property (Set.mem_singleton_iff.mp hpx).symm
  have hxclosed' : IsClosed ({x} : Set {x : SoberSubspaceExample Z z //
      x ≠ soberSubspaceExamplePoint Z z}) := by
    have hpre : Subtype.val ⁻¹' ({(x : SoberSubspaceExample Z z)} :
        Set (SoberSubspaceExample Z z)) = {x} := by
      ext y
      constructor
      · intro hy
        exact Subtype.ext hy
      · intro hy
        have hy' : y = x := Set.mem_singleton_iff.mp hy
        exact congrArg Subtype.val hy'
    rw [← hpre]
    exact hxclosed.preimage continuous_subtype_val
  have hxu : (Set.univ : Set {x : SoberSubspaceExample Z z //
      x ≠ soberSubspaceExamplePoint Z z}) = {x} :=
    hx.def.symm.trans hxclosed'.closure_eq
  obtain ⟨q, hqU, hqnot⟩ := Set.infinite_univ.exists_notMem_finite
    ((finite_singleton (soberSubspaceExamplePoint Z z)).union
      (finite_singleton (x : SoberSubspaceExample Z z)))
  have hqx : q ≠ (x : SoberSubspaceExample Z z) := by
    intro hq
    apply hqnot
    simp [hq]
  have hqp : q ≠ soberSubspaceExamplePoint Z z := by
    intro hq
    apply hqnot
    simp [hq]
  let q' : {x : SoberSubspaceExample Z z //
      x ≠ soberSubspaceExamplePoint Z z} := ⟨q, hqp⟩
  have hq'x : q' = x := by
    apply Set.mem_singleton_iff.mp
    rw [← hxu]
    exact mem_univ _
  apply hqx
  have := congrArg (fun y : {x : SoberSubspaceExample Z z //
      x ≠ soberSubspaceExamplePoint Z z} => (y : SoberSubspaceExample Z z)) hq'x
  simpa [q'] using this

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
  let _ := hf
  let _ : IrreducibleSpace Y := hY
  have hpre : IsPreirreducible (Set.univ : Set X) := by
    intro U V hU hV hU' hV'
    have hU_ne : U.Nonempty := by simpa only [univ_inter] using hU'
    have hV_ne : V.Nonempty := by simpa only [univ_inter] using hV'
    have himage : (f '' U ∩ f '' V).Nonempty :=
      nonempty_preirreducible_inter (hopen U hU) (hopen V hV)
        (Set.image_nonempty.mpr hU_ne) (Set.image_nonempty.mpr hV_ne)
    obtain ⟨y, hyUV, hyD⟩ :=
      hD.inter_open_nonempty (f '' U ∩ f '' V)
        ((hopen U hU).inter (hopen V hV)) himage
    obtain ⟨⟨x, hxU, hfx⟩, ⟨x', hxV, hfx'⟩⟩ := hyUV
    let F : Set X := f ⁻¹' ({y} : Set Y)
    have hxF : x ∈ F := by
      change f x ∈ ({y} : Set Y)
      exact hfx ▸ mem_singleton y
    have hx'F : x' ∈ F := by
      change f x' ∈ ({y} : Set Y)
      exact hfx' ▸ mem_singleton y
    obtain ⟨w, hwF, hwUV⟩ := (hfib y hyD).isPreirreducible U V hU hV
      ⟨x, hxF, hxU⟩ ⟨x', hx'F, hxV⟩
    exact ⟨w, ⟨mem_univ _, hwUV⟩⟩
  have hnonempty : Nonempty X := by
    obtain ⟨y, hyD⟩ := hD.nonempty
    obtain ⟨x, _⟩ := (hfib y hyD).nonempty
    exact ⟨x⟩
  exact { isPreirreducible_univ := hpre, toNonempty := hnonempty }

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
  Set.range (fun U : Opens X => soberificationOpen (U : Set X))

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
  classical
  exact (letI := Fintype.ofFinite ι; by
    rw [← Finset.inf_univ_eq_iInf, ← Finset.inf_univ_eq_iInf]
    exact map_finset_inf (soberificationOpenComap (X := X)) Finset.univ U)

theorem soberificationOpenComap_preserves_arbitrary_unions
    {ι : Type v} (U : ι → Opens (Soberification X)) :
    soberificationOpenComap (X := X) (⨆ i, U i) =
      ⨆ i, soberificationOpenComap (X := X) (U i) := by
  exact map_iSup (soberificationOpenComap (X := X)) U

noncomputable def soberificationLift
    {Y : Type v} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) : Soberification X → Y :=
  fun Z => (Z.isIrreducible.image f hf.continuousOn).genericPoint

theorem soberificationLift_continuous
    {Y : Type v} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) :
    Continuous (soberificationLift f hf) := by
  refine continuous_def.2 ?_
  intro V hV
  let U : Set X := f ⁻¹' V
  have hU : IsOpen U := hV.preimage hf
  have hEq : (soberificationLift f hf) ⁻¹' V = soberificationOpen U := by
    ext Z
    constructor
    · intro hZ
      change (Z.isIrreducible.image f hf.continuousOn).genericPoint ∈ V at hZ
      have hgen := (Z.isIrreducible.image f hf.continuousOn).isGenericPoint_genericPoint_closure
      obtain ⟨y, hycl, hyV⟩ := (hgen.mem_open_set_iff hV).mp hZ
      obtain ⟨w, hwV, hwimage⟩ := mem_closure_iff.mp hycl V hV hyV
      obtain ⟨x, hxZ, hfxw⟩ := hwimage
      have hfx : f x ∈ V := hfxw.symm ▸ hwV
      exact ⟨x, hxZ, hfx⟩
    · rintro ⟨x, hxZ, hfx⟩
      change (Z.isIrreducible.image f hf.continuousOn).genericPoint ∈ V
      have hgen := (Z.isIrreducible.image f hf.continuousOn).isGenericPoint_genericPoint_closure
      exact hgen.specializes (subset_closure ⟨x, hxZ, rfl⟩) |>.mem_open hV hfx
  rw [hEq]
  exact isOpen_generateFrom_of_mem ⟨⟨U, hU⟩, rfl⟩

theorem soberificationLift_comp_map
    {Y : Type v} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) :
    soberificationLift f hf ∘ soberificationMap = f := by
  funext x
  have hleft := (soberificationMap (X := X) x).isIrreducible.image f hf.continuousOn
    |>.isGenericPoint_genericPoint_closure
  have hright := (isGenericPoint_closure (x := x)).image hf
  simpa [soberificationLift, Function.comp_apply] using hleft.eq hright

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
  refine continuous_def.2 ?_
  intro V hV
  let U : Set X := f ⁻¹' V
  have hU : IsOpen U := hV.preimage hf
  have hEq :
      (soberificationRangeLift f hf) ⁻¹' V =
        (Subtype.val : soberificationRange (X := X) → Soberification X) ⁻¹'
          soberificationOpen U := by
    ext r
    let r' : Set.range (soberificationMap (X := X)) :=
      ⟨(r : Soberification X), r.property⟩
    obtain ⟨x, hx⟩ := r'.property
    have hco :
        soberificationMap (X := X) (Set.rangeSplitting (soberificationMap (X := X)) r') =
          soberificationMap (X := X) x := by
      exact (Set.apply_rangeSplitting _ _).trans hx.symm
    have hcl :
        closure ({Set.rangeSplitting (soberificationMap (X := X)) r'} : Set X) =
          closure ({x} : Set X) := by
      simpa [soberificationMap_coe] using
        congrArg (fun Z : Soberification X => (Z : Set X)) hco
    have hfx : f (Set.rangeSplitting (soberificationMap (X := X)) r') = f x := by
      apply (t0Space_iff_inseparable Y).mp inferInstance
      exact (inseparable_iff_closure_eq.mpr hcl).map hf
    have hmem :
        x ∈ U ↔ (((soberificationMap (X := X) x : Soberification X) : Set X) ∩ U).Nonempty :=
      (isGenericPoint_closure (x := x)).mem_open_set_iff hU
    change f (Set.rangeSplitting (soberificationMap (X := X)) r') ∈ V ↔
      ((((r : Soberification X) : Set X) ∩ U).Nonempty)
    rw [hfx, show (r : Soberification X) = soberificationMap (X := X) x by exact hx.symm]
    simpa [U] using hmem
  rw [hEq]
  have hgen : IsOpen (soberificationOpen U) :=
    isOpen_generateFrom_of_mem
      (show soberificationOpen U ∈ soberificationBasis (X := X) from ⟨⟨U, hU⟩, rfl⟩)
  exact hgen.preimage continuous_subtype_val

theorem soberificationRangeLift_comp_map
    {Y : Type v} [TopologicalSpace Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) :
    soberificationRangeLift f hf ∘ soberificationRangeMap = f := by
  funext x
  change f (Set.rangeSplitting (soberificationMap (X := X))
      (Set.rangeFactorization (soberificationMap (X := X)) x)) = f x
  have hco :
      soberificationMap (X := X)
          (Set.rangeSplitting (soberificationMap (X := X))
            (Set.rangeFactorization (soberificationMap (X := X)) x)) =
      soberificationMap (X := X) x := by
    simp [Set.apply_rangeSplitting]
  have hcl :
      closure ({Set.rangeSplitting (soberificationMap (X := X))
        (Set.rangeFactorization (soberificationMap (X := X)) x)} : Set X) =
        closure ({x} : Set X) := by
    simpa [soberificationMap_coe] using
      congrArg (fun Z : Soberification X => (Z : Set X)) hco
  have hinsep :
      Inseparable (Set.rangeSplitting (soberificationMap (X := X))
        (Set.rangeFactorization (soberificationMap (X := X)) x)) x :=
    inseparable_iff_closure_eq.mpr hcl
  exact (t0Space_iff_inseparable Y).mp inferInstance _ _ (hinsep.map hf)

theorem soberificationRange_universal
    {Y : Type v} [TopologicalSpace Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) :
    ∃! g : soberificationRange (X := X) → Y,
      Continuous g ∧ g ∘ soberificationRangeMap = f := by
  refine ⟨soberificationRangeLift f hf,
    ⟨soberificationRangeLift_continuous f hf, soberificationRangeLift_comp_map f hf⟩, ?_⟩
  intro g hg
  funext z
  obtain ⟨x, rfl⟩ := Set.rangeFactorization_surjective z
  calc
    g (soberificationRangeMap (X := X) x) = f x := by
      simpa [Function.comp_apply] using congrFun hg.2 x
    _ = soberificationRangeLift f hf (soberificationRangeMap (X := X) x) := by
      symm
      exact congrFun (soberificationRangeLift_comp_map f hf) x

/-! ## Removing one component from a connected finite union -/

theorem exists_connected_sUnion_irreducibleComponents_sdiff_singleton
    [ConnectedSpace X] (hX : (irreducibleComponents X).Finite)
    (hn : 1 < Set.ncard (irreducibleComponents X)) :
    ∃ C ∈ irreducibleComponents X,
      IsConnected (⋃₀ (irreducibleComponents X \ {C})) := by
  classical
  have hfinite : Finite (irreducibleComponents X) := hX.to_subtype
  have hfinite_set (S : Set (irreducibleComponents X)) : S.Finite :=
    (@Set.finite_univ _ hfinite).subset (subset_univ S)
  have hnontrivial : Nontrivial (irreducibleComponents X) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    have hle : Set.ncard (irreducibleComponents X) ≤ 1 := by
      rw [Set.ncard_le_one_iff_subsingleton]
      intro A hA B hB
      exact congrArg Subtype.val
        (@Subsingleton.elim _ hsub ⟨A, hA⟩ ⟨B, hB⟩)
    exact (Nat.not_lt_of_ge hle) hn
  let G : SimpleGraph (irreducibleComponents X) :=
    SimpleGraph.fromRel (fun C D : irreducibleComponents X =>
      ((C : Set X) ∩ (D : Set X)).Nonempty)
  have hGconn : G.Connected := by
    refine { preconnected := ?_, nonempty := ?_ }
    · intro A B
      by_contra hAB
      let S : Set (irreducibleComponents X) := {D | G.Reachable A D}
      let U : Set X := ⋃ D ∈ S, (D : Set X)
      let V : Set X := ⋃ D ∈ Sᶜ, (D : Set X)
      have hSfin : S.Finite := hfinite_set S
      have hUclosed : IsClosed U := by
        dsimp [U]
        exact hSfin.isClosed_biUnion fun D _ =>
          isClosed_of_mem_irreducibleComponents (D : Set X) D.2
      have hVclosed : IsClosed V := by
        dsimp [V]
        exact (hfinite_set Sᶜ).isClosed_biUnion fun D _ =>
          isClosed_of_mem_irreducibleComponents (D : Set X) D.2
      have hUV : U ∪ V = (Set.univ : Set X) := by
        apply Set.eq_univ_of_forall
        intro x
        obtain ⟨D, hD, hxD⟩ := mem_sUnion.mp (by
          rw [sUnion_irreducibleComponents (X := X)]
          exact mem_univ x)
        let D' : irreducibleComponents X := ⟨D, hD⟩
        by_cases hDS : D' ∈ S
        · exact Or.inl (mem_iUnion₂.2 ⟨D', hDS, hxD⟩)
        · exact Or.inr (mem_iUnion₂.2 ⟨D', hDS, hxD⟩)
      have hUne : U.Nonempty := by
        obtain ⟨x, hx⟩ := (A.2.1 : IsIrreducible (A : Set X)).nonempty
        exact ⟨x, mem_iUnion₂.2 ⟨A, SimpleGraph.Reachable.rfl, hx⟩⟩
      have hVne : V.Nonempty := by
        obtain ⟨x, hx⟩ := (B.2.1 : IsIrreducible (B : Set X)).nonempty
        exact ⟨x, mem_iUnion₂.2 ⟨B, hAB, hx⟩⟩
      have hinter : ((Set.univ : Set X) ∩ (U ∩ V)).Nonempty :=
        isPreconnected_closed_iff.mp (isPreconnected_univ :
          IsPreconnected (Set.univ : Set X)) U V hUclosed hVclosed
          (hUV.symm ▸ subset_rfl)
          (by simpa only [univ_inter] using hUne)
          (by simpa only [univ_inter] using hVne)
      obtain ⟨x, _, hxUV⟩ := hinter
      obtain ⟨D, hDS, hxD⟩ := mem_iUnion₂.mp hxUV.1
      obtain ⟨E, hES, hxE⟩ := mem_iUnion₂.mp hxUV.2
      have hDE : G.Adj D E := by
        have hne : D ≠ E := by
          intro hDE
          apply hES
          simpa [hDE] using hDS
        simpa [G, SimpleGraph.fromRel_adj, inter_comm] using
          (show D ≠ E ∧ ((D : Set X) ∩ (E : Set X)).Nonempty from
            ⟨hne, ⟨x, hxD, hxE⟩⟩)
      exact hES (SimpleGraph.Reachable.trans hDS hDE.reachable)
    · obtain ⟨x⟩ := (inferInstance : Nonempty X)
      exact ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩
  obtain ⟨C, hC⟩ :=
    @SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial
      _ G hfinite hnontrivial hGconn
  refine ⟨C, C.2, ?_⟩
  let t : Set (irreducibleComponents X) := {D | D ≠ C}
  have ht : t.Nonempty := by
    obtain ⟨D, hD⟩ := @exists_ne _ hnontrivial C
    exact ⟨D, hD⟩
  have hfamily : ∀ D ∈ t, IsConnected (D : Set X) := by
    intro D _
    exact D.2.1.isConnected
  have hK : ∀ i, i ∈ t → ∀ j, j ∈ t →
      Relation.ReflTransGen (fun i j : irreducibleComponents X =>
        ((i : Set X) ∩ (j : Set X)).Nonempty ∧ i ∈ t) i j := by
    intro i hi j hj
    have hreach : (G.induce t).Reachable ⟨i, hi⟩ ⟨j, hj⟩ :=
      hC.preconnected ⟨i, hi⟩ ⟨j, hj⟩
    rw [SimpleGraph.reachable_eq_reflTransGen] at hreach
    have hlift : Relation.ReflTransGen
        (fun i j : irreducibleComponents X =>
          ((i : Set X) ∩ (j : Set X)).Nonempty ∧ i ∈ t) i j :=
      (Relation.ReflTransGen.lift
        (r := (G.induce t).Adj)
        (p := fun i j : irreducibleComponents X =>
          ((i : Set X) ∩ (j : Set X)).Nonempty ∧ i ∈ t)
        Subtype.val (by
          intro a b hab
          have habG : G.Adj (a : irreducibleComponents X) (b : irreducibleComponents X) := hab
          have hab' : (a : irreducibleComponents X) ≠ b ∧
              (((a : irreducibleComponents X) : Set X) ∩ (b : Set X)).Nonempty := by
            simpa [G, SimpleGraph.fromRel_adj, inter_comm] using habG
          exact ⟨hab'.2, a.2⟩)) ⟨i, hi⟩ ⟨j, hj⟩ hreach
    exact hlift
  have hconnected : IsConnected (⋃ D ∈ t, (D : Set X)) :=
    IsConnected.biUnion_of_reflTransGen ht hfamily hK
  have hunion : (⋃ D ∈ t, (D : Set X)) =
      ⋃₀ (irreducibleComponents X \ {(C : Set X)}) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨D, hDt, hxD⟩ := mem_iUnion₂.mp hx
      apply mem_sUnion_of_mem hxD
      refine ⟨D.2, ?_⟩
      intro hDC
      apply hDt
      exact Subtype.ext hDC
    · intro x hx
      obtain ⟨D, hD, hxD⟩ := mem_sUnion.mp hx
      let D' : irreducibleComponents X := ⟨D, hD.1⟩
      have hDt : D' ∈ t := by
        intro hDC
        apply hD.2
        exact Set.mem_singleton_iff.mpr (congrArg Subtype.val hDC)
      exact mem_iUnion₂.2 ⟨D', hDt, hxD⟩
  exact hunion ▸ hconnected

end IrreducibleComponents

end Formalization.Books.Topology.Unit08
