import Formalization.Books.Topology.Unit24.LimitsOfSpectralSpaces
import Formalization.Books.Topology.Unit03.HausdorffSpaces
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Sets.OpenCover

/-!
# Pro-étale Cohomology, Chapter 2: Some topology

The source uses the standard spectral-space, specialization, profinite-space,
and connected-components constructions.  Those are represented by the
canonical Mathlib and earlier Topology-chapter interfaces.  This file adds the
chapter-specific w-local predicates and records the statements in source
order.
-/

namespace Formalization.Books.Proetale.Unit02

open Set Function CategoryTheory CategoryTheory.Limits
open TopologicalSpace _root_.Topology
open Formalization.Books.Topology.Unit22
open Formalization.Books.Topology.Unit24

universe u v

/-! ## Spectral spaces with disjoint clopen refinements -/

/- A finite disjoint union refinement of an open cover is represented by a
   finite family of clopen subsets, pairwise disjoint and covering `univ`. -/
def HasFiniteClopenRefinement (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ {ι : Type v} (U : ι → Opens X), IsOpenCover U →
    ∃ (n : ℕ) (V : Fin n → Set X),
      (∀ j, IsOpen (V j) ∧ IsClosed (V j)) ∧
        Pairwise (fun i j => Disjoint (V i) (V j)) ∧
          (⋃ j, V j) = (Set.univ : Set X) ∧
            ∀ j, ∃ i, V j ⊆ (U i : Set X)

/- The canonical map from the closed-point subspace to the quotient by
   connected components. -/
def closedPointComponentMap {X : Type u} [TopologicalSpace X] :
    closedPoints X → ConnectedComponents X :=
  fun x => ConnectedComponents.mk (x : X)

/-- The first lemma of the section: a spectral space has the source's finite
disjoint clopen refinement property exactly when every connected component has
one closed point. -/
theorem spectralSplit_iff_closedPointComponentMap_bijective
    {X : Type u} [TopologicalSpace X] [SpectralSpace X] :
    HasFiniteClopenRefinement X ↔
      Function.Bijective (closedPointComponentMap (X := X)) := by
  constructor
  · intro h
    classical
    have closedPoint_specializes (x : X) :
        ∃ z : closedPoints X, x ⤳ (z : X) := by
      obtain ⟨z, hz, hzclosed⟩ :=
        IsClosed.exists_closed_singleton (S := closure ({x} : Set X))
          isClosed_closure ⟨x, subset_closure rfl⟩
      exact ⟨⟨z, hzclosed⟩, specializes_iff_mem_closure.mpr hz⟩
    have component_eq_of_specializes {x : X} {z : closedPoints X}
        (hs : x ⤳ (z : X)) :
        ConnectedComponents.mk x = ConnectedComponents.mk (z : X) := by
      apply ConnectedComponents.coe_eq_coe.mpr
      apply Formalization.Books.Topology.Unit07.connectedComponent_eq_of_mem
      apply closure_minimal (singleton_subset_iff.mpr mem_connectedComponent)
        (Formalization.Books.Topology.Unit07.connectedComponent_is_closed x)
      exact specializes_iff_mem_closure.mp hs
    constructor
    · intro z₁ z₂ heq
      have hcompEq : connectedComponent (z₁ : X) =
          connectedComponent (z₂ : X) := by
        exact ConnectedComponents.coe_eq_coe.mp heq
      by_contra hne
      have hneval : (z₁ : X) ≠ (z₂ : X) := fun h => hne (Subtype.ext h)
      let U : ULift Bool → Opens X := fun b =>
        match b.down with
        | false => ⟨({(z₁ : X)} : Set X)ᶜ, z₁.property.isOpen_compl⟩
        | true => ⟨({(z₂ : X)} : Set X)ᶜ, z₂.property.isOpen_compl⟩
      have hU : IsOpenCover U := by
        apply IsOpenCover.of_sets
        exact Set.eq_univ_of_forall (fun x => by
          by_cases hx₁ : x = (z₁ : X)
          · subst x
            refine Set.mem_iUnion.mpr ⟨ULift.up true, ?_⟩
            simp [U, hneval]
          · refine Set.mem_iUnion.mpr ⟨ULift.up false, ?_⟩
            simp [U, hx₁])
      obtain ⟨n, V, hV, hdisj, hcover, hsub⟩ := h U hU
      have hz₁union : (z₁ : X) ∈ ⋃ j, V j := by
        rw [hcover]
        simp
      have hz₂union : (z₂ : X) ∈ ⋃ j, V j := by
        rw [hcover]
        simp
      obtain ⟨j, hj₁⟩ := Set.mem_iUnion.mp hz₁union
      obtain ⟨k, hk₂⟩ := Set.mem_iUnion.mp hz₂union
      have hjk : j ≠ k := by
        intro hjk
        subst k
        obtain ⟨i, hi⟩ := hsub j
        cases i with
        | up b =>
          cases b with
          | false =>
            simpa [U] using hi hj₁
          | true =>
            simpa [U] using hi hk₂
      have hclopen : IsClopen (V j) := ⟨(hV j).2, (hV j).1⟩
      have hz₂comp : (z₂ : X) ∈ connectedComponent (z₁ : X) := by
        rw [hcompEq]
        exact mem_connectedComponent
      exact (Set.disjoint_left.1 (hdisj hjk))
        (hclopen.connectedComponent_subset hj₁ hz₂comp) hk₂
    · intro c
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      obtain ⟨z, hsz⟩ := closedPoint_specializes x
      exact ⟨z, (component_eq_of_specializes hsz).symm⟩
  · intro h
    classical
    letI : CompactSpace (closedPoints X) :=
      isCompact_iff_compactSpace.mp
        Formalization.Books.Topology.Unit12.isCompact_closedPoints
    have hcc : IsProfiniteSpace (ConnectedComponents X) :=
      Formalization.Books.Topology.Unit23.connectedComponents_isProfiniteSpace
    letI : T2Space (ConnectedComponents X) :=
      (isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mp hcc).1
    let f : closedPoints X → ConnectedComponents X :=
      closedPointComponentMap
    have hfcont : Continuous f := by
      exact ConnectedComponents.continuous_coe.comp continuous_subtype_val
    have hfhomeo : IsHomeomorph f :=
      isHomeomorph_iff_continuous_bijective.mpr ⟨hfcont, h⟩
    intro ι U hU
    let W : ι → Opens (ConnectedComponents X) := fun i =>
      ⟨f '' ((Subtype.val : closedPoints X → X) ⁻¹' (U i : Set X)),
        hfhomeo.isOpenMap _ ((U i).isOpen.preimage continuous_subtype_val)⟩
    have hW : IsOpenCover W := by
      apply IsOpenCover.of_sets
      exact Set.eq_univ_of_forall (fun c => by
        obtain ⟨z, hz⟩ := h.2 c
        obtain ⟨i, hi⟩ := hU.exists_mem (z : X)
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        exact ⟨z, hi, hz⟩)
    have closedPoint_specializes (x : X) :
        ∃ z : closedPoints X, x ⤳ (z : X) := by
      obtain ⟨z, hz, hzclosed⟩ :=
        IsClosed.exists_closed_singleton (S := closure ({x} : Set X))
          isClosed_closure ⟨x, subset_closure rfl⟩
      exact ⟨⟨z, hzclosed⟩, specializes_iff_mem_closure.mpr hz⟩
    have component_eq_of_specializes {x : X} {z : closedPoints X}
        (hs : x ⤳ (z : X)) :
        ConnectedComponents.mk x = ConnectedComponents.mk (z : X) := by
      apply ConnectedComponents.coe_eq_coe.mpr
      apply Formalization.Books.Topology.Unit07.connectedComponent_eq_of_mem
      apply closure_minimal (singleton_subset_iff.mpr mem_connectedComponent)
        (Formalization.Books.Topology.Unit07.connectedComponent_is_closed x)
      exact specializes_iff_mem_closure.mp hs
    obtain ⟨n, V, hV, hcover, hdisj⟩ :=
      Formalization.Books.Topology.Unit22.profiniteSpace_open_cover_has_finite_clopen_refinement
        hcc W hW
    refine ⟨n, fun j => (ConnectedComponents.mk ⁻¹' (V j : Set (ConnectedComponents X))), ?_,
      ?_, ?_, ?_⟩
    · intro j
      exact ⟨(V j).isOpen.preimage ConnectedComponents.continuous_coe,
        (V j).isClosed.preimage ConnectedComponents.continuous_coe⟩
    · intro j k hjk
      rw [Set.disjoint_left]
      intro x hxj hxk
      change ConnectedComponents.mk x ∈ (V j : Set (ConnectedComponents X)) at hxj
      change ConnectedComponents.mk x ∈ (V k : Set (ConnectedComponents X)) at hxk
      exact (Set.disjoint_left.1
        (Clopens.coe_disjoint.mpr (hdisj hjk))) hxj hxk
    · rw [← Set.preimage_iUnion]
      rw [hcover]
      simp
    · intro j
      obtain ⟨i, hi⟩ := (hV j).2
      refine ⟨i, ?_⟩
      intro x hx
      change ConnectedComponents.mk x ∈ (V j : Set (ConnectedComponents X)) at hx
      have hWmem := hi hx
      change ConnectedComponents.mk x ∈
        f '' ((Subtype.val : closedPoints X → X) ⁻¹' (U i : Set X)) at hWmem
      obtain ⟨z, hzx, hz⟩ := hWmem
      obtain ⟨z₀, hspec⟩ := closedPoint_specializes x
      have hz_eq : z = z₀ := by
        apply h.1
        exact hz.trans (component_eq_of_specializes hspec)
      have hspec' : x ⤳ (z : X) := by
        simpa [hz_eq] using hspec
      exact (U i).isOpen.stableUnderGeneralization hspec' hzx

/-- The final sufficient condition in the spectral-splitting lemma. -/
theorem spectralSplit_of_closedPoints_closed_of_unique_specialization
    {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    (hclosed : IsClosed (closedPoints X))
    (hspecializes : ∀ x : X, ∃! x₀ : closedPoints X, x ⤳ (x₀ : X)) :
    HasFiniteClopenRefinement X ∧
      Function.Bijective (closedPointComponentMap (X := X)) := by
  classical
  letI : SpectralSpace (closedPoints X) :=
    Formalization.Books.Topology.Unit23.spectralSpace_subtype_of_isClosed hclosed
  have hclosed_singleton : ∀ z : closedPoints X,
      IsClosed ({z} : Set (closedPoints X)) := by
    intro z
    have heq : (Subtype.val : closedPoints X → X) ⁻¹'
        ({(z : X)} : Set X) = ({z} : Set (closedPoints X)) := by
      ext y
      constructor
      · intro hy
        exact Subtype.ext hy
      · intro hy
        exact congrArg Subtype.val (Set.mem_singleton_iff.mp hy)
    rw [← heq]
    exact z.property.preimage continuous_subtype_val
  have hprof : IsProfiniteSpace (closedPoints X) :=
    ((Formalization.Books.Topology.Unit23.isProfiniteSpace_TFAE_spectral_separation_conditions
      (X := closedPoints X)).out 5 0).mp hclosed_singleton
  obtain ⟨P, ⟨e⟩⟩ := hprof
  letI : T2Space (closedPoints X) := e.symm.t2Space
  letI : CompactSpace (closedPoints X) := e.symm.compactSpace
  letI : TotallyDisconnectedSpace (closedPoints X) := e.symm.totallyDisconnectedSpace
  letI : TotallySeparatedSpace (closedPoints X) := inferInstance
  have closedPoint_specializes (x : X) :
      ∃ z : closedPoints X, x ⤳ (z : X) := by
    obtain ⟨z, hz, hzclosed⟩ :=
      IsClosed.exists_closed_singleton (S := closure ({x} : Set X))
        isClosed_closure ⟨x, subset_closure rfl⟩
    exact ⟨⟨z, hzclosed⟩, specializes_iff_mem_closure.mpr hz⟩
  have component_eq_of_specializes {x : X} {z : closedPoints X}
      (hs : x ⤳ (z : X)) :
      ConnectedComponents.mk x = ConnectedComponents.mk (z : X) := by
    apply ConnectedComponents.coe_eq_coe.mpr
    apply Formalization.Books.Topology.Unit07.connectedComponent_eq_of_mem
    apply closure_minimal (singleton_subset_iff.mpr mem_connectedComponent)
      (Formalization.Books.Topology.Unit07.connectedComponent_is_closed x)
    exact specializes_iff_mem_closure.mp hs
  have closed_of_clopen_trace {A : Set (closedPoints X)}
      (hA : IsClopen A) :
      IsClosed (pointsSpecializingTo
        ((Subtype.val : closedPoints X → X) '' A)) := by
    let E : Set X := (Subtype.val : closedPoints X → X) '' A
    have hEcompact : IsCompact E := by
      dsimp [E]
      exact hA.isClosed.isCompact.image continuous_subtype_val
    let W : Set X := pointsSpecializingTo E
    have hchar :=
      Formalization.Books.Topology.Unit24.isIntersectionOfConstructibleSets_iff_isCompact_iff_pointsSpecializingTo
        (X := X) (W := W)
    have hWcompactstable : IsCompact W ∧ StableUnderGeneralization W :=
      hchar.2.1.mpr ⟨E, hEcompact, rfl⟩
    have hWconstructible : IsIntersectionOfConstructibleSets W ∧
        StableUnderGeneralization W := hchar.1.mpr hWcompactstable
    have hWctclosed : IsClosed[constructibleTopology X] W := by
      rcases hWconstructible.1 with ⟨S, hWS, hS⟩
      rw [hWS]
      exact @isClosed_sInter X (constructibleTopology X) S (fun F hF =>
        (Formalization.Books.Topology.Unit23.isConstructible_isOpen_isClosed_constructibleTopology
          (hS F hF)).2)
    have hWstableSpecialization : StableUnderSpecialization W := by
      intro x y hxy hx
      rcases hx with ⟨z, hz, hxz⟩
      rcases hz with ⟨zA, hzA, rfl⟩
      obtain ⟨z', hyz', hyuniq⟩ := hspecializes y
      obtain ⟨z₀, hxz₀, hxuniq⟩ := hspecializes x
      have hzz' : z' = zA := by
        exact (hxuniq z' (hxy.trans hyz')).trans
          (hxuniq zA hxz).symm
      refine ⟨(zA : X), ⟨zA, hzA, rfl⟩, ?_⟩
      simpa [hzz'] using hyz'
    exact Formalization.Books.Topology.Unit23.isClosed_of_constructibleClosed_of_stableUnderSpecialization
      hWctclosed hWstableSpecialization
  have hbij : Function.Bijective (closedPointComponentMap (X := X)) := by
    constructor
    · intro z₁ z₂ heq
      by_contra hne
      obtain ⟨B, hBclopen, hz₁B, hz₂Bc⟩ :=
        exists_isClopen_of_totally_separated hne
      let E : Set X := (Subtype.val : closedPoints X → X) '' B
      let Ec : Set X := (Subtype.val : closedPoints X → X) '' Bᶜ
      let W : Set X := pointsSpecializingTo E
      let Wc : Set X := pointsSpecializingTo Ec
      have hWclosed : IsClosed W := by
        dsimp [W, E]
        exact closed_of_clopen_trace hBclopen
      have hWcclosed : IsClosed Wc := by
        dsimp [Wc, Ec]
        exact closed_of_clopen_trace hBclopen.compl
      have hpartition : W ∪ Wc = (Set.univ : Set X) := by
        apply Set.eq_univ_of_forall
        intro x
        obtain ⟨z, hspec⟩ := closedPoint_specializes x
        by_cases hz : z ∈ B
        · left
          refine ⟨z, ⟨z, hz, rfl⟩, hspec⟩
        · right
          refine ⟨z, ⟨z, hz, rfl⟩, hspec⟩
      have hdisjoint : Disjoint W Wc := by
        rw [Set.disjoint_left]
        intro x hx hx'
        rcases hx with ⟨z, hz, hzx⟩
        rcases hx' with ⟨z', hz', hzx'⟩
        rcases hz with ⟨z₀, hz₀B, hz₀eq⟩
        rcases hz' with ⟨z₁, hz₁B, hz₁eq⟩
        have hzx₀ : x ⤳ (z₀ : X) := by simpa [← hz₀eq] using hzx
        have hzx₁ : x ⤳ (z₁ : X) := by simpa [← hz₁eq] using hzx'
        obtain ⟨z₂, hspec₂, huniq₂⟩ := hspecializes x
        have hzero : z₀ = z₂ := huniq₂ z₀ hzx₀
        have hone : z₁ = z₂ := huniq₂ z₁ hzx₁
        have hz₁eqz₀ : z₁ = z₀ := hone.trans hzero.symm
        rw [hz₁eqz₀] at hz₁B
        exact hz₁B hz₀B
      have hWc_eq : Wc = Wᶜ := by
        apply Set.Subset.antisymm
        · intro x hx'
          intro hx
          exact (Set.disjoint_left.1 hdisjoint) hx hx'
        · intro x hx
          have hx' : x ∈ W ∪ Wc := by
            rw [hpartition]
            exact Set.mem_univ x
          exact hx'.resolve_left hx
      have hWopen : IsOpen W := by
        have hW_eq : W = Wcᶜ := by
          rw [hWc_eq]
          simp
        rw [hW_eq]
        exact hWcclosed.isOpen_compl
      have hz₁W : (z₁ : X) ∈ W := by
        exact ⟨z₁, ⟨z₁, hz₁B, rfl⟩, specializes_rfl⟩
      have hz₂Wc : (z₂ : X) ∈ Wc := by
        exact ⟨z₂, ⟨z₂, hz₂Bc, rfl⟩, specializes_rfl⟩
      have hclopenW : IsClopen W := ⟨hWclosed, hWopen⟩
      have hz₂comp : (z₂ : X) ∈ connectedComponent (z₁ : X) := by
        rw [ConnectedComponents.coe_eq_coe.mp heq]
        exact mem_connectedComponent
      exact (Set.disjoint_left.1 hdisjoint)
        (hclopenW.connectedComponent_subset hz₁W hz₂comp) hz₂Wc
    · intro c
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      obtain ⟨z, hspec⟩ := closedPoint_specializes x
      exact ⟨z, (component_eq_of_specializes hspec).symm⟩
  refine ⟨?_, hbij⟩
  exact (spectralSplit_iff_closedPointComponentMap_bijective (X := X)).mpr hbij

/-! ## The profinite counterexample -/

/- The source's carrier is a copy of `T × {0, 1}`.  A structure keeps the
   generated topology separate from the pre-existing product topology on a
   literal product type, while retaining the two coordinates used by the
   construction. -/
structure NotWLocalExamplePoint (T : Type u) (t : T) where
  base : T
  component : Bool

/-- The subbasis specified in the source example. -/
def notWLocalExampleSubbasis {T : Type u} [TopologicalSpace T] (t : T) :
    Set (Set (NotWLocalExamplePoint T t)) :=
  Set.range (fun U : Opens T =>
      {x | x.base ∈ (U : Set T)}) ∪
    {Set.univ \ ({⟨t, false⟩} : Set (NotWLocalExamplePoint T t))} ∪
      Set.range (fun U : {U : Opens T // t ∉ (U : Set T)} =>
        {x | x.base ∈ (U.1 : Set T) ∧ x.component = true})

/-- The topology generated by the source's subbasis. -/
instance notWLocalExampleTopologicalSpace
    {T : Type u} [TopologicalSpace T] (t : T) :
    TopologicalSpace (NotWLocalExamplePoint T t) :=
  TopologicalSpace.generateFrom (notWLocalExampleSubbasis t)

/-- The subset `T × {0}` in the source example. -/
def notWLocalExampleClosedPointSet {T : Type u} [TopologicalSpace T] (t : T) :
    Set (NotWLocalExamplePoint T t) :=
  {x | x.component = false}

/-- The point `(t, 1)` whose closure witnesses that the closed-point set is
not closed. -/
def notWLocalExampleDistinguishedPoint {T : Type u} [TopologicalSpace T] (t : T) :
    NotWLocalExamplePoint T t :=
  ⟨t, true⟩

/-- The source's profinite example has the two properties in the spectral
splitting lemma, but its closed-point set is not closed. -/
theorem notWLocalExample_properties
    {T : Type u} [TopologicalSpace T] (hT : IsProfiniteSpace T) (t : T)
    (hnotcompact : ¬ IsCompact (({t} : Set T)ᶜ)) :
    SpectralSpace (NotWLocalExamplePoint T t) ∧
      closedPoints (NotWLocalExamplePoint T t) =
        notWLocalExampleClosedPointSet t ∧
      notWLocalExampleDistinguishedPoint t ∈
        closure (notWLocalExampleClosedPointSet t) ∧
      HasFiniteClopenRefinement (NotWLocalExamplePoint T t) ∧
      Function.Bijective
        (closedPointComponentMap (X := NotWLocalExamplePoint T t)) ∧
      ¬ IsClosed (closedPoints (NotWLocalExamplePoint T t)) := by
  classical
  have hTprofinite : IsProfiniteSpace T := hT
  obtain ⟨P, ⟨e⟩⟩ := hT
  let _ : T2Space T := e.symm.t2Space
  let _ : CompactSpace T := e.symm.compactSpace
  let _ : TotallyDisconnectedSpace T := e.symm.totallyDisconnectedSpace
  have hTpres : PrespectralSpace T :=
    PrespectralSpace.of_isTopologicalBasis isTopologicalBasis_isClopen
      (fun U hU => hU.isClosed.isCompact)
  let _ : SpectralSpace T :=
    Formalization.Books.Topology.Unit23.spectralSpace_iff_source_conditions.mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance, hTpres⟩
  let q : T × Bool → NotWLocalExamplePoint T t :=
    fun x => ⟨x.1, x.2⟩
  have hqcont : Continuous q := by
    apply continuous_generateFrom_iff.mpr
    intro A hA
    simp [notWLocalExampleSubbasis] at hA
    rcases hA with (rfl | ⟨U, hUA⟩) | ⟨U, hUt, hUA⟩
    · have hclosed : IsClosed (({(t, false)} : Set (T × Bool))) :=
        isClosed_singleton
      have hpre : q ⁻¹' (Set.univ \ ({⟨t, false⟩} : Set (NotWLocalExamplePoint T t))) =
          (({(t, false)} : Set (T × Bool)) : Set (T × Bool))ᶜ := by
        ext x
        rcases x with ⟨s, b⟩
        cases b <;> simp [q]
      rw [hpre]
      exact hclosed.isOpen_compl
    · rw [← hUA]
      exact (U.2.preimage continuous_fst)
    · rw [← hUA]
      exact (U.2.preimage continuous_fst).inter
        ((isOpen_discrete ({true} : Set Bool)).preimage continuous_snd)
  have hcompactX : CompactSpace (NotWLocalExamplePoint T t) := by
    let _ : CompactSpace Bool := Finite.compactSpace
    have hqsurj : Function.Surjective q := by
      intro x
      exact ⟨(x.base, x.component), rfl⟩
    have hqimage : IsCompact (Set.range q) := by
      rw [← Set.image_univ]
      exact (@isCompact_univ (T × Bool) _).image hqcont
    exact ⟨by simpa [Set.range_eq_univ.2 hqsurj] using hqimage⟩
  let _ := hcompactX
  let H : Set (NotWLocalExamplePoint T t) :=
    Set.univ \ ({⟨t, false⟩} : Set (NotWLocalExamplePoint T t))
  have hHcompact : IsCompact H := by
    apply isCompact_generateFrom (s := H) rfl
    intro R hR hcover
    have ht1 : (⟨t, true⟩ : NotWLocalExamplePoint T t) ∈ ⋃₀ R := by
      exact hcover (by simp [H])
    obtain ⟨A, hAR, ht1A⟩ := Set.mem_sUnion.mp ht1
    have hA : A ∈ notWLocalExampleSubbasis t := hR hAR
    simp [notWLocalExampleSubbasis] at hA
    have hA' : A = H ∨
        (∃ U : Opens T, {x : NotWLocalExamplePoint T t | x.base ∈ U} = A) ∨
          ∃ U : Opens T, t ∉ (U : Set T) ∧
            {x : NotWLocalExamplePoint T t |
              x.base ∈ (U : Set T) ∧ x.component = true} = A := by
      rcases hA with (hAH | hA) | hB
      · exact Or.inl hAH
      · exact Or.inr (Or.inl hA)
      · exact Or.inr (Or.inr hB)
    rcases hA' with (hAH | hA)
    · refine ⟨{A}, ?_, ?_⟩
      · simp [hAR]
      · simp [hAH]
    · rcases hA with ⟨U, hUA⟩ | ⟨U, htU, hUA⟩
      · have htU' : t ∈ (U : Set T) := by
          rw [← hUA] at ht1A
          exact ht1A
        by_cases hHR : H ∈ R
        · refine ⟨{H}, ?_, ?_⟩
          · simp [hHR]
          · simp
        let K : Set T := (U : Set T)ᶜ
        have hKcompact : IsCompact K := by
          exact (U.2.isClosed_compl).isCompact
        let I : Type _ := {V : Opens T // {x : NotWLocalExamplePoint T t | x.base ∈ V} ∈ R}
        have hKcover : K ⊆ ⋃ V : I, (V : Set T) := by
          intro s hs
          have hst : s ≠ t := by
            intro hst
            apply hs
            simpa [K, hst] using htU'
          have hsH : (⟨s, false⟩ : NotWLocalExamplePoint T t) ∈ H := by
            simp [H, hst]
          obtain ⟨B, hBR, hsB⟩ := Set.mem_sUnion.mp (hcover hsH)
          have hB : B ∈ notWLocalExampleSubbasis t := hR hBR
          simp [notWLocalExampleSubbasis] at hB
          rcases hB with (hBH | hB) | hB
          · exfalso
            apply hHR
            change Set.univ \ ({⟨t, false⟩} : Set (NotWLocalExamplePoint T t)) ∈ R
            rw [← hBH]
            exact hBR
          · obtain ⟨V, hVB⟩ := hB
            have hVR : {x : NotWLocalExamplePoint T t | x.base ∈ V} ∈ R := by
              rw [hVB]
              exact hBR
            have hsV : s ∈ (V : Set T) := by
              rw [← hVB] at hsB
              exact hsB
            exact Set.mem_iUnion.2 ⟨⟨V, hVR⟩, hsV⟩
          · obtain ⟨V, hVt, hVB⟩ := hB
            rw [← hVB] at hsB
            simp at hsB
        obtain ⟨F, hF⟩ := hKcompact.elim_finite_subcover
          (fun V : I => (V : Set T)) (fun V => V.1.2) hKcover
        let C : I → Set (NotWLocalExamplePoint T t) :=
          fun V => {x | x.base ∈ (V : Set T)}
        let Q : Set (Set (NotWLocalExamplePoint T t)) :=
          {A} ∪ C '' (F : Set I)
        refine ⟨Q, ?_, ?_, ?_⟩
        · intro B hB
          rcases hB with (rfl | ⟨V, hVF, rfl⟩)
          · exact hAR
          · exact V.2
        · exact (Set.finite_singleton A).union (F.finite_toSet.image C)
        · intro x hxH
          by_cases hxA : x ∈ A
          · exact Set.mem_sUnion.2 ⟨A, Set.mem_union_left _ (Set.mem_singleton _), hxA⟩
          · have hxK : x.base ∈ K := by
              change x.base ∉ (U : Set T)
              intro hxU
              apply hxA
              rw [← hUA]
              exact hxU
            rcases Set.mem_iUnion.mp (hF hxK) with ⟨V, hV⟩
            rcases Set.mem_iUnion.mp hV with ⟨hVF, hxV⟩
            exact Set.mem_sUnion.2
              ⟨C V, Set.mem_union_right _ ⟨V, hVF, rfl⟩, hxV⟩
      · exfalso
        have htUA : t ∈ (U : Set T) := by
          rw [← hUA] at ht1A
          exact ht1A.1
        exact htU htUA
  let Cyl : Set T → Set (NotWLocalExamplePoint T t) :=
    fun C => {x | x.base ∈ C}
  let One : Set T → Set (NotWLocalExamplePoint T t) :=
    fun C => {x | x.base ∈ C ∧ x.component = true}
  have hCyl_open {C : Set T} (hC : IsClopen C) : IsOpen (Cyl C) := by
    change IsOpen[TopologicalSpace.generateFrom (notWLocalExampleSubbasis t)] (Cyl C)
    apply isOpen_generateFrom_of_mem
    exact Or.inl (Or.inl ⟨⟨C, hC.isOpen⟩, rfl⟩)
  have hH_open : IsOpen H := by
    change IsOpen[TopologicalSpace.generateFrom (notWLocalExampleSubbasis t)] H
    apply isOpen_generateFrom_of_mem
    simp [H, notWLocalExampleSubbasis]
  have hOne_open {C : Set T} (hC : IsClopen C) (htC : t ∉ C) :
      IsOpen (One C) := by
    change IsOpen[TopologicalSpace.generateFrom (notWLocalExampleSubbasis t)] (One C)
    apply isOpen_generateFrom_of_mem
    exact Or.inr ⟨⟨⟨C, hC.isOpen⟩, htC⟩, rfl⟩
  have hCyl_clopen {C : Set T} (hC : IsClopen C) :
      IsClopen (Cyl C) := by
    refine ⟨?_, hCyl_open hC⟩
    have hcompC : IsOpen (Cyl Cᶜ) := hCyl_open hC.compl
    have heq : (Cyl Cᶜ)ᶜ = Cyl C := by
      ext x
      simp [Cyl]
    rw [← heq]
    exact hcompC.isClosed_compl
  have hrcont : Continuous (fun s : T =>
      (⟨s, true⟩ : NotWLocalExamplePoint T t)) := by
    apply continuous_generateFrom_iff.mpr
    intro A hA
    simp [notWLocalExampleSubbasis] at hA
    rcases hA with (rfl | ⟨U, hUA⟩) | ⟨U, hUt, hUA⟩
    ·
      have hpre : (fun s : T =>
          (⟨s, true⟩ : NotWLocalExamplePoint T t)) ⁻¹'
          ({⟨t, false⟩} : Set (NotWLocalExamplePoint T t)) = ∅ := by
        ext s
        simp
      rw [Set.preimage_sdiff, Set.preimage_univ, hpre]
      simp
    · rw [← hUA]
      simpa [Set.preimage] using U.2
    · rw [← hUA]
      simpa [Set.preimage] using U.2
  have hOne_compact {C : Set T} (hC : IsClopen C) (htC : t ∉ C) :
      IsCompact (One C) := by
    have himage : IsCompact ((fun s : T =>
        (⟨s, true⟩ : NotWLocalExamplePoint T t)) '' C) :=
      hC.isClosed.isCompact.image hrcont
    have heq : (fun s : T =>
        (⟨s, true⟩ : NotWLocalExamplePoint T t)) '' C = One C := by
      ext x
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨hs, rfl⟩
      · intro hx
        refine ⟨x.base, hx.1, ?_⟩
        cases x with
        | mk s b =>
          cases hx.2
          rfl
    rw [← heq]
    exact himage
  let B : Set (Set (NotWLocalExamplePoint T t)) :=
    (Set.range (fun C : {C : Set T // IsClopen C} => Cyl C.1) ∪
      Set.range (fun C : {C : Set T // IsClopen C} => H ∩ Cyl C.1)) ∪
      Set.range (fun C : {C : Set T // IsClopen C ∧ t ∉ C} => One C.1)
  have hB_open : ∀ U ∈ B, IsOpen U := by
    intro U hU
    simp only [B, Set.mem_union, Set.mem_range] at hU
    rcases hU with (⟨C, rfl⟩ | ⟨C, rfl⟩) | ⟨C, rfl⟩
    · exact hCyl_open C.2
    · exact hH_open.inter (hCyl_open C.2)
    · exact hOne_open C.2.1 C.2.2
  have hB_compact : ∀ U ∈ B, IsCompact U := by
    intro U hU
    simp only [B, Set.mem_union, Set.mem_range] at hU
    rcases hU with (⟨C, rfl⟩ | ⟨C, rfl⟩) | ⟨C, rfl⟩
    · exact (hCyl_clopen C.2).isClosed.isCompact
    · exact hHcompact.inter_right (hCyl_clopen C.2).isClosed
    · exact hOne_compact C.2.1 C.2.2
  have exists_clopen_subset {D : Set T} (hD : IsOpen D) {s : T} (hs : s ∈ D) :
      ∃ C : Set T, IsClopen C ∧ s ∈ C ∧ C ⊆ D := by
    obtain ⟨C, hC, hsC, hCD⟩ :=
      isTopologicalBasis_isClopen.exists_subset_of_mem_open hs hD
    exact ⟨C, hC, hsC, hCD⟩
  have hOne_subset_H {C : Set T} (hC : IsClopen C) (htC : t ∉ C) :
      One C ⊆ H := by
    intro y hy
    change y ∈ Set.univ \ ({⟨t, false⟩} : Set (NotWLocalExamplePoint T t))
    simp only [Set.mem_sdiff, Set.mem_univ, true_and]
    intro hy'
    have hyeq : y = ⟨t, false⟩ := Set.mem_singleton_iff.mp hy'
    change y.base ∈ C ∧ y.component = true at hy
    have : t ∈ C := by
      rw [hyeq] at hy
      exact hy.1
    exact htC this
  have hB_refine_subbasis {b A : Set (NotWLocalExamplePoint T t)} {x :
      NotWLocalExamplePoint T t} (hb : b ∈ B) (hxb : x ∈ b)
      (hA : A ∈ notWLocalExampleSubbasis t) (hxA : x ∈ A) :
      ∃ d ∈ B, x ∈ d ∧ d ⊆ b ∩ A := by
    simp [notWLocalExampleSubbasis] at hA
    simp only [B, Set.mem_union, Set.mem_range] at hb
    rcases hb with (⟨C, rfl⟩ | ⟨C, rfl⟩) | ⟨C, rfl⟩
    · rcases hA with (rfl | ⟨U, hUA⟩) | ⟨U, hUt, hUA⟩
      · refine ⟨H ∩ Cyl C.1, Or.inl (Or.inr ⟨C, rfl⟩), ?_, ?_⟩
        · exact ⟨hxA, hxb⟩
        · intro y hy
          exact ⟨hy.2, hy.1⟩
      · have hxC : x.base ∈ C.1 := hxb
        have hxU : x.base ∈ (U : Set T) := by
          have h := hxA
          rw [← hUA] at h
          exact h
        obtain ⟨D, hD, hxD, hDC⟩ := exists_clopen_subset
          (C.2.isOpen.inter U.2) ⟨hxC, hxU⟩
        refine ⟨Cyl D, Or.inl (Or.inl ⟨⟨D, hD⟩, rfl⟩), ?_, ?_⟩
        · exact hxD
        · intro y hy
          refine ⟨hDC hy |>.1, ?_⟩
          rw [← hUA]
          exact hDC hy |>.2
      · have hxC : x.base ∈ C.1 := hxb
        have hxU : x.base ∈ (U : Set T) := by
          have h := hxA
          rw [← hUA] at h
          exact h.1
        obtain ⟨D, hD, hxD, hDC⟩ := exists_clopen_subset
          (C.2.isOpen.inter U.2) ⟨hxC, hxU⟩
        have htD : t ∉ D := fun ht => hUt (hDC ht |>.2)
        refine ⟨One D, Or.inr ⟨⟨D, hD, htD⟩, rfl⟩, ?_, ?_⟩
        · have h := hxA
          rw [← hUA] at h
          exact ⟨hxD, h.2⟩
        · intro y hy
          refine ⟨hDC hy.1 |>.1, ?_⟩
          rw [← hUA]
          exact ⟨hDC hy.1 |>.2, hy.2⟩
    · rcases hA with (rfl | ⟨U, hUA⟩) | ⟨U, hUt, hUA⟩
      · refine ⟨H ∩ Cyl C.1, Or.inl (Or.inr ⟨C, rfl⟩), hxb, ?_⟩
        intro y hy
        exact ⟨hy, hy.1⟩
      · have hxC : x.base ∈ C.1 := hxb.2
        have hxU : x.base ∈ (U : Set T) := by
          have h := hxA
          rw [← hUA] at h
          exact h
        obtain ⟨D, hD, hxD, hDC⟩ := exists_clopen_subset
          (C.2.isOpen.inter U.2) ⟨hxC, hxU⟩
        refine ⟨H ∩ Cyl D, Or.inl (Or.inr ⟨⟨D, hD⟩, rfl⟩),
          ⟨hxb.1, hxD⟩, ?_⟩
        intro y hy
        refine ⟨⟨hy.1, hDC hy.2 |>.1⟩, ?_⟩
        rw [← hUA]
        exact hDC hy.2 |>.2
      · have hxC : x.base ∈ C.1 := hxb.2
        have hxU : x.base ∈ (U : Set T) := by
          have h := hxA
          rw [← hUA] at h
          exact h.1
        obtain ⟨D, hD, hxD, hDC⟩ := exists_clopen_subset
          (C.2.isOpen.inter U.2) ⟨hxC, hxU⟩
        have htD : t ∉ D := fun ht => hUt (hDC ht |>.2)
        refine ⟨One D, Or.inr ⟨⟨D, hD, htD⟩, rfl⟩,
          ?_, ?_⟩
        · have h := hxA
          rw [← hUA] at h
          exact ⟨hxD, h.2⟩
        intro y hy
        refine ⟨⟨hOne_subset_H hD htD hy, hDC hy.1 |>.1⟩, ?_⟩
        rw [← hUA]
        exact ⟨hDC hy.1 |>.2, hy.2⟩
    · rcases hA with (rfl | ⟨U, hUA⟩) | ⟨U, hUt, hUA⟩
      · refine ⟨One C.1, Or.inr ⟨C, rfl⟩, hxb, ?_⟩
        intro y hy
        exact ⟨hy, hOne_subset_H C.2.1 C.2.2 hy⟩
      · have hxC : x.base ∈ C.1 := hxb.1
        have hxU : x.base ∈ (U : Set T) := by
          have h := hxA
          rw [← hUA] at h
          exact h
        obtain ⟨D, hD, hxD, hDC⟩ := exists_clopen_subset
          (C.2.1.isOpen.inter U.2) ⟨hxC, hxU⟩
        have htD : t ∉ D := fun ht => C.2.2 (hDC ht |>.1)
        refine ⟨One D, Or.inr ⟨⟨D, hD, htD⟩, rfl⟩,
          ⟨hxD, hxb.2⟩, ?_⟩
        intro y hy
        refine ⟨⟨hDC hy.1 |>.1, hy.2⟩, ?_⟩
        rw [← hUA]
        exact hDC hy.1 |>.2
      · have hxC : x.base ∈ C.1 := hxb.1
        have hxU : x.base ∈ (U : Set T) := by
          have h := hxA
          rw [← hUA] at h
          exact h.1
        obtain ⟨D, hD, hxD, hDC⟩ := exists_clopen_subset
          (C.2.1.isOpen.inter U.2) ⟨hxC, hxU⟩
        have htD : t ∉ D := fun ht => hUt (hDC ht |>.2)
        refine ⟨One D, Or.inr ⟨⟨D, hD, htD⟩, rfl⟩,
          ?_, ?_⟩
        · have h := hxA
          rw [← hUA] at h
          exact ⟨hxD, h.2⟩
        intro y hy
        refine ⟨⟨hDC hy.1 |>.1, hy.2⟩, ?_⟩
        rw [← hUA]
        exact ⟨hDC hy.1 |>.2, hy.2⟩
  have hfinite_refine :
      ∀ f : Set (Set (NotWLocalExamplePoint T t)), f.Finite →
        f ⊆ notWLocalExampleSubbasis t →
          ∀ x, x ∈ ⋂₀ f →
            ∃ b ∈ B, x ∈ b ∧ b ⊆ ⋂₀ f := by
    intro f hf
    induction f, hf using Set.Finite.induction_on with
    | empty =>
        intro hfs x hx
        refine ⟨Cyl Set.univ,
          Or.inl (Or.inl ⟨⟨Set.univ, isClopen_univ⟩, rfl⟩), ?_, ?_⟩
        · change x.base ∈ (Set.univ : Set T)
          simp
        · intro y hy
          simp only [sInter_empty, mem_univ]
    | @insert A f hAf hf ih =>
        intro hfs x hx
        have hx' : x ∈ A ∧ x ∈ ⋂₀ f := by
          simpa only [sInter_insert, mem_inter_iff] using hx
        obtain ⟨b, hb, hxb, hbf⟩ :=
          ih (fun y hy => hfs (Set.mem_insert_of_mem A hy)) x hx'.2
        obtain ⟨d, hd, hxd, hdbA⟩ :=
          hB_refine_subbasis hb hxb (hfs (Set.mem_insert A f)) hx'.1
        refine ⟨d, hd, hxd, ?_⟩
        rw [sInter_insert]
        intro y hy
        exact ⟨(hdbA hy).2, hbf (hdbA hy).1⟩
  have hB_basis : IsTopologicalBasis B := by
    have hS := TopologicalSpace.isTopologicalBasis_of_subbasis
      (t := notWLocalExampleTopologicalSpace t)
      (s := notWLocalExampleSubbasis t) rfl
    apply hS.isTopologicalBasis_of_exists_subset hB_open
    rintro u ⟨f, ⟨hf, hfs⟩, rfl⟩ x hx
    exact hfinite_refine f hf hfs x hx
  have hprespectral : PrespectralSpace (NotWLocalExamplePoint T t) :=
    PrespectralSpace.of_isTopologicalBasis hB_basis hB_compact
  let b : B → Set (NotWLocalExamplePoint T t) := fun U => U.1
  have hbasis : IsTopologicalBasis (Set.range b) := by
    simpa [b] using hB_basis
  have hB_inter_mem {U V : Set (NotWLocalExamplePoint T t)}
      (hU : U ∈ B) (hV : V ∈ B) : U ∩ V ∈ B := by
    simp only [B, Set.mem_union, Set.mem_range] at hU hV
    rcases hU with (⟨C, rfl⟩ | ⟨C, rfl⟩) | ⟨C, rfl⟩ <;>
      rcases hV with (⟨D, rfl⟩ | ⟨D, rfl⟩) | ⟨D, rfl⟩
    · exact Or.inl (Or.inl ⟨⟨C.1 ∩ D.1, IsClopen.inter C.2 D.2⟩, by
        ext x
        simp [Cyl]
      ⟩)
    · exact Or.inl (Or.inr ⟨⟨C.1 ∩ D.1, IsClopen.inter C.2 D.2⟩, by
        ext x
        change (x ∈ H ∧ x.base ∈ C.1 ∧ x.base ∈ D.1) ↔
          x.base ∈ C.1 ∧ x ∈ H ∧ x.base ∈ D.1
        constructor
        · rintro ⟨hxH, hxC, hxD⟩
          exact ⟨hxC, hxH, hxD⟩
        · rintro ⟨hxC, hxH, hxD⟩
          exact ⟨hxH, hxC, hxD⟩
      ⟩)
    · exact Or.inr ⟨⟨C.1 ∩ D.1,
          ⟨IsClopen.inter C.2 D.2.1, fun ht => D.2.2 ht.2⟩⟩, by
        ext x
        change (x.base ∈ C.1 ∧ x.base ∈ D.1) ∧ x.component = true ↔
          x.base ∈ C.1 ∧ x.base ∈ D.1 ∧ x.component = true
        constructor
        · rintro ⟨⟨hxC, hxD⟩, hxt⟩
          exact ⟨hxC, hxD, hxt⟩
        · rintro ⟨hxC, hxD, hxt⟩
          exact ⟨⟨hxC, hxD⟩, hxt⟩
      ⟩
    · exact Or.inl (Or.inr ⟨⟨C.1 ∩ D.1, IsClopen.inter C.2 D.2⟩, by
        ext x
        simp [Cyl, and_assoc, and_left_comm, and_comm]
      ⟩)
    · exact Or.inl (Or.inr ⟨⟨C.1 ∩ D.1, IsClopen.inter C.2 D.2⟩, by
        ext x
        simp [Cyl, and_assoc, and_left_comm, and_comm]
      ⟩)
    · exact Or.inr ⟨⟨C.1 ∩ D.1,
          ⟨IsClopen.inter C.2 D.2.1, fun ht => D.2.2 ht.2⟩⟩, by
        ext x
        change (x.base ∈ C.1 ∩ D.1 ∧ x.component = true) ↔
          ((x ∈ H ∧ x.base ∈ C.1) ∧
            (x.base ∈ D.1 ∧ x.component = true))
        constructor
        · rintro ⟨⟨hxC, hxD⟩, hxt⟩
          exact ⟨⟨hOne_subset_H D.2.1 D.2.2 ⟨hxD, hxt⟩, hxC⟩,
            ⟨hxD, hxt⟩⟩
        · rintro ⟨⟨hxH, hxC⟩, ⟨hxD, hxt⟩⟩
          exact ⟨⟨hxC, hxD⟩, hxt⟩
      ⟩
    · exact Or.inr ⟨⟨C.1 ∩ D.1,
          ⟨IsClopen.inter C.2.1 D.2, fun ht => C.2.2 ht.1⟩⟩, by
        ext x
        change (x.base ∈ C.1 ∧ x.base ∈ D.1) ∧ x.component = true ↔
          (x.base ∈ C.1 ∧ x.component = true) ∧ x.base ∈ D.1
        constructor
        · rintro ⟨⟨hxC, hxD⟩, hxt⟩
          exact ⟨⟨hxC, hxt⟩, hxD⟩
        · rintro ⟨⟨hxC, hxt⟩, hxD⟩
          exact ⟨⟨hxC, hxD⟩, hxt⟩
      ⟩
    · refine Or.inr ⟨⟨C.1 ∩ D.1,
          ⟨IsClopen.inter C.2.1 D.2, fun ht => C.2.2 ht.1⟩⟩, ?_⟩
      ext x
      change (x.base ∈ C.1 ∩ D.1 ∧ x.component = true) ↔
        ((x.base ∈ C.1 ∧ x.component = true) ∧
          (x ∈ H ∧ x.base ∈ D.1))
      constructor
      · rintro ⟨⟨hxC, hxD⟩, hxt⟩
        exact ⟨⟨hxC, hxt⟩,
          ⟨hOne_subset_H C.2.1 C.2.2 ⟨hxC, hxt⟩, hxD⟩⟩
      · intro hx
        rcases hx with ⟨⟨hxC, hxt⟩, ⟨hxH, hxD⟩⟩
        exact ⟨⟨hxC, hxD⟩, hxt⟩
    · refine Or.inr ⟨⟨C.1 ∩ D.1,
          ⟨IsClopen.inter C.2.1 D.2.1, fun ht => C.2.2 ht.1⟩⟩, ?_⟩
      ext x
      change (x.base ∈ C.1 ∩ D.1 ∧ x.component = true) ↔
        ((x.base ∈ C.1 ∧ x.component = true) ∧
          (x.base ∈ D.1 ∧ x.component = true))
      constructor
      · rintro ⟨⟨hxC, hxD⟩, hxt⟩
        exact ⟨⟨hxC, hxt⟩, ⟨hxD, hxt⟩⟩
      · intro hx
        rcases hx with ⟨⟨hxC, hxt⟩, ⟨hxD, hxt'⟩⟩
        exact ⟨⟨hxC, hxD⟩, hxt⟩
  have hquasiSeparated : QuasiSeparatedSpace (NotWLocalExamplePoint T t) :=
    QuasiSeparatedSpace.of_isTopologicalBasis hbasis
      (fun U V => hB_compact _ (hB_inter_mem U.2 V.2))
  have hclopen_separates {a b : T} (hab : a ≠ b) :
      ∃ C : Set T, IsClopen C ∧ b ∈ C ∧ a ∉ C := by
    obtain ⟨C, hC, hbC, hCab⟩ := exists_clopen_subset
      (isClosed_singleton.isOpen_compl : IsOpen (({a} : Set T)ᶜ))
      (by simpa [ne_comm, hab])
    refine ⟨C, hC, hbC, ?_⟩
    intro haC
    exact (by simpa using hCab haC)
  have hH_transfer {x y : NotWLocalExamplePoint T t}
      (hbase : x.base = y.base)
      (hcomp : x.component = y.component ∨
        (x.component = true ∧ y.component = false))
      (hy : y ∈ H) : x ∈ H := by
    rcases x with ⟨sx, bx⟩
    rcases y with ⟨sy, by'⟩
    simp only [H, Set.mem_sdiff, Set.mem_univ, true_and] at hy ⊢
    intro hx
    rcases hcomp with hcomp | hcomp
    · simp_all
    · simp_all
  have hcontra_false_true {x y : NotWLocalExamplePoint T t}
      (hxy : x ⤳ y) (hbase : x.base = y.base)
      (hxc : x.component = false) (hyc : y.component = true) : False := by
    by_cases hxt : x.base = t
    · have hyNe : y ≠ ⟨t, false⟩ := by
        intro hyEq
        have hyfalse : y.component = false := by simp [hyEq]
        exact Bool.noConfusion (hyc.symm.trans hyfalse)
      have hyH : y ∈ H := by simp [H, hyNe]
      have hxH : x ∉ H := by
        intro hx
        have hxEq : x = ⟨t, false⟩ := by
          cases x with
          | mk sx bx =>
            change sx = t at hxt
            change bx = false at hxc
            cases hxt
            cases hxc
            rfl
        have hxNe : x ≠ ⟨t, false⟩ := by simpa [H] using hx
        exact hxNe hxEq
      exact hxH ((specializes_iff_forall_open.mp hxy) _ hH_open hyH)
    · obtain ⟨C, hC, hxC, hCt⟩ := exists_clopen_subset
        (isClosed_singleton.isOpen_compl : IsOpen (({t} : Set T)ᶜ))
        (by simpa [hxt])
      have hyC : y.base ∈ C := by simpa [hbase] using hxC
      have hyOne : y ∈ One C := by simp [One, hyC, hyc]
      have htC : t ∉ C := by
        intro ht
        have : t ∈ ({t} : Set T)ᶜ := hCt ht
        simp at this
      have hxOne : x ∉ One C := by simp [One, hxc]
      exact hxOne ((specializes_iff_forall_open.mp hxy) _
        (hOne_open hC htC) hyOne)
  have hspecializes_iff {x y : NotWLocalExamplePoint T t} :
      x ⤳ y ↔ x.base = y.base ∧
        (x.component = y.component ∨
          (x.component = true ∧ y.component = false)) := by
    constructor
    · intro hxy
      have hbase : x.base = y.base := by
        by_contra hne
        obtain ⟨C, hC, hyC, hxC⟩ := hclopen_separates hne
        have hyopen : y ∈ Cyl C := hyC
        have hxopen : x ∈ Cyl C :=
          (specializes_iff_forall_open.mp hxy) _ (hCyl_open hC) hyopen
        exact hxC hxopen
      refine ⟨hbase, ?_⟩
      cases hxc : x.component <;> cases hyc : y.component
      · exact Or.inl (by simp)
      · exact False.elim (hcontra_false_true hxy hbase hxc hyc)
      · exact Or.inr (by simp)
      · exact Or.inl (by simp)
    · rintro ⟨hbase, hcomp⟩
      apply specializes_iff_forall_open.mpr
      intro O hO hyO
      obtain ⟨b, hb, hyb, hbO⟩ := hB_basis.exists_subset_of_mem_open hyO hO
      simp only [B, Set.mem_union, Set.mem_range] at hb
      rcases hb with (⟨C, rfl⟩ | ⟨C, rfl⟩) | ⟨C, rfl⟩
      · exact hbO (by simpa [Cyl, hbase] using hyb)
      · have hxH : x ∈ H := hH_transfer hbase hcomp hyb.1
        exact hbO ⟨hxH, by simpa [Cyl, hbase] using hyb.2⟩
      · rcases hcomp with hsame | hgen
        · exact hbO (by simpa [One, hbase, hsame] using hyb)
        · exfalso
          have hfalseTrue : (false : Bool) = true := hgen.2.symm.trans hyb.2
          exact Bool.noConfusion hfalseTrue
  have hclosed_iff {x : NotWLocalExamplePoint T t} :
      IsClosed ({x} : Set (NotWLocalExamplePoint T t)) ↔
        x.component = false := by
    constructor
    · intro hcl
      by_contra hnot
      have hs : x ⤳ (⟨x.base, false⟩ : NotWLocalExamplePoint T t) :=
        hspecializes_iff.mpr ⟨rfl, Or.inr ⟨by simp [hnot], rfl⟩⟩
      have hm := specializes_iff_mem_closure.mp hs
      have heq : (⟨x.base, false⟩ : NotWLocalExamplePoint T t) = x :=
        Set.mem_singleton_iff.mp (hcl.closure_subset hm)
      cases x with
      | mk sx bx =>
        simp_all
    · intro hfalse
      apply (closure_subset_iff_isClosed).mp
      intro y hy
      have hs : x ⤳ y := specializes_iff_mem_closure.mpr hy
      have hxy := hspecializes_iff.mp hs
      exact Set.mem_singleton_iff.mpr (by
        cases x with
        | mk sx bx =>
          cases y with
          | mk sy by' =>
            simp_all)
  have hclosedPoints_eq :
      closedPoints (NotWLocalExamplePoint T t) =
        notWLocalExampleClosedPointSet t := by
    ext x
    simp only [mem_closedPoints_iff, notWLocalExampleClosedPointSet, Set.mem_ofPred_eq,
      hclosed_iff]
  have hC_nontrivial {C : Set T} (hC : IsClopen C) (ht : t ∈ C) :
      ∃ s ∈ C, s ≠ t := by
    by_contra h
    have hCsub : C ⊆ ({t} : Set T) := by
      intro s hs
      by_contra hst
      exact h ⟨s, hs, hst⟩
    have hCeq : C = ({t} : Set T) := by
      apply Set.Subset.antisymm hCsub
      exact singleton_subset_iff.mpr ht
    apply hnotcompact
    rw [← hCeq]
    exact hC.compl.1.isCompact
  have hdistinguished_closure :
      notWLocalExampleDistinguishedPoint t ∈
        closure (notWLocalExampleClosedPointSet t) := by
    apply mem_closure_iff.mpr
    intro O hO hxO
    obtain ⟨b, hb, hxb, hbO⟩ := hB_basis.exists_subset_of_mem_open hxO hO
    simp only [B, Set.mem_union, Set.mem_range] at hb
    rcases hb with (⟨C, rfl⟩ | ⟨C, rfl⟩) | ⟨C, rfl⟩
    · refine ⟨⟨t, false⟩, ?_⟩
      exact ⟨hbO (by simpa [Cyl, notWLocalExampleDistinguishedPoint] using hxb),
        by simp [notWLocalExampleClosedPointSet]⟩
    · have htC : t ∈ C.1 := by
        simpa [H, Cyl, notWLocalExampleDistinguishedPoint] using hxb
      obtain ⟨s, hsC, hst⟩ := hC_nontrivial C.2 htC
      refine ⟨⟨s, false⟩, ?_⟩
      exact ⟨hbO ⟨by simp [H, hst], hsC⟩,
        by simp [notWLocalExampleClosedPointSet]⟩
    · exfalso
      have hxb' : t ∈ C.1 ∧ true = true := by
        simpa [One, notWLocalExampleDistinguishedPoint] using hxb
      exact C.2.2 hxb'.1
  have hT0 : T0Space (NotWLocalExamplePoint T t) := by
    refine (t0Space_iff_inseparable _).2 ?_
    intro x y hxy
    have hxy' := hspecializes_iff.mp (inseparable_iff_specializes_and.mp hxy).1
    have hyx' := hspecializes_iff.mp (inseparable_iff_specializes_and.mp hxy).2
    cases x with
    | mk sx bx =>
      cases y with
      | mk sy by' =>
        rcases hxy'.2 with hsame | hgen
        · rcases hyx'.2 with hsame' | hgen'
          · simp_all
          · simp_all
        · rcases hyx'.2 with hsame | hgen'
          · simp_all
          · simp_all
  let : T0Space (NotWLocalExamplePoint T t) := hT0
  have hbase_cont : Continuous (fun x : NotWLocalExamplePoint T t => x.base) := by
    rw [continuous_def]
    intro U hU
    apply hB_basis.isOpen_iff.mpr
    intro x hx
    change x.base ∈ U at hx
    obtain ⟨C, hC, hxC, hCU⟩ := exists_clopen_subset hU hx
    refine ⟨Cyl C, Or.inl (Or.inl ⟨⟨C, hC⟩, rfl⟩), ?_, ?_⟩
    · exact hxC
    · intro y hy
      exact hCU hy
  have hfalse_clopen_subset {O : Set (NotWLocalExamplePoint T t)}
      (hO : IsOpen O) {s : T}
      (hs : (⟨s, false⟩ : NotWLocalExamplePoint T t) ∈ O) :
      ∃ C : Set T, IsClopen C ∧ s ∈ C ∧ Cyl C ⊆ O := by
    obtain ⟨b, hb, hsb, hbO⟩ := hB_basis.exists_subset_of_mem_open hs hO
    simp only [B, Set.mem_union, Set.mem_range] at hb
    rcases hb with (⟨C, rfl⟩ | ⟨C, rfl⟩) | ⟨C, rfl⟩
    · exact ⟨C.1, C.2, hsb, fun y hy => hbO hy⟩
    · have hst : s ≠ t := by
        intro hst
        have hsnot : s ≠ t := by simpa [H] using hsb.1
        exact hsnot hst
      obtain ⟨D, hD, hsD, hDC⟩ := exists_clopen_subset
        (C.2.isOpen.inter isClosed_singleton.isOpen_compl)
        ⟨hsb.2, by simpa [hst]⟩
      refine ⟨D, hD, hsD, ?_⟩
      intro y hy
      change y.base ∈ D at hy
      have hyH : y ∈ H := by
        simp only [H, Set.mem_sdiff, Set.mem_univ, true_and]
        intro hyEq
        have hyEq' : y = (⟨t, false⟩ : NotWLocalExamplePoint T t) :=
          Set.mem_singleton_iff.mp hyEq
        have hyt : y.base = t := by simp [hyEq']
        have hyt_ne : y.base ≠ t := by simpa using (hDC hy).2
        exact hyt_ne hyt
      have hyC : y.base ∈ C.1 := (hDC hy).1
      exact hbO ⟨hyH, by simpa [Cyl] using hyC⟩
    · exfalso
      have hfalseTrue : (false : Bool) = true := by
        simpa [One] using hsb |>.2
      exact Bool.noConfusion hfalseTrue
  have hfinite_clopen_refinement :
      ∀ {ι : Type _} (U : ι → Opens (NotWLocalExamplePoint T t)),
        IsOpenCover U →
          ∃ (n : ℕ) (V : Fin n → Set (NotWLocalExamplePoint T t)),
            (∀ j, IsOpen (V j) ∧ IsClosed (V j)) ∧
              Pairwise (fun i j => Disjoint (V i) (V j)) ∧
                (⋃ j, V j) = (Set.univ : Set (NotWLocalExamplePoint T t)) ∧
                  ∀ j, ∃ i, V j ⊆ (U i : Set (NotWLocalExamplePoint T t)) := by
    intro ι U hU
    let iOf : T → ι := fun s => Classical.choose (hU.exists_mem
      (⟨s, false⟩ : NotWLocalExamplePoint T t))
    have hiOf (s : T) :
        (⟨s, false⟩ : NotWLocalExamplePoint T t) ∈ U (iOf s) :=
      Classical.choose_spec (hU.exists_mem
        (⟨s, false⟩ : NotWLocalExamplePoint T t))
    let COf : T → Set T := fun s => Classical.choose (hfalse_clopen_subset
      (U (iOf s)).isOpen (hiOf s))
    have hCOf (s : T) : IsClopen (COf s) ∧ s ∈ COf s ∧
        Cyl (COf s) ⊆ (U (iOf s) : Set (NotWLocalExamplePoint T t)) :=
      Classical.choose_spec (hfalse_clopen_subset
        (U (iOf s)).isOpen (hiOf s))
    let W : T → Opens T := fun s => ⟨COf s, (hCOf s).1.isOpen⟩
    have hW : IsOpenCover W := by
      apply IsOpenCover.of_sets
      exact Set.eq_univ_of_forall (fun s => Set.mem_iUnion.2 ⟨s, (hCOf s).2.1⟩)
    obtain ⟨n, V, hV, hcover, hdisj⟩ :=
      Formalization.Books.Topology.Unit22.profiniteSpace_open_cover_has_finite_clopen_refinement
        hTprofinite W hW
    refine ⟨n, fun j => Cyl (V j : Set T), ?_, ?_, ?_, ?_⟩
    · intro j
      exact ⟨(hCyl_clopen (V j).isClopen).isOpen,
        (hCyl_clopen (V j).isClopen).isClosed⟩
    · intro j k hjk
      rw [Set.disjoint_left]
      intro x hxj hxk
      exact (Set.disjoint_left.1 (Clopens.coe_disjoint.mpr (hdisj hjk)))
        hxj hxk
    · ext x
      constructor
      · intro hx
        simp
      · intro hx
        have hxV : x.base ∈ ⋃ j, (V j : Set T) := by
          rw [hcover]
          simp
        obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxV
        exact Set.mem_iUnion.2 ⟨j, hxj⟩
    · intro j
      obtain ⟨hjV, ⟨s, hsV⟩⟩ := hV j
      refine ⟨iOf s, ?_⟩
      intro x hx
      change x.base ∈ (V j : Set T) at hx
      exact (hCOf s).2.2 (hsV hx)
  have hquasiSober : QuasiSober (NotWLocalExamplePoint T t) := by
    constructor
    intro Z hZ hZclosed
    let pZ : Set T := (fun x : NotWLocalExamplePoint T t => x.base) '' Z
    have hpZ : IsIrreducible pZ :=
      hZ.image (fun x : NotWLocalExamplePoint T t => x.base) hbase_cont.continuousOn
    obtain ⟨s, hpZs⟩ :=
      (Formalization.Books.Topology.Unit08.hausdorff_irreducible_iff_singleton
        (E := pZ)).mp hpZ
    obtain ⟨z, hzZ⟩ := hZ.nonempty
    have hzbase : z.base = s := by
      have hzmem : z.base ∈ pZ := ⟨z, hzZ, rfl⟩
      rw [hpZs] at hzmem
      exact Set.mem_singleton_iff.mp hzmem
    let z1 : NotWLocalExamplePoint T t := ⟨s, true⟩
    let z0 : NotWLocalExamplePoint T t := ⟨s, false⟩
    by_cases hz1 : z1 ∈ Z
    · refine ⟨z1, ?_⟩
      change closure ({z1} : Set (NotWLocalExamplePoint T t)) = Z
      apply Set.Subset.antisymm
      · exact closure_minimal (singleton_subset_iff.mpr hz1) hZclosed
      · intro y hy
        have hybase : y.base = s := by
          have hymem : y.base ∈ pZ := ⟨y, hy, rfl⟩
          rw [hpZs] at hymem
          exact Set.mem_singleton_iff.mp hymem
        exact specializes_iff_mem_closure.mp
          (hspecializes_iff.mpr
            ⟨by simpa [z1] using hybase.symm, by cases y.component <;> simp [z1]⟩)
    · have hz0Z : z0 ∈ Z := by
        rcases z with ⟨b, c⟩
        cases c with
        | false =>
            change b = s at hzbase
            cases hzbase
            simpa [z0] using hzZ
        | true =>
            change b = s at hzbase
            cases hzbase
            apply False.elim
            apply hz1
            simpa [z1] using hzZ
      refine ⟨z0, ?_⟩
      change closure ({z0} : Set (NotWLocalExamplePoint T t)) = Z
      apply Set.Subset.antisymm
      · exact closure_minimal (singleton_subset_iff.mpr hz0Z) hZclosed
      · intro y hy
        have hybase : y.base = s := by
          have hymem : y.base ∈ pZ := ⟨y, hy, rfl⟩
          rw [hpZs] at hymem
          exact Set.mem_singleton_iff.mp hymem
        have hyeq : y = z0 := by
          rcases y with ⟨b, c⟩
          cases c with
          | false =>
              change b = s at hybase
              cases hybase
              rfl
          | true =>
              change b = s at hybase
              cases hybase
              apply False.elim
              apply hz1
              simpa [z1] using hy
        rw [hyeq]
        exact subset_closure rfl
  have hspectral : SpectralSpace (NotWLocalExamplePoint T t) :=
    Formalization.Books.Topology.Unit23.spectralSpace_iff_source_conditions.mpr
      ⟨hT0, inferInstance, hquasiSober, hquasiSeparated, hprespectral⟩
  have hbij := (@spectralSplit_iff_closedPointComponentMap_bijective
    (NotWLocalExamplePoint T t) _ hspectral).mp hfinite_clopen_refinement
  have hnclosed : ¬ IsClosed (closedPoints (NotWLocalExamplePoint T t)) := by
    rw [hclosedPoints_eq]
    intro hcl
    have hm := hcl.closure_subset hdistinguished_closure
    simp [notWLocalExampleDistinguishedPoint, notWLocalExampleClosedPointSet] at hm
  exact ⟨hspectral, hclosedPoints_eq, hdistinguished_closure,
    hfinite_clopen_refinement, hbij, hnclosed⟩

/-! ## W-local spaces -/

/-- A spectral space is w-local when its closed points form a closed subset
and every point specializes to exactly one closed point. -/
def IsWLocalSpace (X : Type u) [TopologicalSpace X] : Prop :=
  SpectralSpace X ∧
    IsClosed (closedPoints X) ∧
      ∀ x : X, ∃! x₀ : closedPoints X, x ⤳ (x₀ : X)

/-- A map between w-local spaces is w-local when it is spectral and maps
closed points to closed points. -/
def IsWLocalMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop :=
  IsWLocalSpace X ∧ IsWLocalSpace Y ∧
    IsSpectralMap f ∧ MapsTo f (closedPoints X) (closedPoints Y)

/-- The example is not w-local once the w-local definition has been made
explicit: its closed-point set is not closed. -/
theorem notWLocalExample_not_isWLocalSpace
    {T : Type u} [TopologicalSpace T] (hT : IsProfiniteSpace T) (t : T)
    (hnotcompact : ¬ IsCompact (({t} : Set T)ᶜ)) :
    ¬ IsWLocalSpace (NotWLocalExamplePoint T t) := by
  intro hW
  exact (notWLocalExample_properties.{u, 0} hT t hnotcompact).2.2.2.2.2 hW.2.1

/-- The assertions immediately following the definition of w-locality. -/
theorem isWLocalSpace_properties
    {X : Type u} [TopologicalSpace X] (hX : IsWLocalSpace X) :
    IsHomeomorph (closedPointComponentMap (X := X)) ∧
      IsProfiniteSpace (closedPoints X) ∧
        IsProfiniteSpace (ConnectedComponents X) ∧
          ∀ x₀ : closedPoints X,
            connectedComponent (x₀ : X) =
              pointsSpecializingTo ({(x₀ : X)} : Set X) := by
  have hbij : Function.Bijective (closedPointComponentMap (X := X)) :=
    (@spectralSplit_of_closedPoints_closed_of_unique_specialization.{u, 0}
      X _ hX.1 hX.2.1 hX.2.2).2
  have hclosedSpectral : SpectralSpace (closedPoints X) :=
    @Formalization.Books.Topology.Unit23.spectralSpace_subtype_of_isClosed
      X _ hX.1 (closedPoints X) hX.2.1
  have hclosed_singleton : ∀ z : closedPoints X,
      IsClosed ({z} : Set (closedPoints X)) := by
    intro z
    have heq : (Subtype.val : closedPoints X → X) ⁻¹'
        ({(z : X)} : Set X) = ({z} : Set (closedPoints X)) := by
      ext y
      constructor
      · intro hy
        exact Subtype.ext hy
      · intro hy
        exact congrArg Subtype.val (Set.mem_singleton_iff.mp hy)
    rw [← heq]
    exact z.property.preimage continuous_subtype_val
  have hprof : IsProfiniteSpace (closedPoints X) :=
    ((@Formalization.Books.Topology.Unit23.isProfiniteSpace_TFAE_spectral_separation_conditions
      (closedPoints X) _ hclosedSpectral).out 5 0).mp hclosed_singleton
  have hccprof : IsProfiniteSpace (ConnectedComponents X) :=
    @Formalization.Books.Topology.Unit23.connectedComponents_isProfiniteSpace X _ hX.1
  have hcompactX : CompactSpace X := hX.1.toCompactSpace
  have hT0X : T0Space X := hX.1.toT0Space
  have hcompactClosed : CompactSpace (closedPoints X) :=
    isCompact_iff_compactSpace.mp
      (@Formalization.Books.Topology.Unit12.isCompact_closedPoints X _ hcompactX hT0X)
  have hccT2 : T2Space (ConnectedComponents X) :=
    (Formalization.Books.Topology.Unit22.isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected
      (X := ConnectedComponents X)).mp hccprof |>.1
  have hfcont : Continuous (closedPointComponentMap (X := X)) := by
    exact ConnectedComponents.continuous_coe.comp continuous_subtype_val
  have hhomeo : IsHomeomorph (closedPointComponentMap (X := X)) :=
    (@isHomeomorph_iff_continuous_bijective
      (closedPoints X) (ConnectedComponents X) _ _ (closedPointComponentMap (X := X))
        hcompactClosed hccT2).mpr ⟨hfcont, hbij⟩
  have hcomponent :
      ∀ x₀ : closedPoints X,
        connectedComponent (x₀ : X) =
          pointsSpecializingTo ({(x₀ : X)} : Set X) := by
    intro x₀
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨z, hxz, _⟩ := hX.2.2 x
      have hzcompx : (z : X) ∈ connectedComponent x := by
        apply closure_minimal (singleton_subset_iff.mpr mem_connectedComponent)
          (Formalization.Books.Topology.Unit07.connectedComponent_is_closed x)
        exact specializes_iff_mem_closure.mp hxz
      have hcompx0 : connectedComponent (x₀ : X) = connectedComponent x :=
        Formalization.Books.Topology.Unit07.connectedComponent_eq_of_mem hx
      have hzcompx0 : (z : X) ∈ connectedComponent (x₀ : X) := by
        rw [hcompx0]
        exact hzcompx
      have hcc : closedPointComponentMap x₀ = closedPointComponentMap z :=
        ConnectedComponents.coe_eq_coe.mpr
          (Formalization.Books.Topology.Unit07.connectedComponent_eq_of_mem hzcompx0)
      have hzx₀ : z = x₀ := by
        exact (hbij.1 hcc).symm
      refine ⟨(x₀ : X), ?_, ?_⟩
      · exact Set.mem_singleton_iff.mpr rfl
      · simpa [hzx₀] using hxz
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := hx
      have hy' : y = (x₀ : X) := Set.mem_singleton_iff.mp hy
      subst y
      have hx₀comp : (x₀ : X) ∈ connectedComponent x := by
        apply closure_minimal (singleton_subset_iff.mpr mem_connectedComponent)
          (Formalization.Books.Topology.Unit07.connectedComponent_is_closed x)
        exact specializes_iff_mem_closure.mp hxy
      have hcomp : connectedComponent x = connectedComponent (x₀ : X) :=
        Formalization.Books.Topology.Unit07.connectedComponent_eq_of_mem hx₀comp
      rw [← hcomp]
      exact mem_connectedComponent
  exact ⟨hhomeo, hprof, hccprof, hcomponent⟩

/-- A closed subspace of a w-local spectral space is w-local. -/
theorem isWLocalSpace_subtype_of_isClosed
    {X : Type u} [TopologicalSpace X] (hX : IsWLocalSpace X)
    {Y : Set X} (hY : IsClosed Y) :
    IsWLocalSpace Y := by
  have hYspectral : SpectralSpace Y :=
    @Formalization.Books.Topology.Unit23.spectralSpace_subtype_of_isClosed
      X _ hX.1 Y hY
  have hclosedPoints :
      closedPoints Y = (Subtype.val : Y → X) ⁻¹' closedPoints X := by
    ext y
    simp only [mem_closedPoints_iff]
    constructor
    · intro hy
      obtain ⟨z, hyz, huniq⟩ := hX.2.2 (y : X)
      have hclY : closure ({(y : X)} : Set X) ⊆ Y :=
        closure_minimal (singleton_subset_iff.mpr y.property) hY
      have hzY : (z : X) ∈ Y :=
        hclY (specializes_iff_mem_closure.mp hyz)
      let zY : Y := ⟨(z : X), hzY⟩
      have hyzY : y ⤳ zY :=
        (subtype_specializes_iff y zY).mpr hyz
      have hzYeq : zY = y :=
        Set.mem_singleton_iff.mp
          ((mem_closedPoints_iff.mp hy).closure_subset
            (specializes_iff_mem_closure.mp hyzY))
      have hzval : (z : X) = (y : X) := congrArg Subtype.val hzYeq
      simpa [hzval] using z.property
    · intro hy
      have heq : (Subtype.val : Y → X) ⁻¹'
          ({(y : X)} : Set X) = ({y} : Set Y) := by
        ext z
        constructor
        · intro hz
          exact Subtype.ext hz
        · intro hz
          exact congrArg Subtype.val (Set.mem_singleton_iff.mp hz)
      rw [← heq]
      exact hy.preimage continuous_subtype_val
  have hclosedY : IsClosed (closedPoints Y) := by
    rw [hclosedPoints]
    exact hX.2.1.preimage continuous_subtype_val
  have huniqueY : ∀ y : Y, ∃! z₀ : closedPoints Y, y ⤳ (z₀ : Y) := by
    intro y
    obtain ⟨z, hyz, huniq⟩ := hX.2.2 (y : X)
    have hclY : closure ({(y : X)} : Set X) ⊆ Y :=
      closure_minimal (singleton_subset_iff.mpr y.property) hY
    have hzY : (z : X) ∈ Y :=
      hclY (specializes_iff_mem_closure.mp hyz)
    let zY : Y := ⟨(z : X), hzY⟩
    have hyzY : y ⤳ zY :=
      (subtype_specializes_iff y zY).mpr hyz
    have hzYclosed : zY ∈ closedPoints Y := by
      rw [hclosedPoints]
      change (z : X) ∈ closedPoints X
      exact z.property
    refine ⟨⟨zY, hzYclosed⟩, hyzY, ?_⟩
    intro z' hz'
    have hz'pre : (z' : Y) ∈ (Subtype.val : Y → X) ⁻¹' closedPoints X := by
      rw [← hclosedPoints]
      exact z'.property
    have hz'X : (z' : X) ∈ closedPoints X := hz'pre
    let zX' : closedPoints X := ⟨(z' : X), hz'X⟩
    have hyz'X : (y : X) ⤳ (z' : X) :=
      (subtype_specializes_iff y z').mp hz'
    have hzx' : zX' = z := huniq zX' hyz'X
    have hzYeq : (z' : Y) = zY := by
      apply Subtype.ext
      change (z' : X) = (z : X)
      exact congrArg Subtype.val hzx'
    apply Subtype.ext
    exact hzYeq
  exact ⟨hYspectral, hclosedY, huniqueY⟩

/-! ## The cartesian base-change lemma -/

/- The connected-components quotient map, bundled as a morphism in `TopCat`,
is the bottom map in the source diagram. -/
def connectedComponentsMapHom {X : Type u} [TopologicalSpace X] :
    TopCat.of X ⟶ TopCat.of (ConnectedComponents X) :=
  TopCat.ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩

/-- A cartesian square over the connected-components quotient of `X`. -/
structure CartesianComponentSquare
    (X : Type u) [TopologicalSpace X] where
  Y : TopCat.{u}
  T : TopCat.{u}
  toT : Y ⟶ T
  toX : Y ⟶ TopCat.of X
  toPi0 : T ⟶ TopCat.of (ConnectedComponents X)
  isPullback :
    IsPullback toT toX toPi0 (connectedComponentsMapHom (X := X))

/-- The last lemma of the section: the cartesian pullback over a profinite
space has the asserted spectral and w-local properties.  The identification
`T = π₀(Y)` is represented by a homeomorphism, since a pullback object is only
canonically determined up to homeomorphism in `TopCat`. -/
theorem cartesianComponentSquare_silly
    {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    (sq : CartesianComponentSquare X)
    (hT : IsProfiniteSpace (sq.T : Type u)) :
    SpectralSpace (sq.Y : Type u) ∧
      Nonempty ((sq.T : Type u) ≃ₜ ConnectedComponents (sq.Y : Type u)) ∧
        (IsWLocalSpace X →
          IsWLocalSpace (sq.Y : Type u) ∧
            IsWLocalMap sq.toX.hom ∧
              closedPoints (sq.Y : Type u) =
                sq.toX.hom ⁻¹' closedPoints X) := by
  classical
  let T : Type u := (sq.T : Type u)
  have hcc : IsProfiniteSpace (ConnectedComponents X) :=
    Formalization.Books.Topology.Unit23.connectedComponents_isProfiniteSpace
  obtain ⟨Pcc, ⟨ecc⟩⟩ := hcc
  letI : T2Space (ConnectedComponents X) := ecc.symm.t2Space
  letI : CompactSpace (ConnectedComponents X) := ecc.symm.compactSpace
  letI : TotallyDisconnectedSpace (ConnectedComponents X) :=
    ecc.symm.totallyDisconnectedSpace
  obtain ⟨PT, ⟨eT0⟩⟩ := hT
  let eT : T ≃ₜ (PT : Type u) := eT0
  letI : T2Space T := eT.symm.t2Space
  letI : CompactSpace T := eT.symm.compactSpace
  letI : TotallyDisconnectedSpace T := eT.symm.totallyDisconnectedSpace
  letI : PrespectralSpace T :=
    PrespectralSpace.of_isTopologicalBasis isTopologicalBasis_isClopen
      (fun U hU => hU.1.isCompact)
  letI : SpectralSpace T :=
    Formalization.Books.Topology.Unit23.spectralSpace_iff_source_conditions.mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  letI : SpectralSpace (T × X) :=
    Formalization.Books.Topology.Unit23.spectralSpace_prod
  let hPclosed : IsClosed ({p : T × X |
      sq.toPi0.hom p.1 = ConnectedComponents.mk p.2} : Set (T × X)) :=
    Formalization.Books.Topology.Unit03.isClosed_fiberProduct
      sq.toPi0.hom ConnectedComponents.mk sq.toPi0.hom.continuous
        ConnectedComponents.continuous_coe
  let P : Type u := {p : T × X //
      sq.toPi0.hom p.1 = ConnectedComponents.mk p.2}
  letI : SpectralSpace P :=
    Formalization.Books.Topology.Unit23.spectralSpace_subtype_of_isClosed hPclosed
  let eY : (sq.Y : Type u) ≃ₜ P :=
    TopCat.homeoOfIso
      (sq.isPullback.isoPullback ≪≫
        TopCat.pullbackIsoProdSubtype sq.toPi0
          (connectedComponentsMapHom (X := X)))
  have heY_t (y : (sq.Y : Type u)) :
      (eY y).val.1 = sq.toT.hom y := by
    change pullback.fst sq.toPi0 (connectedComponentsMapHom (X := X))
        ((sq.isPullback.isoPullback).hom y) = sq.toT.hom y
    exact congrArg (fun k => k.hom y)
      (CategoryTheory.IsPullback.isoPullback_hom_fst sq.isPullback)
  have heY_x (y : (sq.Y : Type u)) :
      (eY y).val.2 = sq.toX.hom y := by
    change pullback.snd sq.toPi0 (connectedComponentsMapHom (X := X))
        ((sq.isPullback.isoPullback).hom y) = sq.toX.hom y
    exact congrArg (fun k => k.hom y)
      (CategoryTheory.IsPullback.isoPullback_hom_snd sq.isPullback)
  have hYspectral : SpectralSpace (sq.Y : Type u) :=
    Formalization.Books.Topology.Unit23.spectralSpace_iff_source_conditions.mpr
      ⟨eY.isEmbedding.t0Space,
        eY.symm.compactSpace,
        eY.isOpenEmbedding.quasiSober,
        (quasiSeparatedSpace_congr eY).mpr inferInstance,
        PrespectralSpace.of_isInducing eY eY.isInducing
          eY.isProperMap.isSpectralMap⟩
  letI : SpectralSpace (sq.Y : Type u) := hYspectral
  letI : CompactSpace (sq.Y : Type u) := hYspectral.toCompactSpace
  have hfiber (t : T) :
      IsConnected (sq.toT.hom ⁻¹' ({t} : Set T)) := by
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (sq.toPi0.hom t)
    let S : Set P := {p | p.val.1 = t}
    let Q : Set X := connectedComponent x
    let ef : S ≃ₜ Q :=
      { toFun := fun p =>
          ⟨p.val.val.2, by
            apply ConnectedComponents.coe_eq_coe'.mp
            calc
              ConnectedComponents.mk p.val.val.2 =
                  sq.toPi0.hom p.val.val.1 := p.val.property.symm
              _ = sq.toPi0.hom t := by rw [p.property]
              _ = ConnectedComponents.mk x := hx.symm⟩
        invFun := fun z =>
          ⟨⟨⟨t, z.val⟩, by
            exact hx.symm.trans (ConnectedComponents.coe_eq_coe'.mpr z.property).symm⟩, rfl⟩
        left_inv := by
          intro p
          apply Subtype.ext
          apply Subtype.ext
          apply Prod.ext
          · exact p.property.symm
          · rfl
        right_inv := by
          intro z
          rfl
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact continuous_snd.comp
            (continuous_subtype_val.comp continuous_subtype_val)
        continuous_invFun := by
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          exact continuous_const.prodMk continuous_subtype_val }
    letI : ConnectedSpace Q := Subtype.connectedSpace isConnected_connectedComponent
    letI : ConnectedSpace S := ef.symm.surjective.connectedSpace ef.symm.continuous
    have hSconn : IsConnected S :=
      isConnected_iff_connectedSpace.mpr inferInstance
    have hpre : IsConnected (eY ⁻¹' S) :=
      (eY.isConnected_preimage).mpr hSconn
    have hEq : sq.toT.hom ⁻¹' ({t} : Set T) = eY ⁻¹' S := by
      ext y
      change sq.toT.hom y = t ↔ (eY y).val.1 = t
      rw [heY_t]
    rw [← hEq] at hpre
    exact hpre
  obtain ⟨g, hgcont, hgcomp⟩ :=
    Formalization.Books.Topology.Unit07.continuous_map_factors_through_connectedComponents
      sq.toT.hom.continuous
  have hgbij : Function.Bijective g := by
    constructor
    · intro c₁ c₂ hgc
      obtain ⟨y₁, rfl⟩ := ConnectedComponents.surjective_coe c₁
      obtain ⟨y₂, rfl⟩ := ConnectedComponents.surjective_coe c₂
      have hty : sq.toT.hom y₁ = sq.toT.hom y₂ := by
        calc
          sq.toT.hom y₁ = g (ConnectedComponents.mk y₁) := by
            simpa [Function.comp_def] using congrFun hgcomp y₁ |>.symm
          _ = g (ConnectedComponents.mk y₂) := hgc
          _ = sq.toT.hom y₂ := by
            simpa [Function.comp_def] using congrFun hgcomp y₂
      apply ConnectedComponents.coe_eq_coe'.mpr
      have hy₂fiber : y₂ ∈ sq.toT.hom ⁻¹' ({sq.toT.hom y₁} : Set T) := by
        exact hty.symm
      have hy₁fiber : y₁ ∈ sq.toT.hom ⁻¹' ({sq.toT.hom y₁} : Set T) :=
        rfl
      exact (hfiber _).isPreconnected.subset_connectedComponent hy₂fiber hy₁fiber
    · intro t
      obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (sq.toPi0.hom t)
      let p : P := ⟨⟨t, x⟩, hx.symm⟩
      let y : (sq.Y : Type u) := eY.symm p
      refine ⟨ConnectedComponents.mk y, ?_⟩
      calc
        g (ConnectedComponents.mk y) = sq.toT.hom y := by
          simpa [Function.comp_def] using congrFun hgcomp y
        _ = t := by
          simpa [y, p] using (heY_t y).symm
  have hGhomeo : IsHomeomorph g :=
    (@isHomeomorph_iff_continuous_bijective
      (ConnectedComponents (sq.Y : Type u)) T _ _ g inferInstance inferInstance).mpr
      ⟨hgcont, hgbij⟩
  let eCT : ConnectedComponents (sq.Y : Type u) ≃ₜ T :=
    hGhomeo.homeomorph g
  refine ⟨hYspectral, ⟨eCT.symm⟩, ?_⟩
  intro hX
  have hcomponent : ∀ {a b : X}, a ⤳ b →
      ConnectedComponents.mk a = ConnectedComponents.mk b := by
    intro a b hab
    apply ConnectedComponents.coe_eq_coe.mpr
    apply Formalization.Books.Topology.Unit07.connectedComponent_eq_of_mem
    apply closure_minimal (singleton_subset_iff.mpr mem_connectedComponent)
      (Formalization.Books.Topology.Unit07.connectedComponent_is_closed a)
    exact specializes_iff_mem_closure.mp hab
  have hcomm (y : (sq.Y : Type u)) :
      sq.toPi0.hom (sq.toT.hom y) =
        ConnectedComponents.mk (sq.toX.hom y) := by
    simpa [connectedComponentsMapHom] using ConcreteCategory.congr_hom sq.isPullback.w y
  have hclosed_of_closed_coordinate {z : (sq.Y : Type u)}
      {x₀ : closedPoints X} (hzx : sq.toX.hom z = (x₀ : X)) :
      z ∈ closedPoints (sq.Y : Type u) := by
    rw [mem_closedPoints_iff]
    rw [← closure_subset_iff_isClosed]
    intro z' hz'
    have hzspec : z ⤳ z' := specializes_iff_mem_closure.mpr hz'
    have hxz' : sq.toX.hom z ⤳ sq.toX.hom z' :=
      hzspec.map sq.toX.hom.continuous
    have hx₀z' : (x₀ : X) = sq.toX.hom z' := by
      have hz'x₀ : sq.toX.hom z' ∈ ({(x₀ : X)} : Set X) :=
        x₀.property.closure_subset (by
          rw [← hzx]
          exact specializes_iff_mem_closure.mp hxz')
      exact (Set.mem_singleton_iff.mp hz'x₀).symm
    have htz : sq.toT.hom z = sq.toT.hom z' :=
      specializes_iff_eq.mp
        (hzspec.map sq.toT.hom.continuous)
    apply eY.injective
    apply Subtype.ext
    apply Prod.ext
    · calc
        (eY z').val.1 = sq.toT.hom z' := heY_t z'
        _ = sq.toT.hom z := htz.symm
        _ = (eY z).val.1 := (heY_t z).symm
    · calc
        (eY z').val.2 = sq.toX.hom z' := heY_x z'
        _ = (x₀ : X) := hx₀z'.symm
        _ = sq.toX.hom z := hzx.symm
        _ = (eY z).val.2 := (heY_x z).symm
  have hcanonical (y : (sq.Y : Type u)) :
      ∃ (x₀ : closedPoints X) (y₀ : (sq.Y : Type u)),
        y ⤳ y₀ ∧ sq.toX.hom y₀ = (x₀ : X) := by
    obtain ⟨x₀, hyx₀, -⟩ := hX.2.2 (sq.toX.hom y)
    let p₀ : P := ⟨⟨sq.toT.hom y, x₀⟩,
      (hcomm y).trans (hcomponent hyx₀)⟩
    let y₀ : (sq.Y : Type u) := eY.symm p₀
    refine ⟨x₀, y₀, ?_, ?_⟩
    · apply eY.isInducing.specializes_iff.mp
      rw [show eY y₀ = p₀ by simp [y₀]]
      apply (subtype_specializes_iff _ _).mpr
      change ((eY y).val.1, (eY y).val.2) ⤳
        (sq.toT.hom y, (x₀ : X))
      apply specializes_prod.mpr
      constructor
      · rw [heY_t y]
      · rw [heY_x y]
        exact hyx₀
    · simpa [y₀, p₀] using (heY_x y₀).symm
  have huniqueY : ∀ y : (sq.Y : Type u), ∃! z₀ : closedPoints (sq.Y : Type u),
      y ⤳ (z₀ : (sq.Y : Type u)) := by
    intro y
    obtain ⟨x₀, y₀, hy₀, hy₀x⟩ := hcanonical y
    have hy₀closed : y₀ ∈ closedPoints (sq.Y : Type u) :=
      hclosed_of_closed_coordinate hy₀x
    refine ⟨⟨y₀, hy₀closed⟩, hy₀, ?_⟩
    intro z hz
    obtain ⟨x₁, y₁, hz₀, hz₀x⟩ := hcanonical (z : (sq.Y : Type u))
    have hy₁z : y₁ = (z : (sq.Y : Type u)) := by
      apply Set.mem_singleton_iff.mp
      exact z.property.closure_subset (specializes_iff_mem_closure.mp hz₀)
    have hxy₁ : (sq.toX.hom y) ⤳ (x₁ : X) := by
      have hzx₁ : (sq.toX.hom (z : (sq.Y : Type u))) ⤳ (x₁ : X) := by
        rw [← hz₀x]
        exact hz₀.map sq.toX.hom.continuous
      exact (hz.map sq.toX.hom.continuous).trans hzx₁
    obtain ⟨xstar, hystar, hxustar⟩ := hX.2.2 (sq.toX.hom y)
    have hyx₀ : (sq.toX.hom y) ⤳ (x₀ : X) := by
      rw [← hy₀x]
      exact hy₀.map sq.toX.hom.continuous
    have hx₁x₀ : (x₁ : X) = (x₀ : X) :=
      congrArg Subtype.val ((hxustar x₁ hxy₁).trans (hxustar x₀ hyx₀).symm)
    apply Subtype.ext
    apply eY.injective
    apply Subtype.ext
    apply Prod.ext
    · have hty : sq.toT.hom y = sq.toT.hom (z : (sq.Y : Type u)) :=
        specializes_iff_eq.mp (hz.map sq.toT.hom.continuous)
      have hty₀ : sq.toT.hom y = sq.toT.hom y₀ :=
        specializes_iff_eq.mp (hy₀.map sq.toT.hom.continuous)
      calc
        (eY (z : (sq.Y : Type u))).val.1 =
            sq.toT.hom (z : (sq.Y : Type u)) := heY_t _
        _ = sq.toT.hom y := hty.symm
        _ = sq.toT.hom y₀ := hty₀
        _ = (eY y₀).val.1 := (heY_t y₀).symm
    · calc
        (eY (z : (sq.Y : Type u))).val.2 =
            sq.toX.hom (z : (sq.Y : Type u)) := heY_x _
        _ = (x₁ : X) := by
          calc
            sq.toX.hom (z : (sq.Y : Type u)) = sq.toX.hom y₁ :=
              congrArg sq.toX.hom hy₁z.symm
            _ = (x₁ : X) := hz₀x
        _ = (x₀ : X) := hx₁x₀
        _ = sq.toX.hom y₀ := hy₀x.symm
        _ = (eY y₀).val.2 := (heY_x y₀).symm
  have hclosed_eq :
      closedPoints (sq.Y : Type u) =
        sq.toX.hom ⁻¹' closedPoints X := by
    ext y
    constructor
    · intro hy
      rw [mem_closedPoints_iff] at hy
      obtain ⟨x₀, y₀, hy₀, hy₀x⟩ := hcanonical y
      have hy₀eq : y₀ = y := by
        apply Set.mem_singleton_iff.mp
        exact hy.closure_subset (specializes_iff_mem_closure.mp hy₀)
      have hx₀eq : (x₀ : X) = sq.toX.hom y := by
        calc
          (x₀ : X) = sq.toX.hom y₀ := hy₀x.symm
          _ = sq.toX.hom y := congrArg sq.toX.hom hy₀eq
      simpa [hx₀eq] using x₀.property
    · intro hy
      change sq.toX.hom y ∈ closedPoints X at hy
      let x₀ : closedPoints X := ⟨sq.toX.hom y, hy⟩
      exact hclosed_of_closed_coordinate (x₀ := x₀) rfl
  have hclosedY : IsClosed (closedPoints (sq.Y : Type u)) := by
    rw [hclosed_eq]
    exact hX.2.1.preimage sq.toX.hom.continuous
  have hYwlocal : IsWLocalSpace (sq.Y : Type u) :=
    ⟨hYspectral, hclosedY, huniqueY⟩
  have hcompact_preimage {U : Set X} (hUopen : IsOpen U)
      (hUcompact : IsCompact U) :
      IsCompact (sq.toX.hom ⁻¹' U) := by
    let W : Set P := {p : P | p.val.2 ∈ U}
    have hTUcompact : IsCompact ((Set.univ : Set T) ×ˢ U) :=
      isCompact_univ.prod hUcompact
    have hW : IsCompact W := by
      have hpre := Topology.IsInducing.isCompact_preimage
        (f := (Subtype.val : P → T × X)) IsInducing.subtypeVal
        (by simpa using hPclosed) hTUcompact
      have hset :
          (Subtype.val : P → T × X) ⁻¹' ((Set.univ : Set T) ×ˢ U) = W := by
        ext p
        dsimp [W]
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ,
          Set.mem_setOf_eq, true_and]
        change p.val.2 ∈ U ↔ p.val.2 ∈ U
        rfl
      rw [← hset]
      exact hpre
    have himage : eY '' (sq.toX.hom ⁻¹' U) = W := by
      ext p
      constructor
      · rintro ⟨y, hy, rfl⟩
        change (eY y).val.2 ∈ U
        change sq.toX.hom y ∈ U at hy
        rw [heY_x y]
        exact hy
      · intro hp
        refine ⟨eY.symm p, ?_, eY.apply_symm_apply p⟩
        change sq.toX.hom (eY.symm p) ∈ U
        rw [← heY_x (eY.symm p)]
        change p.val.2 ∈ U at hp
        simpa using hp
    apply (eY.isEmbedding.isCompact_iff).mpr
    rw [himage]
    exact hW
  have htoXspectral : IsSpectralMap sq.toX.hom :=
    ⟨sq.toX.hom.continuous, fun _ hUopen hUcompact =>
      hcompact_preimage hUopen hUcompact⟩
  have hmaps : MapsTo sq.toX.hom
      (closedPoints (sq.Y : Type u)) (closedPoints X) := by
    intro y hy
    rw [hclosed_eq] at hy
    exact hy
  exact ⟨hYwlocal, ⟨hYwlocal, hX, htoXspectral, hmaps⟩, hclosed_eq⟩

end Formalization.Books.Proetale.Unit02
