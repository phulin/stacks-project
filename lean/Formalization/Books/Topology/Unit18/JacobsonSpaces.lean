import Formalization.Books.Topology.Unit10.KrullDimension
import Formalization.Books.Topology.Unit15.ConstructibleSets
import Mathlib.Topology.Constructible
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Spectral.Prespectral
import Mathlib.Topology.Sets.OpenCover

/-!
# Topology, Chapter 18: Jacobson spaces

The source's Jacobson-space definition and its locally closed criterion are
Mathlib's canonical `JacobsonSpace` and `jacobsonSpace_iff_locallyClosed`.
Closed points are represented by `closedPoints`, and the closed-point
subspace has the induced subtype topology.  The source's constructible
subsets use Mathlib's `IsConstructible`; its locally covered unions of
locally closed subsets use the source-facing
`IsLocallyUnionOfLocallyClosed` predicate below.  Chapter 15 records the
finite-locally-closed normal form for constructible sets.
-/

namespace Formalization.Books.Topology.Unit18

open Set Function _root_.Topology TopologicalSpace

universe u v

section JacobsonSpaces

variable {X : Type u} [TopologicalSpace X]

/-! ### Source-facing set predicates and traces -/

/-
Mathlib has no separate predicates for an arbitrary union of locally closed
subsets or for a set which is locally such a union.  These predicates are the
literal source interfaces needed for the inherited-subspace lemma and its
finite-union correspondence.
-/

/-- A subset which is a finite union of locally closed subsets. -/
def IsFiniteUnionLocallyClosed (E : Set X) : Prop :=
  ∃ S : Set (Set X), S.Finite ∧
    (∀ T ∈ S, IsLocallyClosed T) ∧ E = ⋃₀ S

/-- A subset which is a union of locally closed subsets. -/
def IsUnionOfLocallyClosed (E : Set X) : Prop :=
  ∃ S : Set (Set X), (∀ T ∈ S, IsLocallyClosed T) ∧ E = ⋃₀ S

/-! A source-facing open-cover formulation of being locally a union of
locally closed subsets. -/

def IsLocallyUnionOfLocallyClosed (E : Set X) : Prop :=
  ∃ S : Set (Set X),
    (∀ U ∈ S, IsOpen U ∧
      IsUnionOfLocallyClosed ((Subtype.val : U → X) ⁻¹' E)) ∧
      ⋃₀ S = (Set.univ : Set X)

/-- The intersection of a subset with the closed-point subspace. -/
def closedPointTrace (E : Set X) : Set (closedPoints X) :=
  (Subtype.val : closedPoints X → X) ⁻¹' E

/-- The induced map on closed subsets, written as a map of subtype lattices. -/
def closedSubsetsTrace (Z : {Z : Set X // IsClosed Z}) :
    {Z : Set (closedPoints X) // IsClosed Z} :=
  ⟨closedPointTrace (Z : Set X), Z.property.preimage continuous_subtype_val⟩

/-!
The definition and the equivalence with nonempty locally closed subsets are
already provided by Mathlib's `JacobsonSpace` and
`jacobsonSpace_iff_locallyClosed`; no parallel Jacobson predicate is
introduced here.
-/

/-! ### Closed points and the first lemmas -/

theorem closedSubsetsTrace_bijective [JacobsonSpace X] :
    Function.Bijective (closedSubsetsTrace (X := X)) := by
  constructor
  · intro Z W hZW
    apply Subtype.ext
    calc
      (Z : Set X) = closure ((Z : Set X) ∩ closedPoints X) := by
        rw [JacobsonSpace.closure_inter_closedPoints_eq_closure Z.property.isLocallyClosed]
        exact Z.property.closure_eq.symm
      _ = closure ((W : Set X) ∩ closedPoints X) := by
        congr 1
        have htrace :
            (Subtype.val : closedPoints X → X) ⁻¹' (Z : Set X) =
              (Subtype.val : closedPoints X → X) ⁻¹' (W : Set X) := by
          simpa [closedSubsetsTrace, closedPointTrace] using
            congrArg (fun Q : {Z : Set (closedPoints X) // IsClosed Z} =>
              (Q : Set (closedPoints X))) hZW
        ext x
        constructor
        · rintro ⟨hxZ, hxclosed⟩
          have hxW := (Set.ext_iff.mp htrace ⟨x, hxclosed⟩).mp hxZ
          exact ⟨hxW, hxclosed⟩
        · rintro ⟨hxW, hxclosed⟩
          have hxZ := (Set.ext_iff.mp htrace ⟨x, hxclosed⟩).mpr hxW
          exact ⟨hxZ, hxclosed⟩
      _ = (W : Set X) := by
        rw [JacobsonSpace.closure_inter_closedPoints_eq_closure W.property.isLocallyClosed]
        exact W.property.closure_eq
  · intro Z
    rcases IsInducing.subtypeVal.isClosed_iff.mp Z.property with ⟨W, hW, hWZ⟩
    refine ⟨⟨W, hW⟩, ?_⟩
    apply Subtype.ext
    simpa [closedSubsetsTrace, closedPointTrace] using hWZ

private theorem isIrreducible_closedPointTrace [JacobsonSpace X]
    {Z : Set X} (hZ : IsIrreducible Z) (hZclosed : IsClosed Z) :
    IsIrreducible (closedPointTrace Z) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxZ, hxclosed⟩ :=
      nonempty_inter_closedPoints hZ.nonempty hZclosed.isLocallyClosed
    exact ⟨⟨x, hxclosed⟩, hxZ⟩
  · intro U V hU hV hUmem hVmem
    obtain ⟨u, hu, huU⟩ := IsInducing.subtypeVal.isOpen_iff.mp hU
    obtain ⟨v, hv, hvV⟩ := IsInducing.subtypeVal.isOpen_iff.mp hV
    obtain ⟨a, haZ, haU⟩ := hUmem
    obtain ⟨b, hbZ, hbV⟩ := hVmem
    change (a : X) ∈ Z at haZ
    change (b : X) ∈ Z at hbZ
    have hZa : (Z ∩ u).Nonempty := by
      refine ⟨(a : X), haZ, ?_⟩
      have haU' : a ∈ (Subtype.val : closedPoints X → X) ⁻¹' u := huU.symm ▸ haU
      exact haU'
    have hZb : (Z ∩ v).Nonempty := by
      refine ⟨(b : X), hbZ, ?_⟩
      have hbV' : b ∈ (Subtype.val : closedPoints X → X) ⁻¹' v := hvV.symm ▸ hbV
      exact hbV'
    obtain ⟨c, hcZ, hcUV⟩ := hZ.2 u v hu hv hZa hZb
    have hCne : (Z ∩ (u ∩ v)).Nonempty := ⟨c, hcZ, hcUV.1, hcUV.2⟩
    obtain ⟨d, hdC, hdclosed⟩ :=
      nonempty_inter_closedPoints hCne
        (hZclosed.isLocallyClosed.inter (hu.inter hv).isLocallyClosed)
    refine ⟨⟨d, hdclosed⟩, ?_, ?_⟩
    · exact hdC.1
    · have hdU : (⟨d, hdclosed⟩ : closedPoints X) ∈ U := huU ▸ hdC.2.1
      have hdV : (⟨d, hdclosed⟩ : closedPoints X) ∈ V := hvV ▸ hdC.2.2
      exact ⟨hdU, hdV⟩

private theorem isIrreducible_of_closedPointTrace [JacobsonSpace X]
    {Z : Set X} (hZclosed : IsClosed Z)
    (htrace : IsIrreducible (closedPointTrace Z)) :
    IsIrreducible Z := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := htrace.nonempty
    change (x : X) ∈ Z at hx
    exact ⟨(x : X), hx⟩
  · intro U V hU hV hUmem hVmem
    have hUtrace : (closedPointTrace Z ∩
        (Subtype.val : closedPoints X → X) ⁻¹' U).Nonempty := by
      obtain ⟨x, hxZ, hxU⟩ := hUmem
      have hZU : (Z ∩ U).Nonempty := ⟨x, hxZ, hxU⟩
      obtain ⟨y, hyZ, hyclosed⟩ :=
        nonempty_inter_closedPoints hZU
          (hZclosed.isLocallyClosed.inter hU.isLocallyClosed)
      refine ⟨⟨y, hyclosed⟩, ?_, ?_⟩
      · exact hyZ.1
      · exact hyZ.2
    have hVtrace : (closedPointTrace Z ∩
        (Subtype.val : closedPoints X → X) ⁻¹' V).Nonempty := by
      obtain ⟨x, hxZ, hxV⟩ := hVmem
      have hZV : (Z ∩ V).Nonempty := ⟨x, hxZ, hxV⟩
      obtain ⟨y, hyZ, hyclosed⟩ :=
        nonempty_inter_closedPoints hZV
          (hZclosed.isLocallyClosed.inter hV.isLocallyClosed)
      refine ⟨⟨y, hyclosed⟩, ?_, ?_⟩
      · exact hyZ.1
      · exact hyZ.2
    obtain ⟨x, hxtrace, hxUV⟩ :=
      htrace.2 ((Subtype.val : closedPoints X → X) ⁻¹' U)
        ((Subtype.val : closedPoints X → X) ⁻¹' V)
        (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
        hUtrace hVtrace
    change (x : X) ∈ Z at hxtrace
    exact ⟨(x : X), hxtrace, hxUV.1, hxUV.2⟩

theorem topologicalKrullDim_closedPoints [JacobsonSpace X] :
    topologicalKrullDim (closedPoints X) = topologicalKrullDim X := by
  let f : IrreducibleCloseds X → IrreducibleCloseds (closedPoints X) := fun Z =>
    ⟨closedPointTrace (Z : Set X),
      isIrreducible_closedPointTrace Z.isIrreducible Z.isClosed,
      Z.isClosed.preimage continuous_subtype_val⟩
  have hf_inj : Function.Injective f := by
    intro Z W hZW
    have htrace : closedPointTrace (Z : Set X) = closedPointTrace (W : Set X) := by
      have h := congrArg IrreducibleCloseds.carrier hZW
      change closedPointTrace (Z : Set X) = closedPointTrace (W : Set X) at h
      exact h
    have hclosed :
        closedSubsetsTrace (⟨(Z : Set X), Z.isClosed⟩) =
          closedSubsetsTrace (⟨(W : Set X), W.isClosed⟩) := by
      apply Subtype.ext
      simpa [closedSubsetsTrace] using htrace
    have hclosed' := (closedSubsetsTrace_bijective (X := X)).1 hclosed
    apply IrreducibleCloseds.ext
    exact congrArg (fun Q : {Z : Set X // IsClosed Z} => (Q : Set X)) hclosed'
  have hf_surj : Function.Surjective f := by
    intro A
    obtain ⟨Z, hZA⟩ :=
      (closedSubsetsTrace_bijective (X := X)).2
        ⟨(A : Set (closedPoints X)), A.isClosed⟩
    have htrace : closedPointTrace (Z : Set X) = (A : Set (closedPoints X)) := by
      simpa [closedSubsetsTrace] using
        congrArg (fun Q : {Z : Set (closedPoints X) // IsClosed Z} =>
          (Q : Set (closedPoints X))) hZA
    have hZirr : IsIrreducible (Z : Set X) :=
      isIrreducible_of_closedPointTrace Z.property
        (htrace.symm ▸ A.isIrreducible)
    let Z' : IrreducibleCloseds X := ⟨Z, hZirr, Z.property⟩
    refine ⟨Z', ?_⟩
    apply IrreducibleCloseds.ext
    simp [f, Z', htrace]
  have hf_mono : Monotone f := by
    intro Z W hZW
    change closedPointTrace (Z : Set X) ⊆ closedPointTrace (W : Set X)
    exact preimage_mono hZW
  have hf_reflect : ∀ {Z W : IrreducibleCloseds X}, f Z ≤ f W → Z ≤ W := by
    intro Z W hZW
    change closedPointTrace (Z : Set X) ⊆ closedPointTrace (W : Set X) at hZW
    intro x hxZ
    have htrace : (Z : Set X) ∩ closedPoints X ⊆ (W : Set X) := by
      rintro y ⟨hyZ, hyclosed⟩
      have hyZ' : (⟨y, hyclosed⟩ : closedPoints X) ∈
          closedPointTrace (Z : Set X) := hyZ
      have hyW' := hZW hyZ'
      exact hyW'
    apply closure_minimal htrace W.isClosed
    rw [JacobsonSpace.closure_inter_closedPoints_eq_closure Z.isClosed.isLocallyClosed,
      Z.isClosed.closure_eq]
    exact hxZ
  let e₀ : IrreducibleCloseds X ≃ IrreducibleCloseds (closedPoints X) :=
    Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let e : IrreducibleCloseds X ≃o IrreducibleCloseds (closedPoints X) :=
    e₀.toOrderIso hf_mono (by
      intro A B hAB
      apply hf_reflect
      change e₀ (e₀.symm A) ≤ e₀ (e₀.symm B)
      rw [e₀.apply_symm_apply, e₀.apply_symm_apply]
      exact hAB)
  change Order.krullDim (IrreducibleCloseds (closedPoints X)) =
    Order.krullDim (IrreducibleCloseds X)
  exact (Order.krullDim_eq_of_orderIso e).symm

theorem jacobsonSpace_of_closedPoints_dense_in_point_closures
    (h : ∀ x : X,
      closure (closedPoints X ∩ closure ({x} : Set X)) = closure ({x} : Set X)) :
    JacobsonSpace X := by
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZloc
  obtain ⟨x, hxZ⟩ := hZ
  have hZloc' : ∀ x ∈ Z, ∃ U, x ∈ U ∧ IsOpen U ∧ U ∩ closure Z ⊆ Z :=
    (isLocallyClosed_tfae Z).out 0 3 |>.mp hZloc
  obtain ⟨U, hxU, hU, hUZ⟩ := hZloc' x hxZ
  have hxclosure : x ∈ closure (closedPoints X ∩ closure ({x} : Set X)) := by
    rw [h x]
    exact subset_closure (mem_singleton x)
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff.mp hxclosure U hU hxU
  refine ⟨y, ?_⟩
  exact ⟨hUZ ⟨hyU, closure_mono (singleton_subset_iff.mpr hxZ) hy.2⟩, hy.1⟩

theorem exists_nonclosed_point_of_not_jacobson
    [T0Space X] [PrespectralSpace X] (hX : ¬ JacobsonSpace X) :
    ∃ x : X, ¬ IsClosed ({x} : Set X) ∧ IsLocallyClosed ({x} : Set X) := by
  by_contra h
  apply hX
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZloc
  by_contra hZclosed
  obtain ⟨x, hxZ⟩ := hZ
  have hZloc' : ∀ x ∈ Z, ∃ V, x ∈ V ∧ IsOpen V ∧ V ∩ closure Z ⊆ Z :=
    (isLocallyClosed_tfae Z).out 0 3 |>.mp hZloc
  obtain ⟨V, hxV, hV, hVZ⟩ := hZloc' x hxZ
  obtain ⟨U, hUmem, hxU, hUV⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxV hV
  rcases hUmem with ⟨hU, hUcompact⟩
  let K : Set X := U ∩ closure Z
  have hKcompact : IsCompact K := by
    simpa [K] using hUcompact.inter_right isClosed_closure
  have hKne : K.Nonempty := by
    refine ⟨x, ?_⟩
    exact ⟨hxU, subset_closure hxZ⟩
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let _ : Nonempty K := hKne.to_subtype
  obtain ⟨y, hyK, hyclosedK⟩ :=
    IsClosed.exists_closed_singleton (S := (Set.univ : Set K)) isClosed_univ
      Set.univ_nonempty
  have hyK' : (y : X) ∈ U ∩ closure Z := by
    exact y.property
  have hyZ : (y : X) ∈ Z := hVZ ⟨hUV hyK'.1, hyK'.2⟩
  have hKloc : IsLocallyClosed K := by
    exact ⟨U, closure Z, hU, isClosed_closure, by simp [K]⟩
  have hyloc : IsLocallyClosed ({(y : X)} : Set X) := by
    simpa only [image_singleton] using
      hyclosedK.isLocallyClosed.image IsInducing.subtypeVal (by simpa using hKloc)
  have hynotclosed : ¬ IsClosed ({(y : X)} : Set X) := by
    intro hyclosed
    apply hZclosed
    exact ⟨y, hyZ, mem_closedPoints_iff.mpr hyclosed⟩
  exact h ⟨(y : X), hynotclosed, hyloc⟩

/-! ### Open covers -/

/-
`TopologicalSpace.IsOpenCover.jacobsonSpace_iff` is the canonical
open-cover form of the source's local Jacobson lemma.
-/

theorem jacobsonSpace_iff_isOpenCover {ι : Type v} (U : ι → Opens X)
    (hU : IsOpenCover U) :
    JacobsonSpace X ↔ ∀ i, JacobsonSpace (U i) :=
  TopologicalSpace.IsOpenCover.jacobsonSpace_iff hU

theorem closedPoints_eq_iUnion_image_closedPoints_of_isOpenCover
    {ι : Type v} (U : ι → Opens X) (hU : IsOpenCover U)
    [JacobsonSpace X] :
    closedPoints X =
      ⋃ i, (Subtype.val : U i → X) '' closedPoints (U i) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hxi⟩ := hU.exists_mem x
    have hxi' : (⟨x, hxi⟩ : U i) ∈ closedPoints (U i) := by
      have hpre :
          (Subtype.val : U i → X) ⁻¹' closedPoints X = closedPoints (U i) :=
        (U i).2.isOpenEmbedding_subtypeVal.preimage_closedPoints
      exact hpre ▸ hx
    exact mem_iUnion.2 ⟨i, ⟨⟨x, hxi⟩, hxi', rfl⟩⟩
  · intro x hx
    rcases mem_iUnion.mp hx with ⟨i, ⟨y, hy, rfl⟩⟩
    have hpre :
        (Subtype.val : U i → X) ⁻¹' closedPoints X = closedPoints (U i) :=
      (U i).2.isOpenEmbedding_subtypeVal.preimage_closedPoints
    have hy' : y ∈ (Subtype.val : U i → X) ⁻¹' closedPoints X := hpre.symm ▸ hy
    exact hy'

/-! ### Jacobson subspaces -/

/-!
The last case below uses the source-facing open-cover formulation of being
locally a union of locally closed subsets.
-/

private theorem jacobsonSpace_of_isUnionOfLocallyClosed_aux [JacobsonSpace X]
    {T : Set X} {S : Set (Set X)}
    (hS : ∀ P ∈ S, IsLocallyClosed P) (hT : T = ⋃₀ S) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  have hfind : ∀ {A : Set T}, A.Nonempty → IsLocallyClosed A →
      ∃ y : T, y ∈ A ∧ IsClosed ({(y : X)} : Set X) := by
    intro A hA hAloc
    obtain ⟨x, hx⟩ := hA
    have hx' : (x : X) ∈ ⋃₀ S := by
      simpa [hT] using x.property
    obtain ⟨P, hPS, hxP⟩ := mem_sUnion.mp hx'
    have hPT : P ⊆ T := by
      intro z hz
      rw [hT]
      exact mem_sUnion_of_mem hz hPS
    let f : P → T := Set.inclusion hPT
    have hf : Continuous f := continuous_inclusion hPT
    let B : Set P := f ⁻¹' A
    have hB : IsLocallyClosed B := hAloc.preimage hf
    have hBne : B.Nonempty := by
      refine ⟨⟨(x : X), hxP⟩, ?_⟩
      change f ⟨(x : X), hxP⟩ ∈ A
      simpa [f] using hx
    have hBimage : IsLocallyClosed ((Subtype.val : P → X) '' B) :=
      hB.image IsInducing.subtypeVal (by simpa using hS P hPS)
    have hBimage_ne : ((Subtype.val : P → X) '' B).Nonempty :=
      hBne.image (Subtype.val : P → X)
    obtain ⟨y, ⟨hyB, hyclosed⟩⟩ :=
      nonempty_inter_closedPoints hBimage_ne hBimage
    rcases hyB with ⟨p, hpB, rfl⟩
    refine ⟨f p, ?_, ?_⟩
    · change f p ∈ A at hpB
      exact hpB
    · exact mem_closedPoints_iff.mp hyclosed
  refine ⟨?_, ?_⟩
  · rw [jacobsonSpace_iff_locallyClosed]
    intro A hA hAloc
    obtain ⟨y, hyA, hyclosed⟩ := hfind hA hAloc
    refine ⟨y, hyA, ?_⟩
    exact preimage_closedPoints_subset Subtype.val_injective continuous_subtype_val
      (mem_closedPoints_iff.mpr hyclosed)
  · intro x hx
    obtain ⟨y, hyA, hyclosed⟩ :=
      hfind (A := ({x} : Set T)) (singleton_nonempty x)
        (mem_closedPoints_iff.mp hx).isLocallyClosed
    have hxy : y = x := by simpa using hyA
    simpa [hxy] using hyclosed

theorem jacobsonSpace_of_isOpen [JacobsonSpace X] {T : Set X}
    (hT : IsOpen T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  exact jacobsonSpace_of_isUnionOfLocallyClosed_aux
    (S := {T}) (by
      intro P hP
      have hPT : P = T := by simpa using hP
      subst P
      exact hT.isLocallyClosed) (by simp)

theorem jacobsonSpace_of_isClosed [JacobsonSpace X] {T : Set X}
    (hT : IsClosed T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  exact jacobsonSpace_of_isUnionOfLocallyClosed_aux
    (S := {T}) (by
      intro P hP
      have hPT : P = T := by simpa using hP
      subst P
      exact hT.isLocallyClosed) (by simp)

theorem jacobsonSpace_of_isLocallyClosed [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyClosed T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  exact jacobsonSpace_of_isUnionOfLocallyClosed_aux
    (S := {T}) (by
      intro P hP
      have hPT : P = T := by simpa using hP
      subst P
      exact hT) (by simp)

theorem jacobsonSpace_of_isUnionOfLocallyClosed [JacobsonSpace X] {T : Set X}
    (hT : IsUnionOfLocallyClosed T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  rcases hT with ⟨S, hS, hEq⟩
  exact jacobsonSpace_of_isUnionOfLocallyClosed_aux hS hEq

theorem jacobsonSpace_of_isConstructible [JacobsonSpace X] {T : Set X}
    (hT : IsConstructible T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  obtain ⟨S, _, hS, hEq⟩ :=
    Formalization.Books.Topology.Unit15.isConstructible_isFiniteUnion_isLocallyClosed hT
  exact jacobsonSpace_of_isUnionOfLocallyClosed_aux hS hEq

theorem jacobsonSpace_of_isLocallyUnionOfLocallyClosed [JacobsonSpace X]
    {T : Set X} (hT : IsLocallyUnionOfLocallyClosed T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  rcases hT with ⟨S, hS, hcover⟩
  have hfind : ∀ {A : Set T}, A.Nonempty → IsLocallyClosed A →
      ∃ y : T, y ∈ A ∧ IsClosed ({(y : X)} : Set X) := by
    intro A hA hAloc
    obtain ⟨x, hx⟩ := hA
    have hx' : (x : X) ∈ ⋃₀ S := by
      rw [hcover]
      exact mem_univ _
    obtain ⟨U, hUS, hxU⟩ := mem_sUnion.mp hx'
    have hUopen := (hS U hUS).1
    have hUunion := (hS U hUS).2
    have hUresult := jacobsonSpace_of_isOpen (X := X) hUopen
    let _ : JacobsonSpace U := hUresult.1
    have hTUresult :=
      jacobsonSpace_of_isUnionOfLocallyClosed
        (X := U) (T := (Subtype.val : U → X) ⁻¹' T) hUunion
    let _ : JacobsonSpace ((Subtype.val : U → X) ⁻¹' T) := hTUresult.1
    let g : (Subtype.val : U → X) ⁻¹' T → T := fun z =>
      ⟨(z : U), z.property⟩
    have hg : Continuous g := by
      dsimp [g]
      exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun z => z.property)
    let B : Set ((Subtype.val : U → X) ⁻¹' T) := g ⁻¹' A
    have hB : IsLocallyClosed B := hAloc.preimage hg
    have hBne : B.Nonempty := by
      refine ⟨⟨⟨x, hxU⟩, x.property⟩, ?_⟩
      change g ⟨⟨x, hxU⟩, x.property⟩ ∈ A
      simpa [g] using hx
    obtain ⟨y, hyB, hyclosedU⟩ := nonempty_inter_closedPoints hBne hB
    refine ⟨g y, ?_, ?_⟩
    · change g y ∈ A at hyB
      exact hyB
    · exact hUresult.2 (y : U) (mem_closedPoints_iff.mpr (hTUresult.2 y hyclosedU))
  refine ⟨?_, ?_⟩
  · rw [jacobsonSpace_iff_locallyClosed]
    intro A hA hAloc
    obtain ⟨y, hyA, hyclosed⟩ := hfind hA hAloc
    refine ⟨y, hyA, ?_⟩
    exact preimage_closedPoints_subset Subtype.val_injective continuous_subtype_val
      (mem_closedPoints_iff.mpr hyclosed)
  · intro x hx
    obtain ⟨y, hyA, hyclosed⟩ :=
      hfind (A := ({x} : Set T)) (singleton_nonempty x)
        (mem_closedPoints_iff.mp hx).isLocallyClosed
    have hxy : y = x := by simpa using hyA
    simpa [hxy] using hyclosed

/-! ### Finite Jacobson spaces -/

theorem discreteTopology_of_finite_jacobson [Finite X] [JacobsonSpace X] :
    DiscreteTopology X := by
  infer_instance

theorem discreteTopology_of_finite_closedPoints [JacobsonSpace X]
    (hX₀ : (closedPoints X).Finite) :
    DiscreteTopology X :=
  JacobsonSpace.discreteTopology hX₀

private theorem exists_locallyClosed_subset_compl_sUnion
    {R : Set (Set X)} (hR : R.Finite)
    (hRloc : ∀ Q ∈ R, IsLocallyClosed Q) {x : X}
    (hx : x ∉ ⋃₀ R) :
    ∃ N : Set X, IsLocallyClosed N ∧ x ∈ N ∧ N ⊆ (⋃₀ R)ᶜ := by
  induction R, hR using Set.Finite.induction_on with
  | empty =>
      refine ⟨Set.univ, isOpen_univ.isLocallyClosed, mem_univ x, ?_⟩
      simp
  | @insert Q R hQR hR ih =>
      have hxQ : x ∉ Q := by
        intro hxQ
        apply hx
        rw [sUnion_insert]
        exact mem_union_left _ hxQ
      have hxR : x ∉ ⋃₀ R := by
        intro hxR
        apply hx
        rw [sUnion_insert]
        exact mem_union_right _ hxR
      obtain ⟨N, hNloc, hxN, hNsub⟩ :=
        ih (fun Q hQ => hRloc Q (by simp [hQ])) hxR
      obtain ⟨V, Z, hV, hZ, hQeq⟩ := hRloc Q (by simp)
      by_cases hxV : x ∈ V
      · have hxZ : x ∉ Z := by
          intro hxZ
          apply hxQ
          rw [hQeq]
          exact ⟨hxV, hxZ⟩
        refine ⟨Zᶜ ∩ N, hZ.isOpen_compl.isLocallyClosed.inter hNloc,
          ⟨by exact hxZ, hxN⟩, ?_⟩
        intro y hy
        rw [sUnion_insert]
        intro hyunion
        rcases hyunion with hyQ | hyR
        · exact hy.1 (hQeq ▸ hyQ).2
        · exact (hNsub hy.2) hyR
      · refine ⟨Vᶜ ∩ N, hV.isClosed_compl.isLocallyClosed.inter hNloc,
          ⟨by exact hxV, hxN⟩, ?_⟩
        intro y hy
        rw [sUnion_insert]
        intro hyunion
        rcases hyunion with hyQ | hyR
        · exact hy.1 (hQeq ▸ hyQ).1
        · exact (hNsub hy.2) hyR

private theorem closedPointTrace_sUnion (S : Set (Set X)) :
    closedPointTrace (⋃₀ S) = ⋃₀ (closedPointTrace '' S) := by
  ext x
  simp [closedPointTrace]

private theorem isFiniteUnionLocallyClosed_closedPointTrace
    {E : Set X} (hE : IsFiniteUnionLocallyClosed E) :
    IsFiniteUnionLocallyClosed (closedPointTrace E) := by
  rcases hE with ⟨S, hSfinite, hSlocal, hSE⟩
  refine ⟨closedPointTrace '' S, hSfinite.image _, ?_, ?_⟩
  · rintro _ ⟨T, hTS, rfl⟩
    exact (hSlocal T hTS).preimage continuous_subtype_val
  · rw [hSE, closedPointTrace_sUnion]

private theorem exists_finiteUnionLocallyClosed_of_closedPointTrace
    {E : Set (closedPoints X)} (hE : IsFiniteUnionLocallyClosed E) :
    ∃ F : Set X, IsFiniteUnionLocallyClosed F ∧ closedPointTrace F = E := by
  classical
  rcases hE with ⟨S, hSfinite, hSlocal, hSE⟩
  choose T hTlocal hTtrace using fun U hUS =>
    (IsInducing.subtypeVal.isLocallyClosed_iff.mp (hSlocal U hUS))
  let T' : S → Set X := fun U => T U U.property
  let _ : Finite S := hSfinite.to_subtype
  refine ⟨⋃₀ (T' '' (Set.univ : Set S)), ?_, ?_⟩
  · exact ⟨T' '' (Set.univ : Set S),
      (Set.finite_univ : (Set.univ : Set S).Finite).image T', by
        rintro _ ⟨U, -, rfl⟩
        exact hTlocal U U.property, rfl⟩
  · rw [closedPointTrace_sUnion, hSE]
    ext x
    constructor
    · intro hx
      obtain ⟨F, ⟨G, ⟨U, -, rfl⟩, rfl⟩, hx⟩ := mem_sUnion.mp hx
      exact mem_sUnion_of_mem (hTtrace U U.property ▸ hx) U.property
    · intro hx
      obtain ⟨U, hUS, hx⟩ := mem_sUnion.mp hx
      refine mem_sUnion.mpr ⟨closedPointTrace (T' ⟨U, hUS⟩),
        ⟨T' ⟨U, hUS⟩, ⟨⟨U, hUS⟩, Set.mem_univ _, rfl⟩, rfl⟩,
        ?_⟩
      have htrace' : closedPointTrace (T' ⟨U, hUS⟩) = U := by
        change (Subtype.val : closedPoints X → X) ⁻¹' T U hUS = U
        exact hTtrace U hUS
      exact htrace'.symm ▸ hx

private theorem finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
    [JacobsonSpace X] {E F : Set X}
    (hE : IsFiniteUnionLocallyClosed E)
    (hF : IsFiniteUnionLocallyClosed F)
    (htrace : closedPointTrace E ⊆ closedPointTrace F) : E ⊆ F := by
  rcases hE with ⟨S, hSfinite, hSlocal, hSE⟩
  rcases hF with ⟨R, hRfinite, hRlocal, hRF⟩
  intro x hxE
  by_contra hxF
  have hxS : x ∈ ⋃₀ S := hSE ▸ hxE
  obtain ⟨P, hPS, hxP⟩ := mem_sUnion.mp hxS
  have hxR : x ∉ ⋃₀ R := by
    intro hxR
    apply hxF
    exact hRF.symm ▸ hxR
  obtain ⟨N, hNlocal, hxN, hNsub⟩ :=
    exists_locallyClosed_subset_compl_sUnion hRfinite hRlocal hxR
  have hPN : (P ∩ N).Nonempty := ⟨x, hxP, hxN⟩
  obtain ⟨y, hyPN, hyclosed⟩ :=
    nonempty_inter_closedPoints hPN (hSlocal P hPS |>.inter hNlocal)
  have hyE : (⟨y, hyclosed⟩ : closedPoints X) ∈ closedPointTrace E := by
    change (y : X) ∈ E
    rw [hSE]
    exact mem_sUnion_of_mem hyPN.1 hPS
  have hyFtrace := htrace hyE
  have hyF : (y : X) ∈ F := hyFtrace
  have hyR : (y : X) ∈ (⋃₀ R)ᶜ := hNsub hyPN.2
  exact hyR (hRF ▸ hyF)

/-! ### Correspondence for finite unions of locally closed subsets -/

theorem exists_finiteUnionLocallyClosed_closedPoint_correspondence
    [JacobsonSpace X] :
    ∃ e :
        {E : Set X // IsFiniteUnionLocallyClosed E} ≃
          {E : Set (closedPoints X) // IsFiniteUnionLocallyClosed E},
      (∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
        (e E : Set (closedPoints X)) = closedPointTrace (E : Set X)) ∧
      (∀ E F : {E : Set X // IsFiniteUnionLocallyClosed E},
        ((E : Set X) ⊆ (F : Set X)) ↔
          ((e E : Set (closedPoints X)) ⊆ (e F : Set (closedPoints X)))) ∧
      (∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
        IsLocallyClosed (E : Set X) ↔
          IsLocallyClosed (e E : Set (closedPoints X))) ∧
      (∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
        IsOpen (E : Set X) ↔ IsOpen (e E : Set (closedPoints X))) ∧
      (∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
        IsClosed (E : Set X) ↔ IsClosed (e E : Set (closedPoints X))) := by
  classical
  have finite_local : ∀ {E : Set X}, IsLocallyClosed E →
      IsFiniteUnionLocallyClosed E := by
    intro E hE
    refine ⟨{E}, Set.finite_singleton _, ?_, by simp⟩
    intro F hF
    have hFE : F = E := by simpa using hF
    subst F
    exact hE
  let g :
      {E : Set X // IsFiniteUnionLocallyClosed E} →
        {E : Set (closedPoints X) // IsFiniteUnionLocallyClosed E} :=
    fun E => ⟨closedPointTrace (E : Set X),
      isFiniteUnionLocallyClosed_closedPointTrace E.property⟩
  have hg_inj : Function.Injective g := by
    intro E F hEF
    have htrace : closedPointTrace (E : Set X) = closedPointTrace (F : Set X) := by
      have h := congrArg
        (fun A : {E : Set (closedPoints X) // IsFiniteUnionLocallyClosed E} =>
          (A : Set (closedPoints X))) hEF
      change closedPointTrace (E : Set X) = closedPointTrace (F : Set X) at h
      exact h
    apply Subtype.ext
    apply Set.Subset.antisymm
    · exact finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
        E.property F.property htrace.le
    · exact finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
        F.property E.property htrace.ge
  have hg_surj : Function.Surjective g := by
    intro E
    obtain ⟨F, hF, htrace⟩ :=
      exists_finiteUnionLocallyClosed_of_closedPointTrace E.property
    refine ⟨⟨F, hF⟩, ?_⟩
    apply Subtype.ext
    simpa [g] using htrace
  let e :
      {E : Set X // IsFiniteUnionLocallyClosed E} ≃
        {E : Set (closedPoints X) // IsFiniteUnionLocallyClosed E} :=
    Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  have he_trace : ∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
      (e E : Set (closedPoints X)) = closedPointTrace (E : Set X) := by
    intro E
    change (g E : Set (closedPoints X)) = closedPointTrace (E : Set X)
    rfl
  have he_subset : ∀ E F : {E : Set X // IsFiniteUnionLocallyClosed E},
      ((E : Set X) ⊆ (F : Set X)) ↔
        ((e E : Set (closedPoints X)) ⊆ (e F : Set (closedPoints X))) := by
    intro E F
    constructor
    · intro hEF
      rw [he_trace E, he_trace F]
      exact preimage_mono hEF
    · intro hEF
      apply finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
        E.property F.property
      simpa [he_trace E, he_trace F] using hEF
  have he_local : ∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
      IsLocallyClosed (E : Set X) ↔
        IsLocallyClosed (e E : Set (closedPoints X)) := by
    intro E
    constructor
    · intro hE
      rw [he_trace E]
      exact hE.preimage continuous_subtype_val
    · intro hEtrace
      obtain ⟨L, hL, hLE⟩ :=
        IsInducing.subtypeVal.isLocallyClosed_iff.mp hEtrace
      have htraceL : closedPointTrace L = closedPointTrace (E : Set X) := by
        calc
          closedPointTrace L = (e E : Set (closedPoints X)) := by
            simpa [closedPointTrace] using hLE
          _ = closedPointTrace (E : Set X) := he_trace E
      have hLfinite := finite_local hL
      have hEL : (E : Set X) ⊆ L :=
        finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
          E.property hLfinite htraceL.symm.le
      have hLE' : L ⊆ (E : Set X) :=
        finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
          hLfinite E.property htraceL.le
      rw [hEL.antisymm hLE']
      exact hL
  have he_open : ∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
      IsOpen (E : Set X) ↔ IsOpen (e E : Set (closedPoints X)) := by
    intro E
    constructor
    · intro hE
      rw [he_trace E]
      exact hE.preimage continuous_subtype_val
    · intro hEtrace
      obtain ⟨U, hU, hUE⟩ := IsInducing.subtypeVal.isOpen_iff.mp hEtrace
      have hUfinite := finite_local hU.isLocallyClosed
      have htraceU : closedPointTrace (U : Set X) =
          closedPointTrace (E : Set X) := by
        rw [closedPointTrace]
        exact hUE.trans (he_trace E).symm
      have hEU : (E : Set X) ⊆ U :=
        finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
          E.property hUfinite htraceU.symm.le
      have hUE' : U ⊆ (E : Set X) :=
        finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
          hUfinite E.property htraceU.le
      rw [hEU.antisymm hUE']
      exact hU
  have he_closed : ∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
      IsClosed (E : Set X) ↔ IsClosed (e E : Set (closedPoints X)) := by
    intro E
    constructor
    · intro hE
      rw [he_trace E]
      exact hE.preimage continuous_subtype_val
    · intro hEtrace
      obtain ⟨F, hFE⟩ :=
        (closedSubsetsTrace_bijective (X := X)).2
          (⟨(e E : Set (closedPoints X)), hEtrace⟩ :
            {Z : Set (closedPoints X) // IsClosed Z})
      have hF : IsClosed (F : Set X) := F.property
      have htraceF : closedPointTrace (F : Set X) =
          closedPointTrace (E : Set X) := by
        calc
          closedPointTrace (F : Set X) = (e E : Set (closedPoints X)) := by
            simpa [closedSubsetsTrace] using congrArg
              (fun A : {Z : Set (closedPoints X) // IsClosed Z} =>
                (A : Set (closedPoints X))) hFE
          _ = closedPointTrace (E : Set X) := he_trace E
      have hFfinite := finite_local hF.isLocallyClosed
      have hEF : (E : Set X) ⊆ F :=
        finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
          E.property hFfinite htraceF.symm.le
      have hFE' : (F : Set X) ⊆ (E : Set X) :=
        finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
          hFfinite E.property htraceF.le
      rw [hEF.antisymm hFE']
      exact hF
  refine ⟨e, he_trace, he_subset, he_local, he_open, he_closed⟩

private theorem isCompact_open_iff_closedPointTrace [JacobsonSpace X]
    {U : Set X} (hU : IsOpen U) :
    IsCompact U ↔ IsCompact (closedPointTrace U) := by
  constructor
  · intro hUcompact
    rw [isCompact_iff_finite_subcover]
    intro ι V hVopen hVcover
    choose W hWopen hWV using fun i =>
      IsInducing.subtypeVal.isOpen_iff.mp (hVopen i)
    have hUsub : U ⊆ ⋃ i, W i := by
      intro x hx
      by_contra hxnot
      have hnon : (U ∩ (⋃ i, W i)ᶜ).Nonempty := ⟨x, hx, hxnot⟩
      obtain ⟨y, hy, hyclosed⟩ :=
        nonempty_inter_closedPoints hnon
          (hU.isLocallyClosed.inter (isOpen_iUnion hWopen).isClosed_compl.isLocallyClosed)
      have hytrace : (⟨y, hyclosed⟩ : closedPoints X) ∈ closedPointTrace U := hy.1
      obtain ⟨i, hyVi⟩ := mem_iUnion.mp (hVcover hytrace)
      have hyWi : (⟨y, hyclosed⟩ : closedPoints X) ∈
          (Subtype.val : closedPoints X → X) ⁻¹' W i := hWV i |>.symm ▸ hyVi
      exact hy.2 (mem_iUnion_of_mem i hyWi)
    obtain ⟨t, ht⟩ := hUcompact.elim_finite_subcover W hWopen hUsub
    refine ⟨t, ?_⟩
    intro y hy
    have hyU : (y : X) ∈ U := hy
    obtain ⟨i, hi, hyWi⟩ := mem_iUnion₂.mp (ht hyU)
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    exact hWV i ▸ hyWi
  · intro htracecompact
    rw [isCompact_iff_finite_subcover]
    intro ι V hVopen hVcover
    have htracecover : closedPointTrace U ⊆ ⋃ i, closedPointTrace (V i) := by
      intro y hy
      obtain ⟨i, hyVi⟩ := mem_iUnion.mp (hVcover hy)
      exact mem_iUnion_of_mem i hyVi
    obtain ⟨t, ht⟩ := htracecompact.elim_finite_subcover
      (fun i => closedPointTrace (V i))
      (fun i => (hVopen i).preimage continuous_subtype_val) htracecover
    refine ⟨t, ?_⟩
    intro x hx
    by_contra hxnot
    have hnon : (U ∩ (⋃ i ∈ t, V i)ᶜ).Nonempty := by
      refine ⟨x, hx, hxnot⟩
    obtain ⟨y, hy, hyclosed⟩ :=
      nonempty_inter_closedPoints hnon
        (hU.isLocallyClosed.inter
          (isOpen_biUnion fun i _ => hVopen i).isClosed_compl.isLocallyClosed)
    have hytrace : (⟨y, hyclosed⟩ : closedPoints X) ∈ closedPointTrace U := hy.1
    obtain ⟨i, hi, hyVi⟩ := mem_iUnion₂.mp (ht hytrace)
    exact hy.2 (mem_iUnion₂.mpr ⟨i, hi, hyVi⟩)

private theorem isRetrocompact_open_iff_closedPointTrace [JacobsonSpace X]
    {U : Set X} (hU : IsOpen U) :
    IsRetrocompact U ↔ IsRetrocompact (closedPointTrace U) := by
  constructor
  · intro hUretro V hVcompact hVopen
    obtain ⟨W, hWopen, hWV⟩ := IsInducing.subtypeVal.isOpen_iff.mp hVopen
    have hWtrace : closedPointTrace W = V := by
      simpa [closedPointTrace] using hWV
    have hWcompact : IsCompact W :=
      (isCompact_open_iff_closedPointTrace hWopen).mpr
        (hWtrace.symm ▸ hVcompact)
    have hUWcompact := hUretro hWcompact hWopen
    have htracecompact :=
      (isCompact_open_iff_closedPointTrace (hU.inter hWopen)).mp hUWcompact
    simpa [closedPointTrace, preimage_inter, hWV] using htracecompact
  · intro htrace V hVcompact hVopen
    have hVtracecompact :=
      (isCompact_open_iff_closedPointTrace hVopen).mp hVcompact
    have hVtraceopen : IsOpen (closedPointTrace V) :=
      hVopen.preimage continuous_subtype_val
    have hintercompact := htrace hVtracecompact hVtraceopen
    simpa [closedPointTrace, preimage_inter] using
      (isCompact_open_iff_closedPointTrace (hU.inter hVopen)).mpr hintercompact

private theorem isConstructible_closedPointTrace [JacobsonSpace X]
    {E : Set X} (hE : IsConstructible E) :
    IsConstructible (closedPointTrace E) := by
  exact hE.preimage continuous_subtype_val (fun U hUopen hUretro =>
    (isRetrocompact_open_iff_closedPointTrace hUopen).mp hUretro)

private theorem exists_constructible_of_closedPointTrace [JacobsonSpace X]
    {E : Set (closedPoints X)} (hE : IsConstructible E) :
    ∃ F : Set X, IsConstructible F ∧ closedPointTrace F = E := by
  classical
  induction hE using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUretro =>
      obtain ⟨V, hVopen, hVU⟩ := IsInducing.subtypeVal.isOpen_iff.mp hUopen
      have hVretro : IsRetrocompact V := by
        apply (isRetrocompact_open_iff_closedPointTrace hVopen).mpr
        change IsRetrocompact ((Subtype.val : closedPoints X → X) ⁻¹' V)
        exact hVU.symm ▸ hUretro
      refine ⟨V, hVretro.isConstructible hVopen, ?_⟩
      simpa [closedPointTrace] using hVU
  | union s hs t ht hs' ht' =>
      obtain ⟨S, hS, hStrace⟩ := hs'
      obtain ⟨T, hT, hTtrace⟩ := ht'
      refine ⟨S ∪ T, hS.union hT, ?_⟩
      rw [← hStrace, ← hTtrace]
      ext x
      simp [closedPointTrace]
  | compl s hs hs' =>
      obtain ⟨S, hS, hStrace⟩ := hs'
      refine ⟨Sᶜ, hS.compl, ?_⟩
      rw [← hStrace]
      ext x
      simp [closedPointTrace]

/-! ### Correspondence for constructible subsets -/

theorem exists_constructible_closedPoint_correspondence [JacobsonSpace X] :
    ∃ e :
        {E : Set X // IsConstructible E} ≃
          {E : Set (closedPoints X) // IsConstructible E},
      (∀ E : {E : Set X // IsConstructible E},
        (e E : Set (closedPoints X)) = closedPointTrace (E : Set X)) ∧
      (∀ E F : {E : Set X // IsConstructible E},
        ((E : Set X) ⊆ (F : Set X)) ↔
          ((e E : Set (closedPoints X)) ⊆ (e F : Set (closedPoints X)))) ∧
      (∀ E : {E : Set X // IsConstructible E},
        (IsOpen (E : Set X) ∧ IsRetrocompact (E : Set X)) ↔
          (IsOpen (e E : Set (closedPoints X)) ∧
            IsRetrocompact (e E : Set (closedPoints X)))) ∧
      (∀ E : {E : Set X // IsConstructible E},
        IsOpen (E : Set X) ∧ IsRetrocompact (E : Set X) →
          e ⟨(E : Set X)ᶜ, E.property.compl⟩ =
            ⟨(e E : Set (closedPoints X))ᶜ, (e E).property.compl⟩) := by
  classical
  have finite_normal_form : ∀ {E : Set X}, IsConstructible E →
      IsFiniteUnionLocallyClosed E := by
    intro E hE
    obtain ⟨S, hSfinite, hSlocal, hSE⟩ :=
      Formalization.Books.Topology.Unit15.isConstructible_isFiniteUnion_isLocallyClosed hE
    exact ⟨S, hSfinite, hSlocal, hSE⟩
  have finite_local : ∀ {E : Set X}, IsLocallyClosed E →
      IsFiniteUnionLocallyClosed E := by
    intro E hE
    refine ⟨{E}, Set.finite_singleton _, ?_, by simp⟩
    intro F hF
    have hFE : F = E := by simpa using hF
    subst F
    exact hE
  let g :
      {E : Set X // IsConstructible E} →
        {E : Set (closedPoints X) // IsConstructible E} :=
    fun E => ⟨closedPointTrace (E : Set X),
      isConstructible_closedPointTrace E.property⟩
  have hg_inj : Function.Injective g := by
    intro E F hEF
    have htrace : closedPointTrace (E : Set X) = closedPointTrace (F : Set X) := by
      have h := congrArg
        (fun A : {E : Set (closedPoints X) // IsConstructible E} =>
          (A : Set (closedPoints X))) hEF
      change closedPointTrace (E : Set X) = closedPointTrace (F : Set X) at h
      exact h
    apply Subtype.ext
    exact Set.Subset.antisymm
      (finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
        (finite_normal_form E.property) (finite_normal_form F.property) htrace.le)
      (finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
        (finite_normal_form F.property) (finite_normal_form E.property) htrace.ge)
  have hg_surj : Function.Surjective g := by
    intro E
    obtain ⟨F, hF, htrace⟩ := exists_constructible_of_closedPointTrace E.property
    refine ⟨⟨F, hF⟩, ?_⟩
    apply Subtype.ext
    simpa [g] using htrace
  let e :
      {E : Set X // IsConstructible E} ≃
        {E : Set (closedPoints X) // IsConstructible E} :=
    Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  have he_trace : ∀ E : {E : Set X // IsConstructible E},
      (e E : Set (closedPoints X)) = closedPointTrace (E : Set X) := by
    intro E
    change (g E : Set (closedPoints X)) = closedPointTrace (E : Set X)
    rfl
  have he_subset : ∀ E F : {E : Set X // IsConstructible E},
      ((E : Set X) ⊆ (F : Set X)) ↔
        ((e E : Set (closedPoints X)) ⊆ (e F : Set (closedPoints X))) := by
    intro E F
    constructor
    · intro hEF
      rw [he_trace E, he_trace F]
      exact preimage_mono hEF
    · intro hEF
      exact finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
        (finite_normal_form E.property) (finite_normal_form F.property)
        (by simpa [he_trace E, he_trace F] using hEF)
  have he_open_retrocompact : ∀ E : {E : Set X // IsConstructible E},
      (IsOpen (E : Set X) ∧ IsRetrocompact (E : Set X)) ↔
        (IsOpen (e E : Set (closedPoints X)) ∧
          IsRetrocompact (e E : Set (closedPoints X))) := by
    intro E
    constructor
    · rintro ⟨hEopen, hEretro⟩
      refine ⟨?_, ?_⟩
      · rw [he_trace E]
        exact hEopen.preimage continuous_subtype_val
      · rw [he_trace E]
        exact (isRetrocompact_open_iff_closedPointTrace hEopen).mp hEretro
    · rintro ⟨hEopen, hEretro⟩
      obtain ⟨U, hUopen, hUE⟩ := IsInducing.subtypeVal.isOpen_iff.mp hEopen
      have hUretro : IsRetrocompact U := by
        apply (isRetrocompact_open_iff_closedPointTrace hUopen).mpr
        change IsRetrocompact ((Subtype.val : closedPoints X → X) ⁻¹' U)
        exact hUE.symm ▸ hEretro
      have hUfinite := finite_local hUopen.isLocallyClosed
      have htraceU : closedPointTrace U = closedPointTrace (E : Set X) := by
        calc
          closedPointTrace U = (e E : Set (closedPoints X)) := by
            simpa [closedPointTrace] using hUE
          _ = closedPointTrace (E : Set X) := he_trace E
      have hEU : (E : Set X) ⊆ U :=
        finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
          (finite_normal_form E.property) hUfinite htraceU.symm.le
      have hUE' : U ⊆ (E : Set X) :=
        finiteUnionLocallyClosed_subset_of_closedPointTrace_subset
          hUfinite (finite_normal_form E.property) htraceU.le
      have hEq : (E : Set X) = U := hEU.antisymm hUE'
      exact ⟨hEq ▸ hUopen, hEq ▸ hUretro⟩
  have he_compl : ∀ E : {E : Set X // IsConstructible E},
      e ⟨(E : Set X)ᶜ, E.property.compl⟩ =
        ⟨(e E : Set (closedPoints X))ᶜ, (e E).property.compl⟩ := by
    intro E
    apply Subtype.ext
    calc
      (e ⟨(E : Set X)ᶜ, E.property.compl⟩ : Set (closedPoints X)) =
          closedPointTrace ((E : Set X)ᶜ) := he_trace _
      _ = (closedPointTrace (E : Set X))ᶜ := by
        ext x
        simp [closedPointTrace]
      _ = (e E : Set (closedPoints X))ᶜ := by rw [he_trace E]
  refine ⟨e, he_trace, he_subset, he_open_retrocompact, ?_⟩
  intro E _
  exact he_compl E

end JacobsonSpaces

end Formalization.Books.Topology.Unit18
