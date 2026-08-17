import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Maps.Strict.Basic

/-!
# Topology, Chapter 6: Submersive maps

The chapter's induced and quotient topologies, strict maps, quotient maps, and
the criteria for open and closed maps are represented by Mathlib's canonical
topology APIs.
-/

namespace Formalization.Books.Topology.Unit06

open Set Function _root_.Topology

section InducedTopology

/-
The source's induced topology is `TopologicalSpace.induced`.  The following
interface collects the source lemma's weakest-topology, open-set, and
closed-set characterizations.  `hf` records the source's injectivity
hypothesis; the canonical characterization itself is valid without it.
-/

theorem induced_topology_characterization
    {X Y : Type*} (tX : TopologicalSpace X) (f : Y → X) (_hf : Injective f) :
    @_root_.Topology.IsInducing Y X (TopologicalSpace.induced f tX) tX f ∧
      (∀ tY : TopologicalSpace Y,
        @Continuous Y X tY tX f → tY ≤ TopologicalSpace.induced f tX) ∧
      (∀ U : Set Y,
        @IsOpen Y (TopologicalSpace.induced f tX) U ↔
          ∃ V : Set X, @IsOpen X tX V ∧ f ⁻¹' V = U) ∧
      (∀ Z : Set Y,
        @IsClosed Y (TopologicalSpace.induced f tX) Z ↔
          ∃ W : Set X, @IsClosed X tX W ∧ f ⁻¹' W = Z) := by
  refine ⟨Topology.IsInducing.induced f, ?_, ?_, ?_⟩
  · intro tY h_cont
    exact h_cont.le_induced
  · intro U
    exact isOpen_induced_iff
  · intro Z
    exact isClosed_induced_iff

/- The induced topology on a subset is the topology of its subtype. -/

theorem subtype_inclusion_isInducing {X : Type*} [TopologicalSpace X] (E : Set X) :
    IsInducing ((↑) : E → X) :=
  IsInducing.subtypeVal

end InducedTopology

section QuotientTopology

/-
The source's quotient topology is `TopologicalSpace.coinduced`.  The
surjectivity hypothesis turns its coinducing map into the canonical quotient
map, while the remaining conjuncts record the strongest-topology, open-set,
and closed-set characterizations.
-/

theorem quotient_topology_characterization
    {X Y : Type*} (tX : TopologicalSpace X) (f : X → Y) (hf : Surjective f) :
    @_root_.Topology.IsQuotientMap X Y tX (TopologicalSpace.coinduced f tX) f ∧
      (∀ tY : TopologicalSpace Y,
        @Continuous X Y tX tY f → TopologicalSpace.coinduced f tX ≤ tY) ∧
      (∀ V : Set Y,
        @IsOpen Y (TopologicalSpace.coinduced f tX) V ↔
          @IsOpen X tX (f ⁻¹' V)) ∧
      (∀ Z : Set Y,
        @IsClosed Y (TopologicalSpace.coinduced f tX) Z ↔
          @IsClosed X tX (f ⁻¹' Z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · let _ : TopologicalSpace Y := TopologicalSpace.coinduced f tX
    exact ⟨⟨rfl⟩, hf⟩
  · intro tY h_cont
    exact h_cont.coinduced_le
  · intro V
    exact isOpen_coinduced
  · intro Z
    exact isClosed_coinduced

theorem quotient_topology_isQuotientMap
    {X Y : Type*} (tX : TopologicalSpace X) (f : X → Y) (hf : Surjective f) :
    @_root_.Topology.IsQuotientMap X Y tX (TopologicalSpace.coinduced f tX) f := by
  let _ : TopologicalSpace Y := TopologicalSpace.coinduced f tX
  exact ⟨⟨rfl⟩, hf⟩

end QuotientTopology

section ImageFactorization

/-
For a continuous `f`, the source's two topologies on `f(X)` are respectively
the coinduced topology along `Set.rangeFactorization f` and the subtype
topology along the range inclusion.  The identity from the former to the
latter is continuous.
-/

theorem range_inclusion_isInducing
    {X Y : Type*} [TopologicalSpace Y] (f : X → Y) :
    IsInducing ((↑) : Set.range f → Y) :=
  IsInducing.subtypeVal

theorem rangeFactorization_isQuotientMap_coinduced
    {X Y : Type*} [tX : TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    @IsQuotientMap X (Set.range f) tX
      (TopologicalSpace.coinduced (Set.rangeFactorization f) tX)
      (Set.rangeFactorization f) := by
  let _ : TopologicalSpace (Set.range f) :=
    TopologicalSpace.coinduced (Set.rangeFactorization f) tX
  exact ⟨⟨rfl⟩, Set.rangeFactorization_surjective⟩

theorem continuous_range_quotient_to_induced
    {X Y : Type*} [tX : TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    @Continuous (Set.range f) (Set.range f)
      (TopologicalSpace.coinduced (Set.rangeFactorization f) tX)
      (inferInstance : TopologicalSpace (Set.range f))
      (id : Set.range f → Set.range f) := by
  rw [continuous_coinduced_dom]
  simpa [Function.comp_def] using hf.rangeFactorization

end ImageFactorization

section StrictAndSubmersive

/-
Mathlib's `Topology.IsStrictMap` is the source's strict-map notion: it says
that the natural map `X → f(X)` is a quotient map, which is exactly equality
of the quotient and induced topologies on the image.  Mathlib's
`Topology.IsQuotientMap` is the source's submersive notion; the theorem below
is the source's “surjective and strict” characterization.
-/

theorem isSubmersive_iff_isStrictMap_and_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsQuotientMap f ↔ IsStrictMap f ∧ Surjective f :=
  isQuotientMap_iff_isStrictMap_surjective

theorem isSubmersive_iff_open_and_closed_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsQuotientMap f ↔
      Surjective f ∧
        (∀ T : Set Y, IsOpen T ↔ IsOpen (f ⁻¹' T)) ∧
        (∀ T : Set Y, IsClosed T ↔ IsClosed (f ⁻¹' T)) := by
  constructor
  · intro h
    refine ⟨h.surjective, ?_, (isQuotientMap_iff_isClosed.mp h).2⟩
    intro T
    exact h.isCoinducing.isOpen_preimage.symm
  · rintro ⟨h_surj, _h_open, h_closed⟩
    exact isQuotientMap_iff_isClosed.mpr ⟨h_surj, h_closed⟩

end StrictAndSubmersive

section OpenMaps

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} {T : Set Y}

theorem openMap_quotient_preimage_closure
    (h_open : IsOpenMap f) (h_cont : Continuous f) (_h_surj : Surjective f) :
    f ⁻¹' closure T = closure (f ⁻¹' T) := by
  simpa using h_open.preimage_closure_eq_closure_preimage h_cont T

theorem openMap_quotient_isClosed_iff
    (h_open : IsOpenMap f) (h_cont : Continuous f) (h_surj : Surjective f) :
    IsClosed T ↔ IsClosed (f ⁻¹' T) := by
  exact (isQuotientMap_iff_isClosed.mp (h_open.isQuotientMap h_cont h_surj)).2 T

theorem openMap_quotient_isOpen_iff
    (h_open : IsOpenMap f) (h_cont : Continuous f) (h_surj : Surjective f) :
    IsOpen T ↔ IsOpen (f ⁻¹' T) := by
  exact ((h_open.isQuotientMap h_cont h_surj).isCoinducing.isOpen_preimage).symm

theorem openMap_quotient_isLocallyClosed_iff
    (h_open : IsOpenMap f) (h_cont : Continuous f) (h_surj : Surjective f) :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := by
  rw [isLocallyClosed_iff_isOpen_coborder, isLocallyClosed_iff_isOpen_coborder,
    coborder_preimage h_open h_cont T]
  exact openMap_quotient_isOpen_iff h_open h_cont h_surj

/- The source's “in particular” is Mathlib's existing `IsOpenMap.isQuotientMap`. -/

theorem openMap_quotient_isSubmersive
    (h_open : IsOpenMap f) (h_cont : Continuous f) (h_surj : Surjective f) :
    IsQuotientMap f :=
  h_open.isQuotientMap h_cont h_surj

end OpenMaps

section ClosedMaps

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} {T : Set Y}

theorem closedMap_quotient_closure_image
    (h_closed : IsClosedMap f) (h_cont : Continuous f) (_h_surj : Surjective f) :
    closure T = f '' closure (f ⁻¹' T) := by
  apply subset_antisymm
  · refine closure_minimal ?_ (h_closed _ isClosed_closure)
    intro y hy
    obtain ⟨x, rfl⟩ := _h_surj y
    exact ⟨x, subset_closure hy, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    exact h_cont.closure_preimage_subset T hx

theorem closedMap_quotient_isClosed_iff
    (h_closed : IsClosedMap f) (h_cont : Continuous f) (h_surj : Surjective f) :
    IsClosed T ↔ IsClosed (f ⁻¹' T) := by
  exact (isQuotientMap_iff_isClosed.mp (h_closed.isQuotientMap h_cont h_surj)).2 T

theorem closedMap_quotient_isOpen_iff
    (h_closed : IsClosedMap f) (h_cont : Continuous f) (h_surj : Surjective f) :
    IsOpen T ↔ IsOpen (f ⁻¹' T) := by
  exact ((h_closed.isQuotientMap h_cont h_surj).isCoinducing.isOpen_preimage).symm

theorem closedMap_quotient_isLocallyClosed_iff
    (h_closed : IsClosedMap f) (h_cont : Continuous f) (h_surj : Surjective f) :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := by
  constructor
  · intro hT
    exact hT.preimage h_cont
  · intro hT
    obtain ⟨U, Z, hU, hZ, hUZ⟩ := hT
    have hg_cont : Continuous (Set.imageFactorization f Z) := by
      exact (h_cont.comp continuous_subtype_val).subtype_mk _
    have hg_closed : IsClosedMap (Set.imageFactorization f Z) := by
      exact (h_closed.domRestrict hZ).subtype_mk _
    have hg_surj : Surjective (Set.imageFactorization f Z) := by
      intro z
      rcases z.2 with ⟨x, hx, hxz⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
    have hg_quot : IsQuotientMap (Set.imageFactorization f Z) :=
      hg_closed.isQuotientMap hg_cont hg_surj
    let T' : Set (f '' Z) := (Subtype.val : f '' Z → Y) ⁻¹' T
    have hpre : (Set.imageFactorization f Z) ⁻¹' T' =
        (Subtype.val : Z → X) ⁻¹' U := by
      ext z
      change (z : X) ∈ f ⁻¹' T ↔ (z : X) ∈ U
      rw [hUZ]
      simp
    have hT'_open : IsOpen T' := by
      apply hg_quot.isCoinducing.isOpen_preimage.mp
      rw [hpre]
      exact hU.preimage continuous_subtype_val
    obtain ⟨V, hV, hVT⟩ := IsInducing.subtypeVal.isOpen_iff.mp hT'_open
    have hTsub : T ⊆ f '' Z := by
      intro y hy
      obtain ⟨x, rfl⟩ := h_surj y
      have hxZ : x ∈ Z := by
        have hxUZ : x ∈ U ∩ Z := by
          have hxT : x ∈ f ⁻¹' T := hy
          rw [hUZ] at hxT
          exact hxT
        exact hxUZ.2
      exact ⟨x, hxZ, rfl⟩
    have h_eq : V ∩ (f '' Z) = T := by
      ext y
      constructor
      · rintro ⟨hyV, hyZ⟩
        have hyT' : (⟨y, hyZ⟩ : f '' Z) ∈ T' := by
          have hyV' : (⟨y, hyZ⟩ : f '' Z) ∈
              (Subtype.val : f '' Z → Y) ⁻¹' V := hyV
          rw [hVT] at hyV'
          exact hyV'
        change y ∈ T at hyT'
        exact hyT'
      · intro hyT
        have hyZ : y ∈ f '' Z := hTsub hyT
        have hyT' : (⟨y, hyZ⟩ : f '' Z) ∈ T' := hyT
        have hyV : (⟨y, hyZ⟩ : f '' Z) ∈
            (Subtype.val : f '' Z → Y) ⁻¹' V := by
          rw [hVT]
          exact hyT'
        exact ⟨hyV, hyZ⟩
    exact ⟨V, f '' Z, hV, h_closed Z hZ, h_eq.symm⟩

/- The source's “in particular” is Mathlib's existing `IsClosedMap.isQuotientMap`. -/

theorem closedMap_quotient_isSubmersive
    (h_closed : IsClosedMap f) (h_cont : Continuous f) (h_surj : Surjective f) :
    IsQuotientMap f :=
  h_closed.isQuotientMap h_cont h_surj

end ClosedMaps

end Formalization.Books.Topology.Unit06
