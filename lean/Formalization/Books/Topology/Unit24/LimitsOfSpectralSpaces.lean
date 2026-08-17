import Formalization.Books.Topology.Unit23.SpectralSpaces
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Topology, Chapter 24: Limits of spectral spaces

The chapter uses Mathlib's `TopCat` limits, `SpectralSpace`, `IsSpectralMap`,
`IsConstructible`, and the constructible topology.  The source-facing
`inverseLimitSet` and directed-family predicates below make the subset and
intersection descriptions explicit while retaining those canonical APIs.
-/

namespace Formalization.Books.Topology.Unit24

open Set Function CategoryTheory CategoryTheory.Limits _root_.Topology TopologicalSpace
open Formalization.Books.Topology.Unit23

universe u v

noncomputable section

section IntroductoryFacts

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/- The first introductory assertion is already recorded in Unit 23 as
  `spectralSpace_iff_directed_inverse_limit_finite_sober`. -/

/-- A finite sober topological space is spectral.

Sobriety is expressed canonically as `QuasiSober` together with `T0Space`.
-/
theorem spectralSpace_of_finite_sober [Finite X] [QuasiSober X] [T0Space X] :
    SpectralSpace X := by
  sorry

/-- Every continuous map between finite sober spaces is spectral. -/
theorem isSpectralMap_of_continuous_of_finite_sober
    [Finite X] [Finite Y] [QuasiSober X] [T0Space X]
    [QuasiSober Y] [T0Space Y] (f : X → Y) (hf : Continuous f) :
    IsSpectralMap f := by
  sorry

end IntroductoryFacts

section InverseLimitInterfaces

variable {J : Type v} [SmallCategory J]

/-- A diagram of spectral spaces and spectral transition maps. -/
def IsSpectralDiagram (F : J ⥤ TopCat.{max v u}) : Prop :=
  (∀ j : J, SpectralSpace (F.obj j)) ∧
    ∀ (j i : J) (f : j ⟶ i), IsSpectralMap (F.map f)

/-- The subset of the underlying `TopCat` limit whose `j`-component lies in
the prescribed subset `Z j` for every object `j`. -/
def inverseLimitSet (F : J ⥤ TopCat.{max v u}) (Z : ∀ j, Set (F.obj j)) :
    Set ((limit F : TopCat.{max v u}) : Type (max v u)) :=
  {x | ∀ j, (limit.π F j) x ∈ Z j}

/-- Compatibility of a family of subsets with the transition maps of a
diagram. -/
def CompatibleSetFamily (F : J ⥤ TopCat.{max v u})
    (Z : ∀ j, Set (F.obj j)) : Prop :=
  ∀ (j i : J) (f : j ⟶ i), (F.map f) '' Z j ⊆ Z i

end InverseLimitInterfaces

section QuasiCompactness

variable {J : Type v} [SmallCategory J] [IsCofiltered J]

/- Constructibly closed compatible subsets in a cofiltered spectral diagram
have quasi-compact inverse limit. -/
theorem inverseLimitSet_isCompact_of_constructibleClosed
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (Z : ∀ j, Set (F.obj j))
    (hZ : ∀ j, IsClosed[constructibleTopology (F.obj j)] (Z j))
    (hZmap : CompatibleSetFamily F Z) :
    IsCompact (inverseLimitSet F Z) := by
  sorry

/-- The inverse limit of a cofiltered diagram of spectral spaces is
quasi-compact. -/
theorem inverseLimit_spectralDiagram_isCompact
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F) :
    CompactSpace ((limit F : TopCat.{max v u}) : Type (max v u)) := by
  sorry

end QuasiCompactness

section Nonemptiness

variable {J : Type v} [SmallCategory J] [IsCofiltered J]

/- Nonempty constructibly closed compatible subsets in a cofiltered spectral
diagram have nonempty inverse limit. -/
theorem inverseLimitSet_isNonempty_of_constructibleClosed
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (Z : ∀ j, Set (F.obj j))
    (hZnonempty : ∀ j, (Z j).Nonempty)
    (hZ : ∀ j, IsClosed[constructibleTopology (F.obj j)] (Z j))
    (hZmap : CompatibleSetFamily F Z) :
    (inverseLimitSet F Z).Nonempty := by
  sorry

/-- The inverse limit of a cofiltered diagram of nonempty spectral spaces is
nonempty. -/
theorem inverseLimit_spectralDiagram_isNonempty
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (hXnonempty : ∀ j, Nonempty (F.obj j)) :
    Nonempty ((limit F : TopCat.{max v u}) : Type (max v u)) := by
  sorry

end Nonemptiness

section ConstructibleInclusions

variable {J : Type v} [SmallCategory J] [IsCofiltered J]

/-- An inclusion between inverse-image subsets at one stage is witnessed at a
single stage of a cofiltered spectral diagram. -/
theorem inverseLimit_preimage_subset_iff
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (i : J) {E G : Set (F.obj i)}
    (hE : IsClosed[constructibleTopology (F.obj i)] E)
    (hG : IsOpen[constructibleTopology (F.obj i)] G) :
    (limit.π F i) ⁻¹' E ⊆ (limit.π F i) ⁻¹' G ↔
      ∃ (j : J) (f : j ⟶ i), (F.map f) ⁻¹' E ⊆ (F.map f) ⁻¹' G := by
  sorry

/-- Every constructible subset of a cofiltered inverse limit descends to one
stage; source-open and source-closed subsets descend to an open and closed
subset, respectively. -/
theorem inverseLimit_constructibleSet_descends
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    {E : Set ((limit F : TopCat.{max v u}) : Type (max v u))}
    (hE : IsConstructible E) :
    ∃ (i : J) (E_i : Set (F.obj i)),
      IsConstructible E_i ∧
        ((IsOpen E → IsOpen E_i) ∧ (IsClosed E → IsClosed E_i)) ∧
          (limit.π F i) ⁻¹' E_i = E := by
  sorry

end ConstructibleInclusions

section SpectralInverseLimits

variable {J : Type v} [SmallCategory J] [IsCofiltered J]

/-- A cofiltered inverse limit of spectral spaces along spectral maps is
spectral, and all its projections are spectral maps. -/
theorem spectralSpace_of_inverseLimit_spectralDiagram
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F) :
    SpectralSpace ((limit F : TopCat.{max v u}) : Type (max v u)) ∧
      ∀ i : J, IsSpectralMap (limit.π F i) := by
  sorry

end SpectralInverseLimits

section DescendQuasiCompactOpens

variable {J : Type v} [SmallCategory J] [IsCofiltered J]

/-- A quasi-compact open of an inverse limit descends to a quasi-compact
open at one stage. -/
theorem inverseLimit_quasiCompactOpen_descends
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    {U : Set ((limit F : TopCat.{max v u}) : Type (max v u))}
    (hUopen : IsOpen U) (hUcompact : IsCompact U) :
    ∃ (i : J) (U_i : Set (F.obj i)),
      IsOpen U_i ∧ IsCompact U_i ∧ (limit.π F i) ⁻¹' U_i = U := by
  sorry

/-- An inclusion between quasi-compact opens at two stages descends to a
common stage. -/
theorem inverseLimit_quasiCompactOpen_subset_descends
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (i j : J) {U_i : Set (F.obj i)} {U_j : Set (F.obj j)}
    (hU_i_open : IsOpen U_i) (hU_i_compact : IsCompact U_i)
    (hU_j_open : IsOpen U_j) (hU_j_compact : IsCompact U_j)
    (hU : (limit.π F i) ⁻¹' U_i ⊆ (limit.π F j) ⁻¹' U_j) :
    ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j),
      (F.map a) ⁻¹' U_i ⊆ (F.map b) ⁻¹' U_j := by
  sorry

/-- A finite union equality between quasi-compact opens at a stage descends
to an equality at a later stage. -/
theorem inverseLimit_quasiCompactOpen_union_descends
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (i : J) (n : ℕ) {U_i : Set (F.obj i)} (U_ι : Fin n → Set (F.obj i))
    (hU_i_open : IsOpen U_i) (hU_i_compact : IsCompact U_i)
    (hU_ι_open : ∀ l, IsOpen (U_ι l))
    (hU_ι_compact : ∀ l, IsCompact (U_ι l))
    (hU : (limit.π F i) ⁻¹' U_i = ⋃ l, (limit.π F i) ⁻¹' (U_ι l)) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' U_i = ⋃ l, (F.map a) ⁻¹' (U_ι l) := by
  sorry

/-- The intersection analogue of `inverseLimit_quasiCompactOpen_union_descends`. -/
theorem inverseLimit_quasiCompactOpen_inter_descends
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (i : J) (n : ℕ) {U_i : Set (F.obj i)} (U_ι : Fin n → Set (F.obj i))
    (hU_i_open : IsOpen U_i) (hU_i_compact : IsCompact U_i)
    (hU_ι_open : ∀ l, IsOpen (U_ι l))
    (hU_ι_compact : ∀ l, IsCompact (U_ι l))
    (hU : (limit.π F i) ⁻¹' U_i = ⋂ l, (limit.π F i) ⁻¹' (U_ι l)) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' U_i = ⋂ l, (F.map a) ⁻¹' (U_ι l) := by
  sorry

end DescendQuasiCompactOpens

section GeneralizationStableIntersections

variable {X : Type u} [TopologicalSpace X]

/-- The set of points which specialize to a point of `E`. -/
def pointsSpecializingTo (E : Set X) : Set X :=
  {x | ∃ y ∈ E, x ⤳ y}

/-- A subset which is an intersection of constructible subsets. -/
def IsIntersectionOfConstructibleSets (W : Set X) : Prop :=
  ∃ S : Set (Set X), W = ⋂₀ S ∧ ∀ E ∈ S, IsConstructible E

/-- A subset which is an intersection of quasi-compact open subsets. -/
def IsIntersectionOfQuasiCompactOpens (W : Set X) : Prop :=
  ∃ S : Set (Set X), W = ⋂₀ S ∧ ∀ U ∈ S, IsOpen U ∧ IsCompact U

/-- A nonempty directed family of quasi-compact opens, ordered by refinement. -/
def IsDirectedFamilyOfQuasiCompactOpens (I : Set (Set X)) : Prop :=
  I.Nonempty ∧
    (∀ U ∈ I, IsOpen U ∧ IsCompact U) ∧
      ∀ U ∈ I, ∀ V ∈ I, ∃ W ∈ I, W ⊆ U ∩ V

/-- A subset represented by a nonempty directed intersection of quasi-compact
opens. -/
def IsDirectedIntersectionOfQuasiCompactOpens (W : Set X) : Prop :=
  ∃ I : Set (Set X), IsDirectedFamilyOfQuasiCompactOpens I ∧ W = ⋂₀ I

/-- The five equivalent descriptions of generalization-stable intersections
in a spectral space. -/
theorem isIntersectionOfConstructibleSets_iff_isCompact_iff_pointsSpecializingTo
    [SpectralSpace X] {W : Set X} :
    (IsIntersectionOfConstructibleSets W ∧ StableUnderGeneralization W ↔
        IsCompact W ∧ StableUnderGeneralization W) ∧
      (IsCompact W ∧ StableUnderGeneralization W ↔
        ∃ E : Set X, IsCompact E ∧ W = pointsSpecializingTo E) ∧
        ((∃ E : Set X, IsCompact E ∧ W = pointsSpecializingTo E) ↔
          IsIntersectionOfQuasiCompactOpens W) ∧
          (IsIntersectionOfQuasiCompactOpens W ↔
            IsDirectedIntersectionOfQuasiCompactOpens W) := by
  sorry

/-- A directed intersection of quasi-compact opens in a spectral space is
spectral for its induced topology. -/
theorem spectralSpace_of_isDirectedIntersectionOfQuasiCompactOpens
    [SpectralSpace X] {W : Set X}
    (hW : IsDirectedIntersectionOfQuasiCompactOpens W) :
    SpectralSpace W := by
  sorry

/-- The diagram of inclusions of a family of subsets ordered by inclusion. -/
def directedIntersectionDiagram (I : Set (Set X)) : I ⥤ TopCat.{u} where
  obj U := TopCat.of (U : Set X)
  map {U V} f :=
    TopCat.ofHom
      ⟨(fun x : (U : Set X) =>
          (⟨x.1, f.le x.2⟩ : (V : Set X))),
        continuous_subtype_val.subtype_mk (fun x => f.le x.2)⟩
  map_id U := by
    apply TopCat.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp := by
    intro U V W f g
    apply TopCat.ext
    intro x
    apply Subtype.ext
    rfl

/-- The limit of the inclusion diagram is the intersection, as a topological
space. -/
theorem isDirectedIntersectionOfQuasiCompactOpens_isLimit
    [SpectralSpace X] {W : Set X} {I : Set (Set X)}
    (hI : IsDirectedFamilyOfQuasiCompactOpens I) (hW : W = ⋂₀ I) :
    Nonempty
      (W ≃ₜ ((limit (directedIntersectionDiagram I) : TopCat.{u}) : Type u)) := by
  sorry

/-- An open neighbourhood of a directed intersection contains one member of
the directed family. -/
theorem exists_member_of_isDirectedFamilyOfQuasiCompactOpens_subset_of_open
    [SpectralSpace X] {W : Set X} {I : Set (Set X)}
    (hI : IsDirectedFamilyOfQuasiCompactOpens I) (hW : W = ⋂₀ I)
    {U : Set X} (hUopen : IsOpen U) (hWU : W ⊆ U) :
    ∃ V ∈ I, V ⊆ U := by
  sorry

end GeneralizationStableIntersections

section DifferenceByConstructibleSets

variable {X : Type u} [TopologicalSpace X]

/-- The diagram of the differences `U \ E` for a family of subsets ordered by
inclusion. -/
def directedIntersectionDifferenceDiagram (I : Set (Set X)) (E : Set X) : I ⥤ TopCat.{u} where
  obj U := TopCat.of (Set.diff (U : Set X) E)
  map {U V} f :=
    TopCat.ofHom
      ⟨(fun x : (Set.diff (U : Set X) E) =>
          (⟨x.1, f.le x.2.1, x.2.2⟩ : (Set.diff (V : Set X) E))),
        continuous_subtype_val.subtype_mk (fun x => ⟨f.le x.2.1, x.2.2⟩)⟩
  map_id U := by
    apply TopCat.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp := by
    intro U V W f g
    apply TopCat.ext
    intro x
    apply Subtype.ext
    rfl

/-- Removing a constructible subset from the set of points specializing to
that subset leaves a spectral space. -/
theorem spectralSpace_pointsSpecializingTo_diff_constructible
    [SpectralSpace X] {E : Set X} (hE : IsConstructible E) :
    SpectralSpace (Set.diff (pointsSpecializingTo E) E) := by
  sorry

/-- The difference of the points specializing to a constructible subset
is the limit of the corresponding differences of a directed quasi-compact-open
presentation. -/
theorem pointsSpecializingTo_diff_constructible_isLimit
    [SpectralSpace X] {E : Set X} {I : Set (Set X)} (hE : IsConstructible E)
    (hI : IsDirectedFamilyOfQuasiCompactOpens I)
    (hW : pointsSpecializingTo E = ⋂₀ I) :
    Nonempty
      ((Set.diff (pointsSpecializingTo E) E) ≃ₜ
        ((limit (directedIntersectionDifferenceDiagram I E) : TopCat.{u}) : Type u)) := by
  sorry

end DifferenceByConstructibleSets

end

end Formalization.Books.Topology.Unit24
