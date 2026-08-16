import Mathlib.Algebra.Group.Finsupp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Maps.Basic

/-!
# Examples, Chapter 80: Different colimit topologies

The source uses the increasing union of `ℚ × ℝ^n`.  We model its underlying
additive group by `ℚ × (ℕ →₀ ℝ)`: a finitely supported real sequence records
the coordinates `x₁, x₂, …` at indices `0, 1, …`, and the rational coordinate
is kept separate.  The stages are indexed by `n : ℕ` and represent the
source's `G_(n + 1)`.
-/

noncomputable section

open Set
open Topology
open scoped Pointwise

namespace Formalization.«Books.Examples».Unit80

/-! ### The stages and their inclusions -/

/-- The source stage `G_(n + 1) = ℚ × ℝ^(n + 1)`. -/
abbrev Stage (n : ℕ) := ℚ × (Fin (n + 1) → ℝ)

/-- Each stage carries the usual product/finite-dimensional topology and is an
abelian topological group under addition. -/
theorem stage_is_topologicalAddGroup (n : ℕ) :
    IsTopologicalAddGroup (Stage n) := inferInstance

/-- The underlying additive group of the increasing union. -/
abbrev ColimitGroup := ℚ × (ℕ →₀ ℝ)

/-- The index map sending the source coordinate `x_(i + 1)` to index `i`. -/
def stageIndexEmbedding (n : ℕ) : Fin (n + 1) ↪ ℕ where
  toFun i := i.1
  inj' _ _ h := Fin.ext h

/-- A finite real vector, viewed as a finitely supported sequence. -/
def stageRealEmbedding (n : ℕ) (x : Fin (n + 1) → ℝ) : ℕ →₀ ℝ :=
  Finsupp.mapDomain (stageIndexEmbedding n)
    (Finsupp.equivFunOnFinite.symm x)

/-- Append the zero coordinate to a finite real vector. -/
def appendZero (n : ℕ) (x : Fin (n + 1) → ℝ) : Fin ((n + 1) + 1) → ℝ :=
  fun i ↦ if h : i.1 < n + 1 then x ⟨i.1, h⟩ else 0

/-- The transition map `G_(n + 1) → G_(n + 2)`. -/
def stageMap (n : ℕ) : Stage n → Stage (n + 1) :=
  fun x ↦ (x.1, appendZero n x.2)

/-- The inclusion of a stage into the underlying increasing union. -/
def stageInclusion (n : ℕ) : Stage n → ColimitGroup :=
  fun x ↦ (x.1, stageRealEmbedding n x.2)

/-- The transition maps preserve the additive group structures. -/
theorem stageMap_zero (n : ℕ) : stageMap n (0 : Stage n) = 0 := by
  sorry

theorem stageMap_add (n : ℕ) (x y : Stage n) :
    stageMap n (x + y) = stageMap n x + stageMap n y := by
  sorry

/-- The maps into the union preserve the additive group structures. -/
theorem stageInclusion_zero (n : ℕ) : stageInclusion n (0 : Stage n) = 0 := by
  sorry

theorem stageInclusion_add (n : ℕ) (x y : Stage n) :
    stageInclusion n (x + y) = stageInclusion n x + stageInclusion n y := by
  sorry

/-- The transition maps are the closed embeddings from the source. -/
theorem stageMap_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (stageMap n) := by
  sorry

/-- The maps into the union are compatible with the transition maps. -/
theorem stageInclusion_comp_stageMap (n : ℕ) :
    (fun x ↦ stageInclusion (n + 1) (stageMap n x)) = stageInclusion n := by
  sorry

/- The finitely supported model really is the increasing union of the finite
   stages, which is the carrier-level part of the source's notation
   `G = colim G_n`. -/
theorem stageInclusions_cover :
    ⋃ n : ℕ, Set.range (stageInclusion n) = (Set.univ : Set ColimitGroup) := by
  sorry

/-! ### The colimit topology -/

/-- The topology used for the colimit in topological spaces. -/
@[instance_reducible]
def colimitTopology : TopologicalSpace ColimitGroup :=
  ⨆ n : ℕ, (inferInstance : TopologicalSpace (Stage n)).coinduced (stageInclusion n)

instance colimitTopologicalSpace : TopologicalSpace ColimitGroup := colimitTopology

/-- The source's displayed criterion for openness is definitionally the
colimit-topology criterion. -/
theorem isOpen_colimit_iff (U : Set ColimitGroup) :
    IsOpen U ↔ ∀ n : ℕ, IsOpen (stageInclusion n ⁻¹' U) :=
  by
    change IsOpen[colimitTopology] U ↔ _
    simp only [isOpen_iSup_iff, isOpen_coinduced]

/-! ### The bad open set -/

/-- The set `U` from the source, with finitely supported real coordinates. -/
def badSet : Set ColimitGroup :=
  {x | ∀ j : ℕ, 0 < j →
    |x.2 (j - 1)| < |Real.cos ((j : ℝ) * (x.1 : ℝ))|}

/-- The rational coordinate axis. -/
def rationalAxis (x₀ : ℚ) : ColimitGroup :=
  (x₀, 0)

/-- The positive real coordinate axis, with source coordinate `j` stored at
index `j - 1`. -/
def realAxis (j : ℕ) (xⱼ : ℝ) : ColimitGroup :=
  (0, Finsupp.single (j - 1) xⱼ)

/-- The mixed vector used in the contradiction argument. -/
def mixedVector (x₀ : ℚ) (j : ℕ) (xⱼ : ℝ) : ColimitGroup :=
  rationalAxis x₀ + realAxis j xⱼ

theorem mixedVector_eq (x₀ : ℚ) (j : ℕ) (xⱼ : ℝ) :
    mixedVector x₀ j xⱼ = (x₀, Finsupp.single (j - 1) xⱼ) := by
  simp [mixedVector, rationalAxis, realAxis]

/-- The cosine factor in the definition of `U` never vanishes at a rational
multiple of a positive integer.  This is the precise nonvanishing fact used
to prove slice-openness. -/
theorem rational_cosine_ne_zero (j : ℕ) (x₀ : ℚ) (hj : 0 < j) :
    Real.cos ((j : ℝ) * (x₀ : ℝ)) ≠ 0 := by
  sorry

/-- Every finite-dimensional slice of `U` is open. -/
theorem badSet_slice_isOpen (n : ℕ) :
    IsOpen (stageInclusion n ⁻¹' badSet) := by
  sorry

/-- The set `U` is open for the final topology, by the slice criterion. -/
theorem badSet_isOpen : IsOpen badSet := by
  exact (isOpen_colimit_iff badSet).2 (fun n ↦ badSet_slice_isOpen n)

/-- The origin belongs to `U`. -/
theorem zero_mem_badSet : (0 : ColimitGroup) ∈ badSet := by
  sorry

/-! ### The neighbourhood contradiction -/

/-- A neighbourhood whose self-sum is contained in the bad set. -/
def AddNeighborhoodWithSumSubset (V U : Set ColimitGroup) : Prop :=
  IsOpen V ∧ (0 : ColimitGroup) ∈ V ∧ V + V ⊆ U

/-- Continuity of addition at the origin would produce the neighbourhood used
in the source's contradiction. -/
theorem exists_addNeighborhoodWithSumSubset_of_topologicalAddGroup
    (hG : IsTopologicalAddGroup ColimitGroup) :
    ∃ V : Set ColimitGroup, AddNeighborhoodWithSumSubset V badSet := by
  let _ : IsTopologicalAddGroup ColimitGroup := hG
  obtain ⟨V, hV, h0, hVV⟩ :=
    exists_open_nhds_zero_add_subset (badSet_isOpen.mem_nhds zero_mem_badSet)
  exact ⟨V, hV, h0, hVV⟩

/-- A radius for the rational coordinate axis. -/
def IsRationalCoordinateRadius (V : Set ColimitGroup) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ x₀ : ℚ, |(x₀ : ℝ)| < ε → rationalAxis x₀ ∈ V

/-- A radius for a positive real coordinate axis. -/
def IsRealCoordinateRadius (V : Set ColimitGroup) (j : ℕ) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ xⱼ : ℝ, |xⱼ| < ε → realAxis j xⱼ ∈ V

/-- The axis-coordinate radii supplied by an open neighbourhood of zero. -/
theorem exists_coordinate_radii_of_open_mem_zero
    {V : Set ColimitGroup} (hV : IsOpen V) (h0 : (0 : ColimitGroup) ∈ V) :
    (∃ ε₀ : ℝ, IsRationalCoordinateRadius V ε₀) ∧
      ∀ j : ℕ, 0 < j → ∃ εⱼ : ℝ, IsRealCoordinateRadius V j εⱼ := by
  sorry

/-- The self-sum hypothesis puts the mixed vector in `U`. -/
theorem mixedVector_mem_badSet_of_sum_subset
    {V : Set ColimitGroup} (hVV : V + V ⊆ badSet)
    {x₀ : ℚ} {j : ℕ} {xⱼ : ℝ}
    (hx₀ : rationalAxis x₀ ∈ V) (hxⱼ : realAxis j xⱼ ∈ V) :
    mixedVector x₀ j xⱼ ∈ badSet := by
  sorry

/-- The preceding assertion with the radii used in the source. -/
theorem mixedVector_mem_badSet_of_coordinate_radii
    {V : Set ColimitGroup} (hVV : V + V ⊆ badSet)
    {ε₀ εⱼ : ℝ} {x₀ : ℚ} {j : ℕ} {xⱼ : ℝ}
    (hε₀ : IsRationalCoordinateRadius V ε₀)
    (hεⱼ : IsRealCoordinateRadius V j εⱼ)
    (hx₀ : |(x₀ : ℝ)| < ε₀) (hxⱼ : |xⱼ| < εⱼ) :
    mixedVector x₀ j xⱼ ∈ badSet := by
  sorry

/-- A positive radius admits a sufficiently large coordinate index. -/
theorem exists_large_coordinate_index {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ j : ℕ, 0 < j ∧ Real.pi / 2 < (j : ℝ) * ε₀ := by
  sorry

/-- Rationals can be chosen inside the rational-coordinate interval while
making the cosine factor arbitrarily small. -/
theorem exists_rational_with_small_cosine
    {ε₀ εⱼ : ℝ} (j : ℕ) (hj : 0 < j) (hε₀ : 0 < ε₀)
    (hlarge : Real.pi / 2 < (j : ℝ) * ε₀) (hεⱼ : 0 < εⱼ) :
    ∃ x₀ : ℚ,
      |(x₀ : ℝ)| < ε₀ ∧
        |Real.cos ((j : ℝ) * (x₀ : ℝ))| < εⱼ := by
  sorry

/-- There is a real coordinate whose absolute value lies strictly between the
absolute cosine value and its prescribed radius. -/
theorem exists_real_with_abs_between
    {c ε : ℝ} (hcε : |c| < ε) :
    ∃ xⱼ : ℝ, |c| < |xⱼ| ∧ |xⱼ| < ε := by
  sorry

/-- The displayed cosine choice contradicts membership in `U`. -/
theorem badSet_contradiction_of_addNeighborhoodWithSumSubset
    {V : Set ColimitGroup}
    (hV : AddNeighborhoodWithSumSubset V badSet) : False := by
  sorry

/-- The final-topology colimit is not a topological additive group. -/
theorem colimitTopology_not_topologicalAddGroup :
    ¬ IsTopologicalAddGroup ColimitGroup := by
  intro hG
  obtain ⟨V, hV⟩ := exists_addNeighborhoodWithSumSubset_of_topologicalAddGroup hG
  exact badSet_contradiction_of_addNeighborhoodWithSumSubset hV

/-! ### The source's concluding comparison -/

/-- The displayed final-topology condition and the failure of topological-group
compatibility together record that the two colimit topologies differ. -/
theorem lemma_colimit_topology :
    ∃ t : TopologicalSpace ColimitGroup,
      (∀ U : Set ColimitGroup,
        @IsOpen ColimitGroup t U ↔
          ∀ n : ℕ, IsOpen (stageInclusion n ⁻¹' U)) ∧
        ¬ @IsTopologicalAddGroup ColimitGroup t inferInstance := by
  refine ⟨colimitTopology, ?_, ?_⟩
  · intro U
    exact isOpen_colimit_iff U
  · exact colimitTopology_not_topologicalAddGroup

end Formalization.«Books.Examples».Unit80
