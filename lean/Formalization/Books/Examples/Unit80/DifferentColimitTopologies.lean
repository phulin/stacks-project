import Mathlib.Algebra.Group.Finsupp
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
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

namespace Formalization.Books.Examples.Unit80

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
  ext <;> simp [stageMap, appendZero]

theorem stageMap_add (n : ℕ) (x y : Stage n) :
    stageMap n (x + y) = stageMap n x + stageMap n y := by
  apply Prod.ext <;> simp [stageMap]
  funext i
  by_cases h : i.1 < n + 1 <;> simp [appendZero, h]

/-- The maps into the union preserve the additive group structures. -/
theorem stageInclusion_zero (n : ℕ) : stageInclusion n (0 : Stage n) = 0 := by
  refine Prod.ext (by rfl) ?_
  change Finsupp.mapDomain _ (Finsupp.equivFunOnFinite.symm (0 : Fin (n + 1) → ℝ)) = 0
  rw [show Finsupp.equivFunOnFinite.symm (0 : Fin (n + 1) → ℝ) = 0 by
    exact Finsupp.ext (fun i => rfl), Finsupp.mapDomain_zero]

theorem stageInclusion_add (n : ℕ) (x y : Stage n) :
    stageInclusion n (x + y) = stageInclusion n x + stageInclusion n y := by
  refine Prod.ext (by rfl) ?_
  change Finsupp.mapDomain _ (Finsupp.equivFunOnFinite.symm (x.2 + y.2)) = _
  rw [show Finsupp.equivFunOnFinite.symm (x.2 + y.2) =
      Finsupp.equivFunOnFinite.symm x.2 + Finsupp.equivFunOnFinite.symm y.2 by
    exact Finsupp.ext (fun i => rfl), Finsupp.mapDomain_add]
  rfl

/-- The transition maps are the closed embeddings from the source. -/
theorem stageMap_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (stageMap n) := by
  let f : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1 + 1) → ℝ) :=
    { toFun := appendZero n
      map_add' := by
        intro x y
        funext i
        by_cases h : i.1 < n + 1 <;> simp [appendZero, h]
      map_smul' := by
        intro c x
        funext i
        by_cases h : i.1 < n + 1 <;> simp [appendZero, h] }
  have hfi : Function.Injective f := by
    intro x y hxy
    funext i
    have h := congr_fun hxy ⟨i.1, Nat.lt_succ_of_lt i.2⟩
    simpa [f, appendZero, i.2] using h
  have hfe : IsClosedEmbedding f :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hfi)
  have happ : IsClosedEmbedding (appendZero n) := by
    simpa [f] using hfe
  change IsClosedEmbedding (Prod.map id (appendZero n))
  exact IsClosedEmbedding.prodMap IsClosedEmbedding.id happ

/-- The maps into the union are compatible with the transition maps. -/
theorem stageInclusion_comp_stageMap (n : ℕ) :
    (fun x ↦ stageInclusion (n + 1) (stageMap n x)) = stageInclusion n := by
  funext x
  refine Prod.ext (by rfl) ?_
  change stageRealEmbedding (n + 1) (appendZero n x.2) = stageRealEmbedding n x.2
  ext a
  by_cases ha : a < n + 1
  · let i : Fin (n + 1) := ⟨a, ha⟩
    let i' : Fin (n + 1 + 1) := ⟨a, by omega⟩
    calc
      Finsupp.mapDomain (stageIndexEmbedding (n + 1))
          (Finsupp.equivFunOnFinite.symm (appendZero n x.2)) a =
          Finsupp.mapDomain (stageIndexEmbedding (n + 1))
            (Finsupp.equivFunOnFinite.symm (appendZero n x.2))
              (stageIndexEmbedding (n + 1) i') := by rfl
      _ = Finsupp.equivFunOnFinite.symm (appendZero n x.2) i' :=
        Finsupp.mapDomain_apply (stageIndexEmbedding (n + 1)).injective _ i'
      _ = x.2 i := by
        have han : a ≤ n := by omega
        simp [appendZero, i, i', han]
      _ = Finsupp.equivFunOnFinite.symm x.2 i := by rfl
      _ = Finsupp.mapDomain (stageIndexEmbedding n)
            (Finsupp.equivFunOnFinite.symm x.2) (stageIndexEmbedding n i) :=
        (Finsupp.mapDomain_apply (stageIndexEmbedding n).injective _ i).symm
      _ = Finsupp.mapDomain (stageIndexEmbedding n)
            (Finsupp.equivFunOnFinite.symm x.2) a := by rfl
  · by_cases ha' : a < n + 2
    · have haa : a = n + 1 := by omega
      subst a
      let i' : Fin (n + 1 + 1) := ⟨n + 1, by omega⟩
      calc
        Finsupp.mapDomain (stageIndexEmbedding (n + 1))
              (Finsupp.equivFunOnFinite.symm (appendZero n x.2)) (n + 1) =
            Finsupp.mapDomain (stageIndexEmbedding (n + 1))
              (Finsupp.equivFunOnFinite.symm (appendZero n x.2))
                (stageIndexEmbedding (n + 1) i') := by rfl
        _ = Finsupp.equivFunOnFinite.symm (appendZero n x.2) i' :=
          Finsupp.mapDomain_apply (stageIndexEmbedding (n + 1)).injective _ i'
        _ = 0 := by simp [appendZero, i']
        _ = Finsupp.mapDomain (stageIndexEmbedding n)
              (Finsupp.equivFunOnFinite.symm x.2) (n + 1) := by
          symm
          apply Finsupp.mapDomain_of_notMem_range
          rintro ⟨i, hi⟩
          change i.1 = n + 1 at hi
          omega
    · calc
        Finsupp.mapDomain (stageIndexEmbedding (n + 1))
              (Finsupp.equivFunOnFinite.symm (appendZero n x.2)) a = 0 := by
          apply Finsupp.mapDomain_of_notMem_range
          rintro ⟨i, hi⟩
          change i.1 = a at hi
          omega
        _ = Finsupp.mapDomain (stageIndexEmbedding n)
              (Finsupp.equivFunOnFinite.symm x.2) a := by
          symm
          apply Finsupp.mapDomain_of_notMem_range
          rintro ⟨i, hi⟩
          change i.1 = a at hi
          omega

/- The finitely supported model really is the increasing union of the finite
   stages, which is the carrier-level part of the source's notation
   `G = colim G_n`. -/
theorem stageInclusions_cover :
    ⋃ n : ℕ, Set.range (stageInclusion n) = (Set.univ : Set ColimitGroup) := by
  apply Set.eq_univ_iff_forall.mpr
  rintro ⟨x₀, x⟩
  rw [Set.mem_iUnion]
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range x.support
  refine ⟨n, ?_⟩
  have hsub : (x.support : Set ℕ) ⊆ Set.range (stageIndexEmbedding n) := by
    intro b hb
    have hb' : b ∈ Finset.range n := hn hb
    have hb'' : b < n := by simpa using hb'
    exact ⟨⟨b, Nat.lt_succ_of_lt hb''⟩, rfl⟩
  have hzero : ∀ b ∉ Set.range (stageIndexEmbedding n), x b = 0 := by
    intro b hb
    by_contra h
    apply hb
    apply hsub
    exact Finsupp.mem_support_iff.mpr h
  obtain ⟨y, hy⟩ :=
    (Finsupp.mem_range_mapDomain_iff (stageIndexEmbedding n)
      (stageIndexEmbedding n).injective x).2 hzero
  refine ⟨(x₀, Finsupp.equivFunOnFinite y), ?_⟩
  apply Prod.ext (by rfl)
  simpa [stageInclusion, stageRealEmbedding] using hy

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
  intro h
  rcases Real.cos_eq_zero_iff.mp h with ⟨k, hk⟩
  have hk0 : (2 * k + 1 : ℤ) ≠ 0 := by omega
  have hi : Irrational ((2 * k + 1 : ℤ) * Real.pi) :=
    Irrational.intCast_mul irrational_pi hk0
  exact hi ⟨(2 * (j : ℚ) * x₀), by
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    norm_num
    nlinarith [hk, hjR]⟩

/-- Every finite-dimensional slice of `U` is open. -/
theorem badSet_slice_isOpen (n : ℕ) :
    IsOpen (stageInclusion n ⁻¹' badSet) := by
  let S : Fin (n + 1) → Set (Stage n) := fun i ↦
    {x | |x.2 i| <
      |Real.cos (((i.1 + 1 : ℕ) : ℝ) * (x.1 : ℝ))|}
  have hS : IsOpen (⋂ i, S i) := by
    apply isOpen_iInter_of_finite
    intro i
    dsimp [S]
    apply isOpen_lt
    · exact continuous_abs.comp ((continuous_apply i).comp continuous_snd)
    · exact continuous_abs.comp
        (Real.continuous_cos.comp
          (continuous_const.mul (Rat.continuous_coe_real.comp continuous_fst)))
  have hcoord (x : Stage n) (i : Fin (n + 1)) :
      stageRealEmbedding n x.2 i.1 = x.2 i := by
    change Finsupp.mapDomain (stageIndexEmbedding n)
      (Finsupp.equivFunOnFinite.symm x.2) (stageIndexEmbedding n i) = x.2 i
    rw [Finsupp.mapDomain_apply (stageIndexEmbedding n).injective]
    rfl
  rw [show stageInclusion n ⁻¹' badSet = ⋂ i, S i by
    ext x
    constructor
    · intro hx
      change ∀ j : ℕ, 0 < j →
        |stageRealEmbedding n x.2 (j - 1)| <
          |Real.cos ((j : ℝ) * (x.1 : ℝ))| at hx
      refine Set.mem_iInter.mpr ?_
      intro i
      change |x.2 i| <
        |Real.cos (((i.1 + 1 : ℕ) : ℝ) * (x.1 : ℝ))|
      have hi := hx (i.1 + 1) (by omega)
      have harg : i.1 + 1 - 1 = i.1 := by omega
      rw [harg, hcoord] at hi
      exact hi
    · intro hx
      change ∀ j : ℕ, 0 < j →
        |stageRealEmbedding n x.2 (j - 1)| <
          |Real.cos ((j : ℝ) * (x.1 : ℝ))|
      intro j hj
      by_cases hle : j ≤ n + 1
      · let i : Fin (n + 1) := ⟨j - 1, by omega⟩
        have hi := Set.mem_iInter.mp hx i
        change |x.2 i| <
          |Real.cos (((i.1 + 1 : ℕ) : ℝ) * (x.1 : ℝ))| at hi
        have heval : stageRealEmbedding n x.2 (j - 1) = x.2 i := by
          have hji : i.1 = j - 1 := by rfl
          rw [← hji, hcoord]
        rw [heval]
        have hij : i.1 + 1 = j := by
          dsimp [i]
          omega
        simpa [hij] using hi
      · have hzero : stageRealEmbedding n x.2 (j - 1) = 0 := by
          change Finsupp.mapDomain (stageIndexEmbedding n)
            (Finsupp.equivFunOnFinite.symm x.2) (j - 1) = 0
          apply Finsupp.mapDomain_of_notMem_range
          rintro ⟨i, hi⟩
          change i.1 = j - 1 at hi
          omega
        rw [hzero, abs_zero]
        exact abs_pos.mpr (rational_cosine_ne_zero j x.1 hj)]
  exact hS

/-- The set `U` is open for the final topology, by the slice criterion. -/
theorem badSet_isOpen : IsOpen badSet := by
  exact (isOpen_colimit_iff badSet).2 (fun n ↦ badSet_slice_isOpen n)

/-- The origin belongs to `U`. -/
theorem zero_mem_badSet : (0 : ColimitGroup) ∈ badSet := by
  change ∀ j : ℕ, 0 < j →
    |(0 : ColimitGroup).2 (j - 1)| <
      |Real.cos ((j : ℝ) * ((0 : ColimitGroup).1 : ℝ))|
  intro j hj
  simp

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
  have hstage (n : ℕ) : IsOpen (stageInclusion n ⁻¹' V) :=
    (isOpen_colimit_iff V).1 hV n
  have hzero_stage (n : ℕ) : (0 : Stage n) ∈ stageInclusion n ⁻¹' V := by
    change stageInclusion n (0 : Stage n) ∈ V
    rw [stageInclusion_zero]
    exact h0
  let qr : ℚ → Stage 0 := fun q ↦ (q, 0)
  have hqr : Continuous qr := continuous_id.prodMk continuous_const
  have hqr0 : qr 0 ∈ stageInclusion 0 ⁻¹' V := by
    have hz : qr 0 = (0 : Stage 0) := by rfl
    rw [hz]
    exact hzero_stage 0
  have hopenq : IsOpen (qr ⁻¹' (stageInclusion 0 ⁻¹' V)) :=
    (hstage 0).preimage hqr
  obtain ⟨ε₀, hε₀, hε₀sub⟩ :=
    Metric.mem_nhds_iff.mp (hopenq.mem_nhds hqr0)
  have hrational : IsRationalCoordinateRadius V ε₀ := by
    refine ⟨hε₀, ?_⟩
    intro q hq
    have hqball : q ∈ Metric.ball (0 : ℚ) ε₀ := by
      rw [Metric.mem_ball]
      have hn : ‖q‖ = |(q : ℝ)| := by
        rw [← Rat.norm_cast_real, Real.norm_eq_abs]
      simpa only [dist_zero_right, hn] using hq
    have hmem := hε₀sub hqball
    change stageInclusion 0 (qr q) ∈ V at hmem
    change stageInclusion 0 (q, (0 : Fin 1 → ℝ)) ∈ V at hmem
    have hemb : stageRealEmbedding 0 (0 : Fin 1 → ℝ) = 0 := by
      change Finsupp.mapDomain (stageIndexEmbedding 0)
        (Finsupp.equivFunOnFinite.symm (0 : Fin 1 → ℝ)) = 0
      have hz : Finsupp.equivFunOnFinite.symm (0 : Fin 1 → ℝ) = 0 := by
        exact Finsupp.ext (fun i ↦ rfl)
      rw [hz, Finsupp.mapDomain_zero]
    rw [show stageInclusion 0 (q, (0 : Fin 1 → ℝ)) =
        (q, stageRealEmbedding 0 (0 : Fin 1 → ℝ)) by rfl, hemb] at hmem
    simpa [rationalAxis] using hmem
  refine ⟨⟨ε₀, hrational⟩, ?_⟩
  intro j hj
  let i : Fin (j + 1) := ⟨j - 1, by omega⟩
  let rr : ℝ → Stage j := fun r ↦
    (0, fun k ↦ if k = i then r else 0)
  have hrr : Continuous rr := by
    apply continuous_const.prodMk
    apply continuous_pi
    intro k
    change Continuous (fun r : ℝ ↦ if k = i then r else 0)
    by_cases hk : k = i
    · simp only [if_pos hk]
      change Continuous (id : ℝ → ℝ)
      exact continuous_id
    · simp only [if_neg hk]
      exact continuous_const
  have hrr0 : rr 0 ∈ stageInclusion j ⁻¹' V := by
    have heq : rr 0 = (0 : Stage j) := by
      ext k <;> simp [rr]
    rw [heq]
    exact hzero_stage j
  have hopenr : IsOpen (rr ⁻¹' (stageInclusion j ⁻¹' V)) :=
    (hstage j).preimage hrr
  obtain ⟨εⱼ, hεⱼ, hεⱼsub⟩ :=
    Metric.mem_nhds_iff.mp (hopenr.mem_nhds hrr0)
  refine ⟨εⱼ, hεⱼ, ?_⟩
  intro r hr
  have hrball : r ∈ Metric.ball (0 : ℝ) εⱼ := by
    change dist r 0 < εⱼ
    simpa [Real.dist_eq] using hr
  have hmem := hεⱼsub hrball
  change stageInclusion j (rr r) ∈ V at hmem
  have haxis : stageInclusion j (rr r) = realAxis j r := by
    apply Prod.ext (by rfl)
    change Finsupp.mapDomain (stageIndexEmbedding j)
      (Finsupp.equivFunOnFinite.symm (fun k ↦ if k = i then r else 0)) =
      Finsupp.single (j - 1) r
    have hsingle :
        Finsupp.equivFunOnFinite.symm (fun k ↦ if k = i then r else 0) =
          Finsupp.single i r := by
      ext k
      by_cases hk : k = i <;> simp [hk]
    rw [hsingle, Finsupp.mapDomain_single]
    rfl
  rw [haxis] at hmem
  exact hmem

/-- The self-sum hypothesis puts the mixed vector in `U`. -/
theorem mixedVector_mem_badSet_of_sum_subset
    {V : Set ColimitGroup} (hVV : V + V ⊆ badSet)
    {x₀ : ℚ} {j : ℕ} {xⱼ : ℝ}
    (hx₀ : rationalAxis x₀ ∈ V) (hxⱼ : realAxis j xⱼ ∈ V) :
    mixedVector x₀ j xⱼ ∈ badSet := by
  apply hVV
  refine ⟨rationalAxis x₀, hx₀, realAxis j xⱼ, hxⱼ, ?_⟩
  rfl

/-- The preceding assertion with the radii used in the source. -/
theorem mixedVector_mem_badSet_of_coordinate_radii
    {V : Set ColimitGroup} (hVV : V + V ⊆ badSet)
    {ε₀ εⱼ : ℝ} {x₀ : ℚ} {j : ℕ} {xⱼ : ℝ}
    (hε₀ : IsRationalCoordinateRadius V ε₀)
    (hεⱼ : IsRealCoordinateRadius V j εⱼ)
    (hx₀ : |(x₀ : ℝ)| < ε₀) (hxⱼ : |xⱼ| < εⱼ) :
    mixedVector x₀ j xⱼ ∈ badSet := by
  apply mixedVector_mem_badSet_of_sum_subset hVV
  · exact hε₀.2 x₀ hx₀
  · exact hεⱼ.2 xⱼ hxⱼ

/-- A positive radius admits a sufficiently large coordinate index. -/
theorem exists_large_coordinate_index {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ j : ℕ, 0 < j ∧ Real.pi / 2 < (j : ℝ) * ε₀ := by
  obtain ⟨j, hj⟩ := exists_nat_gt (Real.pi / (2 * ε₀))
  have hden : 0 < (2 : ℝ) * ε₀ := by positivity
  have hmul : Real.pi < (j : ℝ) * (2 * ε₀) :=
    (div_lt_iff₀ hden).mp hj
  have hjR : (0 : ℝ) < (j : ℝ) := by
    exact lt_trans (by positivity) hj
  have hjN : 0 < j := by exact_mod_cast hjR
  exact ⟨j, hjN, by nlinarith [hmul]⟩

/-- Rationals can be chosen inside the rational-coordinate interval while
making the cosine factor arbitrarily small. -/
theorem exists_rational_with_small_cosine
    {ε₀ εⱼ : ℝ} (j : ℕ) (hj : 0 < j) (hε₀ : 0 < ε₀)
    (hlarge : Real.pi / 2 < (j : ℝ) * ε₀) (hεⱼ : 0 < εⱼ) :
    ∃ x₀ : ℚ,
      |(x₀ : ℝ)| < ε₀ ∧
        |Real.cos ((j : ℝ) * (x₀ : ℝ))| < εⱼ := by
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  let a : ℝ := Real.pi / (2 * (j : ℝ))
  have ha0 : 0 < a := by
    dsimp [a]
    positivity
  have haε : a < ε₀ := by
    dsimp [a]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (j : ℝ))).2
    nlinarith [hlarge]
  have hcoscont : Continuous (fun x : ℝ ↦
      |Real.cos ((j : ℝ) * x)|) := by
    exact continuous_abs.comp
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hW : IsOpen {x : ℝ | |Real.cos ((j : ℝ) * x)| < εⱼ} := by
    exact isOpen_lt hcoscont continuous_const
  have hja : (j : ℝ) * a = Real.pi / 2 := by
    dsimp [a]
    field_simp
  have haW : a ∈ {x : ℝ | |Real.cos ((j : ℝ) * x)| < εⱼ} := by
    change |Real.cos ((j : ℝ) * a)| < εⱼ
    rw [hja]
    simpa using hεⱼ
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.mem_nhds_iff.mp (hW.mem_nhds haW)
  have hlo : max (a - δ) (-ε₀) < a := by
    apply max_lt
    · exact sub_lt_self a hδ
    · exact (neg_lt_zero.mpr hε₀).trans ha0
  have hhi : a < min (a + δ) ε₀ := by
    apply lt_min
    · linarith
    · exact haε
  obtain ⟨x₀, hxlo, hxhi⟩ := exists_rat_btwn (hlo.trans hhi)
  have hxlo' : -ε₀ < (x₀ : ℝ) :=
    (le_max_right (a - δ) (-ε₀)).trans_lt hxlo
  have hxhi' : (x₀ : ℝ) < ε₀ :=
    lt_of_lt_of_le hxhi (min_le_right (a + δ) (ε₀))
  have hxabs : |(x₀ : ℝ)| < ε₀ := (abs_lt).2 ⟨hxlo', hxhi'⟩
  have hxdiff : |(x₀ : ℝ) - a| < δ := by
    have hxlo'' : a - δ < (x₀ : ℝ) :=
      lt_of_le_of_lt (le_max_left (a - δ) (-ε₀)) hxlo
    have hxhi'' : (x₀ : ℝ) < a + δ :=
      lt_of_lt_of_le hxhi (min_le_left (a + δ) ε₀)
    apply (abs_lt).2
    constructor <;> linarith
  have hxball : (x₀ : ℝ) ∈ Metric.ball a δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact hxdiff
  have hxcos := hδsub hxball
  exact ⟨x₀, hxabs, hxcos⟩

/-- There is a real coordinate whose absolute value lies strictly between the
absolute cosine value and its prescribed radius. -/
theorem exists_real_with_abs_between
    {c ε : ℝ} (hcε : |c| < ε) :
    ∃ xⱼ : ℝ, |c| < |xⱼ| ∧ |xⱼ| < ε := by
  refine ⟨(ε + |c|) / 2, ?_, ?_⟩
  · have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg c) hcε
    have hx : 0 ≤ (ε + |c|) / 2 := by positivity
    rw [abs_of_nonneg hx]
    nlinarith [abs_nonneg c]
  · have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg c) hcε
    have hx : 0 ≤ (ε + |c|) / 2 := by positivity
    rw [abs_of_nonneg hx]
    nlinarith [abs_nonneg c]

/-- The displayed cosine choice contradicts membership in `U`. -/
theorem badSet_contradiction_of_addNeighborhoodWithSumSubset
    {V : Set ColimitGroup}
    (hV : AddNeighborhoodWithSumSubset V badSet) : False := by
  rcases hV with ⟨hVopen, h0, hVV⟩
  rcases exists_coordinate_radii_of_open_mem_zero hVopen h0 with
    ⟨⟨ε₀, hε₀⟩, hreal⟩
  rcases exists_large_coordinate_index hε₀.1 with ⟨j, hj, hlarge⟩
  rcases hreal j hj with ⟨εⱼ, hεⱼ⟩
  rcases exists_rational_with_small_cosine j hj hε₀.1 hlarge hεⱼ.1 with
    ⟨x₀, hx₀, hcos⟩
  rcases exists_real_with_abs_between hcos with ⟨xⱼ, hcos_lt, hxⱼ⟩
  have hmem := mixedVector_mem_badSet_of_coordinate_radii hVV hε₀ hεⱼ hx₀ hxⱼ
  change ∀ k : ℕ, 0 < k →
    |(mixedVector x₀ j xⱼ).2 (k - 1)| <
      |Real.cos ((k : ℝ) * (mixedVector x₀ j xⱼ).1)| at hmem
  have hineq := hmem j hj
  have hineq' : |xⱼ| < |Real.cos ((j : ℝ) * (x₀ : ℝ))| := by
    simpa [mixedVector_eq, Finsupp.single_apply] using hineq
  exact (not_lt_of_ge (le_of_lt hcos_lt)) hineq'

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

end Formalization.Books.Examples.Unit80
