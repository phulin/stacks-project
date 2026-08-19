import Formalization.Books.MoreAlgebra.Unit36.TopologicalGroups
import Formalization.Books.Topology.Unit29.TopologicalRings
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.UniformFilterBasis

namespace Formalization.Books.MoreAlgebra.Unit36

open Filter Set

universe u v

noncomputable section

/-- Continuous ring homomorphisms, reusing the earlier topological-ring API. -/
abbrev TopologicalRingHom (R S : Type u) [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R]
    [IsTopologicalRing S] :=
  Formalization.Books.Topology.Unit29.TopologicalRingHom (R := R) (S := S)

theorem topologicalRingHom_continuous
    (R S : Type u) [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R]
    [IsTopologicalRing S] (f : TopologicalRingHom R S) :
    Continuous f.1 := by
  exact f.2

/-- The source's unbundled topological-module condition. -/
abbrev IsTopologicalModule (R : Type u) (M : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace M]
    [AddCommGroup M] [Module R M] :=
  ContinuousAdd M ∧ ContinuousSMul R M

/-- The ideal formulation of a linear topology on a ring. -/
theorem linearlyTopologizedRing_iff_hasBasis_ideal
    (R : Type u) [CommRing R] [TopologicalSpace R] :
    IsLinearTopology R R ↔
      (nhds (0 : R)).HasBasis
        (fun I : Ideal R => (I : Set R) ∈ nhds (0 : R))
        (fun I : Ideal R => (I : Set R)) := by
  exact isLinearTopology_iff_hasBasis_ideal

theorem linearlyTopologizedRing_hasBasis_open_ideal
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] :
    (nhds (0 : R)).HasBasis
      (fun I : Ideal R => IsOpen (I : Set R))
      (fun I : Ideal R => (I : Set R)) := by
  exact IsLinearTopology.hasBasis_open_ideal

/-- An ideal of definition for the given topology on a commutative topological ring. -/
def IsIdealOfDefinition (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (I : Ideal R) : Prop :=
  IsOpen (I : Set R) ∧
    ∀ U ∈ nhds (0 : R), ∃ n : ℕ, ((I ^ n : Ideal R) : Set R) ⊆ U

/-- A pre-admissible topological ring has an ideal of definition. -/
def IsPreAdmissibleTopologicalRing (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] : Prop :=
  ∃ I : Ideal R, IsIdealOfDefinition R I

/-- An admissible topological ring is pre-admissible and complete separated. -/
def IsAdmissibleTopologicalRing (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] : Prop :=
  IsPreAdmissibleTopologicalRing R ∧ IsCompleteTopologicalAddGroup R

/-- A pre-adic topological ring has powers of one ideal as a neighborhood basis. -/
def IsPreAdicTopologicalRing (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] : Prop :=
  ∃ I : Ideal R,
    IsIdealOfDefinition R I ∧
      (nhds (0 : R)).HasBasis (fun _ : ℕ => True)
        (fun n => ((I ^ n : Ideal R) : Set R))

/-- An adic topological ring is pre-adic and complete separated. -/
def IsAdicTopologicalRing (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] : Prop :=
  IsPreAdicTopologicalRing R ∧ IsCompleteTopologicalAddGroup R

theorem isPreAdicTopologicalRing_iff_ideal_powers_open
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] :
    IsPreAdicTopologicalRing R ↔
      ∃ I : Ideal R,
        IsIdealOfDefinition R I ∧
          ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n : Ideal R) : Set R) := by
  constructor
  · rintro ⟨I, hI, hbasis⟩
    have hpow_mem : ∀ n : ℕ, ((I ^ n : Ideal R) : Set R) ∈ nhds (0 : R) := by
      intro n
      exact hbasis.mem_iff.mpr ⟨n, trivial, subset_rfl⟩
    have hpow_open : ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n : Ideal R) : Set R) := by
      intro n hn
      exact (I ^ n).toAddSubgroup.isOpen_of_mem_nhds (hpow_mem n)
    have hIopen : IsOpen (I : Set R) := by
      simpa using hpow_open 1 (by omega)
    refine ⟨I, ?_, hpow_open⟩
    refine ⟨hIopen, ?_⟩
    intro U hU
    obtain ⟨n, hn, hnU⟩ := hbasis.mem_iff.mp hU
    exact ⟨n, hnU⟩
  · intro h
    obtain ⟨I, hI, hopen⟩ := h
    refine ⟨I, hI, ?_⟩
    refine ⟨fun U => ?_⟩
    constructor
    · intro hU
      obtain ⟨n, hn⟩ := hI.2 U hU
      exact ⟨n, trivial, hn⟩
    · intro h
      obtain ⟨n, htrivial, hnU⟩ := h
      have hmem : ((I ^ n : Ideal R) : Set R) ∈ nhds (0 : R) := by
        cases n with
        | zero =>
            simp
        | succ n =>
            exact (hopen (n + 1) (by omega)).mem_nhds (Ideal.zero_mem _)
      exact Filter.mem_of_superset hmem hnU

theorem isAdicTopologicalRing_iff_ideal_powers_open
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] :
    IsAdicTopologicalRing R ↔
      ∃ I : Ideal R,
        IsIdealOfDefinition R I ∧
          (∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n : Ideal R) : Set R)) ∧
            IsCompleteTopologicalAddGroup R := by
  constructor
  · intro h
    obtain ⟨hpre, hcomplete⟩ := h
    obtain ⟨I, hI, hopen⟩ :=
      (isPreAdicTopologicalRing_iff_ideal_powers_open R).mp hpre
    exact ⟨I, hI, hopen, hcomplete⟩
  · rintro ⟨I, hI, hopen, hcomplete⟩
    exact ⟨(isPreAdicTopologicalRing_iff_ideal_powers_open R).mpr
      ⟨I, hI, hopen⟩, hcomplete⟩

theorem isPreAdicTopologicalRing_iff_preAdmissible_and_powers_open
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] :
    IsPreAdicTopologicalRing R ↔
      IsPreAdmissibleTopologicalRing R ∧
        ∃ I : Ideal R,
          IsIdealOfDefinition R I ∧
            ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n : Ideal R) : Set R) := by
  constructor
  · intro h
    obtain ⟨I, hI, hopen⟩ :=
      (isPreAdicTopologicalRing_iff_ideal_powers_open R).mp h
    exact ⟨⟨I, hI⟩, ⟨I, hI, hopen⟩⟩
  · rintro ⟨hpre, ⟨I, hI, hopen⟩⟩
    exact (isPreAdicTopologicalRing_iff_ideal_powers_open R).mpr
      ⟨I, hI, hopen⟩

theorem isAdicTopologicalRing_iff_admissible_and_powers_open
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] :
    IsAdicTopologicalRing R ↔
      IsAdmissibleTopologicalRing R ∧
        ∃ I : Ideal R,
          IsIdealOfDefinition R I ∧
            ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n : Ideal R) : Set R) := by
  constructor
  · rintro ⟨hpre, hcomplete⟩
    obtain ⟨hpreAdmissible, hI⟩ :=
      (isPreAdicTopologicalRing_iff_preAdmissible_and_powers_open R).mp hpre
    exact ⟨⟨hpreAdmissible, hcomplete⟩, hI⟩
  · rintro ⟨⟨hpreAdmissible, hcomplete⟩, hI⟩
    exact ⟨(isPreAdicTopologicalRing_iff_preAdmissible_and_powers_open R).mpr
      ⟨hpreAdmissible, hI⟩, hcomplete⟩

/-- The canonical Mathlib topology attached to an ideal on a ring. -/
abbrev IAdicRingTopology (R : Type u) [CommRing R] (I : Ideal R) : TopologicalSpace R :=
  I.adicTopology

/-- The canonical Mathlib topology attached to an ideal on a module. -/
abbrev IAdicModuleTopology (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] : TopologicalSpace M :=
  I.adicModuleTopology M

theorem iAdicRingTopology_hasBasis (R : Type u) [CommRing R] (I : Ideal R) :
    (@nhds R I.adicTopology (0 : R)).HasBasis (fun _ : ℕ => True)
      (fun n => ((I ^ n : Ideal R) : Set R)) := by
  exact @Ideal.hasBasis_nhds_zero_adic R _ I

theorem iAdicRingTopology_is_linear (R : Type u) [CommRing R] (I : Ideal R) :
    @IsLinearTopology R R _ _ _ I.adicTopology := by
  exact I.isLinearTopology

theorem iAdicRingTopology_powers_open (R : Type u) [CommRing R] (I : Ideal R) :
    ∀ n : ℕ, 1 ≤ n →
      @IsOpen R I.adicTopology ((I ^ n : Ideal R) : Set R) := by
  let : TopologicalSpace R := I.adicTopology
  intro n hn
  exact (I ^ n).toAddSubgroup.isOpen_of_mem_nhds
    (I.hasBasis_nhds_zero_adic.mem_iff.mpr ⟨n, trivial, subset_rfl⟩)

theorem iAdicModuleTopology_hasBasis
    (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    (@nhds M (I.adicModuleTopology M) (0 : M)).HasBasis
      (fun _ : ℕ => True)
      (fun n => ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M)) := by
  let _ : TopologicalSpace R := I.adicTopology
  refine ⟨by
    intro U
    rw [(I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨n, rfl⟩, h⟩
      exact ⟨n, trivial, h⟩
    · rintro ⟨n, -, h⟩
      exact ⟨(I ^ n • (⊤ : Submodule R M) : Submodule R M), ⟨n, rfl⟩, h⟩⟩

theorem iAdicModuleTopology_is_topological_module
    (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    let _ : TopologicalSpace R := I.adicTopology
    let _ : TopologicalSpace M := I.adicModuleTopology M
    let _ : NonarchimedeanRing R := I.nonarchimedean
    IsTopologicalModule R M := by
  dsimp
  let _ : TopologicalSpace R := I.adicTopology
  let _ : TopologicalSpace M := I.adicModuleTopology M
  let _ : NonarchimedeanRing R := I.nonarchimedean
  exact ⟨(I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).isTopologicalAddGroup.toContinuousAdd,
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).continuousSMul⟩

theorem iAdicTopology_is_preAdic (R : Type u) [CommRing R] (I : Ideal R) :
    let _ : TopologicalSpace R := I.adicTopology
    let _ : NonarchimedeanRing R := I.nonarchimedean
    let _ : IsLinearTopology R R := I.isLinearTopology
    IsPreAdicTopologicalRing R := by
  dsimp
  refine ⟨I, ?_, ?_⟩
  · constructor
    · simpa using iAdicRingTopology_powers_open R I 1 (by omega)
    · intro U hU
      obtain ⟨n, -, hnU⟩ := (iAdicRingTopology_hasBasis R I).mem_iff.mp hU
      exact ⟨n, hnU⟩
  · exact iAdicRingTopology_hasBasis R I

theorem isAdicComplete_iff_complete_for_iAdicRingTopology
    (R : Type u) [CommRing R] (I : Ideal R) :
    IsAdicComplete I R ↔
      IsCompleteSeparatedTopologicalAddGroupFor R I.adicTopology := by
  let _ : TopologicalSpace R := I.adicTopology
  let _ : NonarchimedeanRing R := I.nonarchimedean
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let _ : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  have hI : IsAdic I := rfl
  constructor
  · intro h
    have hcomplete := (IsAdic.isAdicComplete_iff (R := R) (I := I) hI).mp h
    exact ⟨IsTopologicalAddGroup.rightUniformSpace R, rfl, inferInstance,
      hcomplete.1, hcomplete.2⟩
  · rintro ⟨u, hu, hu_uniform, hcomplete, ht2⟩
    let _ : UniformSpace R := u
    let _ : TopologicalSpace R := u.toTopologicalSpace
    let _ : IsUniformAddGroup R := hu_uniform
    have hI' : IsAdic I := hu
    apply (IsAdic.isAdicComplete_iff (R := R) (I := I) hI').mpr
    refine ⟨hcomplete, ?_⟩
    rw [← hu] at ht2
    exact ht2

theorem isAdicComplete_iff_complete_for_iAdicModuleTopology
    (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsAdicComplete I M ↔
      IsCompleteSeparatedTopologicalAddGroupFor M (I.adicModuleTopology M) := by
  let _ : TopologicalSpace R := I.adicTopology
  let B := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis
  let u : UniformSpace M := B.uniformSpace
  constructor
  · intro h
    have hu_top : u.toTopologicalSpace = I.adicModuleTopology M := by
      change B.topology = _
      rfl
    let _ : TopologicalSpace M := I.adicModuleTopology M
    let _ : UniformSpace M := u
    let _ : IsUniformAddGroup M := B.isUniformAddGroup
    have := (iAdicModuleTopology_hasBasis R I M).isCountablyGenerated
    have : (uniformity M).IsCountablyGenerated :=
      IsUniformAddGroup.uniformity_countably_generated
    refine ⟨u, hu_top, B.isUniformAddGroup, ?_, ?_⟩
    · refine UniformSpace.complete_of_cauchySeq_tendsto fun f hf ↦ ?_
      have hc := (iAdicModuleTopology_hasBasis R I M).uniformity_of_nhds_zero.cauchySeq_iff.mp hf
      have hdiff : ∀ i, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
          f n - f m ∈ I ^ i • (⊤ : Submodule R M) := by
        simpa [SModEq.sub_mem] using hc
      choose N hN using hdiff
      let g : ℕ → M := fun i => f ((Finset.Iic i).sup N)
      have hg : ∀ {m n}, m ≤ n → g m ≡ g n [SMOD (I ^ m • (⊤ : Submodule R M))] := by
        intro m n hmn
        apply SModEq.sub_mem.mpr
        have hmN : N m ≤ (Finset.Iic m).sup N :=
          Finset.le_sup (show m ∈ Finset.Iic m by simp)
        have hnN : N m ≤ (Finset.Iic n).sup N :=
          Finset.le_sup (show m ∈ Finset.Iic n by simpa using hmn)
        simpa [g] using (Submodule.neg_mem _ (hN m _ hmN _ hnN))
      obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' g hg
      use L
      have hnb := (iAdicModuleTopology_hasBasis R I M).map (fun y : M => L + y)
      rw [map_add_left_nhds_zero L] at hnb
      suffices ∀ i, ∃ N, ∀ n, N ≤ n →
          f n - L ∈ I ^ i • (⊤ : Submodule R M) by
        simpa [hnb.tendsto_right_iff, sub_eq_neg_add]
      intro i
      refine ⟨(Finset.Iic i).sup N, ?_⟩
      intro n hn
      have hiN : N i ≤ (Finset.Iic i).sup N :=
        Finset.le_sup (show i ∈ Finset.Iic i by simp)
      have h₁ := hN i ((Finset.Iic i).sup N) hiN n (hiN.trans hn)
      have h₂ := SModEq.sub_mem.mp (hL i)
      have h₃ := Submodule.add_mem (I ^ i • (⊤ : Submodule R M)) h₁ h₂
      simpa [g] using h₃
    · rw [B.t2Space_iff_sInter_subset rfl]
      intro x hx
      have hxpow : ∀ n, x ∈ I ^ n • (⊤ : Submodule R M) := by
        intro n
        apply hx
        change ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M) ∈ B.sets
        change ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M) ∈ B.toFilterBasis.sets
        unfold B
        exact ⟨n, rfl⟩
      have hxzero : x = 0 := h.haus x (fun n => SModEq.zero.2 (hxpow n))
      simpa [hxzero]
  · rintro ⟨u, hu, hu_uniform, hcomplete, ht2⟩
    let _ : UniformSpace M := u
    let _ : TopologicalSpace M := u.toTopologicalSpace
    let _ : IsUniformAddGroup M := hu_uniform
    let _ : CompleteSpace M := hcomplete
    have hbasis : (@nhds M u.toTopologicalSpace (0 : M)).HasBasis
        (fun _ : ℕ => True)
        (fun n => ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M)) := by
      rw [hu]
      exact iAdicModuleTopology_hasBasis R I M
    have hBtop : B.topology = I.adicModuleTopology M := by
      rfl
    have ht2B : @T2Space M B.topology := by
      rw [hBtop]
      exact ht2
    refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
    · refine ⟨?_⟩
      have ht2B' : ⋂₀ B.sets ⊆ ({0} : Set M) :=
        (B.t2Space_iff_sInter_subset (t := B.topology) rfl).mp ht2B
      intro x hx
      apply ht2B'
      intro V hV
      unfold B at hV
      rcases hV with ⟨n, rfl⟩
      exact SModEq.zero.mp (hx n)
    · refine ⟨?_⟩
      intro f hf
      obtain ⟨L, hL⟩ := CompleteSpace.complete (f := Filter.atTop.map f)
        (hbasis.uniformity_of_nhds_zero.cauchySeq_iff.mpr fun i _ ↦
          ⟨i, fun m hm n hn ↦ by
            have hmem := Submodule.sub_mem _ (SModEq.sub_mem.mp (hf hm))
              (SModEq.sub_mem.mp (hf hn))
            change f n - f m ∈ I ^ i • (⊤ : Submodule R M)
            convert hmem using 1 <;> abel⟩)
      refine ⟨L, ?_⟩
      have hnb := hbasis.map (fun y : M => L + y)
      rw [map_add_left_nhds_zero L] at hnb
      intro i
      apply SModEq.sub_mem.mpr
      obtain ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n →
          f n - L ∈ I ^ i • (⊤ : Submodule R M) := by
        simpa [sub_eq_neg_add] using (hnb.tendsto_right_iff.mp hL i)
      have h₁ := hN (max i N) le_sup_right
      have h₂ := SModEq.sub_mem.mp (hf (le_max_left i N))
      have h₃ := Submodule.add_mem (I ^ i • (⊤ : Submodule R M)) h₁ h₂
      simpa [sub_add_sub_cancel] using h₃

theorem iAdicTopology_is_adic_of_complete
    (R : Type u) [CommRing R] (I : Ideal R) (hI : IsAdicComplete I R) :
    let _ : TopologicalSpace R := I.adicTopology
    let _ : NonarchimedeanRing R := I.nonarchimedean
    let _ : IsLinearTopology R R := I.isLinearTopology
    IsAdicTopologicalRing R := by
  dsimp
  refine ⟨iAdicTopology_is_preAdic R I, ?_⟩
  let _ : TopologicalSpace R := I.adicTopology
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let _ : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  exact (IsAdic.isAdicComplete_iff (R := R) (I := I) (by rfl)).mp hI

theorem iAdicTopology_is_adic_iff_isAdicComplete
    (R : Type u) [CommRing R] (I : Ideal R) :
    IsAdicComplete I R ↔
      (let _ : TopologicalSpace R := I.adicTopology
       let _ : NonarchimedeanRing R := I.nonarchimedean
       let _ : IsLinearTopology R R := I.isLinearTopology
       IsAdicTopologicalRing R) := by
  constructor
  · intro h
    exact iAdicTopology_is_adic_of_complete R I h
  · intro h
    dsimp at h
    let _ : TopologicalSpace R := I.adicTopology
    let _ : NonarchimedeanRing R := I.nonarchimedean
    let _ : IsLinearTopology R R := I.isLinearTopology
    let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
    let _ : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
    apply (isAdicComplete_iff_complete_for_iAdicRingTopology R I).mpr
    refine ⟨IsTopologicalAddGroup.rightUniformSpace R, rfl, inferInstance, ?_, ?_⟩
    · exact h.2.1
    · exact h.2.2

/-- The inverse-limit topology used for the completion warning in the text. -/
@[instance_reducible]
def AdicCompletionLimitTopology (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    TopologicalSpace (AdicCompletion I M) :=
  ⨅ n : ℕ, TopologicalSpace.induced
    (fun x : AdicCompletion I M => x.val n)
    (⊥ : TopologicalSpace (M ⧸ (I ^ n • (⊤ : Submodule R M))))

theorem adicCompletion_complete_for_limit_topology
    (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsCompleteSeparatedTopologicalAddGroupFor (AdicCompletion I M)
      (AdicCompletionLimitTopology R I M) := by
  classical
  let C := AdicCompletion I M
  let Q : ℕ → Type v := fun n => M ⧸ (I ^ n • (⊤ : Submodule R M))
  let g : C →+ ∀ n : ℕ, Q n :=
    { toFun := fun x n => x.val n
      map_zero' := by
        ext n
        simp
      map_add' := by
        intro x y
        ext n
        exact AdicCompletion.val_add_apply x y n }
  let : ∀ n : ℕ, TopologicalSpace (Q n) := fun _ => ⊥
  let : ∀ n : ℕ, UniformSpace (Q n) := fun _ => ⊥
  let : ∀ n : ℕ, DiscreteTopology (Q n) :=
    fun _ => discreteTopology_bot _
  let u : UniformSpace C := UniformSpace.comap g
    (inferInstance : UniformSpace (∀ n : ℕ, Q n))
  let : UniformSpace C := u
  have hu : IsUniformAddGroup C := by
    refine ⟨?_⟩
    apply uniformContinuous_comap' (f := (g : C → ∀ n : ℕ, Q n))
    convert
      (uniformContinuous_sub.comp
        (((uniformContinuous_comap (f := (g : C → ∀ n : ℕ, Q n))).comp
            uniformContinuous_fst).prodMk
          ((uniformContinuous_comap (f := (g : C → ∀ n : ℕ, Q n))).comp
            uniformContinuous_snd))) using 1
    ext p
    simp [map_sub]
  let : IsUniformAddGroup C := hu
  have htop : u.toTopologicalSpace = AdicCompletionLimitTopology R I M := by
    change TopologicalSpace.induced g Pi.topologicalSpace = _
    rw [induced_to_pi]
    rfl
  have hinj : Function.Injective g := by
    intro x y hxy
    apply AdicCompletion.ext
    intro n
    exact congrFun hxy n
  let S : Set (∀ n : ℕ, Q n) :=
    ⋂ (i : ℕ) (j : ℕ) (h : i ≤ j),
      {z | AdicCompletion.transitionMap I M h (z j) = z i}
  have hgrange : Set.range g = S := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      simp only [S, Set.mem_iInter]
      intro i j h
      exact x.prop h
    · intro hz
      simp only [S, Set.mem_iInter] at hz
      refine ⟨⟨z, ?_⟩, ?_⟩
      · intro i j h
        exact hz i j h
      · rfl
  have hSclosed : IsClosed S := by
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro h
    let : ∀ n : ℕ, T2Space (Q n) := fun _ => by
      infer_instance
    apply isClosed_eq
    · exact (continuous_of_discreteTopology :
        Continuous (AdicCompletion.transitionMap I M h : Q j → Q i)).comp
          (continuous_apply j)
    · exact continuous_apply i
  have hprod : CompleteSpace (∀ n : ℕ, Q n) := by
    infer_instance
  let : CompleteSpace (∀ n : ℕ, Q n) := hprod
  have hrange : IsComplete (Set.range g) := by
    rw [hgrange]
    exact hSclosed.isComplete
  have hcomplete : @CompleteSpace C u :=
    (completeSpace_iff_isComplete_range ⟨rfl⟩).2 hrange
  let : TopologicalSpace C := u.toTopologicalSpace
  have hT2 : @T2Space C (AdicCompletionLimitTopology R I M) := by
    rw [← htop]
    exact T2Space.of_injective_continuous hinj
      (uniformContinuous_comap (f := (g : C → ∀ n : ℕ, Q n))).continuous
  refine ⟨u, htop, hu, hcomplete, hT2⟩

theorem adicCompletion_not_always_iAdically_complete :
    ¬ ∀ (R : Type u) [CommRing R] (I : Ideal R)
      (M : Type v) [AddCommGroup M] [Module R M],
      IsAdicComplete I (AdicCompletion I M) := by
  sorry

theorem adicCompletion_isAdicComplete_of_fg
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsAdicComplete I (AdicCompletion I M) := by
  exact AdicCompletion.isAdicComplete hI

theorem adicCompletion_iAdicTopology_eq_limitTopology_of_fg
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : Type v) [AddCommGroup M] [Module R M] :
    I.adicModuleTopology (AdicCompletion I M) =
      AdicCompletionLimitTopology R I M := by
  sorry

theorem zero_adic_iff_discrete
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsAdic (⊥ : Ideal R) ↔ DiscreteTopology R := by
  exact is_bot_adic_iff

theorem discrete_ring_is_adicTopologicalRing (R : Type u) [CommRing R] :
    let _ : TopologicalSpace R := ⊥
    let _ : DiscreteTopology R := discreteTopology_bot R
    let _ : IsTopologicalRing R :=
      { continuous_add := continuous_of_discreteTopology
        continuous_mul := continuous_of_discreteTopology
        continuous_neg := continuous_of_discreteTopology }
    let _ : IsLinearTopology R R := by infer_instance
    IsAdicTopologicalRing R := by
  sorry

/-- Continuity of a ring map between adic topologies is measured by one power. -/
theorem continuous_ringHom_iff_iAdic_power_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (φ : R →+* S) :
    @Continuous R S I.adicTopology J.adicTopology φ ↔
      ∃ n : ℕ, 1 ≤ n ∧ Ideal.map φ (I ^ n) ≤ J := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit36
