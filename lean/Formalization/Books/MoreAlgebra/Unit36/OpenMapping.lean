import Formalization.Books.MoreAlgebra.Unit36.BaireCategory
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.GDelta.Basic

namespace Formalization.Books.MoreAlgebra.Unit36

open Set
open Filter

universe u

noncomputable section

private theorem openMapping_or_nowhereDense_image_aux
    {N M : Type u} [AddCommGroup N] [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [U : UniformSpace N] [IsUniformAddGroup N] [CompleteSpace N]
    [T : @IsTopologicalAddGroup N U.toTopologicalSpace inferInstance]
    (u : N →+ M) (hu : Continuous u) (hopen : ¬ IsOpenMap u)
    (hM : T2Space M)
    (hNlinear : IsLinearTopology ℤ N)
    (hNcountable : HasCountableNeighborhoodBasisAtZero N)
    (hno : ¬ ∃ N' : AddSubgroup N,
      IsOpen (N' : Set N) ∧ IsNowhereDense (u '' (N' : Set N))) : False := by
  rcases hNcountable with ⟨b, hb⟩
  have hbm : ∀ n, b n ∈ nhds (0 : N) :=
    fun n => hb.mem_iff.2 ⟨n, trivial, subset_rfl⟩
  have hexists : ∀ {s : Set N}, s ∈ nhds (0 : N) →
      ∃ H : AddSubgroup N, IsOpen (H : Set N) ∧ (H : Set N) ⊆ s := by
    intro s hs
    rcases (IsLinearTopology.hasBasis_open_submodule ℤ).mem_iff.mp hs with
      ⟨S, hS, hSs⟩
    exact ⟨S.toAddSubgroup, hS, hSs⟩
  choose H hHo hHs using fun n => hexists (hbm n)
  let V : ℕ → AddSubgroup N := fun n => ⨅ i : Finset.range (n + 1), H i
  have hVo : ∀ n, IsOpen (V n : Set N) := by
    intro n
    change IsOpen ((⨅ i : Finset.range (n + 1), H i : AddSubgroup N) : Set N)
    rw [AddSubgroup.coe_iInf]
    exact isOpen_iInter_of_finite (fun i => hHo i)
  have hVfund : ∀ s : Set N, s ∈ nhds (0 : N) →
      ∃ n, (V n : Set N) ⊆ s := by
    intro s hs
    rcases hb.mem_iff.1 hs with ⟨n, -, hbs⟩
    refine ⟨n, ?_⟩
    intro x hx
    let i : Finset.range (n + 1) := ⟨n, by simp⟩
    have hxi : x ∈ H n := by
      simpa using (iInf_le (fun j : Finset.range (n + 1) => H j) i) hx
    exact hbs (hHs n hxi)
  have hVanti : ∀ n, (V (n + 1) : Set N) ⊆ V n := by
    intro n x hx
    change x ∈ ((⨅ i : Finset.range (n + 2), H i : AddSubgroup N) : Set N) at hx
    change x ∈ ((⨅ i : Finset.range (n + 1), H i : AddSubgroup N) : Set N)
    rw [AddSubgroup.coe_iInf] at hx ⊢
    refine mem_iInter.2 (fun i => ?_)
    have hi : (i : ℕ) < n + 1 := Finset.mem_range.1 i.2
    let j : Finset.range (n + 2) :=
      ⟨(i : ℕ), Finset.mem_range.2 (Nat.lt_trans hi (Nat.lt_succ_self (n + 1)))⟩
    simpa using mem_iInter.1 hx j
  have hVle : ∀ {i j : ℕ}, i ≤ j → (V j : Set N) ⊆ V i := by
    intro i j hij
    exact Nat.le_induction
      subset_rfl (fun j _ ih => (hVanti j).trans ih) j hij
  have hVbasis : (nhds (0 : N)).HasBasis (fun _ : ℕ => True)
      (fun n => (V n : Set N)) := by
    refine ⟨fun s => ?_⟩
    constructor
    · intro hs
      rcases hVfund s hs with ⟨n, hn⟩
      exact ⟨n, trivial, hn⟩
    · rintro ⟨n, -, hn⟩
      exact Filter.mem_of_superset ((hVo n).mem_nhds (V n).zero_mem) hn
  let C : ℕ → AddSubgroup M := fun n => (V n).map u |>.topologicalClosure
  have hCclosed : ∀ n, IsClosed (C n : Set M) :=
    fun n => AddSubgroup.isClosed_topologicalClosure _
  have hCfund : ∀ W : Set M, W ∈ nhds (0 : M) →
      ∃ n, (C n : Set M) ⊆ W := by
    intro W hW
    rcases exists_mem_nhds_isClosed_subset hW with ⟨K, hK, hKclosed, hKW⟩
    have hpre : u ⁻¹' K ∈ nhds (0 : N) := by
      have hKu : K ∈ nhds (u 0) := by simpa using hK
      exact hu.continuousAt.preimage_mem_nhds hKu
    rcases hVfund (u ⁻¹' K) hpre with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change closure (u '' (V n : Set N)) ⊆ W
    exact (closure_minimal (image_subset_iff.2 (fun x hx => hn hx)) hKclosed).trans hKW
  have hCint : ∀ n, (interior (C n : Set M)).Nonempty := by
    intro n
    by_contra hn
    have hempty : interior (C n : Set M) = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hno
    refine ⟨V n, hVo n, ?_⟩
    rw [IsNowhereDense]
    simpa [C] using hempty
  have hopen_subgroup_of_interior {H : AddSubgroup M}
      (hH : (interior (H : Set M)).Nonempty) : IsOpen (H : Set M) := by
    rcases hH with ⟨x, hx⟩
    have hxH : x ∈ H := interior_subset hx
    apply AddSubgroup.isOpen_of_mem_nhds H
    have hopen : IsOpen ((fun y : M => -x + y) '' interior (H : Set M)) :=
      (isOpenMap_add_left (-x)) _ isOpen_interior
    have hzero : (0 : M) ∈ (fun y : M => -x + y) '' interior (H : Set M) := by
      exact ⟨x, hx, by simp⟩
    have hsub : (fun y : M => -x + y) '' interior (H : Set M) ⊆ (H : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      have hzH : z ∈ H := interior_subset hz
      exact H.add_mem (H.neg_mem hxH) hzH
    exact Filter.mem_of_superset (hopen.mem_nhds hzero) hsub
  have hCopen : ∀ n, IsOpen (C n : Set M) :=
    fun n => hopen_subgroup_of_interior (hCint n)
  have hdecomp : ∀ n {x : M}, x ∈ C n →
      ∃ y ∈ V n, ∃ z ∈ C (n + 1), u y + z = x := by
    intro n x hx
    let U : Set M := (fun y : M => x + y) '' (C (n + 1) : Set M)
    have hUopen : IsOpen U := by
      exact (isOpenMap_add_left x) _ (hCopen (n + 1))
    have hxU : x ∈ U := by
      exact ⟨0, (C (n + 1)).zero_mem, by simp⟩
    have hx' : x ∈ closure (u '' (V n : Set N)) := by
      change x ∈ closure (u '' (V n : Set N)) at hx
      exact hx
    rcases (mem_closure_iff.1 hx') U hUopen hxU with ⟨w, hwU, hwimage⟩
    rcases hwU with ⟨c, hc, rfl⟩
    rcases hwimage with ⟨y, hy, hzy⟩
    have hzy' : u y = x + c := by simpa using hzy
    refine ⟨y, hy, -c, (C (n + 1)).neg_mem hc, ?_⟩
    calc
      u y + -c = (x + c) + -c := by rw [hzy']
      _ = x := add_neg_cancel_right x c
  have hCle : ∀ {i j : ℕ}, i ≤ j → (C j : Set M) ⊆ C i := by
    intro i j hij
    have hv := hVle hij
    change closure (u '' (V j : Set N)) ⊆ closure (u '' (V i : Set N))
    apply closure_mono
    rintro z ⟨x, hx, rfl⟩
    exact ⟨x, hv hx, rfl⟩
  have hclosure_eq_image : ∀ n, (C n : Set M) ⊆ u '' (V n : Set N) := by
    intro n x hx
    let S : ℕ → Type u := fun k => {r : M // r ∈ C (n + k)}
    have hstep : ∀ k (r : S k), ∃ p : N × S (k + 1),
        p.1 ∈ V (n + k) ∧ u p.1 + p.2.1 = r.1 := by
      intro k r
      rcases hdecomp (n + k) r.2 with ⟨y, hy, z, hz, hzr⟩
      exact ⟨(y, ⟨z, hz⟩), hy, hzr⟩
    let step : ∀ k, S k → N × S (k + 1) :=
      fun k r => Classical.choose (hstep k r)
    have hstep_spec : ∀ k (r : S k),
        (step k r).1 ∈ V (n + k) ∧ u (step k r).1 + (step k r).2.1 = r.1 := by
      intro k r
      exact Classical.choose_spec (hstep k r)
    let state : ∀ k, S k := fun k =>
      Nat.rec (motive := S) ⟨x, by simpa using hx⟩
        (fun k r => (step k r).2) k
    let y : ℕ → N := fun k => (step k (state k)).1
    let r : ℕ → M := fun k => (state k).1
    have hy : ∀ k, y k ∈ V (n + k) := by
      intro k
      exact (hstep_spec k (state k)).1
    have hr : ∀ k, r k ∈ C (n + k) := by
      intro k
      exact (state k).2
    have hrec : ∀ k, u (y k) + r (k + 1) = r k := by
      intro k
      simpa [y, r, state] using (hstep_spec k (state k)).2
    let p : ℕ → N := Nat.rec 0 (fun k z => z + y k)
    have htail : ∀ L k l, L ≤ n + k → k ≤ l →
        p l + -p k ∈ V L := by
      intro L k l hk hkl
      refine Nat.le_induction
        (by simp [p]) (fun l _ ih => by
          have hyl : y l ∈ V L := hVle (by omega) (hy l)
          rw [show p (l + 1) = p l + y l by rfl]
          convert (V L).add_mem ih hyl using 1
          all_goals abel) l hkl
    have hpcauchy : CauchySeq p := by
      refine (hVbasis.uniformity_of_nhds_zero).cauchySeq_iff.2 ?_
      intro L hL
      refine ⟨max 0 (L - n), ?_⟩
      intro k hk l hl
      by_cases hkl : k ≤ l
      · simpa [sub_eq_add_neg] using htail L k l (by omega) hkl
      · have hlk : l ≤ k := le_of_not_ge hkl
        have h := htail L l k (by omega) hlk
        simpa [sub_eq_add_neg, add_comm] using (V L).neg_mem h
    rcases cauchySeq_tendsto_of_complete hpcauchy with ⟨y₀, hp⟩
    have hrzero : Tendsto r atTop (nhds (0 : M)) := by
      refine tendsto_def.2 ?_
      intro W hW
      rcases hCfund W hW with ⟨q, hq⟩
      filter_upwards [eventually_ge_atTop (max 0 (q - n))] with k hk
      exact hq (hCle (by omega) (hr k))
    have huP : Tendsto (fun k => u (p k)) atTop (nhds (u y₀)) := by
      simpa [Function.comp_def] using (hu.tendsto y₀).comp hp
    have hsum : Tendsto (fun k => u (p k) + r k) atTop (nhds (u y₀)) := by
      simpa using huP.add hrzero
    have hsum_eq : ∀ k, u (p k) + r k = x := by
      intro k
      induction k with
      | zero => simp [p, r, state]
      | succ k ih =>
        rw [show p (k + 1) = p k + y k by rfl, map_add]
        calc
          (u (p k) + u (y k)) + r (k + 1) =
              u (p k) + (u (y k) + r (k + 1)) := by abel
          _ = u (p k) + r k := by rw [hrec k]
          _ = x := ih
    have hsumx : Tendsto (fun k => u (p k) + r k) atTop (nhds x) := by
      rw [show (fun k => u (p k) + r k) = (fun _ : ℕ => x) by
        funext k; exact hsum_eq k]
      exact tendsto_const_nhds
    have hy0 : u y₀ = x := tendsto_nhds_unique hsum hsumx
    have hpV : ∀ k, p k ∈ V n := by
      intro k
      induction k with
      | zero => exact (V n).zero_mem
      | succ k ih =>
        rw [show p (k + 1) = p k + y k by rfl]
        exact (V n).add_mem ih (hVle (by omega) (hy k))
    have hy0V : y₀ ∈ V n := by
      exact (AddSubgroup.isClosed_of_isOpen (V n) (hVo n)).mem_of_tendsto hp
        (Eventually.of_forall hpV)
    exact ⟨y₀, hy0V, hy0⟩
  have hOpenMap : IsOpenMap u := by
    apply IsOpenMap.of_nhds_le
    intro x
    rw [← map_add_left_nhds_zero x, ← map_add_left_nhds_zero (u x),
      Filter.map_map, Function.comp_def]
    have hzero : nhds (0 : M) ≤ Filter.map u (nhds (0 : N)) := by
      intro W hW
      change u ⁻¹' W ∈ nhds (0 : N) at hW
      rcases hVfund (u ⁻¹' W) hW with ⟨n, hn⟩
      apply Filter.mem_of_superset ((hCopen n).mem_nhds (C n).zero_mem)
      intro z hz
      rcases hclosure_eq_image n hz with ⟨y, hy, rfl⟩
      exact hn hy
    convert Filter.map_mono hzero using 1
    all_goals simp [Function.comp_def, map_add]
  exact hopen hOpenMap

/-- The open-map alternative for a continuous homomorphism under the source hypotheses. -/
theorem openMapping_or_nowhereDense_image
    {N M : Type u} [AddCommGroup N] [AddCommGroup M]
    [TopologicalSpace N] [TopologicalSpace M]
    [IsTopologicalAddGroup N] [IsTopologicalAddGroup M]
    (u : N →+ M) (hu : Continuous u) (hM : T2Space M)
    (hNcomplete : IsCompleteTopologicalAddGroup N)
    (hNlinear : IsLinearTopology ℤ N)
    (hNcountable : HasCountableNeighborhoodBasisAtZero N) :
    Xor (IsOpenMap u)
      (∃ N' : AddSubgroup N,
        IsOpen (N' : Set N) ∧ IsNowhereDense (u '' (N' : Set N))) := by
  by_cases hopen : IsOpenMap u
  · left
    refine ⟨hopen, ?_⟩
    rintro ⟨N', hN'open, hN'dense⟩
    have himageopen : IsOpen (u '' (N' : Set N)) := hopen _ hN'open
    have hzero : (0 : M) ∈ u '' (N' : Set N) := ⟨0, N'.zero_mem, by simp⟩
    have hsub : u '' (N' : Set N) ⊆ interior (closure (u '' (N' : Set N))) :=
      interior_maximal subset_closure himageopen
    rw [hN'dense] at hsub
    exact hsub hzero
  · right
    refine ⟨?_, hopen⟩
    by_contra hno
    let uN : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
    have htopN : @IsTopologicalAddGroup N uN.toTopologicalSpace inferInstance := by
      simpa [uN] using (inferInstance : IsTopologicalAddGroup N)
    have hlinN : @IsLinearTopology ℤ N inferInstance inferInstance inferInstance
        uN.toTopologicalSpace := by
      simpa [uN] using hNlinear
    have hcountN : @HasCountableNeighborhoodBasisAtZero N inferInstance
        uN.toTopologicalSpace := by
      simpa [uN] using hNcountable
    have hnoN : ¬ ∃ N' : AddSubgroup N,
        @IsOpen N uN.toTopologicalSpace (N' : Set N) ∧
          @IsNowhereDense M inferInstance (u '' (N' : Set N)) := by
      simpa [uN] using hno
    have hUA : @IsUniformAddGroup N uN inferInstance := by
      simpa [uN] using
        (@isUniformAddGroup_of_addCommGroup N inferInstance inferInstance htopN)
    have hComp : @CompleteSpace N uN := by
      simpa [uN] using hNcomplete.1
    exact @openMapping_or_nowhereDense_image_aux N M inferInstance inferInstance
      inferInstance inferInstance uN hUA hComp htopN
      u hu hopen hM hlinN hcountN hnoN
end

end Formalization.Books.MoreAlgebra.Unit36
