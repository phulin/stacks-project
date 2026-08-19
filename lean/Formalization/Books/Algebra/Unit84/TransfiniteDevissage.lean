import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Commutative Algebra, Chapter 84: Transfinite dévissage of modules

The source indexes a continuous increasing filtration by an ordinal.  The
filtration is represented by submodules, direct summands by Mathlib's
`IsComplemented`, and successive quotients by the canonical submodule
quotient.  Countable generation is exposed as the existence of a countable
set whose span is the whole module.
-/

namespace Formalization.Books.Algebra.Unit84

open DirectSum

universe u v w

noncomputable section

/-! ## Countable generation and ordinal filtrations -/

/-- A module is countably generated when it has a countable spanning set. -/
def Module.IsCountablyGenerated
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤

/-- The indices of the successive quotients in a filtration indexed by `S`. -/
def SuccessorIndex (S : Ordinal.{w}) :=
  {α : Ordinal.{w} // α + 1 < S}

private def successorIndexEquiv (S : Ordinal.{w}) :
    {i : S.ToType // (i : Ordinal) + 1 < S} ≃ SuccessorIndex S := by
  let e : {i : S.ToType // (i : Ordinal) + 1 < S} ≃ SuccessorIndex S :=
    { toFun := fun i => ⟨i.1, i.2⟩
      invFun := fun α =>
        let hα : α.1 < S :=
          by
            have hlt : α.1 < α.1 + 1 := by
              simpa only [Order.succ_eq_add_one] using Order.lt_succ α.1
            exact hlt.trans α.2
        ⟨Ordinal.ToType.mk ⟨α.1, hα⟩, by simpa using α.2⟩
      left_inv := by
        intro i
        apply Subtype.ext
        simpa only using (Ordinal.ToType.mk.apply_symm_apply i.1)
      right_inv := by
        intro α
        apply Subtype.ext
        simp }
  exact e

/- The ordinal successor is definitionally the operation `α + 1` in the
ordinal API, but the generic `lt_add_one` lemma requires a monotonicity
instance which ordinal addition does not provide. -/
theorem ordinal_lt_add_one (α : Ordinal.{w}) : α < α + 1 := by
  simpa only [Order.succ_eq_add_one] using (Order.lt_succ α)

/-- The data of an increasing, continuous ordinal filtration of a module. -/
structure IncreasingDevissage
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Ordinal.{w}) where
  /-- The submodule at each ordinal strictly below `S`. -/
  stage : Set.Iio S → Submodule R M
  /-- The filtration is increasing. -/
  monotone : Monotone stage
  /-- The index set contains the initial stage. -/
  zero_lt : 0 < S
  /-- The initial stage is zero. -/
  zero : stage ⟨0, zero_lt⟩ = ⊥
  /-- The union of the stages is the whole module. -/
  union_eq_top : ⨆ α : Set.Iio S, stage α = ⊤
  /-- A limit stage is the union of its earlier stages. -/
  limit :
    ∀ (α : Set.Iio S), Order.IsSuccLimit α.1 →
      stage α = ⨆ β : Set.Iio α.1,
        stage ⟨β.1, by
          change β.1 < S
          exact β.2.trans α.2⟩

/-- The submodule of the successor stage corresponding to its predecessor. -/
def IncreasingDevissage.successorSubmodule
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S)
    (α : SuccessorIndex S) : Submodule R (D.stage ⟨α.1 + 1, α.2⟩) :=
  (D.stage ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩).comap
    (D.stage ⟨α.1 + 1, α.2⟩).subtype

/-- The successive quotient at a successor index. -/
abbrev IncreasingDevissage.successorQuotient
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S)
    (α : SuccessorIndex S) : Type _ :=
  (D.stage ⟨α.1 + 1, α.2⟩) ⧸ D.successorSubmodule α

/-- All successor inclusions in an increasing dévissage split. -/
def IncreasingDevissage.isSuccessorComplemented
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S) : Prop :=
  ∀ α : SuccessorIndex S, IsComplemented (D.successorSubmodule α)

/-- Every stage is a direct summand of the ambient module. -/
def IncreasingDevissage.isAmbientlyComplemented
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S) : Prop :=
  ∀ α : Set.Iio S, IsComplemented (D.stage α)

local instance (priority := low) successorIndexDecidableEq {S : Ordinal.{w}} :
    DecidableEq (SuccessorIndex S) := Classical.decEq _

local instance (priority := low) successorIndexLinearOrder {S : Ordinal.{w}} :
    LinearOrder (SuccessorIndex S) :=
  LinearOrder.lift' (fun α : SuccessorIndex S => α.1) Subtype.val_injective

private theorem increasingDevissage_isInternal_of_isSuccessorComplemented
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S)
    (h : D.isSuccessorComplemented) :
    DirectSum.IsInternal (fun α : SuccessorIndex S =>
      (Classical.choose (show ∃ Q, IsCompl (D.successorSubmodule α) Q from h α)).map
        (D.stage ⟨α.1 + 1, α.2⟩).subtype) := by
  classical
  let C : ∀ α : SuccessorIndex S,
      Submodule R (D.stage ⟨α.1 + 1, α.2⟩) :=
    fun α => Classical.choose (show ∃ Q, IsCompl (D.successorSubmodule α) Q from h α)
  let E : SuccessorIndex S → Submodule R M :=
    fun α => (C α).map (D.stage ⟨α.1 + 1, α.2⟩).subtype
  change DirectSum.IsInternal E
  have hC (α : SuccessorIndex S) :
      IsCompl (D.successorSubmodule α) (C α) :=
    Classical.choose_spec (show ∃ Q, IsCompl (D.successorSubmodule α) Q from h α)
  have hle (α : SuccessorIndex S) :
      D.stage ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩ ≤
        D.stage ⟨α.1 + 1, α.2⟩ := by
    apply D.monotone
    exact (ordinal_lt_add_one α.1).le
  have hdis (α : SuccessorIndex S) :
      Disjoint (E α) (D.stage ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩) := by
    have hk : LinearMap.ker (D.stage ⟨α.1 + 1, α.2⟩).subtype ≤
        D.successorSubmodule α := by simp
    have hd := Submodule.disjoint_map_of_ker_le_right
      (hC α).disjoint.symm hk
    change Disjoint ((C α).map (D.stage ⟨α.1 + 1, α.2⟩).subtype)
      (D.stage ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩)
    rw [show D.successorSubmodule α =
        (D.stage ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩).comap
          (D.stage ⟨α.1 + 1, α.2⟩).subtype from rfl,
      Submodule.map_comap_subtype, inf_of_le_right (hle α)] at hd
    exact hd
  have hE_le (α β : SuccessorIndex S) (hab : α < β) : E α ≤
      D.stage ⟨β.1, (ordinal_lt_add_one β.1).trans β.2⟩ := by
    exact (Submodule.map_subtype_le _ _).trans <| D.monotone <|
      show (⟨α.1 + 1, α.2⟩ : Set.Iio S) ≤
          ⟨β.1, (ordinal_lt_add_one β.1).trans β.2⟩ from
        (show α.1 + 1 ≤ β.1 from by
          simpa only [Order.succ_eq_add_one] using
            (Order.succ_le_of_lt (show α.1 < β.1 from hab)))
  have hindep : iSupIndep E := by
    apply iSupIndep_of_dfinsupp_lsum_injective E
    intro f g hfg
    by_contra hne
    let s := (f - g).support
    have hs : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hs0
      apply hne
      ext α
      have hnot : α ∉ (f - g).support := by simp [s, hs0]
      have hzeroDF : (f - g) α = 0 := by
        by_contra hne0
        exact hnot (DFinsupp.mem_support_iff.mpr hne0)
      have hzero : f α - g α = 0 := by
        simpa only [DFinsupp.sub_apply] using hzeroDF
      have hzero' : (f α : M) - (g α : M) = 0 := by
        simpa using congrArg (fun z : E α => (z : M)) hzero
      exact sub_eq_zero.mp hzero'
    let β := s.max' hs
    have hβmem : β ∈ s := Finset.max'_mem s hs
    have hβne : (f - g) β ≠ 0 := by
      exact DFinsupp.mem_support_iff.mp hβmem
    have hrest :
        DFinsupp.lsum ℕ (fun α => (E α).subtype) ((f - g).erase β) ∈
          D.stage ⟨β.1, (ordinal_lt_add_one β.1).trans β.2⟩ := by
      rw [DFinsupp.lsum_apply_apply]
      apply Submodule.dfinsuppSumAddHom_mem
      intro α hα
      have hαs : α ∈ s := by
        have hαne : α ≠ β := by
          intro heq
          subst α
          simp at hα
        exact DFinsupp.mem_support_iff.mpr (by
          simpa [DFinsupp.erase_apply, hαne] using hα)
      have hαle : α ≤ β := Finset.le_max' s α hαs
      have hαlt : α < β := lt_of_le_of_ne hαle (by
        intro heq
        apply hβne
        simp [heq] at hα)
      exact hE_le α β hαlt ((f - g).erase β α).property
    have hsum :
        DFinsupp.lsum ℕ (fun α => (E α).subtype) ((f - g).erase β) +
          (E β).subtype ((f - g) β) = 0 := by
      calc
        _ = DFinsupp.lsum ℕ (fun α => (E α).subtype)
            ((f - g).erase β + DFinsupp.single β ((f - g) β)) := by
          rw [map_add, DFinsupp.lsum_single]
        _ = DFinsupp.lsum ℕ (fun α => (E α).subtype) (f - g) := by
          rw [DFinsupp.erase_add_single]
        _ = 0 := by rw [map_sub, hfg]; simp
    have hmem : (E β).subtype ((f - g) β) ∈
        D.stage ⟨β.1, (ordinal_lt_add_one β.1).trans β.2⟩ := by
      rw [eq_neg_of_add_eq_zero_right hsum]
      exact (D.stage ⟨β.1, (ordinal_lt_add_one β.1).trans β.2⟩).neg_mem hrest
    have hzero : (f - g) β = 0 := by
      apply Subtype.ext
      exact Submodule.disjoint_def.mp (hdis β) _
        ((f - g) β).property hmem
    exact hβne hzero
  have htop : iSup E = ⊤ := by
    have hstage : ∀ α : Ordinal.{w}, ∀ hα : α < S,
        D.stage ⟨α, hα⟩ ≤ iSup E := by
      intro α
      induction α using SuccOrder.limitRecOn with
      | isMin α hα =>
          obtain rfl := hα.eq_bot
          intro hα
          have hstage0 : D.stage ⟨0, hα⟩ = ⊥ := by simpa using D.zero
          change D.stage ⟨0, hα⟩ ≤ _
          rw [hstage0]
          exact bot_le
      | succ α hα ih =>
          intro hα
          have hαs : α + 1 < S := by simpa only [Order.succ_eq_add_one] using hα
          have hα' : α < S := (ordinal_lt_add_one α).trans hαs
          have hp := ih hα'
          have he : E ⟨α, hαs⟩ ≤ iSup E := le_iSup E ⟨α, hαs⟩
          have hs :
              D.stage ⟨α + 1, hαs⟩ =
                D.stage ⟨α, hα'⟩ ⊔ E ⟨α, hαs⟩ := by
            apply le_antisymm
            · rw [← Submodule.map_subtype_top (D.stage ⟨α + 1, hαs⟩)]
              rw [← (hC ⟨α, hαs⟩).sup_eq_top, Submodule.map_sup]
              simp [E, C, IncreasingDevissage.successorSubmodule,
                inf_of_le_right (D.monotone (show
                  (⟨α, hα'⟩ : Set.Iio S) ≤
                    ⟨α + 1, hαs⟩ from (ordinal_lt_add_one α).le))]
            · have hprev : D.stage ⟨α, hα'⟩ ≤ D.stage ⟨α + 1, hαs⟩ :=
                D.monotone (show
                  (⟨α, hα'⟩ : Set.Iio S) ≤
                    ⟨α + 1, hαs⟩ from (ordinal_lt_add_one α).le)
              exact sup_le hprev (Submodule.map_subtype_le _ _)
          have hs' : D.stage ⟨Order.succ α, hα⟩ =
                D.stage ⟨α, hα'⟩ ⊔ E ⟨α, hαs⟩ := by
            simpa only [Order.succ_eq_add_one] using hs
          rw [hs']
          exact sup_le hp he
      | isSuccLimit α hlim ih =>
          intro hα
          rw [D.limit ⟨α, hα⟩ hlim]
          refine iSup_le fun β => ?_
          exact ih β.1 β.2 (β.2.trans hα)
    apply top_unique
    rw [← D.union_eq_top]
    exact iSup_le fun α => hstage α.1 α.2
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep htop

private theorem increasingDevissage_stage_eq_iSup_components
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S)
    (h : D.isSuccessorComplemented) :
    ∀ α : Set.Iio S, D.stage α =
      ⨆ β : {β : SuccessorIndex S // β.1 + 1 ≤ α.1},
        (Classical.choose (show ∃ Q, IsCompl (D.successorSubmodule β.1) Q from h β.1)).map
          (D.stage ⟨β.1.1 + 1, β.1.2⟩).subtype := by
  classical
  let C : ∀ β : SuccessorIndex S,
      Submodule R (D.stage ⟨β.1 + 1, β.2⟩) :=
    fun β => Classical.choose (show ∃ Q, IsCompl (D.successorSubmodule β) Q from h β)
  let E : SuccessorIndex S → Submodule R M :=
    fun β => (C β).map (D.stage ⟨β.1 + 1, β.2⟩).subtype
  have hC (β : SuccessorIndex S) :
      IsCompl (D.successorSubmodule β) (C β) :=
    Classical.choose_spec (show ∃ Q, IsCompl (D.successorSubmodule β) Q from h β)
  have hle (β : SuccessorIndex S) :
      D.stage ⟨β.1, (ordinal_lt_add_one β.1).trans β.2⟩ ≤
        D.stage ⟨β.1 + 1, β.2⟩ := by
    apply D.monotone
    exact (ordinal_lt_add_one β.1).le
  have hsplit (β : SuccessorIndex S) :
      D.stage ⟨β.1 + 1, β.2⟩ =
        D.stage ⟨β.1, (ordinal_lt_add_one β.1).trans β.2⟩ ⊔ E β := by
    apply le_antisymm
    · rw [← Submodule.map_subtype_top (D.stage ⟨β.1 + 1, β.2⟩)]
      rw [← (hC β).sup_eq_top, Submodule.map_sup]
      simp [E, C, IncreasingDevissage.successorSubmodule,
        inf_of_le_right (hle β)]
    · exact sup_le (hle β) (Submodule.map_subtype_le _ _)
  have hstage : ∀ α : Ordinal.{w}, ∀ hα : α < S,
      D.stage ⟨α, hα⟩ =
        ⨆ β : {β : SuccessorIndex S // β.1 + 1 ≤ α}, E β := by
    intro α
    induction α using SuccOrder.limitRecOn with
    | isMin α hα =>
        obtain rfl := hα.eq_bot
        intro hα
        have hstage0 : D.stage ⟨0, hα⟩ = ⊥ := by simpa using D.zero
        change D.stage ⟨0, hα⟩ = _
        rw [hstage0]
        let : IsEmpty {β : SuccessorIndex S // β.1 + 1 ≤ 0} :=
          ⟨fun β => (not_le_of_gt (ordinal_lt_add_one β.1.1))
            (β.2.trans (bot_le : (0 : Ordinal) ≤ β.1.1))⟩
        simp only [iSup_of_empty]
    | succ α hα ih =>
        intro hα
        have hαs : α + 1 < S := by simpa only [Order.succ_eq_add_one] using hα
        have hα' : α < S := (ordinal_lt_add_one α).trans hαs
        have hleft :
            D.stage ⟨α, hα'⟩ ≤
              ⨆ β : {β : SuccessorIndex S // β.1 + 1 ≤ α + 1}, E β := by
          rw [ih hα']
          refine iSup_le fun β => ?_
          exact le_iSup_of_le ⟨β.1, le_trans β.2 (ordinal_lt_add_one α).le⟩ le_rfl
        have hright :
            (⨆ β : {β : SuccessorIndex S // β.1 + 1 ≤ α + 1}, E β) ≤
              D.stage ⟨α + 1, hαs⟩ := by
          refine iSup_le fun β => ?_
          have hβα : β.1.1 ≤ α := by
            simpa only [Order.succ_eq_add_one] using
              (Order.succ_le_succ_iff.mp β.2)
          exact (Submodule.map_subtype_le _ _).trans <|
            D.monotone (show
              (⟨β.1.1 + 1, by
                change β.1.1 + 1 < S
                exact β.1.2⟩ : Set.Iio S) ≤
                ⟨α + 1, hαs⟩ from by
                  change β.1.1 + 1 ≤ α + 1
                  exact Order.succ_le_succ hβα)
        have hsplit' : D.stage ⟨Order.succ α, hα⟩ =
              D.stage ⟨α, hα'⟩ ⊔ E ⟨α, hαs⟩ := by
          simpa only [Order.succ_eq_add_one] using hsplit ⟨α, hαs⟩
        rw [hsplit']
        apply le_antisymm
        · exact sup_le hleft
            (le_iSup_of_le ⟨⟨α, hαs⟩, le_rfl⟩ le_rfl)
        · have hright' :
              (⨆ β : {β : SuccessorIndex S // β.1 + 1 ≤ α + 1}, E β) ≤
                D.stage ⟨Order.succ α, hα⟩ := by
            simpa only [Order.succ_eq_add_one] using hright
          rw [hsplit'] at hright'
          exact hright'
    | isSuccLimit α hlim ih =>
        intro hα
        apply le_antisymm
        · rw [D.limit ⟨α, hα⟩ hlim]
          refine iSup_le fun β => ?_
          exact (ih β.1 β.2 (β.2.trans hα)).le.trans <| by
            refine iSup_le fun γ => le_iSup_of_le ⟨γ.1, γ.2.trans β.2.le⟩ le_rfl
        · refine iSup_le fun β => ?_
          exact (Submodule.map_subtype_le _ _).trans (D.monotone (show
            (⟨β.1.1 + 1, by
              change β.1.1 + 1 < S
              exact β.1.2⟩ : Set.Iio S) ≤
              ⟨α, hα⟩ from β.2))
  intro α
  simpa [C, E] using hstage α.1 α.2

private theorem increasingDevissage_isAmbientlyComplemented_of_isSuccessorComplemented
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S)
    (h : D.isSuccessorComplemented) : D.isAmbientlyComplemented := by
  classical
  let C : ∀ β : SuccessorIndex S,
      Submodule R (D.stage ⟨β.1 + 1, β.2⟩) :=
    fun β => Classical.choose (show ∃ Q, IsCompl (D.successorSubmodule β) Q from h β)
  let E : SuccessorIndex S → Submodule R M :=
    fun β => (C β).map (D.stage ⟨β.1 + 1, β.2⟩).subtype
  have hInternal : DirectSum.IsInternal E := by
    simpa [C, E] using increasingDevissage_isInternal_of_isSuccessorComplemented D h
  have hStage (α : Set.Iio S) : D.stage α =
      ⨆ β : {β : SuccessorIndex S // β.1 + 1 ≤ α.1}, E β := by
    simpa [C, E] using increasingDevissage_stage_eq_iSup_components D h α
  let e : (⨁ β, E β) ≃ₗ[R] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap E) hInternal
  intro α
  let pred : SuccessorIndex S → Prop := fun β => β.1 + 1 ≤ α.1
  let p : M →ₗ[R] M :=
    (DirectSum.coeLinearMap E).comp
      ((DFinsupp.filterLinearMap R (fun β => E β) pred).comp e.symm.toLinearMap)
  have hp_mem (x : M) : p x ∈ D.stage α := by
    rw [hStage α]
    rw [iSup_subtype]
    rw [Submodule.mem_biSup_iff_exists_dfinsupp (R := R)
      (N := M) (ι := SuccessorIndex S) pred E]
    refine ⟨e.symm x, ?_⟩
    rfl
  let q : M →ₗ[R] D.stage α := p.codRestrict (D.stage α) hp_mem
  have hq (x : D.stage α) : q x = x := by
    apply Subtype.ext
    have hx : (x : M) ∈
        ⨆ β : {β : SuccessorIndex S // β.1 + 1 ≤ α.1}, E β := by
      rw [← hStage α]
      exact x.property
    have hx' : (x : M) ∈
        ⨆ (β : SuccessorIndex S) (_ : β.1 + 1 ≤ α.1), E β := by
      simpa only [iSup_subtype] using hx
    obtain ⟨v, hv⟩ :=
      (Submodule.mem_biSup_iff_exists_dfinsupp (R := R) (N := M)
        (ι := SuccessorIndex S) pred E (x : M)).mp hx'
    have hv' : DirectSum.coeLinearMap E (v.filter pred) = (x : M) := by
      rw [DirectSum.coeLinearMap_eq_dfinsuppSum]
      simpa only [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
        LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype] using hv
    have hs : e.symm (x : M) = v.filter pred := by
      rw [← hv']
      exact e.symm_apply_apply _
    change p (x : M) = (x : M)
    simp only [p, LinearMap.comp_apply, LinearEquiv.coe_coe, hs]
    have hff :
        (DFinsupp.filterLinearMap R (fun β => E β) pred) (v.filter pred) =
          v.filter pred := by
      ext β
      by_cases hβ : pred β
      · simp [DFinsupp.filter_apply, hβ]
      · simp [DFinsupp.filter_apply, hβ]
    rw [hff]
    exact hv'
  exact ⟨LinearMap.ker q, LinearMap.isCompl_of_proj hq⟩

/-- For a continuous filtration, splitting at every successor is equivalent to
every stage being a direct summand of the ambient module. -/
theorem IncreasingDevissage.isSuccessorComplemented_iff_isAmbientlyComplemented
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S) :
    D.isSuccessorComplemented ↔ D.isAmbientlyComplemented := by
  constructor
  · intro h
    exact increasingDevissage_isAmbientlyComplemented_of_isSuccessorComplemented D h
  · intro h α
    rcases h ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩ with ⟨Q, hQ⟩
    refine ⟨Q.comap (D.stage ⟨α.1 + 1, α.2⟩).subtype, ?_⟩
    apply Submodule.isCompl_comap_subtype_of_isCompl_of_le hQ
    exact D.monotone (show (⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩ :
      Set.Iio S) ≤ ⟨α.1 + 1, α.2⟩ from
      show α.1 ≤ α.1 + 1 from (ordinal_lt_add_one α.1).le)

/-! ## Direct sum and Kaplansky dévissages -/

/-- A direct sum dévissage is an increasing continuous filtration whose
successive inclusions split. -/
structure DirectSumDevissage
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Ordinal.{w}) : Type (max (max u v) (w + 2))
    extends IncreasingDevissage (R := R) (M := M) S where
  /-- Each predecessor is a direct summand of the corresponding successor. -/
  successor : toIncreasingDevissage.isSuccessorComplemented

/-- A Kaplansky dévissage is a direct sum dévissage with countably generated
successive quotients. -/
structure KaplanskyDevissage
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Ordinal.{w}) : Type (max (max u v) (w + 2))
    extends DirectSumDevissage (R := R) (M := M) S where
  /-- Every successive quotient is countably generated. -/
  countablyGenerated :
    ∀ α : SuccessorIndex S,
      Module.IsCountablyGenerated R
        (toDirectSumDevissage.toIncreasingDevissage.successorQuotient α)

/-- A module admits a Kaplansky dévissage. -/
def HasKaplanskyDevissage
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) : Prop :=
  ∃ S : Ordinal.{v},
    Nonempty (KaplanskyDevissage (R := R) (M := (M : Type v)) S)

/-- A bundled module is a direct sum of countably generated modules. -/
def IsDirectSumOfCountablyGeneratedModules
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) : Prop :=
  ∃ (ι : Type v) (N : ι → ModuleCat.{v} R),
    (∀ i, Module.IsCountablyGenerated R (N i)) ∧
      Nonempty ((M : Type v) ≃ₗ[R] (⨁ i, (N i : Type v)))

/-- A bundled module is a direct sum of countably generated projective modules. -/
def IsDirectSumOfCountablyGeneratedProjectiveModules
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) : Prop :=
  ∃ (ι : Type v) (N : ι → ModuleCat.{v} R),
    (∀ i,
      Module.IsCountablyGenerated R (N i) ∧ Module.Projective R (N i)) ∧
      Nonempty ((M : Type v) ≃ₗ[R] (⨁ i, (N i : Type v)))

/-! ## The decomposition lemma and Kaplansky's theorem -/

/-- The successive quotients of a direct sum dévissage give a direct-sum
decomposition of the ambient module. -/
theorem directSumDevissage_decomposition
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : DirectSumDevissage (R := R) (M := M) S) :
    Nonempty
      (M ≃ₗ[R]
        (⨁ α : SuccessorIndex S,
          D.toIncreasingDevissage.successorQuotient α)) := by
  classical
  let D₀ := D.toIncreasingDevissage
  let C : ∀ α : SuccessorIndex S,
      Submodule R (D₀.stage ⟨α.1 + 1, α.2⟩) :=
    fun α => Classical.choose (show ∃ Q, IsCompl (D₀.successorSubmodule α) Q from D.successor α)
  let E : SuccessorIndex S → Submodule R M :=
    fun α => (C α).map (D₀.stage ⟨α.1 + 1, α.2⟩).subtype
  have hC (α : SuccessorIndex S) :
      IsCompl (D₀.successorSubmodule α) (C α) :=
    Classical.choose_spec
      (show ∃ Q, IsCompl (D₀.successorSubmodule α) Q from D.successor α)
  have hInternal : DirectSum.IsInternal E := by
    simpa [C, E, D₀] using
      increasingDevissage_isInternal_of_isSuccessorComplemented D₀ D.successor
  let u : ∀ α : SuccessorIndex S,
      D₀.successorQuotient α ≃ₗ[R] C α :=
    fun α => Submodule.quotientEquivOfIsCompl _ _ (hC α)
  let v : ∀ α : SuccessorIndex S, C α ≃ₗ[R] E α := fun α =>
    LinearEquiv.ofBijective
      (((D₀.stage ⟨α.1 + 1, α.2⟩).subtype.comp (C α).subtype).codRestrict (E α)
        (fun x => Submodule.mem_map_of_mem x.property))
      ⟨(by
          intro x y hxy
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : E α => (z : M)) hxy), (by
          intro z
          rcases z.property with ⟨x, hx, hxz⟩
          refine ⟨⟨x, hx⟩, ?_⟩
          apply Subtype.ext
          exact hxz)⟩
  let w : ∀ α : SuccessorIndex S,
      D₀.successorQuotient α ≃ₗ[R] E α := fun α => (u α).trans (v α)
  let φ :
      (⨁ α : SuccessorIndex S, D₀.successorQuotient α) →ₗ[R] M :=
    DirectSum.toModule R _ M fun α =>
      (E α).subtype.comp (w α).toLinearMap
  have hφ : φ = (DirectSum.coeLinearMap E).comp
      (DirectSum.congrLinearEquiv w).toLinearMap := by
    apply DirectSum.linearMap_ext
    intro α
    ext x
    simp only [φ, DirectSum.toModule_lof, LinearMap.comp_apply,
      DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_lof,
      DirectSum.coeLinearMap_lof]
    rfl
  have hbij : Function.Bijective φ := by
    rw [hφ]
    have hcoe : Function.Bijective (DirectSum.coeLinearMap E) :=
      ⟨hInternal.1, hInternal.2⟩
    exact hcoe.comp (DirectSum.congrLinearEquiv w).bijective
  exact ⟨(LinearEquiv.ofBijective φ hbij).symm⟩

private theorem isCountablyGenerated_of_linearEquiv
    {R : Type u} {X Y : Type v} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (e : X ≃ₗ[R] Y)
    (hX : Module.IsCountablyGenerated R X) :
    Module.IsCountablyGenerated R Y := by
  rcases hX with ⟨s, hs, hspan⟩
  refine ⟨e '' s, hs.image e, ?_⟩
  calc
    Submodule.span R (e '' s) =
        (Submodule.span R s).map (e : X →ₗ[R] Y) :=
      (Submodule.map_span (e : X →ₗ[R] Y) s).symm
    _ = ⊤ := by rw [hspan]; simp

private theorem ordinalDirectSum_hasKaplanskyDevissage
    {R : Type u} [CommRing R] {T : Ordinal.{v}}
    (N : T.ToType → ModuleCat.{v} R)
    (hN : ∀ i, Module.IsCountablyGenerated R (N i)) :
    ∃ S : Ordinal.{v},
      Nonempty (KaplanskyDevissage (R := R)
        (M := (⨁ i, (N i : Type v))) S) := by
  classical
  let S : Ordinal.{v} := T + 1
  let pred : ∀ β : Set.Iio S, T.ToType → Prop :=
    fun β i => (i : Ordinal) < β.1
  let F : ∀ β : Set.Iio S,
      (⨁ i, (N i : Type v)) →ₗ[R] (⨁ i, (N i : Type v)) :=
    fun β => DFinsupp.filterLinearMap R (fun i => (N i : Type v)) (pred β)
  let stage : Set.Iio S → Submodule R (⨁ i, (N i : Type v)) :=
    fun β => LinearMap.range (F β)
  refine ⟨S, ⟨
    { toDirectSumDevissage :=
        { toIncreasingDevissage :=
            { stage := stage, monotone := ?_, zero_lt := ?_, zero := ?_,
              union_eq_top := ?_, limit := ?_ },
          successor := ?_ },
      countablyGenerated := ?_ }⟩⟩
  · intro β γ hβγ
    rintro x ⟨y, rfl⟩
    refine ⟨F β y, ?_⟩
    ext i
    change (if (i : Ordinal) < γ.1 then
        (if (i : Ordinal) < β.1 then y i else 0) else 0) =
      (if (i : Ordinal) < β.1 then y i else 0)
    by_cases hi : (i : Ordinal) < β.1
    · have hi' : (i : Ordinal) < γ.1 := lt_of_lt_of_le hi hβγ
      simp [hi, hi']
    · by_cases hi' : (i : Ordinal) < γ.1
      · simp [hi, hi']
      · simp [hi, hi']
  · change (0 : Ordinal.{v}) < T + 1
    change (⊥ : Ordinal.{v}) < Order.succ T
    exact Order.bot_lt_succ T
  · ext x
    simp only [stage, F, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]
      ext i
      simp [pred, DFinsupp.filterLinearMap, DFinsupp.filter_apply]
    · intro hx
      exact ⟨0, by simpa [DFinsupp.filter_apply] using hx.symm⟩
  · apply top_unique
    intro x hx
    classical
    by_cases hxs : x.support.Nonempty
    · let i := x.support.max' hxs
      let β : Set.Iio S := ⟨(i : Ordinal) + 1, by
        change (i : Ordinal) + 1 < S
        change (i : Ordinal) + 1 < T + 1
        have hiT : (i : Ordinal) < T := by
          exact Ordinal.typein_lt_self i
        simpa only [Order.succ_eq_add_one] using
          Order.succ_lt_succ hiT⟩
      exact (le_iSup stage β) (by
        refine ⟨x, ?_⟩
        ext j
        change (if (j : Ordinal) < β.1 then x j else 0) = x j
        by_cases hzero : x j = 0
        · simp [hzero]
        · have hjmax : j ≤ i := Finset.le_max' x.support j
            (DFinsupp.mem_support_iff.mpr hzero)
          have hjmax' : (j : Ordinal) ≤ (i : Ordinal) := by
            change (Ordinal.ToType.mk.symm j).1 ≤ (Ordinal.ToType.mk.symm i).1
            exact (Ordinal.ToType.mk.symm.le_iff_le).mpr hjmax
          have hjlt : (j : Ordinal) < (i : Ordinal) + 1 :=
            lt_of_le_of_lt hjmax' (ordinal_lt_add_one (i : Ordinal))
          simp [β, hjlt])
    · have hx0 : x = 0 := by
        ext i
        by_contra hi
        exact hxs ⟨i, DFinsupp.mem_support_iff.mpr hi⟩
      subst hx0
      exact zero_mem _
  · intro β hβ
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      classical
      by_cases hys : (F β y).support.Nonempty
      · let i := (F β y).support.max' hys
        let γ : Set.Iio β.1 := ⟨(i : Ordinal) + 1, by
          change (i : Ordinal) + 1 < β.1
          have hiβ : (i : Ordinal) < β.1 := by
            by_contra hiβ
            have hi0 : F β y i = 0 := by
              change (if (i : Ordinal) < β.1 then y i else 0) = 0
              simp [hiβ]
            exact (DFinsupp.mem_support_iff.mp (Finset.max'_mem _ hys)) hi0
          simpa only [Order.succ_eq_add_one] using hβ.succ_lt hiβ⟩
        let emb : Set.Iio β.1 → Set.Iio S :=
          fun δ => ⟨δ.1, by
            exact δ.2.trans (show β.1 < S from β.2)⟩
        have hmem : F β y ∈ stage (emb γ) := by
            refine ⟨F β y, ?_⟩
            ext j
            change (if (j : Ordinal) < γ.1 then F β y j else 0) = F β y j
            by_cases hzero : F β y j = 0
            · simp [hzero]
            · have hjmem : j ∈ (F β y).support :=
                DFinsupp.mem_support_iff.mpr hzero
              have hjmax : j ≤ i := Finset.le_max' (F β y).support j hjmem
              have hjmax' : (j : Ordinal) ≤ (i : Ordinal) := by
                exact (Ordinal.ToType.mk.symm.le_iff_le).mpr hjmax
              have hjlt : (j : Ordinal) < (i : Ordinal) + 1 :=
                lt_of_le_of_lt hjmax' (ordinal_lt_add_one (i : Ordinal))
              have hjltγ : (j : Ordinal) < γ.1 := by simpa [γ] using hjlt
              simp [hjltγ]
        simpa [emb] using
          (le_iSup (fun δ : Set.Iio β.1 => stage (emb δ)) γ) hmem
      · have hz : F β y = 0 := by
          ext i
          by_contra hi
          exact hys ⟨i, DFinsupp.mem_support_iff.mpr hi⟩
        rw [hz]
        exact zero_mem _
    · refine iSup_le fun γ => ?_
      rintro x ⟨y, rfl⟩
      let γS : Set.Iio S := ⟨γ.1, by
        exact γ.2.trans (show β.1 < S from β.2)⟩
      refine ⟨F γS y, ?_⟩
      ext i
      dsimp [F, pred, DFinsupp.filterLinearMap, γS]
      change (if (i : Ordinal) < β.1 then
          (if (i : Ordinal) < γ.1 then y i else 0) else 0) =
        (if (i : Ordinal) < γ.1 then y i else 0)
      by_cases hiγ : (i : Ordinal) < γ.1
      · have hiβ : (i : Ordinal) < β.1 := lt_of_lt_of_le hiγ γ.2.le
        simp [hiγ, hiβ]
      · by_cases hiβ : (i : Ordinal) < β.1
        · simp [hiγ, hiβ]
        · simp [hiγ, hiβ]
  · intro α
    let β₀ : Set.Iio S := ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩
    let β₁ : Set.Iio S := ⟨α.1 + 1, α.2⟩
    have hβ : β₀ ≤ β₁ := (ordinal_lt_add_one α.1).le
    have hfilter (β γ : Set.Iio S) (hβγ : β ≤ γ) (x) :
        F γ (F β x) = F β x := by
      ext i
      dsimp [F, pred, DFinsupp.filterLinearMap]
      change (if (i : Ordinal) < γ.1 then
          (if (i : Ordinal) < β.1 then x i else 0) else 0) =
        (if (i : Ordinal) < β.1 then x i else 0)
      by_cases hiβ : (i : Ordinal) < β.1
      · have hiγ : (i : Ordinal) < γ.1 := lt_of_lt_of_le hiβ hβγ
        simp [hiβ, hiγ]
      · by_cases hiγ : (i : Ordinal) < γ.1
        · simp [hiβ]
        · simp [hiβ]
    have hfilter_left (β γ : Set.Iio S) (hβγ : β ≤ γ) (x) :
        F β (F γ x) = F β x := by
      ext i
      dsimp [F, pred, DFinsupp.filterLinearMap]
      change (if (i : Ordinal) < β.1 then
          (if (i : Ordinal) < γ.1 then x i else 0) else 0) =
        (if (i : Ordinal) < β.1 then x i else 0)
      by_cases hiβ : (i : Ordinal) < β.1
      · have hiγ : (i : Ordinal) < γ.1 := lt_of_lt_of_le hiβ hβγ
        simp [hiβ, hiγ]
      · by_cases hiγ : (i : Ordinal) < γ.1
        · simp [hiβ]
        · simp [hiβ]
    have hle : stage β₀ ≤ stage β₁ := by
      rintro x ⟨y, rfl⟩
      refine ⟨F β₀ y, ?_⟩
      exact hfilter β₀ β₁ hβ y
    let p : Submodule R (stage β₁) := (stage β₀).comap (stage β₁).subtype
    have hmap (x : stage β₁) : F β₀ (x : (⨁ i, (N i : Type v))) ∈ stage β₀ := by
      rcases x.property with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [← hy]
      exact (hfilter_left β₀ β₁ hβ y).symm
    let g : stage β₁ →ₗ[R] stage β₁ :=
      ((F β₀).comp (stage β₁).subtype).codRestrict (stage β₁) (fun x =>
        hle (hmap x))
    let f : stage β₁ →ₗ[R] p :=
      g.codRestrict p (fun x => hmap x)
    have hf (x : p) : f x = x := by
      rcases x.property with ⟨y, hy⟩
      apply Subtype.ext
      apply Subtype.ext
      change F β₀ (x : (⨁ i, (N i : Type v))) = (x : (⨁ i, (N i : Type v)))
      have hx : (x : (⨁ i, (N i : Type v))) = F β₀ y := hy.symm
      rw [hx]
      exact hfilter β₀ β₀ le_rfl y
    exact ⟨LinearMap.ker f, LinearMap.isCompl_of_proj hf⟩
  · intro α
    let β₀ : Set.Iio S := ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩
    let β₁ : Set.Iio S := ⟨α.1 + 1, α.2⟩
    have hβ : β₀ ≤ β₁ := (ordinal_lt_add_one α.1).le
    have hfilter (β γ : Set.Iio S) (hβγ : β ≤ γ) (x) :
        F γ (F β x) = F β x := by
      ext i
      dsimp [F, pred, DFinsupp.filterLinearMap]
      change (if (i : Ordinal) < γ.1 then
          (if (i : Ordinal) < β.1 then x i else 0) else 0) =
        (if (i : Ordinal) < β.1 then x i else 0)
      by_cases hiβ : (i : Ordinal) < β.1
      · have hiγ : (i : Ordinal) < γ.1 := lt_of_lt_of_le hiβ hβγ
        simp [hiβ, hiγ]
      · by_cases hiγ : (i : Ordinal) < γ.1
        · simp [hiβ]
        · simp [hiβ]
    have hfilter_left (β γ : Set.Iio S) (hβγ : β ≤ γ) (x) :
        F β (F γ x) = F β x := by
      ext i
      dsimp [F, pred, DFinsupp.filterLinearMap]
      change (if (i : Ordinal) < β.1 then
          (if (i : Ordinal) < γ.1 then x i else 0) else 0) =
        (if (i : Ordinal) < β.1 then x i else 0)
      by_cases hiβ : (i : Ordinal) < β.1
      · have hiγ : (i : Ordinal) < γ.1 := lt_of_lt_of_le hiβ hβγ
        simp [hiβ, hiγ]
      · by_cases hiγ : (i : Ordinal) < γ.1
        · simp [hiβ]
        · simp [hiβ]
    have hle : stage β₀ ≤ stage β₁ := by
      rintro x ⟨y, rfl⟩
      refine ⟨F β₀ y, ?_⟩
      exact hfilter β₀ β₁ hβ y
    have hmap (x : stage β₁) : F β₀ (x : (⨁ i, (N i : Type v))) ∈ stage β₀ := by
      rcases x.property with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [← hy]
      exact (hfilter_left β₀ β₁ hβ y).symm
    let p : Submodule R (stage β₁) := (stage β₀).comap (stage β₁).subtype
    let g : stage β₁ →ₗ[R] stage β₁ :=
      ((F β₀).comp (stage β₁).subtype).codRestrict (stage β₁) (fun x =>
        hle (hmap x))
    let f : stage β₁ →ₗ[R] p :=
      g.codRestrict p (fun x => hmap x)
    have hf (x : p) : f x = x := by
      rcases x.property with ⟨y, hy⟩
      apply Subtype.ext
      apply Subtype.ext
      change F β₀ (x : (⨁ i, (N i : Type v))) = (x : (⨁ i, (N i : Type v)))
      have hx : (x : (⨁ i, (N i : Type v))) = F β₀ y := hy.symm
      rw [hx]
      exact hfilter β₀ β₀ le_rfl y
    have hαT : α.1 < T := by
      simpa only [Order.succ_eq_add_one] using Order.succ_lt_succ_iff.mp α.2
    let iα : T.ToType := Ordinal.ToType.mk ⟨α.1, hαT⟩
    have hiα : (iα : Ordinal) = α.1 := by simp [iα]
    have hf_apply (x : stage β₁) :
        (f x : stage β₁) = g x := by
      rfl
    have hg_apply (x : stage β₁) :
        ((g x : stage β₁) : (⨁ i, (N i : Type v))) =
          F β₀ (x : (⨁ i, (N i : Type v))) := by
      rfl
    have hlof (n : (N iα : Type v)) :
        DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα n ∈ stage β₁ := by
      refine ⟨DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα n, ?_⟩
      ext k
      change (if (k : Ordinal) < β₁.1 then
          (DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα n) k else 0) =
        (DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα n) k
      by_cases hk : k = iα
      · subst k
        have hiβ₁ : (iα : Ordinal) < β₁.1 := by
          simp [β₁, hiα]
        simp [hiβ₁]
      · by_cases hβ : (k : Ordinal) < β₁.1
        · simp [hβ]
        · have hz :
              (DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα n) k = 0 := by
            rw [DirectSum.lof_eq_of]
            exact DirectSum.of_eq_of_ne (β := fun i => (N i : Type v)) iα k n hk
          rw [hz]
          simp
    have hker (n : (N iα : Type v)) :
        (⟨DirectSum.lof R T.ToType
          (fun i => (N i : Type v)) iα n, hlof n⟩ : stage β₁) ∈ LinearMap.ker f := by
      have hnotβ₀ : ¬ (iα : Ordinal) < β₀.1 := by
        simp [β₀, hiα]
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      apply Subtype.ext
      rw [hf_apply, hg_apply]
      have hfix : F β₁ (DirectSum.lof R T.ToType
          (fun i => (N i : Type v)) iα n) =
          DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα n := by
        rcases hlof n with ⟨y, hy⟩
        rw [← hy]
        exact hfilter β₁ β₁ le_rfl y
      change F β₀ (DirectSum.lof R T.ToType
        (fun i => (N i : Type v)) iα n) = 0
      rw [← hfix]
      rw [hfilter_left β₀ β₁ hβ]
      ext k
      change (if (k : Ordinal) < β₀.1 then
          (DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα n) k else 0) = 0
      by_cases hk : k = iα
      · subst k
        simp [hnotβ₀]
      · have hz :
            (DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα n) k = 0 := by
          rw [DirectSum.lof_eq_of]
          exact DirectSum.of_eq_of_ne (β := fun i => (N i : Type v)) iα k n hk
        simp [hz]
    let j : (N iα : Type v) →ₗ[R] LinearMap.ker f :=
      ((DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα).codRestrict
        (stage β₁) hlof).codRestrict (LinearMap.ker f) (fun c => by
          have hc : (LinearMap.codRestrict (stage β₁)
              (DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα) hlof) c =
              (⟨DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα c,
                hlof c⟩ : stage β₁) := by
            apply Subtype.ext
            rfl
          rw [hc]
          exact hker c)
    have hj (z : (N iα : Type v)) :
        ((j z : LinearMap.ker f) : (⨁ i, (N i : Type v))) =
          DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα z := by
      rfl
    have hkerCount : Module.IsCountablyGenerated R (LinearMap.ker f) := by
      refine isCountablyGenerated_of_linearEquiv
        (LinearEquiv.ofBijective j ⟨?_, ?_⟩) (hN iα)
      · intro x y hxy
        have hcoord := congrArg (fun z : LinearMap.ker f =>
          ((z : stage β₁) : (⨁ i, (N i : Type v)))) hxy
        rw [hj x, hj y] at hcoord
        have hcoord' := congrArg (fun z : (⨁ i, (N i : Type v)) => z iα) hcoord
        simpa only [DirectSum.lof_apply] using hcoord'
      · intro x
        let n : (N iα : Type v) :=
          (((x : LinearMap.ker f) : stage β₁) : (⨁ i, (N i : Type v))) iα
        refine ⟨n, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        ext k
        by_cases hk : k = iα
        · subst k
          rw [hj n]
          dsimp [n]
          simp only [DirectSum.lof_apply]
        · have hfx0 : f x = 0 := LinearMap.mem_ker.mp x.property
          have hfx : F β₀ (x : (⨁ i, (N i : Type v))) = 0 := by
            have hfx' := congrArg (fun z : p =>
              ((z : stage β₁) : (⨁ i, (N i : Type v)))) hfx0
            dsimp [f, g, p] at hfx'
            exact hfx'
          by_cases hkβ : (k : Ordinal) < β₀.1
          · have hcoord := congrArg (fun z : (⨁ i, (N i : Type v)) => z k) hfx
            have hzero_x : (x : (⨁ i, (N i : Type v))) k = 0 := by
              dsimp [F, pred] at hcoord
              change (if (k : Ordinal) < β₀.1 then
                (x : (⨁ i, (N i : Type v))) k else 0) = 0 at hcoord
              simpa [hkβ] using hcoord
            rw [hj n]
            have hzero_n :
                (DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα n) k = 0 := by
              rw [DirectSum.lof_eq_of]
              exact DirectSum.of_eq_of_ne (β := fun i => (N i : Type v)) iα k n hk
            exact hzero_n.trans hzero_x.symm
          · have hkβ₁ : ¬ (k : Ordinal) < β₁.1 := by
              intro hkβ₁
              have hk_le : (k : Ordinal) ≤ α.1 := by
                apply Order.le_of_lt_succ
                simpa only [β₁, Order.succ_eq_add_one] using hkβ₁
              have hk_ne : (k : Ordinal) ≠ α.1 := by
                intro hk_eq
                apply hk
                apply (Ordinal.ToType.mk.symm.injective)
                apply Subtype.ext
                simpa [hiα] using hk_eq
              exact hkβ (lt_of_le_of_ne hk_le hk_ne)
            rcases (x : stage β₁).property with ⟨y, hy⟩
            have hcoord0 : (x : (⨁ i, (N i : Type v))) k = 0 := by
              rw [← hy]
              change (if (k : Ordinal) < β₁.1 then y k else 0) = 0
              simp [hkβ₁]
            rw [hj n]
            have hzero_n :
                (DirectSum.lof R T.ToType (fun i => (N i : Type v)) iα n) k = 0 := by
              rw [DirectSum.lof_eq_of]
              exact DirectSum.of_eq_of_ne (β := fun i => (N i : Type v)) iα k n hk
            exact hzero_n.trans hcoord0.symm
    let qEquiv : (stage β₁ ⧸ p) ≃ₗ[R] LinearMap.ker f :=
      Submodule.quotientEquivOfIsCompl p (LinearMap.ker f)
        (LinearMap.isCompl_of_proj hf)
    have hquot : Module.IsCountablyGenerated R (stage β₁ ⧸ p) :=
      isCountablyGenerated_of_linearEquiv qEquiv.symm hkerCount
    change Module.IsCountablyGenerated R (stage β₁ ⧸ p)
    exact hquot

private theorem isCompl_map_linearEquiv
    {R : Type u} {X Y : Type v} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (e : X ≃ₗ[R] Y) (p q : Submodule R X) (h : IsCompl p q) :
    IsCompl (p.map (e : X →ₗ[R] Y)) (q.map (e : X →ₗ[R] Y)) := by
  have htop : (⊤ : Submodule R X).map (e : X →ₗ[R] Y) = ⊤ := by
    apply top_unique
    rintro y -
    rcases e.surjective y with ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩
  refine ⟨?_, ?_⟩
  · exact Submodule.disjoint_map (f := (e : X →ₗ[R] Y)) e.injective h.disjoint
  · rw [codisjoint_iff_le_sup]
    intro y hy
    have hsup :
        p.map (e : X →ₗ[R] Y) ⊔ q.map (e : X →ₗ[R] Y) = ⊤ := by
      rw [← Submodule.map_sup, h.sup_eq_top, htop]
    rw [hsup]
    exact hy

private def kaplanskyDevissage_of_linearEquiv
    {R : Type u} {X Y : Type v} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    {S : Ordinal.{w}}
    (K : KaplanskyDevissage (R := R) (M := X) S)
    (e : X ≃ₗ[R] Y) :
    KaplanskyDevissage (R := R) (M := Y) S := by
  classical
  let A : Set.Iio S → Submodule R Y :=
    fun α => (K.toDirectSumDevissage.toIncreasingDevissage.stage α).map
      (e : X →ₗ[R] Y)
  have htop : (⊤ : Submodule R X).map (e : X →ₗ[R] Y) = ⊤ := by
    apply top_unique
    rintro y -
    rcases e.surjective y with ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩
  let hstageEquiv : ∀ α : Set.Iio S,
      K.toDirectSumDevissage.toIncreasingDevissage.stage α ≃ₗ[R] A α :=
    fun α => e.ofSubmodules _ _ rfl
  have hPmap (α : SuccessorIndex S) :
      (K.toDirectSumDevissage.toIncreasingDevissage.successorSubmodule α).map
          (hstageEquiv ⟨α.1 + 1, α.2⟩).toLinearMap =
        (A ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩).comap
          (A ⟨α.1 + 1, α.2⟩).subtype := by
    let α₀ : Set.Iio S := ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩
    let α₁ : Set.Iio S := ⟨α.1 + 1, α.2⟩
    let P := K.toDirectSumDevissage.toIncreasingDevissage.successorSubmodule α
    let P' := (A α₀).comap (A α₁).subtype
    let e₁ := hstageEquiv α₁
    change P.map e₁.toLinearMap = P'
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ((e₁ y : A α₁) : Y) ∈ A α₀
      change ((e₁ y : A α₁) : Y) ∈
        (K.toDirectSumDevissage.toIncreasingDevissage.stage α₀).map
          (e : X →ₗ[R] Y)
      apply Submodule.mem_map.mpr
      refine ⟨(y : X), ?_, ?_⟩
      · change (y : X) ∈
          K.toDirectSumDevissage.toIncreasingDevissage.stage α₀ at hy
        exact hy
      · simp [e₁, hstageEquiv]
    · intro hx
      let y := e₁.symm x
      have hy : (y : X) ∈
          K.toDirectSumDevissage.toIncreasingDevissage.stage α₀ := by
        change (x : Y) ∈ A α₀ at hx
        change (x : Y) ∈
          (K.toDirectSumDevissage.toIncreasingDevissage.stage α₀).map
            (e : X →ₗ[R] Y) at hx
        rcases hx with ⟨z, hz, hzx⟩
        have heq : e (y : X) = e z := by
          have hey : e (y : X) = (e₁ y : Y) := by
            simp [y, e₁, hstageEquiv]
          calc
            e (y : X) = (e₁ y : Y) := hey
            _ = (x : A α₁) := by
              exact congrArg (fun z : A α₁ => (z : Y))
                (e₁.apply_symm_apply x)
            _ = e z := hzx.symm
        have : (y : X) = z := e.injective heq
        simpa [this] using hz
      refine ⟨y, ?_, ?_⟩
      · change (y : X) ∈
          K.toDirectSumDevissage.toIncreasingDevissage.stage α₀
        exact hy
      · exact e₁.apply_symm_apply x
  have hsucc : ∀ α : SuccessorIndex S,
      IsComplemented ((A ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩).comap
        (A ⟨α.1 + 1, α.2⟩).subtype) := by
    intro α
    obtain ⟨C, hC⟩ := K.successor α
    let α₁ : Set.Iio S := ⟨α.1 + 1, α.2⟩
    let P' := (A ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩).comap
      (A α₁).subtype
    let C' := C.map (hstageEquiv α₁).toLinearMap
    have hC' : IsCompl P' C' := by
      dsimp [P']
      rw [← hPmap α]
      exact isCompl_map_linearEquiv (hstageEquiv α₁) _ _ hC
    exact ⟨C', hC'⟩
  have hcount : ∀ α : SuccessorIndex S,
      Module.IsCountablyGenerated R
        ((A ⟨α.1 + 1, α.2⟩) ⧸
          (A ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩).comap
            (A ⟨α.1 + 1, α.2⟩).subtype) := by
    intro α
    obtain ⟨C, hC⟩ := K.successor α
    let α₀ : Set.Iio S := ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩
    let α₁ : Set.Iio S := ⟨α.1 + 1, α.2⟩
    let P := K.toDirectSumDevissage.toIncreasingDevissage.successorSubmodule α
    let P' := (A α₀).comap (A α₁).subtype
    let C' := C.map (hstageEquiv α₁).toLinearMap
    have hC' : IsCompl P' C' := by
      dsimp [P']
      rw [← hPmap α]
      exact isCompl_map_linearEquiv (hstageEquiv α₁) _ _ hC
    let q₀ := Submodule.quotientEquivOfIsCompl P C hC
    let q₁ := Submodule.quotientEquivOfIsCompl P' C' hC'
    let cEquiv : C ≃ₗ[R] C' :=
      Submodule.equivMapOfInjective (hstageEquiv α₁).toLinearMap
        (hstageEquiv α₁).injective C
    let q : ((A α₁) ⧸ P') ≃ₗ[R]
        (K.toDirectSumDevissage.toIncreasingDevissage.successorQuotient α) :=
      q₁.trans (cEquiv.symm.trans q₀.symm)
    exact isCountablyGenerated_of_linearEquiv q.symm (K.countablyGenerated α)
  refine
    { toDirectSumDevissage :=
        { toIncreasingDevissage :=
            { stage := A
              monotone := by
                intro α β hαβ
                exact Submodule.map_mono (K.toDirectSumDevissage.toIncreasingDevissage.monotone hαβ)
              zero_lt := K.toDirectSumDevissage.toIncreasingDevissage.zero_lt
              zero := by
                simpa [A] using congrArg (Submodule.map (e : X →ₗ[R] Y))
                  K.toDirectSumDevissage.toIncreasingDevissage.zero
              union_eq_top := by
                rw [← Submodule.map_iSup]
                simpa [A, htop] using congrArg (Submodule.map (e : X →ₗ[R] Y))
                  K.toDirectSumDevissage.toIncreasingDevissage.union_eq_top
              limit := by
                intro α hα
                simpa [A] using congrArg (Submodule.map (e : X →ₗ[R] Y))
                  (K.toDirectSumDevissage.toIncreasingDevissage.limit α hα) }
          successor := by
            intro α
            exact hsucc α }
      countablyGenerated := by
        intro α
        exact hcount α }

/-- A module is a direct sum of countably generated modules exactly when it
admits a Kaplansky dévissage. -/
theorem isDirectSumOfCountablyGeneratedModules_iff_hasKaplanskyDevissage
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) :
    IsDirectSumOfCountablyGeneratedModules M ↔ HasKaplanskyDevissage M := by
  constructor
  · intro h
    rcases h with ⟨ι, N, hN, ⟨eM⟩⟩
    let T : Ordinal.{v} := Cardinal.ord (Cardinal.mk ι)
    have hcard : Cardinal.mk T.ToType = Cardinal.mk ι := by
      simp [T]
    let eι : T.ToType ≃ ι := (Cardinal.eq.mp hcard).some
    let N' : T.ToType → ModuleCat.{v} R := fun i => N (eι i)
    have hN' : ∀ i, Module.IsCountablyGenerated R (N' i) := by
      intro i
      exact hN (eι i)
    rcases ordinalDirectSum_hasKaplanskyDevissage N' hN' with ⟨S, K⟩
    let reindex : (⨁ i : ι, (N i : Type v)) ≃ₗ[R]
        (⨁ i : T.ToType, (N' i : Type v)) :=
      DirectSum.lequivCongrLeft R eι.symm
    let eX : (M : Type v) ≃ₗ[R] (⨁ i : T.ToType, (N' i : Type v)) :=
      eM.trans reindex
    let K' : KaplanskyDevissage (R := R) (M := (M : Type v)) S :=
      kaplanskyDevissage_of_linearEquiv K.some eX.symm
    exact ⟨S, ⟨K'⟩⟩
  · rintro ⟨S, ⟨K⟩⟩
    let J := {i : S.ToType // (i : Ordinal) + 1 < S}
    let eJ : J ≃ SuccessorIndex S := successorIndexEquiv S
    refine ⟨J,
      (fun α => ModuleCat.of R
        (K.toDirectSumDevissage.toIncreasingDevissage.successorQuotient (eJ α))),
      (fun α => K.countablyGenerated (eJ α)), ?_⟩
    exact ⟨(directSumDevissage_decomposition K.toDirectSumDevissage).some |>.trans
      (DirectSum.lequivCongrLeft R eJ.symm)⟩

private theorem isCountablyGenerated_of_surjective
    {R : Type u} {X Y : Type v} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) (hf : Function.Surjective f)
    (hX : Module.IsCountablyGenerated R X) :
    Module.IsCountablyGenerated R Y := by
  rcases hX with ⟨s, hs, hspan⟩
  refine ⟨f '' s, hs.image f, ?_⟩
  rw [← Submodule.map_span]
  rw [hspan]
  apply top_unique
  rintro y -
  rcases hf y with ⟨x, rfl⟩
  exact ⟨x, trivial, rfl⟩

private theorem isCountablyGenerated_directSum_of_countable
    {R : Type u} {ι : Type v} {N : ι → Type v} [CommRing R]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (hι : Set.Countable (Set.univ : Set ι))
    (hN : ∀ i, Module.IsCountablyGenerated R (N i)) :
    Module.IsCountablyGenerated R (⨁ i, N i) := by
  classical
  let hιcount : Countable ι := Set.countable_univ_iff.mp hι
  let s : Set (⨁ i, N i) :=
    ⋃ i, DirectSum.lof R ι N i '' (Classical.choose (hN i))
  have hs : s.Countable := by
    dsimp [s]
    apply Set.countable_iUnion
    intro i
    exact (Classical.choose_spec (hN i)).1.image _
  refine ⟨s, hs, ?_⟩
  apply top_unique
  intro x hx
  clear hx
  change x ∈ Submodule.span R s
  induction x using DirectSum.induction_on with
  | zero => exact zero_mem _
  | of i x =>
      have hx : x ∈ Submodule.span R (Classical.choose (hN i)) :=
        by rw [(Classical.choose_spec (hN i)).2]; trivial
      have hmap : DirectSum.lof R ι N i x ∈
          (Submodule.span R (Classical.choose (hN i))).map
            (DirectSum.lof R ι N i) :=
        Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      have hspan : DirectSum.lof R ι N i x ∈
          Submodule.span R
            (DirectSum.lof R ι N i '' (Classical.choose (hN i))) := by
        rw [← Submodule.map_span]
        exact hmap
      exact (Submodule.span_mono (by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩)) hspan
  | add x y hx hy => exact (Submodule.span R s).add_mem hx hy

/-! ## Direct summands and projective modules -/

/-- A direct summand of a direct sum of countably generated modules is again a
direct sum of countably generated modules. -/
theorem isDirectSumOfCountablyGeneratedModules_of_isComplemented
    {R : Type u} {M P : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (hM : IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R M))
    (hP : ∃ Q : Submodule R M,
      IsComplemented Q ∧ Nonempty (P ≃ₗ[R] Q)) :
    IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R P) := by
  classical
  rcases hM with ⟨ι, N, hN, ⟨eM⟩⟩
  rcases hP with ⟨Q, ⟨C, hQC⟩, ⟨eP⟩⟩
  let X : Type v := ⨁ i : ι, (N i : Type v)
  let proj : M →ₗ[R] Q := Q.projectionOnto C hQC
  let toQ : X →ₗ[R] Q := proj.comp eM.symm.toLinearMap
  let toX : X →ₗ[R] X :=
    eM.toLinearMap.comp ((Q.subtype.comp proj).comp eM.symm.toLinearMap)
  have hproj (x : Q) : proj (x : M) = x := by
    exact Submodule.projectionOnto_apply_left hQC x
  have htoX_apply (x : X) :
      toX x = eM (Q.subtype (toQ x)) := by
    rfl
  let gen : ∀ i : ι, Set (N i) := fun i => Classical.choose (hN i)
  have hgen (i : ι) : Submodule.span R (gen i) = ⊤ :=
    Classical.choose_spec (hN i) |>.2
  let rel : ι → Set ι := fun i =>
    ⋃ x ∈ gen i, (toX (DirectSum.lof R ι (fun i => (N i : Type v)) i x)).support
  have hrel_countable (i : ι) : (rel i).Countable := by
    dsimp [rel]
    apply Set.Countable.biUnion (Classical.choose_spec (hN i) |>.1)
    intro x hx
    exact Finset.countable_toSet _
  have hsupport (i : ι) (x : (N i : Type v))
      (hx : x ∈ Submodule.span R (gen i)) :
      ∀ j, j ∉ rel i → toX (DirectSum.lof R ι (fun i => (N i : Type v)) i x) j = 0 := by
    refine Submodule.span_induction (s := gen i) (p := fun x _ =>
      ∀ j, j ∉ rel i →
        toX (DirectSum.lof R ι (fun i => (N i : Type v)) i x) j = 0) ?_ ?_ ?_ ?_ hx
    · intro x hx j hj
      by_contra hne
      apply hj
      exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hx,
        DFinsupp.mem_support_iff.mpr hne⟩⟩
    · intro j hj
      simp
    · intro x y hx hy ihx ihy j hj
      have hlof : DirectSum.lof R ι (fun i => (N i : Type v)) i (x + y) =
          DirectSum.lof R ι (fun i => (N i : Type v)) i x +
            DirectSum.lof R ι (fun i => (N i : Type v)) i y := by
        exact map_add _ _ _
      rw [hlof, map_add]
      change toX (DirectSum.lof R ι (fun i => (N i : Type v)) i x) j +
          toX (DirectSum.lof R ι (fun i => (N i : Type v)) i y) j = 0
      rw [ihx j hj, ihy j hj, add_zero]
    · intro a x hx ih j hj
      have hlof : DirectSum.lof R ι (fun i => (N i : Type v)) i (a • x) =
          a • DirectSum.lof R ι (fun i => (N i : Type v)) i x := by
        exact map_smul _ _ _
      rw [hlof, map_smul]
      change a • toX (DirectSum.lof R ι (fun i => (N i : Type v)) i x) j = 0
      rw [ih j hj, smul_zero]
  let reach : Set ι → ℕ → Set ι := fun A n =>
    Nat.rec A (fun _ S => ⋃ i ∈ S, rel i) n
  let closure : Set ι → Set ι := fun A => ⋃ n, reach A n
  have hreach_countable : ∀ (A : Set ι), A.Countable →
      ∀ n, (reach A n).Countable := by
    intro A hA n
    induction n with
    | zero => simpa [reach] using hA
    | succ n ih =>
        dsimp [reach] at *
        exact ih.biUnion (fun i hi => hrel_countable i)
  have hclosure_singleton (i : ι) : (closure ({i} : Set ι)).Countable := by
    dsimp [closure]
    exact Set.countable_iUnion (fun n => hreach_countable _ (Set.countable_singleton i) n)
  have hreach_mono {A B : Set ι} (hAB : A ⊆ B) :
      ∀ n, reach A n ⊆ reach B n := by
    intro n
    induction n with
    | zero => exact hAB
    | succ n ih =>
        intro j hj
        dsimp [reach] at hj ⊢
        rcases Set.mem_iUnion.1 hj with ⟨i, hi⟩
        rcases Set.mem_iUnion.1 hi with ⟨hiA, hij⟩
        exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨ih hiA, hij⟩⟩
  have hclosure_mono {A B : Set ι} (hAB : A ⊆ B) :
      closure A ⊆ closure B := by
    intro i hi
    rcases Set.mem_iUnion.1 hi with ⟨n, hn⟩
    exact Set.mem_iUnion.2 ⟨n, hreach_mono hAB n hn⟩
  have hclosure_closed (A : Set ι) {i : ι} (hi : i ∈ closure A) :
      rel i ⊆ closure A := by
    intro j hj
    rcases Set.mem_iUnion.1 hi with ⟨n, hn⟩
    exact Set.mem_iUnion.2 ⟨n + 1, by
      dsimp [reach]
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hn, hj⟩⟩⟩
  have hclosure_union_singleton (A : Set ι) (i : ι) :
      closure (A ∪ {i}) ⊆ closure A ∪ closure ({i} : Set ι) := by
    have hiter : ∀ n, reach (A ∪ {i}) n ⊆
        closure A ∪ closure ({i} : Set ι) := by
      intro n
      induction n with
      | zero =>
          intro j hj
          rcases hj with hj | hj
          · exact Or.inl (Set.mem_iUnion.2 ⟨0, hj⟩)
          · exact Or.inr (Set.mem_iUnion.2 ⟨0, hj⟩)
      | succ n ih =>
          intro j hj
          dsimp [reach] at hj
          rcases Set.mem_iUnion.1 hj with ⟨k, hk⟩
          rcases Set.mem_iUnion.1 hk with ⟨hk', hkj⟩
          rcases ih hk' with hkA | hki
          · exact Or.inl (hclosure_closed A hkA hkj)
          · exact Or.inr (hclosure_closed ({i} : Set ι) hki hkj)
    intro j hj
    rcases Set.mem_iUnion.1 hj with ⟨n, hn⟩
    exact hiter n hn
  have hclosure_anchor (A : Set ι) :
      closure A ⊆ ⋃ j ∈ A, closure ({j} : Set ι) := by
    have hreach_anchor : ∀ n, reach A n ⊆ ⋃ j ∈ A, closure ({j} : Set ι) := by
      intro n
      induction n with
      | zero =>
          intro j hj
          have hjA : j ∈ A := by simpa [reach] using hj
          exact Set.mem_iUnion.2 ⟨j,
            Set.mem_iUnion.2 ⟨hjA,
              Set.mem_iUnion.2 ⟨0, by simp [reach]⟩⟩⟩
      | succ n ih =>
          intro k hk
          dsimp [reach] at hk
          rcases Set.mem_iUnion.1 hk with ⟨j, hj⟩
          rcases Set.mem_iUnion.1 hj with ⟨hjA, hkj⟩
          rcases Set.mem_iUnion.1 (ih hjA) with ⟨a, ha⟩
          rcases Set.mem_iUnion.1 ha with ⟨haA, hja⟩
          exact Set.mem_iUnion.2 ⟨a,
            Set.mem_iUnion.2 ⟨haA,
              hclosure_closed ({a} : Set ι) hja hkj⟩⟩
    intro i hi
    rcases Set.mem_iUnion.1 hi with ⟨n, hn⟩
    exact hreach_anchor n hn
  have hfilter_preserve (A : Set ι) (hA : ∀ i ∈ A, rel i ⊆ A) (y : X) :
      DFinsupp.filter (fun i => i ∈ A) (toX
        (DFinsupp.filter (fun i => i ∈ A) y)) =
        toX (DFinsupp.filter (fun i => i ∈ A) y) := by
    induction y using DirectSum.induction_on with
    | zero => simp
    | add x y ihx ihy =>
        have hxy := DFinsupp.filter_add (fun i => i ∈ A) x y
        rw [hxy, map_add]
        ext j
        by_cases hj : j ∈ A
        · simp [DFinsupp.filter_apply, hj]
        · have hxj := congrArg (fun z : X => z j) ihx
          have hyj := congrArg (fun z : X => z j) ihy
          rw [DFinsupp.filter_apply, if_neg hj]
          rw [DFinsupp.add_apply]
          rw [← hxj, ← hyj]
          simp [DFinsupp.filter_apply, hj]
    | of i x =>
        by_cases hi : i ∈ A
        · have hxi := hsupport i x (by rw [hgen i]; trivial)
          ext j
          by_cases hj : j ∈ A
          · simp [DFinsupp.filter_apply, hj]
          · have hpj := hxi j
              (fun hrel => hj (hA i hi hrel))
            have hfilter_lof :
                DFinsupp.filter (fun i => i ∈ A)
                  (DirectSum.of (fun i => (N i : Type v)) i x) =
                DirectSum.of (fun i => (N i : Type v)) i x := by
              ext k
              by_cases hk : k ∈ A
              · simp [DFinsupp.filter_apply, hk]
              · have hki : k ≠ i := by
                  intro hki
                  apply hk
                  simpa [hki] using hi
                simp [DFinsupp.filter_apply, hk,
                  DirectSum.of_eq_of_ne (β := fun i => (N i : Type v)) i k x hki]
            rw [hfilter_lof]
            have hpj' :
                toX (DirectSum.of (fun i => (N i : Type v)) i x) j = 0 := by
              exact hpj
            simp [DFinsupp.filter_apply, hj, hpj']
        · ext j
          have hzero :
              DFinsupp.filter (fun i => i ∈ A)
                (DirectSum.of (fun i => (N i : Type v)) i x) = 0 := by
            ext k
            by_cases hk : k ∈ A
            · have hki : k ≠ i := by
                intro hki
                apply hi
                simpa [hki] using hk
              simp [DFinsupp.filter_apply, hk,
                DirectSum.of_eq_of_ne (β := fun i => (N i : Type v)) i k x hki]
            · simp [DFinsupp.filter_apply, hk]
          rw [hzero]
          simp
  let T : Ordinal.{v} := Cardinal.ord (Cardinal.mk ι)
  have hcard : Cardinal.mk T.ToType = Cardinal.mk ι := by
    simp [T]
  let eι : T.ToType ≃ ι := (Cardinal.eq.mp hcard).some
  let S : Ordinal.{v} := T + 1
  let base : Set.Iio S → Set ι := fun α =>
    eι '' {i : T.ToType | (i : Ordinal) < α.1}
  have hbase_mono : Monotone base := by
    intro α β hαβ i hi
    rcases hi with ⟨j, hj, rfl⟩
    refine ⟨j, ?_, rfl⟩
    change (j : Ordinal) < β.1
    exact (show (j : Ordinal) < α.1 from hj).trans_le hαβ
  let closedBase : Set.Iio S → Set ι := fun α => closure (base α)
  let filt : Set.Iio S → X →ₗ[R] X := fun α =>
    DFinsupp.filterLinearMap R (fun i => (N i : Type v))
      (fun i => i ∈ closedBase α)
  let stage : Set.Iio S → Submodule R Q := fun α =>
    LinearMap.range (toQ.comp (filt α))
  have hclosedBase (α : Set.Iio S) : ∀ i ∈ closedBase α, rel i ⊆ closedBase α := by
    intro i hi
    exact hclosure_closed (base α) hi
  have hfilter_mono (A B : Set ι) (hAB : A ⊆ B) (x : X) :
      DFinsupp.filter (fun i => i ∈ B)
          (DFinsupp.filter (fun i => i ∈ A) x) =
        DFinsupp.filter (fun i => i ∈ A) x := by
    ext i
    by_cases hi : i ∈ A
    · simp [DFinsupp.filter_apply, hi, hAB hi]
    · simp [DFinsupp.filter_apply, hi]
  have hstage_mono : Monotone stage := by
    intro α β hαβ q hq
    rcases hq with ⟨x, rfl⟩
    refine ⟨filt α x, ?_⟩
    change toQ (filt β (filt α x)) = toQ (filt α x)
    apply congrArg toQ
    apply hfilter_mono
    apply hclosure_mono
    intro i hi
    rcases hi with ⟨j, hj, rfl⟩
    refine ⟨j, ?_, rfl⟩
    change (j : Ordinal) < β.1
    exact (show (j : Ordinal) < α.1 from hj).trans_le hαβ
  have hstage_zero : stage ⟨0, by simp [S]⟩ = ⊥ := by
    apply le_antisymm
    · rintro q ⟨x, rfl⟩
      have hclosure_empty : closure (∅ : Set ι) = ∅ := by
        have hreach_empty : ∀ n, reach (∅ : Set ι) n = ∅ := by
          intro n
          induction n with
          | zero => simp [reach]
          | succ n ih => simp [reach, ih]
        ext i
        constructor
        · intro hi
          change i ∈ ⋃ n, reach (∅ : Set ι) n at hi
          rcases Set.mem_iUnion.1 hi with ⟨n, hn⟩
          rw [hreach_empty n] at hn
          exact hn
        · intro hi
          simp at hi
      have hzero : filt ⟨0, by simp [S]⟩ x = 0 := by
        change DFinsupp.filter
          (fun i => i ∈ closedBase ⟨0, by simp [S]⟩) x = 0
        have hbase_zero :
            base ⟨0, by simp [S]⟩ = ∅ := by
          ext i
          simp [base]
        rw [show closedBase ⟨0, by simp [S]⟩ = ∅ by
          dsimp [closedBase]
          rw [hbase_zero, hclosure_empty]]
        ext i
        simp [DFinsupp.filter_apply]
      change toQ (filt ⟨0, by simp [S]⟩ x) ∈ (⊥ : Submodule R Q)
      rw [hzero]
      simp
    · exact bot_le
  have hstage_ambient : ∀ α : Set.Iio S, IsComplemented (stage α) := by
    intro α
    let fQ : Q →ₗ[R] Q :=
      toQ.comp ((filt α).comp (eM.toLinearMap.comp Q.subtype))
    have hfQ_mem (x : Q) : fQ x ∈ stage α := by
      refine ⟨eM (x : M), ?_⟩
      rfl
    let f : Q →ₗ[R] stage α := fQ.codRestrict (stage α) hfQ_mem
    have hf (x : stage α) : f x = x := by
      rcases x.property with ⟨y, hy⟩
      apply Subtype.ext
      have hfilter := hfilter_preserve (closedBase α) (hclosedBase α) y
      have hyx : toX (filt α y) = eM (x : M) := by
        rw [htoX_apply]
        rw [show toQ (filt α y) = (x : Q) by exact hy]
        rfl
      have hfilter' : filt α (eM (x : M)) = eM (x : M) := by
        change DFinsupp.filter (fun i => i ∈ closedBase α)
            (eM (x : M)) = eM (x : M)
        rw [← hyx]
        exact hfilter
      change toQ (filt α (eM (x : M))) = (x : Q)
      rw [hfilter']
      simpa [toQ] using hproj x
    exact ⟨LinearMap.ker f, LinearMap.isCompl_of_proj hf⟩
  have hfilter_lof_mem (α : Set.Iio S) (i : ι) (x : (N i : Type v))
      (hi : i ∈ closedBase α) :
      filt α (DirectSum.lof R ι (fun i => (N i : Type v)) i x) =
        DirectSum.lof R ι (fun i => (N i : Type v)) i x := by
    ext k
    change (DFinsupp.filter (fun i => i ∈ closedBase α)
      (DirectSum.lof R ι (fun i => (N i : Type v)) i x)) k =
      (DirectSum.lof R ι (fun i => (N i : Type v)) i x) k
    by_cases hki : k = i
    · subst k
      simp [DFinsupp.filter_apply, hi]
    · by_cases hk : k ∈ closedBase α
      · simp [DFinsupp.filter_apply, hk]
      · have hz :
            DirectSum.lof R ι (fun i => (N i : Type v)) i x k = 0 := by
          rw [DirectSum.lof_eq_of]
          exact DirectSum.of_eq_of_ne (β := fun i => (N i : Type v)) i k x hki
        simp [DFinsupp.filter_apply, hk, hz]
  have hfilter_lof_not_mem (α : Set.Iio S) (i : ι) (x : (N i : Type v))
      (hi : i ∉ closedBase α) :
      filt α (DirectSum.lof R ι (fun i => (N i : Type v)) i x) = 0 := by
    ext k
    change (DFinsupp.filter (fun i => i ∈ closedBase α)
      (DirectSum.lof R ι (fun i => (N i : Type v)) i x)) k = 0
    by_cases hki : k = i
    · subst k
      simp [DFinsupp.filter_apply, hi]
    · by_cases hk : k ∈ closedBase α
      · have hz :
            DirectSum.lof R ι (fun i => (N i : Type v)) i x k = 0 := by
          rw [DirectSum.lof_eq_of]
          exact DirectSum.of_eq_of_ne (β := fun i => (N i : Type v)) i k x hki
        simp [DFinsupp.filter_apply, hk, hz]
      · simp [DFinsupp.filter_apply, hk]
  have hstage_limit :
      ∀ (α : Set.Iio S), Order.IsSuccLimit α.1 →
        stage α = ⨆ β : Set.Iio α.1,
          stage ⟨β.1, by
            change β.1 < S
            exact β.2.trans α.2⟩ := by
    intro α hα
    apply le_antisymm
    · rintro q ⟨y, rfl⟩
      induction y using DirectSum.induction_on with
      | zero =>
          change toQ (filt α 0) ∈ (⨆ β : Set.Iio α.1,
            stage ⟨β.1, by
              change β.1 < S
              exact β.2.trans α.2⟩)
          simp
      | add x y ihx ihy =>
          change toQ (filt α (x + y)) ∈ (⨆ β : Set.Iio α.1,
            stage ⟨β.1, by
              change β.1 < S
              exact β.2.trans α.2⟩)
          rw [map_add, map_add]
          exact add_mem ihx ihy
      | of i x =>
          by_cases hi : i ∈ closedBase α
          · change i ∈ closure (base α) at hi
            rcases Set.mem_iUnion.1 (hclosure_anchor (base α) hi) with ⟨k, hk⟩
            rcases Set.mem_iUnion.1 hk with ⟨hkbase, hik⟩
            rcases hkbase with ⟨j, hj, rfl⟩
            change (j : Ordinal) < α.1 at hj
            let β : Set.Iio α.1 := ⟨(j : Ordinal) + 1, by
              change (j : Ordinal) + 1 < α.1
              simpa only [Order.succ_eq_add_one] using hα.succ_lt hj⟩
            let βS : Set.Iio S := ⟨β.1, by
              change β.1 < S
              exact β.2.trans α.2⟩
            have hjβ : eι j ∈ base βS := by
              refine ⟨j, ?_, rfl⟩
              exact ordinal_lt_add_one (j : Ordinal)
            have hclosed : closure ({eι j} : Set ι) ⊆ closedBase βS := by
              apply hclosure_mono
              intro z hz
              simpa only [Set.mem_singleton_iff] using hz ▸ hjβ
            have hiβ : i ∈ closedBase βS := hclosed hik
            have hβα : βS ≤ α := by
              change βS.1 ≤ α.1
              exact β.2.le
            have hbaseβα : base βS ⊆ base α := hbase_mono hβα
            have hclosedβα : closedBase βS ⊆ closedBase α :=
              hclosure_mono hbaseβα
            have hfilt :
                filt α (DirectSum.lof R ι (fun i => (N i : Type v)) i x) =
                  filt βS (DirectSum.lof R ι (fun i => (N i : Type v)) i x) := by
              exact (hfilter_lof_mem α i x hi).trans
                (hfilter_lof_mem βS i x hiβ).symm
            apply (le_iSup (fun β : Set.Iio α.1 =>
              stage ⟨β.1, by
                change β.1 < S
                exact β.2.trans α.2⟩) β)
            refine ⟨DirectSum.lof R ι (fun i => (N i : Type v)) i x, ?_⟩
            change toQ (filt βS (DirectSum.lof R ι
              (fun i => (N i : Type v)) i x)) =
              toQ (filt α (DirectSum.lof R ι
                (fun i => (N i : Type v)) i x))
            rw [hfilt]
          · have hz := hfilter_lof_not_mem α i x hi
            change toQ (filt α (DirectSum.lof R ι
              (fun i => (N i : Type v)) i x)) ∈
              (⨆ β : Set.Iio α.1,
                stage ⟨β.1, by
                  change β.1 < S
                  exact β.2.trans α.2⟩)
            rw [hz]
            simp
    · refine iSup_le fun β => ?_
      rintro q ⟨y, rfl⟩
      let βS : Set.Iio S := ⟨β.1, by
        change β.1 < S
        exact β.2.trans α.2⟩
      refine ⟨filt βS y, ?_⟩
      change toQ (filt α (filt βS y)) = toQ (filt βS y)
      apply congrArg toQ
      apply hfilter_mono
      exact hclosure_mono (hbase_mono (show βS ≤ α by
        change βS.1 ≤ α.1
        exact β.2.le))
  let αT : Set.Iio S := ⟨T, ordinal_lt_add_one T⟩
  have hbase_top : base αT = Set.univ := by
    ext i
    constructor
    · intro hi
      trivial
    · intro hi
      let j : T.ToType := eι.symm i
      refine ⟨j, ?_, ?_⟩
      exact Ordinal.typein_lt_self j
      exact eι.apply_symm_apply i
  have hclosedBase_top : closedBase αT = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    change i ∈ closure (base αT)
    rw [hbase_top]
    exact Set.mem_iUnion.2 ⟨0, by simp [reach]⟩
  have hfilter_top (x : X) : filt αT x = x := by
    change DFinsupp.filter (fun i => i ∈ closedBase αT) x = x
    rw [hclosedBase_top]
    ext i
    simp [DFinsupp.filter_apply]
  have hstage_top : stage αT = ⊤ := by
    apply top_unique
    intro q hq
    refine ⟨eM (q : M), ?_⟩
    change toQ (filt αT (eM (q : M))) = q
    rw [hfilter_top]
    change proj (eM.symm (eM (q : M))) = q
    simpa using hproj q
  have hstage_union : (⨆ α : Set.Iio S, stage α) = ⊤ := by
    apply top_unique
    rw [← hstage_top]
    exact le_iSup stage αT
  let D : IncreasingDevissage (R := R) (M := (Q : Type v)) S :=
    { stage := stage
      monotone := hstage_mono
      zero_lt := by
        change (0 : Ordinal.{v}) < T + 1
        exact Order.bot_lt_succ T
      zero := hstage_zero
      union_eq_top := hstage_union
      limit := hstage_limit }
  have hsucc : D.isSuccessorComplemented := by
    apply (D.isSuccessorComplemented_iff_isAmbientlyComplemented).2
    exact hstage_ambient
  have hcount : ∀ α : SuccessorIndex S,
      Module.IsCountablyGenerated R (D.successorQuotient α) := by
    intro α
    let β₀ : Set.Iio S := ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩
    let β₁ : Set.Iio S := ⟨α.1 + 1, α.2⟩
    let W : Submodule R Q := stage β₁
    let p : Submodule R W := D.successorSubmodule α
    let A : Set ι := closedBase β₀
    let B : Set ι := closedBase β₁
    let hαT : α.1 < T := by
      simpa only [Order.succ_eq_add_one] using Order.succ_lt_succ_iff.mp α.2
    let iα : T.ToType := Ordinal.ToType.mk ⟨α.1, hαT⟩
    have hiα : (iα : Ordinal) = α.1 := by simp [iα]
    have hAB : A ⊆ B := by
      dsimp [A, B]
      exact hclosure_mono (hbase_mono (show β₀ ≤ β₁ from
        (ordinal_lt_add_one α.1).le))
    have hbase_succ : base β₁ ⊆ base β₀ ∪ {eι iα} := by
      intro k hk
      rcases hk with ⟨j, hj, rfl⟩
      have hjle : (j : Ordinal) ≤ α.1 := by
        apply Order.le_of_lt_succ
        simpa [β₁] using hj
      rcases lt_or_eq_of_le hjle with hjlt | hjEq
      · exact Or.inl ⟨j, hjlt, rfl⟩
      · have hjeq : j = iα := by
          apply (Ordinal.ToType.mk.symm.injective)
          apply Subtype.ext
          simpa [hiα] using hjEq
        subst j
        exact Or.inr rfl
    have hBsub : B ⊆ A ∪ closure ({eι iα} : Set ι) := by
      dsimp [A, B]
      exact (hclosure_mono hbase_succ).trans
        (hclosure_union_singleton (base β₀) (eι iα))
    let J : Set ι := B \ A
    have hJsub : J ⊆ closure ({eι iα} : Set ι) := by
      intro j hj
      rcases hBsub hj.1 with hjA | hjC
      · exact False.elim (hj.2 hjA)
      · exact hjC
    have hJcount : J.Countable :=
      (hclosure_singleton (eι iα)).mono hJsub
    let wmap : X →ₗ[R] W :=
      (toQ.comp (filt β₁)).codRestrict W (fun x => ⟨x, rfl⟩)
    let qmap : W →ₗ[R] (W ⧸ p) := Submodule.mkQ p
    let qcoord : ∀ j : J, (N j.1 : Type v) →ₗ[R] (W ⧸ p) := fun j =>
      qmap.comp (wmap.comp
        (DirectSum.lof R ι (fun i => (N i : Type v)) j.1))
    let g : (⨁ j : J, (N j.1 : Type v)) →ₗ[R] (W ⧸ p) :=
      DirectSum.toModule R J (W ⧸ p) qcoord
    let filterJ : X →ₗ[R] X :=
      DFinsupp.filterLinearMap R (fun i => (N i : Type v)) (fun i => i ∈ J)
    let qJ : X →ₗ[R] (W ⧸ p) := qmap.comp (wmap.comp filterJ)
    have hfilter_set_lof (E : Set ι) (i : ι) (x : (N i : Type v))
        (hi : i ∈ E) :
        DFinsupp.filter (fun i => i ∈ E)
            (DirectSum.lof R ι (fun i => (N i : Type v)) i x) =
          DirectSum.lof R ι (fun i => (N i : Type v)) i x := by
      ext k
      by_cases hki : k = i
      · subst k
        simp [DFinsupp.filter_apply, hi]
      · by_cases hk : k ∈ E
        · simp [DFinsupp.filter_apply, hk]
        · have hz :
              DirectSum.lof R ι (fun i => (N i : Type v)) i x k = 0 := by
            rw [DirectSum.lof_eq_of]
            exact DirectSum.of_eq_of_ne
              (β := fun i => (N i : Type v)) i k x hki
          simp [DFinsupp.filter_apply, hk, hz]
    have hfilter_set_lof_not_mem (E : Set ι) (i : ι) (x : (N i : Type v))
        (hi : i ∉ E) :
        DFinsupp.filter (fun i => i ∈ E)
            (DirectSum.lof R ι (fun i => (N i : Type v)) i x) = 0 := by
      ext k
      by_cases hki : k = i
      · subst k
        simp [DFinsupp.filter_apply, hi]
      · by_cases hk : k ∈ E
        · have hz :
              DirectSum.lof R ι (fun i => (N i : Type v)) i x k = 0 := by
            rw [DirectSum.lof_eq_of]
            exact DirectSum.of_eq_of_ne
              (β := fun i => (N i : Type v)) i k x hki
          simp [DFinsupp.filter_apply, hk, hz]
        · simp [DFinsupp.filter_apply, hk]
    have hfilter_add (y : X) :
        filt β₁ y = filt β₀ y + filterJ y := by
      ext i
      rw [DFinsupp.add_apply]
      by_cases hiB : i ∈ B
      · by_cases hiA : i ∈ A
        · have hiB' : i ∈ B := hiB
          simp [filt, filterJ, DFinsupp.filterLinearMap,
            DFinsupp.filter_apply, A, B, J, hiA, hiB']
        · simp [filt, filterJ, DFinsupp.filterLinearMap,
            DFinsupp.filter_apply, A, B, J, hiA, hiB]
      · have hiA : i ∉ A := by
          intro hiA
          exact hiB (hAB hiA)
        simp [filt, filterJ, DFinsupp.filterLinearMap,
          DFinsupp.filter_apply, A, B, J, hiA, hiB]
    have hfilter_J_mem (y : X) :
        filt β₁ (filterJ y) = filterJ y := by
      change DFinsupp.filter (fun i => i ∈ B)
          (DFinsupp.filter (fun i => i ∈ J) y) =
        DFinsupp.filter (fun i => i ∈ J) y
      ext i
      by_cases hi : i ∈ J
      · have hiB : i ∈ B := hi.1
        simp [DFinsupp.filter_apply, hi, hiB]
      · simp [DFinsupp.filter_apply, hi]
    have hqJ_range (y : X) : ∃ d, g d = qJ y := by
      induction y using DirectSum.induction_on with
      | zero => exact ⟨0, by simp [g, qJ]⟩
      | add x y ihx ihy =>
          rcases ihx with ⟨dx, hdx⟩
          rcases ihy with ⟨dy, hdy⟩
          refine ⟨dx + dy, ?_⟩
          rw [map_add, map_add, hdx, hdy]
      | of i x =>
          by_cases hi : i ∈ J
          · let j : J := ⟨i, hi⟩
            have hcoord : qJ (DirectSum.lof R ι
                (fun i => (N i : Type v)) i x) = qcoord j x := by
              have hfilter' : filterJ (DirectSum.lof R ι
                  (fun i => (N i : Type v)) i x) =
                  DirectSum.lof R ι (fun i => (N i : Type v)) i x := by
                change DFinsupp.filter (fun i => i ∈ J)
                    (DirectSum.lof R ι (fun i => (N i : Type v)) i x) = _
                ext k
                by_cases hki : k = i
                · subst k
                  simp [DFinsupp.filter_apply, hi]
                · by_cases hk : k ∈ J
                  · simp [DFinsupp.filter_apply, hk]
                  · have hz :
                        DirectSum.lof R ι (fun i => (N i : Type v)) i x k = 0 := by
                      rw [DirectSum.lof_eq_of]
                      exact DirectSum.of_eq_of_ne
                        (β := fun i => (N i : Type v)) i k x hki
                    simp [DFinsupp.filter_apply, hk, hz]
              change qmap (wmap (filterJ (DirectSum.lof R ι
                  (fun i => (N i : Type v)) i x))) = qcoord j x
              rw [hfilter']
              rfl
            refine ⟨DirectSum.lof R J (fun j => (N j.1 : Type v)) j x, ?_⟩
            rw [DirectSum.toModule_lof]
            rw [← DirectSum.lof_eq_of R ι (fun i => (N i : Type v)) i x]
            exact hcoord.symm
          · have hz := hfilter_set_lof_not_mem J i x hi
            refine ⟨0, ?_⟩
            have hfilter0 : filterJ (DirectSum.of (fun i => (N i : Type v)) i x) = 0 := by
              change DFinsupp.filter (fun i => i ∈ J)
                  (DirectSum.of (fun i => (N i : Type v)) i x) = 0
              ext k
              by_cases hki : k = i
              · subst k
                simp [DFinsupp.filter_apply, hi]
              · by_cases hk : k ∈ J
                · have hz0 :
                      DirectSum.of (fun i => (N i : Type v)) i x k = 0 := by
                    exact DirectSum.of_eq_of_ne
                      (β := fun i => (N i : Type v)) i k x hki
                  simp [DFinsupp.filter_apply, hk, hz0]
                · simp [DFinsupp.filter_apply, hk]
            change g 0 = qmap (wmap
              (filterJ (DirectSum.of (fun i => (N i : Type v)) i x)))
            rw [hfilter0]
            simp
    have hg_surj : Function.Surjective g := by
      intro z
      have hqmap : Function.Surjective qmap := Submodule.mkQ_surjective p
      rcases hqmap z with ⟨w, rfl⟩
      rcases w.property with ⟨y, hy⟩
      have hfilt : filt β₁ (filt β₀ y) = filt β₀ y := by
        change DFinsupp.filter (fun i => i ∈ B)
            (DFinsupp.filter (fun i => i ∈ A) y) =
          DFinsupp.filter (fun i => i ∈ A) y
        exact hfilter_mono A B hAB y
      have hw : toQ (filt β₀ y) ∈ W := by
        change toQ (filt β₀ y) ∈ stage β₁
        refine ⟨filt β₀ y, ?_⟩
        change toQ (filt β₁ (filt β₀ y)) = toQ (filt β₀ y)
        rw [hfilt]
      have hp : (⟨toQ (filt β₀ y), hw⟩ : W) ∈ p := by
        change toQ (filt β₀ y) ∈ stage β₀
        exact ⟨y, rfl⟩
      have hzero : qmap ⟨toQ (filt β₀ y), hw⟩ = 0 := by
        change (Submodule.mkQ p) ⟨toQ (filt β₀ y), hw⟩ = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hp
      have hw_map : w = wmap y := by
        apply Subtype.ext
        exact hy.symm
      have hmap_add : wmap y =
          (⟨toQ (filt β₀ y), hw⟩ : W) + wmap (filterJ y) := by
        apply Subtype.ext
        change toQ (filt β₁ y) =
          toQ (filt β₀ y) + toQ (filt β₁ (filterJ y))
        rw [hfilter_add y, map_add, hfilter_J_mem y]
      have heq : qmap w = qJ y := by
        rw [hw_map]
        change qmap (wmap y) = qmap (wmap (filterJ y))
        rw [hmap_add, map_add, hzero, zero_add]
      rcases hqJ_range y with ⟨d, hd⟩
      exact ⟨d, hd.trans heq.symm⟩
    have hdomain : Module.IsCountablyGenerated R
        (⨁ j : J, (N j.1 : Type v)) := by
      apply isCountablyGenerated_directSum_of_countable
        (hι := @Set.countable_univ J hJcount.to_subtype)
      intro j
      exact hN j.1
    have hquot : Module.IsCountablyGenerated R (W ⧸ p) :=
      isCountablyGenerated_of_surjective g hg_surj hdomain
    change Module.IsCountablyGenerated R (W ⧸ p)
    exact hquot
  let K : KaplanskyDevissage (R := R) (M := (Q : Type v)) S :=
    { toDirectSumDevissage :=
        { toIncreasingDevissage := D
          successor := hsucc }
      countablyGenerated := by
        intro α
        exact hcount α }
  exact (isDirectSumOfCountablyGeneratedModules_iff_hasKaplanskyDevissage
    (ModuleCat.of R P)).2 ⟨S, ⟨kaplanskyDevissage_of_linearEquiv K eP.symm⟩⟩

/- A complemented submodule, equivalently the image of a split idempotent,
   inherits the Kaplansky dévissage property.  The complemented submodule
   formulation keeps the induction invariant at the level of the existing
   `KaplanskyDevissage`/`IncreasingDevissage` interfaces. -/
theorem hasKaplanskyDevissage_of_isComplemented
    {R : Type u} {M P : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (hM : HasKaplanskyDevissage (ModuleCat.of R M))
    (hP : ∃ Q : Submodule R M,
      IsComplemented Q ∧ Nonempty (P ≃ₗ[R] Q)) :
    HasKaplanskyDevissage (ModuleCat.of R P) := by
  rw [← isDirectSumOfCountablyGeneratedModules_iff_hasKaplanskyDevissage] at hM ⊢
  exact isDirectSumOfCountablyGeneratedModules_of_isComplemented hM hP

/-- Every projective module is a direct sum of countably generated projective
modules. -/
theorem projective_isDirectSumOfCountablyGeneratedProjectiveModules
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] :
    IsDirectSumOfCountablyGeneratedProjectiveModules (ModuleCat.of R M) := by
  classical
  let F : Type v := ⨁ x : M, (Submodule.span R ({x} : Set M) : Type v)
  let f : F →ₗ[R] M :=
    DirectSum.toModule R M M (fun x =>
      (Submodule.span R ({x} : Set M)).subtype)
  have hf : Function.Surjective f := by
    intro m
    let xm : (Submodule.span R ({m} : Set M) : Type v) :=
      ⟨m, Submodule.subset_span (by simp)⟩
    refine ⟨DirectSum.lof R M
      (fun x => (Submodule.span R ({x} : Set M) : Type v)) m xm, ?_⟩
    change DirectSum.toModule R M M (fun x =>
      (Submodule.span R ({x} : Set M)).subtype)
        (DirectSum.lof R M
          (fun x => (Submodule.span R ({x} : Set M) : Type v)) m xm) = m
    rw [DirectSum.toModule_lof]
    rfl
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property f (LinearMap.id : M →ₗ[R] M) hf
  let Q : Submodule R F := LinearMap.range g
  let p : F →ₗ[R] Q :=
    (g.comp f).codRestrict Q (fun x => ⟨f x, rfl⟩)
  have hp (x : Q) : p x = x := by
    rcases x.property with ⟨y, hy⟩
    apply Subtype.ext
    change g (f (x : F)) = (x : F)
    have hx : (x : F) = g y := hy.symm
    rw [hx, show f (g y) = y by exact LinearMap.congr_fun hg y]
  have hcomp : IsComplemented Q :=
    ⟨LinearMap.ker p, LinearMap.isCompl_of_proj hp⟩
  let ge : M →ₗ[R] Q :=
    g.codRestrict Q (fun x => ⟨x, rfl⟩)
  let se : Q →ₗ[R] M := f.comp Q.subtype
  have hleft : se.comp ge = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change f (g x) = x
    exact LinearMap.congr_fun hg x
  have hright : ge.comp se = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rcases x.property with ⟨y, hy⟩
    have hx : (x : F) = g y := hy.symm
    change g (f (x : F)) = (x : F)
    rw [hx, show f (g y) = y by exact LinearMap.congr_fun hg y]
  let e : M ≃ₗ[R] Q :=
    LinearEquiv.ofBijective ge ⟨
      (by
        intro x y hxy
        calc
          x = se (ge x) := (LinearMap.congr_fun hleft x).symm
          _ = se (ge y) := congrArg se hxy
          _ = y := LinearMap.congr_fun hleft y),
      (by
        intro x
        refine ⟨se x, ?_⟩
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun hright x)⟩
  have hM : IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R M) :=
    isDirectSumOfCountablyGeneratedModules_of_isComplemented (M := F) (P := M)
      (by
        refine ⟨M, (fun x => ModuleCat.of R
          (Submodule.span R ({x} : Set M) : Type v)), ?_, ?_⟩
        · intro x
          have hcyclic (x : M) :
              Module.IsCountablyGenerated R
                (Submodule.span R ({x} : Set M) : Type v) := by
            let xgen : (Submodule.span R ({x} : Set M) : Type v) :=
              ⟨x, Submodule.subset_span (by simp)⟩
            refine ⟨({xgen} : Set _), Set.countable_singleton _, ?_⟩
            apply top_unique
            intro y _
            change y ∈ Submodule.span R ({xgen} : Set _)
            refine Submodule.span_induction
              (p := fun z hz => (⟨z, hz⟩ :
                (Submodule.span R ({x} : Set M) : Type v)) ∈
                  Submodule.span R ({xgen} : Set _)) ?_ ?_ ?_ ?_ y.property
            · intro z hz
              rcases hz with rfl
              exact Submodule.subset_span rfl
            · exact Submodule.zero_mem _
            · intro z w hz hw hz' hw'
              exact Submodule.add_mem _ hz' hw'
            · intro a z hz hz'
              exact Submodule.smul_mem _ a hz'
          simpa using hcyclic x
        · exact ⟨LinearEquiv.refl R F⟩)
      ⟨Q, hcomp, ⟨e⟩⟩
  rcases hM with ⟨ι, N, hN, ⟨eM⟩⟩
  refine ⟨ι, N, ?_, ⟨eM⟩⟩
  intro i
  refine ⟨hN i, ?_⟩
  let inc : (N i : Type v) →ₗ[R] M :=
    eM.symm.toLinearMap.comp
      (DirectSum.lof R ι (fun j => (N j : Type v)) i)
  let proj : M →ₗ[R] (N i : Type v) :=
    (DirectSum.component R ι (fun j => (N j : Type v)) i).comp eM.toLinearMap
  apply Module.Projective.of_split inc proj
  apply LinearMap.ext
  intro x
  change DirectSum.component R ι (fun j => (N j : Type v)) i
      (eM (eM.symm (DirectSum.lof R ι (fun j => (N j : Type v)) i x))) = x
  rw [eM.apply_symm_apply]
  exact DirectSum.component.lof_self (R := R)
    (M := fun j => (N j : Type v)) i x

end

end Formalization.Books.Algebra.Unit84
