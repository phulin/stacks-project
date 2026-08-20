import Formalization.Books.Algebra.Unit69.QuasiRegularSequences
import Formalization.Books.Algebra.Unit96.Completion
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative Algebra, Chapter 97: Completion for Noetherian rings

The source's completion is Mathlib's `AdicCompletion`.  The declarations in
this file record the Noetherian exactness, flatness, completeness, finite
extension, and splitting statements from the source section.
-/

namespace Formalization.Books.Algebra.Unit97

open scoped TensorProduct
open Formalization.Books.Algebra.Unit96

universe u v w

noncomputable section

/-! ## Exactness and tensor products -/

/- The source's completion map is the canonical `AdicCompletion.map`. -/

theorem completion_map_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {K N : Type u} [AddCommGroup K] [AddCommGroup N]
    [Module R K] [Module R N] [Module.Finite R K] [Module.Finite R N]
    (f : K →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (AdicCompletion.map I f) := by
  exact AdicCompletion.map_injective I hf

/- The three clauses of `lemma-completion-tensor`, expressed with the
   canonical linear maps on completions. -/
theorem completion_short_exact
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {K M N : Type u} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [Module R K] [Module R M] [Module R N]
    [Module.Finite R K] [Module.Finite R M] [Module.Finite R N]
    (f : K →ₗ[R] M) (g : M →ₗ[R] N)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Injective (AdicCompletion.map I f) ∧
      Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
        Function.Surjective (AdicCompletion.map I g) := by
  exact ⟨AdicCompletion.map_injective I hf,
    AdicCompletion.map_exact (I := I) hf hfg hg,
    AdicCompletion.map_surjective I hg⟩

/- The displayed tensor order in the source is related to Mathlib's canonical
   order by `TensorProduct.comm`; Unit96 exposes both maps. -/
theorem completion_tensor_bijective
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (completionTensorMapCanonical I M) := by
  exact AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M

theorem completion_tensor_bijective_source_order
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (completionTensorMap I M) := by
  exact (completion_tensor_bijective I M).comp
    (TensorProduct.comm R M (ringCompletion I)).bijective

/-! ## Flatness and faithful flatness -/

theorem completion_flat
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    RingHom.Flat (algebraMap R (ringCompletion I)) := by
  exact (RingHom.flat_algebraMap_iff).mpr inferInstance

/- Exactness on finite modules is the source's functorial formulation of the
   short-exact statement above. -/
theorem completion_exact_on_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {K M N : Type u} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [Module R K] [Module R M] [Module R N]
    [Module.Finite R K] [Module.Finite R M] [Module.Finite R N]
    {f : K →ₗ[R] M} {g : M →ₗ[R] N}
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) := by
  exact AdicCompletion.map_exact (I := I) hf hfg hg

theorem completion_faithfully_flat
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R) :
    RingHom.FaithfullyFlat (algebraMap R (ringCompletion I)) := by
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, ?_⟩
  intro J hJ h
  have hmap : J.map (algebraMap R (ringCompletion I)) = (⊤ : Ideal (ringCompletion I)) := by
    simpa [Ideal.smul_top_eq_map] using h
  have hq : J.map (Ideal.Quotient.mk I) = (⊤ : Ideal (R ⧸ I)) := by
    have h' := congrArg (Ideal.map (AdicCompletion.evalOneₐ I).toRingHom) hmap
    rw [Ideal.map_map] at h'
    rw [AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk] at h'
    rw [Ideal.map_top] at h'
    exact h'
  have hsup : J ⊔ I = (⊤ : Ideal R) := by
    have hc := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hq
    rw [Ideal.comap_top, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker] at hc
    simpa [sup_comm] using hc
  obtain ⟨m, hm, hJm⟩ := J.exists_le_maximal hJ
  have hIm : I ≤ m := hI.trans (@Ring.jacobson_le_of_isMaximal R _ m hm)
  apply hm.ne_top
  apply top_unique
  rw [← hsup]
  exact sup_le hJm hIm

theorem local_completion_faithfully_flat
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    RingHom.FaithfullyFlat
      (algebraMap R (ringCompletion (IsLocalRing.maximalIdeal R))) := by
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-! ## Completeness and Noetherianity -/

theorem completion_is_adic_complete
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsAdicComplete I (completion I M) := by
  exact AdicCompletion.isAdicComplete I.fg_of_isNoetherianRing

/- This is the canonical inclusion of the completion of `I^n M` into the
   completion of `M`; it is the source's assertion `I^n M^ = (I^n M)^`. -/
theorem completion_power_submodule_eq_range
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    I ^ n • (⊤ : Submodule R (completion I M)) =
      (AdicCompletion.ofPowSMul I M n).range.restrictScalars R := by
  rw [completion_pow_smul_eq_kernel_eval I M I.fg_of_isNoetherianRing n,
    completion_of_power_range_eq_kernel_eval I M n]

/- The quotient assertion `M^/I^n M^ = M/I^n M`, with the canonical
   evaluation map recording the identification. -/
theorem completion_quotient_power_equiv
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    ∃ e :
        (completion I M ⧸ (I ^ n • (⊤ : Submodule R (completion I M))))
          ≃ₗ[R] (M ⧸ (I ^ n • (⊤ : Submodule R M))),
      ∀ x : completion I M,
        e (Submodule.Quotient.mk x) = AdicCompletion.eval I M n x := by
  let f := AdicCompletion.eval I M n
  have hker : I ^ n • (⊤ : Submodule R (completion I M)) = f.ker := by
    calc
      I ^ n • (⊤ : Submodule R (completion I M)) =
          (AdicCompletion.ofPowSMul I M n).range.restrictScalars R :=
        completion_power_submodule_eq_range I M n
      _ = f.ker := completion_of_power_range_eq_kernel_eval I M n
  let e := (Submodule.quotEquivOfEq _ _ hker).trans
    (f.quotKerEquivOfSurjective (AdicCompletion.eval_surjective I M n))
  refine ⟨e, ?_⟩
  intro x
  simp [e, f]

theorem completion_is_noetherian_of_fg_quotient
    {R : Type u} [CommRing R] (I : Ideal R)
    [IsNoetherianRing (R ⧸ I)] (hI : I.FG) :
    IsNoetherianRing (ringCompletion I) ∧
      IsAdicComplete
        (I.map (algebraMap R (ringCompletion I))) (ringCompletion I) := by
  let K : Ideal (ringCompletion I) := I.map (algebraMap R (ringCompletion I))
  have hKcomplete : IsAdicComplete K (ringCompletion I) := by
    simpa [K] using (AdicCompletion.isAdicComplete_self I hI)
  have hKnoetherian : IsNoetherianRing ((ringCompletion I) ⧸ K) := by
    obtain ⟨e, _⟩ := Unit96.completion_quotient_power_equiv I hI 1
    have hKpow : K = Unit96.completionPowerIdeal I 1 := by
      simp [K, Unit96.completionPowerIdeal]
    let e' : (R ⧸ I) ≃+* ((ringCompletion I) ⧸ K) :=
      (Ideal.quotEquivOfEq (show I = I ^ 1 by simp)).trans
        (e.symm.toRingEquiv.trans (Ideal.quotEquivOfEq hKpow.symm))
    exact isNoetherianRing_of_ringEquiv (R ⧸ I) e'
  refine ⟨?_, ?_⟩
  · letI : IsNoetherianRing ((ringCompletion I) ⧸ K) := hKnoetherian
    letI : IsAdicComplete K (ringCompletion I) := hKcomplete
    exact Unit69.isNoetherianRing_of_isAdicComplete_of_fg_quotient K
      (hI.map (algebraMap R (ringCompletion I)))
  · simpa [K] using hKcomplete

theorem completion_is_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (ringCompletion I) := by
  exact (completion_is_noetherian_of_fg_quotient I
    I.fg_of_isNoetherianRing).1

/-! ## Local completions -/

/- The source warns that the completion at the maximal ideal of `S` need not
   be the completion at the extended maximal ideal of `R`. -/
def LocalCompletionAgreement
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] : Prop :=
  Nonempty
    (completion (IsLocalRing.maximalIdeal S) S ≃ₐ[S]
      completion
        ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) S)

private theorem completion_factorPow_eval
    {R : Type u} [CommRing R] (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : ringCompletion I) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  let hn : (I ^ n • (⊤ : Submodule R R)) ≤ I ^ n :=
    le_of_eq (Ideal.mul_top _)
  let hm : (I ^ m • (⊤ : Submodule R R)) ≤ I ^ m :=
    le_of_eq (Ideal.mul_top _)
  have hfac : ∀ (y : R ⧸ (I ^ n • (⊤ : Submodule R R))),
      Ideal.Quotient.factorPow I hmn (Submodule.factor hn y) =
        Submodule.factor hm (AdicCompletion.transitionMap I R hmn y) := by
    intro y
    induction y using Quotient.inductionOn' with
    | _ r => rfl
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x hn]
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x hm]
  rw [hfac]
  exact congrArg (fun z => Submodule.factor hm z)
    (AdicCompletion.transitionMap_comp_eval_apply I R hmn x)

private noncomputable def completion_algHom_of_power_le
    {R : Type u} [CommRing R] (I J : Ideal R) (c : ℕ)
    (hIJ : I ^ c ≤ J) :
    AdicCompletion I R →ₐ[R] AdicCompletion J R := by
  have hpow (n : ℕ) : I ^ (c * n) ≤ J ^ n := by
    simpa [pow_mul] using (Ideal.pow_right_mono hIJ n)
  let f : (n : ℕ) → AdicCompletion I R →ₐ[R] R ⧸ J ^ n :=
    fun n => (Ideal.Quotient.factorₐ R (hpow n)).comp
      (AdicCompletion.evalₐ I (c * n))
  have hf : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (f n) = f m := by
    intro m n hmn
    have hcmn : c * m ≤ c * n := Nat.mul_le_mul_left c hmn
    have hmap :
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
            (Ideal.Quotient.factorₐ R (hpow n)) =
          (Ideal.Quotient.factorₐ R (hpow m)).comp
            (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hcmn)) := by
      apply AlgHom.ext
      intro y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl
    apply AlgHom.ext
    intro x
    change (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
        ((Ideal.Quotient.factorₐ R (hpow n))
          (AdicCompletion.evalₐ I (c * n) x)) =
      (Ideal.Quotient.factorₐ R (hpow m))
        (AdicCompletion.evalₐ I (c * m) x)
    change ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
        (Ideal.Quotient.factorₐ R (hpow n)))
        (AdicCompletion.evalₐ I (c * n) x) = _
    rw [hmap]
    exact congrArg (Ideal.Quotient.factorₐ R (hpow m))
      (completion_factorPow_eval I hcmn x)
  exact AdicCompletion.liftAlgHom J f hf

private noncomputable def completion_algHom_of_le
    {R : Type u} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J) :
    AdicCompletion I R →ₐ[R] AdicCompletion J R := by
  let f : (n : ℕ) → AdicCompletion I R →ₐ[R] R ⧸ J ^ n :=
    fun n => (Ideal.Quotient.factorₐ R (Ideal.pow_right_mono hIJ n)).comp
      (AdicCompletion.evalₐ I n)
  have hf : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (f n) = f m := by
    intro m n hmn
    have hmap :
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
            (Ideal.Quotient.factorₐ R (Ideal.pow_right_mono hIJ n)) =
          (Ideal.Quotient.factorₐ R (Ideal.pow_right_mono hIJ m)).comp
            (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) := by
      apply AlgHom.ext
      intro y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl
    apply AlgHom.ext
    intro x
    change ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
        (Ideal.Quotient.factorₐ R (Ideal.pow_right_mono hIJ n)))
        (AdicCompletion.evalₐ I n x) = _
    rw [hmap]
    exact congrArg (Ideal.Quotient.factorₐ R (Ideal.pow_right_mono hIJ m))
      (completion_factorPow_eval I hmn x)
  exact AdicCompletion.liftAlgHom J f hf

theorem local_completion_not_agree_in_general :
    ¬ ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
      [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)],
      LocalCompletionAgreement R S := by
  sorry

/- This is the change-of-ideal assertion used in the source paragraph. -/
theorem local_completion_agrees_of_power_le
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    (t : ℕ) (ht : 0 < t)
    (h : (IsLocalRing.maximalIdeal S) ^ t ≤
      (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :
    LocalCompletionAgreement R S := by
  let I : Ideal S := IsLocalRing.maximalIdeal S
  let J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have hJI : J ≤ I := by
    exact IsLocalRing.map_maximalIdeal_le (algebraMap R S)
  have hIJ : I ^ t ≤ J := h
  have hIpow (n : ℕ) : I ^ (t * n) ≤ J ^ n := by
    simpa [pow_mul] using (Ideal.pow_right_mono hIJ n)
  have hJpow (n : ℕ) : J ^ n ≤ I ^ n :=
    Ideal.pow_right_mono hJI n
  let F : AdicCompletion I S →ₐ[S] AdicCompletion J S :=
    completion_algHom_of_power_le I J t hIJ
  let G : AdicCompletion J S →ₐ[S] AdicCompletion I S :=
    completion_algHom_of_le J I hJI
  have hF_eval (n : ℕ) (x : AdicCompletion I S) :
      AdicCompletion.evalₐ J n (F x) =
        Ideal.Quotient.factorₐ S (hIpow n)
          (AdicCompletion.evalₐ I (t * n) x) := by
    simp [F, completion_algHom_of_power_le]
  have hG_eval (n : ℕ) (x : AdicCompletion J S) :
      AdicCompletion.evalₐ I n (G x) =
        Ideal.Quotient.factorₐ S (hJpow n)
          (AdicCompletion.evalₐ J n x) := by
    simp [G, completion_algHom_of_le]
  have hleft : Function.LeftInverse G F := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    have hn : n ≤ t * n := by
      exact Nat.le_mul_of_pos_left n ht
    have hcomp :
        (Ideal.Quotient.factorₐ S (hJpow n)).comp
            (Ideal.Quotient.factorₐ S (hIpow n)) =
          Ideal.Quotient.factorₐ S (Ideal.pow_le_pow_right hn) := by
      apply AlgHom.ext
      intro y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl
    rw [hG_eval, hF_eval]
    change ((Ideal.Quotient.factorₐ S (hJpow n)).comp
        (Ideal.Quotient.factorₐ S (hIpow n)))
        (AdicCompletion.evalₐ I (t * n) x) = _
    rw [hcomp]
    exact completion_factorPow_eval I hn x
  have hright : Function.RightInverse G F := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    have hn : n ≤ t * n := by
      exact Nat.le_mul_of_pos_left n ht
    have hcomp :
        (Ideal.Quotient.factorₐ S (hIpow n)).comp
            (Ideal.Quotient.factorₐ S (hJpow (t * n))) =
          Ideal.Quotient.factorₐ S (Ideal.pow_le_pow_right hn) := by
      apply AlgHom.ext
      intro y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl
    rw [hF_eval, hG_eval]
    change ((Ideal.Quotient.factorₐ S (hIpow n)).comp
        (Ideal.Quotient.factorₐ S (hJpow (t * n))))
        (AdicCompletion.evalₐ J (t * n) x) = _
    rw [hcomp]
    exact completion_factorPow_eval J hn x
  refine ⟨AlgEquiv.ofBijective F ⟨hleft.injective, hright.surjective⟩⟩

/- The quotient maps used to define the canonical map between the two local
   completions.  The finite-after-completion theorem uses the resulting map
   through the completion universal property. -/
theorem maximalIdeal_pow_le_comap_pow
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (n : ℕ) :
    (IsLocalRing.maximalIdeal R) ^ n ≤
      ((IsLocalRing.maximalIdeal S) ^ n).comap (algebraMap R S) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono
    (IsLocalRing.map_maximalIdeal_le (algebraMap R S)) n

def localQuotientMap
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (n : ℕ) :
    ringCompletion (IsLocalRing.maximalIdeal R) →+*
      S ⧸ (IsLocalRing.maximalIdeal S) ^ n :=
  (Ideal.quotientMap ((IsLocalRing.maximalIdeal S) ^ n)
      (algebraMap R S) (maximalIdeal_pow_le_comap_pow R S n)).comp
    (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n).toRingHom

theorem localQuotientMap_compatible
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal S) hmn).comp
          (localQuotientMap R S n) = localQuotientMap R S m := by
  intro m n hmn
  apply RingHom.ext
  intro x
  let hmap :
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal S) hmn).comp
          (Ideal.quotientMap ((IsLocalRing.maximalIdeal S) ^ n)
            (algebraMap R S) (maximalIdeal_pow_le_comap_pow R S n)) =
        (Ideal.quotientMap ((IsLocalRing.maximalIdeal S) ^ m)
          (algebraMap R S) (maximalIdeal_pow_le_comap_pow R S m)).comp
          (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal R) hmn) := by
    apply RingHom.ext
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S) ^ m)
        (algebraMap R S r) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S) ^ m)
        (algebraMap R S r)
    rfl
  change
    ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal S) hmn).comp
        (Ideal.quotientMap ((IsLocalRing.maximalIdeal S) ^ n)
          (algebraMap R S) (maximalIdeal_pow_le_comap_pow R S n)))
        ((AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n) x) =
      (Ideal.quotientMap ((IsLocalRing.maximalIdeal S) ^ m)
        (algebraMap R S) (maximalIdeal_pow_le_comap_pow R S m))
        ((AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) m) x)
  rw [hmap, RingHom.comp_apply, completion_factorPow_eval]

noncomputable def completedLocalMap
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    :
    ringCompletion (IsLocalRing.maximalIdeal R) →+*
      completion (IsLocalRing.maximalIdeal S) S := by
  exact AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal S)
    (fun n => localQuotientMap R S n) (localQuotientMap_compatible R S)

theorem completedLocalMap_mod
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    (n : ℕ) :
    (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n).toRingHom.comp
        (completedLocalMap R S) = localQuotientMap R S n := by
  change (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n).toRingHom.comp
      (AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal S)
        (fun n => localQuotientMap R S n) (localQuotientMap_compatible R S)) = _
  exact AdicCompletion.evalₐ_comp_liftRingHom
    (I := IsLocalRing.maximalIdeal S)
    (fun n => localQuotientMap R S n) (localQuotientMap_compatible R S) n

theorem finite_after_completion
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    (hR : (IsLocalRing.maximalIdeal R).FG)
    (hS : (IsLocalRing.maximalIdeal S).FG)
    [Module.Finite (R ⧸ IsLocalRing.maximalIdeal R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))] :
    LocalCompletionAgreement R S ∧
      (let φ := completedLocalMap R S
       letI := φ.toAlgebra
       Module.Finite
         (ringCompletion (IsLocalRing.maximalIdeal R))
         (completion (IsLocalRing.maximalIdeal S) S)) := by
  let K : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have hpower : ∃ n : ℕ, (IsLocalRing.maximalIdeal S) ^ n ≤ K := by
    letI : (IsLocalRing.maximalIdeal R).IsMaximal :=
      IsLocalRing.maximalIdeal.isMaximal R
    letI : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
      Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    letI : Algebra (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ K) := inferInstance
    letI : IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ K) := inferInstance
    letI : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ K) := inferInstance
    letI : IsArtinian (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ K) :=
      isArtinian_of_fg_of_artinian'
    letI : IsArtinianRing (S ⧸ K) :=
      isArtinian_of_tower (R ⧸ IsLocalRing.maximalIdeal R)
        (inferInstance : IsArtinian (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ K))
    obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient K
    exact ⟨n, hn⟩
  rcases hpower with ⟨n, hn⟩
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    have htop : (⊤ : Ideal S) ≤ K := by simpa using hn
    have hmax : (IsLocalRing.maximalIdeal S) = ⊤ := by
      apply top_unique
      exact htop.trans (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top hmax
  refine ⟨local_completion_agrees_of_power_le R S n hnpos hn, ?_⟩
  dsimp
  let A := ringCompletion (IsLocalRing.maximalIdeal R)
  let M := completion (IsLocalRing.maximalIdeal S) S
  let φ : A →+* M := completedLocalMap R S
  letI : Algebra A M := φ.toAlgebra
  let I : Ideal A := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  let L : Ideal M := I.map φ
  have hφ_alg (r : R) :
      φ (algebraMap R A r) =
        algebraMap S M (algebraMap R S r) := by
    apply AdicCompletion.ext_evalₐ
    intro q
    have hmod := congrArg (fun f => f (algebraMap R A r))
      (congrArg (fun f => f) (completedLocalMap_mod R S q))
    calc
      AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) q
          (φ (algebraMap R A r)) = localQuotientMap R S q (algebraMap R A r) := by
            simpa [φ, RingHom.comp_apply] using hmod
      _ = AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) q
          (algebraMap S M (algebraMap R S r)) := by
            change (Ideal.quotientMap
                ((IsLocalRing.maximalIdeal S) ^ q) (algebraMap R S)
                (maximalIdeal_pow_le_comap_pow R S q))
                (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ q) r) = _
            change (Ideal.quotientMap
                ((IsLocalRing.maximalIdeal S) ^ q) (algebraMap R S)
                (maximalIdeal_pow_le_comap_pow R S q))
                (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ q) r) =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S) ^ q)
                (algebraMap R S r)
            rfl
  have hK : K ≤ L.comap (algebraMap S M) := by
    refine (Ideal.map_le_iff_le_comap).2 ?_
    intro r hr
    change algebraMap S M (algebraMap R S r) ∈ L
    rw [← hφ_alg r]
    exact Ideal.mem_map_of_mem φ
      (Ideal.mem_map_of_mem (algebraMap R A) hr)
  have hIL : I • (⊤ : Submodule A M) = L.restrictScalars A := by
    simp only [Ideal.smul_top_eq_map]
    rw [show algebraMap A M = φ by rfl, show L = I.map φ by rfl]
  let N : Submodule A M := I • (⊤ : Submodule A M)
  have hKN : K • (⊤ : Submodule S M) ≤ L.restrictScalars S := by
    rw [Ideal.smul_top_eq_map]
    exact (Ideal.map_le_iff_le_comap).2 hK
  have hpowN : (IsLocalRing.maximalIdeal S) ^ n • (⊤ : Submodule S M) ≤
      L.restrictScalars S :=
    (Submodule.smul_mono_left hn).trans hKN
  have hqK : ∀ k : S, k ∈ K →
      Submodule.Quotient.mk (p := N) (algebraMap S M k) = 0 := by
    intro k hk
    change Submodule.Quotient.mk (p := I • (⊤ : Submodule A M))
      (algebraMap S M k) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    rw [hIL]
    exact hK hk
  let q₀ : S →+ M ⧸ N :=
    { toFun := fun s => Submodule.Quotient.mk (p := N) (algebraMap S M s)
      map_zero' := by simp
      map_add' := by intro x y; simp }
  let q : S ⧸ K →+ M ⧸ N :=
    QuotientAddGroup.lift K.toAddSubgroup q₀ hqK
  have hq_surj : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N y
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n x)
    have hx : x - algebraMap S M s ∈
        (IsLocalRing.maximalIdeal S) ^ n • (⊤ : Submodule S M) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hS]
      apply LinearMap.mem_ker.mpr
      rw [← AdicCompletion.factor_evalₐ_eq_eval
        (IsLocalRing.maximalIdeal S) (x - algebraMap S M s)
        (show (IsLocalRing.maximalIdeal S) ^ n ≤
          (IsLocalRing.maximalIdeal S) ^ n • (⊤ : Submodule S S) by simp)]
      have hsalg :
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n
              (algebraMap S M s) = Ideal.Quotient.mk
                ((IsLocalRing.maximalIdeal S) ^ n) s := by rfl
      rw [map_sub, hsalg, ← hs]
      simp
    have hxL : x - algebraMap S M s ∈ L := hpowN hx
    refine ⟨Ideal.Quotient.mk K s, ?_⟩
    change Submodule.Quotient.mk (p := N) (algebraMap S M s) =
      Submodule.Quotient.mk (p := N) x
    apply (Submodule.Quotient.eq N).2
    change algebraMap S M s - x ∈ I • (⊤ : Submodule A M)
    rw [hIL]
    change algebraMap S M s - x ∈ L
    have hneg := L.neg_mem hxL
    convert hneg using 1 <;> abel
  let σ : (R ⧸ IsLocalRing.maximalIdeal R) →+* (A ⧸ I) :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R)
      ((Ideal.Quotient.mk I).comp (algebraMap R A)) (by
        intro r hr
        change Ideal.Quotient.mk I (algebraMap R A r) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem (algebraMap R A) hr)
  let f : (S ⧸ K) →ₛₗ[σ] (M ⧸ N) :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := by
        intro c x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp only [σ, Ideal.Quotient.lift_mk, RingHom.coe_comp, Algebra.smul_def]
        change q (Ideal.Quotient.mk K ((algebraMap R S r) * s)) =
          (Ideal.Quotient.mk I (algebraMap R A r)) •
            q (Ideal.Quotient.mk K s)
        change Submodule.Quotient.mk (p := N)
              (algebraMap S M ((algebraMap R S r) * s)) =
          Submodule.Quotient.mk (p := N)
            (φ (algebraMap R A r) * algebraMap S M s)
        rw [hφ_alg]
        rfl }
  letI : Module.Finite (A ⧸ I) (M ⧸ N) :=
    Module.Finite.of_surjective f (by simpa [f] using hq_surj)
  have hA : IsAdicComplete I A := by
    simpa [I, Unit96.completionPowerIdeal] using
      AdicCompletion.isAdicComplete_self (IsLocalRing.maximalIdeal R) hR
  have hImax : I.map φ ≤
      (IsLocalRing.maximalIdeal S).map (algebraMap S M) := by
    refine (Ideal.map_le_iff_le_comap).2 ?_
    rw [show I = (IsLocalRing.maximalIdeal R).map (algebraMap R A) by rfl]
    refine (Ideal.map_le_iff_le_comap).2 ?_
    intro r hr
    change φ (algebraMap R A r) ∈
      (IsLocalRing.maximalIdeal S).map (algebraMap S M)
    rw [hφ_alg r]
    exact Ideal.mem_map_of_mem (algebraMap S M)
      ((IsLocalRing.map_maximalIdeal_le (algebraMap R S))
        (Ideal.mem_map_of_mem (algebraMap R S) hr))
  have hpowA (k : ℕ) : I ^ k • (⊤ : Submodule A M) ≤
      (((IsLocalRing.maximalIdeal S) ^ k).map (algebraMap S M)).restrictScalars A := by
    simp only [Ideal.smul_top_eq_map]
    rw [show algebraMap A M = φ by rfl, Ideal.map_pow, Ideal.map_pow]
    exact Ideal.pow_right_mono hImax k
  have hM : (⨅ k : ℕ, I ^ k • (⊤ : Submodule A M)) = ⊥ := by
    have hsep := Unit96.isAdicComplete_separated
      (IsLocalRing.maximalIdeal S)
      (completion_isAdicComplete_of_fg (IsLocalRing.maximalIdeal S) S hS)
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ (⊥ : Submodule S M) := by
        rw [← hsep]
        apply (Submodule.mem_iInf _).2
        intro k
        simpa [Ideal.smul_top_eq_map] using
          (hpowA k ((Submodule.mem_iInf _).1 hx k))
      exact (Submodule.mem_bot A).2 ((Submodule.mem_bot S).1 hx')
    · exact bot_le
  exact Unit96.finite_of_complete_ring_of_finite_residue I hA hM

/-! ## Finite ring maps and completed localizations -/

abbrev localizationAtPrime
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] : Type u :=
  Localization.AtPrime p

abbrev localizedAlgebra
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] : Type u :=
  Localization.AtPrime p ⊗[R] S

abbrev primeCompletion
    (S : Type u) [CommRing S] (q : Ideal S) (hq : q.IsPrime) : Type u :=
  letI : q.IsPrime := hq
  completion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q)

/- The source's finite list of primes over `p` is made explicit by `qs`; the
   injectivity and exhaustiveness fields say that it is exactly that fiber. -/
theorem completion_finite_extension
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime]
    (m : ℕ) (qs : Fin m → Ideal S)
    (hprime : ∀ i, (qs i).IsPrime)
    (hlies : ∀ i, (qs i).comap (algebraMap R S) = p)
    (hinj : Function.Injective qs)
    (hcomplete : ∀ q : Ideal S, q.IsPrime →
      q.comap (algebraMap R S) = p → ∃ i, qs i = q) :
    Nonempty
        ((completion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p) ⊗[R] S) ≃+*
          (completion
            ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
              (algebraMap (Localization.AtPrime p)
                (localizedAlgebra R S p)))
            (localizedAlgebra R S p))) ∧
      Nonempty
        ((completion
            ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
              (algebraMap (Localization.AtPrime p)
                (localizedAlgebra R S p)))
            (localizedAlgebra R S p)) ≃+*
          (∀ i : Fin m, primeCompletion S (qs i) (hprime i))) := by
  sorry

/-! ## Splitting after completion -/

theorem completion_split_exact
    {R : Type u} [CommRing R] (I : Ideal R)
    {K P : Type v} {M : Type w}
    [AddCommGroup K] [AddCommGroup P] [AddCommGroup M]
    [Module R K] [Module R P] [Module R M] [Module.Flat R M]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    (f : K →ₗ[R] P) (g : P →ₗ[R] M)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Injective (AdicCompletion.map I f) ∧
      Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
        Function.Surjective (AdicCompletion.map I g) ∧
      ∃ s : completion I M →ₗ[ringCompletion I] completion I P,
        (AdicCompletion.map I g).comp s = LinearMap.id := by
  sorry

/-! ## Completeness modulo a quotient -/

theorem complete_modulo_ideal
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A)
    (hA : IsAdicComplete I A)
    (hquot : IsAdicComplete (J.map (Ideal.Quotient.mk I)) (A ⧸ I)) :
    IsAdicComplete J A := by
  sorry

end

end Formalization.Books.Algebra.Unit97
