import Formalization.Books.Algebra.Unit96.Completion
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
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

universe u v

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
  sorry

/-! ## Flatness and faithful flatness -/

theorem completion_flat
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    RingHom.Flat (algebraMap R (ringCompletion I)) := by
  sorry

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
  sorry

theorem local_completion_faithfully_flat
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    RingHom.FaithfullyFlat
      (algebraMap R (ringCompletion (IsLocalRing.maximalIdeal R))) := by
  sorry

/-! ## Completeness and Noetherianity -/

theorem completion_is_adic_complete
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsAdicComplete I (completion I M) := by
  sorry

/- This is the canonical inclusion of the completion of `I^n M` into the
   completion of `M`; it is the source's assertion `I^n M^ = (I^n M)^`. -/
theorem completion_power_submodule_eq_range
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    I ^ n • (⊤ : Submodule R (completion I M)) =
      (AdicCompletion.ofPowSMul I M n).range.restrictScalars R := by
  sorry

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
  sorry

theorem completion_is_noetherian_of_fg_quotient
    {R : Type u} [CommRing R] (I : Ideal R)
    [IsNoetherianRing (R ⧸ I)] (hI : I.FG) :
    IsNoetherianRing (ringCompletion I) ∧
      IsAdicComplete
        (I.map (algebraMap R (ringCompletion I))) (ringCompletion I) := by
  sorry

theorem completion_is_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (ringCompletion I) := by
  sorry

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
  sorry

/- The quotient maps used to define the canonical map between the two local
   completions.  The finite-after-completion theorem uses the resulting map
   through the completion universal property. -/
theorem maximalIdeal_pow_le_comap_pow
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (n : ℕ) :
    (IsLocalRing.maximalIdeal R) ^ n ≤
      ((IsLocalRing.maximalIdeal S) ^ n).comap (algebraMap R S) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
    {K P M : Type v} [AddCommGroup K] [AddCommGroup P] [AddCommGroup M]
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
