import Formalization.Books.Algebra.Unit05.FiniteModules
import Formalization.Books.Algebra.Unit40.SupportsAndAnnihilators
import Formalization.Books.Algebra.Unit60.Dimension
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 62: Support and dimension of modules

The source's prime filtration is represented by the earlier chapter's
`FiniteCyclicFiltration`, refined with the assertion that every cyclic factor
is a prime quotient and with the resulting strictness of the filtration.
Support and its dimension use Mathlib's canonical `Module.support` and
`Module.supportDim`.
-/

namespace Formalization.Books.Algebra.Unit62

open Formalization.Books.Algebra.Unit05
open Formalization.Books.Algebra.Unit59
open Set

universe u v

noncomputable section

/-! ## Prime filtrations -/

/- A prime filtration keeps the cyclic-filtration data from Chapter 5 and
   records precisely the extra properties used in this chapter. -/
structure PrimeFiltration
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] where
  cyclic : FiniteCyclicFiltration R M
  ideal_isPrime : ∀ i : Fin cyclic.length, (cyclic.ideal i).IsPrime
  strict_step : ∀ i : Fin cyclic.length,
    cyclic.stage (Fin.castSucc i) < cyclic.stage (Fin.succ i)

theorem exists_primeFiltration
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] :
    Nonempty (PrimeFiltration R M) := by
  sorry

/-! ## Support of a prime filtration -/

theorem support_eq_iUnion_zeroLocus_of_primeFiltration
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (F : PrimeFiltration R M) :
    (Module.support R M =
      ⋃ i : Fin F.cyclic.length,
        PrimeSpectrum.zeroLocus ((F.cyclic.ideal i : Ideal R) : Set R)) ∧
      (∀ i : Fin F.cyclic.length,
        (⟨F.cyclic.ideal i, F.ideal_isPrime i⟩ : PrimeSpectrum R) ∈
          Module.support R M) := by
  sorry

theorem support_eq_singleton_closedPoint_iff_finiteLength
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    Module.support R M = {IsLocalRing.closedPoint R} ↔
      IsFiniteLength R M := by
  sorry

theorem exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) :
    (∃ n : ℕ, I ^ n • (⊤ : Submodule R M) = ⊥) ↔
      Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  sorry

/-! ## Minimal primes and localized length -/

theorem minimal_prime_set_and_occurrences
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (F : PrimeFiltration R M) :
    ({p : PrimeSpectrum R |
        Minimal
          (fun q : Ideal R =>
            q ∈ Set.range (fun i : Fin F.cyclic.length => F.cyclic.ideal i))
          p.asIdeal} =
      {p : PrimeSpectrum R |
        Minimal (fun q : PrimeSpectrum R => q ∈ Module.support R M) p}) ∧
      (∀ p : PrimeSpectrum R,
        Minimal
            (fun q : Ideal R =>
              q ∈ Set.range (fun i : Fin F.cyclic.length => F.cyclic.ideal i))
            p.asIdeal →
          (Nat.card
              {i : Fin F.cyclic.length // F.cyclic.ideal i = p.asIdeal} : ℕ∞) =
            Module.length (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M)) := by
  sorry

/-! ## Dimension -/

/- `d` from Chapter 59 is `WithBot ℕ`, whereas Mathlib's support dimension is
   `WithBot ℕ∞`; the displayed equality uses the canonical embedding of the
   finite natural-valued invariant into extended naturals. -/
theorem d_eq_supportDim
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    WithBot.map (fun n : ℕ => (n : ℕ∞))
        (Formalization.Books.Algebra.Unit59.d R M) =
      Module.supportDim R M := by
  sorry

theorem supportDim_eq_max_of_short_exact
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [IsNoetherianRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    max (Module.supportDim R M') (Module.supportDim R M'') =
      Module.supportDim R M := by
  sorry

end

end Formalization.Books.Algebra.Unit62
