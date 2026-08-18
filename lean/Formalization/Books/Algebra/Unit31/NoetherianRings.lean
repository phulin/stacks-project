import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.OfPrime
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace

/-!
# Commutative Algebra, Chapter 31: Noetherian rings

The source's Noetherian-ring predicate and its standard consequences are
represented by Mathlib's canonical `IsNoetherianRing`, finite-type,
finite-presentation, spectrum, minimal-prime, and localization interfaces.
The source's localization map `R_f → R_p` is made explicit using the
universal property of `Localization.Away`.
-/

namespace Formalization.Books.Algebra.Unit31

open Set
open scoped TensorProduct

noncomputable section

/-! ## Definition and first criteria -/

/- The definition in the source is Mathlib's `IsNoetherianRing`: every ideal
is finitely generated. -/
theorem noetherian_iff_ideal_fg (R : Type*) [CommRing R] :
    IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG :=
  isNoetherianRing_iff_ideal_fg R

/- The source's ascending-chain condition is the specialization of the
canonical module criterion to the regular module `R`. -/
theorem noetherian_iff_ascending_chain_condition
    (R : Type*) [CommRing R] :
    (∀ f : ℕ →o Ideal R, ∃ n, ∀ m, n ≤ m → f n = f m) ↔
      IsNoetherianRing R :=
  monotone_stabilizes_iff_noetherian

/- Cohen's lemma gives the stated prime-ideal criterion. -/
theorem noetherian_of_prime_ideal_fg
    {R : Type*} [CommRing R]
    (h : ∀ I : Ideal R, I.IsPrime → I.FG) :
    IsNoetherianRing R :=
  IsNoetherianRing.of_prime h

/-! ## Permanence and examples -/

/- A finitely generated algebra over a Noetherian ring is Noetherian. -/
theorem finiteType_algebra_isNoetherian
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] :
    IsNoetherianRing S :=
  Algebra.FiniteType.isNoetherianRing R S

/- Every localization of a Noetherian ring is Noetherian. -/
theorem localization_isNoetherian
    {R : Type*} [CommRing R] [IsNoetherianRing R] (S : Submonoid R) :
    IsNoetherianRing (Localization S) := by
  infer_instance

/- The recursive coefficient identities in the source's proof are proof
scaffolding; the chapter-level assertion is the theorem below. -/
theorem mvPowerSeries_isNoetherian
    {R : Type*} [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  infer_instance

/- The two examples in the source use the canonical Noetherian instances for
fields and for `ℤ`. -/
theorem finiteType_algebra_over_field_isNoetherian
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    IsNoetherianRing A :=
  Algebra.FiniteType.isNoetherianRing k A

theorem finiteType_algebra_over_int_isNoetherian
    {A : Type*} [CommRing A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] :
    IsNoetherianRing A :=
  Algebra.FiniteType.isNoetherianRing ℤ A

/-! ## Finite generation and finite presentation -/

/- A finite module over a Noetherian ring is finitely presented. -/
theorem finite_module_isFinitePresentation
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] :
    Module.FinitePresentation R M :=
  Module.finitePresentation_of_finite R M

/- A submodule of a finite module is finite. -/
theorem submodule_of_finite_module_isFinite
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] (N : Submodule R M) :
    Module.Finite R N := by
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)

/- A finite-type algebra over a Noetherian ring is finitely presented. -/
theorem finiteType_algebra_isFinitePresentation
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FinitePresentation R A :=
  (Algebra.FinitePresentation.of_finiteType (R := R) (A := A)).mp inferInstance

/-! ## Topology and minimal primes -/

/- The prime spectrum of a Noetherian ring is a Noetherian topological space. -/
theorem primeSpectrum_isNoetherianSpace
    {R : Type*} [CommRing R] [IsNoetherianRing R] :
    TopologicalSpace.NoetherianSpace (PrimeSpectrum R) := by
  infer_instance

/- The source states the equivalent finiteness of irreducible components and
minimal primes; both canonical consequences are recorded together. -/
theorem primeSpectrum_finite_irreducibleComponents_and_minimalPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] :
    (irreducibleComponents (PrimeSpectrum R)).Finite ∧
      (minimalPrimes R).Finite := by
  exact ⟨TopologicalSpace.NoetherianSpace.finite_irreducibleComponents,
    minimalPrimes.finite_of_isNoetherianRing R⟩

/-! ## Base change -/

/- The two displayed ring maps in the source are represented by the standard
algebra structures, and finite type by `Algebra.FiniteType`. -/
theorem tensorProduct_isNoetherian_of_finiteType
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.FiniteType R R']
    [IsNoetherianRing S] :
    IsNoetherianRing (R' ⊗[R] S) := by
  let _ : Algebra S (S ⊗[R] R') := Algebra.TensorProduct.leftAlgebra
  let _ : IsNoetherianRing (S ⊗[R] R') :=
    Algebra.FiniteType.isNoetherianRing S (S ⊗[R] R')
  let _ : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  exact isNoetherianRing_of_ringEquiv (S ⊗[R] R')
    (Algebra.TensorProduct.commRight R S R').toRingEquiv

/- A finitely generated field extension preserves Noetherianity after tensoring
with a Noetherian algebra. -/
theorem tensorProduct_isNoetherian_of_finiteType_fieldExtension
    {k R K : Type*} [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra.FiniteType k K]
    [IsNoetherianRing R] :
    IsNoetherianRing (K ⊗[k] R) := by
  exact tensorProduct_isNoetherian_of_finiteType (R := k) (S := R) (R' := K)

/-! ## A subring of a local ring -/

/- The canonical map from `R_f` to `R_p`, for `f ∉ p`, obtained by the
localization universal property. -/
noncomputable def localizationAwayToAtPrime
    {R : Type*} [CommRing R] (p : PrimeSpectrum R) (f : R)
    (hf : f ∉ p.asIdeal) :
    Localization.Away f →+* Localization.AtPrime p.asIdeal :=
  Localization.awayLift
    (algebraMap R (Localization.AtPrime p.asIdeal)) f
    ((IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime p.asIdeal) p.asIdeal f).2 hf)

/- In each of the three cases from the source, some localization away from an
element outside `p` embeds in the localization at `p`. -/
theorem exists_injective_localizationAwayToAtPrime_of_domain
    {R : Type*} [CommRing R] [IsDomain R] (p : PrimeSpectrum R) :
    ∃ f : R, ∃ hf : f ∉ p.asIdeal,
      Function.Injective (localizationAwayToAtPrime p f hf) := by
  refine ⟨(1 : R), p.asIdeal.ne_top_iff_one.mp p.isPrime.ne_top, ?_⟩
  unfold localizationAwayToAtPrime Localization.awayLift IsLocalization.Away.lift
  rw [IsLocalization.lift_injective_iff]
  intro x y
  have hAway : Function.Injective (algebraMap R (Localization.Away (1 : R))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors one_ne_zero)
  have hAtPrime : Function.Injective (algebraMap R (Localization.AtPrime p.asIdeal)) :=
    FaithfulSMul.algebraMap_injective R (Localization.AtPrime p.asIdeal)
  constructor <;> intro h <;> first
    | exact congrArg (algebraMap R (Localization.AtPrime p.asIdeal)) (hAway h)
    | exact congrArg (algebraMap R (Localization.Away (1 : R))) (hAtPrime h)

theorem exists_injective_localizationAwayToAtPrime_of_noetherian
    {R : Type*} [CommRing R] [IsNoetherianRing R] (p : PrimeSpectrum R) :
    ∃ f : R, ∃ hf : f ∉ p.asIdeal,
      Function.Injective (localizationAwayToAtPrime p f hf) := by
  sorry

theorem exists_injective_localizationAwayToAtPrime_of_reduced
    {R : Type*} [CommRing R] [IsReduced R]
    (hmin : (minimalPrimes R).Finite) (p : PrimeSpectrum R) :
    ∃ f : R, ∃ hf : f ∉ p.asIdeal,
      Function.Injective (localizationAwayToAtPrime p f hf) := by
  sorry

/-! ## Surjective endomorphisms -/

/- The source calls the conclusion an isomorphism; an explicit ring
equivalence is the corresponding usable Lean interface. -/
theorem surjective_endomorphism_isomorphism
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (f : R →+* R) (hf : Function.Surjective f) :
    ∃ e : R ≃+* R, e.toRingHom = f := by
  sorry

end

end Formalization.Books.Algebra.Unit31
