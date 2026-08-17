import Formalization.Books.Algebra.Unit62
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 63: associated primes

The source uses the exact annihilator definition of an associated prime.  This
file therefore records the source notion on `PrimeSpectrum` points, while the
bridge to Mathlib's `associatedPrimes` is available under Noetherian
hypotheses, where Mathlib's radical-based definition has the same description.
-/

namespace Formalization.Books.Algebra.Unit63

open Set

universe u v

noncomputable section

/-! ## The definition and the support inclusion -/

/-- A prime point is associated to `M` when it is the annihilator of an element
of `M`.  The prime condition is carried by the `PrimeSpectrum` point. -/
def IsAssociatedPrime
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) (M : Type v)
    [AddCommGroup M] [Module R M] : Prop :=
  ∃ m : M, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal

/-- The exact-annihilator associated primes of an `R`-module. -/
def associatedPrimes
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] : Set (PrimeSpectrum R) :=
  {p | IsAssociatedPrime p M}

/-- Under Noetherian hypotheses, the source definition agrees with Mathlib's
canonical associated-prime set after forgetting the spectrum-point wrapper. -/
theorem associatedPrimes_toIdeal_eq_mathlib
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    (fun p : PrimeSpectrum R => p.asIdeal) '' associatedPrimes R M =
      _root_.associatedPrimes R M := by
  sorry

/-- Associated primes lie in the support. -/
theorem ass_subset_support
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    associatedPrimes R M ⊆ Module.support R M := by
  sorry

/-! ## Filtrations and finiteness -/

/-- A finite filtration with prime cyclic factors, without imposing finiteness
of the individual stages. -/
structure PrimeFiltration
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] where
  length : ℕ
  stage : Fin (length + 1) → Submodule R M
  prime : Fin length → Ideal R
  zero : stage 0 = ⊥
  top : stage (Fin.last length) = ⊤
  strict_step : ∀ i : Fin length,
    stage (Fin.castSucc i) < stage (Fin.succ i)
  prime_isPrime : ∀ i : Fin length, (prime i).IsPrime
  quotient : ∀ i : Fin length, Nonempty
    (((stage (Fin.succ i)) ⧸
      (stage (Fin.castSucc i)).comap (stage (Fin.succ i)).subtype) ≃ₗ[R]
        (R ⧸ prime i))

/-- A prime filtration bounds the associated-prime set by its factors. -/
theorem ass_subset_primeFiltration
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M) :
    associatedPrimes R M ⊆
      {p : PrimeSpectrum R | p.asIdeal ∈ Set.range F.prime} := by
  sorry

/-- The minimal points of a subset of the spectrum. -/
def minimalPoints {R : Type u} [CommRing R]
    (s : Set (PrimeSpectrum R)) : Set (PrimeSpectrum R) :=
  {p | p ∈ s ∧ Minimal (fun q : PrimeSpectrum R => q ∈ s) p}

/-- For a finite module over a Noetherian ring, the associated-prime set is
finite. -/
theorem finite_ass
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] :
    (associatedPrimes R M).Finite := by
  sorry

/-- The minimal primes in the support, in the associated-prime set, and among
the factors of any prime filtration coincide. -/
theorem minimal_primes_associated_primes
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (F : PrimeFiltration R M) :
    minimalPoints (Module.support R M) =
        minimalPoints (associatedPrimes R M) ∧
      minimalPoints (associatedPrimes R M) =
        minimalPoints {p : PrimeSpectrum R |
          p.asIdeal ∈ Set.range F.prime} := by
  sorry

/-! ## Exact sequences, zero modules, and zerodivisors -/

/-- The two associated-prime inclusions for a short exact sequence. -/
theorem ass_subset_ass_of_short_exact
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    associatedPrimes R M' ⊆ associatedPrimes R M ∧
      associatedPrimes R M ⊆
        associatedPrimes R M' ∪ associatedPrimes R M'' := by
  sorry

/-- The associated-prime set of a binary direct sum, represented by the
product module `M' × M''`. -/
theorem ass_prod
    {R : Type u} {M' M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M''] :
    associatedPrimes R (M' × M'') =
      associatedPrimes R M' ∪ associatedPrimes R M'' := by
  sorry

/-- Over a Noetherian ring, a module is zero exactly when it has no associated
prime. -/
theorem ass_eq_empty_iff_subsingleton
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    Subsingleton M ↔ associatedPrimes R M = ∅ := by
  sorry

/-- Every minimal point of the support of a module over a Noetherian ring is
associated. -/
theorem ass_of_minimal_support
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M)
    (hminimal : Minimal (fun q : PrimeSpectrum R => q ∈ Module.support R M) p) :
    p ∈ associatedPrimes R M := by
  sorry

/-- The union of the associated primes is the set of module zerodivisors. -/
theorem iUnion_associatedPrimes_eq_module_zeroDivisors
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    (⋃ p : {p : PrimeSpectrum R // p ∈ associatedPrimes R M},
        (p.1.asIdeal : Set R)) =
      {x : R | ∃ m : M, m ≠ 0 ∧ x • m = 0} := by
  sorry

/-! ## One equation -/

/-- The quotient `M/fM`, written using the canonical ideal action on a
submodule. -/
abbrev quotientByElement
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) : Type v :=
  M ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R M))

/-- The support-dimension inequalities for one equation, together with the
minimal-support and regular-element criteria for equality. -/
theorem one_equation_module
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (f : R)
    (hf : f ∈ IsLocalRing.maximalIdeal R) :
    Module.supportDim R (quotientByElement R M f) ≤ Module.supportDim R M ∧
      Module.supportDim R M ≤
        Module.supportDim R (quotientByElement R M f) + 1 ∧
      ((∀ p : PrimeSpectrum R,
          p ∈ minimalPoints (Module.support R M) → f ∉ p.asIdeal) →
        Module.supportDim R M =
          Module.supportDim R (quotientByElement R M f) + 1) ∧
      (IsSMulRegular M f →
        ∀ p : PrimeSpectrum R,
          p ∈ minimalPoints (Module.support R M) → f ∉ p.asIdeal) := by
  sorry

/-! ## Functoriality -/

/-- Associated primes map forward along the map on spectra induced by a ring
map.  The `R`-module structure is the one induced from the `S`-module by the
ring map. -/
theorem ass_functorial
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] (φ : R →+* S) [Module S M] :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ '' associatedPrimes S M ⊆
        associatedPrimes R M) := by
  sorry

/-! ### The reverse-inclusion example -/

/-- The polynomial relation ideal generated by the squares of all variables. -/
def reverseFunctorialityExampleIdeal (k : Type u) [Field k] :
    Ideal (MvPolynomial ℕ k) :=
  Ideal.span (Set.range fun i : ℕ =>
    (MvPolynomial.X i : MvPolynomial ℕ k) ^ 2)

/-- The infinitely generated square-zero-variable quotient used in the source
as a counterexample to reverse functoriality. -/
abbrev reverseFunctorialityExampleRing (k : Type u) [Field k] :=
  MvPolynomial ℕ k ⧸ reverseFunctorialityExampleIdeal k

/-- The displayed example has associated primes over the base field but none
over the quotient ring itself, so the reverse inclusion fails. -/
theorem ass_reverse_functoriality_example
    (k : Type u) [Field k] :
    (associatedPrimes k (reverseFunctorialityExampleRing k)).Nonempty ∧
      associatedPrimes (reverseFunctorialityExampleRing k)
          (reverseFunctorialityExampleRing k) = ∅ ∧
      ¬ (associatedPrimes k (reverseFunctorialityExampleRing k) ⊆
        PrimeSpectrum.comap (algebraMap k (reverseFunctorialityExampleRing k)) ''
          associatedPrimes (reverseFunctorialityExampleRing k)
            (reverseFunctorialityExampleRing k)) := by
  sorry

/-- If the target ring is Noetherian, the functoriality inclusion is an
equality. -/
theorem ass_functorial_eq_of_noetherian
    {R S M : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing S] [AddCommGroup M]
    (φ : R →+* S) [Module S M] :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ '' associatedPrimes S M =
        associatedPrimes R M) := by
  sorry

/-! ## Quotients and localization -/

/-- Passing from `R` to `R/I` preserves associated primes via the canonical
injection of spectra. -/
theorem ass_quotient_ring
    {R : Type u} {M : Type v} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module (R ⧸ I) M] :
    (letI : Module R M := Module.compHom M (Ideal.Quotient.mk I);
      PrimeSpectrum.comap (Ideal.Quotient.mk I) ''
          associatedPrimes (R ⧸ I) M = associatedPrimes R M) := by
  sorry

/-- Localization sends an associated prime to the closed point of the
localized module.  If the prime is finitely generated, the converse holds. -/
theorem associated_primes_localize_at_prime
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    (p ∈ associatedPrimes R M →
      IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) ∈
        associatedPrimes (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) ∧
      (p.asIdeal.FG →
        (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) ∈
            associatedPrimes (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M) →
          p ∈ associatedPrimes R M)) := by
  sorry

/-- The associated-prime set of a localized module, viewed over the localized
ring, maps to the associated-prime set viewed over the original ring. -/
theorem ass_localize_eq_over_localization
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      PrimeSpectrum.comap (algebraMap R (Localization S)) ''
          associatedPrimes (Localization S) (LocalizedModule S M) =
        associatedPrimes R (LocalizedModule S M)) := by
  sorry

/-- Associated primes of a module that survive in the localization remain
associated after localization. -/
theorem ass_localize_subset
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      associatedPrimes R M ∩
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) ⊆
        associatedPrimes R (LocalizedModule S M)) := by
  sorry

/-- For a Noetherian ring, the preceding localization inclusion is an
equality. -/
theorem ass_localize_eq_of_noetherian
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] (S : Submonoid R) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      associatedPrimes R M ∩
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
        associatedPrimes R (LocalizedModule S M)) := by
  sorry

/-- If every element of the multiplicative set is regular on `M`, localization
does not change the associated-prime set over `R`. -/
theorem ass_localize_eq_of_regular
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R)
    (hS : ∀ s : S, IsSMulRegular M (s : R)) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      associatedPrimes R M = associatedPrimes R (LocalizedModule S M)) := by
  sorry

/-! ## Regular elements and detection at associated primes -/

/-- An ideal contained in the maximal ideal contains a module nonzerodivisor
exactly when it is contained in no associated prime. -/
theorem ideal_contains_regular_iff
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) :
    (∃ x : R, x ∈ I ∧ IsSMulRegular M x) ↔
      ∀ q : PrimeSpectrum R, q ∈ associatedPrimes R M → ¬ I ≤ q.asIdeal := by
  sorry

/-- The canonical map from a module to the product of its localizations at
its associated primes. -/
def localizationAtAssociatedPrimesMap
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    M →ₗ[R]
      ∀ p : {p : PrimeSpectrum R // p ∈ associatedPrimes R M},
        LocalizedModule.AtPrime p.1.asIdeal M :=
  LinearMap.pi fun p =>
    LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl M

/-- Over a Noetherian ring, the associated-prime localizations detect every
module element. -/
theorem localizationAtAssociatedPrimesMap_injective
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    Function.Injective (localizationAtAssociatedPrimesMap (R := R) (M := M)) := by
  sorry

/-! ## A dimension-one auxiliary statement -/

/-- A positive-dimensional finite-type algebra over a field has a regular
nonunit. -/
theorem exists_nonzerodivisor_nonunit_of_finiteType_of_positive_dimension
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S]
    (hdim : 0 < ringKrullDim S) :
    ∃ f : S, f ∈ nonZeroDivisors S ∧ ¬ IsUnit f := by
  sorry

end

end Formalization.Books.Algebra.Unit63
