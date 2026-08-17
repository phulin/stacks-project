import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit63
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 66: weakly associated primes

Weak association is represented on `PrimeSpectrum` points, as in Chapter 63's
source-facing associated-prime API.  The minimal-prime condition itself uses
Mathlib's `Ideal.minimalPrimes`, and localization, support, finite maps, and
tensor products use their canonical Mathlib constructions.
-/

namespace Formalization.Books.Algebra.Unit66

open Set
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Definition and localization -/

/-- A prime point is weakly associated to `M` when it is minimal over the
annihilator of one of its elements. -/
def IsWeaklyAssociatedPrime
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) (M : Type v)
    [AddCommGroup M] [Module R M] : Prop :=
  ∃ m : M,
    p.asIdeal ∈ ((⊥ : Submodule R M).colon ({m} : Set M)).minimalPrimes

/-- The weakly associated-prime set of an `R`-module. -/
def weaklyAssociatedPrimes
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] : Set (PrimeSpectrum R) :=
  {p | IsWeaklyAssociatedPrime p M}

/-- Weak association can be characterized after localizing at the prime, or
by the radical of a localized element annihilator. -/
theorem weaklyAssociated_local
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    List.TFAE [
      p ∈ weaklyAssociatedPrimes R M,
      IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) ∈
        weaklyAssociatedPrimes (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M),
      ∃ m : LocalizedModule.AtPrime p.asIdeal M,
        (((⊥ : Submodule (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)).colon ({m} : Set _)).radical =
          (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)).asIdeal)] := by
  sorry

/-! ## Reduced rings and exact sequences -/

/-- For a reduced ring, the weakly associated primes of the ring are its
minimal primes. -/
theorem weaklyAssociatedPrimes_eq_minimalPrimes_of_reduced
    {R : Type u} [CommRing R] [IsReduced R] :
    weaklyAssociatedPrimes R R =
      {p : PrimeSpectrum R | p.asIdeal ∈ minimalPrimes R} := by
  sorry

/-- The weakly associated-prime inclusions for a short exact sequence. -/
theorem weaklyAssociatedPrimes_short_exact
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    weaklyAssociatedPrimes R M' ⊆ weaklyAssociatedPrimes R M ∧
      weaklyAssociatedPrimes R M ⊆
        weaklyAssociatedPrimes R M' ∪ weaklyAssociatedPrimes R M'' := by
  sorry

/-! ## Existence, support, and zerodivisors -/

/-- A module is zero exactly when it has no weakly associated prime. -/
theorem weaklyAssociatedPrimes_eq_empty_iff_subsingleton
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Subsingleton M ↔ weaklyAssociatedPrimes R M = ∅ := by
  sorry

/-- Associated primes are weakly associated, and weakly associated primes lie
in the support. -/
theorem associatedPrimes_subset_weaklyAssociatedPrimes_subset_support
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Formalization.Books.Algebra.Unit63.associatedPrimes R M ⊆
        weaklyAssociatedPrimes R M ∧
      weaklyAssociatedPrimes R M ⊆ Module.support R M := by
  sorry

/-- The union of weakly associated primes is the set of module
zerodivisors. -/
theorem iUnion_weaklyAssociatedPrimes_eq_module_zeroDivisors
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    (⋃ p : {p : PrimeSpectrum R // p ∈ weaklyAssociatedPrimes R M},
        (p.1.asIdeal : Set R)) =
      {x : R | ∃ m : M, m ≠ 0 ∧ x • m = 0} := by
  sorry

/-- A minimal point of the support of a module is weakly associated. -/
theorem weaklyAssociated_of_minimal_support
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M)
    (hminimal : Minimal (fun q : PrimeSpectrum R => q ∈ Module.support R M) p) :
    p ∈ weaklyAssociatedPrimes R M := by
  sorry

/-! ## Finitely generated primes and functoriality -/

/-- At a finitely generated prime, weak association agrees with exact
association. -/
theorem associated_iff_weaklyAssociated_of_fg
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (hfg : p.asIdeal.FG) :
    p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M ↔
      p ∈ weaklyAssociatedPrimes R M := by
  sorry

/-- Over a Noetherian ring, associated and weakly associated primes coincide. -/
theorem associatedPrimes_eq_weaklyAssociatedPrimes_of_noetherian
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    Formalization.Books.Algebra.Unit63.associatedPrimes R M =
      weaklyAssociatedPrimes R M := by
  sorry

/-! ### The non-functoriality example -/

/-- The polynomial ring in the `x_i`, used as the base ring in the example. -/
abbrev weaklyAssociatedExampleBaseRing (k : Type u) [Field k] :=
  MvPolynomial ℕ k

/-- The polynomial ring in the `x_i` and `y_i` before imposing relations. -/
abbrev weaklyAssociatedExamplePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (ℕ ⊕ ℕ) k

/-- The two families of variables in the example. -/
def weaklyAssociatedExampleX (k : Type u) [Field k] (i : ℕ) :
    weaklyAssociatedExamplePolynomialRing k :=
  MvPolynomial.X (.inl i)

def weaklyAssociatedExampleY (k : Type u) [Field k] (i : ℕ) :
    weaklyAssociatedExamplePolynomialRing k :=
  MvPolynomial.X (.inr i)

/-- The displayed relations `x_i y_i`. -/
def weaklyAssociatedExampleRelations (k : Type u) [Field k] :
    Set (weaklyAssociatedExamplePolynomialRing k) :=
  Set.range fun i : ℕ => weaklyAssociatedExampleX k i *
    weaklyAssociatedExampleY k i

/-- The ideal generated by the relations `x_i y_i`. -/
def weaklyAssociatedExampleRelationIdeal (k : Type u) [Field k] :
    Ideal (weaklyAssociatedExamplePolynomialRing k) :=
  Ideal.span (weaklyAssociatedExampleRelations k)

/-- The quotient ring `S` in the example. -/
abbrev weaklyAssociatedExampleRing (k : Type u) [Field k] :=
  weaklyAssociatedExamplePolynomialRing k ⧸
    weaklyAssociatedExampleRelationIdeal k

/-- The ring map `R → S` sending `x_i` to its copy in `S`. -/
def weaklyAssociatedExampleMap (k : Type u) [Field k] :
    weaklyAssociatedExampleBaseRing k →+* weaklyAssociatedExampleRing k :=
  (Ideal.Quotient.mk (weaklyAssociatedExampleRelationIdeal k)).comp
    (MvPolynomial.eval₂Hom
      (MvPolynomial.C : k →+* weaklyAssociatedExamplePolynomialRing k)
      (fun i : ℕ => weaklyAssociatedExampleX k i))

/-- The ideal `q = ∑ x_i S` in the example ring. -/
def weaklyAssociatedExampleQ (k : Type u) [Field k] :
    Ideal (weaklyAssociatedExampleRing k) :=
  Ideal.span (Set.range fun i : ℕ =>
    Ideal.Quotient.mk (weaklyAssociatedExampleRelationIdeal k)
      (weaklyAssociatedExampleX k i))

/-- The ideal `(x_1, x_2, ...)` in the base ring. -/
def weaklyAssociatedExampleP (k : Type u) [Field k] :
    Ideal (weaklyAssociatedExampleBaseRing k) :=
  Ideal.span (Set.range (fun i : ℕ => MvPolynomial.X i))

/-- The quotient ring has a weakly associated prime whose pullback is not
weakly associated over the base ring.  The final conjunct records the
finitely generated-annihilator observation in the source example. -/
theorem weaklyAssociated_nonFunctoriality_example
    (k : Type u) [Field k] :
    ∃ hq : (weaklyAssociatedExampleQ k).IsPrime,
      weaklyAssociatedExampleQ k ∈
          minimalPrimes (weaklyAssociatedExampleRing k) ∧
      (⟨weaklyAssociatedExampleQ k, hq⟩ :
          PrimeSpectrum (weaklyAssociatedExampleRing k)) ∈
        weaklyAssociatedPrimes (weaklyAssociatedExampleRing k)
          (weaklyAssociatedExampleRing k) ∧
      (letI : Module (weaklyAssociatedExampleBaseRing k)
          (weaklyAssociatedExampleRing k) :=
          Module.compHom (weaklyAssociatedExampleRing k)
            (weaklyAssociatedExampleMap k)
       PrimeSpectrum.comap (weaklyAssociatedExampleMap k)
           (⟨weaklyAssociatedExampleQ k, hq⟩ :
             PrimeSpectrum (weaklyAssociatedExampleRing k)) ∉
         weaklyAssociatedPrimes (weaklyAssociatedExampleBaseRing k)
           (weaklyAssociatedExampleRing k)) ∧
      (∀ s : weaklyAssociatedExampleRing k, s ≠ 0 →
        (letI : Module (weaklyAssociatedExampleBaseRing k)
            (weaklyAssociatedExampleRing k) :=
            Module.compHom (weaklyAssociatedExampleRing k)
              (weaklyAssociatedExampleMap k)
         ((⊥ : Submodule (weaklyAssociatedExampleBaseRing k)
             (weaklyAssociatedExampleRing k)).colon ({s} : Set _)).FG)) ∧
      (weaklyAssociatedExampleQ k).comap (weaklyAssociatedExampleMap k) =
        weaklyAssociatedExampleP k := by
  sorry

/-- Weakly associated primes pull back along every ring map. -/
theorem weaklyAssociatedPrimes_reverse_functorial
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (φ : R →+* S) :
    (letI : Module R M := Module.compHom M φ;
      weaklyAssociatedPrimes R M ⊆
        PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M) := by
  sorry

/-- The associated/weakly associated spectrum-map inclusion chain. -/
theorem associated_weaklyAssociated_functorial_chain
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (φ : R →+* S) :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ ''
            Formalization.Books.Algebra.Unit63.associatedPrimes S M ⊆
          Formalization.Books.Algebra.Unit63.associatedPrimes R M ∧
        Formalization.Books.Algebra.Unit63.associatedPrimes R M ⊆
          weaklyAssociatedPrimes R M ∧
        weaklyAssociatedPrimes R M ⊆
          PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M) := by
  sorry

/-- If the target ring is Noetherian, every inclusion in the preceding chain
is an equality. -/
theorem associated_weaklyAssociated_functorial_eq_of_noetherian
    {R S M : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing S] [AddCommGroup M] [Module S M]
    (φ : R →+* S) :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ ''
            Formalization.Books.Algebra.Unit63.associatedPrimes S M =
          Formalization.Books.Algebra.Unit63.associatedPrimes R M ∧
        Formalization.Books.Algebra.Unit63.associatedPrimes R M =
          weaklyAssociatedPrimes R M ∧
        weaklyAssociatedPrimes R M =
          PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M) := by
  sorry

/-! ## Finite maps, quotients, and localization -/

/-- A finite ring map preserves the weakly associated-prime set after mapping
the spectrum. -/
theorem weaklyAssociatedPrimes_finite_ring_map
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (φ : R →+* S) (hφ : RingHom.Finite φ) :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M =
        weaklyAssociatedPrimes R M) := by
  sorry

/-- Passing from `R` to `R/I` preserves weakly associated primes via the
canonical injection of spectra. -/
theorem weaklyAssociatedPrimes_quotient_ring
    {R : Type u} {M : Type v} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module (R ⧸ I) M] :
    (letI : Module R M := Module.compHom M (Ideal.Quotient.mk I);
      PrimeSpectrum.comap (Ideal.Quotient.mk I) ''
          weaklyAssociatedPrimes (R ⧸ I) M = weaklyAssociatedPrimes R M) := by
  sorry

/-- The two weakly associated-prime localization equalities. -/
theorem weaklyAssociatedPrimes_localize
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (S : Submonoid R) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      PrimeSpectrum.comap (algebraMap R (Localization S)) ''
          weaklyAssociatedPrimes (Localization S)
            (LocalizedModule S M) =
        weaklyAssociatedPrimes R (LocalizedModule S M) ∧
      weaklyAssociatedPrimes R M ∩
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
        weaklyAssociatedPrimes R (LocalizedModule S M)) := by
  sorry

/-- Localization at elements that are all module nonzerodivisors does not
change the weakly associated-prime set over the original ring. -/
theorem weaklyAssociatedPrimes_localize_of_regular
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (S : Submonoid R)
    (hS : ∀ s : S, IsSMulRegular M (s : R)) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      weaklyAssociatedPrimes R M =
        weaklyAssociatedPrimes R (LocalizedModule S M)) := by
  sorry

/-! ## Detection by localizations -/

/-- The canonical map from a module to the product of its localizations at
its weakly associated primes. -/
def localizationAtWeaklyAssociatedPrimesMap
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    M →ₗ[R]
      ∀ p : {p : PrimeSpectrum R // p ∈ weaklyAssociatedPrimes R M},
        LocalizedModule.AtPrime p.1.asIdeal M :=
  LinearMap.pi fun p =>
    LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl M

/-- The weakly associated-prime localizations detect every module element. -/
theorem localizationAtWeaklyAssociatedPrimesMap_injective
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Function.Injective
      (localizationAtWeaklyAssociatedPrimesMap (R := R) (M := M)) := by
  sorry

/-! ## The post-Bourbaki localization statement -/

/-- For a flat module over a domain, passing to the fraction field preserves
weakly associated primes after identifying the localized spectrum with the
original spectrum. -/
theorem weaklyAssociatedPrimes_post_bourbaki
    {R S N K : Type*} [CommRing R] [CommRing S] [Field K]
    [IsDomain R] [Algebra R S] [Algebra R K]
    [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Flat R N] [IsFractionRing R K] :
    letI : Algebra R S := (algebraMap R S).toAlgebra
    letI : Algebra R K := (algebraMap R K).toAlgebra
    PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            S →+* S ⊗[R] K) ''
        weaklyAssociatedPrimes (S ⊗[R] K)
          (Formalization.Books.Algebra.Unit14.baseChangeModule
            (M := N) (algebraMap R S) (algebraMap R K)) =
      weaklyAssociatedPrimes S N := by
  sorry

/-! ## Change of fields -/

/-- Weakly associated primes descend along extension of the coefficient
field. -/
theorem weaklyAssociatedPrimes_change_fields
    {k K R M : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R]
    [AddCommGroup M] [Module R M] :
    letI : Algebra k R := (algebraMap k R).toAlgebra
    letI : Algebra k K := (algebraMap k K).toAlgebra
    ∀ (q : PrimeSpectrum (R ⊗[k] K)) (p : PrimeSpectrum R),
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            R →+* R ⊗[k] K) q = p →
        q ∈ weaklyAssociatedPrimes (R ⊗[k] K)
          (Formalization.Books.Algebra.Unit14.baseChangeModule
            (M := M) (algebraMap k R) (algebraMap k K)) →
          p ∈ weaklyAssociatedPrimes R M := by
  sorry

end

end Formalization.Books.Algebra.Unit66
