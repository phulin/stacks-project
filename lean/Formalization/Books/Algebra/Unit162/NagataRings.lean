import Formalization.Books.Algebra.Unit161.JapaneseRings
import Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings
import Formalization.Books.Algebra.Unit119.AroundKrullAkizuki
import Formalization.Books.Algebra.Unit157.SerresCriterion
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Commutative Algebra, Chapter 162: Nagata rings

This file records the definitions and theorem interfaces in the section
“Nagata rings”.  N-1 and N-2 are the canonical predicates from Chapter 161;
integral closures, adic completions, associated primes, and finite or
quasi-finite maps use the corresponding Mathlib and earlier-chapter APIs.
-/

namespace Formalization.Books.Algebra.Unit162

open Set
open Formalization.Books.Algebra.Unit161
open Formalization.Books.Algebra.Unit09

universe u v

noncomputable section

/-! ## Japanese and Nagata properties -/

/-- A ring is universally Japanese when every finite-type domain algebra over
it is N-2. -/
def IsUniversallyJapanese (R : Type u) [CommRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] (f : R →+* S),
    RingHom.FiniteType f →
      ∀ (hS : IsDomain S), @IsJapaneseDomain S _ hS

/-- A Nagata ring is Noetherian and has the N-2 property after every prime
quotient. -/
def IsNagataRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (p : Ideal R), ∀ hp : p.IsPrime,
      letI : p.IsPrime := hp
      IsJapaneseDomain (R ⧸ p)

theorem nagata_of_noetherian_universallyJapanese
    {R : Type u} [CommRing R]
    (hR : IsNoetherianRing R) (hU : IsUniversallyJapanese R) :
    IsNagataRing R := by
  sorry

/-! ## Basic permanence lemmas -/

theorem integralClosure_finite_of_nagata_essFiniteType_reduced
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hR : IsNagataRing R)
    (hfinite : RingHom.EssFiniteType f) (hS : IsReduced S) :
    letI : Algebra R S := f.toAlgebra
    Module.Finite R (integralClosure R S) := by
  sorry

theorem universallyJapanese_of_NOne_finiteType
    {R : Type u} [CommRing R]
    (h : ∀ (S : Type u) [CommRing S] (f : R →+* S),
      RingHom.FiniteType f →
        ∀ (hS : IsDomain S), @IsNOne S _ hS) :
    IsUniversallyJapanese R := by
  sorry

theorem universallyJapanese_essFiniteType
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hR : IsUniversallyJapanese R)
    (hfinite : RingHom.EssFiniteType f) :
    IsUniversallyJapanese S := by
  sorry

theorem nagata_of_quasiFinite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hR : IsNagataRing R)
    (hfinite : RingHom.QuasiFinite f) :
    IsNagataRing S := by
  sorry

theorem nagata_localization
    {R : Type u} [CommRing R] (M : Submonoid R)
    (hR : IsNagataRing R) :
    IsNagataRing (Localization M) := by
  sorry

theorem universallyJapanese_of_localizations
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (hlocal : ∀ i, IsUniversallyJapanese (Localization.Away (f i))) :
    IsUniversallyJapanese R := by
  sorry

theorem nagata_of_localizations
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (hlocal : ∀ i, IsNagataRing (Localization.Away (f i))) :
    IsNagataRing R := by
  sorry

theorem nagata_of_noetherian_complete_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    IsNagataRing R := by
  sorry

/-! The source immediately records the standard completion facts.  The
canonical interfaces for faithful flatness, completeness, and Noetherianity
are supplied by Chapters 96–97; this wrapper records their Nagata consequence.
-/

theorem completion_is_nagata
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsNagataRing
      (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  sorry

theorem completion_is_faithfullyFlat
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    RingHom.FaithfullyFlat
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) := by
  sorry

theorem completion_is_noetherian_complete_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ∃ hN : IsNoetherianRing
        (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      ∃ hL : IsLocalRing
          (AdicCompletion (IsLocalRing.maximalIdeal R) R),
        letI : IsNoetherianRing
            (AdicCompletion (IsLocalRing.maximalIdeal R) R) := hN
        letI : IsLocalRing
            (AdicCompletion (IsLocalRing.maximalIdeal R) R) := hL
        IsAdicComplete
          (IsLocalRing.maximalIdeal
            (AdicCompletion (IsLocalRing.maximalIdeal R) R))
          (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  sorry

theorem completion_is_universallyCatenary
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Formalization.Books.Algebra.Unit105.IsUniversallyCatenary
      (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  sorry

/- The source defines analytic unramifiedness for Noetherian local rings;
the predicate is defined for all local rings so it can be used in interfaces
whose Noetherian hypotheses are stated separately. -/
def IsAnalyticallyUnramified
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  IsReduced (AdicCompletion (IsLocalRing.maximalIdeal R) R)

/-- The prime-quotient version of analytic unramifiedness. -/
def PrimeIsAnalyticallyUnramified
    (R : Type u) [CommRing R] [IsLocalRing R]
    (p : Ideal R) (hp : p.IsPrime) : Prop :=
  letI : p.IsPrime := hp
  letI : Nontrivial (R ⧸ p) :=
    Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  letI : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective
  IsAnalyticallyUnramified (R ⧸ p)

/-- A source-facing wrapper for a discrete valuation ring, retaining the
domain instance required by Mathlib's canonical class. -/
def IsDVR (R : Type u) [CommRing R] : Prop :=
  ∃ hR : IsDomain R, @IsDiscreteValuationRing R _ hR

/-- The source's “associated prime of a quotient” relation. -/
def IsAssociatedPrimeOfQuotient
    (R : Type u) [CommRing R] (I q : Ideal R) : Prop :=
  q ∈ _root_.associatedPrimes R (R ⧸ I)

/-- A module has no embedded primes when all its associated primes are
minimal primes. -/
def HasNoEmbeddedPrimes
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∀ p ∈ _root_.associatedPrimes R M, IsMinimalPrime p

/-! ## Analytically unramified rings -/

theorem analyticallyUnramified_isReduced
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : IsAnalyticallyUnramified R) :
    IsReduced R := by
  sorry

theorem analyticallyUnramified_minimalPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : IsAnalyticallyUnramified R) (p : Ideal R)
    (hp : IsMinimalPrime p) :
    PrimeIsAnalyticallyUnramified R p (IsMinimalPrime.isPrime hp) := by
  sorry

theorem analyticallyUnramified_of_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (s : Finset (Ideal R))
    (hs : ∀ p ∈ s, IsMinimalPrime p)
    (hcover : ∀ p, IsMinimalPrime p → p ∈ s)
    (hp : ∀ (p : Ideal R) (hps : p ∈ s),
      PrimeIsAnalyticallyUnramified R p
        (IsMinimalPrime.isPrime (hs p hps))) :
    IsAnalyticallyUnramified R := by
  sorry

theorem integralClosure_finite_of_analyticallyUnramified
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : IsAnalyticallyUnramified R) :
    Module.Finite R (integralClosure R (totalQuotientRing R)) := by
  sorry

theorem isNOne_of_analyticallyUnramified
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsDomain R] (hR : IsAnalyticallyUnramified R) :
    IsNOne R := by
  sorry

theorem codimensionOne_completion_isDVR
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : PrimeSpectrum R)
    (hp : PrimeIsAnalyticallyUnramified R p.asIdeal p.isPrime)
    (hdvr : IsDVR (Localization.AtPrime p.asIdeal))
    (q : PrimeSpectrum
      (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (hq : IsAssociatedPrimeOfQuotient
      (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (p.asIdeal.map (algebraMap R
        (AdicCompletion (IsLocalRing.maximalIdeal R) R))) q.asIdeal) :
    IsDVR (Localization.AtPrime q.asIdeal) := by
  sorry

theorem analyticallyUnramified_of_criterion
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsDomain R] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx0 : x ≠ 0)
    (hnoembedded : HasNoEmbeddedPrimes R
      (R ⧸ Ideal.span ({x} : Set R)))
    (hregular : ∀ p : PrimeSpectrum R,
      IsAssociatedPrimeOfQuotient R (Ideal.span ({x} : Set R)) p.asIdeal →
        IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (hanalytic : ∀ p : PrimeSpectrum R,
      IsAssociatedPrimeOfQuotient R (Ideal.span ({x} : Set R)) p.asIdeal →
        PrimeIsAnalyticallyUnramified R p.asIdeal p.isPrime) :
    IsAnalyticallyUnramified R := by
  sorry

theorem local_nagata_domain_isAnalyticallyUnramified
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsDomain R] (hR : IsNagataRing R) :
    IsAnalyticallyUnramified R := by
  sorry

/-! The three-way local characterization from the source. -/

/-- Analytic unramifiedness at the local ring of a prime. -/
def IsAnalyticallyUnramifiedAtPrime
    (S : Type u) [CommRing S] (p : PrimeSpectrum S) : Prop :=
  IsAnalyticallyUnramified (Localization.AtPrime p.asIdeal)

def FiniteMapAnalyticallyUnramifiedCondition
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] (f : R →+* S),
    RingHom.Finite f → IsDomain S →
      ∀ p : PrimeSpectrum S, p.asIdeal.IsMaximal →
        IsAnalyticallyUnramifiedAtPrime S p

def FiniteLocalMapAnalyticallyUnramifiedCondition
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] [IsLocalRing S]
    (f : R →+* S), IsLocalHom f → RingHom.Finite f → IsDomain S →
      IsAnalyticallyUnramified S

theorem nagata_iff_local_analytic_unramified
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsNagataRing R ↔
      FiniteMapAnalyticallyUnramifiedCondition R ∧
        FiniteLocalMapAnalyticallyUnramifiedCondition R := by
  sorry

/-! ## Nagata's proposition -/

theorem nagata_iff_finiteType_algebras_nagata
    {R : Type u} [CommRing R] :
    IsNagataRing R ↔
      (∀ (S : Type u) [CommRing S] (f : R →+* S),
        RingHom.FiniteType f → IsNagataRing S) := by
  sorry

theorem nagata_iff_universallyJapanese_noetherian
    {R : Type u} [CommRing R] :
    IsNagataRing R ↔ IsUniversallyJapanese R ∧ IsNoetherianRing R := by
  sorry

/-! ## Ubiquity and examples -/

theorem field_isNagata (K : Type u) [Field K] :
    IsNagataRing K := by
  sorry

theorem dedekindDomain_charZero_isNagata
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsDedekindDomain R] [CharZero (FractionRing R)] :
    IsNagataRing R := by
  sorry

theorem int_isNagata : IsNagataRing ℤ := by
  sorry

theorem finiteType_nagata_of_nagata
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hR : IsNagataRing R)
    (hfinite : RingHom.FiniteType f) :
    IsNagataRing S := by
  sorry

theorem dvr_isNagata_iff_isJapaneseDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsDiscreteValuationRing A] :
    IsNagataRing A ↔ IsJapaneseDomain A := by
  sorry

/- The bad characteristic-p DVR example from Chapter 119 supplies the
non-Nagata example mentioned in this section. -/
theorem noetherian_local_domain_nonreduced_completion_not_nagata
    {A : Type u} [CommRing A]
    (hN : IsNoetherianRing A) (hL : IsLocalRing A) (hD : IsDomain A)
    (hbad : ¬ IsReduced (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
    ¬ IsNagataRing A := by
  sorry

theorem bad_dvr_adjoin_not_nagata
    {k : Type u} {p : ℕ} [Field k] [Fact p.Prime] [CharP k p]
    (D : Formalization.Books.Algebra.Unit119.BadDvrExampleData k p)
    (f : PowerSeries k) (hf : f ∉ D.A) :
    ¬ IsNagataRing
      (Formalization.Books.Algebra.Unit119.badDvrAdjoin D f) := by
  sorry

theorem bad_dvr_is_not_nagata
    {k : Type u} {p : ℕ} [Field k] [Fact p.Prime] [CharP k p]
    (D : Formalization.Books.Algebra.Unit119.BadDvrExampleData k p) :
    ¬ IsNagataRing (D.A : Type u) := by
  sorry

/-! ## Frobenius roots in a Nagata completion -/

theorem nagata_pth_root_of_completion_pth_root
    {A : Type u} {p : ℕ} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] [Fact p.Prime] [CharP A p]
    (hA : IsNagataRing A) (a : A)
    (ha : ∃ α : AdicCompletion (IsLocalRing.maximalIdeal A) A,
      α ^ p = algebraMap A
        (AdicCompletion (IsLocalRing.maximalIdeal A) A) a) :
    ∃ b : A, b ^ p = a := by
  sorry

end

end Formalization.Books.Algebra.Unit162
