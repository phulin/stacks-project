import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit72.Depth
import Formalization.Books.Topology.Unit11.CodimensionAndCatenary
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 164: Descending properties

The source section consists of faithfully flat descent for the standard ring
properties, descent of the Nagata property, and a counterexample showing that
universal catenarity does not descend along an étale map.  The named ring
properties below use Mathlib and earlier-chapter predicates whenever those
interfaces already exist.
-/

namespace Formalization.Books.Algebra.Unit164

open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit60
open Formalization.Books.Algebra.Unit72
open Formalization.Books.Topology.Unit11
open Set
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## The source's local conditions -/

/- The introductory warning that descent results are useful only together with
  the corresponding ascent results is explanatory rather than a separate
  mathematical proposition.  The declarations in this file record the
  precise descent assertions that follow it. -/

/-
The source's `(S_k)` condition says that at every prime, local depth is at
least the minimum of `k` and local dimension.  `ringKrullDim` has codomain
`WithBot ℕ∞`, so the depth and the integer are cast to that same canonical
dimension type.
-/
def HasPropertySk (R : Type u) [CommRing R] (k : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R,
    min ((k : ℕ∞) : WithBot ℕ∞)
        (ringKrullDim (Localization.AtPrime p.asIdeal)) ≤
      ((localDepth (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal) : ℕ∞) : WithBot ℕ∞)

/- The source's `(R_k)` condition says that every prime of height at most `k`
  has regular localization.  The Noetherian hypothesis is kept on the
  theorem statements, as in the source, rather than duplicated in this
  predicate. -/
def HasPropertyRk (R : Type u) [CommRing R] (k : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R,
    p.asIdeal.height ≤ (k : ℕ∞) →
      IsRegularLocalRing (Localization.AtPrime p.asIdeal)

/-! ## Japanese and Nagata properties -/

/- N-2 for a domain: the integral closure in every finite extension of its
  fraction field is finite as a module. -/
def IsJapaneseDomain (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K],
    ∀ (L : Type u) [Field L] [Algebra K L] [Algebra R L]
      [IsScalarTower R K L] [Module.Finite K L],
      Module.Finite R (integralClosure R L)

/- A universally Japanese ring is one for which every finite-type algebra that
  is a domain is Japanese.  The domain assumption is explicit because the
  source quantifies only over domain targets. -/
def IsUniversallyJapanese (R : Type u) [CommRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] (f : R →+* S),
    RingHom.FiniteType f →
      ∀ (hS : IsDomain S), @IsJapaneseDomain S _ hS

/- A Nagata ring is Noetherian and has N-2 quotients at all prime ideals. -/
def IsNagataRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (p : Ideal R) [p.IsPrime], IsJapaneseDomain (R ⧸ p)

/- The characterization invoked in the proof of Nagata descent. -/
theorem nagata_iff_noetherian_universallyJapanese
    {R : Type u} [CommRing R] :
    IsNagataRing R ↔ IsNoetherianRing R ∧ IsUniversallyJapanese R := by
  sorry

/-! ## Catenarity interfaces used by the final counterexample -/

/- Mathlib's topological catenary predicate is the canonical chain condition
  used here for the prime spectrum. -/
def IsCatenaryRing (R : Type u) [CommRing R] : Prop :=
  Formalization.Books.Topology.Unit11.IsCatenary (PrimeSpectrum R)

/- Universal catenarity is catenarity after every finite-type base change. -/
def IsUniversallyCatenary (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (S : Type u) [CommRing S] (f : R →+* S),
      RingHom.FiniteType f → IsCatenaryRing S

/- The map from a ring to the localization of a target ring at one of its
  prime ideals, used to state that the maximal ideal of `A` generates the
  maximal ideal after localization. -/
noncomputable def mapToPrimeLocalization
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (p : PrimeSpectrum B) :
    A →+* Localization.AtPrime p.asIdeal :=
  (algebraMap B (Localization.AtPrime p.asIdeal)).comp f

/-! ## Faithfully flat descent -/

/- The informal proof uses the faithfully flat ideal criterion for the
  Noetherian condition; later proofs use the corresponding nilradical,
  localization, and local-criterion arguments. -/

theorem noetherian_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f)
    (hS : IsNoetherianRing S) : IsNoetherianRing R := by
  sorry

theorem reduced_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f)
    (hS : IsReduced S) : IsReduced R := by
  sorry

theorem normal_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f)
    (hS : IsNormalRing S) : IsNormalRing R := by
  sorry

theorem regular_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f)
    (hS : IsRegularRing S) : IsRegularRing R := by
  sorry

theorem propertySk_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f) (k : ℕ)
    (hS : IsNoetherianRing S) (hSk : HasPropertySk S k) :
    IsNoetherianRing R ∧ HasPropertySk R k := by
  sorry

theorem propertyRk_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f) (k : ℕ)
    (hS : IsNoetherianRing S) (hRk : HasPropertyRk S k) :
    IsNoetherianRing R ∧ HasPropertyRk R k := by
  sorry

/- Smoothness and surjectivity on spectra are the exact hypotheses in the
  source's Nagata descent lemma.  The proof route is the finite-type local
  criterion for the N-2 property together with surjectivity of `Spec S →
  Spec R`. -/
theorem nagata_descends_of_smooth_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hsmooth : RingHom.Smooth f)
    (hsurjective : Function.Surjective (PrimeSpectrum.comap f))
    (hS : IsNagataRing S) : IsNagataRing R := by
  sorry

/-! ## The universally catenary counterexample -/

/- The final source remark is an existence construction.  This structure
  records its rings, all ring maps, the finite/formally-unramified map,
  semilocal and local data, the residue-field identifications, the tensor
  product decomposition, the two minimal primes and quotient identifications,
  and the contrasting catenarity conclusions. -/
structure UniversallyCatenaryDescentCounterexample where
  A : Type u
  B : Type u
  A' : Type u
  B₁ : Type u
  B₂ : Type u
  [commRingA : CommRing A]
  [commRingB : CommRing B]
  [commRingA' : CommRing A']
  [commRingB₁ : CommRing B₁]
  [commRingB₂ : CommRing B₂]
  [localA : IsLocalRing A]
  [localA' : IsLocalRing A']
  f : A →+* B
  finite : RingHom.Finite f
  formallyUnramified : RingHom.FormallyUnramified f
  noetherianA : IsNoetherianRing A
  notUniversallyCatenaryA : ¬ IsUniversallyCatenary A
  m : PrimeSpectrum B
  n : PrimeSpectrum B
  m_maximal : m.asIdeal.IsMaximal
  n_maximal : n.asIdeal.IsMaximal
  distinct_maximals : m ≠ n
  semilocal : ∀ q : PrimeSpectrum B, q.asIdeal.IsMaximal → q = m ∨ q = n
  m_regular : IsRegularLocalRing (Localization.AtPrime m.asIdeal)
  m_dimension : ringKrullDim (Localization.AtPrime m.asIdeal) = 2
  n_regular : IsRegularLocalRing (Localization.AtPrime n.asIdeal)
  n_dimension : ringKrullDim (Localization.AtPrime n.asIdeal) = 1
  m_residueField :
    letI : m.asIdeal.IsMaximal := m_maximal
    Nonempty (m.asIdeal.ResidueField ≃+* IsLocalRing.ResidueField A)
  n_residueField :
    letI : n.asIdeal.IsMaximal := n_maximal
    Nonempty (n.asIdeal.ResidueField ≃+* IsLocalRing.ResidueField A)
  m_maximalIdeal_generates :
    Ideal.map (mapToPrimeLocalization f m) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal)
  n_maximalIdeal_generates :
    Ideal.map (mapToPrimeLocalization f n) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal)
  baseChange : A →+* A'
  baseChange_local : IsLocalHom baseChange
  baseChange_etale : RingHom.Etale baseChange
  factorMap₁ : A' →+* B₁
  factorMap₂ : A' →+* B₂
  factorMap₁_surjective : Function.Surjective factorMap₁
  factorMap₂_surjective : Function.Surjective factorMap₂
  tensorProduct_factors :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A A' := baseChange.toAlgebra
    ∃ e : B ⊗[A] A' ≃+* B₁ × B₂,
      factorMap₁ =
        (RingHom.fst B₁ B₂).comp
          (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ∧
      factorMap₂ =
        (RingHom.snd B₁ B₂).comp
          (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  B₁_regular : IsRegularLocalRing B₁
  B₂_regular : IsRegularLocalRing B₂
  q₁ : Ideal A'
  q₂ : Ideal A'
  q₁_minimal : q₁ ∈ minimalPrimes A'
  q₂_minimal : q₂ ∈ minimalPrimes A'
  distinct_minimal_primes : q₁ ≠ q₂
  exactly_two_minimal_primes :
    ∀ q : Ideal A', q ∈ minimalPrimes A' → q = q₁ ∨ q = q₂
  quotient₁ :
    letI : q₁.IsPrime := q₁_minimal.isPrime
    ∃ e : (A' ⧸ q₁) ≃+* B₁,
      e.toRingHom.comp (Ideal.Quotient.mk q₁) = factorMap₁
  quotient₂ :
    letI : q₂.IsPrime := q₂_minimal.isPrime
    ∃ e : (A' ⧸ q₂) ≃+* B₂,
      e.toRingHom.comp (Ideal.Quotient.mk q₂) = factorMap₂
  universallyCatenaryA' : IsUniversallyCatenary A'

attribute [instance] UniversallyCatenaryDescentCounterexample.commRingA
  UniversallyCatenaryDescentCounterexample.commRingB
  UniversallyCatenaryDescentCounterexample.commRingA'
  UniversallyCatenaryDescentCounterexample.commRingB₁
  UniversallyCatenaryDescentCounterexample.commRingB₂
  UniversallyCatenaryDescentCounterexample.localA
  UniversallyCatenaryDescentCounterexample.localA'

/- Universal catenarity therefore fails to descend even though the displayed
  base-change map is local and étale. -/
theorem exists_universallyCatenary_descent_counterexample :
    Nonempty (UniversallyCatenaryDescentCounterexample.{u}) := by
  sorry

end

end Formalization.Books.Algebra.Unit164
