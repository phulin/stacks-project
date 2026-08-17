import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit54.EssentiallyFiniteType
import Formalization.Books.Topology.Unit20.DimensionFunctions
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.MvPolynomial

/-!
# Commutative Algebra, Chapter 105: Catenary rings

The ring-theoretic catenary predicate uses finite strict chains in the prime
spectrum.  The maximal-chain interface is the canonical one from Topology,
Chapter 11, while universal catenarity and essential finite type use the
established algebra predicates.
-/

namespace Formalization.Books.Algebra.Unit105

universe u v

noncomputable section

/-! ## Prime chains and catenary rings -/

/- A finite strict chain in `Spec R` with prescribed endpoints. -/
def IsPrimeChainBetween
    {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) (hpq : p ≤ q)
    (c : LTSeries (Set.Iic q)) : Prop :=
  c.head = (⟨p, hpq⟩ : Set.Iic q) ∧
    c.last = (⟨q, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic q)

/- The source's bounded-chain/equal-maximal-chain definition. -/
def IsCatenaryRing (R : Type u) [CommRing R] : Prop :=
  ∀ ⦃p q : PrimeSpectrum R⦄ (hpq : p < q),
    ∃ n : ℕ,
      (∀ c : LTSeries (Set.Iic q),
        IsPrimeChainBetween p q (le_of_lt hpq) c → c.length ≤ n) ∧
        ∀ c d : LTSeries (Set.Iic q),
          Formalization.Books.Topology.Unit11.IsMaximalChainBetween
            p q (le_of_lt hpq) c →
          Formalization.Books.Topology.Unit11.IsMaximalChainBetween
            p q (le_of_lt hpq) d →
          c.length = d.length

/- The direct comparison with the topological catenary predicate on `Spec R`. -/
theorem isCatenaryRing_iff_isCatenary_primeSpectrum
    (R : Type u) [CommRing R] :
    IsCatenaryRing R ↔
      Formalization.Books.Topology.Unit11.IsCatenary (PrimeSpectrum R) := by
  sorry

/-! ## Universal catenarity -/

/- An algebra of finite type is represented by the canonical algebra class. -/
def IsUniversallyCatenary (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
      IsCatenaryRing S

/- The source warns that catenarity is not preserved by arbitrary finite-type
   algebras over a catenary ring.  Since the warning supplies no quantified
   counterexample, it is retained here as documentation rather than promoted
   to an unsupported standalone existence theorem. -/

/- The polynomial-algebra test stated immediately after the definition. -/
theorem isUniversallyCatenary_iff_mPolynomial
    (R : Type u) [CommRing R] :
    IsUniversallyCatenary R ↔
      IsNoetherianRing R ∧
        ∀ n : ℕ, IsCatenaryRing (MvPolynomial (Fin n) R) := by
  sorry

/-! ## Localization, essential finite type, and local checking -/

theorem isCatenaryRing_localization
    (R : Type u) [CommRing R] (S : Submonoid R)
    (hR : IsCatenaryRing R) :
    IsCatenaryRing (Localization S) := by
  sorry

theorem isUniversallyCatenary_localization
    (R : Type u) [CommRing R] (S : Submonoid R)
    (hR : IsUniversallyCatenary R) :
    IsUniversallyCatenary (Localization S) := by
  sorry

theorem isUniversallyCatenary_of_essFiniteType
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (hA : IsUniversallyCatenary A)
    (hB : Algebra.EssFiniteType A B) :
    IsUniversallyCatenary B := by
  sorry

theorem isCatenaryRing_localization_iff
    (R : Type u) [CommRing R] :
    List.TFAE
      [ IsCatenaryRing R
      , ∀ p : PrimeSpectrum R,
          IsCatenaryRing (Localization.AtPrime p.asIdeal)
      , ∀ m : MaximalSpectrum R,
          IsCatenaryRing (Localization.AtPrime m.asIdeal) ] := by
  sorry

theorem isUniversallyCatenary_localization_iff
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    List.TFAE
      [ IsUniversallyCatenary R
      , ∀ p : PrimeSpectrum R,
          IsUniversallyCatenary (Localization.AtPrime p.asIdeal)
      , ∀ m : MaximalSpectrum R,
          IsUniversallyCatenary (Localization.AtPrime m.asIdeal) ] := by
  sorry

/-! ## Quotients and minimal components -/

theorem isCatenaryRing_quotient
    (R : Type u) [CommRing R] (I : Ideal R)
    (hR : IsCatenaryRing R) :
    IsCatenaryRing (R ⧸ I) := by
  sorry

theorem isUniversallyCatenary_quotient
    (R : Type u) [CommRing R] (I : Ideal R)
    (hR : IsUniversallyCatenary R) :
    IsUniversallyCatenary (R ⧸ I) := by
  sorry

theorem isCatenaryRing_iff_quotient_minimalPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsCatenaryRing R ↔
      ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R →
        IsCatenaryRing (R ⧸ p.asIdeal) := by
  sorry

theorem isUniversallyCatenary_iff_quotient_minimalPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsUniversallyCatenary R ↔
      ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R →
        IsUniversallyCatenary (R ⧸ p.asIdeal) := by
  sorry

/-! ## Cohen--Macaulay rings and modules -/

theorem isUniversallyCatenary_of_isCohenMacaulayRing
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing R) :
    IsUniversallyCatenary R := by
  sorry

theorem isUniversallyCatenary_of_isCohenMacaulayModule
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Formalization.Books.Algebra.Unit103.IsCohenMacaulayModule R M)
    (hsupp : Module.support R M = Set.univ) :
    IsUniversallyCatenary R := by
  sorry

/-! ## Dimension functions on a Noetherian local ring -/

/-
The topological dimension function has integer values, whereas Mathlib's
Krull dimension has values in `WithBot ℕ∞`.  This predicate records the source
map `p ↦ dim(A / p)` by requiring a nonnegative integer-valued function whose
canonical `toNat` value is that quotient dimension.
-/
def IsPrimeQuotientDimensionFunction
    (A : Type u) [CommRing A]
    (δ : PrimeSpectrum A → ℤ) : Prop :=
  Formalization.Books.Topology.Unit20.IsDimensionFunction δ ∧
    ∀ p : PrimeSpectrum A,
      0 ≤ δ p ∧
        (((δ p).toNat : ℕ∞) : WithBot ℕ∞) =
          ringKrullDim (A ⧸ p.asIdeal)

theorem isCatenaryRing_iff_primeQuotientDimensionFunction
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    IsCatenaryRing A ↔
      ∃ δ : PrimeSpectrum A → ℤ,
        IsPrimeQuotientDimensionFunction A δ := by
  sorry

end

end Formalization.Books.Algebra.Unit105
