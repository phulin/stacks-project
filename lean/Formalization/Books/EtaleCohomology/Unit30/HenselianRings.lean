import Formalization.Books.Algebra.Unit154.FilteredColimitsEtale
import Formalization.Books.Algebra.Unit155.Henselization
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Étale Cohomology, Chapter 30: Henselian rings

This file records the source-facing interfaces in the section “Henselian
rings”.  The algebraic definitions and stronger characterization theorem are
reused from the earlier commutative-algebra formalizations; the structures
below retain the extra decomposition and residue-field data stated in this
section.
-/

namespace Formalization.Books.EtaleCohomology.Unit30

open CategoryTheory
open Polynomial
open Set
open scoped TensorProduct

open Formalization.Books.Algebra.Unit153
open Formalization.Books.Algebra.Unit154
open Formalization.Books.Algebra.Unit155

noncomputable section

universe u v

/-! ## The quasi-finite étale localization theorem -/

/-- The special-fibre dimension condition in the first theorem of the source. -/
def FiberComponentsHaveDimensionAtLeastOne
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (p : PrimeSpectrum A) : Prop :=
  ∀ Z ∈ irreducibleComponents
      (PrimeSpectrum (C ⊗[A] p.asIdeal.ResidueField)),
    1 ≤ topologicalKrullDim Z

/-- The decomposition of a finite-type algebra after an étale localization at a
point.  A finite product is represented by a dependent function over `Fin n`. -/
structure QuasiFiniteEtaleLocalizationData
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) where
  A' : Type u
  [commRingA' : CommRing A']
  [algebraAA' : Algebra A A']
  [etaleAA' : Algebra.Etale A A']
  p' : PrimeSpectrum A'
  p'_over_p : p'.asIdeal.comap (algebraMap A A') = p.asIdeal
  residueEquiv : Nonempty (p.asIdeal.ResidueField ≃+* p'.asIdeal.ResidueField)
  n : ℕ
  factor : Fin n → Type u
  [commRingFactor : ∀ i, CommRing (factor i)]
  [algebraA'Factor : ∀ i, Algebra A' (factor i)]
  remainder : Type u
  [commRingRemainder : CommRing remainder]
  [algebraA'Remainder : Algebra A' remainder]
  decomposition : Nonempty
    ((B ⊗[A] A') ≃+* (∀ i, factor i) × remainder)
  finiteFactor : ∀ i, RingHom.Finite (algebraMap A' (factor i))
  uniquePrimeOver : ∀ i,
    ∃! q : PrimeSpectrum (factor i),
      q.asIdeal.comap (algebraMap A' (factor i)) = p'.asIdeal
  positiveDimensionalRemainder :
    FiberComponentsHaveDimensionAtLeastOne (A := A') (C := remainder) p'

/-- Source theorem: after an étale localization at a prime of the base, the
finite-type algebra splits into finite pieces over the chosen point and a
remainder with positive-dimensional special fibre. -/
theorem quasi_finite_etale_locally
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (p : PrimeSpectrum A) :
    Nonempty (QuasiFiniteEtaleLocalizationData A B p) := by
  sorry

/-! ## Hensel's lemma and the definition of henselianity -/

/- The source's two displayed versions are the specializations of the
canonical root- and coprime-factor lifting interfaces from Algebra, Chapter
153.  Keeping those interfaces avoids introducing a second residue map for a
`p`-adic ring. -/

theorem hensel_root_lifting
    (R : Type u) [CommRing R]
    [HenselianLocalRing R] :
    HenselianRootLifting R := by
  sorry

theorem hensel_coprime_factor_lifting
    (R : Type u) [CommRing R]
    [HenselianLocalRing R] :
    MonicFactorizationLift R := by
  sorry

/-- Reduction of a polynomial over `ℤ_[p]` modulo its maximal ideal. -/
def pAdicResiduePolynomial (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ_[p]) : Polynomial (ZMod p) :=
  f.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)

theorem hensel_factorization_padic (p : ℕ) [Fact p.Prime] :
    ∀ f : Polynomial ℤ_[p], f.Monic →
      ∀ g₀ h₀ : Polynomial (ZMod p),
        pAdicResiduePolynomial p f = g₀ * h₀ → IsCoprime g₀ h₀ →
          ∃ g h : Polynomial ℤ_[p],
            f = g * h ∧ pAdicResiduePolynomial p g = g₀ ∧
              pAdicResiduePolynomial p h = h₀ := by
  sorry

theorem hensel_simple_root_padic (p : ℕ) [Fact p.Prime] :
    ∀ f : Polynomial ℤ_[p], f.Monic → ∀ a₀ : ZMod p,
      (pAdicResiduePolynomial p f).IsRoot a₀ →
      (pAdicResiduePolynomial p f.derivative).eval a₀ ≠ 0 →
        ∃ a : ℤ_[p], f.IsRoot a ∧ PadicInt.toZMod a = a₀ := by
  sorry

/- The definition in the source is exactly the root-lifting predicate already
provided by the algebra chapter; this equivalence records its Chapter 30
use without making a parallel definition. -/
theorem henselian_iff_root_lifting
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsHenselian R ↔ HenselianRootLifting R := by
  sorry

/-! ## Complete local rings and the five source characterizations -/

/-- The source's complete-local-ring hypothesis, expressed by Mathlib's
adic-completeness class at the maximal ideal. -/
abbrev CompleteLocalRing (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal R) R

theorem complete_local_rings_henselian
    (R : Type u) [CommRing R] [IsLocalRing R]
    [CompleteLocalRing R] :
    HenselianLocalRing R := by
  exact complete_local_henselian R

/-- The finite-type decomposition occurring in characterization (4) of the
source theorem. -/
structure FiniteTypeHenselianDecompositionData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] where
  n : ℕ
  localFactor : Fin n → Type u
  [commRingFactor : ∀ i, CommRing (localFactor i)]
  [algebraFactor : ∀ i, Algebra R (localFactor i)]
  [isLocalFactor : ∀ i, IsLocalRing (localFactor i)]
  remainder : Type u
  [commRingRemainder : CommRing remainder]
  [algebraRemainder : Algebra R remainder]
  factorFinite : ∀ i, RingHom.Finite (algebraMap R (localFactor i))
  decomposition : Nonempty (S ≃ₐ[R] (∀ i, localFactor i) × remainder)
  remainderFiber : PositiveDimensionalFiber R remainder

def FiniteTypeHenselianDecompositionProperty
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S],
    Algebra.FiniteType R S →
      Nonempty (FiniteTypeHenselianDecompositionData R S)

/-- The splitting property in characterization (5) of the source theorem. -/
def EtaleResidueSplittingProperty
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {A : Type u} [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (n : Ideal A),
    n.IsMaximal →
    n.comap (algebraMap R A) = IsLocalRing.maximalIdeal R →
    Nonempty (IsLocalRing.ResidueField R ≃+* A ⧸ n) →
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra R A'),
      Nonempty (A ≃ₐ[R] R × A') ∧
        ∃ e : A ≃ₐ[R] R × A',
          Ideal.map e.toRingEquiv.toRingHom n =
            Ideal.prod (IsLocalRing.maximalIdeal R) ⊤

/-- The five equivalent conditions stated in the source.  The imported
algebra chapter proves a stronger thirteen-way characterization; this
Chapter 30 theorem keeps the source's exact five interfaces visible. -/
theorem henselian_characterizations
    (R : Type u) [CommRing R] [IsLocalRing R] :
    List.TFAE
      [ IsHenselian R,
        FactorizationLift R,
        FiniteProductOfLocalAlgebrasProperty R,
        FiniteTypeHenselianDecompositionProperty R,
        EtaleResidueSplittingProperty R ] := by
  sorry

/-! ## Finite algebras and strictly henselian rings -/

theorem finite_over_henselian_local_product
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R]
    (hS : RingHom.Finite (algebraMap R S)) :
    Nonempty (FiniteHenselianLocalProductData R S) := by
  exact finite_over_henselian hS

/- The source definition is Mathlib's separably-closed-residue-field
extension of `HenselianLocalRing`, imported from Algebra, Chapter 153. -/
abbrev StrictlyHenselian (R : Type u) [CommRing R] : Prop :=
  StrictlyHenselianLocalRing R

/-! ## The power-series example -/

/-- The algebra displayed in the power-series example, with the variable
inverted before imposing `X^n = t`. -/
abbrev LaurentRootExtension
    (R : Type u) [CommRing R] (t : R) (n : ℕ) : Type u :=
  (Localization.Away (Polynomial.X : Polynomial R)) ⧸
    Ideal.span ({algebraMap (Polynomial R)
      (Localization.Away (Polynomial.X : Polynomial R))
      ((Polynomial.X : Polynomial R) ^ n - Polynomial.C t)} :
        Set (Localization.Away (Polynomial.X : Polynomial R)))

abbrev ComplexPowerSeries := PowerSeries ℂ

abbrev ComplexPowerSeriesLaurentRootExtension (n : ℕ) : Type :=
  LaurentRootExtension (PowerSeries ℂ) (PowerSeries.X : PowerSeries ℂ) n

/-- A finite product of the two kinds of étale algebra displayed in the
power-series example.  The degrees of the nontrivial factors may vary. -/
structure ComplexPowerSeriesEtaleProductData
    (S : Type u) [CommRing S]
    [Algebra (PowerSeries ℂ) S] [Algebra.Etale (PowerSeries ℂ) S] where
  trivialCount : ℕ
  rootCount : ℕ
  rootDegree : Fin rootCount → ℕ
  decomposition : Nonempty
    (S ≃+*
      (∀ _ : Fin trivialCount, PowerSeries ℂ) ×
        (∀ i : Fin rootCount,
          ComplexPowerSeriesLaurentRootExtension (rootDegree i)))

theorem complex_power_series_etale_classification
    (S : Type u) [CommRing S]
    [Algebra (PowerSeries ℂ) S] [Algebra.Etale (PowerSeries ℂ) S] :
    Nonempty (ComplexPowerSeriesEtaleProductData S) := by
  sorry

/- A small source-facing interface for the covering assertion in the example.
The joint-surjectivity condition is the affine form of a covering family of
spectra, and a retraction of one member is exactly a refinement by the
identity covering. -/
structure EtaleCoveringFamily
    (R : Type u) [CommRing R] where
  index : Type u
  algebra : index → CommRingCat.{u}
  [baseAlgebra : ∀ i, Algebra R (algebra i)]
  [etaleAlgebra : ∀ i, Algebra.Etale R (algebra i)]

def IsEtaleCovering
    {R : Type u} [CommRing R] (F : EtaleCoveringFamily R) : Prop :=
  ∀ p : PrimeSpectrum R, ∃ i,
    letI := F.baseAlgebra i
    ∃ q : PrimeSpectrum (F.algebra i),
      q.asIdeal.comap (algebraMap R (F.algebra i)) = p.asIdeal

def HasIdentityRefinement
    {R : Type u} [CommRing R] (F : EtaleCoveringFamily R) : Prop :=
  ∃ i, letI := F.baseAlgebra i
    Nonempty (F.algebra i →ₐ[R] R)

theorem complex_power_series_etale_cover_has_identity_refinement
    (F : EtaleCoveringFamily (PowerSeries ℂ))
    (hF : IsEtaleCovering F) :
    HasIdentityRefinement F := by
  sorry

/- The final sentence about vanishing higher étale cohomology is a consequence
of the étale-site cohomology theory developed later; no such cohomology
object is introduced in this chapter, so it is intentionally not duplicated
here. -/

/-! ## Henselization and strict henselization -/

/-- A separable algebraic closure of the residue field, using the canonical
field-theoretic predicates from the algebra formalization. -/
abbrev SeparableAlgebraicClosure (k K : Type u) [Field k] [Field K]
    [Algebra k K] : Prop :=
  IsSeparableAlgebraicClosure k K

/-- Chapter 30's diagram `R → Rʰ → Rˢʰ`, with flat local maps, filtered étale
colimit presentations, the henselianity assertions, and the residue-field
identifications stated in the source. -/
structure HenselizationDiagram
    (R K : Type u) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (hK : SeparableAlgebraicClosure
      (IsLocalRing.ResidueField R) K) where
  henselization : Type u
  [commRingHenselization : CommRing henselization]
  [localRingHenselization : IsLocalRing henselization]
  strictHenselization : Type u
  [commRingStrictHenselization : CommRing strictHenselization]
  [localRingStrictHenselization : IsLocalRing strictHenselization]
  henselizationMap : R →+* henselization
  henselizationLocal : IsLocalHom henselizationMap
  henselizationFlat : RingHom.Flat henselizationMap
  henselian : HenselianLocalRing henselization
  henselizationEtaleColimit :
    IsFilteredColimitOfEtale henselizationMap
  strictMap : R →+* strictHenselization
  strictLocal : IsLocalHom strictMap
  strictFlat : RingHom.Flat strictMap
  strictHenselian : StrictlyHenselianLocalRing strictHenselization
  strictEtaleColimit : IsFilteredColimitOfEtale strictMap
  mapFromHenselization : henselization →+* strictHenselization
  mapFromHenselizationLocal : IsLocalHom mapFromHenselization
  mapFromHenselizationFlat : RingHom.Flat mapFromHenselization
  commutes : mapFromHenselization.comp henselizationMap = strictMap
  henselizationMaximalIdeal_eq :
    Ideal.map henselizationMap (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal henselization
  strictMaximalIdeal_eq :
    Ideal.map strictMap (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal strictHenselization
  henselizationResidueEquiv :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField henselization
  strictResidueEquiv : K ≃+* IsLocalRing.ResidueField strictHenselization

theorem exists_henselization_and_strict_henselization
    (R K : Type u) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (hK : SeparableAlgebraicClosure
      (IsLocalRing.ResidueField R) K) :
    Nonempty (HenselizationDiagram R K hK) := by
  sorry

end

end Formalization.Books.EtaleCohomology.Unit30
