import Formalization.Books.Algebra.Unit30.MoreOnImages
import Formalization.Books.Algebra.Unit31.NoetherianRings
import Formalization.Books.Algebra.Unit34.HilbertNullstellensatz
import Formalization.Books.Topology.Unit18.JacobsonSpaces
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Commutative Algebra, Chapter 35: Jacobson rings

The source's Jacobson-ring predicate, closed points, residue fields,
localizations, constructible sets, and irreducible components use the
canonical Mathlib interfaces.  The long matrix examples retain their
polynomial relations, group actions, rank normal forms, and component
statements as usable declarations; their proofs belong to the proving stage.
-/

namespace Formalization.Books.Algebra.Unit35

open Set
open _root_.Topology
open scoped Polynomial TensorProduct

universe u v w

noncomputable section

/-! ## Definition and first criteria -/

/- The source definition is Mathlib's canonical `IsJacobsonRing` class. -/
theorem jacobsonRing_iff_radical_ideal {R : Type u} [CommRing R] :
    IsJacobsonRing R ↔ ∀ I : Ideal R, I.IsRadical → I.jacobson = I := by
  exact isJacobsonRing_iff

theorem primeSpectrum_closedPoints_eq_maximalIdeals {R : Type u} [CommRing R] :
    closedPoints (PrimeSpectrum R) =
      {p : PrimeSpectrum R | p.asIdeal.IsMaximal} := by
  sorry

/- A field and the usual finite-type algebras over a field are Jacobson. -/
theorem finiteType_algebra_over_field_isJacobson
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    IsJacobsonRing A := by
  exact isJacobsonRing_of_finiteType (A := k) (B := A)

theorem jacobson_of_prime_ideals_are_jacobson
    {R : Type u} [CommRing R]
    (h : ∀ P : Ideal R, P.IsPrime → P.jacobson = P) :
    IsJacobsonRing R := by
  exact isJacobsonRing_iff_prime_eq.mpr h

theorem jacobson_iff_primeSpectrum_isJacobsonSpace
    {R : Type u} [CommRing R] :
    IsJacobsonRing R ↔ JacobsonSpace (PrimeSpectrum R) := by
  exact PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace

/- The localization and closed-subset notation used in the next criterion. -/
def primeSpectrumLocallyClosedSet {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (f : R) : Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus (p.asIdeal : Set R) ∩
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))

abbrev primeSpectrumLocalizationAtPrimeElement {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (f : R) :=
  Localization.Away (Ideal.Quotient.mk p.asIdeal f)

theorem characterize_nonJacobson_ring
    {R : Type u} [CommRing R] :
    ¬ IsJacobsonRing R →
      ∃ (p : PrimeSpectrum R) (f : R),
        ¬ p.asIdeal.IsMaximal ∧ f ∉ p.asIdeal ∧
          primeSpectrumLocallyClosedSet p f = {p} ∧
          IsField (primeSpectrumLocalizationAtPrimeElement p f) := by
  sorry

theorem jacobson_locally_closed_sets_infinite
    {R : Type u} [CommRing R] [IsJacobsonRing R]
    (p : PrimeSpectrum R) (f : R)
    (hp : ¬ p.asIdeal.IsMaximal) (hf : f ∉ p.asIdeal) :
    (primeSpectrumLocallyClosedSet p f).Infinite := by
  sorry

/-! ## The PID criterion and elementary examples -/

theorem integer_isJacobson : IsJacobsonRing ℤ := by
  sorry

theorem isJacobsonRing_of_domain_noetherian_nonzero_primes_maximal
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hprime : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → P.IsMaximal)
    (hinfinite : ({P : Ideal R | P.IsMaximal} : Set (Ideal R)).Infinite) :
    IsJacobsonRing R := by
  sorry

/- The “unit times idempotent” property and the quotient-localization property
   used in the product-of-fields example. -/
def IsUnitMulIdempotent {R : Type u} [CommRing R] (f : R) : Prop :=
  ∃ u e : R, IsUnit u ∧ IsIdempotentElem e ∧ f = u * e

def LocalizationAwayIsQuotient (R : Type u) [CommRing R] : Prop :=
  ∀ f : R, ∃ I : Ideal R, Nonempty (Localization.Away f ≃+* R ⧸ I)

theorem isJacobsonRing_of_localizationAwayIsQuotient
    {R : Type u} [CommRing R] (h : LocalizationAwayIsQuotient R) :
    IsJacobsonRing R := by
  sorry

abbrev ProductOfFields (A : Type u) (k : A → Type v) := ∀ a, k a

theorem productOfFields_element_unit_mul_idempotent
    (A : Type u) (k : A → Type v) [∀ a, Field (k a)] :
    ∀ f : ProductOfFields A k, IsUnitMulIdempotent f := by
  sorry

theorem productOfFields_localization_identities
    (A : Type u) (k : A → Type v) [∀ a, Field (k a)]
    (f : ProductOfFields A k) :
    ∃ (u e : ProductOfFields A k),
      IsUnit u ∧ IsIdempotentElem e ∧ f = u * e ∧
        PrimeSpectrum.basicOpen f = PrimeSpectrum.basicOpen e ∧
        Nonempty (Localization.Away f ≃+* Localization.Away e) ∧
        Nonempty
          (Localization.Away e ≃+*
            (ProductOfFields A k ⧸ Ideal.span ({1 - e} : Set (ProductOfFields A k)))) := by
  sorry

theorem productOfFields_isJacobson
    (A : Type u) [Infinite A] (k : A → Type v) [∀ a, Field (k a)] :
    IsJacobsonRing (ProductOfFields A k) := by
  sorry

theorem finite_maximal_domain_isJacobson_iff_isField
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)] :
    IsJacobsonRing R ↔ IsField R := by
  sorry

theorem discreteValuationRing_not_isJacobson
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ¬ IsJacobsonRing R := by
  sorry

theorem localRing_with_two_prime_ideals_not_isJacobson
    {R : Type u} [CommRing R] [IsLocalRing R]
    (h : ∃ p q : PrimeSpectrum R, p ≠ q) :
    ¬ IsJacobsonRing R := by
  sorry

/-! ## Residue fields and cardinality -/

@[instance_reducible]
noncomputable def residueFieldAlgebraOfBaseAlgebra
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (p : Ideal R) [p.IsPrime] : Algebra k p.ResidueField :=
  Algebra.compHom p.ResidueField (algebraMap k R)

@[instance_reducible]
noncomputable def residueFieldAlgebraOfMap
    {R S : Type*} [CommRing R] [CommRing S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (φ : R →+* S) (h : p = q.comap φ) :
    Algebra p.ResidueField q.ResidueField :=
  (Ideal.ResidueField.map p q φ h).toAlgebra

theorem maximal_residueField_isMaximal_of_algebraic
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (m : MaximalSpectrum R) (q : PrimeSpectrum S)
    (h : m.asIdeal = q.asIdeal.comap φ)
    (halg :
      letI : Algebra m.asIdeal.ResidueField q.asIdeal.ResidueField :=
        residueFieldAlgebraOfMap m.asIdeal q.asIdeal φ h
      Algebra.IsAlgebraic m.asIdeal.ResidueField q.asIdeal.ResidueField) :
    q.asIdeal.IsMaximal := by
  sorry

theorem linear_operator_has_noninvertible_monic_polynomial
    {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Nontrivial V]
    (hcard : Module.rank k V < Cardinal.mk k) :
    ∀ T : Module.End k V,
      ∃ P : Polynomial k, P.Monic ∧ ¬ IsUnit (Polynomial.aeval T P) := by
  sorry

theorem uncountable_nullstellensatz
    {k S I : Type u} [Field k] [CommRing S] [Algebra k S]
    (x : I → S) (hgen : Algebra.adjoin k (Set.range x) = ⊤)
    (hcard : Cardinal.mk I < Cardinal.mk k) :
    (∀ m : MaximalSpectrum S,
        letI : Algebra k m.asIdeal.ResidueField :=
          residueFieldAlgebraOfBaseAlgebra (k := k) m.asIdeal
        Algebra.IsAlgebraic k m.asIdeal.ResidueField) ∧
      IsJacobsonRing S := by
  sorry

theorem baseChange_uncountable_nullstellensatz
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Field K] [Algebra k K]
    (hcard : Cardinal.mk S < Cardinal.mk K) :
    (∀ m : MaximalSpectrum (K ⊗[k] S),
        letI : Algebra K m.asIdeal.ResidueField :=
          residueFieldAlgebraOfBaseAlgebra (k := K) m.asIdeal
        Algebra.IsAlgebraic K m.asIdeal.ResidueField) ∧
      IsJacobsonRing (K ⊗[k] S) := by
  sorry

/-! ## The countable-field counterexample -/

abbrev CountableTrickIndex (k : Type u) [Field k] :=
  {f : Polynomial k // f ≠ 0}

abbrev CountableTrickRing (k : Type u) [Field k] :=
  MvPolynomial (CountableTrickIndex k) (Polynomial k)

def countableTrickRelation {k : Type u} [Field k]
    (i : CountableTrickIndex k) : CountableTrickRing k :=
  MvPolynomial.C i.1 * MvPolynomial.X i - 1

def countableTrickIdeal {k : Type u} [Field k] : Ideal (CountableTrickRing k) :=
  Ideal.span (Set.range countableTrickRelation)

theorem countableTrickIdeal_isProper {k : Type u} [Field k] :
    countableTrickIdeal (k := k) ≠ ⊤ := by
  sorry

theorem countableTrick_exists_maximalIdeal {k : Type u} [Field k] :
    ∃ m : MaximalSpectrum (CountableTrickRing k),
      countableTrickIdeal (k := k) ≤ m.asIdeal := by
  sorry

theorem countableTrick_quotient_is_rational_function_field
    {k : Type u} [Field k]
    (m : MaximalSpectrum (CountableTrickRing k))
    (hm : countableTrickIdeal (k := k) ≤ m.asIdeal) :
    Nonempty ((CountableTrickRing k ⧸ m.asIdeal) ≃+* FractionRing (Polynomial k)) ∧
      ¬ Algebra.IsAlgebraic k (CountableTrickRing k ⧸ m.asIdeal) := by
  sorry

/-! ## Localizing, quotienting, and finite-type permanence -/

noncomputable def maximalIdealLocalizationOrderIso
    {R : Type u} [CommRing R] [IsJacobsonRing R] (f : R) :
    {p : Ideal (Localization.Away f) // p.IsMaximal} ≃o
      {p : Ideal R // p.IsMaximal ∧ f ∉ p} :=
  IsLocalization.orderIsoOfMaximal (R := R) (S := Localization.Away f) f

theorem localizationAway_isJacobson_and_maximal_correspondence
    {R : Type u} [CommRing R] [IsJacobsonRing R] (f : R) :
    IsJacobsonRing (Localization.Away f) ∧
      Nonempty
        ({p : Ideal (Localization.Away f) // p.IsMaximal} ≃o
          {p : Ideal R // p.IsMaximal ∧ f ∉ p}) := by
  sorry

def integerTwoIdeal : Ideal ℤ :=
  Ideal.span ({(2 : ℤ)} : Set ℤ)

instance integerTwoIdeal_isMaximal : integerTwoIdeal.IsMaximal := by
  simpa [integerTwoIdeal] using
    (@Int.ideal_span_isMaximal_of_prime 2 ⟨Nat.prime_two⟩)

instance integerTwoIdeal_isPrime : integerTwoIdeal.IsPrime :=
  integerTwoIdeal_isMaximal.isPrime

abbrev ZLocalizedAtTwo :=
  Localization (integerTwoIdeal.primeCompl)

abbrev ZLocalizedAtTwoAtTwo :=
  Localization.Away (algebraMap ℤ ZLocalizedAtTwo (2 : ℤ))

theorem zLocalizedAtTwo_is_rational
    : Nonempty (ZLocalizedAtTwoAtTwo ≃+* ℚ) := by
  sorry

theorem zLocalizedAtTwo_closedPoint_maps_to_generic_point
    : ∃ e : ZLocalizedAtTwoAtTwo ≃+* ℚ,
        PrimeSpectrum.comap
            (e.toRingHom.comp (algebraMap ZLocalizedAtTwo ZLocalizedAtTwoAtTwo))
            (⟨⊥, inferInstance⟩ : PrimeSpectrum ℚ) =
          (⟨⊥, inferInstance⟩ : PrimeSpectrum ZLocalizedAtTwo) := by
  sorry

abbrev RationalLocalizationOfIntegers :=
  Localization (nonZeroDivisors ℤ)

theorem rationalLocalizationOfIntegers_is_rational
    : Nonempty (RationalLocalizationOfIntegers ≃+* ℚ) := by
  sorry

theorem rationalLocalization_closedPoint_maps_to_generic_point
    : ∃ e : RationalLocalizationOfIntegers ≃+* ℚ,
        PrimeSpectrum.comap
            (e.toRingHom.comp (algebraMap ℤ RationalLocalizationOfIntegers))
            (⟨⊥, inferInstance⟩ : PrimeSpectrum ℚ) =
          (⟨⊥, inferInstance⟩ : PrimeSpectrum ℤ) := by
  sorry

theorem quotient_of_isJacobson_isJacobson_with_maximal_correspondence
    {R : Type u} [CommRing R] [IsJacobsonRing R] (I : Ideal R) :
    IsJacobsonRing (R ⧸ I) ∧
      ∃ e :
          {M : Ideal (R ⧸ I) // M.IsMaximal} ≃
            {N : Ideal R // N.IsMaximal ∧ I ≤ N},
        (∀ M, Ideal.map (Ideal.Quotient.mk I) (e M).1 = M.1) ∧
          (∀ N, Ideal.comap (Ideal.Quotient.mk I) (e.symm N).1 = N.1) := by
  sorry

theorem jacobson_subring_of_finiteType_field
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    [IsJacobsonRing R] [Algebra.FiniteType R K]
    (hRK : Function.Injective (algebraMap R K)) :
    IsField R ∧ Module.Finite R K := by
  sorry

theorem finiteType_map_preserves_jacobson_closedPoints_and_residue_finiteness
    {R S : Type u} [CommRing R] [CommRing S] [IsJacobsonRing R]
    (φ : R →+* S) (hφ : RingHom.FiniteType φ) :
    IsJacobsonRing S ∧
      (∀ q : MaximalSpectrum S, (q.asIdeal.comap φ).IsMaximal) ∧
      (∀ q : MaximalSpectrum S,
        let p := q.asIdeal.comap φ
        letI : p.IsPrime := Ideal.comap_isPrime φ q.asIdeal
        letI : Algebra p.ResidueField q.asIdeal.ResidueField :=
          residueFieldAlgebraOfMap p q.asIdeal φ rfl
        Module.Finite p.ResidueField q.asIdeal.ResidueField) := by
  sorry

theorem finiteType_algebra_over_integers_isJacobson
    {A : Type u} [CommRing A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] :
    IsJacobsonRing A := by
  sorry

/-! ## Constructible images and closed points -/

abbrev ConstructibleSet (X : Type u) [TopologicalSpace X] :=
  {E : Set X // IsConstructible E}

def closedPointPart {X : Type u} [TopologicalSpace X] (E : Set X) : Set X :=
  E ∩ closedPoints X

def closedPointsOfSubset {X : Type u} [TopologicalSpace X] (E : Set X) : Set X :=
  Set.range (fun x : closedPoints (↥E) => (x.1 : X))

theorem finiteType_constructible_image_isConstructible
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (φ : R →+* S) (hφ : RingHom.FiniteType φ)
    {E : Set (PrimeSpectrum S)} (hE : IsConstructible E) :
    IsConstructible (PrimeSpectrum.comap φ '' E) := by
  sorry

theorem jacobson_constructible_image_closedPoint_formula
    {R S : Type u} [CommRing R] [CommRing S]
    [IsJacobsonRing R] [IsJacobsonRing S]
    (φ : R →+* S) (hφ : RingHom.FiniteType φ)
    {E : Set (PrimeSpectrum S)} (hE : IsConstructible E) :
    closedPointsOfSubset (PrimeSpectrum.comap φ '' E) =
        PrimeSpectrum.comap φ '' (E ∩ closedPoints (PrimeSpectrum S)) ∧
      PrimeSpectrum.comap φ '' (E ∩ closedPoints (PrimeSpectrum S)) =
        closedPointPart (PrimeSpectrum.comap φ '' E) ∧
      ∀ ξ : PrimeSpectrum R,
        ξ ∈ PrimeSpectrum.comap φ '' E ↔
          closure ({ξ} : Set (PrimeSpectrum R)) =
            closure
              (closure ({ξ} : Set (PrimeSpectrum R)) ∩
                (PrimeSpectrum.comap φ ''
                  (E ∩ closedPoints (PrimeSpectrum S)))) := by
  sorry

theorem noetherian_jacobson_constructible_correspondence_diagram
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsJacobsonRing R]
    (φ : R →+* S) (hφ : RingHom.FiniteType φ) :
    ∃ (imageYX : ConstructibleSet (PrimeSpectrum S) →
          ConstructibleSet (PrimeSpectrum R))
      (imageY₀X₀ : ConstructibleSet (closedPoints (PrimeSpectrum S)) →
          ConstructibleSet (closedPoints (PrimeSpectrum R)))
      (traceX : ConstructibleSet (PrimeSpectrum R) ≃
          ConstructibleSet (closedPoints (PrimeSpectrum R)))
      (traceY : ConstructibleSet (PrimeSpectrum S) ≃
          ConstructibleSet (closedPoints (PrimeSpectrum S))),
      (∀ E, (imageYX E : Set (PrimeSpectrum R)) =
        PrimeSpectrum.comap φ '' (E : Set (PrimeSpectrum S))) ∧
      (∀ E, Set.image (Subtype.val : closedPoints (PrimeSpectrum R) →
          PrimeSpectrum R) (imageY₀X₀ E : Set (closedPoints (PrimeSpectrum R))) =
        PrimeSpectrum.comap φ ''
          Set.image (Subtype.val : closedPoints (PrimeSpectrum S) →
            PrimeSpectrum S) (E : Set (closedPoints (PrimeSpectrum S)))) ∧
      (∀ E, Set.image (Subtype.val : closedPoints (PrimeSpectrum R) →
          PrimeSpectrum R) (traceX E : Set (closedPoints (PrimeSpectrum R))) =
        closedPointPart (E : Set (PrimeSpectrum R))) ∧
      (∀ E, Set.image (Subtype.val : closedPoints (PrimeSpectrum S) →
          PrimeSpectrum S) (traceY E : Set (closedPoints (PrimeSpectrum S))) =
        closedPointPart (E : Set (PrimeSpectrum S))) ∧
      (∀ E, traceX (imageYX E) = imageY₀X₀ (traceY E)) := by
  sorry

/-! ## The two-axis and product-zero matrix examples -/

abbrev ProductZeroPolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

def productZeroRelationIdeal (k : Type u) [Field k] :
    Ideal (ProductZeroPolynomialRing k) :=
  Ideal.span
    {MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1}

abbrev ProductZeroRing (k : Type u) [Field k] :=
  ProductZeroPolynomialRing k ⧸ productZeroRelationIdeal k

def productZeroXAxisIdeal (k : Type u) [Field k] :
    Ideal (ProductZeroPolynomialRing k) :=
  Ideal.span {MvPolynomial.X (R := k) 0}

def productZeroYAxisIdeal (k : Type u) [Field k] :
    Ideal (ProductZeroPolynomialRing k) :=
  Ideal.span {MvPolynomial.X (R := k) 1}

theorem productZero_minimalPrimes_are_the_two_axes
    (k : Type u) [Field k] :
    (productZeroRelationIdeal k).minimalPrimes =
      {productZeroXAxisIdeal k, productZeroYAxisIdeal k} := by
  sorry

theorem productZero_spectrum_has_two_irreducible_components
    (k : Type u) [Field k] :
    Nonempty
      (Fin 2 ≃ irreducibleComponents (PrimeSpectrum (ProductZeroRing k))) := by
  sorry

abbrev ProductZeroSolution (k : Type u) [Field k] :=
  {p : k × k // p.1 * p.2 = 0}

def productZeroXAxis (k : Type u) [Field k] : Set (k × k) :=
  {p | p.1 = 0}

def productZeroYAxis (k : Type u) [Field k] : Set (k × k) :=
  {p | p.2 = 0}

theorem productZero_solution_set_is_union_of_axes
    (k : Type u) [Field k] :
    {p : k × k | p.1 * p.2 = 0} =
      productZeroXAxis k ∪ productZeroYAxis k := by
  ext p
  simp [productZeroXAxis, productZeroYAxis, mul_eq_zero]

theorem productZero_closedPoints_are_algebraic_solutions
    (k : Type u) [Field k] (hk : IsAlgClosed k) :
    Nonempty
      (closedPoints (PrimeSpectrum (ProductZeroRing k)) ≃ ProductZeroSolution k) := by
  sorry

/-! The product-zero matrix example. -/

abbrev Matrix2 (k : Type u) := Matrix (Fin 2) (Fin 2) k
abbrev MatrixPairPolynomial (k : Type u) [CommSemiring k] :=
  MvPolynomial (Fin 8) k

def matrixPairVariable {k : Type u} [Field k] (i : Fin 8) :
    MatrixPairPolynomial k :=
  MvPolynomial.X (R := k) i

def matrixPairX11 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 0
def matrixPairX12 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 1
def matrixPairX21 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 2
def matrixPairX22 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 3
def matrixPairY11 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 4
def matrixPairY12 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 5
def matrixPairY21 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 6
def matrixPairY22 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 7

def matrixPairProductEquations {k : Type u} [Field k] :
    Set (MatrixPairPolynomial k) :=
  { matrixPairX11 (k := k) * matrixPairY11 (k := k) + matrixPairX12 (k := k) * matrixPairY21 (k := k),
    matrixPairX11 (k := k) * matrixPairY12 (k := k) + matrixPairX12 (k := k) * matrixPairY22 (k := k),
    matrixPairX21 (k := k) * matrixPairY11 (k := k) + matrixPairX22 (k := k) * matrixPairY21 (k := k),
    matrixPairX21 (k := k) * matrixPairY12 (k := k) + matrixPairX22 (k := k) * matrixPairY22 (k := k) }

def matrixProductIdeal {k : Type u} [Field k] : Ideal (MatrixPairPolynomial k) :=
  Ideal.span (matrixPairProductEquations (k := k))

abbrev MatrixPairRing (k : Type u) [Field k] :=
  MatrixPairPolynomial k ⧸ matrixProductIdeal (k := k)

abbrev MatrixPairSolution (k : Type u) [Field k] :=
  {P : Matrix2 k × Matrix2 k // P.1 * P.2 = 0}

theorem matrixPair_polynomial_closedPoints_are_matrix_pairs
    (k : Type u) [Field k] (hk : IsAlgClosed k) :
    Nonempty
      (closedPoints (PrimeSpectrum (MatrixPairPolynomial k)) ≃
        (Matrix2 k × Matrix2 k)) := by
  sorry

theorem matrixPair_closedPoints_are_product_zero_solutions
    (k : Type u) [Field k] (hk : IsAlgClosed k) :
    Nonempty
      (closedPoints (PrimeSpectrum (MatrixPairRing k)) ≃ MatrixPairSolution k) := by
  sorry

def matrixPairDetX {k : Type u} [Field k] : MatrixPairPolynomial k :=
  matrixPairX11 (k := k) * matrixPairX22 (k := k) -
    matrixPairX12 (k := k) * matrixPairX21 (k := k)

def matrixPairDetY {k : Type u} [Field k] : MatrixPairPolynomial k :=
  matrixPairY11 (k := k) * matrixPairY22 (k := k) -
    matrixPairY12 (k := k) * matrixPairY21 (k := k)

def matrixProductRankTwoComponentIdeal {k : Type u} [Field k] :
    Ideal (MatrixPairPolynomial k) :=
  Ideal.span {matrixPairY11 (k := k), matrixPairY12 (k := k), matrixPairY21 (k := k), matrixPairY22 (k := k)}

def matrixProductRankOneComponentIdeal {k : Type u} [Field k] :
    Ideal (MatrixPairPolynomial k) :=
  Ideal.span (matrixPairProductEquations (k := k) ∪ {matrixPairDetX (k := k)})

def matrixProductRankZeroComponentIdeal {k : Type u} [Field k] :
    Ideal (MatrixPairPolynomial k) :=
  Ideal.span {matrixPairX11 (k := k), matrixPairX12 (k := k), matrixPairX21 (k := k), matrixPairX22 (k := k)}

def matrixProductDeterminantalIdeal {k : Type u} [Field k] :
    Ideal (MatrixPairPolynomial k) :=
  matrixProductIdeal (k := k) ⊔
    Ideal.span {matrixPairDetX (k := k), matrixPairDetY (k := k)}

theorem matrixProduct_equations_are_matrix_product_entries
    {k : Type u} [Field k] (X Y : Matrix2 k) :
    X * Y = 0 ↔
      (X 0 0 * Y 0 0 + X 0 1 * Y 1 0 = 0) ∧
      (X 0 0 * Y 0 1 + X 0 1 * Y 1 1 = 0) ∧
      (X 1 0 * Y 0 0 + X 1 1 * Y 1 0 = 0) ∧
      (X 1 0 * Y 0 1 + X 1 1 * Y 1 1 = 0) := by
  sorry

def matrixPairAction {k : Type u} [Field k]
    (g : Matrix.GeneralLinearGroup (Fin 2) k ×
      Matrix.GeneralLinearGroup (Fin 2) k × Matrix.GeneralLinearGroup (Fin 2) k)
    (P : Matrix2 k × Matrix2 k) : Matrix2 k × Matrix2 k :=
  let g₁ := g.1
  let g₂ := g.2.1
  let g₃ := g.2.2
  ((g₁ : Matrix2 k) * P.1 * (↑(g₂⁻¹) : Matrix2 k),
    (g₂ : Matrix2 k) * P.2 * (↑(g₃⁻¹) : Matrix2 k))

theorem matrixPairAction_one (k : Type u) [Field k] (P : Matrix2 k × Matrix2 k) :
    matrixPairAction (1, 1, 1) P = P := by
  sorry

theorem matrixPairAction_mul (k : Type u) [Field k]
    (g h : Matrix.GeneralLinearGroup (Fin 2) k ×
      Matrix.GeneralLinearGroup (Fin 2) k × Matrix.GeneralLinearGroup (Fin 2) k)
    (P : Matrix2 k × Matrix2 k) :
    matrixPairAction (g * h) P = matrixPairAction g (matrixPairAction h P) := by
  sorry

instance matrixPairAction_mulAction {k : Type u} [Field k] :
    MulAction
      (Matrix.GeneralLinearGroup (Fin 2) k ×
        Matrix.GeneralLinearGroup (Fin 2) k × Matrix.GeneralLinearGroup (Fin 2) k)
      (Matrix2 k × Matrix2 k) where
  smul := matrixPairAction
  one_smul := matrixPairAction_one k
  mul_smul := matrixPairAction_mul k

theorem matrixProduct_minimalPrime_components
    (k : Type u) [Field k] :
    (matrixProductIdeal (k := k)).minimalPrimes =
      {matrixProductRankTwoComponentIdeal,
        matrixProductRankOneComponentIdeal,
        matrixProductRankZeroComponentIdeal} := by
  sorry

theorem matrixProduct_components_are_prime
    (k : Type u) [Field k] :
    (matrixProductRankTwoComponentIdeal (k := k)).IsPrime ∧
      (matrixProductRankOneComponentIdeal (k := k)).IsPrime ∧
      (matrixProductRankZeroComponentIdeal (k := k)).IsPrime := by
  sorry

theorem matrixProduct_determinantal_component
    (k : Type u) [Field k] :
    matrixProductDeterminantalIdeal (k := k) =
      matrixProductRankOneComponentIdeal (k := k) := by
  sorry

theorem matrixProduct_zero_rank_cases
    {k : Type u} [Field k] (X Y : Matrix2 k) (hXY : X * Y = 0) :
    (X.rank = 2 ∧ Y = 0) ∨ (X.rank = 1 ∧ X.det = 0 ∧ Y.det = 0) ∨ X = 0 := by
  sorry

theorem matrixProduct_rank_normal_forms
    {k : Type u} [Field k] (X : Matrix2 k) :
    (X.rank = 2 →
      ∃ g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) k,
        (g₁ : Matrix2 k) * X * (↑(g₂⁻¹) : Matrix2 k) = 1) ∧
    (X.rank = 1 →
      ∃ g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) k,
        (g₁ : Matrix2 k) * X * (↑(g₂⁻¹) : Matrix2 k) =
          Matrix.diagonal (fun i : Fin 2 => if i = 0 then 1 else 0)) := by
  sorry

abbrev MatrixTriplePolynomial (k : Type u) [CommSemiring k] :=
  MvPolynomial (Fin 12) k

def matrixTripleDetX {k : Type u} [Field k] : MatrixTriplePolynomial k :=
  MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 3 -
    MvPolynomial.X (R := k) 1 * MvPolynomial.X (R := k) 2

def matrixTripleDetY {k : Type u} [Field k] : MatrixTriplePolynomial k :=
  MvPolynomial.X (R := k) 4 * MvPolynomial.X (R := k) 7 -
    MvPolynomial.X (R := k) 5 * MvPolynomial.X (R := k) 6

def matrixTripleDetZ {k : Type u} [Field k] : MatrixTriplePolynomial k :=
  MvPolynomial.X (R := k) 8 * MvPolynomial.X (R := k) 11 -
    MvPolynomial.X (R := k) 9 * MvPolynomial.X (R := k) 10

abbrev GeneralLinearTripleCoordinateRing (k : Type u) [Field k] :=
  Localization (Submonoid.powers
    (matrixTripleDetX (k := k) * matrixTripleDetY (k := k) * matrixTripleDetZ (k := k)))

theorem generalLinearTripleCoordinateRing_isDomain
    (k : Type u) [Field k] :
    IsDomain (GeneralLinearTripleCoordinateRing k) := by
  sorry

theorem generalLinearTriple_spectrum_isIrreducible
    (k : Type u) [Field k] :
    IsIrreducible (Set.univ : Set (PrimeSpectrum (GeneralLinearTripleCoordinateRing k))) := by
  sorry

/-! ## Idempotent matrices -/

abbrev IdempotentMatrixPolynomial (k : Type u) [CommSemiring k] (n : ℕ) :=
  MvPolynomial (Fin n × Fin n) k

def genericIdempotentMatrix {k : Type u} [Field k] (n : ℕ) :
    Matrix (Fin n) (Fin n) (IdempotentMatrixPolynomial k n) :=
  fun i j => MvPolynomial.X (R := k) (i, j)

def idempotentMatrixEquations {k : Type u} [Field k] (n : ℕ) :
    Set (IdempotentMatrixPolynomial k n) :=
  Set.range (fun ij : Fin n × Fin n =>
    (∑ l : Fin n,
      genericIdempotentMatrix (k := k) n ij.1 l * genericIdempotentMatrix (k := k) n l ij.2) -
      genericIdempotentMatrix (k := k) n ij.1 ij.2)

def idempotentMatrixIdeal {k : Type u} [Field k] (n : ℕ) :
    Ideal (IdempotentMatrixPolynomial k n) :=
  Ideal.span (idempotentMatrixEquations (k := k) n)

abbrev IdempotentMatrixRing (k : Type u) [Field k] (n : ℕ) :=
  IdempotentMatrixPolynomial k n ⧸ idempotentMatrixIdeal (k := k) n

def diagonalIdempotent {k : Type u} [Field k] (n r : ℕ) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.diagonal (fun i : Fin n => if i.1 < r then 1 else 0)

def matrixConjugation {k : Type u} [Field k] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (T : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k :=
  (g : Matrix (Fin n) (Fin n) k) * T * (↑(g⁻¹) : Matrix (Fin n) (Fin n) k)

def matrixTrace {k : Type u} [Field k] {n : ℕ}
    (T : Matrix (Fin n) (Fin n) k) : k :=
  ∑ i, T i i

def idempotentMatrixOrbit {k : Type u} [Field k] (n : ℕ)
    (T : Matrix (Fin n) (Fin n) k) : Set (Matrix (Fin n) (Fin n) k) :=
  Set.range (fun g : Matrix.GeneralLinearGroup (Fin n) k => matrixConjugation n g T)

def thirdExteriorPowerTrace {k : Type u} [Field k]
    (T : Matrix (Fin 3) (Fin 3) k) : k :=
  T.det

theorem idempotent_matrix_conjugate_to_diagonal
    {k : Type u} [Field k] (n : ℕ) (T : Matrix (Fin n) (Fin n) k)
    (hT : T * T = T) :
    ∃ r : Fin (n + 1), ∃ g : Matrix.GeneralLinearGroup (Fin n) k,
      T.rank = r.1 ∧
      matrixConjugation n g T =
        Matrix.diagonal (fun i : Fin n => if i.1 < r.1 then 1 else 0) := by
  sorry

theorem idempotent_matrix_rank_orbits_are_components
    (k : Type u) [Field k] (n : ℕ) (hk : IsAlgClosed k) :
    Nonempty (Fin (n + 1) ≃
      irreducibleComponents (PrimeSpectrum (IdempotentMatrixRing k n))) := by
  sorry

theorem idempotent_matrix_different_rank_orbits_disjoint
    {k : Type u} [Field k] (n r s : ℕ)
    (hr : r ≤ n) (hs : s ≤ n) (hrs : r ≠ s) :
    Disjoint
      (idempotentMatrixOrbit (k := k) n
        (Matrix.diagonal (fun i : Fin n => if i.1 < r then 1 else 0)))
      (idempotentMatrixOrbit (k := k) n
        (Matrix.diagonal (fun i : Fin n => if i.1 < s then 1 else 0))) := by
  sorry

theorem matrixTrace_diagonalIdempotent
    {k : Type u} [Field k] (n r : ℕ) :
    matrixTrace (k := k)
        (Matrix.diagonal (fun i : Fin n => if i.1 < r then (1 : k) else 0)) = r := by
  sorry

theorem matrixTrace_separates_idempotent_ranks
    {k : Type u} [Field k] [CharZero k] (n r s : ℕ)
    (hr : r ≤ n) (hs : s ≤ n) (hrs : r ≠ s) :
    matrixTrace (k := k)
        (Matrix.diagonal (fun i : Fin n => if i.1 < r then (1 : k) else 0)) ≠
      matrixTrace (k := k)
        (Matrix.diagonal (fun i : Fin n => if i.1 < s then (1 : k) else 0)) := by
  sorry

theorem characteristic_three_trace_does_not_separate_zero_and_full_rank
    {k : Type u} [Field k] [CharP k 3] :
    matrixTrace (k := k) (Matrix.diagonal (fun i : Fin 3 => (1 : k))) =
      matrixTrace (k := k) (Matrix.diagonal (fun i : Fin 3 => (0 : k))) := by
  sorry

theorem characteristic_three_third_exterior_power_trace_separates_full_rank
    {k : Type u} [Field k] [CharP k 3] :
    thirdExteriorPowerTrace (k := k)
          (Matrix.diagonal (fun i : Fin 3 => (1 : k))) = 1 ∧
      thirdExteriorPowerTrace (k := k)
          (Matrix.diagonal (fun i : Fin 3 => (0 : k))) = 0 := by
  sorry

end

end Formalization.Books.Algebra.Unit35
