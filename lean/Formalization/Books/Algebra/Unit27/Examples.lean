import Formalization.Books.Algebra.Unit17.Spectrum
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Polynomial
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Commutative Algebra, Chapter 27: Examples of spectra of rings

This file formalizes the four examples in the source section.  The concrete
rings and maps use Mathlib's canonical polynomial, quotient, subalgebra,
localization, ideal, and prime-spectrum constructions.  The long
classification and topology arguments are theorem interfaces; their proofs
belong to the proving stage.
-/

namespace Formalization.Books.Algebra.Unit27

open Set
open Topology

open scoped Polynomial

noncomputable section

/-! ## `Spec(ℤ[x]/(x^2 - 4))` -/

abbrev IntPolynomial := Polynomial ℤ

/-- The relation defining the ring `ℤ[x]/(x^2 - 4)`. -/
def intQuadraticRelation : Ideal IntPolynomial :=
  Ideal.span {Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)}

/-- The ring in the first example. -/
abbrev IntQuadraticRing := IntPolynomial ⧸ intQuadraticRelation

/-- The quotient map from `ℤ[x]` to the quadratic ring. -/
def intQuadraticQuotientMap : IntPolynomial →+* IntQuadraticRing :=
  Ideal.Quotient.mk intQuadraticRelation

/-- The structure map `ℤ → ℤ[x]/(x^2 - 4)`. -/
def intQuadraticStructureMap : ℤ →+* IntQuadraticRing :=
  intQuadraticQuotientMap.comp Polynomial.C

/-- The ideal `(x - r)` in the quadratic quotient. -/
def intQuadraticRootIdeal (r : ℤ) : Ideal IntQuadraticRing :=
  Ideal.span {intQuadraticQuotientMap (Polynomial.X - Polynomial.C r)}

/-- The ideal `(q, x - r)` in the quadratic quotient. -/
def intQuadraticPrimeIdeal (q : ℕ) (r : ℤ) : Ideal IntQuadraticRing :=
  Ideal.span
    {intQuadraticQuotientMap (Polynomial.C (q : ℤ)),
      intQuadraticQuotientMap (Polynomial.X - Polynomial.C r)}

theorem int_quadratic_factorization :
    Polynomial.X ^ 2 - Polynomial.C (4 : ℤ) =
      (Polynomial.X - Polynomial.C 2) * (Polynomial.X + Polynomial.C 2) := by
  sorry

theorem int_quadratic_prime_contraction_isPrime (p : PrimeSpectrum IntQuadraticRing) :
    (p.asIdeal.comap intQuadraticStructureMap).IsPrime := by
  sorry

theorem int_quadratic_reduction_mod_prime (q : ℕ) (hq : Nat.Prime q) :
    Nonempty
      ((IntQuadraticRing ⧸
            Ideal.span {intQuadraticQuotientMap (Polynomial.C (q : ℤ))}) ≃+*
          (Polynomial (ℤ ⧸ Ideal.span {(q : ℤ)}) ⧸
            Ideal.span {Polynomial.X ^ 2 - Polynomial.C (4 : ℤ ⧸ Ideal.span {(q : ℤ)})})) := by
  sorry

theorem int_quadratic_reduction_mod_two :
    Nonempty
      ((IntQuadraticRing ⧸
            Ideal.span {intQuadraticQuotientMap (Polynomial.C (2 : ℤ))}) ≃+*
          (Polynomial (ℤ ⧸ Ideal.span {(2 : ℤ)}) ⧸
            Ideal.span
              ({Polynomial.X ^ 2} : Set (Polynomial (ℤ ⧸ Ideal.span {(2 : ℤ)}))))) := by
  sorry

theorem int_quadratic_prime_spectra_reduction_correspondence (q : ℕ) (hq : Nat.Prime q) :
    Nonempty
      (PrimeSpectrum
          (IntQuadraticRing ⧸
            Ideal.span {intQuadraticQuotientMap (Polynomial.C (q : ℤ))}) ≃
        PrimeSpectrum
          (Polynomial (ℤ ⧸ Ideal.span {(q : ℤ)}) ⧸
            Ideal.span {Polynomial.X ^ 2 -
              Polynomial.C (4 : ℤ ⧸ Ideal.span {(q : ℤ)})})) := by
  sorry

theorem int_polynomial_root_quotient_equiv (r : ℤ) :
    Nonempty ((IntPolynomial ⧸
      Ideal.span {Polynomial.X - Polynomial.C r}) ≃+* ℤ) := by
  sorry

theorem int_quadratic_root_ideals_isPrime :
    (intQuadraticRootIdeal 2).IsPrime ∧
      (intQuadraticRootIdeal (-2)).IsPrime := by
  sorry

theorem int_quadratic_prime_ideal_at_two_isPrime :
    (intQuadraticPrimeIdeal 2 0).IsPrime := by
  sorry

theorem int_quadratic_prime_ideals_isPrime (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q) :
    (intQuadraticPrimeIdeal q 2).IsPrime ∧
      (intQuadraticPrimeIdeal q (-2)).IsPrime := by
  sorry

/-- The complete list of prime ideals in the first example.

The two roots over odd residue fields are separated by the explicit
assumption `2 < q`; the ramified prime over `2` is listed separately. -/
theorem prime_spectrum_int_quadratic_cases (p : PrimeSpectrum IntQuadraticRing) :
    p.asIdeal = intQuadraticRootIdeal 2 ∨
      p.asIdeal = intQuadraticRootIdeal (-2) ∨
      p.asIdeal = intQuadraticPrimeIdeal 2 0 ∨
      ∃ q : ℕ, Nat.Prime q ∧ 2 < q ∧
        (p.asIdeal = intQuadraticPrimeIdeal q 2 ∨
          p.asIdeal = intQuadraticPrimeIdeal q (-2)) := by
  sorry

/-! ## `Spec(ℤ[x])` -/

abbrev IntPolynomialMod (q : ℕ) := ℤ ⧸ Ideal.span {(q : ℤ)}

/-- Reduction of an integer polynomial modulo the principal ideal `(q)`. -/
def intPolynomialReduction (q : ℕ) (f : IntPolynomial) : Polynomial (IntPolynomialMod q) :=
  Polynomial.map (Ideal.Quotient.mk (Ideal.span {(q : ℤ)})) f

/-- The prime ideal `(q)` in `ℤ[x]`. -/
def intPolynomialPrimeIdeal (q : ℕ) : Ideal IntPolynomial :=
  Ideal.span {Polynomial.C (q : ℤ)}

/-- The ideal `(q, f)` in `ℤ[x]`. -/
def intPolynomialPrimeAt (q : ℕ) (f : IntPolynomial) : Ideal IntPolynomial :=
  Ideal.span {Polynomial.C (q : ℤ), f}

/-- The condition on a polynomial lift used in the residue-characteristic case. -/
def IsIntegerPolynomialLift (q : ℕ) (f : IntPolynomial) : Prop :=
  Irreducible f ∧ Irreducible (intPolynomialReduction q f)

theorem int_polynomial_isUFD : UniqueFactorizationMonoid IntPolynomial := by
  infer_instance

theorem int_polynomial_isNoetherian : IsNoetherianRing IntPolynomial := by
  infer_instance

theorem int_polynomial_irreducible_maps_to_ratios
    (f : IntPolynomial) (hfdeg : 0 < f.natDegree) (hf : Irreducible f) :
    Irreducible (Polynomial.map (Int.castRingHom ℚ) f) := by
  sorry

theorem int_polynomial_prime_contraction_isPrime (P : Ideal IntPolynomial)
    (hP : P.IsPrime) :
    (P.comap Polynomial.C).IsPrime := by
  sorry

theorem int_polynomial_irreducible_span_isPrime (f : IntPolynomial)
    (hf : Irreducible f) :
    (Ideal.span {f}).IsPrime := by
  sorry

theorem int_polynomial_prime_ideal_candidates_isPrime (q : ℕ) (hq : Nat.Prime q) :
    (intPolynomialPrimeIdeal q).IsPrime ∧
      ∀ f : IntPolynomial, IsIntegerPolynomialLift q f →
        (intPolynomialPrimeAt q f).IsPrime := by
  sorry

/-- The source classification, corrected to include the zero prime in each
PID fiber and the zero prime over the generic point. -/
theorem prime_ideal_int_polynomial_cases (P : Ideal IntPolynomial) (hP : P.IsPrime) :
    ((P.comap Polynomial.C = ⊥ ∧
        (P = ⊥ ∨ ∃ f : IntPolynomial, 0 < f.natDegree ∧ Irreducible f ∧
          P = Ideal.span {f})) ∨
      (∃ q : ℕ, Nat.Prime q ∧ P.comap Polynomial.C = Ideal.span {(q : ℤ)} ∧
        (P = intPolynomialPrimeIdeal q ∨
          ∃ f : IntPolynomial, 0 < f.natDegree ∧ IsIntegerPolynomialLift q f ∧
            P = intPolynomialPrimeAt q f))) := by
  sorry

theorem int_polynomial_prime_ideal_is_zero_or_principal (P : Ideal IntPolynomial)
    (hP : P.IsPrime) (hcontraction : P.comap Polynomial.C = ⊥) :
    P = ⊥ ∨ ∃ f : IntPolynomial, 0 < f.natDegree ∧ Irreducible f ∧
      P = Ideal.span {f} := by
  sorry

theorem int_polynomial_prime_ideal_over_prime_is_zero_or_principal
    (P : Ideal IntPolynomial) (hP : P.IsPrime) (q : ℕ) (hq : Nat.Prime q)
    (hcontraction : P.comap Polynomial.C = Ideal.span {(q : ℤ)}) :
    P = intPolynomialPrimeIdeal q ∨
      ∃ f : IntPolynomial, 0 < f.natDegree ∧ IsIntegerPolynomialLift q f ∧
        P = intPolynomialPrimeAt q f := by
  sorry

/-! ## `Spec(k[x,y])` -/

/-- A concrete nested-polynomial model of the bivariate polynomial ring `k[x,y]`. -/
abbrev BivariatePolynomial (k : Type*) [Field k] := Polynomial (Polynomial k)

def bivariateX {k : Type*} [Field k] : BivariatePolynomial k :=
  Polynomial.C Polynomial.X

def bivariateY {k : Type*} [Field k] : BivariatePolynomial k :=
  Polynomial.X

def bivariateUnivariateIdeal {k : Type*} [Field k] (p : Polynomial k) :
    Ideal (BivariatePolynomial k) :=
  Ideal.span {Polynomial.C p}

abbrev BivariateQuotient {k : Type*} [Field k] (p : Polynomial k) :=
  BivariatePolynomial k ⧸ bivariateUnivariateIdeal p

def bivariateTwoGeneratorIdeal {k : Type*} [Field k]
    (f g : BivariatePolynomial k) : Ideal (BivariatePolynomial k) :=
  Ideal.span {f, g}

def BivariateQuotientIrreducible {k : Type*} [Field k]
    (p : Polynomial k) (f : BivariatePolynomial k) : Prop :=
  Irreducible (Ideal.Quotient.mk (bivariateUnivariateIdeal p) f)

theorem bivariate_zero_isPrime (k : Type*) [Field k] :
    (⊥ : Ideal (BivariatePolynomial k)).IsPrime := by
  infer_instance

theorem bivariate_isNoetherian (k : Type*) [Field k] :
    IsNoetherianRing (BivariatePolynomial k) := by
  infer_instance

theorem bivariate_isUFD (k : Type*) [Field k] :
    UniqueFactorizationMonoid (BivariatePolynomial k) := by
  infer_instance

theorem bivariate_irreducible_span_isPrime (k : Type*) [Field k]
    (f : BivariatePolynomial k) (hf : Irreducible f) :
    (Ideal.span {f}).IsPrime := by
  sorry

theorem bivariate_univariate_span_isPrime (k : Type*) [Field k]
    (p : Polynomial k) (hp : Irreducible p) :
    (bivariateUnivariateIdeal p).IsPrime := by
  sorry

theorem bivariate_prime_has_finite_irreducible_generators
    (k : Type*) [Field k] (P : Ideal (BivariatePolynomial k)) (hP : P.IsPrime)
    (hnprincipal : ∀ f, P ≠ Ideal.span ({f} : Set (BivariatePolynomial k))) :
    ∃ n : ℕ, ∃ f : Fin n → BivariatePolynomial k,
      (∀ i, Irreducible (f i)) ∧ P = Ideal.span (Set.range f) := by
  sorry

theorem bivariate_pair_intersects_univariate
    (k : Type*) [Field k] (f g : BivariatePolynomial k)
    (hf : Irreducible f) (hg : Irreducible g) (hnassoc : ¬Associated f g) :
    ∃ p : Polynomial k, p ≠ 0 ∧ Polynomial.C p ∈ bivariateTwoGeneratorIdeal f g := by
  sorry

theorem bivariate_prime_contains_univariate_irreducible
    (k : Type*) [Field k] (P : Ideal (BivariatePolynomial k)) (hP : P.IsPrime)
    (hnprincipal : ∀ f, P ≠ Ideal.span ({f} : Set (BivariatePolynomial k))) :
    ∃ p : Polynomial k, Irreducible p ∧ Polynomial.C p ∈ P := by
  sorry

theorem bivariate_univariate_quotient_isPID
    (k : Type*) [Field k] (p : Polynomial k) (hp : Irreducible p) :
    IsDomain (BivariateQuotient p) ∧ IsPrincipalIdealRing (BivariateQuotient p) := by
  sorry

/-- Prime ideals of the bivariate ring, with the zero ideal included. -/
theorem prime_ideal_bivariate_cases (k : Type*) [Field k]
    (P : Ideal (BivariatePolynomial k)) (hP : P.IsPrime) :
    P = ⊥ ∨
      (∃ f : BivariatePolynomial k, Irreducible f ∧ P = Ideal.span {f}) ∨
      (∃ p : Polynomial k, Irreducible p ∧
        (P = bivariateUnivariateIdeal p ∨
          ∃ f : BivariatePolynomial k, BivariateQuotientIrreducible p f ∧
            P = bivariateTwoGeneratorIdeal (Polynomial.C p) f)) := by
  sorry

/-! ## The affine open which is not a standard localization -/

/-- The subring `R = {f ∈ ℚ[z] | f(0) = f(1)}` as an equalizer subalgebra. -/
def affineBaseSubalgebra : Subalgebra ℚ (Polynomial ℚ) :=
  AlgHom.equalizer (Polynomial.aeval (0 : ℚ)) (Polynomial.aeval (1 : ℚ))

def affineBaseElement (f : Polynomial ℚ)
    (hf : Polynomial.aeval (0 : ℚ) f = Polynomial.aeval (1 : ℚ) f) :
    affineBaseSubalgebra :=
  ⟨f, hf⟩

def affineA : affineBaseSubalgebra :=
  affineBaseElement (Polynomial.X ^ 2 - Polynomial.X) (by simp)

def affineB : affineBaseSubalgebra :=
  affineBaseElement (Polynomial.X ^ 3 - Polynomial.X ^ 2) (by simp)

def affineBZero : affineBaseSubalgebra :=
  affineBaseElement (Polynomial.X ^ 3 - Polynomial.X) (by simp)

theorem affine_base_isDomain : IsDomain affineBaseSubalgebra := by
  infer_instance

theorem affine_base_is_generated_by_A_and_B :
    affineBaseSubalgebra =
      Algebra.adjoin ℚ ({(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)} :
        Set (Polynomial ℚ)) := by
  sorry

theorem affine_base_isFiniteType : Algebra.FiniteType ℚ affineBaseSubalgebra := by
  sorry

theorem affine_base_z_mul_A_eq_B :
    Polynomial.X * (affineA : Polynomial ℚ) = (affineB : Polynomial ℚ) := by
  sorry

def affinePolynomialF1 (a : ℚ) : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C (1 - a)) * (Polynomial.X - Polynomial.C a)

def affinePolynomialF2AtA (a : ℚ) : Polynomial ℚ :=
  (Polynomial.X ^ 2 - Polynomial.C (1 - a)) * (Polynomial.X - Polynomial.C a)

def affinePolynomialF2AtOneMinusA (a : ℚ) : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C (1 - a)) * (Polynomial.X ^ 2 - Polynomial.C a)

def affineQuadratic (a : ℚ) : Polynomial ℚ :=
  Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (2 * a - 2)

def affinePolynomialG (a : ℚ) : Polynomial ℚ :=
  affineQuadratic a * (Polynomial.X - Polynomial.C a)

theorem affinePolynomialF1_mem_equalizer (a : ℚ) :
    Polynomial.aeval (0 : ℚ) (affinePolynomialF1 a) =
      Polynomial.aeval (1 : ℚ) (affinePolynomialF1 a) := by
  sorry

theorem affinePolynomialF2AtA_mem_equalizer (a : ℚ) :
    Polynomial.aeval (0 : ℚ) (affinePolynomialF2AtA a) =
      Polynomial.aeval (1 : ℚ) (affinePolynomialF2AtA a) := by
  sorry

theorem affinePolynomialF2AtOneMinusA_mem_equalizer (a : ℚ) :
    Polynomial.aeval (0 : ℚ) (affinePolynomialF2AtOneMinusA a) =
      Polynomial.aeval (1 : ℚ) (affinePolynomialF2AtOneMinusA a) := by
  sorry

theorem affinePolynomialG_mem_equalizer (a : ℚ) :
    Polynomial.aeval (0 : ℚ) (affinePolynomialG a) =
      Polynomial.aeval (1 : ℚ) (affinePolynomialG a) := by
  sorry

def affineF1 (a : ℚ) : affineBaseSubalgebra :=
  affineBaseElement (affinePolynomialF1 a) (affinePolynomialF1_mem_equalizer a)

def affineF2AtA (a : ℚ) : affineBaseSubalgebra :=
  affineBaseElement (affinePolynomialF2AtA a) (affinePolynomialF2AtA_mem_equalizer a)

def affineF2AtOneMinusA (a : ℚ) : affineBaseSubalgebra :=
  affineBaseElement (affinePolynomialF2AtOneMinusA a)
    (affinePolynomialF2AtOneMinusA_mem_equalizer a)

def affineG (a : ℚ) : affineBaseSubalgebra :=
  affineBaseElement (affinePolynomialG a) (affinePolynomialG_mem_equalizer a)

/-- The presentation ring `ℚ[A,B]` and its two coordinate variables. -/
abbrev AffinePresentation := MvPolynomial (Fin 2) ℚ

def affinePresentationA : AffinePresentation := MvPolynomial.X 0

def affinePresentationB : AffinePresentation := MvPolynomial.X 1

def affinePresentationRelation : AffinePresentation :=
  affinePresentationA ^ 3 - affinePresentationB ^ 2 +
    affinePresentationA * affinePresentationB

def affinePresentationValues : Fin 2 → affineBaseSubalgebra := fun i =>
  if i = 0 then affineA else affineB

def affinePresentationMap : AffinePresentation →ₐ[ℚ] affineBaseSubalgebra :=
  MvPolynomial.aeval affinePresentationValues

theorem affine_presentation_relation_mem_kernel :
    affinePresentationRelation ∈ RingHom.ker affinePresentationMap.toRingHom := by
  sorry

theorem affine_presentation_surjective : Function.Surjective affinePresentationMap := by
  sorry

theorem affine_base_not_isField : ¬ IsField affineBaseSubalgebra := by
  sorry

theorem affine_presentation_relation_irreducible :
    Irreducible affinePresentationRelation := by
  sorry

theorem affine_presentation_primes_containing_relation
    (P : Ideal AffinePresentation) (hP : P.IsPrime)
    (hrel : Ideal.span {affinePresentationRelation} ≤ P) :
    P = Ideal.span {affinePresentationRelation} ∨ P.IsMaximal := by
  sorry

theorem affine_presentation_kernel :
    RingHom.ker affinePresentationMap.toRingHom =
      Ideal.span {affinePresentationRelation} := by
  sorry

/-- The induced presentation isomorphism has the direction determined by the
surjective map `ℚ[A,B] → R`: the quotient is isomorphic to `R`. -/
theorem affine_presentation_quotient_equiv :
    Nonempty ((AffinePresentation ⧸ Ideal.span {affinePresentationRelation}) ≃+*
      affineBaseSubalgebra) := by
  sorry

/-- The ambient ring `ℚ[z, 1/(z-a)]`. -/
abbrev AffineAmbient (a : ℚ) :=
  Localization.Away (Polynomial.X - Polynomial.C a)

def affineLocalizationMap (a : ℚ) : Polynomial ℚ →+* AffineAmbient a :=
  algebraMap _ _

def affineBaseImage (a : ℚ) : affineBaseSubalgebra →+* AffineAmbient a :=
  (affineLocalizationMap a).comp affineBaseSubalgebra.val.toRingHom

/-- The third generator used for `Rₐ`. -/
noncomputable def affineDenominatorInverse (a : ℚ) : AffineAmbient a :=
  ↑((IsLocalization.Away.algebraMap_isUnit
    (R := Polynomial ℚ) (S := AffineAmbient a)
    (Polynomial.X - Polynomial.C a)).unit⁻¹)

def affineOpenThirdGenerator (a : ℚ) : AffineAmbient a :=
  affineLocalizationMap a (Polynomial.C (a ^ 2 - a)) *
      affineDenominatorInverse a +
    affineLocalizationMap a Polynomial.X

/-- The subalgebra generated by the image of `R` and the third generator. -/
def affineOpenSubalgebra (a : ℚ) : Subalgebra ℚ (AffineAmbient a) :=
  Algebra.adjoin ℚ
    (Set.range (affineBaseImage a) ∪ {affineOpenThirdGenerator a})

abbrev AffineOpenRing (a : ℚ) := affineOpenSubalgebra a

noncomputable def affineAmbientEvaluation (a r : ℚ) (har : r ≠ a) :
    AffineAmbient a →ₐ[ℚ] ℚ :=
  IsLocalization.Away.liftAlgHom (f := Polynomial.aeval r)
    (Polynomial.X - Polynomial.C a) (by
    rw [isUnit_iff_ne_zero]
    simpa using sub_ne_zero.mpr har)

def affineOpenEqualizer (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    Subalgebra ℚ (AffineAmbient a) :=
  AlgHom.equalizer (affineAmbientEvaluation a 0 ha0.symm)
    (affineAmbientEvaluation a 1 ha1.symm)

def affineBaseToOpen (a : ℚ) : affineBaseSubalgebra →+* AffineOpenRing a :=
  RingHom.codRestrict (affineBaseImage a) (affineOpenSubalgebra a)
    (fun x => Algebra.subset_adjoin (Or.inl ⟨x, rfl⟩))

theorem affine_localization_map_injective (a : ℚ) :
    Function.Injective (affineLocalizationMap a) := by
  sorry

theorem affine_base_to_open_injective (a : ℚ) :
    Function.Injective (affineBaseToOpen a) := by
  sorry

def affineOpenThird (a : ℚ) : AffineOpenRing a :=
  ⟨affineOpenThirdGenerator a,
    Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))⟩

def affineOpenA (a : ℚ) : AffineOpenRing a :=
  affineBaseToOpen a affineA

def affineOpenF1 (a : ℚ) : AffineOpenRing a :=
  affineBaseToOpen a (affineF1 a)

def affineOpenG (a : ℚ) : AffineOpenRing a :=
  affineBaseToOpen a (affineG a)

theorem affine_open_is_generated_by_three (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    affineOpenSubalgebra a =
      Algebra.adjoin ℚ
        {affineLocalizationMap a (Polynomial.X ^ 2 - Polynomial.X),
          affineLocalizationMap a (Polynomial.X ^ 3 - Polynomial.X),
          affineOpenThirdGenerator a} := by
  sorry

theorem affine_open_is_equalizer (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    affineOpenSubalgebra a = affineOpenEqualizer a ha0 ha1 := by
  sorry

theorem affine_open_isFiniteType (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    Algebra.FiniteType ℚ (AffineOpenRing a) := by
  sorry

theorem affine_localization_evaluation_exists (a r : ℚ) (har : r ≠ a) :
    ∃ e : AffineAmbient a →+* ℚ,
      e.comp (affineLocalizationMap a) = Polynomial.evalRingHom r := by
  sorry

def affineEvaluation (r : ℚ) : affineBaseSubalgebra →+* ℚ :=
  (Polynomial.evalRingHom r).comp affineBaseSubalgebra.val.toRingHom

def affineMaximalIdeal (r : ℚ) : Ideal affineBaseSubalgebra :=
  RingHom.ker (affineEvaluation r)

theorem affineMaximalIdeal_isMaximal (r : ℚ) :
    (affineMaximalIdeal r).IsMaximal := by
  sorry

def affinePoint (r : ℚ) : PrimeSpectrum affineBaseSubalgebra :=
  ⟨affineMaximalIdeal r, (affineMaximalIdeal_isMaximal r).isPrime⟩

abbrev affineM0 : Ideal affineBaseSubalgebra := affineMaximalIdeal 0

def affineMa (a : ℚ) : Ideal affineBaseSubalgebra := affineMaximalIdeal a

def affineMOneMinusA (a : ℚ) : Ideal affineBaseSubalgebra :=
  affineMaximalIdeal (1 - a)

theorem affine_evaluation_kernel_formulas (a : ℚ) :
    affineM0 = Ideal.span {affineA, affineBZero} ∧
      affineMa a = Ideal.span {affineF1 a, affineF2AtA a} ∧
      affineMOneMinusA a =
        Ideal.span {affineF1 a, affineF2AtOneMinusA a} := by
  sorry

theorem affine_evaluation_at_zero_extends (a : ℚ) (ha0 : a ≠ 0) :
    ∃ e : AffineOpenRing a →+* ℚ,
      e.comp (affineBaseToOpen a) = affineEvaluation 0 := by
  sorry

theorem affine_evaluation_at_one_minus_a_extends (a : ℚ) (haHalf : a ≠ 1 / 2) :
    ∃ e : AffineOpenRing a →+* ℚ,
      e.comp (affineBaseToOpen a) = affineEvaluation (1 - a) := by
  sorry

theorem affine_evaluation_at_a_does_not_extend (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ¬ ∃ e : AffineOpenRing a →+* ℚ,
      e.comp (affineBaseToOpen a) = affineEvaluation a := by
  sorry

def affineOpenSpectrumMap (a : ℚ) :
    PrimeSpectrum (AffineOpenRing a) → PrimeSpectrum affineBaseSubalgebra :=
  PrimeSpectrum.comap (affineBaseToOpen a)

theorem affine_m_a_not_in_spectrum_image (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    ∀ I : Ideal (AffineOpenRing a),
      I.comap (affineBaseToOpen a) ≠ affineMa a := by
  sorry

theorem affine_obstruction_identity (a : ℚ) :
    affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
        affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
          affineOpenThirdGenerator a =
      affineLocalizationMap a
          ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * Polynomial.C (a ^ 2 - a)) +
        affineLocalizationMap a
          ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 *
            (Polynomial.X - Polynomial.C a) * Polynomial.X) := by
  sorry

theorem affine_m_a_obstruction (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    (affineOpenA a) ^ 2 ∈
      Ideal.map (affineBaseToOpen a) (affineMa a) := by
  sorry

theorem affine_base_basic_open_f1_complement (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    (PrimeSpectrum.basicOpen (affineF1 a) : Set (PrimeSpectrum affineBaseSubalgebra))ᶜ =
      {affinePoint a, affinePoint (1 - a)} := by
  sorry

abbrev AffineBaseAway (a : ℚ) := Localization.Away (affineF1 a)

abbrev AffineOpenAway (a : ℚ) := Localization.Away (affineOpenF1 a)

theorem affine_away_rings_equivalent (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    Nonempty (AffineBaseAway a ≃+* AffineOpenAway a) := by
  sorry

theorem affine_first_basic_open_homeomorph (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    ∃ e :
        {p : PrimeSpectrum (AffineOpenRing a) //
            p ∈ (PrimeSpectrum.basicOpen (affineOpenF1 a) :
              Set (PrimeSpectrum (AffineOpenRing a)))} ≃ₜ
          {p : PrimeSpectrum affineBaseSubalgebra //
            p ∈ (PrimeSpectrum.basicOpen (affineF1 a) :
              Set (PrimeSpectrum affineBaseSubalgebra))},
      ∀ p, (e p).1 = affineOpenSpectrumMap a p.1 := by
  sorry

theorem affine_quadratic_at_one_minus_a (a : ℚ) :
    (affineQuadratic a).eval (1 - a) = 0 ↔ a = 0 ∨ a = 1 := by
  sorry

theorem affine_second_basic_open_complement (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    ∃ s : Finset ℚ, s.card ≤ 2 ∧
      (∀ r : ℚ, r ∈ s ↔ (affineQuadratic a).eval r = 0) ∧
      (PrimeSpectrum.basicOpen (affineG a) : Set (PrimeSpectrum affineBaseSubalgebra))ᶜ =
        {affinePoint a} ∪ affinePoint '' (s : Set ℚ) := by
  sorry

theorem affine_second_basic_open_homeomorph (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    ∃ e :
        {p : PrimeSpectrum (AffineOpenRing a) //
            p ∈ (PrimeSpectrum.basicOpen (affineOpenG a) :
              Set (PrimeSpectrum (AffineOpenRing a)))} ≃ₜ
          {p : PrimeSpectrum affineBaseSubalgebra //
            p ∈ (PrimeSpectrum.basicOpen (affineG a) :
              Set (PrimeSpectrum affineBaseSubalgebra))},
      ∀ p, (e p).1 = affineOpenSpectrumMap a p.1 := by
  sorry

theorem affine_open_distinguished_opens_cover (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    Ideal.span {affineOpenF1 a, affineOpenG a} = (⊤ : Ideal (AffineOpenRing a)) := by
  sorry

theorem affine_second_open_avoids_one_minus_a (a : ℚ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (haHalf : a ≠ 1 / 2) :
    affinePoint (1 - a) ∈
      (PrimeSpectrum.basicOpen (affineG a) : Set (PrimeSpectrum affineBaseSubalgebra)) := by
  sorry

theorem affine_open_spectrum_range (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    Set.range (affineOpenSpectrumMap a) =
      ({affinePoint a} : Set (PrimeSpectrum affineBaseSubalgebra))ᶜ := by
  sorry

theorem affine_open_spectrum_homeomorph_complement (a : ℚ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (haHalf : a ≠ 1 / 2) :
    ∃ e : PrimeSpectrum (AffineOpenRing a) ≃ₜ
        {p : PrimeSpectrum affineBaseSubalgebra // p ≠ affinePoint a},
      ∀ p, (e p).1 = affineOpenSpectrumMap a p := by
  sorry

/-- The statement that all units are scalar units from `ℚ`. -/
def UnitsAreRationalScalars {A : Type*} [CommRing A] [Algebra ℚ A] : Prop :=
  ∀ u : Aˣ, ∃ q : ℚˣ, u = Units.map (algebraMap ℚ A) q

theorem affine_base_units_are_rational_scalars :
    UnitsAreRationalScalars (A := affineBaseSubalgebra) := by
  sorry

theorem affine_open_units_are_rational_scalars (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    UnitsAreRationalScalars (A := AffineOpenRing a) := by
  sorry

noncomputable def affineDenominatorUnit (a : ℚ) : (AffineAmbient a)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (Polynomial.X - Polynomial.C a)).unit

theorem affine_ambient_units_description (a : ℚ) (u : (AffineAmbient a)ˣ) :
    ∃ c : ℚˣ, ∃ n : ℤ,
      u = Units.map (algebraMap ℚ (AffineAmbient a)) c *
        affineDenominatorUnit a ^ n := by
  sorry

def IsLocalizationAlong {R A : Type*} [CommRing R] [CommRing A]
    (M : Submonoid R) (f : R →+* A) : Prop :=
  @IsLocalization R _ M A _ f.toAlgebra

theorem localization_inverts_denominators {R : Type*} [CommRing R]
    (M : Submonoid R) (s : M) :
    IsUnit (algebraMap R (Localization M) (s : R)) := by
  exact IsLocalization.map_units (Localization M) s

theorem affine_open_is_not_a_localization (a : ℚ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (haHalf : a ≠ 1 / 2) :
  ∀ M : Submonoid affineBaseSubalgebra,
      ¬ IsLocalizationAlong M (affineBaseToOpen a) := by
  sorry

theorem affine_half_denominator_power_mem_base (n : ℕ) :
    (Polynomial.X - Polynomial.C (1 / 2 : ℚ)) ^ n ∈ affineBaseSubalgebra ↔
      Even n := by
  sorry

end

end Formalization.Books.Algebra.Unit27
