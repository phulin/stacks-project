import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Flat

/-!
# Examples, Chapter 37: finite type, not finitely presented, flat at prime

This file records the construction in the section
“Finite type, not finitely presented, flat at prime”.  The algebraic objects
are defined explicitly; the substantive verification lemmas are theorem
interfaces for the proof stage.
-/

noncomputable section

open DirectSum

namespace Formalization.«Books.Examples».Unit37

universe u v

/-! ## The local base ring and the square-zero extension -/

/-- The two-variable polynomial ring used for the local base. -/
abbrev ftBasePolynomialRing (k : Type u) [Field k] := MvPolynomial (Fin 2) k

/-- The variables `x` and `y` in the base polynomial ring. -/
def ftBaseXVar : Fin 2 := 0

def ftBaseYVar : Fin 2 := 1

def ftBaseX (k : Type u) [Field k] : ftBasePolynomialRing k :=
  MvPolynomial.X ftBaseXVar

def ftBaseY (k : Type u) [Field k] : ftBasePolynomialRing k :=
  MvPolynomial.X ftBaseYVar

/-- The maximal ideal `(x, y)` before localization. -/
def ftBaseMaximalIdeal (k : Type u) [Field k] : Ideal (ftBasePolynomialRing k) :=
  Ideal.span {ftBaseX k, ftBaseY k}

/-- The base maximal ideal is prime. -/
instance ftBaseMaximalIdeal_isPrime (k : Type u) [Field k] :
    (ftBaseMaximalIdeal k).IsPrime := by
  sorry

/-- The base maximal ideal is maximal. -/
instance ftBaseMaximalIdeal_isMaximal (k : Type u) [Field k] :
    (ftBaseMaximalIdeal k).IsMaximal := by
  sorry

/-- The local ring `A₀ = k[x, y]_(x,y)`. -/
abbrev ftA0 (k : Type u) [Field k] :=
  Localization.AtPrime (ftBaseMaximalIdeal k)

abbrev ftAPolynomialRing (k : Type u) [Field k] [h : CommRing (ftA0 k)] :=
  @MvPolynomial ℕ (ftA0 k) h.toCommSemiring

abbrev ftPolynomialRing (R : Type v) [h : CommRing R] :=
  @Polynomial R h.toCommSemiring.toSemiring


/-- A small wrapper for the canonical ideal quotient, keeping its coefficient ring explicit. -/
abbrev ftIdealQuotient (R : Type v) [CommRing R] (I : Ideal R) := R ⧸ I

abbrev ftAway (R : Type v) [CommRing R] (f : R) := Localization.Away f

def ftIdealQuotientMk {R : Type v} [CommRing R] (I : Ideal R) :
    R →+* ftIdealQuotient R I :=
  Ideal.Quotient.mk I

def ftIdealQuotientLift {R : Type v} [CommRing R] {S : Type v} [Semiring S]
    (I : Ideal R) (f : R →+* S) (h : ∀ r : R, r ∈ I → f r = 0) :
    ftIdealQuotient R I →+* S :=
  Ideal.Quotient.lift I f h

def ftX (k : Type u) [Field k] : ftA0 k :=
  algebraMap (ftBasePolynomialRing k) (ftA0 k) (ftBaseX k)

def ftY (k : Type u) [Field k] : ftA0 k :=
  algebraMap (ftBasePolynomialRing k) (ftA0 k) (ftBaseY k)

/-- The element `y + x^n + x^(2n+1)` defining the `n`th prime. -/
def ftPrimeEquation (k : Type u) [Field k] (n : ℕ) : ftA0 k :=
  ftY k + (ftX k) ^ n + (ftX k) ^ (2 * n + 1)

/-- The principal ideal `𝔭₀,ₙ = (y + x^n + x^(2n+1))`. -/
def ftP0 (k : Type u) [Field k] (n : ℕ) : Ideal (ftA0 k) :=
  Ideal.span {ftPrimeEquation k n}

instance ftP0_isPrime (k : Type u) [Field k] (n : ℕ) :
    (ftP0 k n).IsPrime := by
  sorry

/-- The relations in the square-zero extension before quotienting. -/
def ftARelations (k : Type u) [Field k] : Set (ftAPolynomialRing k) :=
  Set.range (fun p : ℕ × ℕ => MvPolynomial.X p.1 * MvPolynomial.X p.2) ∪
    Set.range (fun n : ℕ =>
      MvPolynomial.X n * MvPolynomial.C (ftPrimeEquation k n))

def ftARelationsIdeal (k : Type u) [Field k] : Ideal (ftAPolynomialRing k) :=
  Ideal.span (ftARelations k)

/-- The ring
`A = A₀[z₁, z₂, …]/(zₙzₘ, zₙ(y+xⁿ+x^(2n+1)))`. -/
abbrev ftA (k : Type u) [Field k] :=
  ftIdealQuotient (ftAPolynomialRing k) (ftARelationsIdeal k)

def ftAGenerator (k : Type u) [Field k] (n : ℕ) : ftA k :=
  ftIdealQuotientMk (ftARelationsIdeal k) (MvPolynomial.X n)

def ftA0ToA (k : Type u) [Field k] : ftA0 k →+* ftA k :=
  algebraMap (ftA0 k) (ftA k)

def ftAX (k : Type u) [Field k] : ftA k :=
  ftA0ToA k (ftX k)

def ftAY (k : Type u) [Field k] : ftA k :=
  ftA0ToA k (ftY k)

def ftAPrimeEquation (k : Type u) [Field k] (n : ℕ) : ftA k :=
  ftA0ToA k (ftPrimeEquation k n)

/-- The augmentation which kills all the `zₙ`. -/
def ftAAugmentation (k : Type u) [Field k] :
    ftAPolynomialRing k →+* ftA0 k :=
  MvPolynomial.eval₂Hom (RingHom.id _) (fun _ => 0)

theorem ftARelations_le_augmentation_ker (k : Type u) [Field k] :
    ftARelationsIdeal k ≤ RingHom.ker (ftAAugmentation k) := by
  sorry

/-- The quotient map `A → A₀`. -/
def ftAToA0 (k : Type u) [Field k] : ftA k →+* ftA0 k :=
  ftIdealQuotientLift (ftARelationsIdeal k) (ftAAugmentation k)
    (fun _ h => ftARelations_le_augmentation_ker k h)

theorem ftAToA0_surjective (k : Type u) [Field k] :
    Function.Surjective (ftAToA0 k) := by
  sorry

theorem ftAToA0_kernel_square_zero (k : Type u) [Field k] :
    (RingHom.ker (ftAToA0 k)) ^ 2 = ⊥ := by
  sorry

/-- The prime of `A` corresponding to `𝔭₀,ₙ`. -/
def ftAPrime (k : Type u) [Field k] (n : ℕ) : Ideal (ftA k) :=
  Ideal.comap (ftAToA0 k) (ftP0 k n)

instance ftAPrime_isPrime (k : Type u) [Field k] (n : ℕ) :
    (ftAPrime k n).IsPrime := by
  sorry

/-- The prime spectra of `A` and `A₀` correspond through the square-zero
extension. -/
theorem ft_primeSpectrum_comap_bijective (k : Type u) [Field k] :
    Function.Bijective (PrimeSpectrum.comap (ftAToA0 k)) := by
  sorry

instance ftA_isLocalRing (k : Type u) [Field k] : IsLocalRing (ftA k) := by
  sorry

theorem ftAGenerator_annihilator (k : Type u) [Field k] (n : ℕ) :
    (Submodule.span (ftA k) ({ftAGenerator k n} : Set (ftA k))).annihilator =
      ftAPrime k n := by
  sorry

/-! ## The standard-étale algebra `C` -/

/-- The polynomial relation `xz² + z + y`. -/
def ftCRelation (k : Type u) [Field k] : ftPolynomialRing (ftA k) :=
  Polynomial.C (ftAX k) * Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (ftAY k)

def ftCRelationsIdeal (k : Type u) [Field k] : Ideal (ftPolynomialRing (ftA k)) :=
  Ideal.span {ftCRelation k}

abbrev ftCQuotient (k : Type u) [Field k] :=
  ftIdealQuotient (ftPolynomialRing (ftA k)) (ftCRelationsIdeal k)

def ftCDerivativePolynomial (k : Type u) [Field k] : ftPolynomialRing (ftA k) :=
  Polynomial.C (2 * ftAX k) * Polynomial.X + 1

def ftCDerivative (k : Type u) [Field k] : ftCQuotient k :=
  ftIdealQuotientMk (ftCRelationsIdeal k) (ftCDerivativePolynomial k)

/-- The ring
`C = A[z]/(xz²+z+y)[1/(2zx+1)]`. -/
abbrev ftC (k : Type u) [Field k] :=
  ftAway (ftCQuotient k) (ftCDerivative k)

def ftAToC (k : Type u) [Field k] : ftA k →+* ftC k :=
  algebraMap (ftA k) (ftC k)

def ftCZ (k : Type u) [Field k] : ftC k :=
  algebraMap (ftCQuotient k) (ftC k)
    (ftIdealQuotientMk (ftCRelationsIdeal k) Polynomial.X)

def ftCX (k : Type u) [Field k] : ftC k :=
  ftAToC k (ftAX k)

def ftCY (k : Type u) [Field k] : ftC k :=
  ftAToC k (ftAY k)

def ftCZn (k : Type u) [Field k] (n : ℕ) : ftC k :=
  ftAToC k (ftAGenerator k n)

theorem ftAToC_etale (k : Type u) [Field k] :
    RingHom.Etale (ftAToC k) := by
  sorry

theorem ftAToC_flat (k : Type u) [Field k] :
    RingHom.Flat (ftAToC k) := by
  sorry

/-- The maximal ideal generated by `x`, `y`, `z`, and all `zₙ`. -/
def ftCQ (k : Type u) [Field k] : Ideal (ftC k) :=
  Ideal.span (({ftCX k, ftCY k, ftCZ k} : Set (ftC k)) ∪ Set.range (ftCZn k))

instance ftCQ_isMaximal (k : Type u) [Field k] :
    (ftCQ k).IsMaximal := by
  sorry

instance ftCQ_isPrime (k : Type u) [Field k] :
    (ftCQ k).IsPrime := by
  sorry

def ftCPrimeIdeal (k : Type u) [Field k] (n : ℕ) : Ideal (ftC k) :=
  Ideal.map (ftAToC k) (ftAPrime k n)

theorem ftCZn_annihilator (k : Type u) [Field k] (n : ℕ) :
    (Submodule.span (ftC k) ({ftCZn k n} : Set (ftC k))).annihilator =
      ftCPrimeIdeal k n := by
  sorry

/-! ## The fibre computation -/

abbrev ftCPrimeFibre (k : Type u) [Field k] (n : ℕ) :=
  ftIdealQuotient (ftC k) (ftCPrimeIdeal k n)

def ftCRelationOverA0 (k : Type u) [Field k] : ftPolynomialRing (ftA0 k) :=
  Polynomial.C (ftX k) * Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (ftY k)

abbrev ftCPrimePresentationBase (k : Type u) [Field k] (n : ℕ) :=
  ftIdealQuotient (ftPolynomialRing (ftA0 k))
    (Ideal.span {ftCRelationOverA0 k, Polynomial.C (ftPrimeEquation k n)})

def ftCPrimePresentationDerivative (k : Type u) [Field k] (n : ℕ) :
    ftCPrimePresentationBase k n :=
  ftIdealQuotientMk _ (Polynomial.C (2 * ftX k) * Polynomial.X + 1)

abbrev ftCPrimePresentation (k : Type u) [Field k] (n : ℕ) :=
  ftAway (ftCPrimePresentationBase k n) (ftCPrimePresentationDerivative k n)

def ftKXMaximalIdeal (k : Type u) [Field k] : Ideal (ftPolynomialRing k) :=
  Ideal.span {(Polynomial.X : ftPolynomialRing k)}

instance ftKXMaximalIdeal_isPrime (k : Type u) [Field k] :
    (ftKXMaximalIdeal k).IsPrime := by
  sorry

instance ftKXMaximalIdeal_isMaximal (k : Type u) [Field k] :
    (ftKXMaximalIdeal k).IsMaximal := by
  sorry

abbrev ftKXLocal (k : Type u) [Field k] :=
  Localization.AtPrime (ftKXMaximalIdeal k)

def ftKX (k : Type u) [Field k] : ftKXLocal k :=
  algebraMap (ftPolynomialRing k) (ftKXLocal k) Polynomial.X

def ftSecondRelationPolynomial (k : Type u) [Field k] (n : ℕ) :
    ftPolynomialRing (ftKXLocal k) :=
  Polynomial.C (ftKX k) * Polynomial.X ^ 2 + Polynomial.X -
    Polynomial.C (ftKX k ^ n + ftKX k ^ (2 * n + 1))

def ftSecondDerivative (k : Type u) [Field k] : ftPolynomialRing (ftKXLocal k) :=
  Polynomial.C (2 * ftKX k) * Polynomial.X + 1

abbrev ftSecondBase (k : Type u) [Field k] (n : ℕ) :=
  ftIdealQuotient (ftPolynomialRing (ftKXLocal k))
    (Ideal.span {ftSecondRelationPolynomial k n})

def ftSecondDerivativeQuotient (k : Type u) [Field k] (n : ℕ) :
    ftSecondBase k n :=
  ftIdealQuotientMk _ (ftSecondDerivative k)

abbrev ftSecondPresentation (k : Type u) [Field k] (n : ℕ) :=
  ftAway (ftSecondBase k n) (ftSecondDerivativeQuotient k n)

def ftSecondLeftRelation (k : Type u) [Field k] (n : ℕ) :
    ftPolynomialRing (ftKXLocal k) :=
  Polynomial.X - Polynomial.C (ftKX k ^ n)

abbrev ftSecondLeft (k : Type u) [Field k] (n : ℕ) :=
  ftIdealQuotient (ftPolynomialRing (ftKXLocal k)) (Ideal.span {ftSecondLeftRelation k n})

def ftSecondRightRelation (k : Type u) [Field k] (n : ℕ) :
    ftPolynomialRing (ftKXLocal k) :=
  Polynomial.C (ftKX k) * Polynomial.X +
    Polynomial.C (ftKX k ^ (n + 1) + 1)

abbrev ftSecondRightBase (k : Type u) [Field k] (n : ℕ) :=
  ftIdealQuotient (ftPolynomialRing (ftKXLocal k))
    (Ideal.span {ftSecondRightRelation k n})

def ftSecondRightDerivative (k : Type u) [Field k] (n : ℕ) :
    ftSecondRightBase k n :=
  ftIdealQuotientMk _ (ftSecondDerivative k)

abbrev ftSecondRight (k : Type u) [Field k] (n : ℕ) :=
  ftAway (ftSecondRightBase k n) (ftSecondRightDerivative k n)

abbrev ftSecondProduct (k : Type u) [Field k] (n : ℕ) :=
  ftSecondLeft k n × ftSecondRight k n

abbrev ftRationalFunctionField (k : Type u) [Field k] :=
  FractionRing (Polynomial k)

abbrev ftFinalProduct (k : Type u) [Field k] :=
  ftKXLocal k × ftRationalFunctionField k

theorem ftCPrimeFibre_equiv_first_presentation (k : Type u) [Field k] (n : ℕ) :
    Nonempty (ftCPrimeFibre k n ≃+* ftCPrimePresentation k n) := by
  sorry

theorem ftFirstPresentation_equiv_second_presentation (k : Type u) [Field k]
    (n : ℕ) :
    Nonempty (ftCPrimePresentation k n ≃+* ftSecondPresentation k n) := by
  sorry

theorem ftFibre_factorization (k : Type u) [Field k] (n : ℕ) :
    (Polynomial.X - Polynomial.C (ftKX k ^ n)) *
        (Polynomial.C (ftKX k) * Polynomial.X +
          Polynomial.C (ftKX k ^ (n + 1) + 1)) =
      ftSecondRelationPolynomial k n := by
  sorry

theorem ftSecondPresentation_equiv_product (k : Type u) [Field k] (n : ℕ) :
    Nonempty (ftSecondPresentation k n ≃+* ftSecondProduct k n) := by
  sorry

theorem ftSecondProduct_equiv_final_product (k : Type u) [Field k] (n : ℕ) :
    Nonempty (ftSecondProduct k n ≃+* ftFinalProduct k) := by
  sorry

/-! ## The two maximal ideals over `𝔭ₙ` -/

def ftCRPrimeIdeal (k : Type u) [Field k] (n : ℕ) : Ideal (ftC k) :=
  ftCPrimeIdeal k n ⊔ Ideal.span {ftCZ k - (ftCX k) ^ n}

def ftCQPrimeIdeal (k : Type u) [Field k] (n : ℕ) : Ideal (ftC k) :=
  ftCPrimeIdeal k n ⊔
    Ideal.span {ftCX k * ftCZ k + (ftCX k) ^ (n + 1) + 1}

def ftXi (k : Type u) [Field k] (n : ℕ) : ftC k :=
  (ftCZ k - (ftCX k) ^ n) * ftCZn k n

theorem ftCPrimeIdeal_eq_inf (k : Type u) [Field k] (n : ℕ) :
    ftCPrimeIdeal k n = ftCRPrimeIdeal k n ⊓ ftCQPrimeIdeal k n := by
  sorry

theorem ftCRPrimeIdeal_sup_CQPrimeIdeal (k : Type u) [Field k] (n : ℕ) :
    ftCRPrimeIdeal k n ⊔ ftCQPrimeIdeal k n = ⊤ := by
  sorry

theorem ftCPrimeIdeal_eq_mul (k : Type u) [Field k] (n : ℕ) :
    ftCPrimeIdeal k n = ftCRPrimeIdeal k n * ftCQPrimeIdeal k n := by
  sorry

theorem ftCQPrimeIdeal_annihilator_Xi (k : Type u) [Field k] (n : ℕ) :
    (Submodule.span (ftC k) ({ftXi k n} : Set (ftC k))).annihilator =
      ftCQPrimeIdeal k n := by
  sorry

theorem ftCRPrimeIdeal_le_CQ (k : Type u) [Field k] (n : ℕ) :
    ftCRPrimeIdeal k n ≤ ftCQ k := by
  sorry

theorem ftCQPrimeIdeal_sup_CQ (k : Type u) [Field k] (n : ℕ) :
    ftCQPrimeIdeal k n ⊔ ftCQ k = ⊤ := by
  sorry

theorem ftCQPrimeIdeal_sup_CQPrimeIdeal (k : Type u) [Field k] {n m : ℕ}
    (hnm : n ≠ m) :
    ftCQPrimeIdeal k n ⊔ ftCQPrimeIdeal k m = ⊤ := by
  sorry

theorem ftCQPrimeIdeal_mul_Xi (k : Type u) [Field k] (n : ℕ) {r : ftC k}
    (hr : r ∈ ftCQPrimeIdeal k n) : r * ftXi k n = 0 := by
  sorry

/-! ## The image algebra `B` -/

abbrev ftCAtQ (k : Type u) [Field k] :=
  Localization.AtPrime (ftCQ k)

def ftCToCAtQ (k : Type u) [Field k] : ftC k →+* ftCAtQ k :=
  algebraMap (ftC k) (ftCAtQ k)

/-- `B = Im(C → C_𝔮)`, represented by Mathlib's canonical range subring. -/
abbrev ftB (k : Type u) [Field k] :=
  RingHom.range (ftCToCAtQ k)

def ftCToB (k : Type u) [Field k] : ftC k →+* ftB k :=
  (ftCToCAtQ k).rangeRestrict

def ftAToB (k : Type u) [Field k] : ftA k →+* ftB k :=
  (ftCToB k).comp (ftAToC k)

instance ftB_algebra (k : Type u) [Field k] : Algebra (ftA k) (ftB k) :=
  (ftAToB k).toAlgebra

def ftBQPrime (k : Type u) [Field k] : Ideal (ftB k) :=
  Ideal.map (ftCToB k) (ftCQ k)

instance ftBQPrime_isPrime (k : Type u) [Field k] :
    (ftBQPrime k).IsPrime := by
  sorry

theorem ftB_finiteType (k : Type u) [Field k] :
    RingHom.FiniteType (ftAToB k) := by
  sorry

theorem ftB_localization_equiv (k : Type u) [Field k] :
    Nonempty (Localization.AtPrime (ftBQPrime k) ≃+* ftCAtQ k) := by
  sorry

def ftAToBLocal (k : Type u) [Field k] (g : ftB k) :
    ftA k →+* Localization.Away g :=
  (algebraMap (ftB k) (Localization.Away g)).comp (ftAToB k)

def ftAToBQ (k : Type u) [Field k] :
    ftA k →+* Localization.AtPrime (ftBQPrime k) :=
  (algebraMap (ftB k) (Localization.AtPrime (ftBQPrime k))).comp (ftAToB k)

theorem ftB_localization_at_prime_flat (k : Type u) [Field k] :
    RingHom.Flat (ftAToBQ k) := by
  sorry

theorem ftBQPrime_lies_over_maximal (k : Type u) [Field k] :
    Ideal.comap (ftAToB k) (ftBQPrime k) = IsLocalRing.maximalIdeal (ftA k) := by
  sorry

def ftBGenerator (k : Type u) [Field k] (n : ℕ) : ftB k :=
  ftCToB k (ftCZn k n)

def ftBX (k : Type u) [Field k] : ftB k :=
  ftCToB k (ftCX k)

def ftBLocalGenerator (k : Type u) [Field k] (g : ftB k) (n : ℕ) :
    Localization.Away g :=
  algebraMap (ftB k) (Localization.Away g) (ftBGenerator k n)

def ftBLocalPrime (k : Type u) [Field k] (g : ftB k) (n : ℕ) :
    Ideal (Localization.Away g) :=
  Ideal.map (ftAToBLocal k g) (ftAPrime k n)

def ftBLocalDifference (k : Type u) [Field k] (g : ftB k) (n : ℕ) :
    Localization.Away g :=
  algebraMap (ftB k) (Localization.Away g)
    (ftCToB k (ftCZ k) - (ftBX k) ^ n)

theorem ftB_local_annihilator_under_flat (k : Type u) [Field k] (g : ftB k)
    (hg : g ∉ ftBQPrime k) (n : ℕ)
    (hflat : RingHom.Flat (ftAToBLocal k g)) :
    (Submodule.span (Localization.Away g) ({ftBLocalGenerator k g n} :
      Set (Localization.Away g))).annihilator = ftBLocalPrime k g n := by
  sorry

theorem ftB_local_difference_not_mem_prime (k : Type u) [Field k] (g : ftB k)
    (hg : g ∉ ftBQPrime k) (n : ℕ) :
    ftBLocalDifference k g n ∉ ftBLocalPrime k g n := by
  sorry

/-! ## The kernel calculation behind non-finite-presentation -/

abbrev ftKernelIndex (k : Type u) [Field k] (g : ftC k) :=
  {n : ℕ // g ∉ ftCQPrimeIdeal k n}

abbrev ftKernelSummand (k : Type u) [Field k] (g : ftC k)
    (n : ftKernelIndex k g) :=
  ftIdealQuotient (ftC k) (ftCQPrimeIdeal k n.1)

abbrev ftKernelDirectSum (k : Type u) [Field k] (g : ftC k) :=
  ⨁ n : ftKernelIndex k g, ftKernelSummand k g n

def ftQuotientMulAddHom {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) (s : S)
    (h : ∀ r : R, r ∈ I → f r * s = 0) : ftIdealQuotient R I →+ S :=
  QuotientAddGroup.lift I.toAddSubgroup
    ((AddMonoidHom.mulRight s).comp f.toAddMonoidHom)
    (fun r hr => h r hr)

def ftCPrimeSummandMap (k : Type u) [Field k] (g : ftC k)
    (n : ftKernelIndex k g) : ftKernelSummand k g n →+
      Localization.Away g :=
  ftQuotientMulAddHom (ftCQPrimeIdeal k n.1)
    (algebraMap (ftC k) (Localization.Away g))
    (algebraMap (ftC k) (Localization.Away g) (ftXi k n.1))
    (by
      intro r hr
      rw [← map_mul, ftCQPrimeIdeal_mul_Xi k n.1 hr, map_zero])

def ftKernelMap (k : Type u) [Field k] (g : ftC k) :
    ftKernelDirectSum k g →+ Localization.Away g :=
  by
    classical
    exact DirectSum.toAddMonoid (fun n => ftCPrimeSummandMap k g n)

def ftCLocalizationMap (k : Type u) [Field k] (g : ftC k) :
    Localization.Away g →+* Localization.Away (ftCToB k g) :=
  Localization.awayMap (ftCToB k) g

theorem ftKernelMap_on_summand (k : Type u) [Field k] (g : ftC k)
    (n : ftKernelIndex k g) (c : ftKernelSummand k g n) :
    ftKernelMap k g (DirectSum.of _ n c) = ftCPrimeSummandMap k g n c := by
  classical
  change DirectSum.toAddMonoid (fun n => ftCPrimeSummandMap k g n)
      (DirectSum.of _ n c) = ftCPrimeSummandMap k g n c
  exact DirectSum.toAddMonoid_of (fun n => ftCPrimeSummandMap k g n) n c

theorem ftCQPrime_contains_only_finitely_many (k : Type u) [Field k] (g : ftC k)
    (hg : g ∉ ftCQ k) :
    {n : ℕ | g ∈ ftCQPrimeIdeal k n}.Finite := by
  sorry

theorem ftKernelMap_injective (k : Type u) [Field k] (g : ftC k)
    (hg : g ∉ ftCQ k) :
    Function.Injective (ftKernelMap k g) := by
  sorry

theorem ftKernelMap_range_eq_kernel (k : Type u) [Field k] (g : ftC k)
    (hg : g ∉ ftCQ k) :
    Set.range (ftKernelMap k g) =
      (RingHom.ker (ftCLocalizationMap k g) : Set (Localization.Away g)) := by
  sorry

theorem ftB_local_finitePresentation_iff_kernel_fg (k : Type u) [Field k]
    (g : ftC k) :
    RingHom.FinitePresentation (ftAToBLocal k (ftCToB k g)) ↔
      (RingHom.ker (ftCLocalizationMap k g)).FG := by
  sorry

theorem ftB_local_not_finitePresentation (k : Type u) [Field k] (g : ftB k)
    (hg : g ∉ ftBQPrime k) :
    ¬ RingHom.FinitePresentation (ftAToBLocal k g) := by
  sorry

theorem ftB_local_not_flat (k : Type u) [Field k] (g : ftB k)
    (hg : g ∉ ftBQPrime k) :
    ¬ RingHom.Flat (ftAToBLocal k g) := by
  sorry

/-! ## The chapter's final existence statement -/

theorem ft_raynaud_gruson_example :
    ∃ (k : Type u) (_ : Field k),
      IsLocalRing (ftA k) ∧
        RingHom.FiniteType (ftAToB k) ∧
        ∃ q : Ideal (ftB k),
          q = ftBQPrime k ∧
            Ideal.comap (ftAToB k) q = IsLocalRing.maximalIdeal (ftA k) ∧
            RingHom.Flat (ftAToBQ k) ∧
            ∀ g : ftB k, g ∉ q →
              ¬ RingHom.FinitePresentation (ftAToBLocal k g) ∧
                ¬ RingHom.Flat (ftAToBLocal k g) := by
  sorry

end Formalization.«Books.Examples».Unit37
