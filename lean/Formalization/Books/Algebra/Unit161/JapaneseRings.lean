import Formalization.Books.Algebra.Unit37.NormalRings
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Commutative Algebra, Chapter 161: Japanese rings

This file records the definitions, examples, and theorem interfaces in the
source section “Japanese rings”.  Integral closures are Mathlib's canonical
`integralClosure` subrings, and finiteness is expressed by `Module.Finite`.
-/

namespace Formalization.Books.Algebra.Unit161

open Set
open Formalization.Books.Algebra.Unit37

universe u v

noncomputable section

/-! ## N-1 and N-2 -/

/-- A domain is N-1 when its integral closure in its fraction field is finite. -/
def IsNOne (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  Module.Finite R (integralClosure R (FractionRing R))

/-- A domain is N-2, or Japanese, when all finite field extensions have finite
integral closure. -/
def IsJapaneseDomain (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (FractionRing R) L]
    [Module.Finite (FractionRing R) L],
    letI : Algebra R L :=
      ((algebraMap (FractionRing R) L).comp
        (algebraMap R (FractionRing R))).toAlgebra
    Module.Finite R (integralClosure R L)

/-! The non-Noetherian polynomial examples. -/

theorem mvPolynomial_nat_isJapanese_not_noetherian
    (k : Type u) [Field k] :
    IsJapaneseDomain (MvPolynomial ℕ k) ∧
      ¬ IsNoetherianRing (MvPolynomial ℕ k) := by
  sorry

theorem mvPolynomial_int_isJapanese_not_noetherian :
    IsJapaneseDomain (MvPolynomial ℕ ℤ) ∧
      ¬ IsNoetherianRing (MvPolynomial ℕ ℤ) := by
  sorry

/-! ## Localization and finite extensions -/

theorem isNOne_localization
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (M : Submonoid R)
    [Algebra R S] [IsLocalization M S]
    (hR : IsNOne R) : IsNOne S := by
  sorry

theorem isJapaneseDomain_localization
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (M : Submonoid R)
    [Algebra R S] [IsLocalization M S]
    (hR : IsJapaneseDomain R) : IsJapaneseDomain S := by
  sorry

theorem isNOne_of_localizations
    {R : Type u} [CommRing R] [IsDomain R]
    {ι : Type v} [Fintype ι] (f : ι → R)
    (hunit : Ideal.span (Set.range f) = ⊤)
    (hdom : ∀ i, IsDomain (Localization.Away (f i)))
    (hloc : ∀ i, @IsNOne (Localization.Away (f i)) _ (hdom i)) : IsNOne R := by
  sorry

theorem isJapaneseDomain_of_localizations
    {R : Type u} [CommRing R] [IsDomain R]
    {ι : Type v} [Fintype ι] (f : ι → R)
    (hunit : Ideal.span (Set.range f) = ⊤)
    (hdom : ∀ i, IsDomain (Localization.Away (f i)))
    (hloc : ∀ i,
      @IsJapaneseDomain (Localization.Away (f i)) _ (hdom i)) :
    IsJapaneseDomain R := by
  sorry

theorem isJapaneseDomain_of_quasiFinite
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (f : R →+* S)
    (hinj : Function.Injective f) (hf : RingHom.QuasiFinite f)
    (hR : IsNoetherianRing R) (hJ : IsJapaneseDomain R) :
    IsJapaneseDomain S := by
  sorry

theorem isNOne_of_laurentPolynomial
    {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R]
    (h : IsNOne (LaurentPolynomial R)) : IsNOne R := by
  sorry

theorem isNOne_of_finite_extension
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (f : R →+* S)
    (hinj : Function.Injective f) (hf : RingHom.Finite f)
    (hR : IsNoetherianRing R) (hS : IsNOne S) : IsNOne R := by
  sorry

theorem isJapaneseDomain_of_finite_extension
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (f : R →+* S)
    (hinj : Function.Injective f) (hf : RingHom.Finite f)
    (hR : IsNoetherianRing R) (hS : IsJapaneseDomain S) :
    IsJapaneseDomain R := by
  sorry

/-! ## Separable and purely inseparable extensions -/

theorem integralClosure_finite_of_finite_separable_extension
    {R K L : Type u} [CommRing R] [IsDomain R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    (hR : IsNoetherianRing R) (hnormal : IsNormalDomain R) :
    letI : Algebra R L :=
      ((algebraMap K L).comp (algebraMap R K)).toAlgebra
    Module.Finite R (integralClosure R L) := by
  sorry

def signChange : MvPolynomial ℕ ℂ →+* MvPolynomial ℕ ℂ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* MvPolynomial ℕ ℂ)
    (fun i => -MvPolynomial.X i)

theorem signChange_X (i : ℕ) : signChange (MvPolynomial.X i) = -MvPolynomial.X i := by
  sorry

theorem signChange_involutive :
    signChange.comp signChange = RingHom.id (MvPolynomial ℕ ℂ) := by
  sorry

def signInvariantSubalgebra : Subalgebra ℂ (MvPolynomial ℕ ℂ) :=
  Algebra.adjoin ℂ
    (Set.range (fun ij : ℕ × ℕ => MvPolynomial.X ij.1 * MvPolynomial.X ij.2))

theorem signInvariantSubalgebra_eq_fixed :
    ∀ x : MvPolynomial ℕ ℂ,
      x ∈ signInvariantSubalgebra ↔ signChange x = x := by
  sorry

theorem bad_sign_invariant_example :
    IsNormalRing (signInvariantSubalgebra : Type) ∧
      ¬ Module.Finite (signInvariantSubalgebra : Type)
        (MvPolynomial ℕ ℂ) := by
  sorry

theorem bad_sign_invariant_integral_closure :
    ((integralClosure (signInvariantSubalgebra : Type)
        (FractionRing (MvPolynomial ℕ ℂ))) : Set (FractionRing (MvPolynomial ℕ ℂ))) =
      Set.range (algebraMap (MvPolynomial ℕ ℂ)
        (FractionRing (MvPolynomial ℕ ℂ))) := by
  sorry

theorem integralClosure_finite_of_derivation
    {R K L : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Module.Finite K L]
    (p : ℕ) [CharP K p] (hp : 0 < p) (a : R)
    (D : Derivation R R R) (hD : D a ≠ 0) (x : L)
    (hx : x ^ p = algebraMap K L (algebraMap R K a))
    (hnormal : IsNormalDomain R) :
    letI : Algebra R L :=
      ((algebraMap K L).comp (algebraMap R K)).toAlgebra
    Module.Finite R (integralClosure R L) := by
  sorry

theorem isNOne_iff_isJapaneseDomain_of_charZero
    {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K] :
    IsNOne R ↔ IsJapaneseDomain R := by
  sorry

theorem isJapaneseDomain_iff_purelyInseparable
    {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [CharP K p] (hp : 0 < p) :
    IsJapaneseDomain R ↔
      ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L],
        IsPurelyInseparable K L →
          letI : Algebra R L :=
            ((algebraMap K L).comp (algebraMap R K)).toAlgebra
          Module.Finite R (integralClosure R L) := by
  sorry

/-! ## Polynomial rings and the normal locus -/

theorem isNOne_polynomial
    {R : Type u} [CommRing R] [IsDomain R]
    (hR : IsNoetherianRing R) (hN : IsNOne R) :
    IsNOne (Polynomial R) := by
  sorry

theorem isJapaneseDomain_polynomial
    {R : Type u} [CommRing R] [IsDomain R]
    (hR : IsNoetherianRing R) (hJ : IsJapaneseDomain R) :
    IsJapaneseDomain (Polynomial R) := by
  sorry

def normalLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  {p | IsNormalDomain (Localization.AtPrime p.asIdeal)}

theorem isOpen_normalLocus_of_normal_localization
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (f : R) (hf : f ≠ 0)
    (hnormal : IsNormalRing (Localization.Away f)) :
    IsOpen (normalLocus R) := by
  sorry

theorem isNOne_iff_exists_normal_localization
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    IsNOne R ↔
      (∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f)) ∧
        ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal →
          IsNOne (Localization.AtPrime p.asIdeal) := by
  sorry

/-! ## Tate's lemma and formal power series -/

theorem isJapaneseDomain_of_adic_complete
    {R : Type u} [CommRing R] (x : R)
    [IsDomain R] [IsNoetherianRing R]
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))]
    [IsAdicComplete (Ideal.span ({x} : Set R)) R]
    (hnormal : IsNormalRing R)
    (hquot : IsJapaneseDomain (R ⧸ Ideal.span ({x} : Set R))) :
    IsJapaneseDomain R := by
  sorry

theorem isJapaneseDomain_powerSeries
    {R : Type u} [CommRing R] [IsDomain R]
    (hR : IsNoetherianRing R) (hJ : IsJapaneseDomain R) :
    IsJapaneseDomain (PowerSeries R) := by
  sorry

end

end Formalization.Books.Algebra.Unit161
