import Formalization.Books.Chow.Unit02
import Formalization.Books.Algebra.Unit103.CohenMacaulayModules
import Formalization.Books.Algebra.Unit121.OrdersOfVanishing

/-!
# Chow Homology and Chern Classes, Chapter 3: Calculation of some multiplicities

This file records the definitions and theorem interfaces in the chapter's
single source section.  Lengths are represented by the natural part of
Mathlib's extended-natural module length; the hypotheses in the source are
the hypotheses under which these values are finite.
-/

noncomputable section

open Set
open scoped BigOperators
open CategoryTheory

universe u v

namespace Formalization.Books.Chow.Unit03

open Formalization.Books.Algebra.Unit103
open Formalization.Books.Algebra.Unit121
open Formalization.Books.Chow.Unit02

/-! ## Support and scalar-multiplication interfaces -/

/-- The minimal points of the support of a module. -/
def minimalSupport
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] : Set (PrimeSpectrum R) :=
  {p | p ∈ Module.support R M ∧
    ∀ q : PrimeSpectrum R, q ∈ Module.support R M → q ≤ p → p = q}

/-- The minimal prime points lying over an ideal. -/
def minimalPrimesOver
    (R : Type u) [CommRing R] (I : Ideal R) : Set (PrimeSpectrum R) :=
  {p | I ≤ p.asIdeal ∧
    ∀ q : PrimeSpectrum R, I ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal → p = q}

/-- The order term occurring at a one-dimensional prime component. -/
def orderAtPrime
    (R : Type u) [CommRing R] (x : R) (q : PrimeSpectrum R) : ℕ :=
  principalQuotientLength (R ⧸ q.asIdeal)
    (Ideal.Quotient.mk q.asIdeal x)

/-- Multiplication by a ring element, regarded as an endomorphism of a module. -/
def scalarMap
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (x : R) : M →ₗ[R] M :=
  { toFun := fun m => x • m
    map_add' := by
      intro m n
      simp [smul_add]
    map_smul' := by
      intro r m
      simp [smul_smul, mul_comm] }

/-- The same scalar multiplication map in `ModuleCat`. -/
def scalarEndomorphism
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) (x : R) : M ⟶ M :=
  ModuleCat.ofHom (scalarMap (R := R) (M := (M : Type v)) x)

theorem scalarEndomorphism_commutes
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) (x : R)
    (f : M ⟶ M) :
    f ≫ scalarEndomorphism M x = scalarEndomorphism M x ≫ f := by
  apply ModuleCat.hom_ext_iff.mpr
  ext m
  simp only [ModuleCat.comp_apply]
  change x • f.hom m = f.hom (x • m)
  exact (f.hom.map_smul x m).symm

/-- The `(2, 1)`-periodic complex `(M, 0, x)` from the source. -/
def scalarPeriodicComplex
    (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (x : R) :
    TwoOnePeriodicComplex R :=
  TwoOnePeriodicComplex.zeroFirst (ModuleCat.of R M)
    (ModuleCat.ofHom (scalarMap (R := R) (M := M) x))

/-- A periodic complex made from two composable endomorphisms. -/
def periodicComplexOfLinearMaps
    (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M)
    (hφψ : ψ.comp φ = 0) (hψφ : φ.comp ψ = 0) :
    TwoOnePeriodicComplex R where
  M := ModuleCat.of R M
  phi := ModuleCat.ofHom φ
  psi := ModuleCat.ofHom ψ
  phi_psi := by
    apply ModuleCat.hom_ext_iff.mpr
    exact hφψ
  psi_phi := by
    apply ModuleCat.hom_ext_iff.mpr
    exact hψφ

/-- Multiplication of the first differential by a scalar. -/
def scalePhi
    {R : Type u} [CommRing R] {C : TwoOnePeriodicComplex R} (x : R) :
    TwoOnePeriodicComplex R where
  M := C.M
  phi := scalarEndomorphism C.M x ≫ C.phi
  psi := C.psi
  phi_psi := by
    simp [Category.assoc, C.phi_psi]
  psi_phi := by
    rw [← Category.assoc, scalarEndomorphism_commutes C.M x C.psi,
      Category.assoc, C.psi_phi]
    simp

/-- Multiplication of the second differential by a scalar. -/
def scalePsi
    {R : Type u} [CommRing R] {C : TwoOnePeriodicComplex R} (x : R) :
    TwoOnePeriodicComplex R where
  M := C.M
  phi := C.phi
  psi := scalarEndomorphism C.M x ≫ C.psi
  phi_psi := by
    rw [← Category.assoc, scalarEndomorphism_commutes C.M x C.phi,
      Category.assoc, C.phi_psi]
    simp
  psi_phi := by
    simp [Category.assoc, C.psi_phi]

/-! ## Length under multiplication -/

theorem length_multiplication
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R)
    (hMdim : Module.supportDim R M ≤ 1)
    (hquotdim : Module.supportDim R (QuotSMulTop x M) ≤ 0)
    (t : ℕ) (q : Fin t → PrimeSpectrum R)
    (hsupport : Module.support R M =
      insert (IsLocalRing.closedPoint R) (Set.range q))
    (hq_injective : Function.Injective q)
    (hqclosed : ∀ i, q i ≠ IsLocalRing.closedPoint R)
    (hC : (scalarPeriodicComplex R M x).HasFiniteLengthCohomology) :
    (scalarPeriodicComplex R M x).multiplicity hC =
      ∑ i : Fin t,
        (orderAtPrime R x (q i) : ℤ) *
          (Module.length (Localization.AtPrime (q i).asIdeal)
            (LocalizedModule.AtPrime (q i).asIdeal M)).toNat := by
  sorry

/-! ## Additivity for restricted divisors -/

theorem additivity_divisor_restricted_cmh
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hM : IsCohenMacaulay R M)
    (hdimM : Module.supportDim R M = 1)
    (hdimquot : Module.supportDim R (QuotSMulTop x M) = 0)
    (t : ℕ) (q : Fin t → PrimeSpectrum R)
    (hq_injective : Function.Injective q)
    (hminimal : Set.range q = minimalSupport R M) :
    (Module.length R (QuotSMulTop x M)).toNat =
      ∑ i : Fin t,
        (Module.length R
          (R ⧸ (Ideal.span ({x} : Set R) ⊔ (q i).asIdeal))).toNat *
          (Module.length (Localization.AtPrime (q i).asIdeal)
            (LocalizedModule.AtPrime (q i).asIdeal M)).toNat := by
  sorry

theorem additivity_divisor_restricted_ideal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (x : R)
    (hx : Function.Injective
      (fun y : R ⧸ I => Ideal.Quotient.mk I x * y))
    (hdim : ringKrullDim (R ⧸ I) = 1)
    (t : ℕ) (q : Fin t → PrimeSpectrum R)
    (hq_injective : Function.Injective q)
    (hminimal : Set.range q = minimalPrimesOver R I) :
    (Module.length R
      (R ⧸ (Ideal.span ({x} : Set R) ⊔ I))).toNat =
      ∑ i : Fin t,
        (Module.length R
          (R ⧸ (Ideal.span ({x} : Set R) ⊔ (q i).asIdeal))).toNat *
          (Module.length (Localization.AtPrime (q i).asIdeal)
            (LocalizedModule.AtPrime (q i).asIdeal (R ⧸ I))).toNat := by
  sorry

/-! ## Nilpotent powers -/

/-- Iterated composition of a linear endomorphism. -/
def linearMapPow
    {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] M) : ℕ → M →ₗ[R] M
  | 0 => LinearMap.id
  | n + 1 => φ.comp (linearMapPow φ n)

theorem linearMapPow_comp
    {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] M) (a b : ℕ) :
    (linearMapPow φ a).comp (linearMapPow φ b) = linearMapPow φ (a + b) := by
  sorry

/-- The periodic complex formed by complementary powers of a nilpotent map. -/
def powerPeriodicComplex
    {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] M)
    (n i : ℕ) (hi : i ≤ n) (hzero : linearMapPow φ n = 0) :
    TwoOnePeriodicComplex R :=
  periodicComplexOfLinearMaps R M (linearMapPow φ i)
    (linearMapPow φ (n - i))
    (by
      rw [linearMapPow_comp, Nat.sub_add_cancel hi, hzero])
    (by
      rw [linearMapPow_comp, Nat.add_sub_of_le hi, hzero])

theorem powers_period_length_zero
    {R : Type u} [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] M) (n : ℕ) (hn : 0 < n)
    (hzero : linearMapPow φ n = 0)
    (hfinite : IsFiniteLength R
      (LinearMap.ker φ ⧸
        Submodule.comap (LinearMap.ker φ).subtype
          (LinearMap.range (linearMapPow φ (n - 1)))))
    (hC : ∀ (i : Fin (n + 1)),
      (powerPeriodicComplex φ n i.1 i.is_le hzero).HasFiniteLengthCohomology) :
    ∀ i : Fin (n + 1),
      (powerPeriodicComplex φ n i.1 i.is_le hzero).multiplicity (hC i) = 0 := by
  sorry

/-! ## Multiplying a periodic complex by a scalar -/

theorem multiply_period_length_first
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (C : TwoOnePeriodicComplex R) [Module.Finite R C.M]
    (hC : C.HasFiniteLengthCohomology) (x : R)
    (hquotdim : Module.supportDim R (QuotSMulTop x (C.M : Type v)) ≤ 0)
    (hscaled : (scalePhi (C := C) x).HasFiniteLengthCohomology)
    (himage :
      (scalarPeriodicComplex R (LinearMap.range C.phi.hom) x).HasFiniteLengthCohomology) :
    (scalePhi (C := C) x).multiplicity hscaled =
      C.multiplicity hC -
        (scalarPeriodicComplex R (LinearMap.range C.phi.hom) x).multiplicity himage := by
  sorry

theorem multiply_period_length_second
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (C : TwoOnePeriodicComplex R) [Module.Finite R C.M]
    (hC : C.HasFiniteLengthCohomology) (x : R)
    (hquotdim : Module.supportDim R (QuotSMulTop x (C.M : Type v)) ≤ 0)
    (hscaled : (scalePsi (C := C) x).HasFiniteLengthCohomology)
    (himage :
      (scalarPeriodicComplex R (LinearMap.range C.psi.hom) x).HasFiniteLengthCohomology) :
    (scalePsi (C := C) x).multiplicity hscaled =
      C.multiplicity hC +
        (scalarPeriodicComplex R (LinearMap.range C.psi.hom) x).multiplicity himage := by
  sorry

end Formalization.Books.Chow.Unit03
