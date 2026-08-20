import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Basic
import Formalization.Books.Algebra.Unit69.QuasiRegularSequences
import Formalization.Books.Algebra.Unit119.AroundKrullAkizuki
import Formalization.Books.Examples.Unit12.NonflatCompletions

/-!
# Another local ring with nonreduced completion

This file formalizes the precise statements in Section 18 of
`books/examples.tex`.  The constructions use the existing Mathlib power-series,
localization, and adic-completion APIs; proposition proofs are left for the
proving stage.
-/

namespace Formalization.Books.Examples.Unit18

noncomputable section

universe u

section CoefficientFields

variable (k : Type u) (p : ℕ) [Field k] [Fact p.Prime] [CharP k p]

/-- Chapter 18's name for the established Frobenius subfield interface. -/
abbrev pPowerSubfield : Subfield k :=
  Formalization.Books.Algebra.Unit119.pPowerSubfield k p

/-- Chapter 18's name for the established finite-degree coefficient condition. -/
abbrev FiniteDegreeOverPowers (s : Set k) : Prop :=
  Formalization.Books.Algebra.Unit119.finiteDegreeOverPowers k p s

/-- The hypothesis that `k` has infinite degree over its `p`th-power field. -/
def InfiniteDegreeOverPowers : Prop :=
  ¬ Module.Finite (pPowerSubfield k p) k

/-- Chapter 18's name for the established one-variable coefficient condition. -/
abbrev OneVariableFiniteDegree (f : PowerSeries k) : Prop :=
  Formalization.Books.Algebra.Unit119.badDvrCoefficientCondition k p f

theorem oneVariableFiniteDegree_zero :
    OneVariableFiniteDegree k p 0 := by
  refine ⟨⊥, ?_, inferInstance⟩
  rintro x ⟨i, rfl⟩
  simp

theorem oneVariableFiniteDegree_one :
    OneVariableFiniteDegree k p 1 := by
  refine ⟨⊥, ?_, inferInstance⟩
  rintro x ⟨i, rfl⟩
  by_cases hi : i = 0 <;> simp [hi]

theorem oneVariableFiniteDegree_add {f g : PowerSeries k}
    (hf : OneVariableFiniteDegree k p f)
    (hg : OneVariableFiniteDegree k p g) :
    OneVariableFiniteDegree k p (f + g) := by
  unfold OneVariableFiniteDegree at *
  rcases hf with ⟨F, hF, hFfin⟩
  rcases hg with ⟨G, hG, hGfin⟩
  refine ⟨F ⊔ G, ?_, inferInstance⟩
  rintro x ⟨i, rfl⟩
  have hfi : PowerSeries.coeff i f ∈ (F ⊔ G : IntermediateField (pPowerSubfield k p) k) :=
    (le_sup_left : F ≤ F ⊔ G) (hF ⟨i, rfl⟩)
  have hgi : PowerSeries.coeff i g ∈ (F ⊔ G : IntermediateField (pPowerSubfield k p) k) :=
    (le_sup_right : G ≤ F ⊔ G) (hG ⟨i, rfl⟩)
  change PowerSeries.coeff i f + PowerSeries.coeff i g ∈ F ⊔ G
  simpa only [map_add] using add_mem hfi hgi

theorem oneVariableFiniteDegree_mul {f g : PowerSeries k}
    (hf : OneVariableFiniteDegree k p f)
    (hg : OneVariableFiniteDegree k p g) :
    OneVariableFiniteDegree k p (f * g) := by
  unfold OneVariableFiniteDegree at *
  rcases hf with ⟨F, hF, hFfin⟩
  rcases hg with ⟨G, hG, hGfin⟩
  refine ⟨F ⊔ G, ?_, inferInstance⟩
  rintro x ⟨i, rfl⟩
  change PowerSeries.coeff i (f * g) ∈ F ⊔ G
  rw [PowerSeries.coeff_mul]
  apply (F ⊔ G).sum_mem
  intro q hq
  exact mul_mem
    ((le_sup_left : F ≤ F ⊔ G) (hF ⟨q.1, rfl⟩))
    ((le_sup_right : G ≤ F ⊔ G) (hG ⟨q.2, rfl⟩))

theorem oneVariableFiniteDegree_neg {f : PowerSeries k}
    (hf : OneVariableFiniteDegree k p f) :
    OneVariableFiniteDegree k p (-f) := by
  unfold OneVariableFiniteDegree at *
  rcases hf with ⟨F, hF, hFfin⟩
  refine ⟨F, ?_, hFfin⟩
  rintro x ⟨i, rfl⟩
  change PowerSeries.coeff i (-f) ∈ F
  rw [map_neg]
  exact F.neg_mem (hF ⟨i, rfl⟩)

/-- The subring of one-variable series whose coefficients lie in a finite
extension of `k ^ p`. -/
def badDvrSubring : Subring (PowerSeries k) where
  carrier := {f | OneVariableFiniteDegree k p f}
  zero_mem' := by
    exact oneVariableFiniteDegree_zero k p
  add_mem' := by
    intro f g hf hg
    exact oneVariableFiniteDegree_add k p hf hg
  one_mem' := by
    exact oneVariableFiniteDegree_one k p
  mul_mem' := by
    intro f g hf hg
    exact oneVariableFiniteDegree_mul k p hf hg
  neg_mem' := by
    intro f hf
    exact oneVariableFiniteDegree_neg k p hf

/-- The one-variable coefficient ring used in the fiber product. -/
abbrev badDvrRing := ↥(badDvrSubring k p)

/-- The residue map given by the constant coefficient. -/
def badDvrConstantCoeff : badDvrRing k p →+* k :=
  (PowerSeries.constantCoeff).comp (badDvrSubring k p).subtype

theorem oneVariableFiniteDegree_X :
    OneVariableFiniteDegree k p PowerSeries.X := by
  unfold OneVariableFiniteDegree
  refine ⟨⊥, ?_, inferInstance⟩
  rintro x ⟨i, rfl⟩
  by_cases hi : i = 1
  · simp [PowerSeries.coeff_X, hi]
  · simp [PowerSeries.coeff_X, hi]

/-- The image of the variable in the bad one-variable subring. -/
def badDvrVariable : badDvrRing k p :=
  ⟨PowerSeries.X, oneVariableFiniteDegree_X k p⟩

private theorem oneVariableFiniteDegree_isUnit_of_constantCoeff_ne_zero
    {f : PowerSeries k} (hf : OneVariableFiniteDegree k p f)
    (hc : PowerSeries.constantCoeff f ≠ 0) :
    IsUnit (⟨f, hf⟩ : badDvrRing k p) := by
  unfold OneVariableFiniteDegree at hf
  rcases hf with ⟨F, hF, hFfin⟩
  let fF : PowerSeries F :=
    PowerSeries.mk (fun i => ⟨PowerSeries.coeff i f, hF ⟨i, rfl⟩⟩)
  have hmap : PowerSeries.map F.val.toRingHom fF = f := by
    ext i
    simp [fF]
  have hconstF : PowerSeries.constantCoeff fF ≠ 0 := by
    intro hzero
    apply hc
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hzero ⊢
    rw [← hmap, PowerSeries.coeff_map]
    exact congrArg (fun a : F => (a : k)) hzero
  let g : PowerSeries k := PowerSeries.map F.val.toRingHom (fF⁻¹)
  have hg : OneVariableFiniteDegree k p g := by
    unfold OneVariableFiniteDegree
    refine ⟨F, ?_, hFfin⟩
    rintro x ⟨i, rfl⟩
    change PowerSeries.coeff i (PowerSeries.map F.val.toRingHom (fF⁻¹)) ∈ F
    rw [PowerSeries.coeff_map]
    exact (PowerSeries.coeff i (fF⁻¹)).property
  have hfg : f * g = 1 := by
    have hprod := congrArg (PowerSeries.map F.val.toRingHom)
      (PowerSeries.mul_inv_cancel fF hconstF)
    simp only [map_mul] at hprod
    rw [hmap] at hprod
    simpa only [g, map_one] using hprod
  let u : (badDvrRing k p)ˣ :=
    { val := ⟨f, ⟨F, hF, hFfin⟩⟩
      inv := ⟨g, hg⟩
      val_inv := by
        apply Subtype.ext
        exact hfg
      inv_val := by
        apply Subtype.ext
        simpa [mul_comm] using hfg }
  exact ⟨u, rfl⟩

private theorem oneVariableFiniteDegree_shift {f : PowerSeries k}
    (hf : OneVariableFiniteDegree k p f) :
    OneVariableFiniteDegree k p (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) f) := by
  unfold OneVariableFiniteDegree at *
  rcases hf with ⟨F, hF, hFfin⟩
  refine ⟨F, ?_, hFfin⟩
  rintro x ⟨i, rfl⟩
  change PowerSeries.coeff i (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) f) ∈ F
  simp only [PowerSeries.coeff_mk]
  exact hF ⟨i + 1, rfl⟩

private theorem oneVariableFiniteDegree_divXPowOrder {f : PowerSeries k}
    (hf : OneVariableFiniteDegree k p f) :
    OneVariableFiniteDegree k p (PowerSeries.divXPowOrder f) := by
  unfold OneVariableFiniteDegree at *
  rcases hf with ⟨F, hF, hFfin⟩
  refine ⟨F, ?_, hFfin⟩
  rintro x ⟨i, rfl⟩
  change PowerSeries.coeff i (PowerSeries.divXPowOrder f) ∈ F
  rw [PowerSeries.coeff_divXPowOrder]
  exact hF ⟨i + f.order.toNat, rfl⟩

theorem badDvrRing_isDiscreteValuationRing :
    IsDiscreteValuationRing (badDvrRing k p) := by
  have hprime : Prime (badDvrVariable k p) := by
    refine ⟨?_, ?_, ?_⟩
    · intro hzero
      apply (PowerSeries.X_ne_zero (R := k))
      simpa [badDvrVariable] using congrArg Subtype.val hzero
    · intro hu
      apply (PowerSeries.X_irreducible (R := k)).not_isUnit
      simpa [badDvrVariable] using hu.map (badDvrSubring k p).subtype
    · intro a b hab
      have hab' : (PowerSeries.X : PowerSeries k) ∣ (a : PowerSeries k) * (b : PowerSeries k) := by
        rcases hab with ⟨c, hc⟩
        refine ⟨(c : PowerSeries k), ?_⟩
        exact congrArg Subtype.val hc
      rcases PowerSeries.X_prime.dvd_or_dvd hab' with ha | hb
      · left
        rw [PowerSeries.X_dvd_iff] at ha
        let s : PowerSeries k := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (a : PowerSeries k)
        have hs : OneVariableFiniteDegree k p s := by
          dsimp [s]
          exact oneVariableFiniteDegree_shift k p a.property
        have hs' : s ∈ badDvrSubring k p := by
          change OneVariableFiniteDegree k p s
          exact hs
        refine ⟨⟨s, hs'⟩, ?_⟩
        apply Subtype.ext
        rw [PowerSeries.eq_shift_mul_X_add_const (a : PowerSeries k), ha]
        simp [s, badDvrVariable, mul_comm]
      · right
        rw [PowerSeries.X_dvd_iff] at hb
        let s : PowerSeries k := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (b : PowerSeries k)
        have hs : OneVariableFiniteDegree k p s := by
          dsimp [s]
          exact oneVariableFiniteDegree_shift k p b.property
        have hs' : s ∈ badDvrSubring k p := by
          change OneVariableFiniteDegree k p s
          exact hs
        refine ⟨⟨s, hs'⟩, ?_⟩
        apply Subtype.ext
        rw [PowerSeries.eq_shift_mul_X_add_const (b : PowerSeries k), hb]
        simp [s, badDvrVariable, mul_comm]
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨badDvrVariable k p, hprime.irreducible, ?_⟩
  intro x hx
  have hfx : (x : PowerSeries k) ≠ 0 := by
    intro hzero
    apply hx
    exact Subtype.ext hzero
  have hdiv : OneVariableFiniteDegree k p
      (PowerSeries.divXPowOrder (x : PowerSeries k)) :=
    oneVariableFiniteDegree_divXPowOrder k p x.property
  have hconst : PowerSeries.constantCoeff (PowerSeries.divXPowOrder (x : PowerSeries k)) ≠ 0 :=
    (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff).not.mpr hfx
  obtain ⟨u, hu⟩ := oneVariableFiniteDegree_isUnit_of_constantCoeff_ne_zero k p hdiv hconst
  refine ⟨(x : PowerSeries k).order.toNat, ?_⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  have hu' := congrArg Subtype.val hu
  change PowerSeries.X ^ (x : PowerSeries k).order.toNat * (u : PowerSeries k) = (x : PowerSeries k)
  rw [hu']
  exact PowerSeries.X_pow_order_mul_divXPowOrder

def pPowerSeriesSubring1 : Subring (PowerSeries k) :=
  (PowerSeries.map (pPowerSubfield k p).subtype).range

theorem pPowerSeriesSubring1_le_badDvrSubring :
    pPowerSeriesSubring1 k p ≤ badDvrSubring k p := by
  intro f hf
  rcases hf with ⟨g, rfl⟩
  unfold badDvrSubring OneVariableFiniteDegree
  refine ⟨⊥, ?_, inferInstance⟩
  rintro x ⟨i, rfl⟩
  change PowerSeries.coeff i (PowerSeries.map (pPowerSubfield k p).subtype g) ∈
    (⊥ : IntermediateField (pPowerSubfield k p) k)
  rw [PowerSeries.coeff_map]
  apply IntermediateField.mem_bot.mpr
  exact ⟨PowerSeries.coeff i g, rfl⟩

theorem badDvrSubring_le_ambient :
    badDvrSubring k p ≤ ⊤ := by
  exact le_top

abbrev cSubring := badDvrSubring
abbrev dSubring := badDvrSubring
abbrev cRing := badDvrRing
abbrev dRing := badDvrRing
abbrev cConstantCoeff := badDvrConstantCoeff
abbrev dConstantCoeff := badDvrConstantCoeff

theorem cRing_isDiscreteValuationRing :
    IsDiscreteValuationRing (cRing k p) := by
  exact badDvrRing_isDiscreteValuationRing k p

theorem dRing_isDiscreteValuationRing :
    IsDiscreteValuationRing (dRing k p) := by
  exact badDvrRing_isDiscreteValuationRing k p

end CoefficientFields

/-- A concrete field with countably many algebraically independent variables
over `𝔽_p`, as in the example in the text. -/
abbrev FpTranscendentalField (p : ℕ) [Fact p.Prime] :=
  FractionRing (MvPolynomial ℕ (ZMod p))

theorem FpTranscendentalField_infiniteDegree (p : ℕ) [Fact p.Prime] :
    InfiniteDegreeOverPowers (FpTranscendentalField p) p := by
  intro hfinite
  let hli₀ : LinearIndependent (MvPolynomial ℕ (ZMod p))
      (KaehlerDifferential.mvPolynomialBasis (ZMod p) ℕ) :=
    (KaehlerDifferential.mvPolynomialBasis (ZMod p) ℕ).linearIndependent
  let hli₁ : LinearIndependent (FpTranscendentalField p)
      (fun i : ℕ => KaehlerDifferential.D (ZMod p) (FpTranscendentalField p)
        (algebraMap (MvPolynomial ℕ (ZMod p)) (FpTranscendentalField p)
          (MvPolynomial.X i))) := by
    let f := KaehlerDifferential.map (ZMod p) (ZMod p)
      (MvPolynomial ℕ (ZMod p)) (FpTranscendentalField p)
    have h := hli₀.of_isLocalizedModule (FpTranscendentalField p)
      (nonZeroDivisors (MvPolynomial ℕ (ZMod p))) f
    have heq :
        (fun i : ℕ => KaehlerDifferential.D (ZMod p) (FpTranscendentalField p)
          (algebraMap (MvPolynomial ℕ (ZMod p)) (FpTranscendentalField p)
            (MvPolynomial.X i))) =
        (fun i : ℕ => f ((KaehlerDifferential.mvPolynomialBasis (ZMod p) ℕ) i)) := by
      funext i
      dsimp [f]
      rw [KaehlerDifferential.mvPolynomialBasis_apply,
        KaehlerDifferential.map_D (ZMod p) (ZMod p)
          (MvPolynomial ℕ (ZMod p)) (FpTranscendentalField p)]
    rw [heq]
    exact h
  let dlin : FpTranscendentalField p →ₗ[pPowerSubfield (FpTranscendentalField p) p]
      KaehlerDifferential (ZMod p) (FpTranscendentalField p) := by
    refine
      { toFun := KaehlerDifferential.D (ZMod p) (FpTranscendentalField p)
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      exact (KaehlerDifferential.D (ZMod p) (FpTranscendentalField p)).map_add x y
    · intro c x
      obtain ⟨y, hy⟩ := (RingHom.mem_fieldRange).mp c.property
      have hy' : y ^ p = (c : FpTranscendentalField p) := by
        change y ^ p = (c : FpTranscendentalField p) at hy
        exact hy
      have hcy : KaehlerDifferential.D (ZMod p) (FpTranscendentalField p)
          (c : FpTranscendentalField p) = 0 := by
        rw [← hy', (KaehlerDifferential.D (ZMod p) (FpTranscendentalField p)).leibniz_pow]
        rw [← Nat.cast_smul_eq_nsmul (FpTranscendentalField p),
          CharP.cast_eq_zero (FpTranscendentalField p) p]
        simp
      change KaehlerDifferential.D (ZMod p) (FpTranscendentalField p)
          ((c : FpTranscendentalField p) * x) =
        (c : FpTranscendentalField p) •
          KaehlerDifferential.D (ZMod p) (FpTranscendentalField p) x
      rw [(KaehlerDifferential.D (ZMod p) (FpTranscendentalField p)).leibniz,
        hcy]
      simp
  let d : Derivation (pPowerSubfield (FpTranscendentalField p) p)
      (FpTranscendentalField p)
      (KaehlerDifferential (ZMod p) (FpTranscendentalField p)) :=
    Derivation.mk' dlin (by
      intro x y
      exact (KaehlerDifferential.D (ZMod p) (FpTranscendentalField p)).leibniz x y)
  let φ := d.liftKaehlerDifferential
  have hliF : LinearIndependent (FpTranscendentalField p)
      (fun i : ℕ => KaehlerDifferential.D (pPowerSubfield (FpTranscendentalField p) p)
        (FpTranscendentalField p)
        (algebraMap (MvPolynomial ℕ (ZMod p)) (FpTranscendentalField p)
          (MvPolynomial.X i))) := by
    apply LinearIndependent.of_comp φ
    have heq :
        (fun i : ℕ => φ
          (KaehlerDifferential.D (pPowerSubfield (FpTranscendentalField p) p)
            (FpTranscendentalField p)
            (algebraMap (MvPolynomial ℕ (ZMod p)) (FpTranscendentalField p)
              (MvPolynomial.X i)))) =
        (fun i : ℕ => KaehlerDifferential.D (ZMod p) (FpTranscendentalField p)
          (algebraMap (MvPolynomial ℕ (ZMod p)) (FpTranscendentalField p)
              (MvPolynomial.X i))) := by
      funext i
      dsimp [φ]
      rw [Derivation.liftKaehlerDifferential_comp_D]
      rfl
    change LinearIndependent (FpTranscendentalField p) (fun i : ℕ => φ
      (KaehlerDifferential.D (pPowerSubfield (FpTranscendentalField p) p)
        (FpTranscendentalField p)
        (algebraMap (MvPolynomial ℕ (ZMod p)) (FpTranscendentalField p)
          (MvPolynomial.X i))))
    rw [heq]
    exact hli₁
  let hfiniteType : Algebra.FiniteType (pPowerSubfield (FpTranscendentalField p) p)
      (FpTranscendentalField p) :=
    ⟨Subalgebra.fg_of_submodule_fg hfinite.1⟩
  let hess : Algebra.EssFiniteType (pPowerSubfield (FpTranscendentalField p) p)
      (FpTranscendentalField p) :=
    @Algebra.EssFiniteType.of_finiteType
      (pPowerSubfield (FpTranscendentalField p) p) (FpTranscendentalField p)
      _ _ _ hfiniteType
  let hfiniteOmega : Module.Finite (FpTranscendentalField p)
      (KaehlerDifferential (pPowerSubfield (FpTranscendentalField p) p)
        (FpTranscendentalField p)) :=
    @KaehlerDifferential.finite
      (pPowerSubfield (FpTranscendentalField p) p) (FpTranscendentalField p)
      _ _ _ hess
  exact (@Module.Finite.not_linearIndependent_of_infinite
    (R := FpTranscendentalField p)
    (M := KaehlerDifferential (pPowerSubfield (FpTranscendentalField p) p)
      (FpTranscendentalField p)) _ _ _ hfiniteOmega _ (ι := ℕ) _
    (fun i : ℕ => KaehlerDifferential.D (pPowerSubfield (FpTranscendentalField p) p)
      (FpTranscendentalField p)
      (algebraMap (MvPolynomial ℕ (ZMod p)) (FpTranscendentalField p)
        (MvPolynomial.X i))) hliF)

section TwoVariableSeries

variable (k : Type u) (p : ℕ) [Field k] [Fact p.Prime] [CharP k p]

abbrev TwoVariablePowerSeries := MvPowerSeries (Fin 2) k

/-- The coefficient of `x ^ i * y ^ j` in a bivariate series. -/
def coefficientXY (f : TwoVariablePowerSeries k) (i j : ℕ) : k :=
  MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j) f

/-- The diagonal block of exponents at distance `n` from the diagonal. -/
def diagonalSlice (n : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {d | (d 0 = n ∧ n ≤ d 1) ∨ (d 1 = n ∧ n ≤ d 0)}

/-- The coefficients appearing in the `n`th diagonal block. -/
def diagonalCoefficients (f : TwoVariablePowerSeries k) (n : ℕ) : Set k :=
  {a | ∃ d, d ∈ diagonalSlice n ∧ MvPowerSeries.coeff d f = a}

/-- The coefficient condition defining the bivariate subring `A`. -/
def ACondition (f : TwoVariablePowerSeries k) : Prop :=
  ∀ n : ℕ, FiniteDegreeOverPowers k p (diagonalCoefficients k f n)

theorem aCondition_zero :
    ACondition k p 0 := by
  intro n
  unfold FiniteDegreeOverPowers
  refine ⟨⊥, ?_, inferInstance⟩
  rintro a ⟨d, hd, rfl⟩
  change MvPowerSeries.coeff d (0 : TwoVariablePowerSeries k) ∈
    (⊥ : IntermediateField (pPowerSubfield k p) k)
  simp

theorem aCondition_one :
    ACondition k p 1 := by
  intro n
  unfold FiniteDegreeOverPowers
  refine ⟨⊥, ?_, inferInstance⟩
  rintro a ⟨d, hd, rfl⟩
  change MvPowerSeries.coeff d (1 : TwoVariablePowerSeries k) ∈
    (⊥ : IntermediateField (pPowerSubfield k p) k)
  by_cases hd0 : d = 0
  · subst d
    simp
  · rw [MvPowerSeries.coeff_one, if_neg hd0]
    exact (⊥ : IntermediateField (pPowerSubfield k p) k).zero_mem

theorem aCondition_add {f g : TwoVariablePowerSeries k}
    (hf : ACondition k p f) (hg : ACondition k p g) :
    ACondition k p (f + g) := by
  unfold ACondition at hf hg ⊢
  intro n
  unfold FiniteDegreeOverPowers at hf hg ⊢
  rcases hf n with ⟨F, hF, hFfin⟩
  rcases hg n with ⟨G, hG, hGfin⟩
  refine ⟨F ⊔ G, ?_, inferInstance⟩
  rintro a ⟨d, hd, rfl⟩
  have hfd : MvPowerSeries.coeff d f ∈ (F ⊔ G : IntermediateField (pPowerSubfield k p) k) :=
    (le_sup_left : F ≤ F ⊔ G) (hF ⟨d, hd, rfl⟩)
  have hgd : MvPowerSeries.coeff d g ∈ (F ⊔ G : IntermediateField (pPowerSubfield k p) k) :=
    (le_sup_right : G ≤ F ⊔ G) (hG ⟨d, hd, rfl⟩)
  change MvPowerSeries.coeff d f + MvPowerSeries.coeff d g ∈ F ⊔ G
  simpa only [map_add] using add_mem hfd hgd

theorem aCondition_mul {f g : TwoVariablePowerSeries k}
    (hf : ACondition k p f) (hg : ACondition k p g) :
    ACondition k p (f * g) := by
  unfold ACondition at hf hg ⊢
  intro n
  unfold FiniteDegreeOverPowers at hf hg ⊢
  have hfinite : ∀ r : ℕ, ∃ H : IntermediateField (pPowerSubfield k p) k,
      (∀ m ≤ r, diagonalCoefficients k f m ⊆ H) ∧
        (∀ m ≤ r, diagonalCoefficients k g m ⊆ H) ∧
          Module.Finite (pPowerSubfield k p) H := by
    intro r
    induction r with
    | zero =>
        rcases hf 0 with ⟨F, hF, hFfin⟩
        rcases hg 0 with ⟨G, hG, hGfin⟩
        refine ⟨F ⊔ G, ?_, ?_, inferInstance⟩
        · intro m hm
          have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
          subst m
          intro x hx
          exact (le_sup_left : F ≤ F ⊔ G) (hF hx)
        · intro m hm
          have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
          subst m
          intro x hx
          exact (le_sup_right : G ≤ F ⊔ G) (hG hx)
    | succ r ihr =>
        rcases ihr with ⟨H, hHf, hHg, hHfin⟩
        rcases hf (r + 1) with ⟨F, hF, hFfin⟩
        rcases hg (r + 1) with ⟨G, hG, hGfin⟩
        refine ⟨H ⊔ F ⊔ G, ?_, ?_, inferInstance⟩
        · intro m hm
          have hmr : m ≤ r ∨ m = r + 1 := by omega
          rcases hmr with hmr | rfl
          · have hHF : H ≤ H ⊔ F ⊔ G :=
              (le_sup_left : H ≤ H ⊔ F).trans
                (le_sup_left : H ⊔ F ≤ H ⊔ F ⊔ G)
            intro x hx
            exact hHF (hHf m hmr hx)
          · have hF' : F ≤ H ⊔ F ⊔ G :=
              (le_sup_right : F ≤ H ⊔ F).trans
                (le_sup_left : H ⊔ F ≤ H ⊔ F ⊔ G)
            intro x hx
            exact hF' (hF hx)
        · intro m hm
          have hmr : m ≤ r ∨ m = r + 1 := by omega
          rcases hmr with hmr | rfl
          · have hHF : H ≤ H ⊔ F ⊔ G :=
              (le_sup_left : H ≤ H ⊔ F).trans
                (le_sup_left : H ⊔ F ≤ H ⊔ F ⊔ G)
            intro x hx
            exact hHF (hHg m hmr hx)
          · intro x hx
            exact (le_sup_right : G ≤ H ⊔ F ⊔ G) (hG hx)
  rcases hfinite n with ⟨H, hHf, hHg, hHfin⟩
  refine ⟨H, ?_, hHfin⟩
  have hcoeff_f : ∀ e : Fin 2 →₀ ℕ, e 0 ≤ n ∨ e 1 ≤ n →
      MvPowerSeries.coeff e f ∈ H := by
    intro e he
    by_cases he01 : e 0 ≤ e 1
    · have he0 : e 0 ≤ n := by
        rcases he with he0 | he1
        · exact he0
        · exact he01.trans he1
      exact (hHf (e 0) he0) ⟨e, Or.inl ⟨rfl, he01⟩, rfl⟩
    · have he10 : e 1 ≤ e 0 := by omega
      have he1 : e 1 ≤ n := by
        rcases he with he0 | he1
        · exact he10.trans he0
        · exact he1
      exact (hHf (e 1) he1) ⟨e, Or.inr ⟨rfl, he10⟩, rfl⟩
  have hcoeff_g : ∀ e : Fin 2 →₀ ℕ, e 0 ≤ n ∨ e 1 ≤ n →
      MvPowerSeries.coeff e g ∈ H := by
    intro e he
    by_cases he01 : e 0 ≤ e 1
    · have he0 : e 0 ≤ n := by
        rcases he with he0 | he1
        · exact he0
        · exact he01.trans he1
      exact (hHg (e 0) he0) ⟨e, Or.inl ⟨rfl, he01⟩, rfl⟩
    · have he10 : e 1 ≤ e 0 := by omega
      have he1 : e 1 ≤ n := by
        rcases he with he0 | he1
        · exact he10.trans he0
        · exact he1
      exact (hHg (e 1) he1) ⟨e, Or.inr ⟨rfl, he10⟩, rfl⟩
  rintro a ⟨d, hd, rfl⟩
  change MvPowerSeries.coeff d (f * g) ∈ H
  rw [MvPowerSeries.coeff_mul]
  apply H.sum_mem
  intro q hq
  have hqadd : q.1 + q.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
  have hq0 := congrArg (fun z : (Fin 2 →₀ ℕ) => z 0) hqadd
  have hq1 := congrArg (fun z : (Fin 2 →₀ ℕ) => z 1) hqadd
  change q.1 0 + q.2 0 = d 0 at hq0
  change q.1 1 + q.2 1 = d 1 at hq1
  change (d 0 = n ∧ n ≤ d 1) ∨ (d 1 = n ∧ n ≤ d 0) at hd
  have hqf : q.1 0 ≤ n ∨ q.1 1 ≤ n := by
    rcases hd with ⟨hd0, hdn⟩ | ⟨hd1, hdn⟩
    · left
      omega
    · right
      omega
  have hqg : q.2 0 ≤ n ∨ q.2 1 ≤ n := by
    rcases hd with ⟨hd0, hdn⟩ | ⟨hd1, hdn⟩
    · left
      omega
    · right
      omega
  exact mul_mem (hcoeff_f q.1 hqf) (hcoeff_g q.2 hqg)

theorem aCondition_neg {f : TwoVariablePowerSeries k}
    (hf : ACondition k p f) :
    ACondition k p (-f) := by
  unfold ACondition at hf ⊢
  intro n
  unfold FiniteDegreeOverPowers at hf ⊢
  rcases hf n with ⟨F, hF, hFfin⟩
  refine ⟨F, ?_, hFfin⟩
  rintro a ⟨d, hd, rfl⟩
  change MvPowerSeries.coeff d (-f) ∈ F
  rw [map_neg]
  exact F.neg_mem (hF ⟨d, hd, rfl⟩)

/-- The bivariate subring `A` from the example. -/
def aSubring : Subring (TwoVariablePowerSeries k) where
  carrier := {f | ACondition k p f}
  zero_mem' := by
    exact aCondition_zero k p
  add_mem' := by
    intro f g hf hg
    exact aCondition_add k p hf hg
  one_mem' := by
    exact aCondition_one k p
  mul_mem' := by
    intro f g hf hg
    exact aCondition_mul k p hf hg
  neg_mem' := by
    intro f hf
    exact aCondition_neg k p hf

abbrev aRing := ↥(aSubring k p)

/-- The coefficientwise image of `k ^ p [[x,y]]` in the ambient bivariate
power-series ring. -/
def pPowerSeriesSubring : Subring (TwoVariablePowerSeries k) :=
  (MvPowerSeries.map (σ := Fin 2) (pPowerSubfield k p).subtype).range

/-- The coefficient ring `k^p[[x, y]]`, viewed as a type. -/
abbrev pPowerSeriesRing := ↥(pPowerSeriesSubring k p)

/-- The canonical scalar structure of the ambient power-series ring over
`k^p[[x, y]]`. -/
noncomputable instance pPowerSeriesRingAlgebra :
    Algebra (pPowerSeriesRing k p) (TwoVariablePowerSeries k) :=
  (pPowerSeriesSubring k p).subtype.toAlgebra

theorem pPowerSeriesSubring_le_aSubring :
    pPowerSeriesSubring k p ≤ aSubring k p := by
  intro f hf
  rcases hf with ⟨g, rfl⟩
  unfold aSubring ACondition FiniteDegreeOverPowers
  intro n
  refine ⟨⊥, ?_, inferInstance⟩
  rintro a ⟨d, hd, rfl⟩
  change MvPowerSeries.coeff d
      (MvPowerSeries.map (σ := Fin 2) (pPowerSubfield k p).subtype g) ∈
    (⊥ : IntermediateField (pPowerSubfield k p) k)
  rw [MvPowerSeries.coeff_map]
  apply IntermediateField.mem_bot.mpr
  exact ⟨MvPowerSeries.coeff d g, rfl⟩

/-- The ring `A` is a `k^p[[x, y]]`-subalgebra of `k[[x, y]]`. -/
def aSubalgebra : Subalgebra (pPowerSeriesRing k p) (TwoVariablePowerSeries k) where
  carrier := {f | ACondition k p f}
  zero_mem' := by
    exact aCondition_zero k p
  add_mem' := by
    intro f g hf hg
    exact aCondition_add k p hf hg
  one_mem' := by
    exact aCondition_one k p
  mul_mem' := by
    intro f g hf hg
    exact aCondition_mul k p hf hg
  algebraMap_mem' := by
    intro r
    exact pPowerSeriesSubring_le_aSubring k p r.property

theorem aSubring_le_ambient :
    aSubring k p ≤ ⊤ := by
  exact le_top

theorem aSubring_inclusions :
    pPowerSeriesSubring k p ≤ aSubring k p ∧ aSubring k p ≤ ⊤ := by
  exact ⟨pPowerSeriesSubring_le_aSubring k p, aSubring_le_ambient k p⟩

/-- The two one-variable series making up the `n`th diagonal block. -/
def diagonalBlock (f : TwoVariablePowerSeries k) (n : ℕ) : PowerSeries k × PowerSeries k :=
  (PowerSeries.mk (fun i : ℕ => coefficientXY k f (n + i) n),
    PowerSeries.mk (fun j : ℕ => coefficientXY k f n (n + j)))

def diagonalBlockCoefficients (f : TwoVariablePowerSeries k) (n : ℕ) : Set k :=
  Set.range (fun i : ℕ => PowerSeries.coeff i (diagonalBlock k f n).1) ∪
    Set.range (fun j : ℕ => PowerSeries.coeff j (diagonalBlock k f n).2)

theorem diagonalBlock_spec_left (f : TwoVariablePowerSeries k) (n i : ℕ) :
    PowerSeries.coeff i (diagonalBlock k f n).1 = coefficientXY k f (n + i) n := by
  simp [diagonalBlock, PowerSeries.coeff_mk]

theorem diagonalBlock_spec_right (f : TwoVariablePowerSeries k) (n j : ℕ) :
    PowerSeries.coeff j (diagonalBlock k f n).2 = coefficientXY k f n (n + j) := by
  simp [diagonalBlock, PowerSeries.coeff_mk]

theorem diagonalBlocks_unique (f : TwoVariablePowerSeries k) :
    ∃! blocks : ℕ → PowerSeries k × PowerSeries k,
      (∀ n i, PowerSeries.coeff i (blocks n).1 = coefficientXY k f (n + i) n) ∧
        ∀ n j, PowerSeries.coeff j (blocks n).2 = coefficientXY k f n (n + j) := by
  refine ⟨diagonalBlock k f, ?_, ?_⟩
  · exact ⟨diagonalBlock_spec_left k f, diagonalBlock_spec_right k f⟩
  · intro blocks hblocks
    funext n
    apply Prod.ext
    · apply PowerSeries.ext
      intro i
      exact (hblocks.1 n i).trans (diagonalBlock_spec_left k f n i).symm
    · apply PowerSeries.ext
      intro j
      exact (hblocks.2 n j).trans (diagonalBlock_spec_right k f n j).symm

/-- The coefficient selected by the diagonal expansion associated to a family
of blocks. -/
def diagonalExpansionCoeff (blocks : ℕ → PowerSeries k × PowerSeries k)
    (d : Fin 2 →₀ ℕ) : k :=
  if _h : d 0 ≤ d 1 then
    PowerSeries.coeff (d 1 - d 0) (blocks (d 0)).2
  else
    PowerSeries.coeff (d 0 - d 1) (blocks (d 1)).1

theorem diagonalExpansionCoeff_diagonalBlock (f : TwoVariablePowerSeries k)
    (d : Fin 2 →₀ ℕ) :
    diagonalExpansionCoeff k (diagonalBlock k f) d = MvPowerSeries.coeff d f := by
  unfold diagonalExpansionCoeff
  split_ifs with h
  · rw [diagonalBlock_spec_right]
    unfold coefficientXY
    have hindex :
        Finsupp.single (0 : Fin 2) (d 0) +
            Finsupp.single (1 : Fin 2) (d 0 + (d 1 - d 0)) = d := by
      ext i
      fin_cases i
      · simp
      · simp [Nat.add_sub_of_le h]
    rw [hindex]
  · have h' : d 1 ≤ d 0 := by omega
    rw [diagonalBlock_spec_left]
    unfold coefficientXY
    have hindex :
        Finsupp.single (0 : Fin 2) (d 1 + (d 0 - d 1)) +
            Finsupp.single (1 : Fin 2) (d 1) = d := by
      ext i
      fin_cases i
      · simp [Nat.add_sub_of_le h']
      · simp
    rw [hindex]

def diagonalExpansion (blocks : ℕ → PowerSeries k × PowerSeries k) :
    TwoVariablePowerSeries k :=
  fun d => diagonalExpansionCoeff k blocks d

theorem diagonalExpansion_diagonalBlocks (f : TwoVariablePowerSeries k) :
    diagonalExpansion k (diagonalBlock k f) = f := by
  funext d
  exact diagonalExpansionCoeff_diagonalBlock k f d

theorem aCondition_iff_diagonalBlocks (f : TwoVariablePowerSeries k) :
    ACondition k p f ↔
      ∀ n : ℕ, FiniteDegreeOverPowers k p (diagonalBlockCoefficients k f n) := by
  have hcoeff (n : ℕ) :
      diagonalBlockCoefficients k f n = diagonalCoefficients k f n := by
    ext a
    constructor
    · intro ha
      rcases ha with ha | ha
      · rcases ha with ⟨i, rfl⟩
        refine ⟨Finsupp.single (0 : Fin 2) (n + i) +
            Finsupp.single (1 : Fin 2) n, ?_, ?_⟩
        · right
          constructor <;> simp
        · change MvPowerSeries.coeff
              (Finsupp.single (0 : Fin 2) (n + i) +
                Finsupp.single (1 : Fin 2) n) f =
            PowerSeries.coeff i (diagonalBlock k f n).1
          rw [diagonalBlock_spec_left]
          rfl
      · rcases ha with ⟨j, rfl⟩
        refine ⟨Finsupp.single (0 : Fin 2) n +
            Finsupp.single (1 : Fin 2) (n + j), ?_, ?_⟩
        · left
          constructor <;> simp
        · change MvPowerSeries.coeff
              (Finsupp.single (0 : Fin 2) n +
                Finsupp.single (1 : Fin 2) (n + j)) f =
            PowerSeries.coeff j (diagonalBlock k f n).2
          rw [diagonalBlock_spec_right]
          rfl
    · intro ha
      rcases ha with ⟨d, hd, rfl⟩
      rcases hd with ⟨hd0, hdn⟩ | ⟨hd1, hdn⟩
      · right
        refine ⟨d 1 - n, ?_⟩
        change PowerSeries.coeff (d 1 - n) (diagonalBlock k f n).2 =
            MvPowerSeries.coeff d f
        rw [diagonalBlock_spec_right]
        unfold coefficientXY
        have hdeq :
            Finsupp.single (0 : Fin 2) n +
                Finsupp.single (1 : Fin 2) (n + (d 1 - n)) = d := by
          ext i
          fin_cases i <;> simp [hd0, Nat.add_sub_of_le hdn]
        rw [hdeq]
      · left
        refine ⟨d 0 - n, ?_⟩
        change PowerSeries.coeff (d 0 - n) (diagonalBlock k f n).1 =
            MvPowerSeries.coeff d f
        rw [diagonalBlock_spec_left]
        unfold coefficientXY
        have hdeq :
            Finsupp.single (0 : Fin 2) (n + (d 0 - n)) +
                Finsupp.single (1 : Fin 2) n = d := by
          ext i
          fin_cases i <;> simp [hd1, Nat.add_sub_of_le hdn]
        rw [hdeq]
  unfold ACondition
  constructor
  · intro h n
    rw [hcoeff n]
    exact h n
  · intro h n
    rw [← hcoeff n]
    exact h n

end TwoVariableSeries

section TheRingA

variable (k : Type u) (p : ℕ) [Field k] [Fact p.Prime] [CharP k p]

/-! The ambient bivariate power-series ring is viewed as an algebra over the
subring `A`.  This is the scalar structure used by the integral-extension
form of the dimension argument below. -/

noncomputable instance aRingAlgebraAmbient :
    Algebra (aRing k p) (TwoVariablePowerSeries k) :=
  (aSubring k p).subtype.toAlgebra

theorem x_mem_aSubring :
    (MvPowerSeries.X 0 : TwoVariablePowerSeries k) ∈ aSubring k p := by
  change ACondition k p (MvPowerSeries.X 0)
  unfold ACondition
  intro n
  unfold FiniteDegreeOverPowers
  refine ⟨⊥, ?_, inferInstance⟩
  rintro a ⟨d, hd, rfl⟩
  change MvPowerSeries.coeff d (MvPowerSeries.X 0) ∈
    (⊥ : IntermediateField (pPowerSubfield k p) k)
  rw [MvPowerSeries.coeff_X]
  by_cases h : d = Finsupp.single (0 : Fin 2) 1
  · simp [h]
  · simp [h]

theorem y_mem_aSubring :
    (MvPowerSeries.X 1 : TwoVariablePowerSeries k) ∈ aSubring k p := by
  change ACondition k p (MvPowerSeries.X 1)
  unfold ACondition
  intro n
  unfold FiniteDegreeOverPowers
  refine ⟨⊥, ?_, inferInstance⟩
  rintro a ⟨d, hd, rfl⟩
  change MvPowerSeries.coeff d (MvPowerSeries.X 1) ∈
    (⊥ : IntermediateField (pPowerSubfield k p) k)
  rw [MvPowerSeries.coeff_X]
  by_cases h : d = Finsupp.single (1 : Fin 2) 1
  · simp [h]
  · simp [h]

abbrev aX : aRing k p :=
  ⟨MvPowerSeries.X 0, x_mem_aSubring k p⟩

abbrev aY : aRing k p :=
  ⟨MvPowerSeries.X 1, y_mem_aSubring k p⟩

def aXYIdeal : Ideal (aRing k p) :=
  Ideal.span {aX k p * aY k p}

def aMaximalIdeal : Ideal (aRing k p) :=
  Ideal.span {aX k p, aY k p}

abbrev aCompletion : Type u := AdicCompletion (aXYIdeal k p) (aRing k p)

theorem a_is_complete :
    IsAdicComplete (aXYIdeal k p) (aRing k p) := by
  have hzeroX (n : ℕ) {z : aRing k p}
      (hz : z ∈ (aXYIdeal k p) ^ n • (⊤ : Submodule (aRing k p) (aRing k p)))
      (d : Fin 2 →₀ ℕ) (hd : d 0 < n) :
      MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) = 0 := by
    have hz' : z ∈ (aXYIdeal k p) ^ n := by
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr x hx
        simpa [smul_eq_mul, mul_comm] using
          (aXYIdeal k p ^ n).mul_mem_left x hr
      · intro x y hx hy
        exact (aXYIdeal k p ^ n).add_mem hx hy
    change z ∈ (Ideal.span {aX k p * aY k p}) ^ n at hz'
    rw [Ideal.span_singleton_pow] at hz'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz'
    have hdiv : (MvPowerSeries.X 0 : TwoVariablePowerSeries k) ^ n ∣
        (z : TwoVariablePowerSeries k) := by
      refine ⟨((c : aRing k p) : TwoVariablePowerSeries k) *
          (MvPowerSeries.X 1 : TwoVariablePowerSeries k) ^ n, ?_⟩
      rw [← hc]
      simp [aX, aY, mul_pow, mul_left_comm]
    exact (MvPowerSeries.X_pow_dvd_iff.mp hdiv d hd)
  have hzeroY (n : ℕ) {z : aRing k p}
      (hz : z ∈ (aXYIdeal k p) ^ n • (⊤ : Submodule (aRing k p) (aRing k p)))
      (d : Fin 2 →₀ ℕ) (hd : d 1 < n) :
      MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) = 0 := by
    have hz' : z ∈ (aXYIdeal k p) ^ n := by
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr x hx
        simpa [smul_eq_mul, mul_comm] using
          (aXYIdeal k p ^ n).mul_mem_left x hr
      · intro x y hx hy
        exact (aXYIdeal k p ^ n).add_mem hx hy
    change z ∈ (Ideal.span {aX k p * aY k p}) ^ n at hz'
    rw [Ideal.span_singleton_pow] at hz'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz'
    have hdiv : (MvPowerSeries.X 1 : TwoVariablePowerSeries k) ^ n ∣
        (z : TwoVariablePowerSeries k) := by
      refine ⟨((c : aRing k p) : TwoVariablePowerSeries k) *
          (MvPowerSeries.X 0 : TwoVariablePowerSeries k) ^ n, ?_⟩
      rw [← hc]
      simp [aX, aY, mul_pow, mul_assoc, mul_comm]
    exact (MvPowerSeries.X_pow_dvd_iff.mp hdiv d hd)
  have hhaus : IsHausdorff (aXYIdeal k p) (aRing k p) := by
    refine ⟨fun z hz => ?_⟩
    apply Subtype.ext
    ext d
    have hzero :=
      hzeroX (d 0 + 1) (SModEq.sub_mem.mp (hz (d 0 + 1))) d
        (Nat.lt_succ_self _)
    simpa using hzero
  have hlimit_condition (fseq : ℕ → aRing k p) :
      ACondition k p (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d
          (fseq (min (d 0) (d 1) + 1) : TwoVariablePowerSeries k)) := by
    let g : TwoVariablePowerSeries k := fun d =>
      MvPowerSeries.coeff d
        (fseq (min (d 0) (d 1) + 1) : TwoVariablePowerSeries k)
    change ACondition k p g
    apply (aCondition_iff_diagonalBlocks k p _).2
    intro q
    have hFq := (aCondition_iff_diagonalBlocks k p
      (fseq (q + 1))).1 (fseq (q + 1)).property q
    rcases hFq with ⟨F, hF, hFfin⟩
    refine ⟨F, ?_, hFfin⟩
    intro a ha
    rcases ha with ha | ha
    · rcases ha with ⟨i, rfl⟩
      apply hF
      left
      refine ⟨i, ?_⟩
      change PowerSeries.coeff i
          (diagonalBlock k (fseq (q + 1) : TwoVariablePowerSeries k) q).1 =
        PowerSeries.coeff i (diagonalBlock k g q).1
      rw [diagonalBlock_spec_left, diagonalBlock_spec_left]
      unfold coefficientXY
      let e : Fin 2 →₀ ℕ :=
        Finsupp.single (0 : Fin 2) q + Finsupp.single (0 : Fin 2) i +
          Finsupp.single (1 : Fin 2) q
      have heq :
          Finsupp.single (0 : Fin 2) (q + i) +
              Finsupp.single (1 : Fin 2) q = e := by
        ext t
        fin_cases t <;> simp [e]
      rw [heq]
      have hmin : min (e 0) (e 1) = q := by simp [e]
      change MvPowerSeries.coeff e
          (fseq (q + 1) : TwoVariablePowerSeries k) =
        MvPowerSeries.coeff e
          (fseq (min (e 0) (e 1) + 1) : TwoVariablePowerSeries k)
      rw [hmin]
    · rcases ha with ⟨j, rfl⟩
      apply hF
      right
      refine ⟨j, ?_⟩
      change PowerSeries.coeff j
          (diagonalBlock k (fseq (q + 1) : TwoVariablePowerSeries k) q).2 =
        PowerSeries.coeff j (diagonalBlock k g q).2
      rw [diagonalBlock_spec_right, diagonalBlock_spec_right]
      unfold coefficientXY
      let e : Fin 2 →₀ ℕ :=
        Finsupp.single (0 : Fin 2) q +
          (Finsupp.single (1 : Fin 2) q + Finsupp.single (1 : Fin 2) j)
      have heq :
          Finsupp.single (0 : Fin 2) q +
              Finsupp.single (1 : Fin 2) (q + j) = e := by
        ext t
        fin_cases t <;> simp [e]
      rw [heq]
      have hmin : min (e 0) (e 1) = q := by simp [e]
      change MvPowerSeries.coeff e
          (fseq (q + 1) : TwoVariablePowerSeries k) =
        MvPowerSeries.coeff e
          (fseq (min (e 0) (e 1) + 1) : TwoVariablePowerSeries k)
      rw [hmin]
  have hquotient (z : aRing k p) (n : ℕ)
      (hz0 : ∀ d : Fin 2 →₀ ℕ, d 0 < n →
        MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) = 0)
      (hz1 : ∀ d : Fin 2 →₀ ℕ, d 1 < n →
        MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) = 0) :
      ∃ q : aRing k p, z = (aX k p * aY k p) ^ n * q := by
    let shift : Fin 2 →₀ ℕ :=
      Finsupp.single (0 : Fin 2) n + Finsupp.single (1 : Fin 2) n
    let q0 : TwoVariablePowerSeries k := fun d =>
      MvPowerSeries.coeff (d + shift) (z : TwoVariablePowerSeries k)
    have hqcond : ACondition k p q0 := by
      apply (aCondition_iff_diagonalBlocks k p q0).2
      intro r
      have hF := (aCondition_iff_diagonalBlocks k p (z : TwoVariablePowerSeries k)).1
        z.property (r + n)
      rcases hF with ⟨F, hF, hFfin⟩
      refine ⟨F, ?_, hFfin⟩
      intro a ha
      rcases ha with ha | ha
      · rcases ha with ⟨i, rfl⟩
        apply hF
        left
        refine ⟨i, ?_⟩
        change PowerSeries.coeff i
            (diagonalBlock k (z : TwoVariablePowerSeries k) (r + n)).1 =
          PowerSeries.coeff i (diagonalBlock k q0 r).1
        rw [diagonalBlock_spec_left, diagonalBlock_spec_left]
        unfold coefficientXY
        have heq :
            Finsupp.single (0 : Fin 2) (r + n + i) +
                Finsupp.single (1 : Fin 2) (r + n) =
              (Finsupp.single (0 : Fin 2) (r + i) +
                Finsupp.single (1 : Fin 2) r) + shift := by
          ext t
          fin_cases t <;> simp [shift, Nat.add_left_comm, Nat.add_comm]
        rw [heq]
        rfl
      · rcases ha with ⟨j, rfl⟩
        apply hF
        right
        refine ⟨j, ?_⟩
        change PowerSeries.coeff j
            (diagonalBlock k (z : TwoVariablePowerSeries k) (r + n)).2 =
          PowerSeries.coeff j (diagonalBlock k q0 r).2
        rw [diagonalBlock_spec_right, diagonalBlock_spec_right]
        unfold coefficientXY
        have heq :
            Finsupp.single (0 : Fin 2) (r + n) +
                Finsupp.single (1 : Fin 2) (r + n + j) =
              (Finsupp.single (0 : Fin 2) r +
                Finsupp.single (1 : Fin 2) (r + j)) + shift := by
          ext t
          fin_cases t <;> simp [shift, Nat.add_left_comm, Nat.add_comm]
        rw [heq]
        rfl
    refine ⟨⟨q0, hqcond⟩, ?_⟩
    apply Subtype.ext
    ext d
    change MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) =
      MvPowerSeries.coeff d
        (((MvPowerSeries.X 0 * MvPowerSeries.X 1 :
          TwoVariablePowerSeries k) ^ n) * q0)
    rw [show (MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        TwoVariablePowerSeries k) ^ n =
          MvPowerSeries.monomial shift 1 by
      simp [shift, mul_pow, MvPowerSeries.X_pow_eq,
        MvPowerSeries.monomial_mul_monomial]]
    rw [MvPowerSeries.coeff_monomial_mul]
    split_ifs with h
    · dsimp [q0]
      simp only [one_mul]
      change MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) =
        MvPowerSeries.coeff (d - shift + shift) (z : TwoVariablePowerSeries k)
      rw [tsub_add_cancel_of_le h]
    · by_cases h0 : d 0 < n
      · exact hz0 d h0
      · by_cases h1 : d 1 < n
        · exact hz1 d h1
        · have hle : shift ≤ d := by
            intro i
            fin_cases i <;> simp [shift, Nat.le_of_not_gt h0,
              Nat.le_of_not_gt h1]
          exact (h hle).elim
  rw [← AdicCompletion.of_bijective_iff]
  refine ⟨AdicCompletion.of_injective_iff.mpr hhaus, ?_⟩
  apply AdicCompletion.of_surjective_iff.mpr
  constructor
  intro fseq hf
  let g : TwoVariablePowerSeries k := fun d =>
    MvPowerSeries.coeff d
      (fseq (min (d 0) (d 1) + 1) : TwoVariablePowerSeries k)
  have hgcond : ACondition k p g := by
    simpa [g] using hlimit_condition fseq
  let L : aRing k p := ⟨g, hgcond⟩
  refine ⟨L, ?_⟩
  intro n
  apply SModEq.sub_mem.mpr
  have hcoeff (d : Fin 2 →₀ ℕ)
      (hn : min (d 0) (d 1) + 1 ≤ n) :
      MvPowerSeries.coeff d (fseq n : TwoVariablePowerSeries k) =
        MvPowerSeries.coeff d (L : TwoVariablePowerSeries k) := by
    by_cases h01 : d 0 ≤ d 1
    · have hm : min (d 0) (d 1) + 1 = d 0 + 1 := by
        rw [min_eq_left h01]
      have hmn : d 0 + 1 ≤ n := by simpa [hm] using hn
      have hdiff := SModEq.sub_mem.mp (hf hmn)
      have hzero := hzeroX (d 0 + 1) hdiff d (by omega)
      have hzero' :
          MvPowerSeries.coeff d (fseq (d 0 + 1) : TwoVariablePowerSeries k) -
            MvPowerSeries.coeff d (fseq n : TwoVariablePowerSeries k) = 0 := by
        change MvPowerSeries.coeff d
            ((fseq (d 0 + 1) : TwoVariablePowerSeries k) -
              (fseq n : TwoVariablePowerSeries k)) = 0 at hzero
        simpa only [map_sub] using hzero
      change MvPowerSeries.coeff d (fseq n : TwoVariablePowerSeries k) =
        MvPowerSeries.coeff d
          (fseq (min (d 0) (d 1) + 1) : TwoVariablePowerSeries k)
      rw [hm]
      exact (sub_eq_zero.mp hzero').symm
    · have hlt : d 1 < d 0 := Nat.lt_of_not_ge h01
      have hm : min (d 0) (d 1) + 1 = d 1 + 1 := by
        rw [min_eq_right (Nat.le_of_lt hlt)]
      have hmn : d 1 + 1 ≤ n := by simpa [hm] using hn
      have hdiff := SModEq.sub_mem.mp (hf hmn)
      have hzero := hzeroY (d 1 + 1) hdiff d (by omega)
      have hzero' :
          MvPowerSeries.coeff d (fseq (d 1 + 1) : TwoVariablePowerSeries k) -
            MvPowerSeries.coeff d (fseq n : TwoVariablePowerSeries k) = 0 := by
        change MvPowerSeries.coeff d
            ((fseq (d 1 + 1) : TwoVariablePowerSeries k) -
              (fseq n : TwoVariablePowerSeries k)) = 0 at hzero
        simpa only [map_sub] using hzero
      change MvPowerSeries.coeff d (fseq n : TwoVariablePowerSeries k) =
        MvPowerSeries.coeff d
          (fseq (min (d 0) (d 1) + 1) : TwoVariablePowerSeries k)
      rw [hm]
      exact (sub_eq_zero.mp hzero').symm
  have hz0 : ∀ d : Fin 2 →₀ ℕ, d 0 < n →
      MvPowerSeries.coeff d ((fseq n - L : aRing k p) : TwoVariablePowerSeries k) = 0 := by
    intro d hd
    have hmn : min (d 0) (d 1) + 1 ≤ n := by
      by_cases h01 : d 0 ≤ d 1
      · simpa [min_eq_left h01] using (Nat.succ_le_of_lt hd)
      · have hlt : d 1 < d 0 := Nat.lt_of_not_ge h01
        rw [min_eq_right (Nat.le_of_lt hlt)]
        exact le_trans (Nat.succ_le_of_lt hlt) (Nat.le_of_lt hd)
    have hc := hcoeff d hmn
    change MvPowerSeries.coeff d
      ((fseq n : TwoVariablePowerSeries k) - (L : TwoVariablePowerSeries k)) = 0
    rw [map_sub, hc]
    exact sub_self _
  have hz1 : ∀ d : Fin 2 →₀ ℕ, d 1 < n →
      MvPowerSeries.coeff d ((fseq n - L : aRing k p) : TwoVariablePowerSeries k) = 0 := by
    intro d hd
    have hmn : min (d 0) (d 1) + 1 ≤ n := by
      by_cases h01 : d 0 ≤ d 1
      · rw [min_eq_left h01]
        exact Nat.succ_le_of_lt (lt_of_le_of_lt h01 hd)
      · simpa [min_eq_right (Nat.le_of_not_ge h01)] using (Nat.succ_le_of_lt hd)
    have hc := hcoeff d hmn
    change MvPowerSeries.coeff d
      ((fseq n : TwoVariablePowerSeries k) - (L : TwoVariablePowerSeries k)) = 0
    rw [map_sub, hc]
    exact sub_self _
  obtain ⟨q, hq⟩ := hquotient (fseq n - L) n hz0 hz1
  rw [hq]
  have hgen : aX k p * aY k p ∈ aXYIdeal k p := by
    exact Ideal.subset_span (by simp)
  simpa [smul_eq_mul] using
    (Submodule.smul_mem_smul (Ideal.pow_mem_pow hgen n)
      (show q ∈ (⊤ : Submodule (aRing k p) (aRing k p)) by trivial))

theorem a_quotient_is_fiberProduct :
    Nonempty ((aRing k p ⧸ aXYIdeal k p) ≃+*
      ↥(RingHom.pullback (badDvrConstantCoeff k p) (badDvrConstantCoeff k p))) := by
  let e : Unit ↪ Fin 2 := ⟨fun _ => 0, by intro x y h; simp⟩
  let r : TwoVariablePowerSeries k →+* PowerSeries k :=
    (MvPowerSeries.killCompl e).toRingHom
  have hr (z : aRing k p) : OneVariableFiniteDegree k p
      (r (z : TwoVariablePowerSeries k)) := by
    rcases (aCondition_iff_diagonalBlocks k p
      (z : TwoVariablePowerSeries k)).1 z.property 0 with ⟨F, hF, hFfin⟩
    refine ⟨F, ?_, hFfin⟩
    rintro a ⟨i, rfl⟩
    change PowerSeries.coeff i (r (z : TwoVariablePowerSeries k)) ∈ F
    change MvPowerSeries.coeff (Finsupp.single () i)
      ((MvPowerSeries.killCompl e) (z : TwoVariablePowerSeries k)) ∈ F
    rw [MvPowerSeries.coeff_killCompl]
    have he : Finsupp.embDomain e (Finsupp.single () i) =
        Finsupp.single (0 : Fin 2) i := by
      ext j
      have he0 : e () = (0 : Fin 2) := rfl
      fin_cases j <;> simp [he0]
    rw [he]
    apply hF
    left
    refine ⟨i, ?_⟩
    simp [diagonalBlock_spec_left, coefficientXY]
  let e' : Unit ↪ Fin 2 := ⟨fun _ => 1, by intro x y h; simp⟩
  let r' : TwoVariablePowerSeries k →+* PowerSeries k :=
    (MvPowerSeries.killCompl e').toRingHom
  have hr' (z : aRing k p) : OneVariableFiniteDegree k p
      (r' (z : TwoVariablePowerSeries k)) := by
    rcases (aCondition_iff_diagonalBlocks k p
      (z : TwoVariablePowerSeries k)).1 z.property 0 with ⟨F, hF, hFfin⟩
    refine ⟨F, ?_, hFfin⟩
    rintro a ⟨i, rfl⟩
    change PowerSeries.coeff i (r' (z : TwoVariablePowerSeries k)) ∈ F
    change MvPowerSeries.coeff (Finsupp.single () i)
      ((MvPowerSeries.killCompl e') (z : TwoVariablePowerSeries k)) ∈ F
    rw [MvPowerSeries.coeff_killCompl]
    have he : Finsupp.embDomain e' (Finsupp.single () i) =
        Finsupp.single (1 : Fin 2) i := by
      ext j
      have he1 : e' () = (1 : Fin 2) := rfl
      fin_cases j <;> simp [he1]
    rw [he]
    apply hF
    right
    refine ⟨i, ?_⟩
    simp [diagonalBlock_spec_right, coefficientXY]

  let x : PowerSeries k →ₐ[k] TwoVariablePowerSeries k :=
    MvPowerSeries.rename e
  let y : PowerSeries k →ₐ[k] TwoVariablePowerSeries k :=
    MvPowerSeries.rename e'
  have hx (f : PowerSeries k) (hf : OneVariableFiniteDegree k p f) :
      ACondition k p (x f) := by
    unfold ACondition
    intro n
    rcases hf with ⟨F, hF, hFfin⟩
    refine ⟨F, ?_, hFfin⟩
    rintro a ⟨d, hd, rfl⟩
    change MvPowerSeries.coeff d (x f) ∈ F
    by_cases hd1 : d 1 = 0
    · have heq : d = Finsupp.embDomain e (Finsupp.single () (d 0)) := by
        ext j
        have he0 : e () = (0 : Fin 2) := rfl
        fin_cases j <;> simp [hd1, he0]
      rw [heq]
      change MvPowerSeries.coeff
        (Finsupp.embDomain e (Finsupp.single () (d 0)))
        (MvPowerSeries.rename e f) ∈ F
      rw [MvPowerSeries.coeff_embDomain_rename]
      exact hF ⟨d 0, rfl⟩
    · have hnot : d ∉ Set.range (Finsupp.mapDomain e) := by
        rintro ⟨q, rfl⟩
        apply hd1
        have h1 : (1 : Fin 2) ∉ Set.range e := by
          rintro ⟨u, hu⟩
          cases u
          change (0 : Fin 2) = 1 at hu
          exact Fin.zero_ne_one hu
        exact Finsupp.mapDomain_of_notMem_range q 1 h1
      change MvPowerSeries.coeff d (MvPowerSeries.rename e f) ∈ F
      rw [MvPowerSeries.coeff_rename_eq_zero e f hnot]
      exact (F : IntermediateField (pPowerSubfield k p) k).zero_mem
  have hy (f : PowerSeries k) (hf : OneVariableFiniteDegree k p f) :
      ACondition k p (y f) := by
    unfold ACondition
    intro n
    rcases hf with ⟨F, hF, hFfin⟩
    refine ⟨F, ?_, hFfin⟩
    rintro a ⟨d, hd, rfl⟩
    change MvPowerSeries.coeff d (y f) ∈ F
    by_cases hd0 : d 0 = 0
    · have heq : d = Finsupp.embDomain e' (Finsupp.single () (d 1)) := by
        ext j
        have he1 : e' () = (1 : Fin 2) := rfl
        fin_cases j <;> simp [hd0, he1]
      rw [heq]
      change MvPowerSeries.coeff
        (Finsupp.embDomain e' (Finsupp.single () (d 1)))
        (MvPowerSeries.rename e' f) ∈ F
      rw [MvPowerSeries.coeff_embDomain_rename]
      exact hF ⟨d 1, rfl⟩
    · have hnot : d ∉ Set.range (Finsupp.mapDomain e') := by
        rintro ⟨q, rfl⟩
        apply hd0
        have h0 : (0 : Fin 2) ∉ Set.range e' := by
          rintro ⟨u, hu⟩
          cases u
          change (1 : Fin 2) = 0 at hu
          exact Fin.zero_ne_one hu.symm
        exact Finsupp.mapDomain_of_notMem_range q 0 h0
      change MvPowerSeries.coeff d (MvPowerSeries.rename e' f) ∈ F
      rw [MvPowerSeries.coeff_rename_eq_zero e' f hnot]
      exact (F : IntermediateField (pPowerSubfield k p) k).zero_mem

  let xMap : aRing k p →+* badDvrRing k p :=
    (r.comp (aSubring k p).subtype).codRestrict
      (badDvrSubring k p) (fun z => hr z)
  let yMap : aRing k p →+* badDvrRing k p :=
    (r'.comp (aSubring k p).subtype).codRestrict
      (badDvrSubring k p) (fun z => hr' z)
  have hconst (z : aRing k p) :
      badDvrConstantCoeff k p (xMap z) = badDvrConstantCoeff k p (yMap z) := by
    change PowerSeries.constantCoeff (r (z : TwoVariablePowerSeries k)) =
      PowerSeries.constantCoeff (r' (z : TwoVariablePowerSeries k))
    change MvPowerSeries.coeff 0
        ((MvPowerSeries.killCompl e) (z : TwoVariablePowerSeries k)) =
      MvPowerSeries.coeff 0
        ((MvPowerSeries.killCompl e') (z : TwoVariablePowerSeries k))
    rw [MvPowerSeries.coeff_killCompl, MvPowerSeries.coeff_killCompl]
    rfl
  let phi : aRing k p →+*
      RingHom.pullback (badDvrConstantCoeff k p) (badDvrConstantCoeff k p) :=
    (xMap.prod yMap).codRestrict _ hconst

  have hconstSeries (c : badDvrRing k p) :
      OneVariableFiniteDegree k p (PowerSeries.C (PowerSeries.constantCoeff c)) := by
    rcases c.property with ⟨F, hF, hFfin⟩
    refine ⟨F, ?_, hFfin⟩
    rintro a ⟨i, rfl⟩
    by_cases hi : i = 0
    · subst i
      simpa using hF ⟨0, rfl⟩
    · simp [PowerSeries.coeff_C, hi, F.zero_mem]

  have hxx (f : PowerSeries k) : r (x f) = f := by
    change MvPowerSeries.killCompl e (MvPowerSeries.rename e f) = f
    exact MvPowerSeries.killCompl_rename_app (e := e) f
  have hyy (f : PowerSeries k) : r' (y f) = f := by
    change MvPowerSeries.killCompl e' (MvPowerSeries.rename e' f) = f
    exact MvPowerSeries.killCompl_rename_app (e := e') f
  have hxy (f : PowerSeries k) :
      r (y f) = PowerSeries.C (PowerSeries.constantCoeff f) := by
    ext i
    change PowerSeries.coeff i
        (MvPowerSeries.killCompl e (MvPowerSeries.rename e' f)) =
      PowerSeries.coeff i (PowerSeries.C (PowerSeries.constantCoeff f))
    by_cases hi : i = 0
    · subst i
      change MvPowerSeries.coeff (Finsupp.single () 0)
          (MvPowerSeries.killCompl e (MvPowerSeries.rename e' f)) = _
      rw [MvPowerSeries.coeff_killCompl]
      have heq : Finsupp.embDomain e (Finsupp.single () 0) = 0 := by
        ext j
        fin_cases j
        · simp [e]
        · simp [e]
      rw [heq]
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rfl
    · have heq : Finsupp.embDomain e (Finsupp.single () i) =
          Finsupp.single (0 : Fin 2) i := by
        ext j
        have he0 : e () = (0 : Fin 2) := rfl
        fin_cases j <;> simp [he0]
      change MvPowerSeries.coeff (Finsupp.single () i)
          (MvPowerSeries.killCompl e (MvPowerSeries.rename e' f)) = _
      rw [MvPowerSeries.coeff_killCompl, heq]
      have hnot : Finsupp.single (0 : Fin 2) i ∉
          Set.range (Finsupp.mapDomain e') := by
        rintro ⟨q, hq⟩
        have h0 : (0 : Fin 2) ∉ Set.range e' := by
          rintro ⟨u, hu⟩
          cases u
          change (1 : Fin 2) = 0 at hu
          exact Fin.zero_ne_one hu.symm
        have := Finsupp.mapDomain_of_notMem_range q 0 h0
        have hcoord := this
        rw [hq] at hcoord
        simp [hi] at hcoord
      rw [MvPowerSeries.coeff_rename_eq_zero e' f hnot]
      simp [PowerSeries.coeff_C, hi]
  have hyx (f : PowerSeries k) :
      r' (x f) = PowerSeries.C (PowerSeries.constantCoeff f) := by
    ext i
    change PowerSeries.coeff i
        (MvPowerSeries.killCompl e' (MvPowerSeries.rename e f)) =
      PowerSeries.coeff i (PowerSeries.C (PowerSeries.constantCoeff f))
    by_cases hi : i = 0
    · subst i
      change MvPowerSeries.coeff (Finsupp.single () 0)
          (MvPowerSeries.killCompl e' (MvPowerSeries.rename e f)) = _
      rw [MvPowerSeries.coeff_killCompl]
      have heq : Finsupp.embDomain e' (Finsupp.single () 0) = 0 := by
        ext j
        fin_cases j
        · simp [e']
        · simp [e']
      rw [heq]
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rfl
    · have heq : Finsupp.embDomain e' (Finsupp.single () i) =
          Finsupp.single (1 : Fin 2) i := by
        ext j
        have he1 : e' () = (1 : Fin 2) := rfl
        fin_cases j <;> simp [he1]
      change MvPowerSeries.coeff (Finsupp.single () i)
          (MvPowerSeries.killCompl e' (MvPowerSeries.rename e f)) = _
      rw [MvPowerSeries.coeff_killCompl, heq]
      have hnot : Finsupp.single (1 : Fin 2) i ∉
          Set.range (Finsupp.mapDomain e) := by
        rintro ⟨q, hq⟩
        have h1 : (1 : Fin 2) ∉ Set.range e := by
          rintro ⟨u, hu⟩
          cases u
          change (0 : Fin 2) = 1 at hu
          exact Fin.zero_ne_one hu
        have := Finsupp.mapDomain_of_notMem_range q 1 h1
        have hcoord := this
        rw [hq] at hcoord
        simp [hi] at hcoord
      rw [MvPowerSeries.coeff_rename_eq_zero e f hnot]
      simp [PowerSeries.coeff_C, hi]

  have hsurj : Function.Surjective phi := by
    intro w
    let c : PowerSeries k := w.1.1
    let d : PowerSeries k := w.1.2
    let t : k := PowerSeries.constantCoeff c
    have hcd : PowerSeries.constantCoeff c = PowerSeries.constantCoeff d := by
      have hw := w.property
      change badDvrConstantCoeff k p w.1.1 = badDvrConstantCoeff k p w.1.2 at hw
      simpa [c, d, badDvrConstantCoeff] using hw
    have htd : PowerSeries.constantCoeff d = t := by
      simpa [t] using hcd.symm
    have hct : OneVariableFiniteDegree k p (PowerSeries.C t) := by
      simpa [t] using hconstSeries w.1.1
    have hzcond : ACondition k p
        (x c + y d - x (PowerSeries.C t)) := by
      simpa only [sub_eq_add_neg] using (aCondition_add k p
        (aCondition_add k p (hx c w.1.1.property) (hy d w.1.2.property))
        (aCondition_neg k p (hx (PowerSeries.C t) hct)))
    let z : aRing k p := ⟨x c + y d - x (PowerSeries.C t), hzcond⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change xMap z = w.1.1
      apply Subtype.ext
      change r (x c + y d - x (PowerSeries.C t)) = c
      rw [map_sub, map_add, hxx, hxy, hxx]
      simp [htd]
    · change yMap z = w.1.2
      apply Subtype.ext
      change r' (x c + y d - x (PowerSeries.C t)) = d
      rw [map_sub, map_add, hyx, hyy, hyx]
      simp [t]

  have hr_aX : r (aX k p) = PowerSeries.X := by
    change MvPowerSeries.killCompl e (MvPowerSeries.X (0 : Fin 2)) = _
    convert MvPowerSeries.killCompl_X (R := k) (e := e) () using 1 <;> rfl
  have hr_aY : r (aY k p) = 0 := by
    change MvPowerSeries.killCompl e (MvPowerSeries.X (1 : Fin 2)) = 0
    have h1 : (1 : Fin 2) ∉ Set.range e := by
      rintro ⟨u, hu⟩
      cases u
      change (0 : Fin 2) = 1 at hu
      exact Fin.zero_ne_one hu
    exact MvPowerSeries.killCompl_X_eq_zero (R := k) (e := e) h1
  have hr'_aX : r' (aX k p) = 0 := by
    change MvPowerSeries.killCompl e' (MvPowerSeries.X (0 : Fin 2)) = 0
    have h0 : (0 : Fin 2) ∉ Set.range e' := by
      rintro ⟨u, hu⟩
      cases u
      change (1 : Fin 2) = 0 at hu
      exact Fin.zero_ne_one hu.symm
    exact MvPowerSeries.killCompl_X_eq_zero (R := k) (e := e') h0
  have hr'_aY : r' (aY k p) = PowerSeries.X := by
    change MvPowerSeries.killCompl e' (MvPowerSeries.X (1 : Fin 2)) = _
    convert MvPowerSeries.killCompl_X (R := k) (e := e') () using 1 <;> rfl

  have hdiv (z : aRing k p) (n : ℕ)
      (hz0 : ∀ d : Fin 2 →₀ ℕ, d 0 < n →
        MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) = 0)
      (hz1 : ∀ d : Fin 2 →₀ ℕ, d 1 < n →
        MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) = 0) :
      ∃ q : aRing k p, z = (aX k p * aY k p) ^ n * q := by
    let shift : Fin 2 →₀ ℕ :=
      Finsupp.single (0 : Fin 2) n + Finsupp.single (1 : Fin 2) n
    let q0 : TwoVariablePowerSeries k := fun d =>
      MvPowerSeries.coeff (d + shift) (z : TwoVariablePowerSeries k)
    have hqcond : ACondition k p q0 := by
      apply (aCondition_iff_diagonalBlocks k p q0).2
      intro r0
      have hF := (aCondition_iff_diagonalBlocks k p
        (z : TwoVariablePowerSeries k)).1 z.property (r0 + n)
      rcases hF with ⟨F, hF, hFfin⟩
      refine ⟨F, ?_, hFfin⟩
      intro a ha
      rcases ha with ha | ha
      · rcases ha with ⟨i, rfl⟩
        apply hF
        left
        refine ⟨i, ?_⟩
        change PowerSeries.coeff i
            (diagonalBlock k (z : TwoVariablePowerSeries k) (r0 + n)).1 =
          PowerSeries.coeff i (diagonalBlock k q0 r0).1
        rw [diagonalBlock_spec_left, diagonalBlock_spec_left]
        unfold coefficientXY
        have heq :
            Finsupp.single (0 : Fin 2) (r0 + n + i) +
                Finsupp.single (1 : Fin 2) (r0 + n) =
              (Finsupp.single (0 : Fin 2) (r0 + i) +
                Finsupp.single (1 : Fin 2) r0) + shift := by
          ext t
          fin_cases t <;> simp [shift, Nat.add_left_comm, Nat.add_comm]
        rw [heq]
        rfl
      · rcases ha with ⟨j, rfl⟩
        apply hF
        right
        refine ⟨j, ?_⟩
        change PowerSeries.coeff j
            (diagonalBlock k (z : TwoVariablePowerSeries k) (r0 + n)).2 =
          PowerSeries.coeff j (diagonalBlock k q0 r0).2
        rw [diagonalBlock_spec_right, diagonalBlock_spec_right]
        unfold coefficientXY
        have heq :
            Finsupp.single (0 : Fin 2) (r0 + n) +
                Finsupp.single (1 : Fin 2) (r0 + n + j) =
              (Finsupp.single (0 : Fin 2) r0 +
                Finsupp.single (1 : Fin 2) (r0 + j)) + shift := by
          ext t
          fin_cases t <;> simp [shift, Nat.add_left_comm, Nat.add_comm]
        rw [heq]
        rfl
    refine ⟨⟨q0, hqcond⟩, ?_⟩
    apply Subtype.ext
    ext d
    change MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) =
      MvPowerSeries.coeff d
        (((MvPowerSeries.X 0 * MvPowerSeries.X 1 :
          TwoVariablePowerSeries k) ^ n) * q0)
    rw [show (MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        TwoVariablePowerSeries k) ^ n =
          MvPowerSeries.monomial shift 1 by
      simp [shift, mul_pow, MvPowerSeries.X_pow_eq,
        MvPowerSeries.monomial_mul_monomial]]
    rw [MvPowerSeries.coeff_monomial_mul]
    split_ifs with h
    · dsimp [q0]
      simp only [one_mul]
      change MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) =
        MvPowerSeries.coeff (d - shift + shift) (z : TwoVariablePowerSeries k)
      rw [tsub_add_cancel_of_le h]
    · by_cases h0 : d 0 < n
      · exact hz0 d h0
      · by_cases h1 : d 1 < n
        · exact hz1 d h1
        · have hle : shift ≤ d := by
            intro i
            fin_cases i <;> simp [shift, Nat.le_of_not_gt h0,
              Nat.le_of_not_gt h1]
          exact (h hle).elim
  have hker : RingHom.ker phi = aXYIdeal k p := by
    apply le_antisymm
    · intro z hz
      have hz' : phi z = 0 := hz
      have hz'' : (xMap z, yMap z) = (0, 0) := by
        have h := congrArg Subtype.val hz'
        change (xMap z, yMap z) = (0, 0) at h
        exact h
      have hxzero : xMap z = 0 := congrArg Prod.fst hz''
      have hyzero : yMap z = 0 := congrArg Prod.snd hz''
      have hrzero : r (z : TwoVariablePowerSeries k) = 0 := by
        exact congrArg Subtype.val hxzero
      have hr'zero : r' (z : TwoVariablePowerSeries k) = 0 := by
        exact congrArg Subtype.val hyzero
      have hzero0 : ∀ d : Fin 2 →₀ ℕ, d 0 < 1 →
          MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) = 0 := by
        intro d hd
        have hd0 : d 0 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hd)
        have heq : d = Finsupp.embDomain e' (Finsupp.single () (d 1)) := by
          ext j
          have he1 : e' () = (1 : Fin 2) := rfl
          fin_cases j <;> simp [hd0, he1]
        rw [heq]
        change PowerSeries.coeff (d 1) (r' (z : TwoVariablePowerSeries k)) = 0
        rw [hr'zero]
        simp
      have hzero1 : ∀ d : Fin 2 →₀ ℕ, d 1 < 1 →
          MvPowerSeries.coeff d (z : TwoVariablePowerSeries k) = 0 := by
        intro d hd
        have hd1 : d 1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hd)
        have heq : d = Finsupp.embDomain e (Finsupp.single () (d 0)) := by
          ext j
          have he0 : e () = (0 : Fin 2) := rfl
          fin_cases j <;> simp [hd1, he0]
        rw [heq]
        change PowerSeries.coeff (d 0) (r (z : TwoVariablePowerSeries k)) = 0
        rw [hrzero]
        simp
      obtain ⟨q, hq⟩ := hdiv z 1 hzero0 hzero1
      rw [hq]
      simpa [pow_one] using
        (Ideal.mul_mem_right q (aXYIdeal k p)
          (Ideal.subset_span (by simp only [Set.mem_singleton_iff]; rfl)))
    · intro z hz
      have hspan : Ideal.span {aX k p * aY k p} ≤ RingHom.ker phi := by
        apply Ideal.span_le.2
        rintro _ ⟨rfl⟩
        exact RingHom.mem_ker.mpr (by
          apply Subtype.ext
          dsimp [phi]
          change (xMap (aX k p * aY k p), yMap (aX k p * aY k p)) = (0, 0)
          apply Prod.ext
          · apply Subtype.ext
            change r (aX k p * aY k p) = 0
            rw [map_mul, hr_aX, hr_aY]
            simp
          · apply Subtype.ext
            change r' (aX k p * aY k p) = 0
            rw [map_mul, hr'_aX, hr'_aY]
            simp)
      exact hspan hz
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)⟩

theorem a_quotient_is_C_fiberProduct :
    Nonempty ((aRing k p ⧸ aXYIdeal k p) ≃+*
      ↥(RingHom.pullback (cConstantCoeff k p) (dConstantCoeff k p))) := by
  simpa only [cConstantCoeff, dConstantCoeff] using
    (a_quotient_is_fiberProduct k p)

theorem a_quotient_is_noetherian :
    IsNoetherianRing (aRing k p ⧸ aXYIdeal k p) := by
  let P := ↥(RingHom.pullback (badDvrConstantCoeff k p)
    (badDvrConstantCoeff k p))
  let diag : badDvrRing k p →+* P :=
    { toFun := fun c => ⟨(c, c), by rfl⟩
      map_one' := by rfl
      map_mul' := by intro c d; rfl
      map_zero' := by rfl
      map_add' := by intro c d; rfl }
  let : Algebra (badDvrRing k p) P :=
    diag.toAlgebra
  let : IsDiscreteValuationRing (badDvrRing k p) :=
    badDvrRing_isDiscreteValuationRing k p
  let gen : P :=
    ⟨(badDvrVariable k p, 0), by
      simp [badDvrVariable, badDvrConstantCoeff, PowerSeries.constantCoeff_X]⟩
  have hfg : (⊤ : Subalgebra (badDvrRing k p) P).FG := by
    apply Subalgebra.fg_def.2
    refine ⟨{gen}, Set.finite_singleton _, ?_⟩
    apply le_antisymm le_top
    intro w hw
    have hwd : PowerSeries.constantCoeff (w.1.1 : PowerSeries k) =
        PowerSeries.constantCoeff (w.1.2 : PowerSeries k) := by
      simpa [badDvrConstantCoeff] using w.property
    let diff : PowerSeries k := (w.1.1 : PowerSeries k) - w.1.2
    have hdiff : OneVariableFiniteDegree k p diff := by
      simpa [diff, sub_eq_add_neg] using
        (oneVariableFiniteDegree_add k p w.1.1.property
          (oneVariableFiniteDegree_neg k p w.1.2.property))
    let q : badDvrRing k p :=
      ⟨PowerSeries.mk fun n => PowerSeries.coeff (n + 1) diff,
        oneVariableFiniteDegree_shift k p hdiff⟩
    have hdiff_const : PowerSeries.constantCoeff diff = 0 := by
      dsimp [diff]
      rw [map_sub]
      exact sub_eq_zero.mpr hwd
    have hdiff_eq : diff = (q : PowerSeries k) * PowerSeries.X := by
      rw [PowerSeries.eq_shift_mul_X_add_const diff]
      simp [q, hdiff_const]
    have hw_eq : w = algebraMap (badDvrRing k p) P w.1.2 + gen *
        algebraMap (badDvrRing k p) P q := by
      apply Subtype.ext
      simp only [RingHom.algebraMap_toAlgebra]
      dsimp [gen, diag]
      change (w.1.1, w.1.2) =
        ((w.1.2, w.1.2) + (badDvrVariable k p, 0) * (q, q))
      apply Prod.ext
      · apply Subtype.ext
        change (w.1.1 : PowerSeries k) =
          (w.1.2 : PowerSeries k) + PowerSeries.X * (q : PowerSeries k)
        have hdiff' : (w.1.1 : PowerSeries k) - (w.1.2 : PowerSeries k) =
            PowerSeries.X * (q : PowerSeries k) := by
          simpa [diff, mul_comm] using hdiff_eq
        exact (sub_eq_iff_eq_add').mp hdiff'
      · apply Subtype.ext
        simp
    rw [hw_eq]
    exact add_mem (Subalgebra.algebraMap_mem _ _)
      (mul_mem (Algebra.subset_adjoin (by simp)) (Subalgebra.algebraMap_mem _ _))
  let : Algebra.FiniteType (badDvrRing k p) P := ⟨hfg⟩
  have hP : IsNoetherianRing P :=
    Algebra.FiniteType.isNoetherianRing (badDvrRing k p) P
  obtain ⟨e⟩ := a_quotient_is_C_fiberProduct k p
  exact @isNoetherianRing_of_ringEquiv P _ _ _ e.symm hP

theorem a_is_noetherian :
    IsNoetherianRing (aRing k p) := by
  let : IsNoetherianRing (aRing k p ⧸ aXYIdeal k p) :=
    a_quotient_is_noetherian k p
  let : IsAdicComplete (aXYIdeal k p) (aRing k p) :=
    a_is_complete k p
  exact Formalization.Books.Algebra.Unit69.isNoetherianRing_of_isAdicComplete_of_fg_quotient
    (aXYIdeal k p) (by
      change Submodule.FG
        (Ideal.span {aX k p * aY k p} :
          Submodule (aRing k p) (aRing k p))
      exact Submodule.fg_span_singleton _)

private theorem quotient_mk_isLocalHom_of_le_jacobson_bot
    {R : Type*} [CommRing R] (I : Ideal R)
    (h : I ≤ Ideal.jacobson ⊥) : IsLocalHom (Ideal.Quotient.mk I) := by
  constructor
  intro a ha
  have hbot : IsUnit (Ideal.Quotient.mk (Ideal.jacobson ⊥) a) := by
    rw [isUnit_iff_exists_inv] at ha ⊢
    obtain ⟨b, hb⟩ := ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    use Ideal.Quotient.mk _ b
    rw [← (Ideal.Quotient.mk _).map_one, ← (Ideal.Quotient.mk _).map_mul,
      Ideal.Quotient.eq] at hb ⊢
    exact h hb
  obtain ⟨⟨x, y, h1, h2⟩, rfl : x = _⟩ := hbot
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← (Ideal.Quotient.mk _).map_mul, ← (Ideal.Quotient.mk _).map_one,
    Ideal.Quotient.eq, Ideal.mem_jacobson_bot] at h1 h2
  specialize h1 1
  have h1 : IsUnit a ∧ IsUnit y := by simpa using h1
  exact h1.1

theorem a_is_local :
    IsLocalRing (aRing k p) := by
  let : IsDiscreteValuationRing (badDvrRing k p) :=
    badDvrRing_isDiscreteValuationRing k p
  let : IsLocalRing (badDvrRing k p) := by infer_instance
  let : IsLocalHom (badDvrConstantCoeff k p) :=
    { map_nonunit := by
        intro z hz
        apply oneVariableFiniteDegree_isUnit_of_constantCoeff_ne_zero k p z.property
        exact (isUnit_iff_ne_zero.mp hz) }
  let P := ↥(RingHom.pullback (badDvrConstantCoeff k p)
    (badDvrConstantCoeff k p))
  let : IsLocalRing P :=
    RingHom.isLocalRing_pullback (badDvrConstantCoeff k p)
      (badDvrConstantCoeff k p)
  obtain ⟨e⟩ := a_quotient_is_C_fiberProduct k p
  let : Nontrivial (aRing k p ⧸ aXYIdeal k p) :=
    e.symm.injective.nontrivial
  let : IsLocalRing (aRing k p ⧸ aXYIdeal k p) := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro a
    have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (e a)
    rcases h with h | h
    · left
      have h' : IsUnit (e.symm (e a)) := IsUnit.map e.symm h
      simpa using h'
    · right
      have h' : IsUnit (e.symm (1 - e a)) := IsUnit.map e.symm h
      simpa only [map_sub, map_one, e.symm_apply_apply] using h'
  let : IsAdicComplete (aXYIdeal k p) (aRing k p) :=
    a_is_complete k p
  let : IsLocalHom (Ideal.Quotient.mk (aXYIdeal k p)) :=
    quotient_mk_isLocalHom_of_le_jacobson_bot (aXYIdeal k p)
      (IsAdicComplete.le_jacobson_bot (aXYIdeal k p))
  exact RingHom.domain_isLocalRing (Ideal.Quotient.mk (aXYIdeal k p))

theorem aMaximalIdeal_is_maximal :
    (aMaximalIdeal k p).IsMaximal := by
  sorry

theorem a_is_domain :
    IsDomain (aRing k p) := by
  sorry

theorem ambient_power_mem_aSubring (g : TwoVariablePowerSeries k) :
    g ^ p ∈ aSubring k p := by
  sorry

theorem ambient_is_integral_over_a :
    Algebra.IsIntegral (aRing k p) (TwoVariablePowerSeries k) := by
  sorry

theorem a_krull_dimension :
    ringKrullDim (aRing k p) = (2 : WithBot ℕ∞) := by
  sorry

theorem ambient_krull_dimension :
    ringKrullDim (TwoVariablePowerSeries k) = (2 : WithBot ℕ∞) := by
  sorry

theorem a_krull_dimension_from_integral_subring :
    ringKrullDim (aRing k p) = ringKrullDim (TwoVariablePowerSeries k) := by
  sorry

theorem aXYIdeal_is_principal :
    Submodule.IsPrincipal (aXYIdeal k p : Submodule (aRing k p) (aRing k p)) := by
  change Submodule.IsPrincipal
    (Ideal.span {aX k p * aY k p} : Submodule (aRing k p) (aRing k p))
  infer_instance

end TheRingA

section TheFiniteExtension

variable (k : Type u) (p : ℕ) [Field k] [Fact p.Prime] [CharP k p]

/-- Embed a one-variable series as a series in `x` with no `y` terms. -/
def embedOneVariableSeries (f : PowerSeries k) : TwoVariablePowerSeries k :=
  MvPowerSeries.rename (R := k) (fun _ : Unit => (0 : Fin 2)) f

def InfiniteCoefficientDegree (f : PowerSeries k) : Prop :=
  ¬ OneVariableFiniteDegree k p f

/-- An infinite purely inseparable coefficient extension supplies a one-variable
series whose coefficients are not contained in any finite intermediate
extension.  This is the existence step implicit in the choice of `f` in the
source example. -/
theorem exists_infiniteCoefficientDegree_series
    (h : InfiniteDegreeOverPowers k p) :
    ∃ f : PowerSeries k, InfiniteCoefficientDegree k p f := by
  sorry

theorem embeddedSeries_not_mem_aSubring (f : PowerSeries k)
    (hf : InfiniteCoefficientDegree k p f) :
    embedOneVariableSeries k f ∉ aSubring k p := by
  sorry

theorem embeddedSeries_pow_mem_aSubring (f : PowerSeries k) :
    (embedOneVariableSeries k f) ^ p ∈ aSubring k p := by
  sorry

/-- The finite extension `B = A[f]` inside the ambient bivariate series ring. -/
def bSubring (f : PowerSeries k) : Subring (TwoVariablePowerSeries k) :=
  Subring.closure ((aSubring k p : Set (TwoVariablePowerSeries k)) ∪
    {embedOneVariableSeries k f})

abbrev bRing (f : PowerSeries k) := ↥(bSubring k p f)

/-- The inclusion `A → B`. -/
def aToB (f : PowerSeries k) : aRing k p →+* bRing k p f where
  toFun a :=
    ⟨a.1, Subring.subset_closure (show a.1 ∈
      (aSubring k p : Set (TwoVariablePowerSeries k)) ∪
        {embedOneVariableSeries k f} from Or.inl a.2)⟩
  map_one' := by rfl
  map_mul' := by intro x y; rfl
  map_zero' := by rfl
  map_add' := by intro x y; rfl

noncomputable instance aAlgebraB (f : PowerSeries k) : Algebra (aRing k p) (bRing k p f) :=
  (aToB k p f).toAlgebra

def bF (f : PowerSeries k) : bRing k p f :=
  ⟨embedOneVariableSeries k f,
    Subring.subset_closure (show embedOneVariableSeries k f ∈
      (aSubring k p : Set (TwoVariablePowerSeries k)) ∪
        {embedOneVariableSeries k f} from Or.inr rfl)⟩

def bX (f : PowerSeries k) : bRing k p f :=
  aToB k p f (aX k p)

def bY (f : PowerSeries k) : bRing k p f :=
  aToB k p f (aY k p)

def bXYIdeal (f : PowerSeries k) : Ideal (bRing k p f) :=
  Ideal.span {bX k p f * bY k p f}

theorem bXYIdeal_is_principal (f : PowerSeries k) :
    (bXYIdeal k p f).IsPrincipal := by
  change (Ideal.span {bX k p f * bY k p f}).IsPrincipal
  infer_instance

abbrev bCompletion (f : PowerSeries k) : Type u :=
  AdicCompletion (bXYIdeal k p f) (bRing k p f)

theorem b_is_finite_over_a (f : PowerSeries k) :
    Module.Finite (aRing k p) (bRing k p f) := by
  sorry

theorem b_is_noetherian (f : PowerSeries k) :
    IsNoetherianRing (bRing k p f) := by
  sorry

theorem b_is_domain (f : PowerSeries k) :
    IsDomain (bRing k p f) := by
  sorry

theorem b_is_complete (f : PowerSeries k) :
    IsAdicComplete (bXYIdeal k p f) (bRing k p f) := by
  sorry

def bPower (f : PowerSeries k) (i : Fin p) : bRing k p f :=
  bF k p f ^ (i : ℕ)

theorem exists_b_power_basis (f : PowerSeries k)
    (hf : InfiniteCoefficientDegree k p f) :
    ∃ e : Module.Basis (Fin p) (aRing k p) (bRing k p f),
      ∀ i, e i = bPower k p f i := by
  sorry

end TheFiniteExtension

section LocalizedCompletions

variable (k : Type u) (p : ℕ) [Field k] [Fact p.Prime] [CharP k p]
variable (f : PowerSeries k)

abbrev aLocalizedRing : Type u := Localization.Away (aY k p)
abbrev bLocalizedRing : Type u :=
  Localization.Away (bY k p f)

def aLocalizedX : aLocalizedRing k p :=
  algebraMap (aRing k p) (aLocalizedRing k p) (aX k p)

def aLocalizedXYIdeal : Ideal (aLocalizedRing k p) :=
  Ideal.map (algebraMap (aRing k p) (aLocalizedRing k p)) (aXYIdeal k p)

def aLocalizedIdeal : Ideal (aLocalizedRing k p) :=
  Ideal.span {aLocalizedX k p}

abbrev aLocalizedCompletion : Type u :=
  Formalization.Books.Examples.Unit12.localizedAdicCompletion
    (aRing k p) (aXYIdeal k p) (aY k p)

def bLocalizedXYIdeal : Ideal (bLocalizedRing k p f) :=
  Ideal.map (algebraMap (bRing k p f) (bLocalizedRing k p f)) (bXYIdeal k p f)

def bLocalizedIdeal : Ideal (bLocalizedRing k p f) :=
  Ideal.span {algebraMap (bRing k p f) (bLocalizedRing k p f) (bX k p f)}

abbrev bLocalizedCompletion : Type u :=
  Formalization.Books.Examples.Unit12.localizedAdicCompletion
    (bRing k p f) (bXYIdeal k p f) (bY k p f)

theorem aLocalizedXYIdeal_eq_x :
    aLocalizedXYIdeal k p = aLocalizedIdeal k p := by
  sorry

theorem bLocalizedXYIdeal_eq_x :
    bLocalizedXYIdeal k p f = bLocalizedIdeal k p f := by
  sorry

theorem localized_power_formula (n : ℕ) :
    (aLocalizedXYIdeal k p) ^ n = (aLocalizedIdeal k p) ^ n := by
  sorry

theorem localized_b_power_formula (n : ℕ) :
    (bLocalizedXYIdeal k p f) ^ n = (bLocalizedIdeal k p f) ^ n := by
  sorry

theorem a_localized_completion_inverse_limit_description :
    Nonempty (aLocalizedCompletion k p ≃+*
      AdicCompletion (aLocalizedIdeal k p) (aLocalizedRing k p)) := by
  sorry

theorem b_localized_completion_inverse_limit_description :
    Nonempty (bLocalizedCompletion k p f ≃+*
      AdicCompletion (bLocalizedIdeal k p f) (bLocalizedRing k p f)) := by
  sorry

noncomputable def aLocalizedToBLocalized :
    aLocalizedRing k p →+* bLocalizedRing k p f :=
  IsLocalization.Away.map (Localization.Away (aY k p))
    (Localization.Away (aToB k p f (aY k p))) (aToB k p f) (aY k p)

/-- The adjoined series after localizing `B` at `y`. -/
def localizedRingF : bLocalizedRing k p f :=
  algebraMap (bRing k p f) (bLocalizedRing k p f) (bF k p f)

theorem exists_localized_ring_power_basis
    (hf : InfiniteCoefficientDegree k p f) :
    letI : Algebra (aLocalizedRing k p) (bLocalizedRing k p f) :=
      (aLocalizedToBLocalized k p f).toAlgebra
    ∃ e : Module.Basis (Fin p) (aLocalizedRing k p) (bLocalizedRing k p f),
      ∀ i, e i = localizedRingF k p f ^ (i : ℕ) := by
  sorry

theorem exists_localized_completion_map :
    ∃ φ : aLocalizedCompletion k p →+* bLocalizedCompletion k p f,
      ∀ z : aLocalizedRing k p,
        φ (algebraMap (aLocalizedRing k p) (aLocalizedCompletion k p) z) =
          algebraMap (bLocalizedRing k p f) (bLocalizedCompletion k p f)
            (aLocalizedToBLocalized k p f z) := by
  sorry

noncomputable def localizedCompletionMap :
    aLocalizedCompletion k p →+* bLocalizedCompletion k p f :=
  Classical.choose (exists_localized_completion_map k p f)

/-- The image of the adjoined series `f` in the completed localization. -/
def localizedCompletionF : bLocalizedCompletion k p f :=
  algebraMap (bRing k p f) (bLocalizedCompletion k p f) (bF k p f)

theorem localizedCompletionMap_spec (z : aLocalizedRing k p) :
    localizedCompletionMap k p f
        (algebraMap (aLocalizedRing k p) (aLocalizedCompletion k p) z) =
      algebraMap (bLocalizedRing k p f) (bLocalizedCompletion k p f)
        (aLocalizedToBLocalized k p f z) := by
  exact Classical.choose_spec (exists_localized_completion_map k p f) z

theorem exists_localized_completion_power_basis
    (hf : InfiniteCoefficientDegree k p f) :
    letI : Algebra (aLocalizedCompletion k p) (bLocalizedCompletion k p f) :=
      (localizedCompletionMap k p f).toAlgebra
      ∃ e : Module.Basis (Fin p) (aLocalizedCompletion k p)
        (bLocalizedCompletion k p f),
      ∀ i, e i = localizedCompletionF k p f ^ (i : ℕ) := by
  sorry

abbrev truncatedPolynomial (R : Type u) [CommRing R] (p : ℕ) : Type u :=
  Polynomial R ⧸ Ideal.span {(Polynomial.X : Polynomial R) ^ p}

abbrev completionRelationQuotient (R : Type u) [CommRing R] (p : ℕ) (g : R) : Type u :=
  Polynomial R ⧸
    Ideal.span {(Polynomial.X : Polynomial R) ^ p - Polynomial.C (g ^ p)}

theorem exists_g_in_localized_completion
    (hf : InfiniteCoefficientDegree k p f) :
    ∃ g : aLocalizedCompletion k p,
      localizedCompletionMap k p f g ^ p =
        localizedCompletionF k p f ^ p := by
  sorry

theorem localized_completion_is_truncated_polynomial
    (hf : InfiniteCoefficientDegree k p f) :
    Nonempty (bLocalizedCompletion k p f ≃+*
      truncatedPolynomial (aLocalizedCompletion k p) p) := by
  sorry

theorem localized_completion_is_quotient_by_frobenius_relation
    (hf : InfiniteCoefficientDegree k p f) :
    ∃ g : aLocalizedCompletion k p,
      Nonempty (bLocalizedCompletion k p f ≃+*
        completionRelationQuotient (aLocalizedCompletion k p) p g) := by
  sorry

theorem localized_completion_is_nonreduced
    (hf : InfiniteCoefficientDegree k p f) :
    ¬ IsReduced (bLocalizedCompletion k p f) := by
  sorry

theorem a_localized_completion_is_DVR :
    ∃ h : IsDomain (aLocalizedCompletion k p),
      ∃ h' : @IsDiscreteValuationRing (aLocalizedCompletion k p) inferInstance h,
        letI : IsDomain (aLocalizedCompletion k p) := h
        letI : IsDiscreteValuationRing (aLocalizedCompletion k p) := h'
        IsLocalRing.maximalIdeal (aLocalizedCompletion k p) =
          Ideal.span {algebraMap (aLocalizedRing k p) (aLocalizedCompletion k p)
            (aLocalizedX k p)} := by
  sorry

theorem a_localized_completion_residue_field :
    ∃ h : IsDomain (aLocalizedCompletion k p),
      ∃ h' : @IsDiscreteValuationRing (aLocalizedCompletion k p) inferInstance h,
        letI : IsDomain (aLocalizedCompletion k p) := h
        letI : IsDiscreteValuationRing (aLocalizedCompletion k p) := h'
        Nonempty ((aLocalizedCompletion k p ⧸
          Ideal.span {algebraMap (aLocalizedRing k p) (aLocalizedCompletion k p)
            (aLocalizedX k p)}) ≃+*
          FractionRing (badDvrRing k p)) := by
  sorry

abbrev bCompletionAtB : Type u :=
  Localization.Away
    (algebraMap (bLocalizedRing k p f) (bLocalizedCompletion k p f)
      (algebraMap (bRing k p f) (bLocalizedRing k p f)
        (bX k p f * bY k p f)))

theorem completion_after_inverting_xy_is_nonreduced
    (hf : InfiniteCoefficientDegree k p f) :
    ¬ IsReduced (bCompletionAtB k p f) := by
  sorry

end LocalizedCompletions

section FinalExistence

/-- The `I`-adic completion of the localization of a ring at `f`. -/
abbrev principalLocalizationCompletion (B : CommRingCat.{u})
    (I : Ideal (B : Type u)) (f : (B : Type u)) : Type u :=
  Formalization.Books.Examples.Unit12.localizedAdicCompletion
    (B : Type u) I f

/-- The localization of the preceding completion at the image of `b`. -/
abbrev principalLocalizationCompletionAt (B : CommRingCat.{u})
    (I : Ideal (B : Type u)) (f b : (B : Type u)) : Type u :=
  Localization.Away
    (algebraMap (Localization.Away f)
      (principalLocalizationCompletion B I f)
      (algebraMap (B : Type u) (Localization.Away f) b))

theorem exists_local_noetherian_two_dimensional_domain_with_nonreduced_completion :
    ∃ (B : CommRingCat.{u}) (m I : Ideal (B : Type u)) (b f : (B : Type u)),
      m.IsMaximal ∧
        IsLocalRing (B : Type u) ∧
        IsDomain (B : Type u) ∧
        IsNoetherianRing (B : Type u) ∧
        ringKrullDim (B : Type u) = (2 : WithBot ℕ∞) ∧
        I = Ideal.span {b} ∧
        IsAdicComplete I (B : Type u) ∧
        f ∈ m ∧
        f ∉ I ∧
        ¬ IsReduced (principalLocalizationCompletion B I f) ∧
        ¬ IsReduced (principalLocalizationCompletionAt B I f b) := by
  sorry

end FinalExistence

end

end Formalization.Books.Examples.Unit18
