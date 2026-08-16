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
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Another local ring with nonreduced completion

This file formalizes the precise statements in Section 18 of
`books/examples.tex`.  The constructions use the existing Mathlib power-series,
localization, and adic-completion APIs; proposition proofs are left for the
proving stage.
-/

namespace Formalization.«Books.Examples».Unit18

noncomputable section

universe u

section CoefficientFields

variable (k : Type u) (p : ℕ) [Field k] [Fact p.Prime] [CharP k p]

/-- The subfield of `p`th powers, represented by the Frobenius field range. -/
def pPowerSubfield : Subfield k :=
  (frobenius k p).fieldRange

/-- A set of elements is contained in a finite extension of `k ^ p`. -/
def FiniteDegreeOverPowers (s : Set k) : Prop :=
  ∃ F : IntermediateField (pPowerSubfield k p) k,
    s ⊆ (F : Set k) ∧ Module.Finite (pPowerSubfield k p) F

/-- The hypothesis that `k` has infinite degree over its `p`th-power field. -/
def InfiniteDegreeOverPowers : Prop :=
  ¬ Module.Finite (pPowerSubfield k p) k

/-- The coefficient condition used for the one-variable bad DVR. -/
def OneVariableFiniteDegree (f : PowerSeries k) : Prop :=
  FiniteDegreeOverPowers k p (Set.range (fun i : ℕ => PowerSeries.coeff i f))

theorem oneVariableFiniteDegree_zero :
    OneVariableFiniteDegree k p 0 := by
  sorry

theorem oneVariableFiniteDegree_one :
    OneVariableFiniteDegree k p 1 := by
  sorry

theorem oneVariableFiniteDegree_add {f g : PowerSeries k}
    (hf : OneVariableFiniteDegree k p f)
    (hg : OneVariableFiniteDegree k p g) :
    OneVariableFiniteDegree k p (f + g) := by
  sorry

theorem oneVariableFiniteDegree_mul {f g : PowerSeries k}
    (hf : OneVariableFiniteDegree k p f)
    (hg : OneVariableFiniteDegree k p g) :
    OneVariableFiniteDegree k p (f * g) := by
  sorry

theorem oneVariableFiniteDegree_neg {f : PowerSeries k}
    (hf : OneVariableFiniteDegree k p f) :
    OneVariableFiniteDegree k p (-f) := by
  sorry

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
  sorry

/-- The image of the variable in the bad one-variable subring. -/
def badDvrVariable : badDvrRing k p :=
  ⟨PowerSeries.X, oneVariableFiniteDegree_X k p⟩

theorem badDvrRing_isDiscreteValuationRing :
    IsDiscreteValuationRing (badDvrRing k p) := by
  sorry

def pPowerSeriesSubring1 : Subring (PowerSeries k) :=
  (PowerSeries.map (pPowerSubfield k p).subtype).range

theorem pPowerSeriesSubring1_le_badDvrSubring :
    pPowerSeriesSubring1 k p ≤ badDvrSubring k p := by
  sorry

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
  sorry

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
  sorry

theorem aCondition_one :
    ACondition k p 1 := by
  sorry

theorem aCondition_add {f g : TwoVariablePowerSeries k}
    (hf : ACondition k p f) (hg : ACondition k p g) :
    ACondition k p (f + g) := by
  sorry

theorem aCondition_mul {f g : TwoVariablePowerSeries k}
    (hf : ACondition k p f) (hg : ACondition k p g) :
    ACondition k p (f * g) := by
  sorry

theorem aCondition_neg {f : TwoVariablePowerSeries k}
    (hf : ACondition k p f) :
    ACondition k p (-f) := by
  sorry

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

theorem pPowerSeriesSubring_le_aSubring :
    pPowerSeriesSubring k p ≤ aSubring k p := by
  sorry

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
  sorry

theorem diagonalBlock_spec_right (f : TwoVariablePowerSeries k) (n j : ℕ) :
    PowerSeries.coeff j (diagonalBlock k f n).2 = coefficientXY k f n (n + j) := by
  sorry

theorem diagonalBlocks_unique (f : TwoVariablePowerSeries k) :
    ∃! blocks : ℕ → PowerSeries k × PowerSeries k,
      (∀ n i, PowerSeries.coeff i (blocks n).1 = coefficientXY k f (n + i) n) ∧
        ∀ n j, PowerSeries.coeff j (blocks n).2 = coefficientXY k f n (n + j) := by
  sorry

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
  sorry

def diagonalExpansion (blocks : ℕ → PowerSeries k × PowerSeries k) :
    TwoVariablePowerSeries k :=
  fun d => diagonalExpansionCoeff k blocks d

theorem diagonalExpansion_diagonalBlocks (f : TwoVariablePowerSeries k) :
    diagonalExpansion k (diagonalBlock k f) = f := by
  sorry

theorem aCondition_iff_diagonalBlocks (f : TwoVariablePowerSeries k) :
    ACondition k p f ↔
      ∀ n : ℕ, FiniteDegreeOverPowers k p (diagonalBlockCoefficients k f n) := by
  sorry

end TwoVariableSeries

section TheRingA

variable (k : Type u) (p : ℕ) [Field k] [Fact p.Prime] [CharP k p]

theorem x_mem_aSubring :
    (MvPowerSeries.X 0 : TwoVariablePowerSeries k) ∈ aSubring k p := by
  sorry

theorem y_mem_aSubring :
    (MvPowerSeries.X 1 : TwoVariablePowerSeries k) ∈ aSubring k p := by
  sorry

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
  sorry

theorem a_quotient_is_fiberProduct :
    Nonempty ((aRing k p ⧸ aXYIdeal k p) ≃+*
      ↥(RingHom.pullback (badDvrConstantCoeff k p) (badDvrConstantCoeff k p))) := by
  sorry

theorem a_quotient_is_C_fiberProduct :
    Nonempty ((aRing k p ⧸ aXYIdeal k p) ≃+*
      ↥(RingHom.pullback (cConstantCoeff k p) (dConstantCoeff k p))) := by
  sorry

theorem a_quotient_is_noetherian :
    IsNoetherianRing (aRing k p ⧸ aXYIdeal k p) := by
  sorry

theorem a_is_noetherian :
    IsNoetherianRing (aRing k p) := by
  sorry

theorem a_is_local :
    IsLocalRing (aRing k p) := by
  sorry

theorem aMaximalIdeal_is_maximal :
    (aMaximalIdeal k p).IsMaximal := by
  sorry

theorem a_is_domain :
    IsDomain (aRing k p) := by
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
  sorry

end TheRingA

section TheFiniteExtension

variable (k : Type u) (p : ℕ) [Field k] [Fact p.Prime] [CharP k p]

/-- Embed a one-variable series as a series in `x` with no `y` terms. -/
def embedOneVariableSeries (f : PowerSeries k) : TwoVariablePowerSeries k :=
  MvPowerSeries.rename (R := k) (fun _ : Unit => (0 : Fin 2)) f

def InfiniteCoefficientDegree (f : PowerSeries k) : Prop :=
  ¬ OneVariableFiniteDegree k p f

theorem embeddedSeries_not_mem_aSubring (f : PowerSeries k)
    (hf : InfiniteCoefficientDegree k p f) :
    embedOneVariableSeries k f ∉ aSubring k p := by
  sorry

theorem embeddedSeries_pow_mem_aSubring (f : PowerSeries k)
    (hf : InfiniteCoefficientDegree k p f) :
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

abbrev bCompletion (f : PowerSeries k) : Type u :=
  AdicCompletion (bXYIdeal k p f) (bRing k p f)

theorem b_is_finite_over_a (f : PowerSeries k)
    (hf : InfiniteCoefficientDegree k p f) :
    Module.Finite (aRing k p) (bRing k p f) := by
  sorry

theorem b_is_noetherian (f : PowerSeries k)
    (hf : InfiniteCoefficientDegree k p f) :
    IsNoetherianRing (bRing k p f) := by
  sorry

theorem b_is_domain (f : PowerSeries k)
    (hf : InfiniteCoefficientDegree k p f) :
    IsDomain (bRing k p f) := by
  sorry

theorem b_is_complete (f : PowerSeries k)
    (hf : InfiniteCoefficientDegree k p f) :
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
  Localization.Away (aToB k p f (aY k p))

def aLocalizedX : aLocalizedRing k p :=
  algebraMap (aRing k p) (aLocalizedRing k p) (aX k p)

def aLocalizedXYIdeal : Ideal (aLocalizedRing k p) :=
  Ideal.map (algebraMap (aRing k p) (aLocalizedRing k p)) (aXYIdeal k p)

def aLocalizedIdeal : Ideal (aLocalizedRing k p) :=
  Ideal.span {aLocalizedX k p}

abbrev aLocalizedCompletion : Type u :=
  AdicCompletion (aLocalizedIdeal k p) (aLocalizedRing k p)

def bLocalizedXYIdeal : Ideal (bLocalizedRing k p f) :=
  Ideal.map (algebraMap (bRing k p f) (bLocalizedRing k p f)) (bXYIdeal k p f)

def bLocalizedIdeal : Ideal (bLocalizedRing k p f) :=
  Ideal.span {algebraMap (bRing k p f) (bLocalizedRing k p f) (bX k p f)}

abbrev bLocalizedCompletion : Type u :=
  AdicCompletion (bLocalizedIdeal k p f) (bLocalizedRing k p f)

theorem aLocalizedXYIdeal_eq_x :
    aLocalizedXYIdeal k p = aLocalizedIdeal k p := by
  sorry

theorem bLocalizedXYIdeal_eq_x :
    bLocalizedXYIdeal k p f = bLocalizedIdeal k p f := by
  sorry

theorem localized_power_quotient_formula (n : ℕ) :
    (aLocalizedXYIdeal k p) ^ n = (aLocalizedIdeal k p) ^ n := by
  sorry

theorem localized_b_power_quotient_formula (n : ℕ) :
    (bLocalizedXYIdeal k p f) ^ n = (bLocalizedIdeal k p f) ^ n := by
  sorry

theorem a_localized_completion_inverse_limit_description :
    Nonempty (aLocalizedCompletion k p ≃+*
      AdicCompletion (aLocalizedIdeal k p) (aLocalizedRing k p)) := by
  exact ⟨RingEquiv.refl _⟩

theorem b_localized_completion_inverse_limit_description :
    Nonempty (bLocalizedCompletion k p f ≃+*
      AdicCompletion (bLocalizedIdeal k p f) (bLocalizedRing k p f)) := by
  exact ⟨RingEquiv.refl _⟩

noncomputable def aLocalizedToBLocalized :
    aLocalizedRing k p →+* bLocalizedRing k p f :=
  IsLocalization.Away.map (Localization.Away (aY k p))
    (Localization.Away (aToB k p f (aY k p))) (aToB k p f) (aY k p)

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
      ∀ i, e i =
        (algebraMap (bRing k p f) (bLocalizedCompletion k p f) (bF k p f)) ^ (i : ℕ) := by
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
        (algebraMap (bRing k p f) (bLocalizedCompletion k p f) (bF k p f)) ^ p := by
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

theorem a_localized_completion_is_DVR
    (hf : InfiniteCoefficientDegree k p f) :
    ∃ h : IsDomain (aLocalizedCompletion k p),
      ∃ h' : @IsDiscreteValuationRing (aLocalizedCompletion k p) inferInstance h,
        letI : IsDomain (aLocalizedCompletion k p) := h
        letI : IsDiscreteValuationRing (aLocalizedCompletion k p) := h'
        IsLocalRing.maximalIdeal (aLocalizedCompletion k p) =
          Ideal.span {algebraMap (aLocalizedRing k p) (aLocalizedCompletion k p)
            (aLocalizedX k p)} := by
  sorry

theorem a_localized_completion_residue_field
    (hf : InfiniteCoefficientDegree k p f) :
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
  AdicCompletion
    (Ideal.map (algebraMap (B : Type u) (Localization.Away f)) I)
    (Localization.Away f)

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

end Formalization.«Books.Examples».Unit18
