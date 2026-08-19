import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Data.Complex.Basic
import Mathlib.Data.PNat.Notation
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Noetherian.OfPrime
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Examples, Chapter 17: Local rings with nonreduced completion

This file records the Ferrand--Raynaud construction from the source section.
Mathlib has formal and Laurent power series, but it does not have a built-in
ring of convergent power series.  `ConvergentPowerSeriesRing` is therefore the
small interface for that analytic ring; the algebraic part of the construction
below is defined from it and from Mathlib's canonical power-series APIs.
-/

noncomputable section

open scoped LaurentSeries

namespace Formalization.Books.Examples.Unit17

universe u v

/-! ## The analytic and formal series rings -/

/-- The positive-radius condition on a formal scalar power series. -/
def IsConvergentPowerSeries (f : PowerSeries ℂ) : Prop :=
  0 < (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n f)).radius

/-- Positive natural numbers, used for the sequence `f₁, f₂, ...`. -/
abbrev PositiveNat := ℕ+

/--
The analytic ring `ℂ\{x\}` together with the facts about it used in the
Ferrand--Raynaud example.

The `expansion` map records the Taylor-series inclusion into `ℂ[[x]]`.
`localization_is_fraction_ring` expresses that inverting `x` gives the field
of convergent Laurent series, and `completion` records the usual completion
identification with formal power series.
-/
structure ConvergentPowerSeriesRing where
  carrier : Type u
  [commRing : CommRing carrier]
  [isDomain : IsDomain carrier]
  [complexAlgebra : Algebra ℂ carrier]
  x : carrier
  expansion : carrier →ₐ[ℂ] PowerSeries ℂ
  expansion_injective : Function.Injective expansion
  expansion_convergent : ∀ c, IsConvergentPowerSeries (expansion c)
  expansion_x : expansion x = PowerSeries.X
  /-- Every convergent series is its constant term plus an `x`-multiple. -/
  exists_eq_algebraMap_add_x_mul :
    ∀ c, ∃ z : ℂ, ∃ g : carrier,
      c = algebraMap ℂ carrier z + x * g
  localization_is_fraction_ring :
    IsFractionRing carrier (Localization.Away x)
  completion :
    Nonempty
      (PowerSeries ℂ ≃ₐ[ℂ]
        AdicCompletion (Ideal.span ({x} : Set carrier)) carrier)

attribute [instance] ConvergentPowerSeriesRing.commRing
  ConvergentPowerSeriesRing.isDomain ConvergentPowerSeriesRing.complexAlgebra

/-- The fraction field of the analytic power-series ring. -/
abbrev convergentPowerSeriesFractionField (C : ConvergentPowerSeriesRing) :=
  FractionRing C.carrier

/-- The Laurent-series target `ℂ((x))`. -/
abbrev FormalLaurentSeries := LaurentSeries ℂ

/-- The formal power-series target `ℂ[[x]]`. -/
abbrev FormalPowerSeries := PowerSeries ℂ

/-- The canonical inclusion of formal power series into formal Laurent series. -/
def formalPowerSeriesToLaurent : FormalPowerSeries →+* FormalLaurentSeries :=
  algebraMap FormalPowerSeries FormalLaurentSeries

/-- The Taylor inclusion of the analytic ring into formal Laurent series. -/
def convergentToLaurent (C : ConvergentPowerSeriesRing) :
    C.carrier →+* FormalLaurentSeries :=
  formalPowerSeriesToLaurent.comp C.expansion.toRingHom

instance convergentPowerSeriesLaurentAlgebra (C : ConvergentPowerSeriesRing) :
    Algebra C.carrier FormalLaurentSeries :=
  RingHom.toAlgebra (convergentToLaurent C)

/-! ## The chosen differentials -/

/-- The `C`-submodule of `ℂ((x))` represented by formal power series. -/
def formalPowerSeriesSubmodule (C : ConvergentPowerSeriesRing) :
    Submodule C.carrier FormalLaurentSeries :=
  Submodule.span C.carrier
    (Set.range (fun f : FormalPowerSeries => formalPowerSeriesToLaurent f))

/-- A useful interface lemma for reading membership in the formal submodule. -/
theorem mem_formalPowerSeriesSubmodule_iff (C : ConvergentPowerSeriesRing)
    (z : FormalLaurentSeries) :
    z ∈ formalPowerSeriesSubmodule C ↔
      ∃ f : FormalPowerSeries, formalPowerSeriesToLaurent f = z := by
  constructor
  · intro hz
    refine Submodule.span_induction (fun x hx => ?_) ?_ ?_ ?_ hz
    · rcases hx with ⟨f, rfl⟩
      exact ⟨f, rfl⟩
    · exact ⟨0, by simp⟩
    · rintro x y _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
      exact ⟨f + g, by simp [formalPowerSeriesToLaurent]⟩
    · rintro a x _ ⟨f, rfl⟩
      refine ⟨C.expansion a * f, ?_⟩
      change formalPowerSeriesToLaurent (C.expansion a * f) =
        formalPowerSeriesToLaurent (C.expansion a) *
          formalPowerSeriesToLaurent f
      rw [map_mul]
  · rintro ⟨f, rfl⟩
    exact Submodule.subset_span ⟨f, rfl⟩

/--
The derivation and the sequence `f_n` used in the construction.  The basis
field is the source statement that `dx, df₁, df₂, ...` are part of a basis of
`Ω_{K/ℂ}`.
-/
structure FerrandRaynaudDifferentialData (C : ConvergentPowerSeriesRing) where
  f : PositiveNat → C.carrier
  f_mem : ∀ n, f n ∈ Ideal.span ({C.x} : Set C.carrier)
  derivation : Derivation ℂ C.carrier FormalLaurentSeries
  derivation_x : derivation C.x = 0
  /- The source writes `D(f_i) = x⁻ⁿ`; the later calculation and indexing
     make the intended statement `D(f_n) = x⁻ⁿ` for every positive `n`. -/
  derivation_f : ∀ n,
    derivation (f n) = (convergentToLaurent C C.x)⁻¹ ^ (n : ℕ)
  K : Type u
  [fieldK : Field K]
  [algebraCK : Algebra C.carrier K]
  [algebraComplexK : Algebra ℂ K]
  [towerK : IsScalarTower ℂ C.carrier K]
  localization_equiv :
    Nonempty (Localization.Away C.x ≃ₐ[C.carrier] K)
  differential_basis :
      ∃ (ι : Type u), Infinite ι ∧
      ∃ b : Module.Basis ι K (Ω[K⁄ℂ]),
        ∃ i₀ : ι, ∃ j : PositiveNat → ι,
          Function.Injective j ∧
            (∀ n, j n ≠ i₀) ∧
              b i₀ = KaehlerDifferential.D ℂ K
                (algebraMap C.carrier K C.x) ∧
                (∀ n, b (j n) = KaehlerDifferential.D ℂ K
                  (algebraMap C.carrier K (f n)))

attribute [instance] FerrandRaynaudDifferentialData.fieldK
  FerrandRaynaudDifferentialData.algebraCK
  FerrandRaynaudDifferentialData.algebraComplexK
  FerrandRaynaudDifferentialData.towerK

/-- The differential module in the source is infinite-dimensional over `K`.

The chosen basis in `FerrandRaynaudDifferentialData.differential_basis` is the
source-facing witness; this theorem records the assertion in its usual
Mathlib form as well.
-/
theorem ferrandRaynaudDifferential_infinite_dimensional
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    ¬ Module.Finite Δ.K (Ω[Δ.K⁄ℂ]) := by
  rcases Δ.differential_basis with ⟨ι, hι, b, i₀, j, hj, hji, hbi₀, hbj⟩
  exact Module.not_finite_of_infinite_basis b

/-! ## The local ring `A` -/

/-- The differential-integral subalgebra `A = {f | D(f) ∈ ℂ[[x]]}`. -/
def localCompletionSubalgebra (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) : Subalgebra ℂ C.carrier where
  carrier := {f | Δ.derivation f ∈ formalPowerSeriesSubmodule C}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change Δ.derivation (a + b) ∈ formalPowerSeriesSubmodule C
    change Δ.derivation a ∈ formalPowerSeriesSubmodule C at ha
    change Δ.derivation b ∈ formalPowerSeriesSubmodule C at hb
    rw [map_add]
    exact (formalPowerSeriesSubmodule C).add_mem ha hb
  one_mem' := by
    change Δ.derivation 1 ∈ formalPowerSeriesSubmodule C
    rw [Derivation.map_one_eq_zero]
    exact (formalPowerSeriesSubmodule C).zero_mem
  mul_mem' := by
    intro a b ha hb
    change Δ.derivation (a * b) ∈ formalPowerSeriesSubmodule C
    change Δ.derivation a ∈ formalPowerSeriesSubmodule C at ha
    change Δ.derivation b ∈ formalPowerSeriesSubmodule C at hb
    rw [Derivation.leibniz]
    exact (formalPowerSeriesSubmodule C).add_mem
      ((formalPowerSeriesSubmodule C).smul_mem a hb)
      ((formalPowerSeriesSubmodule C).smul_mem b ha)
  algebraMap_mem' := by
    intro c
    change Δ.derivation (algebraMap ℂ C.carrier c) ∈ formalPowerSeriesSubmodule C
    rw [Derivation.map_algebraMap]
    exact (formalPowerSeriesSubmodule C).zero_mem

/-- The ring underlying `A`. -/
def localCompletionRing (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :=
  (localCompletionSubalgebra C Δ : Type)

instance localCompletionRing_commRing (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) : CommRing (localCompletionRing C Δ) := by
  unfold localCompletionRing
  infer_instance

instance localCompletionRing_algebra_complex (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) : Algebra ℂ (localCompletionRing C Δ) := by
  unfold localCompletionRing
  infer_instance

instance localCompletionRing_algebra_carrier (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    Algebra (localCompletionRing C Δ) C.carrier := by
  unfold localCompletionRing
  infer_instance

instance localCompletionRing_isDomain (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) : IsDomain (localCompletionRing C Δ) := by
  unfold localCompletionRing
  infer_instance

instance localCompletionRing_algebra_self (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    Algebra (localCompletionRing C Δ) (localCompletionRing C Δ) :=
  Algebra.id _

/-- The power-series-valued restriction of `Δ.derivation` to `A`. -/
noncomputable def localCompletionDerivation
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (a : localCompletionRing C Δ) : FormalPowerSeries :=
  Classical.choose
    ((mem_formalPowerSeriesSubmodule_iff C
        (Δ.derivation (show localCompletionSubalgebra C Δ from a).1)).mp
      (show Δ.derivation (show localCompletionSubalgebra C Δ from a).1 ∈
          formalPowerSeriesSubmodule C from
        a.property))

theorem localCompletionDerivation_spec
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (a : localCompletionRing C Δ) :
    formalPowerSeriesToLaurent (localCompletionDerivation C Δ a) =
      Δ.derivation (show localCompletionSubalgebra C Δ from a).1 := by
  exact Classical.choose_spec
    ((mem_formalPowerSeriesSubmodule_iff C
        (Δ.derivation (show localCompletionSubalgebra C Δ from a).1)).mp
      (show Δ.derivation (show localCompletionSubalgebra C Δ from a).1 ∈
          formalPowerSeriesSubmodule C from
        a.property))

/-- The element `x ∈ A`. -/
def localCompletionX (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) : localCompletionRing C Δ :=
  ⟨C.x, by
    change Δ.derivation C.x ∈ formalPowerSeriesSubmodule C
    rw [Δ.derivation_x]
    exact (formalPowerSeriesSubmodule C).zero_mem⟩

/-- The first distinguished element `x f₁ ∈ A`. -/
theorem localCompletion_x_mul_f_one_mem (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    C.x * Δ.f ⟨1, Nat.zero_lt_succ 0⟩ ∈ localCompletionSubalgebra C Δ := by
  change Δ.derivation (C.x * Δ.f ⟨1, Nat.zero_lt_succ 0⟩) ∈
    formalPowerSeriesSubmodule C
  rw [Δ.derivation.leibniz, Δ.derivation_x]
  have hdf := Δ.derivation_f (⟨1, by decide⟩ : PositiveNat)
  rw [hdf]
  simp
  rw [Algebra.smul_def]
  change (convergentToLaurent C C.x) * (convergentToLaurent C C.x)⁻¹ ∈
    formalPowerSeriesSubmodule C
  have hxl : convergentToLaurent C C.x ≠ 0 := by
    change formalPowerSeriesToLaurent (C.expansion C.x) ≠ 0
    rw [C.expansion_x]
    intro h
    have hc := congrArg (fun z : FormalLaurentSeries => z.coeff 1) h
    simp [formalPowerSeriesToLaurent] at hc
  have hone : convergentToLaurent C C.x * (convergentToLaurent C C.x)⁻¹ = 1 :=
    mul_inv_cancel₀ hxl
  rw [hone]
  apply (mem_formalPowerSeriesSubmodule_iff C (1 : FormalLaurentSeries)).2
  refine ⟨PowerSeries.C 1, ?_⟩
  simp

def localCompletionXFOne (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) : localCompletionRing C Δ :=
  ⟨C.x * Δ.f ⟨1, Nat.zero_lt_succ 0⟩,
    localCompletion_x_mul_f_one_mem C Δ⟩

/-- The ideal `(x, x f₁)` in `A`. -/
def localCompletionCandidateMaximalIdeal (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    Ideal (localCompletionRing C Δ) :=
  Ideal.span {localCompletionX C Δ, localCompletionXFOne C Δ}

/-- The elements `xⁿ f_n` used in the final dual-number calculation lie in `A`. -/
theorem localCompletion_x_pow_f_mem
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (n : PositiveNat) :
    C.x ^ (n : ℕ) * Δ.f n ∈ localCompletionSubalgebra C Δ := by
  change Δ.derivation (C.x ^ (n : ℕ) * Δ.f n) ∈ formalPowerSeriesSubmodule C
  rw [Δ.derivation.leibniz, Δ.derivation.leibniz_pow, Δ.derivation_x, Δ.derivation_f]
  simp only [smul_zero, add_zero]
  rw [Algebra.smul_def]
  rw [map_pow]
  change (convergentToLaurent C C.x) ^ (n : ℕ) *
      (convergentToLaurent C C.x)⁻¹ ^ (n : ℕ) ∈ formalPowerSeriesSubmodule C
  have hxl : convergentToLaurent C C.x ≠ 0 := by
    change formalPowerSeriesToLaurent (C.expansion C.x) ≠ 0
    rw [C.expansion_x]
    intro h
    have hc := congrArg (fun z : FormalLaurentSeries => z.coeff 1) h
    simp [formalPowerSeriesToLaurent] at hc
  have hp : (convergentToLaurent C C.x) ^ (n : ℕ) ≠ 0 :=
    pow_ne_zero _ hxl
  have hone :
      (convergentToLaurent C C.x) ^ (n : ℕ) *
        (convergentToLaurent C C.x)⁻¹ ^ (n : ℕ) = 1 := by
    rw [inv_pow]
    exact mul_inv_cancel₀ hp
  rw [hone]
  apply (mem_formalPowerSeriesSubmodule_iff C (1 : FormalLaurentSeries)).2
  refine ⟨PowerSeries.C 1, ?_⟩
  simp

def localCompletionXPowF
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (n : PositiveNat) : localCompletionRing C Δ :=
  ⟨C.x ^ (n : ℕ) * Δ.f n, localCompletion_x_pow_f_mem C Δ n⟩

/-! ## The preliminary differential-power calculation -/

theorem differential_power_mem_formalPowerSeriesSubmodule
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    {f : C.carrier} (hf : f ∈ Ideal.span ({C.x} : Set C.carrier))
    (hf0 : f ≠ 0) :
      ∃ n : ℕ, ∃ h : FormalPowerSeries,
      Δ.derivation f =
      formalPowerSeriesToLaurent h / (convergentToLaurent C f) ^ n ∧
      f ^ (n + 1) ∈ localCompletionSubalgebra C Δ ∧
      f ^ (n + 2) ∈ localCompletionSubalgebra C Δ := by
  /- PROOF ROADMAP (Luna).
  Stage 1 -- put the Laurent denominator on `f`.  From `hf` use
  `Ideal.mem_span_singleton` to write `f = C.x * g`; use
  `C.expansion_injective`, `C.expansion_x`, and
  `HahnSeries.ofPowerSeries_injective` (all Laurent-series facts are in
  `Mathlib/RingTheory/LaurentSeries.lean`) to show
  `convergentToLaurent C f != 0`.  Compare the integer orders of this element
  and `Δ.derivation f` (split off the easy case `Δ.derivation f = 0` first).
  Choose `n : Nat` large enough that the order of
  `(convergentToLaurent C f)^n * Δ.derivation f` is nonnegative.  The
  `LaurentSeries.powerSeriesPart` API, especially
  `LaurentSeries.ofPowerSeries_powerSeriesPart`, then supplies `h` with
  `formalPowerSeriesToLaurent h =
    (convergentToLaurent C f)^n * Δ.derivation f`.  Cancel the nonzero power
  to obtain the displayed quotient identity.
  Stage 2 -- apply `Derivation.leibniz_pow` at exponents `n + 1` and `n + 2`.
  Substitute the quotient identity, use `map_pow`, and cancel the denominator;
  the remaining Laurent series are respectively scalar multiples of `h` and
  of `C.expansion f * h`, hence are in `formalPowerSeriesSubmodule C` by
  `mem_formalPowerSeriesSubmodule_iff`.  Do not try to use
  `IsLocalization.surj`: it gives an arbitrary power-series denominator and
  does not establish the required denominator `(convergentToLaurent C f)^n`.
  -/
  sorry

/-! ## The six assertions in the source -/

/-- Every convergent power series is integral over `A`. -/
theorem convergentPowerSeries_integral_over_localCompletion
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    ∀ c : C.carrier, IsIntegral (localCompletionRing C Δ) c := by
  /- PROOF ROADMAP (Luna).
  Fix `c` and use `C.exists_eq_algebraMap_add_x_mul c` to write
  `c = algebraMap _ _ z + f` with `f = C.x * g`.  The constant summand is the
  image of an element of `localCompletionRing C Δ`, so it is integral by
  `isIntegral_algebraMap`.  If `f = 0`, finish with `IsIntegral.add`.
  Otherwise apply `differential_power_mem_formalPowerSeriesSubmodule` to `f`
  (membership in `Ideal.span {C.x}` follows from
  `Ideal.mem_span_singleton`).  Regard the resulting `f^(n+1)` and `f^(n+2)`
  as elements `a b : localCompletionRing C Δ`.  Exhibit `f` as a root of the
  monic polynomial `X^(n+2) - Polynomial.C a * X`: after `aeval_def`, its vanishing is
  exactly `f^(n+2) - f^(n+1) * f = 0`.  Use
  `IsIntegral.of_pow` only if its local signature matches this pair of
  consecutive powers; the explicit polynomial avoids divisibility side
  conditions.  Finally rewrite the chosen decomposition and use
  `IsIntegral.add`.
  -/
  sorry

/-- The ring `A` is a local domain. -/
theorem localCompletion_isLocalDomain
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    IsLocalRing (localCompletionRing C Δ) ∧
      IsDomain (localCompletionRing C Δ) := by
  /- PROOF ROADMAP (Luna).
  The domain half is `inferInstance`.  For locality, first prove the analytic
  unit criterion in `C.carrier`: `c` is a nonunit iff
  `c ∈ Ideal.span {C.x}`.  The forward direction uses
  `C.exists_eq_algebraMap_add_x_mul`; if the constant is nonzero, apply
  `C.localization_is_fraction_ring` as a local instance, install
  `IsFractionRing.toField C.carrier` on `Localization.Away C.x`, and use
  `IsLocalization.surj` in `Localization.Away C.x`, then repeatedly remove
  factors of `C.x` (using the constant-term decomposition and domain
  cancellation) to construct an inverse already in `C.carrier`.  Conversely,
  `C.x` is nonzero by `C.expansion_injective` and `C.expansion_x`, while its
  image is not a unit because the constant coefficient of `PowerSeries.X`
  vanishes.
  For `a : localCompletionRing C Δ`, a unit in the subalgebra is a unit in
  `C.carrier`.  If its carrier is not an `x`-multiple, the inverse constructed
  above has derivative `-a^(-2) * Δ.derivation a`; closure of formal power
  series under multiplication by the convergent expansion shows that inverse
  lies in `localCompletionSubalgebra C Δ`.  Thus the nonunits of `A` are
  exactly the carrier elements in `(C.x)`.  Apply the constructor
  `IsLocalRing.of_nonunits_add`: the sum of two such elements is again an
  `x`-multiple.  This argument is deliberately inline because
  `localCompletion_nonunits_eq_x_multiple` occurs later in source order.
  -/
  sorry

theorem localCompletion_isDomain
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    IsDomain (localCompletionRing C Δ) := by
  infer_instance

/-- The dimension assertion `dim(A) = 1`. -/
theorem localCompletion_dimension_one
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    ringKrullDim (localCompletionRing C Δ) = 1 := by
  /- PROOF ROADMAP (Luna).
  Install the local-ring component of `localCompletion_isLocalDomain` and use
  `ringKrullDim_eq_one_iff_of_isLocalRing_isDomain` from
  `Mathlib/RingTheory/KrullDimension/LocalRing.lean`.
  First, `A` is not a field: `localCompletionX C Δ` is nonzero (apply the
  carrier coercion, then `C.expansion_injective` and `C.expansion_x`) and is a
  nonunit by the unit criterion from the locality proof.
  For the radical condition, fix nonzero `a : A`.  Reproduce the fraction-field
  construction later packaged as
  `localCompletion_fractionField_eq_convergent_fractionField`: consecutive
  powers from `differential_power_mem_formalPowerSeriesSubmodule` express each
  analytic series as a quotient of elements of `A`.  Equivalently, one may use
  `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain` from
  `Mathlib/RingTheory/Ideal/GoingUp.lean` (its final argument is the kernel
  inclusion, discharged using injectivity of the subalgebra map) after
  installing the integrality instance furnished by
  `convergentPowerSeries_integral_over_localCompletion`.  A prime of
  `C.carrier` above a nonzero prime of `A` is nonzero; localizing away from
  `C.x` and using `C.localization_is_fraction_ring` forces it to contain
  `C.x`, hence it is the analytic maximal ideal.  Contracting shows every
  nonzero prime of `A` is its maximal ideal, which is the radical condition in
  the cited dimension-one lemma.
  -/
  sorry

/-- The claimed presentation of the maximal ideal. -/
theorem localCompletion_maximalIdeal_eq_candidate
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    [IsLocalRing (localCompletionRing C Δ)] :
    IsLocalRing.maximalIdeal (localCompletionRing C Δ) =
      localCompletionCandidateMaximalIdeal C Δ := by
  /- PROOF ROADMAP (Luna).
  Prove equality by two inclusions.  Both generators of the candidate are
  nonunits: their carriers are visibly multiples of `C.x`, so the unit
  criterion established in `localCompletion_isLocalDomain` and
  `IsLocalRing.mem_maximalIdeal` put them in the maximal ideal; conclude the
  easy inclusion with `Ideal.span_le`.
  For the reverse inclusion, take `a` in the maximal ideal.  Its carrier `f`
  is an `x`-multiple by the same criterion, and `a.property` gives
  `Δ.derivation f ∈ formalPowerSeriesSubmodule C`.  Repeat the staged
  calculation later exposed by `localCompletion_ideal_membership_steps`:
  choose `h` via `mem_formalPowerSeriesSubmodule_iff`, split it as
  `PowerSeries.C c + PowerSeries.X * h'`, write
  `f - c • (C.x * Δ.f 1) = C.x * g`, and cancel the nonzero Laurent image of
  `C.x` in the derivative identity to prove `g ∈ A`.  The resulting equation
  `f = c • (C.x * Δ.f 1) + C.x * g` is exactly membership in the span of
  `localCompletionXFOne` and `localCompletionX` (use `Submodule.mem_span_pair`
  if available, otherwise two applications of `Ideal.subset_span`).  The
  calculation must be inline here because its named helper is declared later.
  -/
  sorry

/-- The Noetherian assertion for `A`. -/
theorem localCompletion_isNoetherian
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    IsNoetherianRing (localCompletionRing C Δ) := by
  /- PROOF ROADMAP (Luna).
  Install the local-ring instance from `localCompletion_isLocalDomain`.
  Apply `IsNoetherianRing.of_prime_ne_bot` from
  `Mathlib/RingTheory/Noetherian/OfPrime.lean`.  By
  `localCompletion_dimension_one` and
  `Ring.krullDimLE_one_iff_of_noZeroDivisors`, every nonzero prime is maximal;
  `IsLocalRing.eq_maximalIdeal` identifies it with the unique maximal ideal.
  Rewrite with `localCompletion_maximalIdeal_eq_candidate` and close finite
  generation with `localCompletion_candidateMaximalIdeal_fg`'s underlying
  proof `Submodule.fg_span (by simp)`.  Since that named theorem is later in
  source order, invoke `Submodule.fg_span` directly here.
  -/
  sorry

/-! ## Further elementary calculations used to prove the ideal presentation -/

theorem differential_power_derivative_identities
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    {f : C.carrier} (hf : f ∈ Ideal.span ({C.x} : Set C.carrier))
    (hf0 : f ≠ 0) :
      ∃ n : ℕ, ∃ h : FormalPowerSeries,
      Δ.derivation f =
          formalPowerSeriesToLaurent h / (convergentToLaurent C f) ^ n ∧
        Δ.derivation
            (((n + 1 : ℕ) : ℂ)⁻¹ • f ^ (n + 1)) =
          formalPowerSeriesToLaurent h ∧
        Δ.derivation
            (((n + 2 : ℕ) : ℂ)⁻¹ • f ^ (n + 2)) =
          convergentToLaurent C f * formalPowerSeriesToLaurent h := by
  /- PROOF ROADMAP (Luna).
  Obtain `n, h, hquot, _, _` from
  `differential_power_mem_formalPowerSeriesSubmodule C Δ hf hf0`; only its
  quotient identity is needed.  Apply `map_smul_of_tower`/`map_smul` for the
  `ℂ`-derivation and `Derivation.leibniz_pow` to both displayed derivatives.
  In characteristic zero, simplify
  `((n+k : Nat) : ℂ)⁻¹ * (n+k : ℂ) = 1`; discharge nonzeroness with
  `Nat.cast_ne_zero` (the exponents are successors).  Rewrite `hquot`, turn
  `/` into multiplication by the inverse, and cancel
  `(convergentToLaurent C f)^n` using the nonzeroness proof from the first
  stage (`C.expansion_injective` followed by
  `HahnSeries.ofPowerSeries_injective`).  The first identity reduces to
  `formalPowerSeriesToLaurent h`; the second has one uncancelled factor
  `convergentToLaurent C f`.  Normalizing with `map_pow`, `inv_pow`, and
  `mul_assoc` is more reliable here than `field_simp`, whose denominators are
  hidden behind the Laurent embedding.
  -/
  sorry

theorem localCompletion_fractionField_eq_convergent_fractionField
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    Nonempty (FractionRing (localCompletionRing C Δ) ≃+*
      convergentPowerSeriesFractionField C) := by
  /- PROOF ROADMAP (Luna).
  Put on `FractionRing C.carrier` its algebra structure over
  `localCompletionRing C Δ` induced by the subalgebra inclusion.  Prove it is
  a fraction ring of `A` using `IsFractionRing.of_field` from
  `Mathlib/RingTheory/Localization/FractionRing.lean`.  For a numerator
  `c : C.carrier`, split off its constant with
  `C.exists_eq_algebraMap_add_x_mul`.  If the remainder `f` is nonzero,
  `differential_power_mem_formalPowerSeriesSubmodule` gives consecutive
  powers `f^(n+1), f^(n+2)` in `A`, hence
  `f = f^(n+2) / f^(n+1)`; the denominator is nonzero by `hf0` and the domain
  instance.  Constants already come from `A`, and a general element of
  `FractionRing C.carrier` is a quotient by `IsLocalization.surj`.
  With this local `IsFractionRing A (FractionRing C.carrier)` instance,
  compare it to the canonical `FractionRing A` using
  `IsLocalization.algEquiv` (or `IsFractionRing.algEquiv`) and forget scalars
  with `.toRingEquiv`.  Universe `u` is shared by both carriers, so no lift is
  needed.
  -/
  sorry

theorem localCompletion_nonunits_eq_x_multiple
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    {a : localCompletionRing C Δ | ¬ IsUnit a} =
      {a : localCompletionRing C Δ |
        (show localCompletionSubalgebra C Δ from a).1 ∈
          Ideal.span ({C.x} : Set C.carrier)} := by
  /- PROOF ROADMAP (Luna).
  Use `Set.ext` on `a`.  The forward implication follows from the analytic
  unit criterion used in `localCompletion_isLocalDomain`: if the carrier is
  not divisible by `C.x`, construct its inverse in `C.carrier`; the quotient
  rule for `Δ.derivation` and `mem_formalPowerSeriesSubmodule_iff` show this
  inverse belongs to `A`, contradicting `¬ IsUnit a`.
  Conversely, if the carrier is `C.x * g` and `a` were a unit of `A`, applying
  the subalgebra inclusion would make it a unit of `C.carrier`.  Its expansion
  would then be a unit formal power series, but `C.expansion_x` and
  `PowerSeries.isUnit_iff_constantCoeff` show the constant coefficient of
  `C.expansion (C.x * g)` is zero.  This contradiction proves nonunitness.
  Keep all coercions explicit as
  `(show localCompletionSubalgebra C Δ from a).1`; rewriting the subtype as a
  bare carrier tends to choose the self-algebra instance on `A`.
  -/
  sorry

theorem localCompletion_ideal_membership_steps
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    {f : C.carrier}
    (hf : f ∈ Ideal.span ({C.x} : Set C.carrier))
    (hfA : Δ.derivation f ∈ formalPowerSeriesSubmodule C) :
    ∃ (h h' : FormalPowerSeries) (c : ℂ) (g : C.carrier),
      formalPowerSeriesToLaurent h = Δ.derivation f ∧
        h = PowerSeries.C c + PowerSeries.X * h' ∧
        f - c • (C.x * Δ.f ⟨1, Nat.zero_lt_succ 0⟩) = C.x * g ∧
        Δ.derivation
            (f - c • (C.x * Δ.f ⟨1, Nat.zero_lt_succ 0⟩)) =
          formalPowerSeriesToLaurent (PowerSeries.X * h') ∧
        Δ.derivation g = formalPowerSeriesToLaurent h' ∧
        Δ.derivation g ∈ formalPowerSeriesSubmodule C := by
  /- PROOF ROADMAP (Luna).
  (1) Use `mem_formalPowerSeriesSubmodule_iff C _` on `hfA` to choose `h`
  with the first equality.
  (2) Set `c := PowerSeries.constantCoeff ℂ h`.  Use
  `PowerSeries.X_dvd_iff` (equivalently `PowerSeries.X_pow_dvd_iff` at one)
  on `h - PowerSeries.C c`, then choose `h'` and rearrange to
  `h = PowerSeries.C c + PowerSeries.X * h'`.
  (3) Both `f` and `C.x * Δ.f 1` lie in `Ideal.span {C.x}`; subtract and use
  `Ideal.mem_span_singleton'` to choose `g` with
  `f - c • (C.x * Δ.f 1) = C.x * g`.
  (4) Expand the derivative with `map_sub`, `map_smul`, and
  `localCompletion_x_mul_f_one_mem`'s calculation
  `Δ.derivation (C.x * Δ.f 1) = 1`.  Rewrite the chosen equations and
  `C.expansion_x` to get the `PowerSeries.X * h'` equality.
  (5) Differentiate `C.x * g`, use `Δ.derivation_x`, and compare the two
  Laurent equalities.  Cancel `convergentToLaurent C C.x`, whose nonzeroness
  follows from `C.expansion_x` and `HahnSeries.ofPowerSeries_injective`, to
  obtain `Δ.derivation g = formalPowerSeriesToLaurent h'`.
  (6) Finish membership with
  `(mem_formalPowerSeriesSubmodule_iff C _).2 ⟨h', rfl⟩`.
  -/
  sorry

theorem localCompletion_ideal_membership_calculation
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    {f : C.carrier}
    (hf : f ∈ Ideal.span ({C.x} : Set C.carrier))
    (hfA : Δ.derivation f ∈ formalPowerSeriesSubmodule C) :
    ∃ c : ℂ, ∃ g : C.carrier,
      f = c • (C.x * Δ.f ⟨1, Nat.zero_lt_succ 0⟩) + C.x * g ∧
        Δ.derivation g ∈ formalPowerSeriesSubmodule C := by
  rcases localCompletion_ideal_membership_steps C Δ hf hfA with
    ⟨h, h', c, g, _, _, hfg, _, hg, hA⟩
  exact ⟨c, g, by rw [← sub_eq_iff_eq_add'.mp hfg], hA⟩

/-! ## Completion, continuity, and the dual-number map -/

/-- The ideal generated by the `n`th power of the formal parameter. -/
def formalPowerSeriesXIdealPower (n : ℕ) : Ideal FormalPowerSeries :=
  Ideal.span ({PowerSeries.X ^ n} : Set FormalPowerSeries)

theorem localCompletion_derivation_adic_continuity
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    (∀ n : ℕ, ∀ a : localCompletionRing C Δ,
      a ∈ localCompletionCandidateMaximalIdeal C Δ ^ n →
        localCompletionDerivation C Δ a ∈ formalPowerSeriesXIdealPower (n - 1)) ∧
      @Continuous (localCompletionRing C Δ) FormalPowerSeries
        (localCompletionCandidateMaximalIdeal C Δ).adicTopology
        (Ideal.span ({PowerSeries.X} : Set FormalPowerSeries)).adicTopology
        (localCompletionDerivation C Δ) := by
  /- PROOF ROADMAP (Luna).
  First prove uniqueness of representatives:
  `HahnSeries.ofPowerSeries_injective` plus
  `localCompletionDerivation_spec` transfers `map_zero`, `map_add`, and the
  Leibniz rule of `Δ.derivation` to `localCompletionDerivation`.  Package at
  least the additive part as a local `AddMonoidHom`; this is required by
  `continuous_of_continuousAt_zero`.
  For the filtration estimate, rewrite the candidate ideal with
  `localCompletionCandidateMaximalIdeal` and induct on membership in its
  powers (or use `Ideal.pow_span` and span induction).  Each monomial is a
  product of `n` factors chosen from `x` and `x*f_1`.  Repeated Leibniz gives
  zero for an `x` derivative and, when one `x*f_1` is differentiated, leaves
  at least `n-1` factors of `PowerSeries.X`.  Convert divisibility to
  membership using `Ideal.span_singleton_pow` and
  `PowerSeries.X_pow_dvd_iff`; handle `n = 0` separately.
  For continuity at zero, use
  `Ideal.hasBasis_nhds_zero_adic` from
  `Mathlib/Topology/Algebra/Nonarchimedean/AdicTopology.lean` on source and
  target.  Given target exponent `k`, choose source exponent `k+1`; the bound
  yields membership in `(X^k)`.  Apply
  `continuous_of_continuousAt_zero` to the local additive hom and coerce back
  to the original function.  The shift `n-1` is intentional and is exactly
  why the source exponent must be `k+1`.
  -/
  sorry

/-- The `m`-adic completion of `A` at the displayed candidate ideal. -/
abbrev localCompletionCompletion (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :=
  @AdicCompletion (localCompletionRing C Δ) _
    (localCompletionCandidateMaximalIdeal C Δ) (localCompletionRing C Δ) _
      Semiring.toModule

def localCompletionCompletionIdeal
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    Ideal (localCompletionCompletion C Δ) :=
  (localCompletionCandidateMaximalIdeal C Δ).map
    (algebraMap (localCompletionRing C Δ)
      (localCompletionCompletion C Δ))

theorem localCompletion_candidateMaximalIdeal_fg
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    (localCompletionCandidateMaximalIdeal C Δ).FG := by
  exact Submodule.fg_span (by simp)

theorem localCompletion_completion_isAdicComplete
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    IsAdicComplete (localCompletionCompletionIdeal C Δ)
      (localCompletionCompletion C Δ) := by
  exact AdicCompletion.isAdicComplete_self _
    (localCompletion_candidateMaximalIdeal_fg C Δ)

/-- A derivation relative to a ring map, used for `ψ + ε D`. -/
structure RelativeDerivation {A P : Type*} [CommRing A] [CommRing P]
    (ψ : A →+* P) where
  toAddMonoidHom : A →+ P
  leibniz' (a b : A) :
    toAddMonoidHom (a * b) = ψ a * toAddMonoidHom b + ψ b * toAddMonoidHom a

instance {A P : Type*} [CommRing A] [CommRing P] {ψ : A →+* P} :
    CoeFun (RelativeDerivation ψ) (fun _ => A → P) :=
  ⟨fun d => d.toAddMonoidHom⟩

@[simp]
theorem RelativeDerivation.map_zero {A P : Type*} [CommRing A] [CommRing P]
    {ψ : A →+* P} (d : RelativeDerivation ψ) : d 0 = 0 := by
  exact d.toAddMonoidHom.map_zero

@[simp]
theorem RelativeDerivation.map_add {A P : Type*} [CommRing A] [CommRing P]
    {ψ : A →+* P} (d : RelativeDerivation ψ) (a b : A) :
    d (a + b) = d a + d b := by
  exact d.toAddMonoidHom.map_add a b

@[simp]
theorem RelativeDerivation.zero_at_one {A P : Type*} [CommRing A] [CommRing P]
    {ψ : A →+* P} (d : RelativeDerivation ψ) : d 1 = 0 := by
  have h : d 1 = ψ 1 * d 1 + ψ 1 * d 1 := by
    simpa only [one_mul, mul_one] using d.leibniz' 1 1
  have h' : d 1 = d 1 + d 1 := by
    calc
      d 1 = ψ 1 * d 1 + ψ 1 * d 1 := h
      _ = d 1 + d 1 := by rw [map_one, one_mul]
  have h'' := congrArg (fun z => z + -d 1) h'
  simpa [add_assoc] using h''.symm

/-- The ring map `ψ + ε D : A → ℂ[[x]][ε]`. -/
def dualNumberMap {A P : Type*} [CommRing A] [CommRing P]
    (ψ : A →+* P) (d : RelativeDerivation ψ) :
    A →+* DualNumber P where
  toFun a := TrivSqZeroExt.inl (ψ a) + TrivSqZeroExt.inr (d a)
  map_one' := by
    rw [RelativeDerivation.zero_at_one d]
    simp
  map_mul' a b := by
    ext <;> simp [d.leibniz' a b, mul_add, add_mul, add_comm, mul_comm]
  map_zero' := by simp
  map_add' a b := by
    ext <;> simp [map_add]

/-- The source's completion data, including the split map from formal series.

The `sectionMap` fields encode the map induced by the inclusion
`ℂ[x]_(x) ⊂ A`; it is a section of `psi`.  The field
`ext_psi_induced_derivation` is the omitted separation verification in the
source: the two coordinates `psi` and the extended derivation determine a
completion element.  Finally, `psi_on_localCompletion` identifies `ψ` with
the Taylor expansion on the dense subring `A`. -/
structure LocalCompletionCompletionData
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) where
  psi : localCompletionCompletion C Δ →+* FormalPowerSeries
  psi_surjective : Function.Surjective psi
  psi_on_localCompletion :
    ∀ a : localCompletionRing C Δ,
      psi (algebraMap (localCompletionRing C Δ)
        (localCompletionCompletion C Δ) a) =
          C.expansion (show localCompletionSubalgebra C Δ from a).1
  sectionMap : FormalPowerSeries →+* localCompletionCompletion C Δ
  section_psi : psi.comp sectionMap = RingHom.id _
  induced_derivation : RelativeDerivation psi
  induced_derivation_continuous :
    @Continuous (localCompletionCompletion C Δ) FormalPowerSeries
      (localCompletionCompletionIdeal C Δ).adicTopology
      (Ideal.span ({PowerSeries.X} : Set FormalPowerSeries)).adicTopology
      induced_derivation
  induced_derivation_on_section :
    ∀ f, induced_derivation (sectionMap f) = 0
  induced_derivation_on_localCompletion :
    ∀ a : localCompletionRing C Δ,
      induced_derivation
          (algebraMap (localCompletionRing C Δ)
            (localCompletionCompletion C Δ) a) =
        localCompletionDerivation C Δ a
  ext_psi_induced_derivation :
    ∀ {a b : localCompletionCompletion C Δ},
      psi a = psi b → induced_derivation a = induced_derivation b → a = b

/-- The dual-number-valued map `ψ + ε D̂` from the source. -/
def LocalCompletionCompletionData.completionMap
    (Γ : LocalCompletionCompletionData C Δ) :
    localCompletionCompletion C Δ →+* DualNumber FormalPowerSeries :=
  dualNumberMap Γ.psi Γ.induced_derivation

theorem completion_map_apply
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ) (a : localCompletionCompletion C Δ) :
    Γ.completionMap a =
      TrivSqZeroExt.inl (Γ.psi a) + TrivSqZeroExt.inr (Γ.induced_derivation a) := by
  rfl

theorem completion_map_surjective
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ) :
    Function.Surjective Γ.completionMap := by
  /- PROOF ROADMAP (Luna).
  Let `a` be the image in the completion of
  `localCompletionXPowF C Δ (1 : PositiveNat)` and put
  `k := a - Γ.sectionMap (Γ.psi a)`.  The corrected split identity
  `Γ.section_psi : Γ.psi.comp Γ.sectionMap = RingHom.id _` gives
  `Γ.psi k = 0`; `Γ.induced_derivation_on_section`,
  `Γ.induced_derivation_on_localCompletion`, and an inline use of
  `localCompletionDerivation_spec`, `Δ.derivation_f`, and
  `Δ.derivation_x` give `Γ.induced_derivation a = 1` (the named theorem
  `localCompletionDerivation_x_pow_f` is later in source order).  Hence
  `Γ.induced_derivation k = 1`.  Derive subtraction through
  `Γ.induced_derivation.toAddMonoidHom.map_sub`.
  For arbitrary `z : DualNumber FormalPowerSeries`, use its coordinates
  `z.fst` and `z.snd` and choose the preimage
  `Γ.sectionMap z.fst + Γ.sectionMap z.snd * k`.  The split identity computes
  its `psi` coordinate as `z.fst`; `Γ.induced_derivation_on_section` and
  `Γ.induced_derivation.leibniz'` compute its derivative coordinate as
  `z.snd`.  Finish with `TrivSqZeroExt.ext` and `completion_map_apply`.
  This exact construction is why `section_psi` must be `psi ∘ sectionMap = id`;
  the former orientation would kill `k` and make the data inconsistent.
  -/
  sorry

theorem completion_map_isRingEquiv
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ) :
    ∃ e : localCompletionCompletion C Δ ≃+* DualNumber FormalPowerSeries,
      e.toRingHom = Γ.completionMap := by
  /- PROOF ROADMAP (Luna).
  Combine `completion_map_surjective C Δ Γ` with injectivity obtained from the
  repaired coordinate-separation field.  If
  `Γ.completionMap a = Γ.completionMap b`, unfold with
  `completion_map_apply` and apply `TrivSqZeroExt.ext_iff` (or congruence with
  `.fst` and `.snd`) to read off `Γ.psi a = Γ.psi b` and
  `Γ.induced_derivation a = Γ.induced_derivation b`; then exact
  `Γ.ext_psi_induced_derivation`.
  Define `e := RingEquiv.ofBijective Γ.completionMap ⟨hinj, hsurj⟩` from
  `Mathlib/Algebra/Ring/Equiv.lean`.  Its coercion is definitionally the ring
  hom, so `e.toRingHom = Γ.completionMap` follows by `rfl` or `ext; rfl`.
  The separation field is essential: surjectivity alone cannot turn a ring
  hom into an equivalence, and a reduced ring may have nonreduced quotients.
  -/
  sorry

theorem completion_map_isEquiv
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ) :
    Nonempty (localCompletionCompletion C Δ ≃+* DualNumber FormalPowerSeries) := by
  rcases completion_map_isRingEquiv C Δ Γ with ⟨e, _⟩
  exact ⟨e⟩

/-- The source's sixth claim: the completion is the ring of dual numbers over
`ℂ[[x]]`.
-/
theorem localCompletion_completion_is_dualNumber
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ) :
    Nonempty (localCompletionCompletion C Δ ≃+*
      DualNumber FormalPowerSeries) := by
  exact completion_map_isEquiv C Δ Γ

theorem localCompletion_completion_is_nonreduced
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ) :
    ¬ IsReduced (localCompletionCompletion C Δ) := by
  /- PROOF ROADMAP (Luna).
  Choose `e` from `completion_map_isRingEquiv C Δ Γ`.  Assuming the completion
  reduced, pull the dual-number epsilon
  `ε := TrivSqZeroExt.inr (1 : FormalPowerSeries)` back along `e.symm`.
  `DualNumber.isNilpotent_eps` and preservation of powers by `e.symm` show the
  pullback is nilpotent, hence zero by `IsReduced.eq_zero`.  Apply `e` and use
  `e.apply_symm_apply` to deduce `ε = 0`, contradicting
  `TrivSqZeroExt.inr_injective` and `one_ne_zero`.
  This proof is intentionally independent of
  `formalPowerSeries_dualNumber_not_reduced`, which is declared immediately
  afterward and is unavailable by chronological source order.
  -/
  sorry

/-- The dual numbers over the formal power-series ring are nonreduced. -/
theorem formalPowerSeries_dualNumber_not_reduced :
    ¬ IsReduced (DualNumber FormalPowerSeries) := by
  intro hR
  have hε :
      (TrivSqZeroExt.inr (1 : FormalPowerSeries) :
        DualNumber FormalPowerSeries) ≠ 0 := by
    intro h
    have h' : (1 : FormalPowerSeries) = 0 :=
      TrivSqZeroExt.inr_injective h
    exact one_ne_zero h'
  exact hε (hR.eq_zero _ DualNumber.isNilpotent_eps)

/-! ## The displayed calculation and the chapter-level existence theorem -/

theorem localCompletionDerivation_x_pow_f
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (n : PositiveNat) :
    localCompletionDerivation C Δ (localCompletionXPowF C Δ n) = 1 := by
  /- PROOF ROADMAP (Luna).
  Apply `HahnSeries.ofPowerSeries_injective` (the map is
  `formalPowerSeriesToLaurent`) and rewrite the left side with
  `localCompletionDerivation_spec`.  Unfold `localCompletionXPowF` and compute
  with `Δ.derivation.leibniz`, `Δ.derivation.leibniz_pow`,
  `Δ.derivation_x`, and `Δ.derivation_f n`.  After `map_pow` and
  `Algebra.smul_def`, the remaining expression is
  `(convergentToLaurent C C.x)^n *
    (convergentToLaurent C C.x)^(-n)`.
  Prove the Laurent image of `C.x` nonzero from `C.expansion_x` and
  `HahnSeries.ofPowerSeries_injective`, then close with `inv_pow`,
  `pow_ne_zero`, and `mul_inv_cancel₀`.  Finally identify the embedded
  power-series `1` with `map_one`.
  -/
  sorry

theorem completion_map_x_pow_f
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ)
    (n : PositiveNat) :
    Γ.completionMap
        (algebraMap (localCompletionRing C Δ)
          (localCompletionCompletion C Δ)
          (localCompletionXPowF C Δ n)) =
      TrivSqZeroExt.inl
          (Γ.psi
            (algebraMap (localCompletionRing C Δ)
              (localCompletionCompletion C Δ)
              (localCompletionXPowF C Δ n))) +
        TrivSqZeroExt.inr 1 := by
  /- PROOF ROADMAP (Luna).
  Rewrite the left side by `completion_map_apply`.  Rewrite its second
  coordinate using `Γ.induced_derivation_on_localCompletion` at
  `localCompletionXPowF C Δ n`, then
  `localCompletionDerivation_x_pow_f C Δ n`.  The first coordinate is already
  syntactically the required `Γ.psi` term.  `rfl` after those two rewrites (or
  one `simp only`) finishes; do not invoke `Γ.psi_on_localCompletion` here,
  since that specialization is reserved for the subsequent explicit theorem.
  -/
  sorry

theorem completion_map_x_pow_f_explicit
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ)
    (n : PositiveNat) :
    Γ.completionMap
        (algebraMap (localCompletionRing C Δ)
          (localCompletionCompletion C Δ)
          (localCompletionXPowF C Δ n)) =
      TrivSqZeroExt.inl
          (C.expansion
            (C.x ^ (n : ℕ) * Δ.f n)) +
        TrivSqZeroExt.inr 1 := by
  rw [completion_map_x_pow_f C Δ Γ n, Γ.psi_on_localCompletion]
  simp [localCompletionXPowF]

/-- All six algebraic claims of the characteristic-zero example, conditional
on the analytic and completion data whose existence the source omits. -/
theorem exists_local_ring_with_nonreduced_completion
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ) :
    ∃ (C' : ConvergentPowerSeriesRing)
      (Δ' : FerrandRaynaudDifferentialData C')
      (Γ' : LocalCompletionCompletionData C' Δ'),
      (∀ c : C'.carrier, IsIntegral (localCompletionRing C' Δ') c) ∧
        ∃ hA : IsLocalRing (localCompletionRing C' Δ'),
          letI : IsLocalRing (localCompletionRing C' Δ') := hA
          IsDomain (localCompletionRing C' Δ') ∧
            ringKrullDim (localCompletionRing C' Δ') = 1 ∧
            IsLocalRing.maximalIdeal (localCompletionRing C' Δ') =
              localCompletionCandidateMaximalIdeal C' Δ' ∧
            IsNoetherianRing (localCompletionRing C' Δ') ∧
            IsLocalRing (localCompletionCompletion C' Δ') ∧
            IsNoetherianRing (localCompletionCompletion C' Δ') ∧
            ringKrullDim (localCompletionCompletion C' Δ') = 1 ∧
            IsAdicComplete (localCompletionCompletionIdeal C' Δ')
              (localCompletionCompletion C' Δ') ∧
            Nonempty (localCompletionCompletion C' Δ' ≃+*
              DualNumber FormalPowerSeries) ∧
            ¬ IsReduced (localCompletionCompletion C' Δ') := by
  /- PROOF ROADMAP (Luna).
  Witness the existential with `C, Δ, Γ`.  Supply integrality from
  `convergentPowerSeries_integral_over_localCompletion`, and destruct
  `localCompletion_isLocalDomain C Δ` as `⟨hlocal, hdomain⟩`; use `hlocal` as
  the `letI` required by the statement.  The next three conjuncts are
  `hdomain`, `localCompletion_dimension_one`, and
  `localCompletion_maximalIdeal_eq_candidate`.  Install
  `localCompletion_isNoetherian C Δ` as the Noetherian instance.
  For locality of the completion, rewrite the completion ideal along
  `localCompletion_maximalIdeal_eq_candidate` and apply the instance/theorem
  `AdicCompletion.isLocalRing_of_fg` from
  `Mathlib/RingTheory/AdicCompletion/LocalRing.lean` with
  `localCompletion_candidateMaximalIdeal_fg`.
  Choose `e` from `completion_map_isRingEquiv C Δ Γ`.  The ring
  `DualNumber FormalPowerSeries` is Noetherian: `PowerSeries ℂ` has the
  `IsNoetherianRing` instance from
  `Mathlib/RingTheory/PowerSeries/Ideal.lean`, and the dual numbers are finite
  as a module, so use `IsNoetherianRing.of_finite`; transport across `e`
  (equivalently transport finite generation of ideals with `Ideal.map` and
  `Ideal.comap`).
  For the completion dimension, use `RingEquiv.ringKrullDim e` and identify
  the prime spectrum of the dual numbers with that of `PowerSeries ℂ` via the
  quotient by
  `TrivSqZeroExt.kerIdeal FormalPowerSeries FormalPowerSeries` from
  `Mathlib/Algebra/TrivSqZeroExt/Ideal.lean`.  Its square is bottom by
  `TrivSqZeroExt.kerIdeal_sq`, so it is contained in every prime.  Apply
  `Ideal.primeSpectrumQuotientOrderIsoZeroLocus` and the quotient equivalence
  `RingHom.quotientKerEquivOfSurjective` induced by
  `TrivSqZeroExt.fstHom`; finish with
  `IsDiscreteValuationRing.ringKrullDim_eq_one` from
  `Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean`.
  The remaining conjuncts are, in order,
  `localCompletion_completion_isAdicComplete`, `⟨e⟩`, and
  `localCompletion_completion_is_nonreduced C Δ Γ`.
  The explicit parameters are essential: the source omits construction of
  the convergent-series ring, the independent differentials, and the
  completion separation theorem, so the previous unconditional existential
  had no witness derivable anywhere in this file or its imports.
  -/
  sorry

end Formalization.Books.Examples.Unit17
