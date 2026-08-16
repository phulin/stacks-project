import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.DualNumber
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

namespace Formalization.«Books.Examples».Unit17

universe u v

/-! ## The analytic and formal series rings -/

/-- The positive-radius condition on a formal scalar power series. -/
def IsConvergentPowerSeries (f : PowerSeries ℂ) : Prop :=
  0 < (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n f)).radius

/-- Positive natural numbers, used for the sequence `f₁, f₂, ...`. -/
abbrev PositiveNat := {n : ℕ // 0 < n}

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
  sorry

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
abbrev localCompletionRing (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :=
  (localCompletionSubalgebra C Δ : Type)

/-- The power-series-valued restriction of `Δ.derivation` to `A`. -/
noncomputable def localCompletionDerivation
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (a : localCompletionRing C Δ) : FormalPowerSeries :=
  Classical.choose
    ((mem_formalPowerSeriesSubmodule_iff C
        (Δ.derivation (a : C.carrier))).mp
      (show Δ.derivation (a : C.carrier) ∈ formalPowerSeriesSubmodule C from
        a.property))

theorem localCompletionDerivation_spec
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (a : localCompletionRing C Δ) :
    formalPowerSeriesToLaurent (localCompletionDerivation C Δ a) =
      Δ.derivation (a : C.carrier) := by
  exact Classical.choose_spec
    ((mem_formalPowerSeriesSubmodule_iff C
        (Δ.derivation (a : C.carrier))).mp
      (show Δ.derivation (a : C.carrier) ∈ formalPowerSeriesSubmodule C from
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
  sorry

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
  sorry

def localCompletionXPowF
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (n : PositiveNat) : localCompletionRing C Δ :=
  ⟨C.x ^ (n : ℕ) * Δ.f n, localCompletion_x_pow_f_mem C Δ n⟩

/-! ## The six assertions in the source -/

/-- Every convergent power series is integral over `A`. -/
theorem convergentPowerSeries_integral_over_localCompletion
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    ∀ c : C.carrier, IsIntegral (localCompletionRing C Δ) c := by
  sorry

/-- The ring `A` is a local domain. -/
theorem localCompletion_isLocalDomain
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    IsLocalRing (localCompletionRing C Δ) := by
  sorry

theorem localCompletion_isDomain
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    IsDomain (localCompletionRing C Δ) := by
  infer_instance

/-- The dimension assertion `dim(A) = 1`, expressed by Mathlib's API. -/
theorem localCompletion_dimension_one
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    Ring.KrullDimLE 1 (localCompletionRing C Δ) ∧
      ¬ Ring.KrullDimLE 0 (localCompletionRing C Δ) := by
  sorry

/-- The claimed presentation of the maximal ideal. -/
theorem localCompletion_maximalIdeal_eq_candidate
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    [IsLocalRing (localCompletionRing C Δ)] :
    IsLocalRing.maximalIdeal (localCompletionRing C Δ) =
      localCompletionCandidateMaximalIdeal C Δ := by
  sorry

/-- The Noetherian assertion for `A`. -/
theorem localCompletion_isNoetherian
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    IsNoetherianRing (localCompletionRing C Δ) := by
  sorry

/-! ## The elementary calculation used to prove the ideal presentation -/

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
  sorry

theorem localCompletion_fractionField_eq_convergent_fractionField
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    Nonempty (FractionRing (localCompletionRing C Δ) ≃+*
      convergentPowerSeriesFractionField C) := by
  sorry

theorem localCompletion_nonunits_eq_x_multiple
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :
    {a : localCompletionRing C Δ | ¬ IsUnit a} =
      {a : localCompletionRing C Δ |
        (a : C.carrier) ∈ Ideal.span ({C.x} : Set C.carrier)} := by
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
  sorry

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
  sorry

/-- The `m`-adic completion of `A` at the displayed candidate ideal. -/
abbrev localCompletionCompletion (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) :=
  AdicCompletion (localCompletionCandidateMaximalIdeal C Δ)
    (localCompletionRing C Δ)

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

/-- The source's completion data, including the split map from formal series. -/
structure LocalCompletionCompletionData
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C) where
  psi : localCompletionCompletion C Δ →+* FormalPowerSeries
  psi_surjective : Function.Surjective psi
  sectionMap : FormalPowerSeries →+* localCompletionCompletion C Δ
  section_psi : sectionMap.comp psi = RingHom.id _
  induced_derivation : RelativeDerivation psi
  induced_derivation_on_section :
    ∀ f, induced_derivation (sectionMap f) = 0
  induced_derivation_on_localCompletion :
    ∀ a : localCompletionRing C Δ,
      induced_derivation
          (algebraMap (localCompletionRing C Δ)
            (localCompletionCompletion C Δ) a) =
        localCompletionDerivation C Δ a

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
  sorry

theorem completion_map_isEquiv
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ) :
    Nonempty (localCompletionCompletion C Δ ≃+* DualNumber FormalPowerSeries) := by
  sorry

theorem localCompletion_completion_is_nonreduced
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (Γ : LocalCompletionCompletionData C Δ) :
    ¬ IsReduced (localCompletionCompletion C Δ) := by
  sorry

/-! ## The displayed calculation and the chapter-level existence theorem -/

theorem localCompletionDerivation_x_pow_f
    (C : ConvergentPowerSeriesRing)
    (Δ : FerrandRaynaudDifferentialData C)
    (n : PositiveNat) :
    localCompletionDerivation C Δ (localCompletionXPowF C Δ n) = 1 := by
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
  sorry

/-- All data and all six claims of the characteristic-zero example. -/
theorem exists_local_ring_with_nonreduced_completion :
    ∃ (C : ConvergentPowerSeriesRing)
      (Δ : FerrandRaynaudDifferentialData C)
      (Γ : LocalCompletionCompletionData C Δ),
      (∀ c : C.carrier, IsIntegral (localCompletionRing C Δ) c) ∧
        IsLocalRing (localCompletionRing C Δ) ∧
        Ring.KrullDimLE 1 (localCompletionRing C Δ) ∧
        ¬ Ring.KrullDimLE 0 (localCompletionRing C Δ) ∧
        IsNoetherianRing (localCompletionRing C Δ) ∧
        Nonempty (localCompletionCompletion C Δ ≃+*
          DualNumber FormalPowerSeries) ∧
        ¬ IsReduced (localCompletionCompletion C Δ) := by
  sorry

end Formalization.«Books.Examples».Unit17
