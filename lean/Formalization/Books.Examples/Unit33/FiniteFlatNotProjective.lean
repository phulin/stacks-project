import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Examples, Chapter 33: A finite flat module which is not projective

This file records the smooth-function counterexample and the associated affine
scheme morphism from the source section.  The substantive analytic and
algebraic arguments belong to the proof stage.
-/

noncomputable section

open AlgebraicGeometry
open scoped ContDiff

namespace Formalization.«Books.Examples».Unit33

/-! ## The smooth-function ring and its two ideals -/

/-- The subring of `ℝ → ℝ` consisting of infinitely differentiable functions. -/
def smoothFunctionSubring : Subring (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by
    change ContDiff ℝ ∞ (0 : ℝ → ℝ)
    exact contDiff_zero_fun
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    change ContDiff ℝ ∞ (fun x : ℝ => f x + g x)
    exact hf.add hg
  one_mem' := by
    change ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ))
    exact contDiff_const
  mul_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    change ContDiff ℝ ∞ (fun x : ℝ => f x * g x)
    exact hf.mul hg
  neg_mem' := by
    intro f hf
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ (fun x : ℝ => -f x)
    exact hf.neg

/-- The ring `R = C^∞(ℝ)` in the source example. -/
abbrev SmoothRing := (smoothFunctionSubring : Type)

/-- Evaluation at the origin on the smooth-function ring. -/
def smoothEvaluationAtZero : SmoothRing →+* ℝ :=
  (Pi.evalRingHom (fun _ : ℝ => ℝ) (0 : ℝ)).comp smoothFunctionSubring.subtype

/-- The ideal `𝔪 = {f | f(0) = 0}`. -/
def exampleMaximalIdeal : Ideal SmoothRing :=
  RingHom.ker smoothEvaluationAtZero

@[simp]
theorem mem_exampleMaximalIdeal_iff (f : SmoothRing) :
    f ∈ exampleMaximalIdeal ↔ f.1 0 = 0 := by
  simp [exampleMaximalIdeal, smoothEvaluationAtZero]

/-- The ideal `𝔪` is maximal (and hence prime), as used by the notation `R_𝔪`. -/
instance exampleMaximalIdeal_isMaximal : exampleMaximalIdeal.IsMaximal := by
  sorry

/-- A smooth function vanishes on a neighborhood of the origin. -/
def VanishesNearZero (f : SmoothRing) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε → f.1 x = 0

/-- The ideal `I` of smooth functions which vanish near the origin. -/
def exampleGermIdeal : Ideal SmoothRing where
  carrier := {f | VanishesNearZero f}
  zero_mem' := by
    change VanishesNearZero (0 : SmoothRing)
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    simp
  add_mem' := by
    intro f g hf hg
    change VanishesNearZero f at hf
    change VanishesNearZero g at hg
    change VanishesNearZero (f + g)
    rcases hf with ⟨ε, hε, hf⟩
    rcases hg with ⟨δ, hδ, hg⟩
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩
    intro x hx
    change f.1 x + g.1 x = 0
    rw [hf x (lt_of_lt_of_le hx (min_le_left _ _)),
      hg x (lt_of_lt_of_le hx (min_le_right _ _)), add_zero]
  smul_mem' := by
    intro r f hf
    change VanishesNearZero f at hf
    change VanishesNearZero (r • f)
    rcases hf with ⟨ε, hε, hf⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx
    change r.1 x * f.1 x = 0
    rw [hf x hx, mul_zero]

@[simp]
theorem mem_exampleGermIdeal_iff (f : SmoothRing) :
    f ∈ exampleGermIdeal ↔ VanishesNearZero f := by
  rfl

/-! ## The finite flat module -/

/-- The localization `R_𝔪` at the complement of the origin ideal. -/
abbrev exampleLocalization := Localization exampleMaximalIdeal.primeCompl

/-- The module `M = R/I` from the source example. -/
abbrev ExampleModule := SmoothRing ⧸ exampleGermIdeal

/-- The displayed identification `R_𝔪 ≅ R/I`. -/
theorem exampleLocalization_equiv_module :
    Nonempty (exampleLocalization ≃ₐ[SmoothRing] ExampleModule) := by
  sorry

/-- The module in the example is finite over `R`. -/
theorem exampleModule_finite : Module.Finite SmoothRing ExampleModule := by
  infer_instance

/-- The module in the example is flat over `R`. -/
theorem exampleModule_flat : Module.Flat SmoothRing ExampleModule := by
  sorry

/-- The module in the example is not projective over `R`. -/
theorem exampleModule_not_projective : ¬ Module.Projective SmoothRing ExampleModule := by
  sorry

/-- The concrete smooth-function example is finite flat but not projective. -/
theorem exampleModule_finite_flat_not_projective :
    Module.Finite SmoothRing ExampleModule ∧
      Module.Flat SmoothRing ExampleModule ∧
        ¬ Module.Projective SmoothRing ExampleModule := by
  exact ⟨exampleModule_finite, exampleModule_flat, exampleModule_not_projective⟩

/-- There exists a finite flat module which is not projective. -/
theorem exists_finite_flat_nonprojective :
    ∃ (R : Type) (_ : CommRing R) (M : Type) (_ : AddCommGroup M)
      (_ : Module R M),
      Module.Finite R M ∧ Module.Flat R M ∧ ¬ Module.Projective R M := by
  refine ⟨SmoothRing, inferInstance, ExampleModule, inferInstance, inferInstance, ?_⟩
  exact exampleModule_finite_flat_not_projective

/-! ## The associated flat closed immersion -/

/-- The affine morphism `Spec(R/I) → Spec(R)` induced by the quotient map. -/
abbrev smoothRingCommRing : CommRingCat := CommRingCat.of SmoothRing

abbrev exampleModuleCommRing : CommRingCat := CommRingCat.of ExampleModule

noncomputable def exampleSpecMap :
    Spec exampleModuleCommRing ⟶ Spec smoothRingCommRing :=
  Spec.map <| CommRingCat.ofHom <| Ideal.Quotient.mk exampleGermIdeal

/-- The displayed affine morphism is a closed immersion. -/
instance exampleSpecMap_isClosedImmersion : IsClosedImmersion exampleSpecMap := by
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The displayed affine morphism is flat. -/
instance exampleSpecMap_isFlat : AlgebraicGeometry.Flat exampleSpecMap := by
  change AlgebraicGeometry.Flat
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk exampleGermIdeal)))
  rw [AlgebraicGeometry.Flat.SpecMap_iff]
  exact exampleModule_flat

/-- The displayed affine morphism is not an open immersion. -/
theorem exampleSpecMap_not_isOpenImmersion :
    ¬ IsOpenImmersion exampleSpecMap := by
  sorry

/-- There exists a flat closed immersion which is not open. -/
theorem exists_flat_closedImmersion_not_open :
    ∃ (X Y : Scheme.{0}) (f : X ⟶ Y),
      IsClosedImmersion f ∧ AlgebraicGeometry.Flat f ∧ ¬ IsOpenImmersion f := by
  refine ⟨Spec exampleModuleCommRing, Spec smoothRingCommRing,
    exampleSpecMap, ?_⟩
  exact ⟨inferInstance, inferInstance, exampleSpecMap_not_isOpenImmersion⟩

end Formalization.«Books.Examples».Unit33
