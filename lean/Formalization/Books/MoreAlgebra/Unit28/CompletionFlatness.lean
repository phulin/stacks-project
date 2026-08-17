import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.Algebra.Unit82.UniversallyInjective
import Formalization.Books.Algebra.Unit87
import Formalization.Books.Algebra.Unit96.Completion
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Noetherian.Basic

/-!
# More on Algebra, Chapter 28: Completion and flatness

The completion is Mathlib's `AdicCompletion`.  Direct sums and products use
the canonical `DirectSum` and function-space module structures.  Inverse
systems are the canonical functors on opposite preorders, and Tor is the
canonical construction from Algebra, Chapter 75.
-/

namespace Formalization.Books.MoreAlgebra.Unit28

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit75
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Algebra.Unit96
open Formalization.Books.Categories.Unit21
open scoped DirectSum TensorProduct

universe u v

noncomputable section

/-! ## The completed direct sum and its product map -/

/- The completion of each coordinate is identified with the coordinate ring
   by the existing `AdicCompletion.ofLinearEquiv` under adic completeness. -/
/-- The canonical map from the completion of a direct sum of copies of `R` to
the corresponding product of copies of `R`. -/
noncomputable def completedDirectSumToProduct
    {R : Type u} [CommRing R] (I : Ideal R) (A : Type v)
    [IsAdicComplete I R] :
    AdicCompletion I (⨁ _ : A, R) →ₗ[R] (∀ _ : A, R) :=
  LinearMap.pi (fun a =>
    (AdicCompletion.ofLinearEquiv I R).symm.toLinearMap.comp
      ((AdicCompletion.map I (DirectSum.component R A (fun _ : A => R) a)).restrictScalars R))

/-- Under Noetherianity and completeness, the completed-direct-sum map is
universally injective. -/
theorem completedDirectSumToProduct_universallyInjective
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (A : Type v)
    [IsAdicComplete I R] :
    universallyInjective (completedDirectSumToProduct I A) := by
  sorry

/-! ## Flatness of completed direct sums -/

/-- The completion of an arbitrary direct sum of copies of a Noetherian ring
is flat over that ring. -/
theorem completedDirectSum_flat
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (A : Type v) :
    Module.Flat R (AdicCompletion I (⨁ _ : A, R)) := by
  sorry

/-! ## Strict Tor vanishing -/

/- The source's `A/I^n` is written as the canonical quotient module
   `A ⧸ (I^n • ⊤)`, so the transition map is exactly Mathlib's
   `Submodule.factorPow`. -/
/-- The transition map on the canonical Tor groups induced by a power
quotient transition. -/
noncomputable def torPowerTransition
    {A : Type u} [CommRing A] (I : Ideal A) (M : ModuleCat.{u} A)
    (p : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Tor M (ModuleCat.of A
      (A ⧸ (I ^ n • (⊤ : Submodule A A)))) p ⟶
      Tor M (ModuleCat.of A
        (A ⧸ (I ^ m • (⊤ : Submodule A A)))) p :=
  torMapSecond M
    (ModuleCat.of A (A ⧸ (I ^ n • (⊤ : Submodule A A))))
    (ModuleCat.of A (A ⧸ (I ^ m • (⊤ : Submodule A A))))
    (ModuleCat.ofHom (Submodule.factorPow I A hmn)) p

/- The source reference notes that the word “strict” was omitted from the
   published statement; the positive exponent below records the intended
   assertion. -/
/-- For a finite module over a Noetherian ring, the transition maps on positive
Tor groups of successive power quotients are eventually zero. -/
theorem torPowerTransition_eventually_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)]
    (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, 0 < c ∧
      ∀ n : ℕ, c ≤ n →
        torPowerTransition I M p (m := n - c) (n := n) (Nat.sub_le n c) = 0 := by
  sorry

/-! ## Flat inverse limits -/

/- This is the canonical way to tensor every stage of an inverse system by a
   fixed module. -/
/-- The inverse system obtained by tensoring every stage on the left by `Q`. -/
abbrev tensorInverseSystem
    {A : Type u} [CommRing A] (Q : ModuleCat.{u} A)
    {I : Type v} [Preorder I]
    (F : InverseSystem I (ModuleCat.{u} A)) :
    InverseSystem I (ModuleCat.{u} A) :=
  F ⋙ MonoidalCategory.tensorLeft Q

/- The source's phrase “flat over `A/I^n`” includes the induced quotient
   action.  `Module.IsTorsionBySet.module` is the established project API for
   that action. -/
/-- A stage is flat over the indicated power quotient, with its quotient action
induced from the given `A`-module structure. -/
def IsFlatOverPowerQuotient
    {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ)
    (M : ModuleCat.{u} A) : Prop :=
  ∃ h : Module.IsTorsionBySet A (M : Type u) ((I ^ n : Ideal A) : Set A),
    letI : SMul (A ⧸ I ^ n) (M : Type u) := h.hasSMul
    letI : Module (A ⧸ I ^ n) (M : Type u) := h.module
    Module.Flat (A ⧸ I ^ n) (M : Type u)

/-- A surjective inverse system of modules flat over its successive power
quotients has a flat inverse limit, and tensoring a finite module commutes
with that inverse limit. -/
theorem inverseLimit_flat
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (F : InverseSystem ℕ (ModuleCat.{u} A))
    (hflat : ∀ n : ℕ, IsFlatOverPowerQuotient I n (F.obj (Opposite.op n)))
    (hsurj : ∀ n : ℕ,
      Function.Surjective ((F.map (opHomOfLE (Nat.le_succ n))).hom)) :
    Module.Flat A ((InverseSystemLimit F : ModuleCat.{u} A) : Type u) ∧
      ∀ (Q : ModuleCat.{u} A) [Module.Finite A (Q : Type u)],
        Nonempty ((MonoidalCategory.tensorLeft Q).obj (InverseSystemLimit F) ≅
          (InverseSystemLimit (tensorInverseSystem Q F) : ModuleCat.{u} A)) := by
  sorry

/-! ## Flatness after completion -/

/-- Flatness of the reduction together with vanishing first Tor implies that
completion is flat over the Noetherian completed ring. -/
theorem flat_after_completion
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)]
    (hflat : Module.Flat (R ⧸ I)
      ((M : Type u) ⧸ (I • (⊤ : Submodule R (M : Type u)))))
    (htor : IsZero (Tor M (ModuleCat.of R (R ⧸ I)) 1)) :
    IsNoetherianRing (ringCompletion I) ∧
      Module.Flat (ringCompletion I) (completion I (M : Type u)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit28
