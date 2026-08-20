import Formalization.Books.MoreAlgebra.Unit112.ExtensionsDiscreteValuationRings
import Formalization.Books.Algebra.Unit96.Completion
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic

/-!
This file formalizes the definitions and theorem interfaces in More on Algebra,
Chapter 114.  Polynomial roots and coefficient congruences use Mathlib's
canonical `Polynomial` and ideal APIs.  Completion and fraction-field data are
kept explicit so that the interfaces can be used with the chosen field models.
-/

namespace Formalization.Books.MoreAlgebra.Unit114

open Formalization.Books.MoreAlgebra.Unit112
open Formalization.Books.Algebra.Unit96
open scoped TensorProduct

noncomputable section

universe u v w

/-! ## Krasner's lemma -/

/-- The polynomial Taylor expansion used in the proof of Krasner's lemma:
the quadratic remainder is represented as a polynomial in the two variables.
-/
theorem polynomial_eval_add_with_quadratic_remainder
    {A : Type u} [CommRing A] (P : Polynomial A) :
    ∃ R : Polynomial (Polynomial A), ∀ x y : A,
      P.eval (x + y) =
        P.eval x + P.derivative.eval x * y +
          Polynomial.eval x (Polynomial.eval (Polynomial.C y) R) * y ^ 2 := by
  sorry

/-- Krasner's root-lifting lemma for a complete one-dimensional local domain.

The condition on `Q` says that every coefficient of the perturbation lies in
the indicated power of the maximal ideal.  Since the exponent `c` is a natural
number, the source's condition `c ≥ 0` is built into the interface. -/
theorem krasner_lemma
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (h_dim : ringKrullDim A = 1)
    (P : Polynomial A) (α : A)
    (hroot : P.eval α = 0)
    (hderiv : P.derivative.eval α ≠ 0) (c : ℕ) :
    ∃ n : ℕ, ∀ Q : Polynomial A,
      (∀ i : ℕ, Q.coeff i ∈ (IsLocalRing.maximalIdeal A) ^ n) →
      ∃ β : A,
        (P + Q).eval β = 0 ∧
          β - α ∈ (IsLocalRing.maximalIdeal A) ^ c := by
  sorry

/-! ## Approximation of finite separable extensions -/

/-- Data expressing that a finite separable extension is recovered after
completion of the base field. -/
structure ApproximateSeparableExtension
    (K Khat M : Type*) [Field K] [Field Khat] [Field M]
    [Algebra K Khat] [Algebra Khat M] where
  carrier : Type*
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finite : FiniteDimensional K carrier]
  [separable : Algebra.IsSeparable K carrier]
  baseChange :
    letI : Algebra Khat (Khat ⊗[K] carrier) :=
      Algebra.TensorProduct.leftAlgebra
    Nonempty (M ≃ₐ[Khat] Khat ⊗[K] carrier)

/-- A finite separable extension of the fraction field of the completion is
the base change of a finite separable extension of the original fraction
field.  The displayed compatibility condition identifies the two natural
maps from `A` into the completed fraction field. -/
theorem approximate_separable_extension
    {A K Khat M : Type u}
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Field K] [Field Khat] [Field M]
    [Algebra A K] [Algebra A Khat] [Algebra K Khat]
    [Algebra (ringCompletion (IsLocalRing.maximalIdeal A)) Khat]
    [Algebra Khat M] [IsScalarTower A K Khat]
    [FiniteDimensional Khat M] [Algebra.IsSeparable Khat M]
    (hK : IsFractionRing A K)
    (hKhat : IsFractionRing
      (ringCompletion (IsLocalRing.maximalIdeal A)) Khat)
    (hcompletion : ∀ a : A,
      algebraMap A Khat a =
        algebraMap (ringCompletion (IsLocalRing.maximalIdeal A)) Khat
          (algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A)) a)) :
    Nonempty (ApproximateSeparableExtension K Khat M) := by
  sorry

/-! ## Mixed characteristic -/

/-- A discrete valuation ring has mixed characteristic when its residue field
has positive prime characteristic and its fraction field has characteristic
zero. -/
def IsMixedCharacteristic
    (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] : Prop :=
  ∃ p : ℕ,
    Nat.Prime p ∧
      ringChar (DVRResidueField A) = p ∧
        ringChar (FractionRing A) = 0

/-- The localization `ℤ_(p)` used as the mixed-characteristic base DVR. -/
abbrev pLocalIntegers (p : ℕ) [Fact (Nat.Prime p)] :=
  Localization.AtPrime (Ideal.span {(p : ℤ)})

/-- A source-facing package for the `ℤ_(p)`-to-`A` extension.  The explicit
domain and DVR fields expose the instances that Mathlib's localization API
does not infer for this concrete presentation of `ℤ_(p)`. -/
structure MixedCharacteristicBaseMap
    (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (p : ℕ) [Fact (Nat.Prime p)] where
  baseDomain : IsDomain (pLocalIntegers p)
  baseDVR : @IsDiscreteValuationRing (pLocalIntegers p) _ baseDomain
  map :
    letI : IsDomain (pLocalIntegers p) := baseDomain
    letI : IsDiscreteValuationRing (pLocalIntegers p) := baseDVR
    DVRMap (pLocalIntegers p) A

/-- In mixed characteristic, the source's extension
`ℤ_(p) ⊂ A` is represented by a local injective map of DVRs. -/
theorem mixed_characteristic_base_extension
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (hA : IsMixedCharacteristic A) :
    ∃ p : ℕ, ∃ hp : Nat.Prime p,
      letI : Fact (Nat.Prime p) := ⟨hp⟩
      ringChar (DVRResidueField A) = p ∧
        ringChar (FractionRing A) = 0 ∧
          Nonempty (MixedCharacteristicBaseMap A p) := by
  sorry

/-- The absolute ramification index of a mixed-characteristic DVR, computed
from its `ℤ_(p)`-to-`A` extension. -/
noncomputable def absoluteRamificationIndex
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {p : ℕ} [Fact (Nat.Prime p)]
    (E : MixedCharacteristicBaseMap A p) : ℕ := by
  letI : IsDomain (pLocalIntegers p) := E.baseDomain
  letI : IsDiscreteValuationRing (pLocalIntegers p) := E.baseDVR
  exact ramificationIndex E.map

end

end Formalization.Books.MoreAlgebra.Unit114
