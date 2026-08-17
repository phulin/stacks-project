import Formalization.Books.Algebra.Unit90.CoherentRings
import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Commutative Algebra, Chapter 91: Examples and non-examples of Mittag-Leffler modules

This file records the examples and non-examples at the end of the source
section.  The Mittag-Leffler predicate and the tensor-product APIs are the
canonical interfaces from Chapters 88 and 89.
-/

namespace Formalization.Books.Algebra.Unit91

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit84
open Formalization.Books.Algebra.Unit88
open Formalization.Books.Algebra.Unit89
open scoped DirectSum TensorProduct

universe u v w

noncomputable section

/-! ## Mittag-Leffler modules -/

/- The assertion that finitely presented modules are Mittag-Leffler is already
   `isMittagLefflerModule_of_finitePresentation` from Chapter 88. -/

/-- A finitely generated module is Mittag-Leffler exactly when it is finitely
presented (the first example in the source). -/
theorem finite_isMittagLeffler_iff_finitePresentation
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (hM : Module.Finite R (M : Type v)) :
    IsMittagLefflerModule M ↔ Module.FinitePresentation R (M : Type v) := by
  sorry

/-- A free module is Mittag-Leffler. -/
theorem isMittagLefflerModule_of_free
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (hM : Module.Free R (M : Type v)) :
    IsMittagLefflerModule M := by
  sorry

/-- A projective module is Mittag-Leffler. -/
theorem isMittagLefflerModule_of_projective
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (hM : Module.Projective R (M : Type v)) :
    IsMittagLefflerModule M := by
  sorry

/-! ## The flat Mittag-Leffler criterion -/

/-- For a flat module, Mittag-Lefflerness is equivalent to the existence of a
smallest submodule through which every tensor element from a finite free
module factors.  The predicate `tensorProductContains` is the canonical
tensor containment relation from Chapter 89. -/
theorem flat_isMittagLeffler_iff_minimal_tensor_submodule
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hflat : Module.Flat R M) :
    IsMittagLefflerModule (ModuleCat.of R M) ↔
      ∀ (F : Type u) [AddCommGroup F] [Module R F],
        Module.Free R F → Module.Finite R F →
          ∀ x : TensorProduct R F M, ∃ F' : Submodule R F,
            IsLeast {G : Submodule R F | tensorProductContains G x} F' := by
  sorry

/-! ## Products and power series -/

/-- A product of copies of a Noetherian ring is flat and Mittag-Leffler. -/
theorem modulePower_is_flat_and_mittagLeffler
    (R : Type u) [CommRing R] [IsNoetherianRing R] (A : Type v) :
    Module.Flat R (modulePower R A) ∧
      IsMittagLefflerModule (ModuleCat.of R (modulePower R A)) := by
  sorry

/-- Multivariate formal power series over a Noetherian ring are flat and
Mittag-Leffler as modules over the coefficient ring. -/
theorem mvPowerSeries_is_flat_and_mittagLeffler
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (n : ℕ) (hn : 0 < n) :
    Module.Flat R (MvPowerSeries (Fin n) R) ∧
      IsMittagLefflerModule
        (ModuleCat.of R (MvPowerSeries (Fin n) R)) := by
  sorry

/-! ## Non-examples -/

/- The first non-example reuses the rational module and the failed injectivity
   statement from Chapter 89. -/

/-- The rational numbers are not a Mittag-Leffler `ℤ`-module. -/
theorem rationalModule_not_mittagLeffler :
    ¬ IsMittagLefflerModule rationalModule := by
  sorry

/-- A flat, countably generated, non-projective module is not Mittag-Leffler.
This is the implication used in the second non-example. -/
theorem flat_countablyGenerated_nonprojective_not_mittagLeffler
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hflat : Module.Flat R M)
    (hcountable : Module.IsCountablyGenerated R M)
    (hprojective : ¬ Module.Projective R M) :
    ¬ IsMittagLefflerModule (ModuleCat.of R M) := by
  sorry

/-! ### Quotients and annihilators -/

/-- The quotient of a module by `I M`, expressed using the canonical
submodule quotient. -/
abbrev moduleQuotientByIdeal
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) : Type u :=
  M ⧸ (I • (⊤ : Submodule R M))

/-- The canonical class of an element in a quotient by `I M`. -/
def moduleQuotientElement
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (m : M) :
  moduleQuotientByIdeal (R := R) (M := M) I :=
  (I • (⊤ : Submodule R M)).mkQ m

/-- The scalar annihilator of an element after quotienting a module by `I M`. -/
def elementAnnihilatorModuloIdeal
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (m : M) : Ideal R :=
  (Submodule.span R
    ({moduleQuotientElement (R := R) (M := M) I m} :
      Set (moduleQuotientByIdeal (R := R) (M := M) I))).annihilator

/-! ### The product of power-series quotients -/

/-- The principal ideal `(x)` in the one-variable power-series ring `k[[x]]`. -/
def powerSeriesXIdeal (k : Type u) [Field k] : Ideal (PowerSeries k) :=
  Ideal.span {(PowerSeries.X : PowerSeries k)}

/-- The family of quotients `k[[x]]/(x^n)`, indexed by positive integers. -/
abbrev powerSeriesQuotientFamily (k : Type u) [Field k] (n : ℕ+) :
    ModuleCat.{u} (PowerSeries k) :=
  ModuleCat.of (PowerSeries k)
    (PowerSeries k ⧸ (powerSeriesXIdeal k) ^ (n : ℕ))

/-- The product `∏ₙ k[[x]]/(x^n)` from the third non-example. -/
abbrev powerSeriesTorsionProduct (k : Type u) [Field k] : Type u :=
  ∀ n : ℕ+, (powerSeriesQuotientFamily k n : Type u)

/-- The positive natural number `2^m`. -/
def positivePowOfTwo (m : ℕ) : ℕ+ :=
  ⟨2 ^ m, Nat.pow_pos (by decide)⟩

/-- The displayed element `ξ`, with `ξ_(2^m) = x^(2^(m-1))` for positive
`m` and zero at the other coordinates. -/
noncomputable def powerSeriesXiCoordinate
    (k : Type u) [Field k] (n : ℕ+) :
    (powerSeriesQuotientFamily k n : Type u) := by
  classical
  exact if h : ∃ m : ℕ, 1 ≤ m ∧ (n : ℕ) = 2 ^ m then
    Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
      ((PowerSeries.X : PowerSeries k) ^
        (2 ^ (Classical.choose h - 1)))
  else 0

/-- The element used to witness failure of the Mittag-Leffler condition. -/
noncomputable def powerSeriesXi (k : Type u) [Field k] :
    powerSeriesTorsionProduct k :=
  fun n => powerSeriesXiCoordinate k n

/-- At the powers of two, `ξ` has the displayed coordinates. -/
theorem powerSeriesXi_at_powerOfTwo
    (k : Type u) [Field k] (m : ℕ) (hm : 1 ≤ m) :
    powerSeriesXi k (positivePowOfTwo m) =
      Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (2 ^ m))
        ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1))) := by
  sorry

/-- The other coordinates of `ξ` vanish. -/
theorem powerSeriesXi_eq_zero_of_not_powerOfTwo
    (k : Type u) [Field k] (n : ℕ+)
    (h : ¬ ∃ m : ℕ, 1 ≤ m ∧ (n : ℕ) = 2 ^ m) :
    powerSeriesXi k n = 0 := by
  sorry

/-- The eventual annihilator calculation for the displayed element. -/
theorem powerSeriesXi_annihilator_eventually
    (k : Type u) [Field k] :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      elementAnnihilatorModuloIdeal
          ((powerSeriesXIdeal k) ^ (2 ^ m)) (powerSeriesXi k) =
        Ideal.span
          {((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)))} := by
  sorry

/-- The finite-module approximation supplied by the first characterization of
Mittag-Leffler modules. -/
theorem finite_annihilator_approximation_of_mittagLeffler
    (k : Type u) [Field k]
    (hML : IsMittagLefflerModule
      (ModuleCat.of (PowerSeries k) (powerSeriesTorsionProduct k))) :
    ∃ Q : ModuleCat.{u} (PowerSeries k),
      Module.Finite (PowerSeries k) (Q : Type u) ∧
        ∃ ξ' : (Q : Type u), ∀ l : ℕ, 1 ≤ l →
          elementAnnihilatorModuloIdeal
              ((powerSeriesXIdeal k) ^ l) (powerSeriesXi k) =
            elementAnnihilatorModuloIdeal
              ((powerSeriesXIdeal k) ^ l) ξ' := by
  sorry

/-- For a finite module over `k[[x]]`, the annihilator of an element in the
quotients by powers of `(x)` is eventually generated by `x^a` or by
`x^(l-a)`. -/
theorem finite_module_annihilator_eventually_principal
    (k : Type u) [Field k] (Q : ModuleCat.{u} (PowerSeries k))
    (ξ' : (Q : Type u)) (hQ : Module.Finite (PowerSeries k) (Q : Type u)) :
    ∃ a : ℕ,
      (∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l →
        elementAnnihilatorModuloIdeal
            ((powerSeriesXIdeal k) ^ l) ξ' =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ a)}) ∨
      (∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l →
        elementAnnihilatorModuloIdeal
            ((powerSeriesXIdeal k) ^ l) ξ' =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (l - a))}) := by
  sorry

/-- The product `∏ₙ k[[x]]/(x^n)` is not Mittag-Leffler. -/
theorem powerSeriesTorsionProduct_not_mittagLeffler
    (k : Type u) [Field k] :
    ¬ IsMittagLefflerModule
      (ModuleCat.of (PowerSeries k) (powerSeriesTorsionProduct k)) := by
  sorry

/-! ### The adic completion of the direct sum -/

/-- The direct sum `⊕ₙ k[[x]]/(x^n)`. -/
abbrev powerSeriesTorsionDirectSum (k : Type u) [Field k] : Type u :=
  ⨁ n : ℕ+, (powerSeriesQuotientFamily k n : Type u)

/-- Its `(x)`-adic module completion. -/
abbrev powerSeriesTorsionDirectSumCompletion
    (k : Type u) [Field k] : Type u :=
  AdicCompletion (powerSeriesXIdeal k) (powerSeriesTorsionDirectSum k)

/-- The map from the completion of the direct sum to the completion of the
product induced by the canonical direct-sum inclusion. -/
def powerSeriesDirectSumCompletionToProductCompletion
    (k : Type u) [Field k] :
    powerSeriesTorsionDirectSumCompletion k →ₗ[
        AdicCompletion (powerSeriesXIdeal k) (PowerSeries k)]
      AdicCompletion (powerSeriesXIdeal k) (powerSeriesTorsionProduct k) :=
  AdicCompletion.map (powerSeriesXIdeal k)
    (DirectSum.coeFnLinearMap (PowerSeries k))

/-- The element `ξ` is represented by an element of the `(x)`-adic completion
of the direct sum. -/
theorem powerSeriesXi_lies_in_directSum_adicCompletion
    (k : Type u) [Field k] :
    ∃ η : powerSeriesTorsionDirectSumCompletion k,
      powerSeriesDirectSumCompletionToProductCompletion k η =
        AdicCompletion.of (powerSeriesXIdeal k)
          (powerSeriesTorsionProduct k) (powerSeriesXi k) := by
  sorry

/-- The `(x)`-adic completion of the direct sum is not Mittag-Leffler. -/
theorem powerSeriesTorsionDirectSumCompletion_not_mittagLeffler
    (k : Type u) [Field k] :
    ¬ IsMittagLefflerModule
      (ModuleCat.of (PowerSeries k) (powerSeriesTorsionDirectSumCompletion k)) := by
  sorry

/-! ### The Artinian-local example -/

/-- The polynomial ring in the two variables `a` and `b`. -/
abbrev artinianLocalExamplePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

/-- The ideal `(a^2, ab, b^2)`. -/
def artinianLocalExampleRelationIdeal (k : Type u) [Field k] :
    Ideal (artinianLocalExamplePolynomialRing k) :=
  Ideal.span
    {MvPolynomial.X (0 : Fin 2) ^ 2,
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2),
      MvPolynomial.X (1 : Fin 2) ^ 2}

/-- The Artinian local ring `k[a,b]/(a^2,ab,b^2)`. -/
abbrev artinianLocalExampleBaseRing (k : Type u) [Field k] :=
  artinianLocalExamplePolynomialRing k ⧸ artinianLocalExampleRelationIdeal k

/-- The residue classes of `a` and `b`. -/
def artinianLocalExampleA (k : Type u) [Field k] :
    artinianLocalExampleBaseRing k :=
  Ideal.Quotient.mk (artinianLocalExampleRelationIdeal k)
    (MvPolynomial.X (0 : Fin 2))

def artinianLocalExampleB (k : Type u) [Field k] :
    artinianLocalExampleBaseRing k :=
  Ideal.Quotient.mk (artinianLocalExampleRelationIdeal k)
    (MvPolynomial.X (1 : Fin 2))

/-- The polynomial relation `at-b`. -/
def artinianLocalExamplePolynomialRelation (k : Type u) [Field k] :
    Polynomial (artinianLocalExampleBaseRing k) :=
  Polynomial.C (artinianLocalExampleA k) * Polynomial.X -
    Polynomial.C (artinianLocalExampleB k)

/-- The relation ideal `(at-b)` in the polynomial ring over the base ring. -/
def artinianLocalExamplePolynomialRelationIdeal (k : Type u) [Field k] :
    Ideal (Polynomial (artinianLocalExampleBaseRing k)) :=
  Ideal.span {artinianLocalExamplePolynomialRelation k}

/-- The finitely presented algebra `S = R[t]/(at-b)`. -/
abbrev artinianLocalExampleAlgebra (k : Type u) [Field k] :=
  AdjoinRoot (artinianLocalExamplePolynomialRelation k)

/-- The algebra in the final non-example, viewed as an `R`-module. -/
abbrev artinianLocalExampleModule (k : Type u) [Field k] :
    ModuleCat.{u} (artinianLocalExampleBaseRing k) :=
  ModuleCat.of (artinianLocalExampleBaseRing k)
    (artinianLocalExampleAlgebra k)

/-- The displayed algebra is finitely presented over its base ring. -/
theorem artinianLocalExample_finitePresentation
    (k : Type u) [Field k] :
    Algebra.FinitePresentation (artinianLocalExampleBaseRing k)
      (artinianLocalExampleAlgebra k) := by
  sorry

/-- The displayed algebra is countably generated as a module. -/
theorem artinianLocalExample_countablyGenerated
    (k : Type u) [Field k] :
    Module.IsCountablyGenerated (artinianLocalExampleBaseRing k)
      (artinianLocalExampleAlgebra k) := by
  sorry

/-- The displayed module is indecomposable. -/
theorem artinianLocalExample_indecomposable
    (k : Type u) [Field k] :
    Indecomposable (artinianLocalExampleModule k) := by
  sorry

/-- The displayed module is not finitely generated.  This implicit fact is
needed to turn the direct-sum conclusion into the source's non-example. -/
theorem artinianLocalExample_not_finite
    (k : Type u) [Field k] :
    ¬ Module.Finite (artinianLocalExampleBaseRing k)
      (artinianLocalExampleAlgebra k) := by
  sorry

/-- The base ring is Artinian. -/
theorem artinianLocalExample_baseRing_isArtinian
    (k : Type u) [Field k] :
    IsArtinianRing (artinianLocalExampleBaseRing k) := by
  sorry

/-- The base ring is local. -/
theorem artinianLocalExample_baseRing_isLocal
    (k : Type u) [Field k] :
    IsLocalRing (artinianLocalExampleBaseRing k) := by
  sorry

/-- The base ring is complete at its maximal ideal. -/
theorem artinianLocalExample_baseRing_isComplete
    (k : Type u) [Field k] :
    letI : IsLocalRing (artinianLocalExampleBaseRing k) :=
      artinianLocalExample_baseRing_isLocal k
    IsAdicComplete
      (IsLocalRing.maximalIdeal (artinianLocalExampleBaseRing k))
      (artinianLocalExampleBaseRing k) := by
  sorry

/-- The base ring is henselian local. -/
theorem artinianLocalExample_baseRing_isHenselianLocal
    (k : Type u) [Field k] :
    HenselianLocalRing (artinianLocalExampleBaseRing k) := by
  sorry

/- The source's forward reference to `lemma-split-ML-henselian` is exposed as
   a small, named interface because the later source lemma is not an earlier
   chapter dependency. -/

/-- A countably generated Mittag-Leffler module over a henselian local ring is
a direct sum of finitely presented modules. -/
def IsDirectSumOfFinitelyPresentedModules
    (R : Type u) [CommRing R] (M : ModuleCat.{v} R) : Prop :=
  ∃ (ι : Type v) (N : ι → ModuleCat.{v} R),
    (∀ i, Module.FinitePresentation R (N i : Type v)) ∧
      Nonempty ((M : Type v) ≃ₗ[R] (⨁ i, (N i : Type v)))

theorem split_mittagLeffler_over_henselian_local
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (M : ModuleCat.{v} R)
    (hcountable : Module.IsCountablyGenerated R (M : Type v))
    (hML : IsMittagLefflerModule M) :
    IsDirectSumOfFinitelyPresentedModules R M := by
  sorry

/-- In the final example, Mittag-Lefflerness would force the forbidden direct
sum decomposition. -/
theorem artinianLocalExample_mittagLeffler_implies_directSum
    (k : Type u) [Field k]
    (hML : IsMittagLefflerModule (artinianLocalExampleModule k)) :
    IsDirectSumOfFinitelyPresentedModules
      (artinianLocalExampleBaseRing k) (artinianLocalExampleModule k) := by
  sorry

/-- The finitely presented algebra in the final non-example is not
Mittag-Leffler as a module over the Artinian local base ring. -/
theorem artinianLocalExample_not_mittagLeffler
    (k : Type u) [Field k] :
    ¬ IsMittagLefflerModule (artinianLocalExampleModule k) := by
  sorry

end

end Formalization.Books.Algebra.Unit91
