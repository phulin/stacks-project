import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.RingHom
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Commutative Algebra, Chapter 5: Finite modules and finitely presented modules

The source's finite and finitely presented module notions are Mathlib's
`Module.Finite` and `Module.FinitePresentation`.  The source-facing results
below use finite free modules `(Fin n → R)` and Mathlib's canonical short exact
complexes of modules.
-/

namespace Formalization.Books.Algebra.Unit05

open CategoryTheory

universe u v

/-! ## Definitions and finite free presentations -/

-- “Finite module” and “finitely presented module” are respectively
-- `Module.Finite` and `Module.FinitePresentation`.

/-- The finite-module definition is equivalent to a finite free surjection. -/
theorem finite_iff_exists_fin_surjective
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.Finite R M ↔
      ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Function.Surjective f := by
  constructor
  · exact fun h =>
      letI : Module.Finite R M := h
      Module.Finite.exists_fin' R M
  · rintro ⟨n, f, hf⟩
    exact Module.Finite.of_surjective f hf

/-- A finite presentation is exactly a right-exact sequence of finite free
modules ending in the given module. -/
theorem finitePresentation_iff_exists_fin_presentation
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.FinitePresentation R M ↔
      ∃ (n m : ℕ)
        (f : (Fin n → R) →ₗ[R] M)
        (g : (Fin m → R) →ₗ[R] (Fin n → R)),
        Function.Surjective f ∧ Function.Exact g f := by
  constructor
  · exact fun h =>
      letI : Module.FinitePresentation R M := h
      Module.FinitePresentation.exists_fin' R M
  · rintro ⟨n, m, f, g, hf, hgf⟩
    apply Module.finitePresentation_of_surjective f hf
    rw [LinearMap.exact_iff.mp hgf]
    exact Submodule.fg_range g

/-! ## Lifting maps -/

/-- A map out of a finite free module lifts through any map containing its
image. -/
theorem linearMap_exists_factorization_of_range_le
    {R : Type u} {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {n : ℕ} (α : (Fin n → R) →ₗ[R] M) (β : N →ₗ[R] M)
    (hαβ : LinearMap.range α ≤ LinearMap.range β) :
    ∃ γ : (Fin n → R) →ₗ[R] N, α = β.comp γ := by
  sorry

/-! ## Extensions -/

/- The source's sequence

    0 → M₁ → M₂ → M₃ → 0

  is represented by `S : ShortComplex (ModuleCat R)` together with
  `hS : S.ShortExact`. -/

/-- Finite modules are closed under extensions. -/
theorem finite_middle_of_shortExact
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₁ : Module.Finite R S.X₁) (h₃ : Module.Finite R S.X₃) :
    Module.Finite R S.X₂ := by
  sorry

/-- An extension of two finitely presented modules is finitely presented. -/
theorem finitePresentation_middle_of_shortExact
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₁ : Module.FinitePresentation R S.X₁)
    (h₃ : Module.FinitePresentation R S.X₃) :
    Module.FinitePresentation R S.X₂ := by
  sorry

/-- A quotient of a finite module is finite. -/
theorem finite_right_of_shortExact
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₂ : Module.Finite R S.X₂) :
    Module.Finite R S.X₃ := by
  sorry

/-- If the middle module is finitely presented and the left module is finite,
then the quotient is finitely presented. -/
theorem finitePresentation_right_of_shortExact
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₂ : Module.FinitePresentation R S.X₂)
    (h₁ : Module.Finite R S.X₁) :
    Module.FinitePresentation R S.X₃ := by
  sorry

/-- If the quotient is finitely presented and the middle module is finite,
then the left module is finite. -/
theorem finite_left_of_shortExact
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₃ : Module.FinitePresentation R S.X₃)
    (h₂ : Module.Finite R S.X₂) :
    Module.Finite R S.X₁ := by
  sorry

/-! ## Filtrations by cyclic modules -/

/-- A finite filtration whose successive factors are cyclic modules. -/
structure FiniteCyclicFiltration
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] where
  length : ℕ
  stage : Fin (length + 1) → Submodule R M
  ideal : Fin length → Ideal R
  zero : stage 0 = ⊥
  top : stage (Fin.last length) = ⊤
  step : ∀ i : Fin length,
    stage (Fin.castSucc i) ≤ stage (Fin.succ i)
  finite : ∀ i, Module.Finite R (stage i)
  quotient : ∀ i : Fin length,
    Nonempty
      (((stage (Fin.succ i)) ⧸
        (stage (Fin.castSucc i)).comap (stage (Fin.succ i)).subtype)
        ≃ₗ[R] (R ⧸ ideal i))

/-- Every finite module has a finite filtration with cyclic successive
quotients. -/
theorem exists_finiteCyclicFiltration
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (hM : Module.Finite R M) :
    Nonempty (FiniteCyclicFiltration R M) := by
  sorry

/-! ## Finite modules over a larger ring -/

/-- A module finite over a ring is finite over any larger ring acting on it;
the smaller action is the one induced by the ring map. -/
theorem finite_over_ringHom
    {R S M : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) [AddCommGroup M] [Module S M]
    (hM : letI : Module R M := Module.compHom M f; Module.Finite R M) :
    Module.Finite S M := by
  exact
    letI : Module R S := Module.compHom S f
    letI : Module R M := Module.compHom M f
    letI : IsScalarTower R S M := SMul.comp.isScalarTower f
    letI : Module.Finite R M := hM
    Module.Finite.of_restrictScalars_finite R S M

end Formalization.Books.Algebra.Unit05
