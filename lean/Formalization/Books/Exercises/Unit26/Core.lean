import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Exercises, Chapter 26: Hilbert functions

This file contains the chapter-wide interfaces used by the definitions and
exercise statements.  The underlying graded objects are represented by
Mathlib's internal direct-sum decompositions, and graded algebras use
Mathlib's `GradedAlgebra` API.
-/

noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.ShortComplex

namespace Formalization.Books.Exercises.Unit26

/-! ## Numerical polynomials and graded modules -/

/-- A rational polynomial which takes integer values at every integer. -/
def IsNumericalPolynomial (f : Polynomial ℚ) : Prop :=
  ∀ n : ℤ, ∃ z : ℤ, f.eval (n : ℚ) = (z : ℚ)

/-- An internally graded module, expressed by its homogeneous submodules and
their direct-sum decomposition. -/
structure GradedModuleData (A M : Type u) (ι : Type v)
    [CommRing A] [AddCommGroup M] [Module A M] [DecidableEq ι] where
  component : ι → Submodule A M
  decomposition : DirectSum.Decomposition component

namespace GradedModuleData

/-- Every homogeneous component is a finite `A`-module. -/
def LocallyFinite {A M : Type u} {ι : Type v}
    [CommRing A] [AddCommGroup M] [Module A M] [DecidableEq ι]
    (G : GradedModuleData A M ι) : Prop :=
  ∀ n : ι, Module.Finite A (G.component n)

end GradedModuleData

/-! ## Euler–Poincaré functions and Hilbert polynomials -/

/-- An Euler–Poincaré function on finitely generated modules over a Noetherian
ring.  Invariance under isomorphism follows from additivity on short exact
sequences, so it is not repeated as a separate field. -/
structure EulerPoincareFunction (A : Type u) [CommRing A] [IsNoetherianRing A] where
  toFun : FGModuleCat.{u} A → ℤ
  map_shortExact' :
    ∀ (S : ShortComplex (FGModuleCat.{u} A)), S.ShortExact →
      toFun S.X₂ = toFun S.X₁ + toFun S.X₃

instance {A : Type u} [CommRing A] [IsNoetherianRing A] :
    CoeFun (EulerPoincareFunction A) (fun _ => FGModuleCat.{u} A → ℤ) :=
  ⟨EulerPoincareFunction.toFun⟩

/-- The Hilbert function attached to a locally finite integer-graded module and
an Euler–Poincaré function. -/
def GradedModuleData.hilbertFunction
    {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    (φ : EulerPoincareFunction A) (G : GradedModuleData A M ℤ)
    (hG : G.LocallyFinite) (n : ℤ) : ℤ :=
  letI : Module.Finite A (G.component n) := hG n
  φ (FGModuleCat.of A (G.component n))

/-- An integer-graded module has a Hilbert polynomial when its Hilbert function
eventually agrees with a numerical polynomial. -/
def GradedModuleData.HasHilbertPolynomial
    {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    (φ : EulerPoincareFunction A) (G : GradedModuleData A M ℤ)
    (hG : G.LocallyFinite) : Prop :=
  ∃ P : Polynomial ℚ, IsNumericalPolynomial P ∧
    ∀ᶠ n : ℤ in Filter.atTop,
      (G.hilbertFunction φ hG n : ℚ) = P.eval (n : ℚ)

/-- The corresponding eventual-polynomial predicate for a natural-number
graded Hilbert function, used by the weighted examples in this chapter. -/
def HasHilbertPolynomialOnNat (h : ℕ → ℕ) : Prop :=
  ∃ P : Polynomial ℚ, IsNumericalPolynomial P ∧
    ∀ᶠ n : ℕ in Filter.atTop, (h n : ℚ) = P.eval (n : ℚ)

/-! ## Graded algebras, modules, and maps -/

/-- Natural-number degrees act on integer degrees by addition. -/
instance natVAddInt : VAdd ℕ ℤ where
  vadd n d := (n : ℤ) + d

/-- A graded module over an internally graded algebra.  The decomposition and
the homogeneous scalar-action condition are Mathlib's canonical interfaces. -/
structure GradedModuleOver (A B M : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] where
  component : ℤ → Submodule A M
  decomposition : DirectSum.Decomposition component
  graded_smul : SetLike.GradedSMul 𝒜 component

/-- A degree-preserving linear map between internally graded modules. -/
structure GradedLinearMap
    {A M N : Type u} {ι : Type v}
    [CommRing A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [DecidableEq ι]
    (G : GradedModuleData A M ι) (H : GradedModuleData A N ι) where
  toLinearMap : M →ₗ[A] N
  map_component' : ∀ (n : ι) {m : M}, m ∈ G.component n →
    toLinearMap m ∈ H.component n

namespace GradedLinearMap

/-- The degree-`n` part of the kernel, viewed as a submodule of the kernel. -/
def kernelComponent
    {A M N : Type u} {ι : Type v}
    [CommRing A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [DecidableEq ι]
    {G : GradedModuleData A M ι} {H : GradedModuleData A N ι}
    (f : GradedLinearMap G H) (n : ι) :
    Submodule A (LinearMap.ker f.toLinearMap) :=
  (G.component n).comap (LinearMap.ker f.toLinearMap).subtype

end GradedLinearMap

end Formalization.Books.Exercises.Unit26
