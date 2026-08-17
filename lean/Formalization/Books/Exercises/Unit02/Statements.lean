import Formalization.Books.Exercises.Unit02.Core

import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Exercises, Chapter 2: Colimits

This file records the theorem interfaces for the exercises in the source
section.  Proposition proofs are intentionally deferred to the proving stage
unless Mathlib already supplies the exact result.
-/

noncomputable section

universe u v w

open CategoryTheory
open CategoryTheory.Limits

namespace Formalization.Books.Exercises.Unit02

/-! ## Directed colimits of rings -/

/-- The canonical ring colimit has the universal property stated in the first
exercise. -/
theorem ringColimit_universal
    {I : Type u} [Preorder I]
    {A : I → Type v} [∀ i, CommRing (A i)]
    (φ : RingSystem I A) [DirectedSystem A (φ · · ·)]
    (_hI : IsDirectedSet I)
    {B : Type w} [CommRing B] (ψ : ∀ i, A i →+* B)
    (hψ : ∀ i j (hij : i ≤ j) (x : A i),
      ψ j (φ i j hij x) = ψ i x) :
    ∃! g : ringColimit φ →+* B,
      ∀ i, g.comp (ringColimitMap φ i) = ψ i := by
  sorry

/-! ## Prime spectra -/

/-- The prime spectrum of a directed ring colimit is in bijection with the
compatible families of primes in its stages. -/
theorem primeSpectrum_colimit_bijective
    {I : Type u} [Preorder I]
    {A : I → Type v} [∀ i, CommRing (A i)]
    (φ : RingSystem I A) [DirectedSystem A (φ · · ·)]
    (hI : IsDirectedSet I) :
    Function.Bijective (primeSpectrumColimitMap φ) := by
  sorry

/-- If every transition map induces a surjection on prime spectra, then each
stage maps surjectively to the spectrum of the directed colimit. -/
theorem primeSpectrum_colimit_map_surjective_of_stagewise
    {I : Type u} [Preorder I]
    {A : I → Type v} [∀ i, CommRing (A i)]
    (φ : RingSystem I A) [DirectedSystem A (φ · · ·)]
    (hI : IsDirectedSet I)
    (hSpec : ∀ i j (hij : i ≤ j),
      Function.Surjective (PrimeSpectrum.comap (φ i j hij))) :
    ∀ i, Function.Surjective (PrimeSpectrum.comap (ringColimitMap φ i)) := by
  sorry

/-! ## Integral extensions -/

/-- Every finite subalgebra in an integral extension is finite as a module over
the base ring. -/
theorem finiteSubalgebra_finite_of_integral
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (s : Finset B) :
    Module.Finite A (finiteSubalgebra (A := A) (B := B) s) := by
  exact Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
    (fun x _ => Algebra.IsIntegral.isIntegral x)

/-- The finite subalgebras generated inside `B` have colimit `B`. -/
theorem finiteSubalgebra_colimit_bijective
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    Function.Bijective (finiteSubalgebraColimitMap (A := A) (B := B)) := by
  sorry

/-- An integral injective ring map induces a surjection on prime spectra. -/
theorem integral_extension_primeSpectrum_surjective
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (hIntegral : f.IsIntegral) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  exact hIntegral.comap_surjective hf

/-! ## Tensor products -/

/- The displayed tensor-product isomorphism is the real definition
`tensorProductDirectedColimitEquiv`, whose body is Mathlib's canonical
`TensorProduct.directLimitRight` equivalence. -/

/-! ## Finite presentation -/

/-- A source-facing characterization of finite presentation by a cokernel of a
map between finite free modules. -/
theorem finitePresentation_iff_finite_free_cokernel
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.FinitePresentation R M ↔
      ∃ n m : ℕ,
        ∃ f : ModuleCat.of R (Fin n → R) ⟶ ModuleCat.of R (Fin m → R),
          Nonempty (ModuleCat.of R M ≅ cokernel f) := by
  sorry

/-! ## Colimits of modules -/

/-- Every module is the directed colimit of its finitely generated
submodules.  The equivalence is Mathlib's canonical `Module.fgSystem.equiv`. -/
theorem module_is_colimit_of_finitely_generated_submodules
    {R M : Type u} [Semiring R] [AddCommMonoid M] [Module R M] :
    Nonempty
      (letI : DecidableEq (Submodule R M) := Classical.decEq _
       Module.DirectLimit
          (fun N : {N : Submodule R M // N.FG} => N)
          (Module.fgSystem R M) ≃ₗ[R] M) := by
  let h : DecidableEq (Submodule R M) := Classical.decEq _
  exact ⟨@Module.fgSystem.equiv R M _ _ _ h⟩

/-- Every module admits a directed-colimit presentation by finitely presented
modules. -/
theorem exists_directed_finitelyPresented_module_colimit
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    Nonempty
      (DirectedFinitelyPresentedModuleColimit (ModuleCat.of R M)) := by
  sorry

end Formalization.Books.Exercises.Unit02
