import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.LocalProperties.Injective
import Mathlib.RingTheory.RingHom.Flat

/-!
# Injective modules

This file records the precise statements in Chapter 3 of the dualizing-complexes
book.  The statements use Mathlib's module-theoretic injectivity predicate and
its canonical constructions for change of scalars, localization, torsion, and
polynomial modules.
-/

namespace Formalization.Books.Dualizing.Unit03

universe u v w

open scoped TensorProduct
noncomputable section

/-! ### Products and change of rings -/

theorem product_injective
    {R : Type u} [CommRing R] {ι : Type w} {M : ι → Type v}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Injective R (M i)] [Small.{v} R] :
    Module.Injective R (∀ i, M i) := by
  infer_instance

theorem injective_of_flat
    {R S E : Type*} [CommRing R] [CommRing S] [AddCommGroup E]
    [Module S E] (f : R →+* S) (hf : f.Flat)
    [Module.Injective S E] :
    @Module.Injective R _ E _ (Module.compHom E f) := by
  sorry

theorem injective_of_ring_epimorphism
    {R S : Type u} {E : Type v} [CommRing R] [CommRing S] [AddCommGroup E]
    [Module S E] (f : R →+* S) (hf : CategoryTheory.Epi (CommRingCat.ofHom f))
    (hE : @Module.Injective R _ E _ (Module.compHom E f)) :
    Module.Injective S E := by
  sorry

/-! ### Hom and coextension of scalars -/

theorem hom_injective
    {R S E : Type*} [CommRing R] [CommRing S] [AddCommGroup E]
    [Module R E] (f : R →+* S) [Module.Injective R E] :
    Module.Injective S
      ((ModuleCat.coextendScalars f).obj (ModuleCat.of R E) : Type _) := by
  sorry

/-! ### Essential extensions -/

def IsEssentialExtension
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (E E' : Submodule R M) : Prop :=
  E ≤ E' ∧ ∀ N : Submodule R M, N ≤ E' → N ≠ ⊥ → N ⊓ E ≠ ⊥

def IsEssentialExtensionMap
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) : Prop :=
  Function.Injective f ∧
    ∀ P : Submodule R N, P ≠ ⊥ → P ⊓ LinearMap.range f ≠ ⊥

theorem injective_iff_essential_extensions_trivial
    {R I : Type*} [CommRing R] [AddCommGroup I] [Module R I]
    [Module.Injective R I] (E : Submodule R I) :
    Module.Injective R E ↔
      ∀ E' : Submodule R I, IsEssentialExtension E E' → E = E' := by
  sorry

theorem injective_iff_essential_extension_maps_trivial
    {R M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Injective R M ↔
      ∀ (N : ModuleCat.{v} R) (f : ModuleCat.of R M ⟶ N),
        IsEssentialExtensionMap f.hom → Function.Surjective f.hom := by
  sorry

/-! ### A reduced ring and a minimal-prime localization -/

theorem minimal_prime_localization_isField
    {R : Type u} [CommRing R] [IsReduced R] (p : Ideal R) [p.IsPrime]
    (hp : IsMinimalPrime p) :
    IsField (Localization.AtPrime p) := by
  sorry

theorem minimal_prime_localization_injective
    {R : Type u} [CommRing R] [IsReduced R] (p : Ideal R) [p.IsPrime]
    (hp : IsMinimalPrime p) :
    Module.Injective R (Localization.AtPrime p) := by
  sorry

theorem hom_to_minimal_prime_localization_equiv
    {R : Type u} [CommRing R] [IsReduced R]
    {M : Type v} [AddCommGroup M] [Module R M] (p : Ideal R) [p.IsPrime]
    (hp : IsMinimalPrime p) :
    Nonempty
      ((M →ₗ[R] Localization.AtPrime p) ≃+
        (LocalizedModule p.primeCompl M →ₗ[Localization.AtPrime p]
          Localization.AtPrime p)) := by
  sorry

/-! ### Noetherian sums, localization, and torsion -/

theorem directSum_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R] {ι : Type w}
    {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Injective R (M i)] :
    Module.Injective R (DirectSum ι M) := by
  sorry

theorem localization_injective
    {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [IsNoetherianRing R] (S : Submonoid R) [Module.Injective R E] :
    Module.Injective (Localization S) (LocalizedModule S E) := by
  sorry

theorem principal_power_torsion_injective
    {R I : Type*} [CommRing R] [AddCommGroup I] [Module R I]
    [IsNoetherianRing R] [Module.Injective R I] (f : R) :
    Module.Injective R (Submodule.torsion' R I (Submonoid.powers f)) := by
  sorry

theorem ideal_power_torsion_injective
    {R I : Type*} [CommRing R] [AddCommGroup I] [Module R I]
    [IsNoetherianRing R] [Module.Injective R I] (J : Ideal R) :
    Module.Injective R (Ideal.primaryComponent I J) := by
  sorry

/-! ### Polynomial extensions -/

def polynomial_tensorProduct_equiv
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    (Polynomial A ⊗[A] E) ≃ₗ[Polynomial A] PolynomialModule A E :=
  PolynomialModule.polynomialTensorProductLEquivPolynomialModule A E

def polynomial_module_directSum_equiv
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    PolynomialModule A E ≃ₗ[A] DirectSum ℕ (fun _ : ℕ => E) :=
  (PolynomialModule.coeffLinearEquiv A A).trans
    (finsuppLEquivDirectSum A E ℕ)

abbrev polynomial_hom_module
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :=
  (ModuleCat.coextendScalars (algebraMap A (Polynomial A))).obj
    ((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
      (ModuleCat.of (Polynomial A) (PolynomialModule A E)))

abbrev polynomial_base_module
    (A : Type u) [CommRing A] :=
  (ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
    (ModuleCat.of (Polynomial A) (Polynomial A))

def polynomial_first_map
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    ModuleCat.of (Polynomial A) (PolynomialModule A E) →ₗ[Polynomial A]
      polynomial_hom_module A E :=
  ModuleCat.RestrictionCoextensionAdj.app' (algebraMap A (Polynomial A))
    (ModuleCat.of (Polynomial A) (PolynomialModule A E))

theorem polynomial_first_map_apply
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E]
    (p : PolynomialModule A E) (f : polynomial_base_module A) :
    polynomial_first_map A E p f = (let f' : Polynomial A := f; f' • p) := by
  sorry

def polynomial_differential_formula
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E]
    (φ : polynomial_hom_module A E) (f : polynomial_base_module A) :
    PolynomialModule A E :=
  let f' : Polynomial A := f
  φ (show polynomial_base_module A from
      (show Polynomial A from (Polynomial.X : Polynomial A) * f')) -
    (Polynomial.X : Polynomial A) • φ f

theorem polynomial_hom_module_as_product
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    Nonempty
      (((ModuleCat.restrictScalars (algebraMap A (Polynomial A))).obj
          (polynomial_hom_module A E)) ≃ₗ[A]
        (ModuleCat.of A (ℕ → PolynomialModule A E))) := by
  sorry

theorem polynomial_short_exact
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E] :
    ∃ d : polynomial_hom_module A E →ₗ[Polynomial A] polynomial_hom_module A E,
      (∀ φ f, d φ f = polynomial_differential_formula A E φ f) ∧
        Function.Injective (polynomial_first_map A E) ∧
        Function.Exact (polynomial_first_map A E) d ∧
        Function.Surjective d := by
  sorry

theorem polynomial_module_injective_amplitude
    (A E : Type u) [CommRing A] [AddCommGroup E] [Module A E]
    [IsNoetherianRing A] [Module.Injective A E] :
    CategoryTheory.HasInjectiveDimensionLE
        (ModuleCat.of (Polynomial A) (PolynomialModule A E)) 1 ∧
      CategoryTheory.injectiveDimension
          (ModuleCat.of (Polynomial A) (PolynomialModule A E)) ≠ ⊤ := by
  sorry

end
end Formalization.Books.Dualizing.Unit03
