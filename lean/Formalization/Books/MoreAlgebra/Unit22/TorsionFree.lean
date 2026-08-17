import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Formalization.Books.Algebra.Unit157.SerresCriterion
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# More on Algebra, Chapter 22: Torsion free modules

This file records the source's torsion notions and the consequences collected
in the chapter.  Torsion-free modules use Mathlib's canonical
`Module.IsTorsionFree` class, and torsion submodules use `Submodule.torsion`.
The source's support and associated-prime terminology is represented by the
interfaces established in the earlier Algebra chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit22

open Set
open Formalization.Books.Algebra.Unit63
open Formalization.Books.Algebra.Unit67
open Formalization.Books.Algebra.Unit157
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Definitions -/

/-- The source's torsion-free predicate, delegated to Mathlib's canonical
`Module.IsTorsionFree` class. -/
abbrev TorsionFree (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : Prop :=
  Module.IsTorsionFree R M

/-- The source's torsion-module predicate, delegated to Mathlib's canonical
`Module.IsTorsion` abbreviation. -/
abbrev TorsionModule (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : Prop :=
  Module.IsTorsion R M

/-- Over a domain, membership in the canonical torsion submodule is exactly
the elementwise definition in the source. -/
theorem mem_torsion_iff_exists_smul_eq_zero
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (x : M) :
    x ∈ Submodule.torsion R M ↔
      ∃ r : R, r ≠ 0 ∧ r • x = 0 := by
  sorry

/-- The usual elementwise characterization of the source's torsion-free
condition. -/
theorem torsionFree_iff_smul_eq_zero
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    TorsionFree R M ↔
      ∀ (r : R) (x : M), r • x = 0 → r = 0 ∨ x = 0 :=
  Module.isTorsionFree_iff_smul_eq_zero

/-- Every element is torsion exactly when it belongs to the torsion
submodule. -/
theorem torsionModule_iff_forall_mem_torsion
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    TorsionModule R M ↔ ∀ x : M, x ∈ Submodule.torsion R M := by
  sorry

/-! ## Localization and torsion quotients -/

/-- The canonical map into a fraction-field tensor product. -/
noncomputable def fractionFieldTensorMap
    {R M K : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Field K] [Algebra R K] :
    M →ₗ[R] M ⊗[R] K :=
  (TensorProduct.mk R M K).flip 1

/-- A domain module is torsion-free exactly when its localization at all
nonzero elements is injective. -/
theorem torsionFree_iff_nonZeroDivisorLocalization_injective
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    TorsionFree R M ↔
      Function.Injective
        (LocalizedModule.mkLinearMap (nonZeroDivisors R) M) := by
  sorry

/-- For a fraction field, the localization criterion can be written using
the canonical map into the tensor product with that field. -/
theorem torsionFree_iff_fractionFieldTensorMap_injective
    {R M K : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    TorsionFree R M ↔
      Function.Injective
        (fractionFieldTensorMap (R := R) (M := M) (K := K)) := by
  sorry

/-- The torsion submodule is the kernel of the fraction-field map. -/
theorem torsion_eq_ker_fractionFieldTensorMap
    {R M K : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Submodule.torsion R M =
      LinearMap.ker
        (fractionFieldTensorMap (R := R) (M := M) (K := K)) := by
  sorry

/-- Quotienting by the torsion submodule produces a torsion-free module. -/
theorem quotient_by_torsion_isTorsionFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    TorsionFree R (M ⧸ Submodule.torsion R M) := by
  infer_instance

/-- Localization preserves torsion-freeness over a domain. -/
theorem localizedModule_isTorsionFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (S : Submonoid R)
    [Module.IsTorsionFree R M] :
    Module.IsTorsionFree (Localization S) (LocalizedModule S M) := by
  infer_instance

/-- Flat base change between domains preserves torsion-freeness. -/
theorem flat_baseChange_isTorsionFree
    {R R' M : Type*} [CommRing R] [CommRing R']
    [IsDomain R] [IsDomain R'] [Algebra R R']
    [AddCommGroup M] [Module R M] [Module.Flat R R']
    [Module.IsTorsionFree R M] :
    Module.IsTorsionFree R' (R' ⊗[R] M) := by
  sorry

/-! ## Extensions, local tests, and finite modules -/

/-- In a short exact sequence, torsion-freeness is inherited by the middle
module from the two end modules. -/
theorem shortExact_middle_isTorsionFree
    {R M M' M'' : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] M'')
    (hf : Function.Injective f)
    (h_exact : Function.Exact (f : M → M') (g : M' → M''))
    (hg : Function.Surjective g)
    [Module.IsTorsionFree R M] [Module.IsTorsionFree R M''] :
    Module.IsTorsionFree R M' := by
  sorry

/-- Torsion-freeness can be checked after localizing at every maximal ideal.
The points are represented by the canonical `MaximalSpectrum` type. -/
theorem torsionFree_iff_localized_at_maximal
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    TorsionFree R M ↔
      ∀ m : MaximalSpectrum R,
        Module.IsTorsionFree (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal M) := by
  sorry

/-- A finite torsion-free module over a domain embeds in a finite free module.
The finite free module is represented canonically by a finite Finsupp type. -/
theorem finite_torsionFree_iff_embeds_finiteFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    TorsionFree R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n →₀ R), Function.Injective f := by
  sorry

/-! ## The noetherian-domain criteria -/

/-- The finite-module characterizations of torsion-freeness over a noetherian
domain.  The last two clauses use the earlier chapters' support, associated
prime, embedded-prime, and `(S_1)` interfaces. -/
theorem finite_noetherian_domain_torsionFree_criteria
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    List.TFAE
      [TorsionFree R M,
       ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n →₀ R), Function.Injective f,
       ∀ p : PrimeSpectrum R,
         p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M ↔
           p.asIdeal = (⊥ : Ideal R),
       (∃ p : PrimeSpectrum R,
          p ∈ Module.support R M ∧ p.asIdeal = (⊥ : Ideal R)) ∧
         Formalization.Books.Algebra.Unit157.HasPropertySkModule R M 1,
       (∃ p : PrimeSpectrum R,
          p ∈ Module.support R M ∧ p.asIdeal = (⊥ : Ideal R)) ∧
         Formalization.Books.Algebra.Unit67.embeddedAssociatedPrimes
           (R := R) (M := M) = ∅] := by
  sorry

/-! ## Flatness, valuation rings, and Dedekind domains -/

/-- Every flat module over a domain is torsion-free. -/
theorem flat_isTorsionFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] :
    TorsionFree R M := by
  infer_instance

/-- Over a valuation ring, flatness and torsion-freeness coincide. -/
theorem valuationRing_flat_iff_torsionFree
    {A M : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [AddCommGroup M] [Module A M] :
    Module.Flat A M ↔ Module.IsTorsionFree A M := by
  sorry

/-- Over a Dedekind domain, flatness and torsion-freeness coincide. -/
theorem dedekindDomain_flat_iff_torsionFree
    {A M : Type*} [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] :
    Module.Flat A M ↔ Module.IsTorsionFree A M := by
  sorry

/-- A finite torsion-free module over a Dedekind domain is finite locally
free, using the earlier chapter's source-facing local-freeness predicate. -/
theorem finite_torsionFree_dedekindDomain_isFiniteLocallyFree
    {A M : Type*} [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] :
    Formalization.Books.Algebra.Unit78.FiniteLocallyFree A M := by
  sorry

/-- A finite torsion-free module over a PID is finite free.  Mathlib's
`IsPrincipalIdealRing` is the canonical PID class; its domain instance also
supplies the Dedekind-domain structure used in the surrounding source. -/
theorem finite_torsionFree_pid_isFree
    {A M : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] :
    Module.Free A M := by
  infer_instance

/-! The source's parenthetical DVR examples are covered by Mathlib's
canonical instances from discrete valuation rings to Dedekind domains. -/

/-! ## Hom modules -/

/-- If the target is torsion-free, the linear Hom module into it is
torsion-free. -/
theorem hom_into_torsionFree_isTorsionFree
    {R M N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.IsTorsionFree R N] :
    Module.IsTorsionFree R (M →ₗ[R] N) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit22
