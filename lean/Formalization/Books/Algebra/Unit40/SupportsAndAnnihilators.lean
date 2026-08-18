import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 40: supports and annihilators

The source's support and annihilator constructions are represented by Mathlib's canonical
`Module.support`, `Module.annihilator`, and the earlier chapter's `annihilatorOf`.  The
source-facing interfaces below record the statements that are not already available under a
chapter-specific name.
-/

namespace Formalization.Books.Algebra.Unit40

open Set
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Support and annihilators -/

/- The definition in the source is Mathlib's `Module.support R M`: the primes at which
   `LocalizedModule p.asIdeal.primeCompl M` is nontrivial. -/

/- The source's zero module is represented by the canonical `Subsingleton M` proposition. -/
theorem support_eq_empty_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.support R M = ∅ ↔ Subsingleton M :=
  Module.support_eq_empty_iff

/- The proof notes the stronger maximal-ideal consequence; it is recorded explicitly here. -/
theorem exists_maximal_mem_support {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Nontrivial M] :
    ∃ p : PrimeSpectrum R, p.asIdeal.IsMaximal ∧ p ∈ Module.support R M := by
  sorry

/- The earlier chapter's `annihilatorOf` is definitionally this span-annihilator expression;
   the source-facing theorem is stated using Mathlib's universe-polymorphic form. -/
theorem annihilator_element_mem_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) (r : R) :
    r ∈ Formalization.Books.Algebra.Unit03.annihilatorOf m ↔ r • m = 0 :=
  Formalization.Books.Algebra.Unit03.annihilatorOf_mem_iff m r

/- `Module.annihilator R M` is Mathlib's canonical ideal of scalars annihilating every
   element of `M`. -/
theorem annihilator_module_mem_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) :
    r ∈ Module.annihilator R M ↔ ∀ m : M, r • m = 0 :=
  Module.mem_annihilator

/-! ### Flat base change of annihilators -/

theorem annihilator_element_flat_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat R S] (m : M) :
    (Formalization.Books.Algebra.Unit03.annihilatorOf m).map (algebraMap R S) =
      Formalization.Books.Algebra.Unit03.annihilatorOf ((1 : S) ⊗ₜ[R] m) := by
  sorry

theorem annihilator_module_flat_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat R S] [Module.Finite R M] :
    (Module.annihilator R M).map (algebraMap R S) =
      Module.annihilator S (S ⊗[R] M) := by
  sorry

/-! ### Support of finite modules -/

theorem support_closed_of_finite
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    IsClosed (Module.support R M) ∧
      PrimeSpectrum.zeroLocus (Module.annihilator R M : Set R) = Module.support R M := by
  exact ⟨Module.isClosed_support, Module.support_eq_zeroLocus.symm⟩

/- The source's base-change statement is formulated with the canonical algebra structure on the
   target ring; this is the Lean form of a commutative ring map. -/
theorem support_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.support S (S ⊗[R] M) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' Module.support R M := by
  sorry

/- The source's element criterion uses the canonical localization map into
   `LocalizedModule p.asIdeal.primeCompl M`. -/
theorem support_element_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (m : M) :
    p ∈ PrimeSpectrum.zeroLocus
      ((Formalization.Books.Algebra.Unit03.annihilatorOf m : Ideal R) : Set R) ↔
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) m ≠ 0 := by
  sorry

/-! ### Finitely presented modules -/

theorem support_finitePresentation_constructible
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    IsClosed (Module.support R M) ∧ IsCompact (Module.support R M)ᶜ := by
  constructor
  · exact Module.isClosed_support
  · sorry

/-! ### Quotients, submodules, and exact sequences -/

theorem support_quotient_by_ideal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) :
    Module.support R (M ⧸ (I • (⊤ : Submodule R M))) =
      Module.support R M ∩ PrimeSpectrum.zeroLocus (I : Set R) :=
  Module.support_quotient I

theorem support_submodule_subset
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    Module.support R N ⊆ Module.support R M := by
  exact Module.support_subset_of_injective (Submodule.subtype N) Subtype.val_injective

/- A quotient module is represented by a surjective linear map. -/
theorem support_quotient_subset
    {R M Q : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup Q]
    [Module R M] [Module R Q] (q : M →ₗ[R] Q) (hq : Function.Surjective q) :
    Module.support R Q ⊆ Module.support R M :=
  Module.support_subset_of_surjective q hq

theorem support_short_exact
    {R N M Q : Type*} [CommRing R]
    [AddCommGroup N] [AddCommGroup M] [AddCommGroup Q]
    [Module R N] [Module R M] [Module R Q]
    (f : N →ₗ[R] M) (g : M →ₗ[R] Q)
    (hexact : Function.Exact f g) (hinjective : Function.Injective f)
    (hsurjective : Function.Surjective g) :
    Module.support R M = Module.support R Q ∪ Module.support R N := by
  simpa [Set.union_comm] using
    (Module.support_of_exact (f := f) (g := g) hexact hinjective hsurjective)

end
end Formalization.Books.Algebra.Unit40
