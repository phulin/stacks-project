import Formalization.Books.MoreAlgebra.Unit53.AbelianCategoriesOfModules
import Formalization.Books.MoreAlgebra.Unit67.TorDimension
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# More on Algebra, Chapter 89: Torsion modules

This file records the definitions and theorem interfaces in the section on
modules supported on a closed subset.  The ideal-power torsion predicate and
the Serre subcategory are reused from Chapter 53; localization, derived
tensor products, and completion likewise use the canonical declarations
established earlier.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.MoreAlgebra.Unit53
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.Derived.Unit11
open scoped BigOperators TensorProduct

universe u w

namespace Formalization.Books.MoreAlgebra.Unit89

/-! ## I-power torsion modules -/

/-- The source's `M[I^n]`, represented by Mathlib's canonical torsion-by-set
submodule for the ideal `I^n`. -/
def idealPowerTorsionSubmodule {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (n : ℕ) : Submodule R M :=
  Submodule.torsionBySet R M (↑(I ^ n) : Set R)

/-- The union `M[I^∞]`, bundled as the supremum of the increasing family of
positive ideal-power torsion submodules. -/
def idealPowerTorsionSubmoduleInfinity {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) : Submodule R M :=
  ⨆ n : ℕ, idealPowerTorsionSubmodule I (n + 1)

theorem idealPowerTorsionSubmoduleInfinity_coe_eq_iUnion
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    (idealPowerTorsionSubmoduleInfinity (M := M) I : Set M) =
      ⋃ n : ℕ,
        (idealPowerTorsionSubmodule (M := M) I (n + 1) : Set M) := by
  sorry

@[simp]
theorem mem_idealPowerTorsionSubmodule_iff
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) (x : M) :
    x ∈ idealPowerTorsionSubmodule I n ↔
      ∀ a : R, a ∈ I ^ n → a • x = 0 := by
  simp [idealPowerTorsionSubmodule]

@[simp]
theorem mem_idealPowerTorsionSubmoduleInfinity_iff
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (x : M) :
    x ∈ idealPowerTorsionSubmoduleInfinity I ↔
      ∃ n : ℕ, 0 < n ∧ ∀ a : R, a ∈ I ^ n → a • x = 0 := by
  sorry

theorem isIPowerTorsion_iff_infinity_eq_top
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    IsIPowerTorsion I M ↔
      idealPowerTorsionSubmoduleInfinity (M := M) I = ⊤ := by
  sorry

theorem principal_isIPowerTorsion_iff
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (f : R) :
    IsIPowerTorsion (Ideal.span ({f} : Set R)) M ↔
      ∀ x : M, ∃ n : ℕ, 0 < n ∧ f ^ n • x = 0 := by
  sorry

/-- A resolution whose terms are direct sums of modules `R/I^n`. -/
structure IPowerTorsionResolution
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hM : IsIPowerTorsion I M) where
  K : ℕ → ModuleCat.{u} R
  quotientPresentation : ∀ i : ℕ, ∃ (ι : Type u) (n : ι → ℕ),
    (∀ j, 0 < n j) ∧
      Nonempty (K i ≅ ModuleCat.of R
        (DirectSum ι (fun j : ι => R ⧸ I ^ n j)))
  d : ∀ i : ℕ, K (i + 1) ⟶ K i
  augmentation : K 0 ⟶ ModuleCat.of R M
  d_squared : ∀ i : ℕ, d (i + 1) ≫ d i = 0
  exact_at_zero : Function.Exact (d 0).hom augmentation.hom
  augmentation_surjective : Function.Surjective augmentation.hom
  exact_at_positive : ∀ i : ℕ, Function.Exact (d (i + 1)).hom (d i).hom

theorem exists_iPowerTorsionResolution
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hM : IsIPowerTorsion I M) :
    Nonempty (IPowerTorsionResolution I hM) := by
  sorry

/-! ## The torsion-free quotient and local criterion -/

/-- The map to the product of localizations at a finite family of elements. -/
noncomputable def localizationCoverMap
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (t : ℕ) (f : Fin t → R) :
    M → ∀ i : Fin t, LocalizedModule (Submonoid.powers (f i)) M :=
  fun x i => LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M x

theorem idealPowerTorsion_torsionFree_criteria
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) :
    List.TFAE
      [idealPowerTorsionSubmodule (M := M) I 1 = ⊥,
       ∀ n : ℕ, 0 < n → idealPowerTorsionSubmodule (M := M) I n = ⊥,
       ∀ (t : ℕ) (f : Fin t → R),
         I = Ideal.span (Set.range f) →
           Function.Injective (localizationCoverMap (M := M) t f)] := by
  sorry

theorem quotient_by_iPowerTorsion_is_torsionFree
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) :
    (idealPowerTorsionSubmodule
        (M := M ⧸ idealPowerTorsionSubmoduleInfinity (M := M) I) I 1 =
      (⊥ : Submodule R
        (M ⧸ idealPowerTorsionSubmoduleInfinity (M := M) I))) := by
  sorry

theorem iPowerTorsion_extension
    {R M M' M'' : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']
    (I : Ideal R) (hI : I.FG)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f)
    (h_exact : Function.Exact (f : M' → M) (g : M → M''))
    (hg : Function.Surjective g)
    (hM' : IsIPowerTorsion I M') (hM'' : IsIPowerTorsion I M'') :
    IsIPowerTorsion I M := by
  sorry

theorem iPowerTorsion_modules_form_serre
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    (iPowerTorsionModuleProperty R I).IsSerreClass :=
  iPowerTorsionModuleProperty_isSerreClass R I hI

theorem iPowerTorsion_iff_support_subset_zeroLocus
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) :
    IsIPowerTorsion I M ↔
      Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  sorry

theorem iPowerTorsion_depends_only_on_zeroLocus
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Ideal R) (hI : I.FG) (hJ : J.FG)
    (hZ : PrimeSpectrum.zeroLocus (I : Set R) =
      PrimeSpectrum.zeroLocus (J : Set R)) :
    IsIPowerTorsion I M ↔ IsIPowerTorsion J M := by
  sorry

/-! ## Derived vanishing for torsion modules -/

abbrev DerivedModule (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  DerivedCategory (ModuleCat.{u} R)

noncomputable def derivedTensorWithModule
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedModule R) (N : ModuleCat.{u} R) : DerivedModule R :=
  derivedTensor K (moduleInDerived R N)

theorem boundedAbove_mod_ideal
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (K : DerivedModule R)
    (hK : ∀ i : ℤ, 0 < i →
      IsZero ((derivedCohomology R i).obj (derivedTensorWithModule K
        (ModuleCat.of R (R ⧸ I))))) :
    (∀ n : ℕ, 0 < n → ∀ i : ℤ, 0 < i →
      IsZero ((derivedCohomology R i).obj
        (derivedTensorWithModule K (ModuleCat.of R (R ⧸ I ^ n))))) ∧
    (∀ N : ModuleCat.{u} R, IsIPowerTorsion I (N : Type u) →
      ∀ i : ℤ, 0 < i →
        IsZero ((derivedCohomology R i).obj (derivedTensorWithModule K N))) ∧
    (∀ M : DerivedModule R,
      derivedBoundedProperty (ModuleCat.{u} R) M →
      (∀ i : ℤ, IsIPowerTorsion I
        ((derivedCohomology R i).obj M : Type u)) →
      (∀ i : ℤ, 0 < i →
        IsZero ((derivedCohomology R i).obj M)) →
      ∀ i : ℤ, 0 < i → IsZero ((derivedCohomology R i).obj
        (derivedTensor K M))) := by
  sorry

theorem derived_vanishing_mod_ideal
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (K : DerivedModule R)
    (hK : IsZero
      (derivedTensorWithModule K (ModuleCat.of R (R ⧸ I)))) :
    (∀ n : ℕ, 0 < n → IsZero
      (derivedTensorWithModule K (ModuleCat.of R (R ⧸ I ^ n)))) ∧
    (∀ N : ModuleCat.{u} R, IsIPowerTorsion I (N : Type u) →
      IsZero (derivedTensorWithModule K N)) ∧
    (∀ M : DerivedModule R,
      derivedBoundedProperty (ModuleCat.{u} R) M →
      (∀ i : ℤ, IsIPowerTorsion I
        ((derivedCohomology R i).obj M : Type u)) →
      IsZero (derivedTensor K M)) := by
  sorry

/-! ## Completion on I-power torsion modules -/

noncomputable def tensorUnitMap
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [Algebra R S] :
    M →ₗ[R] M ⊗[R] S :=
  (TensorProduct.mk R M S).flip 1

def quotientPowerMap
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (n : ℕ) :
    R ⧸ I ^ n →+* S ⧸ Ideal.map φ (I ^ n) :=
  Ideal.quotientMap (Ideal.map φ (I ^ n)) φ Ideal.le_comap_map

theorem torsion_module_completion
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M]
    (φ : R →+* S) (I : Ideal R)
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowerMap φ I n))
    (hM : IsIPowerTorsion I M) :
    letI : Algebra R S := φ.toAlgebra
    Function.Bijective
      (tensorUnitMap (R := R) (S := S) (M := M)) := by
  sorry

theorem torsion_module_adicCompletion
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) (hM : IsIPowerTorsion I M) :
    Function.Bijective
      (tensorUnitMap (R := R) (S := AdicCompletion I R) (M := M)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit89
