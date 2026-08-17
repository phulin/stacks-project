import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Commutative Algebra, Chapter 23: Glueing properties

The source's localizations are represented by Mathlib's canonical
`LocalizedModule` constructions.  A finite standard-open cover is represented
by a finite set whose ideal span is `⊤`; Mathlib identifies this condition
with the corresponding cover of `PrimeSpectrum` by basic opens.
-/

namespace Formalization.Books.Algebra.Unit23

universe u v w

noncomputable section

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ## Localizations at primes and maximal ideals -/

/-- The canonical map from a module to its localization at a prime. -/
def primeLocalizationMap {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) :
    M →ₗ[R] LocalizedModule p.asIdeal.primeCompl M :=
  LocalizedModule.mkLinearMap p.asIdeal.primeCompl M

/-- The canonical map from a module to its localization at a maximal ideal. -/
def maximalLocalizationMap {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (m : MaximalSpectrum R) :
    M →ₗ[R] LocalizedModule m.asIdeal.primeCompl M :=
  LocalizedModule.mkLinearMap m.asIdeal.primeCompl M

/-- The map from a module to the product of its localizations at maximal ideals. -/
def maximalLocalizationProductMap {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
  M →ₗ[R] (∀ m : MaximalSpectrum R,
      LocalizedModule m.asIdeal.primeCompl M) :=
  LinearMap.pi fun m => maximalLocalizationMap (R := R) (M := M) m

/-! ## Characterizing zero objects and local properties -/

/-- An element is zero exactly when all its prime localizations are zero. -/
theorem element_eq_zero_iff_prime_localizations
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : M) :
    x = 0 ↔ ∀ p : PrimeSpectrum R, primeLocalizationMap p x = 0 := by
  sorry

/-- An element is zero exactly when all its maximal localizations are zero. -/
theorem element_eq_zero_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : M) :
    x = 0 ↔ ∀ m : MaximalSpectrum R, maximalLocalizationMap m x = 0 := by
  sorry

/-- The prime-localization and maximal-localization zero conditions agree. -/
theorem element_prime_localizations_zero_iff_maximal_localizations_zero
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : M) :
    (∀ p : PrimeSpectrum R, primeLocalizationMap p x = 0) ↔
      ∀ m : MaximalSpectrum R, maximalLocalizationMap m x = 0 := by
  sorry

/-- The map to the product of all maximal localizations is injective. -/
theorem maximalLocalizationProductMap_injective
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective (maximalLocalizationProductMap (R := R) M) := by
  sorry

/-- A module is zero exactly when all its prime localizations are zero modules. -/
theorem module_subsingleton_iff_prime_localizations
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Subsingleton M ↔
      ∀ p : PrimeSpectrum R, Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  sorry

/-- A module is zero exactly when all its maximal localizations are zero modules. -/
theorem module_subsingleton_iff_maximal_localizations
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Subsingleton M ↔
      ∀ m : MaximalSpectrum R, Subsingleton (LocalizedModule m.asIdeal.primeCompl M) := by
  sorry

/-- The prime-localization and maximal-localization zero-module conditions agree. -/
theorem module_prime_localizations_subsingleton_iff_maximal_localizations_subsingleton
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    (∀ p : PrimeSpectrum R, Subsingleton (LocalizedModule p.asIdeal.primeCompl M)) ↔
      ∀ m : MaximalSpectrum R,
        Subsingleton (LocalizedModule m.asIdeal.primeCompl M) := by
  sorry

/-! ### Exact complexes -/

/-- Exactness of a complex of modules can be checked at every prime. -/
theorem exact_iff_prime_localizations
    {R : Type u} [CommRing R]
    {M₁ : Type v} {M₂ : Type w} {M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    Function.Exact f g ↔
      ∀ p : PrimeSpectrum R,
        Function.Exact (LocalizedModule.map p.asIdeal.primeCompl f)
          (LocalizedModule.map p.asIdeal.primeCompl g) := by
  sorry

/-- Exactness of a complex of modules can be checked at every maximal ideal. -/
theorem exact_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M₁ : Type v} {M₂ : Type w} {M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    Function.Exact f g ↔
      ∀ m : MaximalSpectrum R,
        Function.Exact (LocalizedModule.map m.asIdeal.primeCompl f)
          (LocalizedModule.map m.asIdeal.primeCompl g) := by
  sorry

/-- Prime and maximal localizations give equivalent exactness conditions. -/
theorem exact_prime_localizations_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M₁ : Type v} {M₂ : Type w} {M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    (∀ p : PrimeSpectrum R,
      Function.Exact (LocalizedModule.map p.asIdeal.primeCompl f)
        (LocalizedModule.map p.asIdeal.primeCompl g)) ↔
      ∀ m : MaximalSpectrum R,
        Function.Exact (LocalizedModule.map m.asIdeal.primeCompl f)
          (LocalizedModule.map m.asIdeal.primeCompl g) := by
  sorry

/-! ### Injective, surjective, and bijective maps -/

/-- Injectivity of a linear map can be checked at every prime. -/
theorem injective_iff_prime_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Injective f ↔
      ∀ p : PrimeSpectrum R,
        Function.Injective (LocalizedModule.map p.asIdeal.primeCompl f) := by
  sorry

/-- Injectivity of a linear map can be checked at every maximal ideal. -/
theorem injective_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Injective f ↔
      ∀ m : MaximalSpectrum R,
        Function.Injective (LocalizedModule.map m.asIdeal.primeCompl f) := by
  sorry

/-- Prime and maximal localizations give equivalent injectivity conditions. -/
theorem injective_prime_localizations_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (∀ p : PrimeSpectrum R,
      Function.Injective (LocalizedModule.map p.asIdeal.primeCompl f)) ↔
      ∀ m : MaximalSpectrum R,
        Function.Injective (LocalizedModule.map m.asIdeal.primeCompl f) := by
  sorry

/-- Surjectivity of a linear map can be checked at every prime. -/
theorem surjective_iff_prime_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Surjective f ↔
      ∀ p : PrimeSpectrum R,
        Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl f) := by
  sorry

/-- Surjectivity of a linear map can be checked at every maximal ideal. -/
theorem surjective_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Surjective f ↔
      ∀ m : MaximalSpectrum R,
        Function.Surjective (LocalizedModule.map m.asIdeal.primeCompl f) := by
  sorry

/-- Prime and maximal localizations give equivalent surjectivity conditions. -/
theorem surjective_prime_localizations_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (∀ p : PrimeSpectrum R,
      Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl f)) ↔
      ∀ m : MaximalSpectrum R,
        Function.Surjective (LocalizedModule.map m.asIdeal.primeCompl f) := by
  sorry

/-- Bijectivity of a linear map can be checked at every prime. -/
theorem bijective_iff_prime_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Bijective f ↔
      ∀ p : PrimeSpectrum R,
        Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f) := by
  sorry

/-- Bijectivity of a linear map can be checked at every maximal ideal. -/
theorem bijective_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Bijective f ↔
      ∀ m : MaximalSpectrum R,
        Function.Bijective (LocalizedModule.map m.asIdeal.primeCompl f) := by
  sorry

/-- Prime and maximal localizations give equivalent bijectivity conditions. -/
theorem bijective_prime_localizations_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (∀ p : PrimeSpectrum R,
      Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f)) ↔
      ∀ m : MaximalSpectrum R,
        Function.Bijective (LocalizedModule.map m.asIdeal.primeCompl f) := by
  sorry

/-! ## Finite standard-open covers -/

/-
The source writes the cover as `⋃ D(fᵢ) = Spec(R)`, equivalently
`(fᵢ) = R`.  In these declarations the latter is represented by
`Ideal.span (s : Set R) = ⊤`; Mathlib's
`PrimeSpectrum.iSup_basicOpen_eq_top_iff'` is the canonical equivalence with
the former formulation.
-/

/-- A module that vanishes on a finite standard-open cover is zero. -/
theorem standard_cover_subsingleton
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, Subsingleton (LocalizedModule.Away (f : R) M)) :
    Subsingleton M := by
  sorry

/-- Finiteness of a module descends from a finite standard-open cover. -/
theorem standard_cover_finite_module
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s,
      Module.Finite (Localization.Away (f : R))
        (LocalizedModule.Away (f : R) M)) :
    Module.Finite R M := by
  exact Module.Finite.of_localizationSpan_finite s hs h

/-- Finite presentation of a module descends from a finite standard-open cover. -/
theorem standard_cover_finitePresentation_module
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s,
      Module.FinitePresentation (Localization.Away (f : R))
        (LocalizedModule.Away (f : R) M)) :
    Module.FinitePresentation R M := by
  apply Module.FinitePresentation.of_localizationSpan (s := (s : Set R)) hs
  intro f
  exact h ⟨f.1, f.2⟩

/-- A linear map that is an isomorphism on a finite standard-open cover is an isomorphism. -/
theorem standard_cover_bijective_linearMap
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ r : s,
      Function.Bijective (LocalizedModule.map (Submonoid.powers (r : R)) f)) :
    Function.Bijective f := by
  apply bijective_of_localized_span (s := (s : Set R)) hs f
  intro r
  exact h ⟨r.1, r.2⟩

/-- A short exact sequence that is exact on a finite standard-open cover is exact. -/
theorem standard_cover_short_exact
    {R : Type u} [CommRing R]
    {M₀ : Type v} {M₁ : Type w} {M₂ : Type*}
    [AddCommGroup M₀] [Module R M₀]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ r : s,
      Function.Injective (LocalizedModule.map (Submonoid.powers (r : R)) f) ∧
        Function.Exact
          (LocalizedModule.map (Submonoid.powers (r : R)) f)
          (LocalizedModule.map (Submonoid.powers (r : R)) g) ∧
        Function.Surjective (LocalizedModule.map (Submonoid.powers (r : R)) g)) :
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g := by
  sorry

/-- Noetherianity of a ring descends from a finite standard-open cover. -/
theorem standard_cover_noetherian
    {R : Type u} [CommRing R]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, IsNoetherianRing (Localization.Away (f : R))) :
    IsNoetherianRing R := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  apply Ideal.fg_of_localizationSpan (s : Set R) hs
  intro f
  exact (h ⟨f.1, f.2⟩).noetherian _

/-- Finite type of an algebra descends from a finite standard-open cover of its source. -/
theorem standard_cover_finiteType_algebra
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s,
      Algebra.FiniteType (Localization.Away (f : R))
        (Localization.Away (f : R) ⊗[R] S)) :
    Algebra.FiniteType R S := by
  apply Algebra.FiniteType.of_span_eq_top_source (s : Set R) hs
  intro f hf
  exact h ⟨f, hf⟩

/-- Finite presentation of an algebra descends from a finite standard-open cover of its source. -/
theorem standard_cover_finitePresentation_algebra
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s,
      Algebra.FinitePresentation (Localization.Away (f : R))
        (Localization.Away (f : R) ⊗[R] S)) :
    Algebra.FinitePresentation R S := by
  sorry

/-! ## Finite covers in the target ring -/

/-- Finite type of a ring map descends from a finite standard-open cover of its target. -/
theorem target_cover_finiteType
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (t : Finset S) (ht : Ideal.span (t : Set S) = ⊤)
    (h : ∀ g : t,
      RingHom.FiniteType
        ((algebraMap S (Localization.Away (g : S))).comp f)) :
    RingHom.FiniteType f := by
  sorry

/-- Finite presentation of a ring map descends from a finite standard-open cover of its target. -/
theorem target_cover_finitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (t : Finset S) (ht : Ideal.span (t : Set S) = ⊤)
    (h : ∀ g : t,
      RingHom.FinitePresentation
        ((algebraMap S (Localization.Away (g : S))).comp f)) :
    RingHom.FinitePresentation f := by
  sorry

end

end Formalization.Books.Algebra.Unit23
