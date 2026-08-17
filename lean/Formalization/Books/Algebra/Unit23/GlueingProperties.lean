import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.Algebra.Module.LocalizedModule.Exact
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
  constructor
  · rintro rfl p
    simp
  · intro h
    exact Module.eq_zero_of_localization_maximal
      (fun P _ ↦ LocalizedModule P.primeCompl M)
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) x
      (fun P hP ↦ h ⟨P, hP.isPrime⟩)

/-- An element is zero exactly when all its maximal localizations are zero. -/
theorem element_eq_zero_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : M) :
    x = 0 ↔ ∀ m : MaximalSpectrum R, maximalLocalizationMap m x = 0 := by
  constructor
  · rintro rfl m
    simp
  · intro h
    exact Module.eq_zero_of_localization_maximal
      (fun P _ ↦ LocalizedModule P.primeCompl M)
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) x
      (fun P hP ↦ h ⟨P, hP⟩)

/-- The prime-localization and maximal-localization zero conditions agree. -/
theorem element_prime_localizations_zero_iff_maximal_localizations_zero
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (x : M) :
    (∀ p : PrimeSpectrum R, primeLocalizationMap p x = 0) ↔
      ∀ m : MaximalSpectrum R, maximalLocalizationMap m x = 0 := by
  constructor
  · intro h
    exact (element_eq_zero_iff_maximal_localizations x).mp
      ((element_eq_zero_iff_prime_localizations x).mpr h)
  · intro h
    exact (element_eq_zero_iff_prime_localizations x).mp
      ((element_eq_zero_iff_maximal_localizations x).mpr h)

/-- The map to the product of all maximal localizations is injective. -/
theorem maximalLocalizationProductMap_injective
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective (maximalLocalizationProductMap (R := R) M) := by
  intro x y h
  apply Module.eq_of_localization_maximal (R := R) (M := M)
    (fun P _ ↦ LocalizedModule P.primeCompl M)
    (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) x y
  intro P hP
  exact congrFun h ⟨P, hP⟩

/-- A module is zero exactly when all its prime localizations are zero modules. -/
theorem module_subsingleton_iff_prime_localizations
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Subsingleton M ↔
      ∀ p : PrimeSpectrum R, Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  constructor
  · intro h p
    letI := h
    infer_instance
  · intro h
    rw [subsingleton_iff_forall_eq 0]
    intro x
    apply (element_eq_zero_iff_prime_localizations (R := R) (M := M) x).mpr
    intro p
    letI := h p
    exact Subsingleton.elim _ _

/-- A module is zero exactly when all its maximal localizations are zero modules. -/
theorem module_subsingleton_iff_maximal_localizations
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Subsingleton M ↔
      ∀ m : MaximalSpectrum R, Subsingleton (LocalizedModule m.asIdeal.primeCompl M) := by
  constructor
  · intro h m
    letI := h
    infer_instance
  · intro h
    exact Module.subsingleton_of_localization_maximal
      (fun P _ ↦ LocalizedModule P.primeCompl M)
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M)
      (fun P hP ↦ h ⟨P, hP⟩)

/-- The prime-localization and maximal-localization zero-module conditions agree. -/
theorem module_prime_localizations_subsingleton_iff_maximal_localizations_subsingleton
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    (∀ p : PrimeSpectrum R, Subsingleton (LocalizedModule p.asIdeal.primeCompl M)) ↔
      ∀ m : MaximalSpectrum R,
        Subsingleton (LocalizedModule m.asIdeal.primeCompl M) := by
  constructor
  · intro h
    have hM : Subsingleton M :=
      (module_subsingleton_iff_prime_localizations M).mpr h
    exact (module_subsingleton_iff_maximal_localizations M).mp hM
  · intro h
    have hM : Subsingleton M :=
      (module_subsingleton_iff_maximal_localizations M).mpr h
    exact (module_subsingleton_iff_prime_localizations M).mp hM

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
  constructor
  · intro h p
    exact LocalizedModule.map_exact p.asIdeal.primeCompl f g h
  · intro h
    exact exact_of_localized_maximal f g
      (fun P hP ↦ h ⟨P, hP.isPrime⟩)

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
  constructor
  · intro h m
    exact LocalizedModule.map_exact m.asIdeal.primeCompl f g h
  · intro h
    exact exact_of_localized_maximal f g
      (fun P hP ↦ h ⟨P, hP⟩)

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
  constructor
  · intro h
    exact (exact_iff_maximal_localizations f g).mp
      ((exact_iff_prime_localizations f g).mpr h)
  · intro h
    exact (exact_iff_prime_localizations f g).mp
      ((exact_iff_maximal_localizations f g).mpr h)

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
  constructor
  · intro h p
    exact LocalizedModule.map_injective p.asIdeal.primeCompl f h
  · intro h
    exact injective_of_localized_maximal f
      (fun P hP ↦ h ⟨P, hP.isPrime⟩)

/-- Injectivity of a linear map can be checked at every maximal ideal. -/
theorem injective_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Injective f ↔
      ∀ m : MaximalSpectrum R,
        Function.Injective (LocalizedModule.map m.asIdeal.primeCompl f) := by
  constructor
  · intro h m
    exact LocalizedModule.map_injective m.asIdeal.primeCompl f h
  · intro h
    exact injective_of_localized_maximal f
      (fun P hP ↦ h ⟨P, hP⟩)

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
  constructor
  · intro h
    exact (injective_iff_maximal_localizations f).mp
      ((injective_iff_prime_localizations f).mpr h)
  · intro h
    exact (injective_iff_prime_localizations f).mp
      ((injective_iff_maximal_localizations f).mpr h)

/-- Surjectivity of a linear map can be checked at every prime. -/
theorem surjective_iff_prime_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Surjective f ↔
      ∀ p : PrimeSpectrum R,
        Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl f) := by
  constructor
  · intro h p
    exact LocalizedModule.map_surjective p.asIdeal.primeCompl f h
  · intro h
    exact surjective_of_localized_maximal f
      (fun P hP ↦ h ⟨P, hP.isPrime⟩)

/-- Surjectivity of a linear map can be checked at every maximal ideal. -/
theorem surjective_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Surjective f ↔
      ∀ m : MaximalSpectrum R,
        Function.Surjective (LocalizedModule.map m.asIdeal.primeCompl f) := by
  constructor
  · intro h m
    exact LocalizedModule.map_surjective m.asIdeal.primeCompl f h
  · intro h
    exact surjective_of_localized_maximal f
      (fun P hP ↦ h ⟨P, hP⟩)

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
  constructor
  · intro h
    exact (surjective_iff_maximal_localizations f).mp
      ((surjective_iff_prime_localizations f).mpr h)
  · intro h
    exact (surjective_iff_prime_localizations f).mp
      ((surjective_iff_maximal_localizations f).mpr h)

/-- Bijectivity of a linear map can be checked at every prime. -/
theorem bijective_iff_prime_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Bijective f ↔
      ∀ p : PrimeSpectrum R,
        Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f) := by
  constructor
  · intro h p
    exact ⟨LocalizedModule.map_injective p.asIdeal.primeCompl f h.1,
      LocalizedModule.map_surjective p.asIdeal.primeCompl f h.2⟩
  · intro h
    exact ⟨injective_of_localized_maximal f
      (fun P hP ↦ (h ⟨P, hP.isPrime⟩).1),
      surjective_of_localized_maximal f
        (fun P hP ↦ (h ⟨P, hP.isPrime⟩).2)⟩

/-- Bijectivity of a linear map can be checked at every maximal ideal. -/
theorem bijective_iff_maximal_localizations
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Bijective f ↔
      ∀ m : MaximalSpectrum R,
        Function.Bijective (LocalizedModule.map m.asIdeal.primeCompl f) := by
  constructor
  · intro h m
    exact ⟨LocalizedModule.map_injective m.asIdeal.primeCompl f h.1,
      LocalizedModule.map_surjective m.asIdeal.primeCompl f h.2⟩
  · intro h
    exact ⟨injective_of_localized_maximal f
      (fun P hP ↦ (h ⟨P, hP⟩).1),
      surjective_of_localized_maximal f
        (fun P hP ↦ (h ⟨P, hP⟩).2)⟩

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
  constructor
  · intro h
    exact (bijective_iff_maximal_localizations f).mp
      ((bijective_iff_prime_localizations f).mpr h)
  · intro h
    exact (bijective_iff_prime_localizations f).mp
      ((bijective_iff_maximal_localizations f).mpr h)

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
  rw [subsingleton_iff_forall_eq 0]
  intro x
  apply Module.eq_zero_of_isLocalized_span (s : Set R) hs
    (fun r : (s : Set R) => LocalizedModule.Away (r : R) M)
    (fun r => LocalizedModule.mkLinearMap (Submonoid.powers (r : R)) M) x
  intro r
  exact @Subsingleton.elim _ (h ⟨r.1, r.2⟩) _ _

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
  refine ⟨?_, ?_, ?_⟩
  · apply injective_of_localized_span (s := (s : Set R)) hs f
    intro r
    exact (h ⟨r.1, r.2⟩).1
  · apply exact_of_localized_span (s := (s : Set R)) hs f g
    intro r
    exact (h ⟨r.1, r.2⟩).2.1
  · apply surjective_of_localized_span (s := (s : Set R)) hs g
    intro r
    exact (h ⟨r.1, r.2⟩).2.2

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
  have hs' : Ideal.span ((algebraMap R S) '' (s : Set R)) = ⊤ := by
    rw [← Ideal.map_span, hs, Ideal.map_top]
  apply Algebra.FinitePresentation.of_span_eq_top_target
    ((algebraMap R S) '' (s : Set R)) hs'
  rintro _ ⟨r, hr, rfl⟩
  let A := Localization.Away r
  let L := Localization.Away (algebraMap R S r)
  let e := IsLocalization.Away.tensorRightEquiv S r A
  letI : Algebra A L := (Localization.awayMap (algebraMap R S) r).toAlgebra
  have hmap : algebraMap A (A ⊗[R] S) =
      ((e.symm : L →+* (A ⊗[R] S)).comp (algebraMap A L)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext
    simp [e, A, L, RingHom.algebraMap_toAlgebra, Localization.awayMap,
      IsLocalization.Away.map, Algebra.TensorProduct.tmul_one_eq_one_tmul,
      RingHom.algebraMap_toAlgebra]
  let eA : (A ⊗[R] S) ≃ₐ[A] L :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (by
      intro a
      apply e.symm.injective
      simpa [hmap])
  have hL : RingHom.FinitePresentation (algebraMap A L) := by
    rw [RingHom.finitePresentation_algebraMap]
    letI : Algebra.FinitePresentation A (A ⊗[R] S) := h ⟨r, hr⟩
    exact Algebra.FinitePresentation.equiv eA
  have hA : RingHom.FinitePresentation (algebraMap R A) := by
    rw [RingHom.finitePresentation_algebraMap]
    exact IsLocalization.Away.finitePresentation r
  have hc := RingHom.FinitePresentation.comp hL hA
  letI : IsScalarTower R A L :=
    IsScalarTower.of_algebraMap_eq'
      (IsLocalization.map_comp (Submonoid.powers r).le_comap_map).symm
  have haway :
      (Localization.awayMap (algebraMap R S) r).comp (algebraMap R A) =
        algebraMap R L := by
    change (algebraMap A L).comp (algebraMap R A) = algebraMap R L
    exact (IsScalarTower.algebraMap_eq R A L).symm
  rw [show algebraMap A L =
      Localization.awayMap (algebraMap R S) r by rfl] at hc
  rw [haway] at hc
  rw [RingHom.finitePresentation_algebraMap] at hc
  exact hc

/-! ## Finite covers in the target ring -/

/-- Finite type of a ring map descends from a finite standard-open cover of its target. -/
theorem target_cover_finiteType
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (t : Finset S) (ht : Ideal.span (t : Set S) = ⊤)
    (h : ∀ g : t,
      RingHom.FiniteType
        ((algebraMap S (Localization.Away (g : S))).comp f)) :
    RingHom.FiniteType f := by
  algebraize [f]
  replace h : ∀ g ∈ (t : Set S), Algebra.FiniteType R (Localization.Away g) := by
    intro g hg
    simp_rw [RingHom.FiniteType] at h
    convert! h ⟨g, hg⟩
    ext
    simp_rw [Algebra.smul_def]
    rfl
  exact Algebra.FiniteType.of_span_eq_top_target (t : Set S) ht h

/-- Finite presentation of a ring map descends from a finite standard-open cover of its target. -/
theorem target_cover_finitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (t : Finset S) (ht : Ideal.span (t : Set S) = ⊤)
    (h : ∀ g : t,
      RingHom.FinitePresentation
        ((algebraMap S (Localization.Away (g : S))).comp f)) :
    RingHom.FinitePresentation f := by
  algebraize [f]
  replace h : ∀ g ∈ (t : Set S), Algebra.FinitePresentation R (Localization.Away g) := by
    intro g hg
    simp_rw [RingHom.FinitePresentation] at h
    convert! h ⟨g, hg⟩
    ext
    simp_rw [Algebra.smul_def]
    rfl
  exact Algebra.FinitePresentation.of_span_eq_top_target (t : Set S) ht h

end

end Formalization.Books.Algebra.Unit23
