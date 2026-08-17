import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit54.EssentiallyFiniteType
import Formalization.Books.Algebra.Unit56.GradedRings
import Formalization.Books.Algebra.Unit66.WeaklyAssociatedPrimes
import Formalization.Books.MoreAlgebra.Unit22.TorsionFree
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

namespace Formalization.Books.MoreAlgebra.Unit26

open scoped TensorProduct

universe u v

noncomputable section

/-- The source's finite family of prime localizations detecting elements of a
    ring.  The family is indexed by `Fin n`, so its codomain is the finite
    dependent product of the corresponding localizations. -/
def HasFinitePrimeLocalizationCover (R : Type u) [CommRing R] : Prop :=
  ∃ (n : ℕ) (p : Fin n → PrimeSpectrum R),
    Function.Injective
      (RingHom.pi (fun i => algebraMap R (Localization.AtPrime (p i).asIdeal)))

/-- Finite presentation of the canonical base-change module over the
    base-changed algebra.  This packages the local module notation `M_p`
    using the established `Unit14.baseChangeModule` construction. -/
def BaseChangeModuleFinitePresentation
    {R S R' M : Type*} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (g : R →+* R') : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  Module.FinitePresentation (S ⊗[R] R')
    (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g)

/-- The local finite-presentation condition for the base-changed algebra
    `S_p` over `R_p`. -/
def IsPrimeLocallyFinitelyPresented
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) : Prop :=
  RingHom.FinitePresentation
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap
      (algebraMap R S) (algebraMap R (Localization.AtPrime p.asIdeal)))

/-- The local finite-presentation condition for `M_p` over `S_p`. -/
def IsPrimeLocallyFinitelyPresentedModule
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] (p : PrimeSpectrum R) : Prop :=
  BaseChangeModuleFinitePresentation (M := M) (algebraMap R S)
    (algebraMap R (Localization.AtPrime p.asIdeal))

/-- Flatness, finite generation, and prime-local finite presentation imply
    finite presentation for a module over a polynomial algebra. -/
theorem flat_finiteType_finitePresentation_local_module
    {R M : Type*} [CommRing R] (n : ℕ)
    [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module.Finite (MvPolynomial (Fin n) R) M]
    (hflat : letI : Module R M :=
      Module.compHom M (algebraMap R (MvPolynomial (Fin n) R));
      Module.Flat R M)
    (hlocal : ∀ p : PrimeSpectrum R,
      IsPrimeLocallyFinitelyPresentedModule
        (R := R) (S := MvPolynomial (Fin n) R) (M := M) p) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  sorry

/-- The ring-map version of the preceding local finite-presentation result. -/
theorem flat_finiteType_finitePresentation_local
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.Flat R S]
    (hcover : HasFinitePrimeLocalizationCover R)
    (hlocal : ∀ p : PrimeSpectrum R,
      IsPrimeLocallyFinitelyPresented (R := R) (S := S) p) :
    Algebra.FinitePresentation R S := by
  sorry

/-- A finite flat graded module over a positively graded polynomial algebra
    over a local ring is finitely presented. -/
theorem flat_gradedPolynomial_finitePresentation_module
    {R M : Type*} [CommRing R] (n : ℕ)
    [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    (𝒜 : ℕ → Submodule R (MvPolynomial (Fin n) R))
    (𝓜 : ℤ → Submodule (MvPolynomial (Fin n) R) M)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (hX : ∀ i, MvPolynomial.X i ∈ 𝒜 (w i))
    [GradedAlgebra 𝒜] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝒜 𝓜]
    [IsLocalRing R] [Module.Finite (MvPolynomial (Fin n) R) M]
    (hflat : letI : Module R M :=
      Module.compHom M (algebraMap R (MvPolynomial (Fin n) R));
      Module.Flat R M) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  sorry

/-- The two graded finite-type finite-presentation conclusions from the
    source, for the algebra and for a finite flat graded module. -/
theorem flat_graded_finiteType_finitePresentation
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M]
    (𝒜 : ℕ → Submodule R S) (𝓜 : ℤ → Submodule S M)
    [GradedAlgebra 𝒜] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝒜 𝓜] [Algebra.FiniteType R S]
    [Module.Finite R (𝒜 0)]
    (hcover : HasFinitePrimeLocalizationCover R) :
    (Module.Flat R S → Algebra.FinitePresentation R S) ∧
      (letI : Module R M := Module.compHom M (algebraMap R S)
       Module.Flat R M → Module.Finite S M →
         Module.FinitePresentation S M) := by
  sorry

/- The source's presentation `0 → K → S^r → M → 0`, its localization
   diagram, and the componentwise exact sequences in the graded proof are
   proof scaffolding for the preceding interfaces; no additional theorem is
   needed for those chosen presentations.  The same applies to the finite
   polynomial presentation and homogenization steps in the later valuation
   ring proofs. -/

/-- A local ring has a finite prime-localization cover. -/
theorem hasFinitePrimeLocalizationCover_of_local
    {R : Type u} [CommRing R] [IsLocalRing R] :
    HasFinitePrimeLocalizationCover R := by
  sorry

/-- A Noetherian ring has a finite prime-localization cover. -/
theorem hasFinitePrimeLocalizationCover_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    HasFinitePrimeLocalizationCover R := by
  sorry

/-- A domain has a finite prime-localization cover. -/
theorem hasFinitePrimeLocalizationCover_of_domain
    {R : Type u} [CommRing R] [IsDomain R] :
    HasFinitePrimeLocalizationCover R := by
  sorry

/-- A reduced ring with finitely many minimal primes has a finite
    prime-localization cover. -/
theorem hasFinitePrimeLocalizationCover_of_reduced
    {R : Type u} [CommRing R] [IsReduced R]
    (hminimal : (minimalPrimes R).Finite) :
    HasFinitePrimeLocalizationCover R := by
  sorry

/-- Finitely many weakly associated primes give a finite
    prime-localization cover. -/
theorem hasFinitePrimeLocalizationCover_of_finite_weaklyAssociatedPrimes
    {R : Type u} [CommRing R]
    (hfinite :
      (Formalization.Books.Algebra.Unit66.weaklyAssociatedPrimes R R).Finite) :
    HasFinitePrimeLocalizationCover R := by
  sorry

/-- Nagata's valuation-ring finite-presentation theorem, with its algebra and
    module conclusions recorded together. -/
theorem valuationRing_flat_finitePresentation
    {A B M : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    [Algebra.FiniteType A B] :
    (Module.Flat A B → Algebra.FinitePresentation A B) ∧
      (letI : Module A M := Module.compHom M (algebraMap A B)
       Module.Flat A M → Module.FinitePresentation B M) := by
  sorry

/-- The local essentially-finite-type valuation-ring refinement. -/
theorem valuationRing_local_essFiniteType_finitePresentation
    {A B M : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hess : RingHom.EssFiniteType (algebraMap A B)) :
    (Module.Flat A B →
        Formalization.Books.Algebra.Unit54.RingHom.EssFinitePresentation
          (algebraMap A B)) ∧
      (letI : Module A M := Module.compHom M (algebraMap A B)
       Module.Flat A M → Module.FinitePresentation B M) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit26
