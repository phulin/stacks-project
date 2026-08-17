import Formalization.Books.Algebra.Unit17.Spectrum
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 118: Generic flatness

The source's localizations are represented by the canonical localization of the
target ring at the image of the base element and by `LocalizedModule.Away` for
the module.  The map from the localized base ring to the localized target is
the canonical `Localization.awayLift` map.
-/

namespace Formalization.Books.Algebra.Unit118

open Set

universe u v w

noncomputable section

/-! ## Localized pairs and the good condition -/

/-- The map `R_f → S_f` induced by a ring map `φ : R →+* S`.

The target localization is taken at `φ f`, so that a localized `S`-module is
canonically an `S_f`-module.  This is the source's notation `S_f` with its
canonical Mathlib model.
-/
noncomputable def localizedRingHom
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) :
    Localization.Away f →+* Localization.Away (φ f) := by
  exact Localization.awayLift
    ((algebraMap S (Localization.Away (φ f))).comp φ) f
    (by
      change IsUnit (algebraMap S (Localization.Away (φ f)) (φ f))
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ f)) (φ f))

/-- Freeness of the localized module over the localized base ring. -/
def LocalizedModuleFreeOverBase
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Type*) [AddCommGroup M] [Module S M]
    (f : R) : Prop :=
  let ψ := localizedRingHom φ f
  letI : Module (Localization.Away f)
      (LocalizedModule.Away (φ f) M) :=
    Module.compHom (LocalizedModule.Away (φ f) M) ψ
  Module.Free (Localization.Away f) (LocalizedModule.Away (φ f) M)

/-- Freeness of `S_f` as a module over `R_f`. -/
def LocalizedRingFreeOverBase
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) : Prop :=
  let ψ := localizedRingHom φ f
  letI : Algebra (Localization.Away f) (Localization.Away (φ f)) := ψ.toAlgebra
  Module.Free (Localization.Away f) (Localization.Away (φ f))

/-- The condition on `f` in the source's displayed good-locus equation.

The first two conjuncts are finite presentation of `S_f` over `R_f` and of
`M_f` over `S_f`; the last two are freeness of `S_f` and `M_f` over `R_f`.
-/
def GenericFlatnessCondition
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Type*) [AddCommGroup M] [Module S M]
    (f : R) : Prop :=
  let ψ := localizedRingHom φ f
  RingHom.FinitePresentation ψ ∧
    Module.FinitePresentation (Localization.Away (φ f))
      (LocalizedModule.Away (φ f) M) ∧
      LocalizedRingFreeOverBase φ f ∧
      LocalizedModuleFreeOverBase φ M f

/-- The source's good locus, as the union of the principal opens satisfying
`GenericFlatnessCondition`. -/
def genericFlatnessLocus
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Type*) [AddCommGroup M] [Module S M] :
    Set (PrimeSpectrum R) :=
  ⋃ f : {f : R // GenericFlatnessCondition φ M f},
    (PrimeSpectrum.basicOpen (f : R) : Set (PrimeSpectrum R))

/-- The good locus is open because it is a union of principal opens. -/
theorem isOpen_genericFlatnessLocus
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (φ : R →+* S) :
    IsOpen (genericFlatnessLocus φ M) := by
  exact isOpen_iUnion fun _ => PrimeSpectrum.isOpen_basicOpen

/-! ## Generic freeness -/

/-- Generic freeness over a Noetherian domain (the first version in the
source). -/
theorem genericFlatness_noetherian
    {R S M : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsDomain R] [AddCommGroup M] [Module S M]
    (φ : R →+* S) (hfiniteType : RingHom.FiniteType φ)
    (hM : Module.Finite S M) :
    ∃ f : R, f ≠ 0 ∧ LocalizedModuleFreeOverBase φ M f := by
  sorry

/-- Generic freeness for a finite-presentation algebra and module over a
domain (the second version in the source). -/
theorem genericFlatness_finitelyPresented
    {R S M : Type*} [CommRing R] [CommRing S] [IsDomain R]
    [AddCommGroup M] [Module S M]
    (φ : R →+* S) (hfinitePresentation : RingHom.FinitePresentation φ)
    (hM : Module.FinitePresentation S M) :
    ∃ f : R, f ≠ 0 ∧ LocalizedModuleFreeOverBase φ M f := by
  sorry

/-- Generic freeness together with finite-presentation after localization.

This is the strongest of the three generic-flatness statements in the
source. -/
theorem genericFlatness
    {R S M : Type*} [CommRing R] [CommRing S] [IsDomain R]
    [AddCommGroup M] [Module S M]
    (φ : R →+* S) (hfiniteType : RingHom.FiniteType φ)
    (hM : Module.Finite S M) :
    ∃ f : R, f ≠ 0 ∧ GenericFlatnessCondition φ M f := by
  sorry

/-! ## Properties of the good locus -/

/-- The good locus is stable under extensions, represented by an exact pair of
`S`-linear maps with injective first map and surjective second map. -/
theorem genericFlatnessLocus_extension
    {R S M₁ M₂ M₃ : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module S M₁] [Module S M₂] [Module S M₃]
    (φ : R →+* S) (f : M₁ →ₗ[S] M₂) (g : M₂ →ₗ[S] M₃)
    (hinjective : Function.Injective f)
    (hexact : Function.Exact f g)
    (hsurjective : Function.Surjective g) :
    genericFlatnessLocus φ M₁ ∩ genericFlatnessLocus φ M₃ ⊆
      genericFlatnessLocus φ M₂ := by
  sorry

/-- Localization of the good locus, expressed through the canonical
homeomorphism `Spec(R_f) ≃ D(f)`. -/
theorem genericFlatnessLocus_localize
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (φ : R →+* S) (f : R) :
    genericFlatnessLocus (localizedRingHom φ f)
        (LocalizedModule.Away (φ f) M) =
      (Formalization.Books.Algebra.Unit17.standardOpenSpectrumHomeomorph f) ⁻¹'
        (Subtype.val ⁻¹'
          ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩
            genericFlatnessLocus φ M)) := by
  sorry

/-- Density of the good locus can be checked on a dense open covered by
principal opens.  The local density hypotheses are read in the canonical
`Spec(R_f) ≃ D(f)` subspaces. -/
theorem genericFlatnessLocus_reduce
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (φ : R →+* S) (V : Set (PrimeSpectrum R))
    (hVopen : IsOpen V) (hVdense : Dense V)
    {ι : Type u} (f : ι → R)
    (hcover : V = ⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R)))
    (hlocal : ∀ i,
      Dense
        ((Formalization.Books.Algebra.Unit17.standardOpenSpectrumHomeomorph (f i)) ''
          genericFlatnessLocus (localizedRingHom φ (f i))
            (LocalizedModule.Away (φ (f i)) M))) :
    Dense (genericFlatnessLocus φ M) := by
  sorry

/-! ## The reduced-base theorem -/

/-- Over a reduced base, the good locus contains a dense open, with a basic
good neighborhood at every point of that open. -/
theorem exists_denseOpen_subset_genericFlatnessLocus
    {R S M : Type*} [CommRing R] [CommRing S] [IsReduced R] [AddCommGroup M]
    [Module S M]
    (φ : R →+* S) (hfiniteType : RingHom.FiniteType φ)
    (hM : Module.Finite S M) :
    ∃ V : Set (PrimeSpectrum R),
      IsOpen V ∧ Dense V ∧
        ∀ u ∈ V, ∃ f : R,
          u ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∧
            (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ V ∧
              GenericFlatnessCondition φ M f := by
  sorry

/- The filtrations, polynomial presentations, fraction-field reductions, and
displayed short exact sequences occurring inside the textbook proofs are proof
scaffolding rather than additional chapter-level assertions.  The reusable
short-exact-sequence content is represented by the explicit `Function.Exact`,
injectivity, and surjectivity hypotheses of `genericFlatnessLocus_extension`.
-/

end

end Formalization.Books.Algebra.Unit118
