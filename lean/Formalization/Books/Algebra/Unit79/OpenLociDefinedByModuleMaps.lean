import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 79: Open loci defined by module maps

The source's localizations and fibers are represented by Mathlib's canonical
`LocalizedModule`, `Localization`, and tensor-product constructions.  The
finite-projective conclusions reuse Chapter 78's source-facing predicate,
which is the canonical conjunction of `Module.Finite` and `Module.Projective`.
-/

namespace Formalization.Books.Algebra.Unit79

open Set

universe u v

noncomputable section

/-! ## Canonical maps and loci -/

/- The map on stalks is Mathlib's localization of a linear map. -/

/-- The localization at a prime of a map of modules. -/
noncomputable def localizedMapAtPrime
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    LocalizedModule p.asIdeal.primeCompl M →ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl N :=
  LocalizedModule.map p.asIdeal.primeCompl φ

/- The source writes the fiber as `M ⊗ κ(p)`.  We use Mathlib's canonical
   `Ideal.Fiber`, which fixes the equivalent normalization `κ(p) ⊗ M`; the
   map is the canonical `LinearMap.baseChange` and is linear over the residue
   field. -/

/-- The map on fibers over the residue field at a prime. -/
def fiberMapAtPrime
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    p.asIdeal.Fiber M →ₗ[p.asIdeal.ResidueField] p.asIdeal.Fiber N :=
  LinearMap.baseChange p.asIdeal.ResidueField φ

/-- The locus where the localization of a module map at a prime is surjective. -/
def localizedSurjectiveLocus
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Surjective (localizedMapAtPrime φ p)}

/-- The locus where the fiber map of a module map is surjective. -/
def fiberSurjectiveLocus
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Surjective (fiberMapAtPrime φ p)}

/-- The locus where the localization of a module map is bijective. -/
def localizedIsomorphismLocus
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Bijective (localizedMapAtPrime φ p)}

/-- The locus where the fiber map of a module map is injective. -/
def fiberInjectiveLocus
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Injective (fiberMapAtPrime φ p)}

/-- The locus where the fiber map of a module map is bijective. -/
def fiberIsomorphismLocus
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Bijective (fiberMapAtPrime φ p)}

/- The source's identity `V = U ∩ W` is immediate from
   `Function.Bijective`, so it is accounted for by this definition rather
   than duplicated as a separate theorem. -/

/- The map away from an element is the same canonical localized map with the
   powers submonoid. -/

/-- The localization away from an element of a map of modules. -/
noncomputable def localizedMapAway
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (f : R) :
    LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f N :=
  LocalizedModule.map (Submonoid.powers f) φ

/-! ## A finite target: surjectivity -/

/--
If the target of a module map is finite, its surjectivity locus can be read
on fibers, is open, and localizes to a surjection on every basic open it
contains.
-/
theorem map_between_finite
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] (φ : M →ₗ[R] N) :
    localizedSurjectiveLocus φ = fiberSurjectiveLocus φ ∧
      IsOpen (localizedSurjectiveLocus φ) ∧
        ∀ f : R,
          (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
              localizedSurjectiveLocus φ →
            Function.Surjective (localizedMapAway φ f) := by
  sorry

/-! ## A finite source and finitely presented target: isomorphisms -/

/--
If the source is finite and the target is finitely presented, the locus where
a module map is an isomorphism after localization at a prime is open.
-/
theorem map_between_finitely_presented
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.FinitePresentation R N]
    (φ : M →ₗ[R] N) :
    IsOpen (localizedIsomorphismLocus φ) := by
  sorry

/-! ## Finite presentation and local freeness -/

/--
A finitely presented module which is free at a prime is free after localizing
away from an element outside that prime.
-/
theorem finitely_presented_localization_free
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (p : PrimeSpectrum R)
    (hM : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M)) :
    ∃ f : R, f ∉ p.asIdeal ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  sorry

/-! ## Finite projective maps -/

/- The source-facing finite-projective predicate from Chapter 78 is reused for
   the kernel and cokernel conclusions. -/

/--
For a map between finite projective modules, the injective, surjective, and
bijective fiber loci are open.  On any basic open contained in one of these
loci, the corresponding localized map has the asserted property, and the
associated kernel or cokernel is finite projective.
-/
theorem cokernel_flat
    {R P₁ P₂ : Type*} [CommRing R]
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
    [Module.Finite R P₁] [Module.Projective R P₁]
    [Module.Finite R P₂] [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) :
    IsOpen (fiberInjectiveLocus φ) ∧
      (∀ f : R,
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
            fiberInjectiveLocus φ →
          Function.Injective (localizedMapAway φ f) ∧
            Formalization.Books.Algebra.Unit78.FiniteProjective
              (Localization.Away f)
              (LocalizedModule.Away f (P₂ ⧸ LinearMap.range φ))) ∧
      IsOpen (fiberSurjectiveLocus φ) ∧
        (∀ f : R,
          (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
              fiberSurjectiveLocus φ →
            Function.Surjective (localizedMapAway φ f) ∧
              Formalization.Books.Algebra.Unit78.FiniteProjective
                (Localization.Away f)
                (LocalizedModule.Away f (LinearMap.ker φ))) ∧
        IsOpen (fiberIsomorphismLocus φ) ∧
          ∀ f : R,
            (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
                fiberIsomorphismLocus φ →
              Function.Bijective (localizedMapAway φ f) := by
  sorry

end

end Formalization.Books.Algebra.Unit79
