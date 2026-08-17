import Formalization.Books.Algebra.Unit137.SmoothRingMaps
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Commutative Algebra, Chapter 141: Smooth ring maps in the Noetherian case

This chapter records the small-extension lifting test for smoothness at a
prime.  Local algebra diagrams are expressed with Mathlib's canonical
`AlgHom`s, and residue fields use `Ideal.ResidueField`.
-/

namespace Formalization.Books.Algebra.Unit141

noncomputable section

universe u v

/-! ## Small extensions -/

/-- A small extension is a surjection of local Artinian rings whose kernel
has module length one over the source. -/
def IsSmallExtension
    {B' B : Type*} [CommRing B'] [CommRing B]
    (φ : B' →+* B) : Prop :=
  IsLocalRing B' ∧ IsArtinianRing B' ∧
    IsLocalRing B ∧ IsArtinianRing B ∧
      Function.Surjective φ ∧
        Module.length B' (RingHom.ker φ) = 1

/-- The kernel of a small extension is square-zero. -/
theorem smallExtension_kernel_square_zero
    {B' B : Type*} [CommRing B'] [CommRing B]
    (φ : B' →+* B) (hφ : IsSmallExtension φ) :
    (RingHom.ker φ) ^ 2 = ⊥ := by
  sorry

/-- The kernel of a small extension is principal and is annihilated by the
maximal ideal of the source. -/
theorem smallExtension_kernel_principal
    {B' B : Type*} [CommRing B'] [CommRing B] [IsLocalRing B']
    (φ : B' →+* B) (hφ : IsSmallExtension φ) :
    ∃ x : B',
      RingHom.ker φ = Ideal.span ({x} : Set B') ∧
        ∀ y : B', y ∈ IsLocalRing.maximalIdeal B' → y * x = 0 := by
  sorry

/-! ## Lifting conditions -/

/-- The square-zero lifting condition at a prime, with all solid diagrams
encoded by `R`-algebra homomorphisms. -/
def squareZeroLiftingAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∀ {B' B : Type*} [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B]
    [IsLocalRing B'] [IsLocalRing B]
    (e : B' →ₐ[R] B),
    Function.Surjective e →
      (RingHom.ker e.toRingHom) ^ 2 = ⊥ →
        ∀ (g : S →ₐ[R] B),
          q.asIdeal = (IsLocalRing.maximalIdeal B).comap g.toRingHom →
            ∃ lift : S →ₐ[R] B', e.comp lift = g

/-- The lifting condition restricted to small extensions. -/
def smallExtensionLiftingAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∀ {B' B : Type*} [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B]
    [IsLocalRing B'] [IsLocalRing B]
    (e : B' →ₐ[R] B),
    IsSmallExtension e.toRingHom →
      ∀ (g : S →ₐ[R] B),
        q.asIdeal = (IsLocalRing.maximalIdeal B).comap g.toRingHom →
          ∃ lift : S →ₐ[R] B', e.comp lift = g

/-- The canonical map on residue fields induced by a map to a local ring is
bijective precisely when the map induces an isomorphism of residue fields. -/
def residueFieldMapIsBijective
    {S B : Type*} [CommRing S] [CommRing B] [IsLocalRing B]
    (q : PrimeSpectrum S) (g : S →+* B)
    (hq : q.asIdeal = (IsLocalRing.maximalIdeal B).comap g) : Prop :=
  Function.Bijective
    (Ideal.ResidueField.map q.asIdeal (IsLocalRing.maximalIdeal B) g hq)

/-- The small-extension lifting condition with the additional residue-field
isomorphism required in the final condition of the source lemma. -/
def smallExtensionResidueFieldLiftingAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∀ {B' B : Type*} [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B]
    [IsLocalRing B'] [IsLocalRing B]
    (e : B' →ₐ[R] B),
    IsSmallExtension e.toRingHom →
      ∀ (g : S →ₐ[R] B),
        (hq : q.asIdeal = (IsLocalRing.maximalIdeal B).comap g.toRingHom) →
          residueFieldMapIsBijective q g.toRingHom hq →
            ∃ lift : S →ₐ[R] B', e.comp lift = g

/-! ## The Noetherian smoothness test -/

/-- For a finite-type map from a Noetherian ring, smoothness at a prime is
equivalent to the square-zero, small-extension, and residue-field-restricted
lifting conditions. -/
theorem smooth_test_artinian
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hpq : p.asIdeal = q.asIdeal.comap f)
    [IsNoetherianRing R] (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    List.TFAE
      [ Formalization.Books.Algebra.Unit137.IsSmoothAt R S q,
        squareZeroLiftingAt R S q,
        smallExtensionLiftingAt R S q,
        smallExtensionResidueFieldLiftingAt R S q ] := by
  sorry

end

end Formalization.Books.Algebra.Unit141
