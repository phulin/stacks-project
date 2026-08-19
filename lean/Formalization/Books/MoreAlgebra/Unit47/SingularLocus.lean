import Formalization.Books.Algebra.Unit113.DimensionFormula
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# More Algebra, Chapter 47: The singular locus

This file records the definitions and theorem interfaces in the section on
regular and singular loci.  The regular locus is the set of primes whose
localization is a regular local ring.  The J-conditions are kept as explicit
propositions (including the Noetherian hypothesis from the source), while
relative openness is expressed by taking an ambient open and intersecting it
with the closed subspace under consideration.
-/

namespace Formalization.Books.MoreAlgebra.Unit47

universe u

noncomputable section

/-! ## Regular and singular loci -/

/-- The regular locus of the affine scheme associated to a commutative ring. -/
def regularLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  {p | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

/-- The singular locus is the complement of the regular locus. -/
def singularLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  (regularLocus R)ᶜ

/-! ## The J-conditions -/

/-- A ring has a nonempty open regular locus (the J-0 condition). -/
def IsJ0 (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∃ U : Set (PrimeSpectrum R),
      IsOpen U ∧ U.Nonempty ∧ U ⊆ regularLocus R

/-- The regular locus is open (the J-1 condition). -/
def IsJ1 (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ IsOpen (regularLocus R)

/-- Every finite-type algebra has open regular locus (the J-2 condition). -/
def IsJ2 (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
      IsJ1 S

/-- A relative open subset of `S` is nonempty and contained in `T`.

The set `S` is viewed with its subspace topology: every relative open is the
intersection of `S` with an ambient open set. -/
def ContainsNonemptyRelativeOpen {X : Type*} [TopologicalSpace X]
    (S T : Set X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ (U ∩ S).Nonempty ∧ U ∩ S ⊆ T

/-! ## The local criterion for J-1 -/

/-- The J-1 condition is characterized by regular points on every irreducible
closed subset having a nonempty relative open neighborhood of regular points. -/
theorem isJ1_iff_regularLocus_inter_closed_contains_open
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsJ1 R ↔
      ∀ p : PrimeSpectrum R, p ∈ regularLocus R →
        ContainsNonemptyRelativeOpen
          (PrimeSpectrum.zeroLocus p.asIdeal)
          (PrimeSpectrum.zeroLocus p.asIdeal ∩ regularLocus R) := by
  sorry

/-! ## Passing from closed subsets to the whole spectrum -/

/-- If every quotient by a prime has a nonempty open regular locus, then the
regular locus of the original Noetherian ring is open. -/
theorem isJ1_of_isJ0_quotient_prime
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (h : ∀ p : PrimeSpectrum R, IsJ0 (R ⧸ p.asIdeal)) :
    IsJ1 R := by
  sorry

/-! ## J-0 under finite-type maps -/

/-- A finite-type injective map from a Noetherian domain to a J-0 domain
descends the J-0 property to the source. -/
theorem isJ0_of_finiteType_injective_domain
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsDomain R] [IsDomain S]
    (f : R →+* S) (hinj : Function.Injective f)
    (hfinite : RingHom.FiniteType f) (hS : IsJ0 S) :
    IsJ0 R := by
  sorry

/-- The induced fraction-field extension used in the J-0 ascent lemma is
separable. -/
def FractionFieldExtensionIsSeparable
    {R S : Type u} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S]
    (f : R →+* S) (hinj : Function.Injective f) : Prop :=
  letI : Algebra (FractionRing R) (FractionRing S) :=
    (Formalization.Books.Algebra.Unit113.fractionFieldMap f hinj).toAlgebra
  Algebra.IsSeparable (FractionRing R) (FractionRing S)

/-- A finite-type injective map of domains carries J-0 from the source to the
target when the induced extension of fraction fields is separable. -/
theorem isJ0_of_finiteType_injective_domain_separable
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsDomain R] [IsDomain S]
    (f : R →+* S) (hinj : Function.Injective f)
    (hfinite : RingHom.FiniteType f)
    (hR : IsJ0 R)
    (hseparable : FractionFieldExtensionIsSeparable f hinj) :
    IsJ0 S := by
  sorry

/-! ## The four characterizations of J-2 -/

/-- Data for the finite-domain algebra in the purely inseparable residue-field
criterion for J-2. -/
structure FiniteDomainJ0Algebra
    (R K : Type u) [CommRing R] [Field K] where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]
  [finite : Module.Finite R carrier]
  [domain : IsDomain carrier]
  j0 : IsJ0 carrier
  fractionFieldEquiv : Nonempty (FractionRing carrier ≃+* K)

/-- The four equivalent formulations of the J-2 property. -/
theorem isJ2_iff
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    List.TFAE
      [ IsJ2 R,
        ∀ (S : Type u) [CommRing S] [Algebra R S]
          [Algebra.FiniteType R S],
          IsDomain S → IsJ0 S,
        ∀ (S : Type u) [CommRing S] [Algebra R S]
          [Module.Finite R S],
          IsJ1 S,
        ∀ (p : PrimeSpectrum R) (K : Type u) [Field K]
          [Algebra p.asIdeal.ResidueField K]
          [FiniteDimensional p.asIdeal.ResidueField K]
          [IsPurelyInseparable p.asIdeal.ResidueField K],
          Nonempty (FiniteDomainJ0Algebra R K) ] := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit47
