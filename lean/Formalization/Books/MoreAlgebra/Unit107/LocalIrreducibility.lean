import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit155.Henselization
import Mathlib.Data.ENat.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.RingHom.PurelyInseparable
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# More on Algebra, Chapter 107: Local irreducibility

The source section defines unibranch and geometrically unibranch local rings,
compares their branches after henselization and strict henselization, defines
branch counts, and records invariance under smooth local maps.
The chosen henselizations are represented by the source-facing data from
Algebra, Chapter 155.
-/

namespace Formalization.Books.MoreAlgebra.Unit107

open Formalization.Books.Algebra.Unit155
open Formalization.Books.Algebra.Unit37
open scoped TensorProduct

noncomputable section

universe u v

/-! ## The reduction and its normalization -/

/-- The reduced quotient of a commutative ring. -/
abbrev ReducedRing (A : Type u) [CommRing A] : Type u :=
  A ⧸ nilradical A

/-- The total ring of fractions of the reduced quotient. -/
abbrev TotalFractionRing (A : Type u) [CommRing A] : Type u :=
  FractionRing (ReducedRing A)

/-- The integral closure of the reduced quotient in its total ring of fractions.

This is the ring called `A'` in the source.  The ambient `A`-algebra below is
obtained from the quotient map `A → A_red`. -/
abbrev Normalization (A : Type u) [CommRing A] : Type u :=
  integralClosure (ReducedRing A) (TotalFractionRing A)

/-- The canonical map from a ring to the normalization of its reduction. -/
def normalizationMap (A : Type u) [CommRing A] : A →+* Normalization A :=
  (algebraMap (ReducedRing A) (Normalization A)).comp
    (Ideal.Quotient.mk (nilradical A))

instance normalizationAlgebra (A : Type u) [CommRing A] :
    Algebra A (Normalization A) :=
  (normalizationMap A).toAlgebra

instance henselizationDataCommRing
    (A : Type u) [CommRing A] [IsLocalRing A]
    (D : HenselizationData A) : CommRing D.carrier :=
  D.commRingCarrier

instance henselizationDataLocalRing
    (A : Type u) [CommRing A] [IsLocalRing A]
    (D : HenselizationData A) : IsLocalRing D.carrier :=
  D.localRingCarrier

instance henselizationDataAlgebra
    (A : Type u) [CommRing A] [IsLocalRing A]
    (D : HenselizationData A) : Algebra A D.carrier :=
  D.map.toAlgebra

instance strictHenselizationDataCommRing
    (A : Type u) [CommRing A] [IsLocalRing A]
    {K : Type u} [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K) : CommRing D.strictHenselization :=
  D.commRingStrictHenselization

instance strictHenselizationDataLocalRing
    (A : Type u) [CommRing A] [IsLocalRing A]
    {K : Type u} [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K) : IsLocalRing D.strictHenselization :=
  D.localRingStrictHenselization

instance strictHenselizationDataAlgebra
    (A : Type u) [CommRing A] [IsLocalRing A]
    {K : Type u} [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K) : Algebra A D.strictHenselization :=
  D.strictMap.toAlgebra

/-! ## Unibranch local rings -/

/-- A local ring is unibranch when its reduction is a domain and the
normalization of that reduction is local. -/
def IsUnibranch (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  IsDomain (ReducedRing A) ∧ IsLocalRing (Normalization A)

/-- A residue-field extension is purely inseparable when witnessed by a ring
homomorphism with Mathlib's canonical purely-inseparable predicate. -/
def PurelyInseparableResidueExtension
    (A B : Type u) [CommRing A] [IsLocalRing A]
    [CommRing B] (hB : IsLocalRing B) : Prop :=
  letI := hB
  ∃ f : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B,
    RingHom.IsPurelyInseparable f

/-- A local ring is geometrically unibranch when it is unibranch and its
normalization has purely inseparable residue field over the original ring. -/
def IsGeometricallyUnibranch
    (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ∃ hB : IsLocalRing (Normalization A),
    IsUnibranch A ∧ PurelyInseparableResidueExtension A (Normalization A) hB

/-- The alternate minimal-prime formulation of unibranchness. -/
theorem isUnibranch_iff_unique_minimal_and_normalization_local
    (A : Type u) [CommRing A] [IsLocalRing A] :
    IsUnibranch A ↔
      (∃! p : PrimeSpectrum A, IsMin p) ∧
        IsLocalRing (Normalization A) := by
  sorry

/-- The alternate minimal-prime and residue-field formulation of geometric
unibranchness. -/
theorem isGeometricallyUnibranch_iff_unique_minimal_and_residue_extension
    (A : Type u) [CommRing A] [IsLocalRing A] :
    IsGeometricallyUnibranch A ↔
      ∃ hB : IsLocalRing (Normalization A),
        (∃! p : PrimeSpectrum A, IsMin p) ∧
          PurelyInseparableResidueExtension A (Normalization A) hB := by
  sorry

/-- A normal local domain is geometrically unibranch. -/
theorem isGeometricallyUnibranch_of_isNormalDomain
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hA : IsNormalDomain A) :
    IsGeometricallyUnibranch A := by
  sorry

/-! ## Prime-spectrum interfaces for the branch comparisons -/

/-- The minimal-prime points of a ring. -/
def MinimalPrimeSpectrum (R : Type u) [CommRing R] : Type u :=
  {p : PrimeSpectrum R // IsMin p}

/-- The maximal-prime points of a ring. -/
def MaximalPrimeSpectrum (R : Type u) [CommRing R] : Type u :=
  {p : PrimeSpectrum R // IsMax p}

/-- The fibre over a maximal prime along a map of rings. -/
def MaximalFiberOver
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (m : MaximalPrimeSpectrum R) : Type u :=
  {p : MaximalPrimeSpectrum S // PrimeSpectrum.comap f p.1 = m.1}

/-- Ring homomorphisms between two extensions which agree on a specified
base ring. -/
def RingHomsOver
    {k K L : Type u} [CommRing k] [CommRing K] [CommRing L]
    (ι : k →+* K) (j : k →+* L) : Type u :=
  {f : K →+* L // f.comp ι = j}

/-! ## Henselian and strict-henselian branch diagrams -/

/-- The ring `(A')^h = A' ⊗_A A^h` in the source. -/
abbrev HenselianNormalization
    (A : Type u) [CommRing A] [IsLocalRing A]
    (D : HenselizationData A) : Type u :=
  Normalization A ⊗[A] D.carrier

/-- The left-hand ring map in the henselian branch diagram. -/
def henselianNormalizationLeft
    (A : Type u) [CommRing A] [IsLocalRing A]
    (D : HenselizationData A) :
    Normalization A →+* HenselianNormalization A D :=
  Algebra.TensorProduct.includeLeftRingHom

/-- The right-hand ring map in the henselian branch diagram. -/
def henselianNormalizationRight
    (A : Type u) [CommRing A] [IsLocalRing A]
    (D : HenselizationData A) :
    D.carrier →+* HenselianNormalization A D :=
  Algebra.TensorProduct.includeRight.toRingHom

/-- The ring `(A')^sh = A' ⊗_A A^sh` in the source. -/
abbrev StrictHenselianNormalization
    (A : Type u) [CommRing A] [IsLocalRing A]
    {K : Type u} [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K) : Type u :=
  Normalization A ⊗[A] D.strictHenselization

/-- The left-hand ring map in the strict-henselian branch diagram. -/
def strictHenselianNormalizationLeft
    (A : Type u) [CommRing A] [IsLocalRing A]
    {K : Type u} [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K) :
    Normalization A →+* StrictHenselianNormalization A D :=
  Algebra.TensorProduct.includeLeftRingHom

/-- The right-hand ring map in the strict-henselian branch diagram. -/
def strictHenselianNormalizationRight
    (A : Type u) [CommRing A] [IsLocalRing A]
    {K : Type u} [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K) :
    D.strictHenselization →+* StrictHenselianNormalization A D :=
  Algebra.TensorProduct.includeRight.toRingHom

/-- The three assertions in the source's henselian branch lemma: maximal
ideals on the left, minimal primes on the right, and unique incidence between
minimal and maximal primes. -/
theorem branches
    (A : Type u) [CommRing A] [IsLocalRing A]
    [Finite (MinimalPrimeSpectrum A)]
    (D : HenselizationData A) :
    (∃ f : MaximalPrimeSpectrum (HenselianNormalization A D) →
        MaximalPrimeSpectrum (Normalization A),
      (∀ p, (f p).1 =
        PrimeSpectrum.comap (henselianNormalizationLeft A D) p.1) ∧
        Function.Bijective f) ∧
    (∃ f : MinimalPrimeSpectrum (HenselianNormalization A D) →
        MinimalPrimeSpectrum D.carrier,
      (∀ p, (f p).1 =
        PrimeSpectrum.comap (henselianNormalizationRight A D) p.1) ∧
        Function.Bijective f) ∧
    (∀ p : MinimalPrimeSpectrum (HenselianNormalization A D),
      ∃! m : MaximalPrimeSpectrum (HenselianNormalization A D),
        p.1 ≤ m.1) ∧
    (∀ m : MaximalPrimeSpectrum (HenselianNormalization A D),
      ∃! p : MinimalPrimeSpectrum (HenselianNormalization A D),
        p.1 ≤ m.1) := by
  sorry

/-- The strict-henselian branch lemma, including the residue-field fibre
description over every maximal ideal of the normalization. -/
theorem geometricBranches
    (A : Type u) [CommRing A] [IsLocalRing A]
    [Finite (MinimalPrimeSpectrum A)]
    {K : Type u} [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K) :
    (∀ m : MaximalPrimeSpectrum (Normalization A),
      ∃ i : IsLocalRing.ResidueField A →+*
          m.1.asIdeal.ResidueField,
        RingHom.IsIntegral i ∧
        Nonempty
          (MaximalFiberOver (strictHenselianNormalizationLeft A D) m ≃
            RingHomsOver i
              (algebraMap (IsLocalRing.ResidueField A)
                (AlgebraicClosure (IsLocalRing.ResidueField A))))) ∧
    (∃ f : MinimalPrimeSpectrum (StrictHenselianNormalization A D) →
        MinimalPrimeSpectrum D.strictHenselization,
      (∀ p, (f p).1 =
        PrimeSpectrum.comap (strictHenselianNormalizationRight A D) p.1) ∧
        Function.Bijective f) ∧
    (∀ p : MinimalPrimeSpectrum (StrictHenselianNormalization A D),
      ∃! m : MaximalPrimeSpectrum (StrictHenselianNormalization A D),
        p.1 ≤ m.1) ∧
    (∀ m : MaximalPrimeSpectrum (StrictHenselianNormalization A D),
      ∃! p : MinimalPrimeSpectrum (StrictHenselianNormalization A D),
        p.1 ≤ m.1) := by
  sorry

/-! ## Characterization by henselizations -/

/-- A ring has a unique minimal prime. -/
def HasUniqueMinimalPrime (R : Type u) [CommRing R] : Prop :=
  ∃! p : PrimeSpectrum R, IsMin p

theorem isUnibranch_iff_henselization_has_unique_minimal_prime
    (A : Type u) [CommRing A] [IsLocalRing A]
    (D : HenselizationData A) :
    IsUnibranch A ↔ HasUniqueMinimalPrime D.carrier := by
  sorry

theorem isGeometricallyUnibranch_iff_strict_henselization_has_unique_minimal_prime
    (A : Type u) [CommRing A] [IsLocalRing A]
    {K : Type u} [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K) :
    IsGeometricallyUnibranch A ↔
      HasUniqueMinimalPrime D.strictHenselization := by
  sorry

/-! ## Branch counts -/

/-- The number of branches, with `⊤` denoting infinitely many branches. -/
def numberOfBranches
    (A : Type u) [CommRing A] [IsLocalRing A]
    (D : HenselizationData A) : ℕ∞ :=
  ENat.card (MinimalPrimeSpectrum D.carrier)

/-- The number of geometric branches, with `⊤` denoting infinitely many
geometric branches. -/
def numberOfGeometricBranches
    (A : Type u) [CommRing A] [IsLocalRing A]
    {K : Type u} [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K) : ℕ∞ :=
  ENat.card (MinimalPrimeSpectrum D.strictHenselization)

/-- The finite sum of natural-number weights, or infinity when the index type
is infinite. -/
noncomputable def finiteWeightSum
    (ι : Type u) (w : ι → ℕ) : ℕ∞ :=
  by
    classical
    exact if hι : Finite ι then
    letI := Fintype.ofFinite ι
    ∑ i, (w i : ℕ∞)
    else
      ⊤

/-- The separable degree of a field extension presented by a ring homomorphism. -/
noncomputable def separableDegreeOfRingHom
    {k L : Type u} [Field k] [Field L] (f : k →+* L) : ℕ :=
  letI : Algebra k L := f.toAlgebra
  Field.finSepDegree k L

/-- The branch multiplicity sum attached to residue-field maps from the base
to the residue fields of the maximal ideals of its normalization. -/
noncomputable def geometricBranchMultiplicity
    (A : Type u) [CommRing A] [IsLocalRing A]
    (ι : ∀ m : MaximalPrimeSpectrum (Normalization A),
      IsLocalRing.ResidueField A →+* m.1.asIdeal.ResidueField) : ℕ∞ :=
  finiteWeightSum _ (fun m => separableDegreeOfRingHom (ι m))

/-- The source's five relationships between minimal primes, branch counts,
normalizations, and separable residue-field degrees. -/
theorem numberOfBranches_relationships
    (A : Type u) [CommRing A] [IsLocalRing A]
    (D : HenselizationData A)
    {K : Type u} [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    (Ds : StrictHenselizationData A K) :
    (Infinite (MinimalPrimeSpectrum A) →
      numberOfBranches A D = ⊤ ∧
      numberOfGeometricBranches A Ds = ⊤) ∧
    (numberOfBranches A D = 1 ↔ IsUnibranch A) ∧
    (numberOfGeometricBranches A Ds = 1 ↔ IsGeometricallyUnibranch A) ∧
    (∀ [Finite (MinimalPrimeSpectrum A)],
      numberOfBranches A D =
        ENat.card (MaximalPrimeSpectrum (Normalization A))) ∧
    (∀ [Finite (MinimalPrimeSpectrum A)],
      ∃ ι : ∀ m : MaximalPrimeSpectrum (Normalization A),
          IsLocalRing.ResidueField A →+* m.1.asIdeal.ResidueField,
        numberOfGeometricBranches A Ds = geometricBranchMultiplicity A ι) := by
  sorry

/-! ## Smooth invariance -/

theorem numberOfGeometricBranches_invariant_of_smooth_local_map
    {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    (f : A →+* B) (hf : IsLocalHom f) (hsmooth : RingHom.Smooth f)
    {K K' : Type u} [Field K] [Field K']
    [Algebra (IsLocalRing.ResidueField A) K]
    [Algebra (IsLocalRing.ResidueField B) K']
    (DA : StrictHenselizationData A K)
    (DB : StrictHenselizationData B K') :
    numberOfGeometricBranches A DA =
      numberOfGeometricBranches B DB := by
  sorry

theorem numberOfBranches_invariant_of_smooth_local_map_of_purely_inseparable_residue_field
    {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    (f : A →+* B) (hf : IsLocalHom f) (hsmooth : RingHom.Smooth f)
    (hres : ∃ g : IsLocalRing.ResidueField A →+*
        IsLocalRing.ResidueField B, RingHom.IsPurelyInseparable g)
    (DA : HenselizationData A) (DB : HenselizationData B) :
    numberOfBranches A DA = numberOfBranches B DB := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit107
