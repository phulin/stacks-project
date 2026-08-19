import Formalization.Books.Dga.Unit14.DifferentialGradedProjectives
import Formalization.Books.Dga.Unit36.CompactObjects
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Examples, Chapter 71: an interesting compact object

This section records the explicit characteristic-two dg-algebra example and
the compact-object obstruction built from it.  The quotient algebra and its
distinguished elements use Mathlib's polynomial and ideal-quotient APIs.  The
chapter-specific data records the graded differential, derived-category
model, and the intermediate homological calculations in source order; the
general compactness and finite graded-projective predicates are the canonical
ones from the earlier Dga formalization.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit14
open Formalization.Books.Dga.Unit22
open Formalization.Books.Dga.Unit36
open Formalization.Books.Derived.Unit37
open Formalization.Books.Homology.Unit03

universe u v w wk vk

namespace Formalization.Books.Examples.Unit71

/-! ## The base-ring comparison -/

/-- A finite complex of finite projective `R`-modules. -/
def IsFiniteProjectiveComplex
    (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧
    (∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
    (∀ n : ℤ, a ≤ n → n ≤ b →
      Module.Finite R (K.X n : Type u) ∧
        Module.Projective R (K.X n : Type u))

/-- The source's meaning of “perfect” for an object represented by a finite
complex of finite projective modules. -/
def IsPerfectModuleDerivedObject
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (E : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
    Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
      IsFiniteProjectiveComplex R K

/-- The comparison statement recalled at the beginning of the source
section. -/
def CompactObjectsOverRingArePerfect
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    [AdditiveCategory (DerivedCategory (ModuleCat.{u} R))]
    [HasCoproducts (DerivedCategory (ModuleCat.{u} R))] : Prop :=
  ∀ E : DerivedCategory (ModuleCat.{u} R),
    IsCompactObject E → IsPerfectModuleDerivedObject R E

theorem compact_objects_over_ring_are_perfect
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    [AdditiveCategory (DerivedCategory (ModuleCat.{u} R))]
    [HasCoproducts (DerivedCategory (ModuleCat.{u} R))] :
    CompactObjectsOverRingArePerfect R := by
  sorry

/-! ## The explicit characteristic-two algebra -/

/-- The polynomial ring in the two variables used by the source example. -/
abbrev ExamplePolynomialRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k

/-- The polynomial variables `x` and `y`. -/
def exampleX (k : Type u) [CommRing k] : ExamplePolynomialRing k :=
  MvPolynomial.X 0

def exampleY (k : Type u) [CommRing k] : ExamplePolynomialRing k :=
  MvPolynomial.X 1

/-- The square-zero relation defining the dg-algebra's underlying ring. -/
def exampleYSquaredIdeal (k : Type u) [CommRing k] :
    Ideal (ExamplePolynomialRing k) :=
  Ideal.span {(exampleY k) ^ 2}

/-- The algebra `k[x,y]/(y^2)` from the source. -/
abbrev InterestingAlgebra (k : Type u) [CommRing k] :=
  ExamplePolynomialRing k ⧸ exampleYSquaredIdeal k

/-- The images of the two polynomial generators in the quotient algebra. -/
def interestingX (k : Type u) [CommRing k] : InterestingAlgebra k :=
  Ideal.Quotient.mk _ (exampleX k)

def interestingY (k : Type u) [CommRing k] : InterestingAlgebra k :=
  Ideal.Quotient.mk _ (exampleY k)

/-- The degree-zero element `x^2+x` which is the differential of `y`. -/
def interestingDifferentialOfY (k : Type u) [CommRing k] :
    InterestingAlgebra k :=
  (interestingX k) ^ 2 + interestingX k

/-- The quotient presentation is canonical and uses the identity ring
equivalence on the quotient. -/
def interestingAlgebraPresentation (k : Type u) [CommRing k] :
    InterestingAlgebra k ≃+* InterestingAlgebra k :=
  RingEquiv.refl _

/-- The square-zero relation for the distinguished element `y`. -/
theorem interestingY_sq (k : Type u) [CommRing k] :
    (interestingY k) ^ 2 = 0 := by
  sorry

/-! ## The dg-algebra specification -/

/-- Source-facing data for the grading and differential on the quotient
algebra.

The underlying quotient ring is concrete.  The grading is recorded on the
distinguished generators, while `differential_squared` and
`differential_leibniz` retain the dg-algebra laws.  This avoids introducing a
second graded-ring implementation for the quotient: the canonical graded
dg-algebra API is available through `DifferentialGradedAlgebraData` whenever a
model supplies its homogeneous pieces. -/
structure InterestingDGAData (k : Type u) [Field k] [CharP k 2] where
  carrier : Type u
  [carrierRing : CommRing carrier]
  presentation : carrier ≃+* InterestingAlgebra k
  x : carrier
  y : carrier
  differential : carrier → carrier
  x_degree : ℤ
  y_degree : ℤ
  x_degree_spec : x_degree = 0
  y_degree_spec : y_degree = -1
  x_presentation : presentation x = interestingX k
  y_presentation : presentation y = interestingY k
  differential_x : differential x = 0
  differential_y : differential y = x ^ 2 + x
  differential_degree : Prop
  differential_degree_holds : differential_degree
  differential_squared : ∀ a, differential (differential a) = 0
  differential_leibniz : ∀ a b,
    differential (a * b) = differential a * b + a * differential b

/-- The source's assertion that the displayed quotient carries the stated
characteristic-two dg-algebra structure. -/
def HasInterestingDGAData (k : Type u) [Field k] [CharP k 2] : Prop :=
  Nonempty (InterestingDGAData k)

theorem interesting_dga_data_exists (k : Type u) [Field k] [CharP k 2] :
    HasInterestingDGAData k := by
  sorry

/-! ## The projector and its compact summand -/

/-- A projector in the homotopy category together with the decomposition of
its image and kernel used in the source argument. -/
structure InterestingProjectorData (k : Type u) [Field k] [CharP k 2]
    where
  dga : InterestingDGAData k
  homotopyCategory : Type u
  [category : Category homotopyCategory]
  [additive : AdditiveCategory homotopyCategory]
  [hasBinaryBiproducts : HasBinaryBiproducts homotopyCategory]
  regularObject : homotopyCategory
  multiplicationByX : regularObject ⟶ regularObject
  projector_equation :
    multiplicationByX ≫ multiplicationByX = multiplicationByX
  complementProjector : regularObject ⟶ regularObject
  complement_formula :
    complementProjector = 𝟙 regularObject - multiplicationByX
  kernelObject : homotopyCategory
  imageObject : homotopyCategory
  splitting : Nonempty (regularObject ≅ kernelObject ⊞ imageObject)
  kernel_compact : Prop
  kernel_compact_holds : kernel_compact

/-- The source's direct-sum conclusion for the regular object. -/
def HasProjectorDecomposition
    {k : Type u} [Field k] [CharP k 2]
    (P : InterestingProjectorData k) :=
  P.splitting

/-- The compactness of the kernel summand follows from compactness of the
regular dg module and closure of compact objects under summands. -/
theorem projector_kernel_is_compact
    {k : Type u} [Field k] [CharP k 2]
    (P : InterestingProjectorData k) :
    P.kernel_compact := by
  exact P.kernel_compact_holds

/-! ## The finite graded-projective contradiction -/

/-- The displayed short exact sequence `0 → M → M → N → 0`, with its maps
and componentwise exactness retained as data. -/
structure InterestingShortExactSequence (k : Type u) [Field k]
    [CharP k 2] where
  module : Type u
  quotient : Type u
  inclusion : module → module
  projection : module → quotient
  inclusion_formula : Prop
  projection_formula : Prop
  differential_is_linear : Prop
  exact : Prop
  inclusion_formula_holds : inclusion_formula
  projection_formula_holds : projection_formula
  differential_is_linear_holds : differential_is_linear
  exact_holds : exact

/-- The differential on `N` is linear because `d(y)=x^2+x` becomes zero in
the quotient by `M(x^2+x)`. -/
def QuotientDifferentialIsLinear
    {k : Type u} [Field k] [CharP k 2]
    (S : InterestingShortExactSequence k) : Prop :=
  S.differential_is_linear

/-- The cohomology computation for the representing module `M`. -/
structure InterestingRepresentingModuleData (k : Type u) [Field k]
    [CharP k 2] where
  shortExact : InterestingShortExactSequence k
  finite : Prop
  gradedProjective : Prop
  finite_free : Prop
  finite_free_holds : finite_free
  finite_holds : finite
  gradedProjective_holds : gradedProjective
  hMinusOne : ModuleCat.{u} k
  hZero : ModuleCat.{u} k
  hM : ModuleCat.{u} k
  hMinusOne_to_hZero : hMinusOne ⟶ hZero
  hZero_to_hM : hZero ⟶ hM
  first_map_is_iso : Nonempty (hMinusOne ≅ hZero)
  second_map_is_iso : Nonempty (hZero ≅ hM)
  cohomology_is_k : Prop
  cohomology_is_k_holds : cohomology_is_k

/-- The source's computation of the cohomology of `N`. -/
structure InterestingQuotientCohomologyData (k : Type u) [Field k]
    [CharP k 2] where
  representing : InterestingRepresentingModuleData k
  quotientCohomology : Type u
  polynomialQuotient : Type u
  cohomology_identification : Prop
  cohomology_identification_holds : cohomology_identification

/-- The periodic resolution by multiplication by `y`. -/
structure InterestingPeriodicResolution (k : Type u) [Field k]
    [CharP k 2] where
  quotientCohomology : Type u
  differential : quotientCohomology → quotientCohomology
  differential_formula : Prop
  compatible_with_differential : Prop
  differential_formula_holds : differential_formula
  compatible_with_differential_holds : compatible_with_differential
  resolution_exact : Prop
  resolution_exact_holds : resolution_exact

/-- The spectral-sequence consequence used in the source proof. -/
structure InterestingSpectralSequenceConclusion (k : Type u) [Field k]
    [CharP k 2] where
  periodicResolution : InterestingPeriodicResolution k
  bounded : Prop
  hZero_identification : Prop
  quotient_by_y_hZero : Prop
  bounded_holds : bounded
  hZero_identification_holds : hZero_identification
  quotient_by_y_hZero_holds : quotient_by_y_hZero

/-- The parity obstruction for a finite complex of free modules over
`k[x]/(x^2+x)`, which is isomorphic to `k × k` in characteristic two. -/
abbrev ExampleCoefficientRing (k : Type u) [CommRing k] :=
  Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2 + Polynomial.X}

structure InterestingParityObstruction (k : Type u) [Field k]
    [CharP k 2] where
  finiteFreeComplex : Prop
  coefficientRing_is_product :
    Nonempty (ExampleCoefficientRing k ≃+* (k × k))
  cohomologyEvenDimension : Prop
  finiteFreeComplex_holds : finiteFreeComplex
  cohomologyEvenDimension_holds : cohomologyEvenDimension

/-- The contradiction between the one-dimensional `H^0` calculation and the
even-dimensionality forced by the finite free complex. -/
def InterestingParityContradiction
    {k : Type u} [Field k] [CharP k 2]
    (S : InterestingSpectralSequenceConclusion k)
    (P : InterestingParityObstruction k) : Prop :=
  ¬ (S.quotient_by_y_hZero ∧ P.cohomologyEvenDimension)

/-! ## Compactness and the chapter lemma -/

/-- The source's phrase “represented by a finite and graded projective dg
module”, expressed using the established Dga derived-category interface. -/
def HasFiniteGradedProjectiveRepresentative
    {R : Type u} {A : ℤ → Type v}
    [CommRing R] [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel (D := D) (K := K))
    (E : DgDerivedCategory H) : Prop :=
  ∃ P : DGModule.{u, v, w} D,
    Nonempty (dgDerivedObject H P ≅ E) ∧ IsFiniteGradedProjective P

/-- Compactness together with failure of every finite graded-projective
representation. -/
def IsInterestingCompactObject
    {R : Type u} {A : ℤ → Type v}
    [CommRing R] [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel (D := D) (K := K))
    [AdditiveCategory (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)]
    (E : DgDerivedCategory H) : Prop :=
  DgCompactObject H E ∧ ¬ HasFiniteGradedProjectiveRepresentative H E

/-- The canonical earlier-chapter witness packages precisely the compact
object and its non-representability. -/
abbrev InterestingCompactObjectWitness
    {R : Type u} {A : ℤ → Type v}
    [CommRing R] [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel (D := D) (K := K))
    [AdditiveCategory (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)]
    :=
  CompactObjectNotFiniteGradedProjective H

/-- Same-universe specialization used by the concrete chapter witness. -/
def HasFiniteGradedProjectiveRepresentativeSameUniverse
    {k : Type u}
    {A : ℤ → Type u}
    [CommRing k] [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    [DirectSum.GSemiring A] [DirectSum.GAlgebra k A]
    {D : DifferentialGradedAlgebraData (R := k) (A := A)}
    {K : Type u} [Category.{u} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel (D := D) (K := K))
    (E : DgDerivedCategory H) : Prop :=
  ∃ P : DGModule.{u, u, u} D,
    Nonempty (dgDerivedObject H P ≅ E) ∧ IsFiniteGradedProjective P

/-- All data needed to instantiate the canonical compact-object witness for
the characteristic-two example.  The `presentation_compatible` field states
that the homogeneous pieces and differential in the chosen Dga model are the
graded presentation of `k[x,y]/(y^2)` recorded above. -/
structure InterestingCompactObjectChapterData
    (k : Type u) [Field k] [CharP k 2] where
  dgaPresentation : InterestingDGAData k
  gradedCarrier : ℤ → Type u
  [gradedAddCommGroup : ∀ i, AddCommGroup (gradedCarrier i)]
  [gradedModule : ∀ i, Module k (gradedCarrier i)]
  [gradedSemiring : DirectSum.GSemiring gradedCarrier]
  [gradedAlgebra : DirectSum.GAlgebra k gradedCarrier]
  dga : DifferentialGradedAlgebraData (R := k) (A := gradedCarrier)
  presentation_compatible : Prop
  presentation_compatible_holds : presentation_compatible
  homotopyCarrier : Type u
  [homotopyCategory : Category.{u} homotopyCarrier]
  [homotopyAdditive : AdditiveCategory homotopyCarrier]
  [homotopyShift : HasShift homotopyCarrier ℤ]
  [homotopyShiftAdditive : ∀ n : ℤ,
    (shiftFunctor homotopyCarrier n).Additive]
  [homotopyPretriangulated : Pretriangulated homotopyCarrier]
  homotopyModel : DgHomotopyCategoryModel.{u, u, u, u, u}
    (D := dga) (K := homotopyCarrier)
  [derivedAdditive : AdditiveCategory (DgDerivedCategory homotopyModel)]
  [derivedCoproducts : HasCoproducts (DgDerivedCategory homotopyModel)]
  object : DgDerivedCategory homotopyModel
  compact : DgCompactObject homotopyModel object
  not_represented : ¬ HasFiniteGradedProjectiveRepresentativeSameUniverse
    homotopyModel object

/-! ## Source theorem -/

/-- There is a characteristic-two dg algebra with a compact derived object
which is not represented by a finite graded-projective dg module. -/
theorem lemma_no_good_representatif_compact_object :
    ∃ (k : Type u) (hField : Field k) (hCharP : CharP k 2),
      Nonempty (@InterestingCompactObjectChapterData k hField hCharP) := by
  sorry

end Formalization.Books.Examples.Unit71
