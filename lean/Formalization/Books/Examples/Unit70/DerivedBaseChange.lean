import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.MoreAlgebra.Unit60.DerivedBaseChange
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Examples, Chapter 70: derived base change

This file records the derived base-change square, the comparison map, and the
explicit polynomial counterexample from the source.  The derived-category
constructions reuse the canonical change-of-rings interfaces from More on
Algebra, Chapter 60.  The one comparison map not exposed by that API is
introduced through an existence interface, so its later users have the exact
source-facing type without choosing a resolution in this chapter.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.Algebra.Unit14
open Formalization.Books.MoreAlgebra.Unit60
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit10
open scoped TensorProduct

universe u

namespace Formalization.Books.Examples.Unit70

/-! ## Derived categories and the base-change square -/

/- Mathlib's standard derived-category construction is canonical, but it is
not registered as a global instance for every module category. -/
noncomputable instance standardModuleDerivedCategory (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard (ModuleCat.{u} R)

/-- The standard derived category of modules over a commutative ring. -/
abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)] :=
  Formalization.Books.MoreAlgebra.Unit60.D R

/-- Derived extension of scalars along a ring map. -/
noncomputable abbrev derivedBaseChange
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : D R ⥤ D S :=
  Formalization.Books.MoreAlgebra.Unit60.derivedBaseChangeFunctor f

/-- Derived restriction of scalars along a ring map. -/
noncomputable abbrev derivedRestriction
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : D S ⥤ D R :=
  Formalization.Books.MoreAlgebra.Unit60.derivedRestrictionFunctor f

/-- The ring `A' = A ⊗[R] R'` in a base-change square. -/
abbrev baseChangedRing
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) :=
  letI : Algebra R A := g.toAlgebra
  letI : Algebra R R' := f.toAlgebra
  A ⊗[R] R'

/-- The canonical map `A → A ⊗[R] R'`. -/
def baseChangedLeftMap
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) :
    letI : Algebra R A := g.toAlgebra
    letI : Algebra R R' := f.toAlgebra
    A →+* baseChangedRing f g :=
  baseChangeAlgebraMap g f

/-- The canonical map `R' → A ⊗[R] R'`. -/
def baseChangedRightMap
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) :
    letI : Algebra R A := g.toAlgebra
    letI : Algebra R R' := f.toAlgebra
    R' →+* baseChangedRing f g :=
  baseChangeRingMap g f

/-- The two canonical maps give the commutative base-change square. -/
theorem baseChanged_square_commutes
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) :
    (baseChangedLeftMap f g).comp g = (baseChangedRightMap f g).comp f := by
  sorry

/-- The base-changed module `M ⊗[R] R'`, with its canonical `A ⊗[R] R'` action.

The underlying construction is Mathlib's extension-of-scalars model from
Algebra, Chapter 14. -/
noncomputable def baseChangedModule
    {R R' A M : Type u} [CommRing R] [CommRing R'] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* R') (g : R →+* A) :
    letI : Algebra R A := g.toAlgebra
    letI : Algebra R R' := f.toAlgebra
    ModuleCat (baseChangedRing f g) :=
  (ModuleCat.extendScalars (baseChangedLeftMap f g)).obj (ModuleCat.of A M)

/-- The derived object `K ⊗ᴸ_R R'`, viewed in `D(R')`, for `K : D(A)`. -/
noncomputable def derivedTensorOverBase
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) (K : D A) : D R' :=
  (derivedBaseChange f).obj ((derivedRestriction g).obj K)

/-- The derived functor `- ⊗ᴸ_A A' : D(A) ⥤ D(A')`. -/
noncomputable def derivedBaseChangeToChangedRing
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) :
    letI : Algebra R A := g.toAlgebra
    letI : Algebra R R' := f.toAlgebra
    D A ⥤ D (baseChangedRing f g) :=
  derivedBaseChange (baseChangedLeftMap f g)

/-- The derived object `K ⊗ᴸ_A (A ⊗[R] R')`, restricted to `D(R')`. -/
noncomputable def derivedTensorOverChangedRing
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) (K : D A) : D R' :=
  letI : Algebra R A := g.toAlgebra
  letI : Algebra R R' := f.toAlgebra
  (derivedRestriction (baseChangedRightMap f g)).obj
    ((derivedBaseChangeToChangedRing f g).obj K)

/-- Data for the canonical derived comparison map in `D(R')`. -/
structure DerivedBaseChangeComparisonData
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) (K : D A) where
  comparison : derivedTensorOverBase f g K ⟶ derivedTensorOverChangedRing f g K

/-- The comparison morphism exists for every derived object. -/
theorem existsDerivedBaseChangeComparison
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) (K : D A) :
    Nonempty (DerivedBaseChangeComparisonData f g K) := by
  sorry

/-- A chosen version of the canonical comparison morphism. -/
noncomputable def derivedBaseChangeComparison
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) (K : D A) :
    derivedTensorOverBase f g K ⟶ derivedTensorOverChangedRing f g K :=
  (Classical.choice (existsDerivedBaseChangeComparison f g K)).comparison

/-- The statement that the derived comparison is an isomorphism. -/
def DerivedBaseChangeComparisonIsIso
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A) (K : D A) : Prop :=
  IsIso (derivedBaseChangeComparison f g K)

/-! ## The polynomial counterexample -/

/-- The two-variable polynomial ring `k[x,y]`. -/
abbrev ExamplePolynomialRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k

/-- The variables `x` and `y`. -/
def exampleX (k : Type u) [CommRing k] : ExamplePolynomialRing k :=
  MvPolynomial.X 0

def exampleY (k : Type u) [CommRing k] : ExamplePolynomialRing k :=
  MvPolynomial.X 1

/-- The ideals `(xy)` and `(x²)`. -/
def exampleXYIdeal (k : Type u) [CommRing k] :
    Ideal (ExamplePolynomialRing k) :=
  Ideal.span {exampleX k * exampleY k}

def exampleXSquaredIdeal (k : Type u) [CommRing k] :
    Ideal (ExamplePolynomialRing k) :=
  Ideal.span {(exampleX k) ^ 2}

/-- The rings `R' = R/(xy)` and `A = R/(x²)`. -/
abbrev exampleRPrime (k : Type u) [CommRing k] :=
  ExamplePolynomialRing k ⧸ exampleXYIdeal k

abbrev exampleA (k : Type u) [CommRing k] :=
  ExamplePolynomialRing k ⧸ exampleXSquaredIdeal k

/-- The two quotient maps in the example. -/
def exampleRToRPrime (k : Type u) [CommRing k] :
    ExamplePolynomialRing k →+* exampleRPrime k :=
  Ideal.Quotient.mk _

def exampleRToA (k : Type u) [CommRing k] :
    ExamplePolynomialRing k →+* exampleA k :=
  Ideal.Quotient.mk _

/-- The base-changed ring `A' = A ⊗[R] R'`. -/
abbrev exampleAPrime (k : Type u) [CommRing k] :=
  baseChangedRing (exampleRToRPrime k) (exampleRToA k)

/-- The image of `x` in `R'`. -/
def exampleXPrime (k : Type u) [CommRing k] : exampleRPrime k :=
  exampleRToRPrime k (exampleX k)

/-- Multiplication by `x²` on `R'`, the differential in the displayed model. -/
def exampleXSquaredDifferential (k : Type u) [CommRing k] :
    exampleRPrime k →ₗ[exampleRPrime k] exampleRPrime k :=
  LinearMap.lsmul (exampleRPrime k) (exampleRPrime k) ((exampleXPrime k) ^ 2)

/-- A two-term complex presentation records its two nonzero terms and its
differential. -/
structure TwoTermComplexPresentation (S : Type u) [CommRing S] where
  degreeMinusOne : ModuleCat.{u} S
  degreeZero : ModuleCat.{u} S
  differential : degreeMinusOne ⟶ degreeZero

/-- A complex is represented by the given two-term presentation. -/
def IsRepresentedByTwoTermComplex
    {S : Type u} [CommRing S] [HasDerivedCategory.{u + 1} (ModuleCat.{u} S)]
    (E : D S) (P : TwoTermComplexPresentation S) : Prop :=
  ∃ K : CochainComplex (ModuleCat.{u} S) ℤ,
    (∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero (K.X n)) ∧
    Nonempty (K.X (-1) ≅ P.degreeMinusOne) ∧
    Nonempty (K.X 0 ≅ P.degreeZero) ∧
    (∃ (eMinusOne : K.X (-1) ≅ P.degreeMinusOne)
      (eZero : K.X 0 ≅ P.degreeZero),
      eMinusOne.hom ≫ P.differential ≫ eZero.inv = K.d (-1) 0) ∧
    Nonempty ((DerivedCategory.Q.obj K) ≅ E)

/-- The two-term presentation with differential `x² : R' → R'`. -/
def exampleTwoTermPresentation (k : Type u) [CommRing k] :
    TwoTermComplexPresentation (exampleRPrime k) where
  degreeMinusOne := ModuleCat.of (exampleRPrime k) (exampleRPrime k)
  degreeZero := ModuleCat.of (exampleRPrime k) (exampleRPrime k)
  differential := ModuleCat.ofHom (exampleXSquaredDifferential k)

/-- The ordinary base change `A ⊗[R] R'`, viewed as an `R'`-module. -/
noncomputable def exampleOrdinaryBaseChangeModule (k : Type u) [CommRing k] :
    ModuleCat (exampleRPrime k) :=
  letI : Algebra (ExamplePolynomialRing k) (exampleA k) :=
    (exampleRToA k).toAlgebra
  letI : Algebra (ExamplePolynomialRing k) (exampleRPrime k) :=
    (exampleRToRPrime k).toAlgebra
  (ModuleCat.restrictScalars (baseChangedRightMap
      (exampleRToRPrime k) (exampleRToA k))).obj
    (ModuleCat.of (exampleAPrime k) (exampleAPrime k))

/-- The object `A ⊗ᴸ_R R'` in `D(R')`. -/
noncomputable def exampleDerivedTensor (k : Type u) [CommRing k] :
    D (exampleRPrime k) :=
  derivedTensorOverBase (exampleRToRPrime k) (exampleRToA k)
    (moduleStalk (exampleA k) (ModuleCat.of (exampleA k) (exampleA k)))

/-- The explicit polynomial derived tensor product is represented by the
two-term complex `x² : R' → R'`. -/
theorem example_derivedTensor_represented_by_xSquared
    (k : Type u) [Field k] :
    IsRepresentedByTwoTermComplex (exampleDerivedTensor k)
      (exampleTwoTermPresentation k) := by
  sorry

/-- Its degree-zero cohomology is the ordinary tensor product. -/
theorem example_derivedTensor_h0
    (k : Type u) [Field k] :
    Nonempty ((derivedCohomologyFunctor (ModuleCat.{u} (exampleRPrime k)) 0).obj
      (exampleDerivedTensor k) ≅ exampleOrdinaryBaseChangeModule k) := by
  sorry

/-! ## Splitting and the obstruction -/

/-- An object splits as the direct sum of its degree-zero and degree-minus-one
cohomology objects. -/
def SplitsAsCohomology
    {S : Type u} [CommRing S] [HasDerivedCategory.{u + 1} (ModuleCat.{u} S)]
    (E : D S) : Prop :=
  Nonempty ((moduleStalk S
      ((derivedCohomologyFunctor (ModuleCat.{u} S) 0).obj E)) ⊞
    ((moduleStalk S
      ((derivedCohomologyFunctor (ModuleCat.{u} S) (-1)).obj E))⟦(1 : ℤ)⟧) ≅ E)

/-- A free degree-zero cohomology object gives the splitting asserted in the
source discussion. -/
theorem free_h0_gives_cohomology_split
    {S : Type u} [CommRing S] (E : D S)
    [Module.Free S
      ((derivedCohomologyFunctor (ModuleCat.{u} S) 0).obj E : Type u)] :
    SplitsAsCohomology E := by
  sorry

/-- The displayed two-term object is not isomorphic to the sum of its
cohomology objects. -/
theorem example_derivedTensor_not_split
    (k : Type u) [Field k] :
    ¬ SplitsAsCohomology (exampleDerivedTensor k) := by
  sorry

/-- The canonical comparison map fails to be an isomorphism in the explicit
polynomial example. -/
theorem example_derivedBaseChangeComparison_not_iso
    (k : Type u) [Field k] :
    ¬ DerivedBaseChangeComparisonIsIso (exampleRToRPrime k) (exampleRToA k)
      (moduleStalk (exampleA k) (ModuleCat.of (exampleA k) (exampleA k))) := by
  sorry

/-- Any proposed lift in the polynomial example has free degree-zero
cohomology over `A'`. -/
theorem lifted_object_h0_free
    (k : Type u) [Field k] (E : D (exampleAPrime k))
    (hE : Nonempty ((derivedRestriction (baseChangedRightMap
      (exampleRToRPrime k) (exampleRToA k))).obj E ≅
      exampleDerivedTensor k)) :
    Module.Free (exampleAPrime k)
      ((derivedCohomologyFunctor (ModuleCat.{u} (exampleAPrime k)) 0).obj E : Type u) := by
  sorry

/-- Consequently, a proposed lift splits as its degree-zero and
degree-minus-one cohomology objects. -/
theorem lifted_object_splits
    (k : Type u) [Field k] (E : D (exampleAPrime k))
    (hE : Nonempty ((derivedRestriction (baseChangedRightMap
      (exampleRToRPrime k) (exampleRToA k))).obj E ≅
      exampleDerivedTensor k)) :
    SplitsAsCohomology E := by
  sorry

/-- No object of `D(A')` maps to the displayed derived tensor object in
`D(R')`. -/
theorem example_no_object_lifts_derivedTensor
    (k : Type u) [Field k] :
    ¬ ∃ E : D (exampleAPrime k),
      Nonempty ((derivedRestriction (baseChangedRightMap
        (exampleRToRPrime k) (exampleRToA k))).obj E ≅
        exampleDerivedTensor k) := by
  sorry

/-! ## The chapter lemma -/

/-- A triangulated functor has the source's required compatibility with
derived base change on degree-zero module objects. -/
def IsDerivedBaseChangeFunctor
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (f : R →+* R') (g : R →+* A)
    (T : D A ⥤ D (baseChangedRing f g)) : Prop :=
  Nonempty (ExactTriangulatedFunctorData T) ∧
    ∀ M : ModuleCat.{u} A,
      Nonempty ((derivedRestriction (baseChangedRightMap f g)).obj
        (T.obj (moduleStalk A M)) ≅
        derivedTensorOverBase f g (moduleStalk A M))

/-- The explicit polynomial maps witness that a derived base-change functor
does not exist in general. -/
theorem lemma_no_derived_base_change
    (k : Type u) [Field k] :
    ¬ ∃ T : D (exampleA k) ⥤ D (exampleAPrime k),
      IsDerivedBaseChangeFunctor (exampleRToRPrime k) (exampleRToA k) T := by
  sorry

end Formalization.Books.Examples.Unit70
