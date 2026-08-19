import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Finite
import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.MoreAlgebra.Unit60.DerivedBaseChange
import Formalization.Books.MoreAlgebra.Unit67.TorDimension
import Formalization.Books.MoreAlgebra.Unit75.RecognizingPerfectComplexes
import Formalization.Books.MoreAlgebra.Unit83.PseudoCoherentPerfectRingMaps

/-!
# More on Algebra, Chapter 84: Relatively perfect modules

This file records the definitions and theorem interfaces in the source
section.  Derived restriction, base change, tensor product, and Hom are the
canonical constructions from the preceding chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit60
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit75
open Formalization.Books.MoreAlgebra.Unit73
open Formalization.Books.MoreAlgebra.Unit83
open Formalization.Books.Algebra.Unit14
open scoped TensorProduct

universe u w

namespace Formalization.Books.MoreAlgebra.Unit84

abbrev Mod (R : Type u) [CommRing R] := Unit65.Mod R

abbrev Comp (R : Type u) [CommRing R] := Unit65.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit65.D R

/-! ## Relative perfectness -/

/-- The source's notion of an `R`-perfect object of `D(A)`.  The flatness and
finite-presentation hypotheses on `f` are hypotheses of the source section;
the predicate itself records pseudo-coherence over `A` and finite Tor
dimension after restriction to `R`. -/
def IsRelativelyPerfect
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (K : D A) : Prop :=
  IsPseudoCoherent A K ∧
    HasFiniteTorDimension R ((derivedRestrictionFunctor f).obj K)

/-- The object property of relatively perfect objects for a fixed flat map of
finite presentation. -/
def relativelyPerfectProperty
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : ObjectProperty (D A) :=
  fun K => IsRelativelyPerfect f K

/-- A bounded complex whose terms are flat over `R` and finitely presented
over `A`, with the displayed derived object as its target. -/
def IsFiniteComplexOfRelativelyFlatFinitelyPresented
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (K : D A) : Prop :=
  ∃ E : Comp A,
    IsBounded E ∧
      (∀ i : ℤ,
        Module.Flat R
            (((ModuleCat.restrictScalars f).obj (E.X i)) : Type u) ∧
          Module.FinitePresentation A (E.X i : Type u)) ∧
      Nonempty ((derivedComplexQuotient A).obj E ≅ K)

/-- The relative-perfect objects form a strictly full, saturated,
triangulated subcategory. -/
theorem relativelyPerfect_is_strictlyFull_saturated_pretriangulated
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hflat : RingHom.Flat f)
    (hfp : RingHom.FinitePresentation f) :
    IsStrictlyFullSaturatedPretriangulated
      (relativelyPerfectProperty f) := by
  sorry

/-! ## Tensor products and finite complexes -/

/-- Perfect objects are relatively perfect, and tensoring a relatively perfect
object by a perfect object preserves relative perfectness. -/
theorem perfect_relativelyPerfect_tensor
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hflat : RingHom.Flat f)
    (hfp : RingHom.FinitePresentation f) (K M : D A) :
    (Perfect A K → IsRelativelyPerfect f K) ∧
      ((Perfect A K ∧ IsRelativelyPerfect f M) →
        IsRelativelyPerfect f (Unit74.derivedTensor K M)) := by
  sorry

/-- Relative perfectness is equivalent to having a finite complex of
`R`-flat, finitely presented `A`-modules. -/
theorem relativelyPerfect_iff_finite_complex
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hflat : RingHom.Flat f)
    (hfp : RingHom.FinitePresentation f) (K : D A) :
    IsRelativelyPerfect f K ↔
      IsFiniteComplexOfRelativelyFlatFinitelyPresented f K := by
  sorry

/-! ## Base change -/

/-- Relative perfectness is preserved by arbitrary base change on the base
ring.  `baseChangeAlgebraMap f g` is the canonical map
`A → A ⊗[R] R'`, and `baseChangeRingMap f g` is the resulting map from `R'`. -/
theorem baseChange_relativelyPerfect
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R')
    (hflat : RingHom.Flat f) (hfp : RingHom.FinitePresentation f)
    (K : D A) (hK : IsRelativelyPerfect f K) :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    IsRelativelyPerfect (baseChangeRingMap f g)
      ((derivedBaseChange (baseChangeAlgebraMap f g)).obj K) := by
  sorry

/-! ## Derived Hom computations -/

/-- The data supplied by the source's computation of derived Hom.  The
complex `homComplex P F` is the source's `Hom^•(P, F)`, and the final field
uses the canonical extension-of-scalars complex for `E ⊗_R R'`. -/
structure RelativelyPerfectRHomComputation
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (K L : D A) where
  P : Unit65.Comp A
  F : Unit65.Comp A
  P_boundedAbove : IsBoundedAbove P
  P_finiteFree : ∀ i : ℤ, Unit65.FiniteFreeModule A (P.X i)
  P_represents : Nonempty ((Unit59.derivedComplexQuotient A).obj P ≅ K)
  F_bounded : IsBounded F
  F_flat : ∀ i : ℤ,
    Module.Flat R (((ModuleCat.restrictScalars f).obj (F.X i)) : Type u)
  F_represents : Nonempty ((Unit59.derivedComplexQuotient A).obj F ≅ L)
  hom_represents :
    Nonempty ((Unit59.derivedComplexQuotient A).obj
      (Unit73.homComplex P F) ≅
      RHom K L)
  hom_boundedBelow : IsBoundedBelow (Unit73.homComplex P F)
  hom_flat : ∀ i : ℤ,
    Module.Flat R (((ModuleCat.restrictScalars f).obj
      ((Unit73.homComplex P F).X i)) : Type u)

/-- The choices in the source lemma can be made so that `Hom^•(P, F)`
represents `RHom_A(K,L)`. -/
theorem exists_relativelyPerfectRHomComputation
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (K L : D A)
    (hK : IsPseudoCoherent A K)
    (hL : HasFiniteTorDimension R ((derivedRestrictionFunctor f).obj L)) :
    Nonempty (RelativelyPerfectRHomComputation f K L) := by
  sorry

/-- Base change of the Hom-complex in the preceding computation computes the
derived Hom after base change. -/
theorem relativelyPerfectRHom_baseChange
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R')
    (K L : D A) (C : RelativelyPerfectRHomComputation f K L) :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Nonempty ((Unit59.derivedComplexQuotient (A ⊗[R] R')).obj
      (baseChangeComplex (baseChangeAlgebraMap f g)
        (Unit73.homComplex C.P C.F)) ≅
      RHom
        ((derivedBaseChange (baseChangeAlgebraMap f g)).obj K)
        ((derivedBaseChange (baseChangeAlgebraMap f g)).obj L)) := by
  sorry

/-- If `L` is relatively perfect over a flat map of finite presentation, the
`F` in the derived-Hom computation may be chosen termwise finitely presented
over `A`; then every term of `Hom^•(P,F)` is finitely presented as well. -/
theorem exists_relativelyPerfectRHomComputation_with_finite_terms
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hflat : RingHom.Flat f)
    (hfp : RingHom.FinitePresentation f) (K L : D A)
    (hK : IsPseudoCoherent A K)
    (hL : IsRelativelyPerfect f L) :
    ∃ C : RelativelyPerfectRHomComputation f K L,
      (∀ i : ℤ, Module.FinitePresentation A (C.F.X i)) ∧
      (∀ i : ℤ, Module.FinitePresentation A
        ((Unit73.homComplex C.P C.F).X i : Type u)) := by
  sorry

/-! ## Filtered colimits -/

/-- A filtered diagram of rings together with a distinguished stage and a
chosen colimit cocone.  This packages the source's `R = colim R_i` data. -/
structure FilteredRingColimitData (I : Type u) [SmallCategory I]
    [IsFiltered I] where
  diagram : I ⥤ CommRingCat.{u}
  colimit : CommRingCat.{u}
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  distinguished : I
  toStage : ∀ i : I, distinguished ⟶ i

/- The algebra instances needed by tensor products are canonically induced by
the two ring maps; hiding them in this abbreviation keeps the colimit
statement readable and agrees with `baseChangeRingMap`. -/
abbrev BaseChangedRing
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R') : Type u :=
  letI : Algebra R A := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  A ⊗[R] R'

/-- The two source assertions for a filtered colimit of relatively perfect
objects and for morphisms between the base-changed objects.  The displayed
Hom equality is represented by an equality of the corresponding `Type`s;
the transition maps and tensor base changes are supplied explicitly by the
chosen colimit cocone. -/
theorem relativelyPerfect_filteredColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (S : FilteredRingColimitData I)
    (A₀ : CommRingCat) (f₀ : S.diagram.obj S.distinguished ⟶ A₀)
    (hflat : RingHom.Flat f₀.hom)
    (hfp : RingHom.FinitePresentation f₀.hom)
    (K : D (BaseChangedRing f₀.hom
      (S.cocone.ι.app S.distinguished).hom))
    (hK : IsRelativelyPerfect
      (baseChangeRingMap f₀.hom
        (S.cocone.ι.app S.distinguished).hom) K)
    (hstage : ∀ i : I,
      BaseChangedRing f₀.hom
        (S.diagram.map (S.toStage i)).hom →+*
        BaseChangedRing f₀.hom (S.cocone.ι.app S.distinguished).hom) :
    ∃ i : I, ∃ Kᵢ : D
        (BaseChangedRing f₀.hom
          (S.diagram.map (S.toStage i)).hom),
      IsRelativelyPerfect (baseChangeRingMap f₀.hom
        (S.diagram.map (S.toStage i)).hom) Kᵢ ∧
        Nonempty (
          (derivedBaseChange (hstage i)).obj Kᵢ ≅
          K) := by
  sorry

/-- The Hom-set component of the filtered-colimit assertion.  `H` is the
canonical diagram whose `i`th object is the Hom-set over `A_i`; the explicit
pointwise identification keeps the statement independent of a particular
presentation of the transition maps in the derived category. -/
theorem relativelyPerfect_filteredColimit_hom
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (S : FilteredRingColimitData I)
    (A₀ : CommRingCat) (f₀ : S.diagram.obj S.distinguished ⟶ A₀)
    (hflat : RingHom.Flat f₀.hom)
    (hfp : RingHom.FinitePresentation f₀.hom)
    (K₀ L₀ : D (A₀ : Type u))
    (hK₀ : IsPseudoCoherent (A₀ : Type u) K₀)
    (hL₀ : HasFiniteTorDimension
      (S.diagram.obj S.distinguished : Type u)
      ((derivedRestrictionFunctor f₀.hom).obj L₀))
    (H : I ⥤ Type (u + 1))
    (hH : ∀ i : I,
      H.obj i =
        ((derivedBaseChange
          (baseChangeAlgebraMap f₀.hom
            (S.diagram.map (S.toStage i)).hom)).obj K₀ ⟶
          (derivedBaseChange
            (baseChangeAlgebraMap f₀.hom
              (S.diagram.map (S.toStage i)).hom)).obj L₀)) :
    ((derivedBaseChange (baseChangeAlgebraMap f₀.hom
      (S.cocone.ι.app S.distinguished).hom)).obj K₀ ⟶
      (derivedBaseChange (baseChangeAlgebraMap f₀.hom
        (S.cocone.ι.app S.distinguished).hom)).obj L₀) =
      colimit H := by
  sorry

/-! ## Nilpotent thickenings -/

/-- Relative perfectness descends across a nilpotent thickening of the base. -/
theorem relativelyPerfect_of_nilpotent_thickening
    {R' A' R : Type u} [CommRing R'] [CommRing A'] [CommRing R]
    (f' : R' →+* A') (g : R' →+* R)
    (hflat : RingHom.Flat f')
    (hfp : RingHom.FinitePresentation f')
    (hsurj : Function.Surjective g)
    (hnil : NilpotentKernel g)
    (K' : D A')
    (hK : IsRelativelyPerfect
      (baseChangeRingMap f' g)
      ((derivedBaseChange (baseChangeAlgebraMap f' g)).obj K')) :
    IsRelativelyPerfect f' K' := by
  sorry

/-! ## Fibrewise Tor amplitude -/

/-- A named quotient type lets the quotient commutative-ring structure be
selected before maps into its localization are elaborated. -/
def PolynomialQuotient
    {R : Type u} [CommRing R] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) R)) : Type u :=
  MvPolynomial (Fin d) R ⧸ I

instance polynomialQuotientCommRing
    {R : Type u} [CommRing R] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) R)) :
    CommRing (PolynomialQuotient d I) := by
  dsimp [PolynomialQuotient]
  exact Ideal.Quotient.commRing I

/-- The canonical map from `R` to an ideal quotient of a finite polynomial
ring. -/
def polynomialQuotientStructureMap
    {R : Type u} [CommRing R] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) R)) :
    R →+* PolynomialQuotient d I :=
  (Ideal.Quotient.mk I).comp (algebraMap R (MvPolynomial (Fin d) R))

abbrev comapResidueField
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (q : PrimeSpectrum A) : Type u :=
  (PrimeSpectrum.comap f q).asIdeal.ResidueField

/- The explicit local instance prevents the quotient's weaker semiring
structure from being selected while forming the localization map. -/
noncomputable def polynomialQuotientLocalizationMap
    {R : Type u} [CommRing R] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) R))
    (q : PrimeSpectrum (PolynomialQuotient d I)) :
    (PolynomialQuotient d I) →+*
      Localization.AtPrime q.asIdeal := by
  exact algebraMap _ _

/-- The fibre object at a prime of the base.  The localized map is the
canonical one from the Tor-dimension chapter, and the residue-field base
change is taken after restriction to the localized base. -/
noncomputable def primeFiberObject
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (K : D A) (q : PrimeSpectrum A) :
    D (PrimeSpectrum.comap f q).asIdeal.ResidueField := by
  let hmap := localizedRingMapData f q
  let e : D (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal) :=
    (derivedRestrictionFunctor hmap.map).obj
      ((derivedBaseChange (algebraMap A (Localization.AtPrime q.asIdeal))).obj K)
  exact (derivedBaseChange
    (IsLocalRing.residue (Localization.AtPrime
      (PrimeSpectrum.comap f q).asIdeal))).obj e

/-- Bounded fibre cohomology gives the stated Tor-amplitude bound at a prime.
The polynomial presentation is expressed by an ideal quotient of a finite
multivariate polynomial ring. -/
theorem torAmplitude_at_primeFiber_of_bounded_cohomology
    {R : Type u} [CommRing R] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) R))
    (hf : RingHom.Flat (polynomialQuotientStructureMap d I))
    (hfp : RingHom.FinitePresentation (polynomialQuotientStructureMap d I))
    (q : PrimeSpectrum (PolynomialQuotient d I))
    (K : D (PolynomialQuotient d I))
    (hK : IsPseudoCoherent (PolynomialQuotient d I) K) (a b : ℤ)
    (hcoh : ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((derivedCohomology
        (comapResidueField (polynomialQuotientStructureMap d I) q) i).obj
        (primeFiberObject (polynomialQuotientStructureMap d I) K q))) :
    TorAmplitude R
      ((derivedRestrictionFunctor
        ((polynomialQuotientLocalizationMap d I q).comp
          (polynomialQuotientStructureMap d I))).obj
        ((derivedBaseChange (polynomialQuotientLocalizationMap d I q)).obj K))
      (a - (d : ℤ)) b := by
  sorry

/-! ## Boundedness on fibres -/

/-- For a flat finitely presented map, a pseudo-coherent object is relatively
perfect exactly when it is bounded below and all of its base fibres are
bounded below. -/
theorem relativelyPerfect_iff_boundedBelow_on_fibres
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hflat : RingHom.Flat f)
    (hfp : RingHom.FinitePresentation f) (K : D A)
    (hK : IsPseudoCoherent A K) :
    IsRelativelyPerfect f K ↔
      IsBoundedBelowDerived A K ∧
        (∀ p : PrimeSpectrum R,
          IsBoundedBelowDerived p.asIdeal.ResidueField
            ((derivedBaseChange (residueFieldMap p)).obj
              ((derivedRestrictionFunctor f).obj K))) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit84
