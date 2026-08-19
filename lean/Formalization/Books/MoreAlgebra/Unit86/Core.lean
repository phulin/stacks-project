import Formalization.Books.MoreAlgebra.Unit83
import Formalization.Books.MoreAlgebra.Unit85
import Formalization.Books.Categories.Unit09.Pushouts
import Formalization.Books.Algebra.Unit134.NaiveCotangentComplex
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# More on Algebra, Chapter 86: The naive cotangent complex

This file records the base-change and local-complete-intersection statements
from the chapter.  The derived-category object attached to a ring map and the
comparison maps are supplied by the presentation-independent interface from
the preceding chapter; the small comparison-data structure below exposes the
two maps used by this chapter without introducing a second cotangent complex.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit09
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit75
open Formalization.Books.MoreAlgebra.Unit85
open Formalization.Books.MoreAlgebra.Unit60
open Formalization.Books.MoreAlgebra.Unit83
open scoped TensorProduct

universe w u v

namespace Formalization.Books.MoreAlgebra.Unit86

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit75.D R

abbrev Presentation (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (ι : Type v) :=
  Formalization.Books.Algebra.Unit134.Presentation R S ι

/-! ## The comparison maps used below -/

/- The ordinary tensor product is retained as a separate derived object from
   derived base change.  Its comparison map is the source's canonical map
   `K ⊗ᴸ_R S → K ⊗_R S`. -/
class OrdinaryTensorData
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S) (K : D R) where
  object : D S
  comparison : (derivedBaseChange f).obj K ⟶ object

noncomputable abbrev ordinaryTensorObject
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S) (K : D R) [OrdinaryTensorData f K] : D S :=
  OrdinaryTensorData.object (f := f) (K := K)

noncomputable abbrev ordinaryTensorComparison
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S) (K : D R) [OrdinaryTensorData f K] :
    (derivedBaseChange f).obj K ⟶ ordinaryTensorObject f K :=
  OrdinaryTensorData.comparison (f := f) (K := K)

/- The presentation-independent cotangent construction supplies both the
   ordinary and derived base-change maps into a target cotangent object. -/
class NaiveCotangentComparisonData
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S) (K : D R) (L : D S)
    [OrdinaryTensorData f K] where
  ordinary : ordinaryTensorObject f K ⟶ L
  derived : (derivedBaseChange f).obj K ⟶ L

noncomputable abbrev naiveCotangentOrdinaryComparison
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S) (K : D R) (L : D S)
    [OrdinaryTensorData f K] [NaiveCotangentComparisonData f K L] :
    ordinaryTensorObject f K ⟶ L :=
  NaiveCotangentComparisonData.ordinary (f := f) (K := K) (L := L)

noncomputable abbrev naiveCotangentDerivedComparison
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S) (K : D R) (L : D S)
    [OrdinaryTensorData f K] [NaiveCotangentComparisonData f K L] :
    (derivedBaseChange f).obj K ⟶ L :=
  NaiveCotangentComparisonData.derived (f := f) (K := K) (L := L)

noncomputable def cotangentHomologyMap
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {K L : D R} (φ : K ⟶ L) (i : ℤ) : H R i K ⟶ H R i L :=
  (Unit85.derivedCohomologyFunctor R i).map φ

/- The truncation `τ_{≥ -1}` is expressed by the induced isomorphisms on all
   cohomology objects in degrees at least `-1`; this is the form needed by
   the two-term naive complex. -/
def IsIsoOnCohomologyAtOrAboveMinusOne
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {K L : D R} (φ : K ⟶ L) : Prop :=
  ∀ i : ℤ, (-1 : ℤ) ≤ i → IsIso (cotangentHomologyMap φ i)

def IsIsoOnHZeroAndSurjectiveOnHMinusOne
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {K L : D R} (φ : K ⟶ L) : Prop :=
  IsIso (cotangentHomologyMap φ 0) ∧
    Function.Surjective (cotangentHomologyMap φ (-1)).hom

/- A morphism in the derived category is the source's quasi-isomorphism
   assertion for the represented complexes. -/
abbrev IsDerivedQuasiIso
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {K L : D R} (φ : K ⟶ L) : Prop := IsIso φ

/- A cocartesian square of rings, with the maps named in the orientation used
   in the source. -/
def IsCocartesianRingSquare
    {A B A' B' : Type u} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B']
    (f : A →+* B) (g : A →+* A')
    (p : B →+* B') (q : A' →+* B') : Prop :=
  IsCocartesianSquare (CommRingCat.ofHom f) (CommRingCat.ofHom g)
    (CommRingCat.ofHom p) (CommRingCat.ofHom q)

/-! ## Base change of presentations -/

noncomputable def baseChangedPresentation
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] {ι : Type v}
    (P : Presentation R S ι) :
    Presentation R' (R' ⊗[R] S) ι :=
  Algebra.Generators.baseChange R' P

noncomputable def tensorRightRingHom
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] : S →+* (R' ⊗[R] S) :=
  (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom

abbrev presentationNaiveCotangentObject
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HasDerivedCategory.{w} (Mod S)] (P : Presentation R S v)
    [NaiveCotangentComplexData (algebraMap R S)] : D S :=
  naiveCotangentObject (algebraMap R S)

/-! ## Tensoring and truncation -/

theorem tensor_NL
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    [HasDerivedCategory.{w} (Mod S')]
    (f : R →+* S) (g : S →+* S')
    [NaiveCotangentComplexData f]
    [OrdinaryTensorData g (naiveCotangentObject f)] :
    IsIsoOnCohomologyAtOrAboveMinusOne (ordinaryTensorComparison g
      (naiveCotangentObject f)) := by
  sorry

theorem tensor_NL_presentation
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [HasDerivedCategory.{w} (Mod S)]
    [HasDerivedCategory.{w} (Mod S')]
    (P : Presentation R S v) (g : S →+* S')
    [NaiveCotangentComplexData (algebraMap R S)]
    [OrdinaryTensorData g (presentationNaiveCotangentObject P)] :
    IsIsoOnCohomologyAtOrAboveMinusOne
      (ordinaryTensorComparison g (presentationNaiveCotangentObject P)) := by
  sorry

/-! ## Presentation and intrinsic base change -/

theorem base_change_NL_presentation
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    [HasDerivedCategory.{w} (Mod S)]
    [HasDerivedCategory.{w} (Mod (R' ⊗[R] S))]
    {ι : Type v} (P : Presentation R S ι)
    [NaiveCotangentComplexData (algebraMap R S)]
    [NaiveCotangentComplexData (algebraMap R' (R' ⊗[R] S))]
    [OrdinaryTensorData (tensorRightRingHom (R := R) (S := S) (R' := R'))
      (presentationNaiveCotangentObject P)]
    [NaiveCotangentComparisonData
      (tensorRightRingHom (R := R) (S := S) (R' := R'))
      (presentationNaiveCotangentObject P)
      (presentationNaiveCotangentObject (baseChangedPresentation P))] :
    IsIsoOnHZeroAndSurjectiveOnHMinusOne
      (naiveCotangentOrdinaryComparison
        (tensorRightRingHom (R := R) (S := S) (R' := R'))
        (presentationNaiveCotangentObject P)
        (presentationNaiveCotangentObject (baseChangedPresentation P))) := by
  sorry

theorem base_change_NL
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    [HasDerivedCategory.{w} (Mod S)]
    [HasDerivedCategory.{w} (Mod (R' ⊗[R] S))]
    [NaiveCotangentComplexData (algebraMap R S)]
    [NaiveCotangentComplexData (algebraMap R' (R' ⊗[R] S))]
    [OrdinaryTensorData (tensorRightRingHom (R := R) (S := S) (R' := R'))
      (naiveCotangentObject (algebraMap R S))]
    [NaiveCotangentComparisonData
      (tensorRightRingHom (R := R) (S := S) (R' := R'))
      (naiveCotangentObject (algebraMap R S))
      (naiveCotangentObject (algebraMap R' (R' ⊗[R] S)))] :
    IsIsoOnHZeroAndSurjectiveOnHMinusOne
      (naiveCotangentOrdinaryComparison
        (tensorRightRingHom (R := R) (S := S) (R' := R'))
        (naiveCotangentObject (algebraMap R S))
        (naiveCotangentObject (algebraMap R' (R' ⊗[R] S)))) := by
  sorry

/-! ## Flat base change and local complete intersections -/

theorem base_change_NL_flat
    {A B A' B' : Type u} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B']
    [HasDerivedCategory.{w} (Mod B)] [HasDerivedCategory.{w} (Mod B')]
    (f : A →+* B) (g : A →+* A') (p : B →+* B') (q : A' →+* B')
    (hsquare : IsCocartesianRingSquare f g p q)
    (hflat : RingHom.Flat f)
    [NaiveCotangentComplexData f] [NaiveCotangentComplexData q]
    [OrdinaryTensorData p (naiveCotangentObject f)]
    [NaiveCotangentComparisonData p (naiveCotangentObject f)
      (naiveCotangentObject q)] :
    IsDerivedQuasiIso
      (naiveCotangentOrdinaryComparison p (naiveCotangentObject f)
        (naiveCotangentObject q)) ∧
      (TorAmplitude B (naiveCotangentObject f) (-1) 0 →
        IsDerivedQuasiIso
          (naiveCotangentDerivedComparison p (naiveCotangentObject f)
            (naiveCotangentObject q))) := by
  sorry

theorem lci_NL
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B)
    (hf : IsLocalCompleteIntersectionHom f)
    [NaiveCotangentComplexData f] :
    Perfect B (naiveCotangentObject f) ∧
      TorAmplitude B (naiveCotangentObject f) (-1) 0 := by
  sorry

/- The source's final kernel is the kernel in `Mod_{B'}` of the induced
   degree `-1` homology map. -/
noncomputable def minusOneHomologyKernel
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {K L : D R} (φ : K ⟶ L) : Mod R :=
  kernel (cotangentHomologyMap φ (-1))

theorem base_change_lci_bis
    {A B A' B' : Type u} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B']
    [HasDerivedCategory.{w} (Mod B)] [HasDerivedCategory.{w} (Mod B')]
    (f : A →+* B) (g : A →+* A') (p : B →+* B') (q : A' →+* B')
    (hsquare : IsCocartesianRingSquare f g p q)
    (hf : IsLocalCompleteIntersectionHom f)
    (hq : IsLocalCompleteIntersectionHom q)
    [NaiveCotangentComplexData f] [NaiveCotangentComplexData q]
    [OrdinaryTensorData p (naiveCotangentObject f)]
    [NaiveCotangentComparisonData p (naiveCotangentObject f)
      (naiveCotangentObject q)] :
    FiniteProjectiveModule B'
      (minusOneHomologyKernel
        (naiveCotangentOrdinaryComparison p (naiveCotangentObject f)
          (naiveCotangentObject q))) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit86
