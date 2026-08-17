import Formalization.Books.Derived.Unit21.CartanEilenbergResolutions

/-!
# Derived Categories, Chapter 22: composition of right derived functors

The canonical comparison of right-derived functors is built from the
universal property of the right-derived functor in Mathlib.  The
Grothendieck spectral sequence is recorded using the filtered-complex
spectral-sequence interface developed in the preceding homological-algebra
chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit07
open Formalization.Books.Homology.Unit24

universe v u v' u' v'' u'' w w' w''

namespace Formalization.Books.Derived.Unit22

/-! ## The canonical comparison map -/

/-- The composite of left exact functors is left exact. -/
theorem isLeftExact_comp
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    {C : Type u''} [Category.{v''} C] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C)
    (hF : IsLeftExact F) (hG : IsLeftExact G) :
    IsLeftExact (F ⋙ G) := by
  let _ : PreservesFiniteLimits F := hF
  let _ : PreservesFiniteLimits G := hG
  change PreservesFiniteLimits (F ⋙ G)
  infer_instance

/- The raw Mathlib functor carries an `Additive` typeclass in its type.  This
wrapper installs the canonical additivity consequence of left exactness so
that the chapter-facing declarations only require the source hypotheses. -/
/-- The canonical right-derived functor attached to a left exact functor. -/
noncomputable def leftExactRightDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) :
    DPlus A ⥤ DPlus B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  exact F.rightDerivedFunctorPlus

/-- The everywhere-defined bounded-below right-derived functor of a composite. -/
noncomputable def rightDerivedCompositionFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [EnoughInjectives B]
    {C : Type u''} [Category.{v''} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  [HasDerivedCategory.{w''} C]
    (F : A ⥤ B) (hF : IsLeftExact F)
    (G : B ⥤ C) (hG : IsLeftExact G) :
    DPlus A ⥤ DPlus C := by
  exact leftExactRightDerivedFunctor F hF ⋙
    leftExactRightDerivedFunctor G hG

/-- The canonical comparison transformation

`R(G ∘ F) ⟶ RF ∘ RG`, with Lean's functor-composition notation written as
`RF ⋙ RG`. -/
noncomputable def rightDerivedCompositionTransformation
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [EnoughInjectives B]
    {C : Type u''} [Category.{v''} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [HasDerivedCategory.{w''} C]
    (F : A ⥤ B) (hF : IsLeftExact F)
    (G : B ⥤ C) (hG : IsLeftExact G) :
    leftExactRightDerivedFunctor (F ⋙ G) (isLeftExact_comp F G hF hG) ⟶
      leftExactRightDerivedFunctor F hF ⋙ leftExactRightDerivedFunctor G hG := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  letI : G.Additive := left_or_right_exact_additive G (Or.inl hG)
  let hFG : IsLeftExact (F ⋙ G) := isLeftExact_comp F G hF hG
  letI : (F ⋙ G).Additive :=
    left_or_right_exact_additive (F ⋙ G) (Or.inl hFG)
  let e : F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ≅
      (F ⋙ G).mapHomotopyCategoryPlus :=
    Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))
  let β : (F ⋙ G).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh (C := C) ⟶
      DerivedCategory.Plus.Qh (C := A) ⋙
        (leftExactRightDerivedFunctor F hF ⋙
          leftExactRightDerivedFunctor G hG) := by
    exact
      Functor.whiskerRight e.inv (DerivedCategory.Plus.Qh (C := C)) ≫
        (Functor.associator F.mapHomotopyCategoryPlus
          G.mapHomotopyCategoryPlus (DerivedCategory.Plus.Qh (C := C))).hom ≫
        Functor.whiskerLeft F.mapHomotopyCategoryPlus
          G.rightDerivedFunctorPlusUnit ≫
        (Functor.associator F.mapHomotopyCategoryPlus
          (DerivedCategory.Plus.Qh (C := B)) G.rightDerivedFunctorPlus).inv ≫
        Functor.whiskerRight F.rightDerivedFunctorPlusUnit
          G.rightDerivedFunctorPlus ≫
        (Functor.associator (DerivedCategory.Plus.Qh (C := A))
          F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus).hom
  exact
    (F ⋙ G).rightDerivedFunctorPlus.rightDerivedDesc
      (F ⋙ G).rightDerivedFunctorPlusUnit
      (quasiIsoPlusProperty A)
      (leftExactRightDerivedFunctor F hF ⋙ leftExactRightDerivedFunctor G hG)
      β

/- The source warns that the comparison need not be invertible.  The precise
criterion for invertibility is the next theorem, so no unsupported universal
counterexample is introduced here. -/

/-- Every image of an injective object under `F` is right acyclic for `G`. -/
def RightAcyclicOnInjectiveImages
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    {C : Type u''} [Category.{v''} C] [Abelian C]
    [HasDerivedCategory.{w''} C]
    (F : A ⥤ B) (G : B ⥤ C) (hG : IsLeftExact G) : Prop := by
  let _ : G.Additive := left_or_right_exact_additive G (Or.inl hG)
  exact ∀ I : A, Injective I → RightAcyclic G (F.obj I)

/-- Grothendieck's acyclicity criterion for the comparison transformation. -/
theorem rightDerivedCompositionTransformation_isIso_iff
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [EnoughInjectives B]
    {C : Type u''} [Category.{v''} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [HasDerivedCategory.{w''} C]
    (F : A ⥤ B) (hF : IsLeftExact F)
    (G : B ⥤ C) (hG : IsLeftExact G) :
    RightAcyclicOnInjectiveImages F G hG ↔
      IsIso (rightDerivedCompositionTransformation F hF G hG) := by
  sorry

/-! ## The Grothendieck spectral sequence -/

/-- The filtered-complex realization of a Grothendieck spectral sequence for
an object of the bounded-below derived category.

The type of `spectralSequence` supplies bigraded pages and differentials of
bidegree `(r, -r + 1)`.  The convergence fields use the existing
filtered-complex notions, while `abutment` identifies the resulting
cohomology objects with the cohomology of `R(G ∘ F)(X)`. -/
structure GrothendieckSpectralSequenceData
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [EnoughInjectives B]
    {C : Type u''} [Category.{v''} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [HasDerivedCategory.{w''} C]
    (F : A ⥤ B) (hF : IsLeftExact F)
    (G : B ⥤ C) (hG : IsLeftExact G)
    (X : DPlus A) (K : FilteredComplex C) where
  /-- The pages and differentials of the spectral sequence. -/
  spectralSequence : FilteredComplexSpectralSequence K
  /-- `E₂^{p,q} = R^pG(H^q(RF(X)))`. -/
  e₂_page : ∀ p q : ℤ,
    Nonempty (spectralSequence.page 2 (p, q) ≅
      (higherRightDerivedFunctor G hG p).obj
        ((DerivedCategory.Plus.homologyFunctor B q).obj
          ((leftExactRightDerivedFunctor F hF).obj X)))
  /-- The spectral sequence is bounded. -/
  bounded : filteredComplexBounded spectralSequence
  /-- The selected spectral sequence converges in the filtered-complex sense. -/
  converges :
    filteredComplexRegular spectralSequence ∧
      filteredComplexAbuts K ∧ FilteredComplexCohomologyComplete K
  /-- Each abutment carries a finite filtration. -/
  finite_filtration : FilteredComplexCohomologyFiniteFiltration K
  /-- The abutment is the cohomology of `R(G ∘ F)(X)`. -/
  abutment : ∀ n : ℤ,
    Nonempty (filteredComplexCohomology K n ≅
      (DerivedCategory.Plus.homologyFunctor C n).obj
        ((rightDerivedCompositionFunctor F hF G hG).obj X))

/-- Existence of the Grothendieck spectral sequence for a bounded-below
derived object under the acyclicity criterion. -/
theorem grothendieckSpectralSequence_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [EnoughInjectives B]
    {C : Type u''} [Category.{v''} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [HasDerivedCategory.{w''} C]
    (F : A ⥤ B) (hF : IsLeftExact F)
    (G : B ⥤ C) (hG : IsLeftExact G)
    (hacyclic : RightAcyclicOnInjectiveImages F G hG)
    (X : DPlus A) :
    ∃ K : FilteredComplex C,
      Nonempty (GrothendieckSpectralSequenceData F hF G hG X K) := by
  sorry

/-- The object-level form of the Grothendieck spectral sequence. -/
structure GrothendieckObjectSpectralSequenceData
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [EnoughInjectives B]
    {C : Type u''} [Category.{v''} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [HasDerivedCategory.{w''} C]
    (F : A ⥤ B) (hF : IsLeftExact F)
    (G : B ⥤ C) (hG : IsLeftExact G)
    (A₀ : A) (K : FilteredComplex C) where
  /-- The pages and differentials of the object-level spectral sequence. -/
  spectralSequence : FilteredComplexSpectralSequence K
  /-- `E₂^{p,q} = R^pG(R^qF(A₀))`. -/
  e₂_page : ∀ p q : ℤ,
    Nonempty (spectralSequence.page 2 (p, q) ≅
      (higherRightDerivedFunctor G hG p).obj
        ((higherRightDerivedFunctor F hF q).obj A₀))
  /-- Boundedness and convergence of the spectral sequence. -/
  bounded : filteredComplexBounded spectralSequence
  converges :
    filteredComplexRegular spectralSequence ∧
      filteredComplexAbuts K ∧ FilteredComplexCohomologyComplete K
  /-- Each abutment carries a finite filtration. -/
  finite_filtration : FilteredComplexCohomologyFiniteFiltration K
  /-- The total-degree abutment is `Rⁿ(G ∘ F)(A₀)`. -/
  abutment : ∀ n : ℤ,
    Nonempty (filteredComplexCohomology K n ≅
      (higherRightDerivedFunctor (F ⋙ G)
        (isLeftExact_comp F G hF hG) n).obj A₀)

/-- The Grothendieck spectral sequence specialized to an object of `A`. -/
theorem grothendieckObjectSpectralSequence_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [EnoughInjectives B]
    {C : Type u''} [Category.{v''} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [HasDerivedCategory.{w''} C]
    (F : A ⥤ B) (hF : IsLeftExact F)
    (G : B ⥤ C) (hG : IsLeftExact G)
    (hacyclic : RightAcyclicOnInjectiveImages F G hG)
    (A₀ : A) :
    ∃ K : FilteredComplex C,
      Nonempty (GrothendieckObjectSpectralSequenceData F hF G hG A₀ K) := by
  sorry

end Formalization.Books.Derived.Unit22
