import Formalization.Books.Categories.Unit22.EssentiallyConstantSystems
import Formalization.Books.Categories.Unit27.Localization
import Formalization.Books.Derived.Unit13.FilteredDerivedCategories
import Formalization.Books.Homology.Unit04.KaroubianCategories

/-!
# Derived Categories, Chapter 14: core derived-functor data

The source defines derived functors by taking essentially constant systems over
the left and right denominator categories.  This file exposes those systems,
their chosen values, the canonical maps from and to the original functor, and
the square conditions which characterize the induced maps.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit22
open Formalization.Books.Categories.Unit27
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u'

namespace Formalization.Books.Derived.Unit14

/-! ## The two denominator diagrams -/

/-- The system `X/S ↪ 𝒟 ⥤ 𝒟'` used to define a right derived value. -/
def rightDerivedDiagram
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (F : D ⥤ D') (X : D)
    [LeftMultiplicativeSystem S] :
    LeftDenominatorCategory S X ⥤ D' where
  obj s := F.obj s.right
  map f := F.map f.right
  map_id s := by simp
  map_comp f g := by simp

/-- The system `S/X ↪ 𝒟 ⥤ 𝒟'` used to define a left derived value. -/
def leftDerivedDiagram
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (F : D ⥤ D') (X : D)
    [RightMultiplicativeSystem S] :
    RightDenominatorCategory S X ⥤ D' where
  obj s := F.obj s.left
  map f := F.map f.left
  map_id s := by simp
  map_comp f g := by simp

/-! ## Definedness, values, and canonical comparison maps -/

/-- `RF` is defined at `X` when its denominator diagram is ind-essentially
constant. -/
def rightDerivedDefined
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) : Prop :=
  letI : LeftMultiplicativeSystem S := hS.1.1
  letI : IsFiltered (LeftDenominatorCategory S X) :=
    left_denominator_category_is_filtered X
  IsEssentiallyConstantIndDiagram (rightDerivedDiagram S F X)

/-- `LF` is defined at `X` when its denominator diagram is pro-essentially
constant. -/
def leftDerivedDefined
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) : Prop :=
  letI : RightMultiplicativeSystem S := hS.1.2
  letI : IsCofiltered (RightDenominatorCategory S X) :=
    right_denominator_category_is_cofiltered X
  IsEssentiallyConstantProDiagram (leftDerivedDiagram S F X)

/-- A chosen essentially-constant cocone for a right derived value. -/
noncomputable def rightDerivedCocone
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) (hX : rightDerivedDefined S hS F X)
    [LeftMultiplicativeSystem S] :
    Cocone (rightDerivedDiagram S F X) := by
  letI : IsFiltered (LeftDenominatorCategory S X) :=
    left_denominator_category_is_filtered X
  exact Classical.choose hX

/-- The chosen value of `RF` at an object where it is defined. -/
noncomputable def rightDerivedValue
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) (hX : rightDerivedDefined S hS F X) : D' :=
  letI : LeftMultiplicativeSystem S := hS.1.1
  (rightDerivedCocone S hS F X hX).pt

/-- A chosen essentially-constant cone for a left derived value. -/
noncomputable def leftDerivedCone
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) (hX : leftDerivedDefined S hS F X)
    [RightMultiplicativeSystem S] :
    Cone (leftDerivedDiagram S F X) := by
  letI : IsCofiltered (RightDenominatorCategory S X) :=
    right_denominator_category_is_cofiltered X
  exact Classical.choose hX

/-- The chosen value of `LF` at an object where it is defined. -/
noncomputable def leftDerivedValue
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) (hX : leftDerivedDefined S hS F X) : D' :=
  letI : RightMultiplicativeSystem S := hS.1.2
  (leftDerivedCone S hS F X hX).pt

/-- The identity denominator in `X/S`. -/
noncomputable def rightDerivedIdentityIndex
    {D : Type*} [Category* D] (S : MorphismProperty D)
    (X : D) [LeftMultiplicativeSystem S] :
    LeftDenominatorCategory S X :=
  MorphismProperty.Under.mk (P := S) (Q := (⊤ : MorphismProperty D))
    (X := X) (𝟙 X) (S.id_mem X)

/-- The identity denominator in `S/X`. -/
noncomputable def leftDerivedIdentityIndex
    {D : Type*} [Category* D] (S : MorphismProperty D)
    (X : D) [RightMultiplicativeSystem S] :
    RightDenominatorCategory S X :=
  MorphismProperty.Over.mk (P := S) (Q := (⊤ : MorphismProperty D))
    (𝟙 X) (S.id_mem X)

/-- The canonical map `F(X) ⟶ RF(X)`. -/
noncomputable def rightDerivedCanonicalMap
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) (hX : rightDerivedDefined S hS F X) :
    F.obj X ⟶ rightDerivedValue S hS F X hX := by
  letI : LeftMultiplicativeSystem S := hS.1.1
  let c := rightDerivedCocone S hS F X hX
  simpa [rightDerivedValue, rightDerivedDiagram, rightDerivedIdentityIndex] using
    (F.map (𝟙 X) ≫ c.ι.app (rightDerivedIdentityIndex S X))

/-- The canonical map `LF(X) ⟶ F(X)`. -/
noncomputable def leftDerivedCanonicalMap
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) (hX : leftDerivedDefined S hS F X) :
    leftDerivedValue S hS F X hX ⟶ F.obj X := by
  letI : RightMultiplicativeSystem S := hS.1.2
  let c := leftDerivedCone S hS F X hX
  simpa [leftDerivedValue, leftDerivedDiagram, leftDerivedIdentityIndex] using
    c.π.app (leftDerivedIdentityIndex S X)

/-- The value predicate for `RF`, retaining the cocone and its comparison
isomorphism to the proposed value. -/
def IsRightDerivedValue
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) (Y : D') : Prop := by
  letI : LeftMultiplicativeSystem S := hS.1.1
  letI : IsFiltered (LeftDenominatorCategory S X) :=
    left_denominator_category_is_filtered X
  exact ∃ c : Cocone (rightDerivedDiagram S F X),
    IsEssentiallyConstantInd (rightDerivedDiagram S F X) c ∧
      Nonempty (c.pt ≅ Y)

/-- The value predicate for `LF`, retaining the cone and its comparison
isomorphism to the proposed value. -/
def IsLeftDerivedValue
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) (Y : D') : Prop := by
  letI : RightMultiplicativeSystem S := hS.1.2
  letI : IsCofiltered (RightDenominatorCategory S X) :=
    right_denominator_category_is_cofiltered X
  exact ∃ c : Cone (leftDerivedDiagram S F X),
    IsEssentiallyConstantPro (leftDerivedDiagram S F X) c ∧
      Nonempty (c.pt ≅ Y)

/-! ## Squares and the induced-map conditions -/

/-- A commutative denominator square used by the right derived map. -/
structure RightDerivedSquare
    {D : Type*} [Category* D] (S : MorphismProperty D)
    {X Y : D} (f : X ⟶ Y) [LeftMultiplicativeSystem S] where
  source : LeftDenominatorCategory S X
  target : LeftDenominatorCategory S Y
  dotted : (source.right : D) ⟶ target.right
  comm : source.hom ≫ dotted = f ≫ target.hom

/-- A commutative denominator square used by the left derived map. -/
structure LeftDerivedSquare
    {D : Type*} [Category* D] (S : MorphismProperty D)
    {X Y : D} (f : X ⟶ Y) [RightMultiplicativeSystem S] where
  source : RightDenominatorCategory S X
  target : RightDenominatorCategory S Y
  dotted : (source.left : D) ⟶ target.left
  comm : dotted ≫ target.hom = source.hom ≫ f

/-- The condition characterizing the morphism `RF(f)` between chosen values. -/
def rightDerivedMapCondition
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') {X Y : D} (f : X ⟶ Y)
    (hX : rightDerivedDefined S hS F X)
    (hY : rightDerivedDefined S hS F Y)
    (φ : rightDerivedValue S hS F X hX ⟶
      rightDerivedValue S hS F Y hY) : Prop :=
  letI : LeftMultiplicativeSystem S := hS.1.1
  letI : IsFiltered (LeftDenominatorCategory S X) :=
    left_denominator_category_is_filtered X
  letI : IsFiltered (LeftDenominatorCategory S Y) :=
    left_denominator_category_is_filtered Y
  let cX := rightDerivedCocone S hS F X hX
  let cY := rightDerivedCocone S hS F Y hY
  ∀ q : RightDerivedSquare S f,
    F.map q.dotted ≫ cY.ι.app q.target = cX.ι.app q.source ≫ φ

/-- The condition characterizing the morphism `LF(f)` between chosen values. -/
def leftDerivedMapCondition
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') {X Y : D} (f : X ⟶ Y)
    (hX : leftDerivedDefined S hS F X)
    (hY : leftDerivedDefined S hS F Y)
    (φ : leftDerivedValue S hS F X hX ⟶
      leftDerivedValue S hS F Y hY) : Prop :=
  letI : RightMultiplicativeSystem S := hS.1.2
  letI : IsCofiltered (RightDenominatorCategory S X) :=
    right_denominator_category_is_cofiltered X
  letI : IsCofiltered (RightDenominatorCategory S Y) :=
    right_denominator_category_is_cofiltered Y
  let cX := leftDerivedCone S hS F X hX
  let cY := leftDerivedCone S hS F Y hY
  ∀ q : LeftDerivedSquare S f,
    φ ≫ cY.π.app q.target = cX.π.app q.source ≫ F.map q.dotted

/-! ## Computing objects -/

/-- An object computes `RF` when the canonical map from `F` is an isomorphism. -/
def ComputesRightDerived
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) : Prop :=
  ∃ hX : rightDerivedDefined S hS F X,
    IsIso (rightDerivedCanonicalMap S hS F X hX)

/-- An object computes `LF` when the canonical map to `F` is an isomorphism. -/
def ComputesLeftDerived
    {D D' : Type*} [Category* D] [Category* D']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (X : D) : Prop :=
  ∃ hX : leftDerivedDefined S hS F X,
    IsIso (leftDerivedCanonicalMap S hS F X hX)

end Formalization.Books.Derived.Unit14
