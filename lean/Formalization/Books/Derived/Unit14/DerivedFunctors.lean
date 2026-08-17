import Formalization.Books.Derived.Unit14.Core
import Formalization.Books.Derived.Unit06.Quotients

/-!
# Derived Categories, Chapter 14: derived-functor interfaces

This file records the theorem interfaces in the source section.  The
essentially-constant constructions and their comparison maps are defined in
`Core`; the results below retain the source hypotheses and its right/left
duality.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit22
open Formalization.Books.Categories.Unit27
open Formalization.Books.Derived.Unit05
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit14
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w

namespace Formalization.Books.Derived.Unit14

/-! ## Induced maps, inversion, and shifts -/

section InducedMaps

variable {D D' : Type*} [Category* D] [Category* D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  (F : D ⥤ D')

/-- The induced map between chosen right derived values exists uniquely and is
characterized by every commutative denominator square. -/
theorem rightDerivedMap_exists_unique
    {X Y : D} (f : X ⟶ Y)
    (hX : rightDerivedDefined S hS F X)
    (hY : rightDerivedDefined S hS F Y) :
    ∃! φ : rightDerivedValue S hS F X hX ⟶
        rightDerivedValue S hS F Y hY,
      rightDerivedMapCondition S hS F f hX hY φ := by
  sorry

/-- A chosen induced map `RF(f)`. -/
noncomputable def rightDerivedMap
    {X Y : D} (f : X ⟶ Y)
    (hX : rightDerivedDefined S hS F X)
    (hY : rightDerivedDefined S hS F Y) :
    rightDerivedValue S hS F X hX ⟶ rightDerivedValue S hS F Y hY :=
  Classical.choose (rightDerivedMap_exists_unique hS F f hX hY)

theorem rightDerivedMap_condition
    {X Y : D} (f : X ⟶ Y)
    (hX : rightDerivedDefined S hS F X)
    (hY : rightDerivedDefined S hS F Y) :
      rightDerivedMapCondition S hS F f hX hY
      (rightDerivedMap hS F f hX hY) := by
  exact (Classical.choose_spec (rightDerivedMap_exists_unique hS F f hX hY)).1

/-- The left-derived version of the induced-map construction. -/
theorem leftDerivedMap_exists_unique
    {X Y : D} (f : X ⟶ Y)
    (hX : leftDerivedDefined S hS F X)
    (hY : leftDerivedDefined S hS F Y) :
    ∃! φ : leftDerivedValue S hS F X hX ⟶
        leftDerivedValue S hS F Y hY,
      leftDerivedMapCondition S hS F f hX hY φ := by
  sorry

noncomputable def leftDerivedMap
    {X Y : D} (f : X ⟶ Y)
    (hX : leftDerivedDefined S hS F X)
    (hY : leftDerivedDefined S hS F Y) :
    leftDerivedValue S hS F X hX ⟶ leftDerivedValue S hS F Y hY :=
  Classical.choose (leftDerivedMap_exists_unique hS F f hX hY)

theorem leftDerivedMap_condition
    {X Y : D} (f : X ⟶ Y)
    (hX : leftDerivedDefined S hS F X)
    (hY : leftDerivedDefined S hS F Y) :
      leftDerivedMapCondition S hS F f hX hY
      (leftDerivedMap hS F f hX hY) := by
  exact (Classical.choose_spec (leftDerivedMap_exists_unique hS F f hX hY)).1

/-- Definedness is invariant under a denominator. -/
theorem rightDerived_defined_iff_of_mem
    {X Y : D} (s : X ⟶ Y) (hs : S s) :
    rightDerivedDefined S hS F X ↔ rightDerivedDefined S hS F Y := by
  sorry

theorem leftDerived_defined_iff_of_mem
    {X Y : D} (s : X ⟶ Y) (hs : S s) :
    leftDerivedDefined S hS F X ↔ leftDerivedDefined S hS F Y := by
  sorry

/-- The induced map of a denominator is an isomorphism. -/
theorem rightDerived_map_isIso_of_mem
    {X Y : D} (s : X ⟶ Y) (hs : S s)
    (hX : rightDerivedDefined S hS F X)
    (hY : rightDerivedDefined S hS F Y) :
    IsIso (rightDerivedMap hS F s hX hY) := by
  sorry

theorem leftDerived_map_isIso_of_mem
    {X Y : D} (s : X ⟶ Y) (hs : S s)
    (hX : leftDerivedDefined S hS F X)
    (hY : leftDerivedDefined S hS F Y) :
    IsIso (leftDerivedMap hS F s hX hY) := by
  sorry

end InducedMaps

section ExactSituation

variable {D D' : Type*} [Category* D] [Category* D']
  [Preadditive D] [Preadditive D'] [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  [CompatibleWithTriangulation S]
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/-- Definedness is invariant under shifts. -/
theorem rightDerived_defined_iff_shift
    (X : D) (n : ℤ) :
    rightDerivedDefined S hS F X ↔
      rightDerivedDefined S hS F ((shiftFunctor D n).obj X) := by
  sorry

theorem leftDerived_defined_iff_shift
    (X : D) (n : ℤ) :
    leftDerivedDefined S hS F X ↔
      leftDerivedDefined S hS F ((shiftFunctor D n).obj X) := by
  sorry

theorem rightDerived_shift_iso_exists
    (X : D) (n : ℤ)
    (hX : rightDerivedDefined S hS F X)
    (hXn : rightDerivedDefined S hS F ((shiftFunctor D n).obj X)) :
    Nonempty
      ((shiftFunctor D' n).obj (rightDerivedValue S hS F X hX) ≅
        rightDerivedValue S hS F ((shiftFunctor D n).obj X) hXn) := by
  sorry

noncomputable def rightDerivedShiftIso
    (X : D) (n : ℤ)
    (hX : rightDerivedDefined S hS F X)
    (hXn : rightDerivedDefined S hS F ((shiftFunctor D n).obj X)) :
    (shiftFunctor D' n).obj (rightDerivedValue S hS F X hX) ≅
      rightDerivedValue S hS F ((shiftFunctor D n).obj X) hXn :=
  Classical.choice (rightDerived_shift_iso_exists hS F X n hX hXn)

theorem leftDerived_shift_iso_exists
    (X : D) (n : ℤ)
    (hX : leftDerivedDefined S hS F X)
    (hXn : leftDerivedDefined S hS F ((shiftFunctor D n).obj X)) :
    Nonempty
      ((shiftFunctor D' n).obj (leftDerivedValue S hS F X hX) ≅
        leftDerivedValue S hS F ((shiftFunctor D n).obj X) hXn) := by
  sorry

noncomputable def leftDerivedShiftIso
    (X : D) (n : ℤ)
    (hX : leftDerivedDefined S hS F X)
    (hXn : leftDerivedDefined S hS F ((shiftFunctor D n).obj X)) :
    (shiftFunctor D' n).obj (leftDerivedValue S hS F X hX) ≅
      leftDerivedValue S hS F ((shiftFunctor D n).obj X) hXn :=
  Classical.choice (leftDerived_shift_iso_exists hS F X n hX hXn)

/-! ## Two-out-of-three and direct sums -/

noncomputable def rightDerivedTriangle
    (T : Triangle D)
    (h₁ : rightDerivedDefined S hS F T.obj₁)
    (h₂ : rightDerivedDefined S hS F T.obj₂)
    (h₃ : rightDerivedDefined S hS F T.obj₃) : Triangle D' :=
  let h₁' : rightDerivedDefined S hS F
      ((shiftFunctor D (1 : ℤ)).obj T.obj₁) :=
    (rightDerived_defined_iff_shift hS F T.obj₁ (1 : ℤ)).mp h₁
  Triangle.mk
    (rightDerivedMap hS F T.mor₁ h₁ h₂)
    (rightDerivedMap hS F T.mor₂ h₂ h₃)
    (rightDerivedMap hS F T.mor₃ h₃ h₁' ≫
      (rightDerivedShiftIso hS F T.obj₁ (1 : ℤ) h₁ h₁').inv)

noncomputable def leftDerivedTriangle
    (T : Triangle D)
    (h₁ : leftDerivedDefined S hS F T.obj₁)
    (h₂ : leftDerivedDefined S hS F T.obj₂)
    (h₃ : leftDerivedDefined S hS F T.obj₃) : Triangle D' :=
  let h₁' : leftDerivedDefined S hS F
      ((shiftFunctor D (1 : ℤ)).obj T.obj₁) :=
    (leftDerived_defined_iff_shift hS F T.obj₁ (1 : ℤ)).mp h₁
  Triangle.mk
    (leftDerivedMap hS F T.mor₁ h₁ h₂)
    (leftDerivedMap hS F T.mor₂ h₂ h₃)
    (leftDerivedMap hS F T.mor₃ h₃ h₁' ≫
      (leftDerivedShiftIso hS F T.obj₁ (1 : ℤ) h₁ h₁').inv)

theorem rightDerived_two_out_of_three
    (T : Triangle D) (hT : T ∈ distTriang D) :
    ((h₁₂ : rightDerivedDefined S hS F T.obj₁ ∧
        rightDerivedDefined S hS F T.obj₂) →
      ∃ h₃ : rightDerivedDefined S hS F T.obj₃,
        rightDerivedTriangle hS F T h₁₂.1 h₁₂.2 h₃ ∈ distTriang D') ∧
    ((h₂₃ : rightDerivedDefined S hS F T.obj₂ ∧
        rightDerivedDefined S hS F T.obj₃) →
      ∃ h₁ : rightDerivedDefined S hS F T.obj₁,
        rightDerivedTriangle hS F T h₁ h₂₃.1 h₂₃.2 ∈ distTriang D') ∧
    ((h₃₁ : rightDerivedDefined S hS F T.obj₃ ∧
        rightDerivedDefined S hS F T.obj₁) →
      ∃ h₂ : rightDerivedDefined S hS F T.obj₂,
        rightDerivedTriangle hS F T h₃₁.2 h₂ h₃₁.1 ∈ distTriang D') := by
  sorry

theorem leftDerived_two_out_of_three
    (T : Triangle D) (hT : T ∈ distTriang D) :
    ((h₁₂ : leftDerivedDefined S hS F T.obj₁ ∧
        leftDerivedDefined S hS F T.obj₂) →
      ∃ h₃ : leftDerivedDefined S hS F T.obj₃,
        leftDerivedTriangle hS F T h₁₂.1 h₁₂.2 h₃ ∈ distTriang D') ∧
    ((h₂₃ : leftDerivedDefined S hS F T.obj₂ ∧
        leftDerivedDefined S hS F T.obj₃) →
      ∃ h₁ : leftDerivedDefined S hS F T.obj₁,
        leftDerivedTriangle hS F T h₁ h₂₃.1 h₂₃.2 ∈ distTriang D') ∧
    ((h₃₁ : leftDerivedDefined S hS F T.obj₃ ∧
        leftDerivedDefined S hS F T.obj₁) →
      ∃ h₂ : leftDerivedDefined S hS F T.obj₂,
        leftDerivedTriangle hS F T h₃₁.2 h₂ h₃₁.1 ∈ distTriang D') := by
  sorry

theorem rightDerived_biproduct_defined_of_defined
    [HasBinaryBiproducts D] [HasBinaryBiproducts D']
    (X Y : D) (hX : rightDerivedDefined S hS F X)
    (hY : rightDerivedDefined S hS F Y) :
    rightDerivedDefined S hS F (X ⊞ Y) := by
  sorry

theorem leftDerived_biproduct_defined_of_defined
    [HasBinaryBiproducts D] [HasBinaryBiproducts D']
    (X Y : D) (hX : leftDerivedDefined S hS F X)
    (hY : leftDerivedDefined S hS F Y) :
    leftDerivedDefined S hS F (X ⊞ Y) := by
  sorry

theorem rightDerived_biproduct_defined_iff
    [HasBinaryBiproducts D] [HasBinaryBiproducts D']
    [IsIdempotentComplete D'] (X Y : D) :
    rightDerivedDefined S hS F (X ⊞ Y) ↔
      rightDerivedDefined S hS F X ∧ rightDerivedDefined S hS F Y := by
  sorry

theorem leftDerived_biproduct_defined_iff
    [HasBinaryBiproducts D] [HasBinaryBiproducts D']
    [IsIdempotentComplete D'] (X Y : D) :
    leftDerivedDefined S hS F (X ⊞ Y) ↔
      leftDerivedDefined S hS F X ∧ leftDerivedDefined S hS F Y := by
  sorry

theorem rightDerived_biproduct_iso
    [HasBinaryBiproducts D] [HasBinaryBiproducts D']
    (X Y : D)
    (hX : rightDerivedDefined S hS F X)
    (hY : rightDerivedDefined S hS F Y)
    (hXY : rightDerivedDefined S hS F (X ⊞ Y)) :
    Nonempty
      (rightDerivedValue S hS F (X ⊞ Y) hXY ≅
        rightDerivedValue S hS F X hX ⊞ rightDerivedValue S hS F Y hY) := by
  sorry

theorem leftDerived_biproduct_iso
    [HasBinaryBiproducts D] [HasBinaryBiproducts D']
    (X Y : D)
    (hX : leftDerivedDefined S hS F X)
    (hY : leftDerivedDefined S hS F Y)
    (hXY : leftDerivedDefined S hS F (X ⊞ Y)) :
    Nonempty
      (leftDerivedValue S hS F (X ⊞ Y) hXY ≅
        leftDerivedValue S hS F X hX ⊞ leftDerivedValue S hS F Y hY) := by
  sorry

end ExactSituation

/-! ## The derived-functor subcategories -/

section DerivedSubcategory

variable {D D' : Type*} [Category* D] [Category* D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  (F : D ⥤ D')

/-- `F` is right derivable when `RF` is defined at every object. -/
def RightDerivable (S : MorphismProperty D)
    (hS : SaturatedMultiplicativeSystem S) (F : D ⥤ D') : Prop :=
  ∀ X : D, rightDerivedDefined S hS F X

/-- `F` is left derivable when `LF` is defined at every object. -/
def LeftDerivable (S : MorphismProperty D)
    (hS : SaturatedMultiplicativeSystem S) (F : D ⥤ D') : Prop :=
  ∀ X : D, leftDerivedDefined S hS F X

/-- The strictly full subcategory on which the right derived functor is
defined. -/
def rightDerivedProperty (S : MorphismProperty D)
    (hS : SaturatedMultiplicativeSystem S) (F : D ⥤ D') : ObjectProperty D :=
  fun X => rightDerivedDefined S hS F X

/-- The strictly full subcategory on which the left derived functor is
defined. -/
def leftDerivedProperty (S : MorphismProperty D)
    (hS : SaturatedMultiplicativeSystem S) (F : D ⥤ D') : ObjectProperty D :=
  fun X => leftDerivedDefined S hS F X

abbrev rightDerivedSubcategory (S : MorphismProperty D)
    (hS : SaturatedMultiplicativeSystem S) (F : D ⥤ D') : Type _ :=
  (rightDerivedProperty S hS F).FullSubcategory

abbrev leftDerivedSubcategory (S : MorphismProperty D)
    (hS : SaturatedMultiplicativeSystem S) (F : D ⥤ D') : Type _ :=
  (leftDerivedProperty S hS F).FullSubcategory

/-- The chosen right derived functor on its domain of definition. -/
noncomputable def rightDerivedFunctor (S : MorphismProperty D)
    (hS : SaturatedMultiplicativeSystem S) (F : D ⥤ D') :
    rightDerivedSubcategory S hS F ⥤ D' where
  obj X := rightDerivedValue S hS F X.obj X.property
  map {X Y} f := rightDerivedMap hS F f.hom X.property Y.property
  map_id := by sorry
  map_comp := by sorry

/-- The chosen left derived functor on its domain of definition. -/
noncomputable def leftDerivedFunctor (S : MorphismProperty D)
    (hS : SaturatedMultiplicativeSystem S) (F : D ⥤ D') :
    leftDerivedSubcategory S hS F ⥤ D' where
  obj X := leftDerivedValue S hS F X.obj X.property
  map {X Y} f := leftDerivedMap hS F f.hom X.property Y.property
  map_id := by sorry
  map_comp := by sorry

end DerivedSubcategory

section DerivedSubcategoryExact

variable {D D' : Type*} [Category* D] [Category* D']
  [Preadditive D] [Preadditive D'] [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  [CompatibleWithTriangulation S]
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/-- The right-derived domain is a strictly full triangulated subcategory. -/
theorem rightDerivedProperty_isTriangulated :
    (rightDerivedProperty S hS F).IsClosedUnderIsomorphisms ∧
      (rightDerivedProperty S hS F).IsTriangulated := by
  sorry

/-- The left-derived domain is a strictly full triangulated subcategory. -/
theorem leftDerivedProperty_isTriangulated :
    (leftDerivedProperty S hS F).IsClosedUnderIsomorphisms ∧
      (leftDerivedProperty S hS F).IsTriangulated := by
  sorry

/-- A denominator with one endpoint in the right-derived domain has both
endpoints in that domain. -/
theorem rightDerived_property_of_mem_of_source_or_target
    {X Y : D} (s : X ⟶ Y) (hs : S s) :
    (rightDerivedProperty S hS F X ∨ rightDerivedProperty S hS F Y) →
      rightDerivedProperty S hS F X ∧ rightDerivedProperty S hS F Y := by
  sorry

theorem leftDerived_property_of_mem_of_source_or_target
    {X Y : D} (s : X ⟶ Y) (hs : S s) :
    (leftDerivedProperty S hS F X ∨ leftDerivedProperty S hS F Y) →
      leftDerivedProperty S hS F X ∧ leftDerivedProperty S hS F Y := by
  sorry

/-- Exactness for a functor whose source is a full subcategory: the
triangulated structure on that subcategory is supplied by the object
property. -/
def IsExactOnObjectPropertySubcategory
    {C E : Type*} [Category* C] [Category* E]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive E] [HasZeroObject E] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (P : ObjectProperty C) (G : P.FullSubcategory ⥤ E) : Prop :=
  ∃ hP : P.IsTriangulated,
    letI : P.IsTriangulated := hP
    ∃ hG : G.CommShift ℤ,
      letI : G.CommShift ℤ := hG
      G.IsTriangulated

/-- The right-derived functor is exact on its domain. -/
theorem rightDerivedFunctor_isExact :
    IsExactOnObjectPropertySubcategory
      (rightDerivedProperty S hS F) (rightDerivedFunctor S hS F) := by
  sorry

/-- The left-derived functor is exact on its domain. -/
theorem leftDerivedFunctor_isExact :
    IsExactOnObjectPropertySubcategory
      (leftDerivedProperty S hS F) (leftDerivedFunctor S hS F) := by
  sorry

end DerivedSubcategoryExact

/-! ## Localization of the derived domain -/

section DerivedRestrictedProperties

variable {D D' : Type*} [Category* D] [Category* D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  (F : D ⥤ D')

abbrev rightDerivedRestrictedMorphismProperty :
    MorphismProperty (rightDerivedSubcategory S hS F) :=
  restrictedMorphismProperty S (rightDerivedProperty S hS F)

abbrev leftDerivedRestrictedMorphismProperty :
    MorphismProperty (leftDerivedSubcategory S hS F) :=
  restrictedMorphismProperty S (leftDerivedProperty S hS F)

end DerivedRestrictedProperties

section RightDerivedRestrictedProperties

variable {D D' : Type*} [Category* D] [Category* D']
  [Preadditive D] [Preadditive D'] [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  [CompatibleWithTriangulation S]
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
  [(rightDerivedProperty S hS F).IsTriangulated]

/-- The restricted right-derived denominator system is saturated and
compatible with the triangulation. -/
theorem rightDerivedRestrictedMorphismProperty_properties :
    SaturatedMultiplicativeSystem
        (rightDerivedRestrictedMorphismProperty hS F) ∧
      CompatibleWithTriangulation
        (rightDerivedRestrictedMorphismProperty hS F) := by
  sorry

/-- A denominator in the right-derived domain is sent to an isomorphism. -/
theorem rightDerivedFunctor_inverts_restricted :
    (rightDerivedRestrictedMorphismProperty hS F).IsInvertedBy
      (rightDerivedFunctor S hS F) := by
  sorry

end RightDerivedRestrictedProperties

section LeftDerivedRestrictedProperties

variable {D D' : Type*} [Category* D] [Category* D']
  [Preadditive D] [Preadditive D'] [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  [CompatibleWithTriangulation S]
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
  [(leftDerivedProperty S hS F).IsTriangulated]

theorem leftDerivedRestrictedMorphismProperty_properties :
    SaturatedMultiplicativeSystem
        (leftDerivedRestrictedMorphismProperty hS F) ∧
      CompatibleWithTriangulation
        (leftDerivedRestrictedMorphismProperty hS F) := by
  sorry

theorem leftDerivedFunctor_inverts_restricted :
    (leftDerivedRestrictedMorphismProperty hS F).IsInvertedBy
      (leftDerivedFunctor S hS F) := by
  sorry

end LeftDerivedRestrictedProperties

section RightDerivedLocalization

variable {D D' : Type*} [Category* D] [Category* D']
  [Preadditive D] [Preadditive D'] [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  [LeftMultiplicativeSystem S] [RightMultiplicativeSystem S]
  [CompatibleWithTriangulation S]
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
  [(rightDerivedProperty S hS F).IsTriangulated]
  [LeftMultiplicativeSystem
    (restrictedMorphismProperty S (rightDerivedProperty S hS F))]
  [RightMultiplicativeSystem
    (restrictedMorphismProperty S (rightDerivedProperty S hS F))]
  [CompatibleWithTriangulation
    (restrictedMorphismProperty S (rightDerivedProperty S hS F))]

/-! ## The right-derived localization -/

noncomputable def rightDerivedLocalizationEmbedding :
    (rightDerivedRestrictedMorphismProperty hS F).Localization ⥤
      S.Localization :=
  fullSubcategoryLocalizationFunctor S (rightDerivedProperty S hS F)

/-- The localization of the right-derived domain embeds fully faithfully and
exactly into the localization of the ambient category. -/
theorem rightDerivedLocalizationEmbedding_fullyFaithful_exact :
    (rightDerivedLocalizationEmbedding hS F).Full ∧
      (rightDerivedLocalizationEmbedding hS F).Faithful ∧
        IsExactLocalizationFactor
          (S := rightDerivedRestrictedMorphismProperty hS F)
          (rightDerivedLocalizationEmbedding hS F) := by
  sorry

noncomputable def rightDerivedLocalizedFunctor :
    (rightDerivedRestrictedMorphismProperty hS F).Localization ⥤ D' :=
  localizationFactor (S := rightDerivedRestrictedMorphismProperty hS F)
    (rightDerivedFunctor S hS F)
    (rightDerivedFunctor_inverts_restricted hS F)

theorem rightDerivedLocalizedFunctor_isExact :
    IsExactLocalizationFactor
      (S := rightDerivedRestrictedMorphismProperty hS F)
      (rightDerivedLocalizedFunctor hS F) := by
  sorry

end RightDerivedLocalization

section LeftDerivedLocalization

variable {D D' : Type*} [Category* D] [Category* D']
  [Preadditive D] [Preadditive D'] [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  [LeftMultiplicativeSystem S] [RightMultiplicativeSystem S]
  [CompatibleWithTriangulation S]
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
  [(leftDerivedProperty S hS F).IsTriangulated]
  [LeftMultiplicativeSystem
    (restrictedMorphismProperty S (leftDerivedProperty S hS F))]
  [RightMultiplicativeSystem
    (restrictedMorphismProperty S (leftDerivedProperty S hS F))]
  [CompatibleWithTriangulation
    (restrictedMorphismProperty S (leftDerivedProperty S hS F))]

/-! ## The left-derived localization -/

noncomputable def leftDerivedLocalizationEmbedding :
    (leftDerivedRestrictedMorphismProperty hS F).Localization ⥤
      S.Localization :=
  fullSubcategoryLocalizationFunctor S (leftDerivedProperty S hS F)

theorem leftDerivedLocalizationEmbedding_fullyFaithful_exact :
    (leftDerivedLocalizationEmbedding hS F).Full ∧
      (leftDerivedLocalizationEmbedding hS F).Faithful ∧
        IsExactLocalizationFactor
          (S := leftDerivedRestrictedMorphismProperty hS F)
          (leftDerivedLocalizationEmbedding hS F) := by
  sorry

noncomputable def leftDerivedLocalizedFunctor :
    (leftDerivedRestrictedMorphismProperty hS F).Localization ⥤ D' :=
  localizationFactor (S := leftDerivedRestrictedMorphismProperty hS F)
    (leftDerivedFunctor S hS F)
    (leftDerivedFunctor_inverts_restricted hS F)

theorem leftDerivedLocalizedFunctor_isExact :
    IsExactLocalizationFactor
      (S := leftDerivedRestrictedMorphismProperty hS F)
      (leftDerivedLocalizedFunctor hS F) := by
  sorry

end LeftDerivedLocalization

/-! ## Saturation of the derived domain -/

section DerivedSaturation

variable {D D' : Type*} [Category* D] [Category* D']
  [AdditiveCategory D]
  [Preadditive D'] [HasZeroObject D'] [HasBinaryBiproducts D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  [CompatibleWithTriangulation S]
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
  [IsIdempotentComplete D']

/-- If the target is Karoubian, the right-derived domain is saturated. -/
theorem rightDerivedProperty_isSaturated :
    Formalization.Books.Derived.Unit06.IsSaturated
      (rightDerivedProperty S hS F) := by
  sorry

theorem leftDerivedProperty_isSaturated :
    Formalization.Books.Derived.Unit06.IsSaturated
      (leftDerivedProperty S hS F) := by
  sorry

theorem rightDerivedProperty_isStrictlyFullSaturatedPretriangulated :
    Formalization.Books.Derived.Unit06.IsStrictlyFullSaturatedPretriangulated
      (rightDerivedProperty S hS F) := by
  sorry

theorem leftDerivedProperty_isStrictlyFullSaturatedPretriangulated :
    Formalization.Books.Derived.Unit06.IsStrictlyFullSaturatedPretriangulated
      (leftDerivedProperty S hS F) := by
  sorry

end DerivedSaturation

/-! ## Everywhere-defined functors and computing objects -/

section EverywhereDefined

variable {D D' : Type*} [Category* D] [Category* D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  (F : D ⥤ D')

/-- The right-derived functor on all of `D`, once defined everywhere. -/
noncomputable def rightDerivedEverywhereFunctor
    (hF : RightDerivable S hS F) : D ⥤ D' where
  obj X := rightDerivedValue S hS F X (hF X)
  map {X Y} f := rightDerivedMap hS F f (hF X) (hF Y)
  map_id := by sorry
  map_comp := by sorry

/-- The left-derived functor on all of `D`, once defined everywhere. -/
noncomputable def leftDerivedEverywhereFunctor
    (hF : LeftDerivable S hS F) : D ⥤ D' where
  obj X := leftDerivedValue S hS F X (hF X)
  map {X Y} f := leftDerivedMap hS F f (hF X) (hF Y)
  map_id := by sorry
  map_comp := by sorry

theorem rightDerivedEverywhereFunctor_inverts
    (hF : RightDerivable S hS F) :
    S.IsInvertedBy (rightDerivedEverywhereFunctor hS F hF) := by
  sorry

theorem leftDerivedEverywhereFunctor_inverts
    (hF : LeftDerivable S hS F) :
    S.IsInvertedBy (leftDerivedEverywhereFunctor hS F hF) := by
  sorry

end EverywhereDefined

section EverywhereLocalizationAndComputes

variable {D D' : Type*} [Category* D] [Category* D']
  [Preadditive D] [Preadditive D'] [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  {S : MorphismProperty D} (hS : SaturatedMultiplicativeSystem S)
  [LeftMultiplicativeSystem S] [RightMultiplicativeSystem S]
  [CompatibleWithTriangulation S]
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/-- The everywhere-defined right-derived functor on the localization. -/
noncomputable def rightDerivedEverywhereLocalizedFunctor
    (hF : RightDerivable S hS F) : S.Localization ⥤ D' :=
  localizationFactor (S := S)
    (rightDerivedEverywhereFunctor hS F hF)
    (rightDerivedEverywhereFunctor_inverts hS F hF)

/-- The everywhere-defined left-derived functor on the localization. -/
noncomputable def leftDerivedEverywhereLocalizedFunctor
    (hF : LeftDerivable S hS F) : S.Localization ⥤ D' :=
  localizationFactor (S := S)
    (leftDerivedEverywhereFunctor hS F hF)
    (leftDerivedEverywhereFunctor_inverts hS F hF)

theorem rightDerivedEverywhereLocalizedFunctor_isExact
    (hF : RightDerivable S hS F) :
    IsExactLocalizationFactor
      (S := S) (rightDerivedEverywhereLocalizedFunctor hS F hF) := by
  sorry

theorem leftDerivedEverywhereLocalizedFunctor_isExact
    (hF : LeftDerivable S hS F) :
    IsExactLocalizationFactor
      (S := S) (leftDerivedEverywhereLocalizedFunctor hS F hF) := by
  sorry

/-! ## Computing lemmas -/

theorem rightDerived_computes_iff_shift
    (X : D) (n : ℤ) :
    ComputesRightDerived S hS F X ↔
      ComputesRightDerived S hS F ((shiftFunctor D n).obj X) := by
  sorry

theorem leftDerived_computes_iff_shift
    (X : D) (n : ℤ) :
    ComputesLeftDerived S hS F X ↔
      ComputesLeftDerived S hS F ((shiftFunctor D n).obj X) := by
  sorry

theorem rightDerived_two_out_of_three_computes
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : ComputesRightDerived S hS F T.obj₁)
    (h₂ : ComputesRightDerived S hS F T.obj₂) :
    ComputesRightDerived S hS F T.obj₃ := by
  sorry

theorem leftDerived_two_out_of_three_computes
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : ComputesLeftDerived S hS F T.obj₁)
    (h₂ : ComputesLeftDerived S hS F T.obj₂) :
    ComputesLeftDerived S hS F T.obj₃ := by
  sorry

theorem rightDerived_biproduct_computes
    [HasBinaryBiproducts D] [HasBinaryBiproducts D']
    (X Y : D) :
    ComputesRightDerived S hS F (X ⊞ Y) →
      ComputesRightDerived S hS F X ∧ ComputesRightDerived S hS F Y := by
  sorry

theorem leftDerived_biproduct_computes
    [HasBinaryBiproducts D] [HasBinaryBiproducts D']
    (X Y : D) :
    ComputesLeftDerived S hS F (X ⊞ Y) →
      ComputesLeftDerived S hS F X ∧ ComputesLeftDerived S hS F Y := by
  sorry

theorem rightDerived_everywhere_of_computing_replacements
    (h : ∀ X : D, ∃ X' : D, ∃ s : X ⟶ X',
      S s ∧ ComputesRightDerived S hS F X') :
    RightDerivable S hS F := by
  sorry

theorem leftDerived_everywhere_of_computing_replacements
    (h : ∀ X : D, ∃ X' : D, ∃ s : X' ⟶ X,
      S s ∧ ComputesLeftDerived S hS F X') :
    LeftDerivable S hS F := by
  sorry

end EverywhereLocalizationAndComputes

section ComputingFamilies

variable {D D' : Type*} [Category* D] [Category* D']
  {S : MorphismProperty D} (F : D ⥤ D')

/-- A right-computing family is cofinal for `X/S` and is stable under
denominators after applying `F`. -/
def RightComputingFamily (S : MorphismProperty D) (F : D ⥤ D')
    (I : Set D) : Prop :=
  (∀ X : D, ∃ X' : D, ∃ s : X ⟶ X', I X' ∧ S s) ∧
    (∀ ⦃X X' : D⦄ (s : X ⟶ X'), I X → I X' → S s →
      IsIso (F.map s))

/-- A left-computing family is coinitial for `S/X` and is stable under
denominators after applying `F`. -/
def LeftComputingFamily (S : MorphismProperty D) (F : D ⥤ D')
    (I : Set D) : Prop :=
  (∀ X : D, ∃ X' : D, ∃ s : X' ⟶ X, I X' ∧ S s) ∧
    (∀ ⦃X X' : D⦄ (s : X ⟶ X'), I X → I X' → S s →
      IsIso (F.map s))

theorem rightDerived_everywhere_and_computes_of_family
    (hS : SaturatedMultiplicativeSystem S) (I : Set D)
    (hI : RightComputingFamily S F I) :
    RightDerivable S hS F ∧
      ∀ X : D, I X → ComputesRightDerived S hS F X := by
  sorry

theorem leftDerived_everywhere_and_computes_of_family
    (hS : SaturatedMultiplicativeSystem S) (I : Set D)
    (hI : LeftComputingFamily S F I) :
    LeftDerivable S hS F ∧
      ∀ X : D, I X → ComputesLeftDerived S hS F X := by
  sorry

end ComputingFamilies

/-! ## Composition of derived functors -/

section Composition

variable {A B C : Type*}
  [Category* A] [Category* B] [Category* C]
  [Preadditive A] [Preadditive B] [Preadditive C]
  [HasZeroObject A] [HasZeroObject B] [HasZeroObject C]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor A n).Additive]
  [∀ n : ℤ, (shiftFunctor B n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated A] [Pretriangulated B] [Pretriangulated C]
  [CategoryTheory.IsTriangulated A]
  [CategoryTheory.IsTriangulated B]
  [CategoryTheory.IsTriangulated C]
  {S : MorphismProperty A} (hS : SaturatedMultiplicativeSystem S)
  {S' : MorphismProperty B} (hS' : SaturatedMultiplicativeSystem S')
  [LeftMultiplicativeSystem S] [RightMultiplicativeSystem S]
  [CompatibleWithTriangulation S]
  [LeftMultiplicativeSystem S'] [RightMultiplicativeSystem S']
  [CompatibleWithTriangulation S']
  (F : A ⥤ B) (G : B ⥤ C)
  [F.CommShift ℤ] [F.IsTriangulated]
  [G.CommShift ℤ] [G.IsTriangulated]

/-- The functor called `F'` in the composition lemma. -/
noncomputable def localizedFunctor : A ⥤ S'.Localization :=
  F ⋙ S'.Q

theorem rightDerived_composition_transformation
    (hF' : RightDerivable S hS (localizedFunctor F))
    (hG : RightDerivable S' hS' G)
    (hGF : RightDerivable S hS (F ⋙ G)) :
    Nonempty
      (NatTrans
        (rightDerivedEverywhereLocalizedFunctor hS (F ⋙ G) hGF)
        ((rightDerivedEverywhereLocalizedFunctor hS
            (localizedFunctor F) hF') ⋙
          rightDerivedEverywhereLocalizedFunctor hS' G hG)) := by
  sorry

noncomputable def rightDerivedCompositionTransformation
    (hF' : RightDerivable S hS (localizedFunctor F))
    (hG : RightDerivable S' hS' G)
    (hGF : RightDerivable S hS (F ⋙ G)) :
    NatTrans
      (rightDerivedEverywhereLocalizedFunctor hS (F ⋙ G) hGF)
      ((rightDerivedEverywhereLocalizedFunctor hS
          (localizedFunctor F) hF') ⋙
        rightDerivedEverywhereLocalizedFunctor hS' G hG) :=
  Classical.choice (rightDerived_composition_transformation
    hS hS' F G hF' hG hGF)

theorem leftDerived_composition_transformation
    (hF' : LeftDerivable S hS (localizedFunctor F))
    (hG : LeftDerivable S' hS' G)
    (hGF : LeftDerivable S hS (F ⋙ G)) :
    Nonempty
      (NatTrans
        ((leftDerivedEverywhereLocalizedFunctor hS
            (localizedFunctor F) hF') ⋙
          leftDerivedEverywhereLocalizedFunctor hS' G hG)
        (leftDerivedEverywhereLocalizedFunctor hS (F ⋙ G) hGF)) := by
  sorry

noncomputable def leftDerivedCompositionTransformation
    (hF' : LeftDerivable S hS (localizedFunctor F))
    (hG : LeftDerivable S' hS' G)
    (hGF : LeftDerivable S hS (F ⋙ G)) :
    NatTrans
      ((leftDerivedEverywhereLocalizedFunctor hS
          (localizedFunctor F) hF') ⋙
        leftDerivedEverywhereLocalizedFunctor hS' G hG)
      (leftDerivedEverywhereLocalizedFunctor hS (F ⋙ G) hGF) :=
  Classical.choice (leftDerived_composition_transformation
    hS hS' F G hF' hG hGF)

end Composition

end Formalization.Books.Derived.Unit14
