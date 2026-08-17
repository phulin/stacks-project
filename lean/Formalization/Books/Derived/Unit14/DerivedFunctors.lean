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

section DerivedLocalization

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

abbrev rightDerivedRestrictedMorphismProperty :
    MorphismProperty (rightDerivedSubcategory S hS F) :=
  restrictedMorphismProperty S (rightDerivedProperty S hS F)

abbrev leftDerivedRestrictedMorphismProperty :
    MorphismProperty (leftDerivedSubcategory S hS F) :=
  restrictedMorphismProperty S (leftDerivedProperty S hS F)

/-- The restricted denominator system is saturated and compatible with the
triangulation. -/
theorem rightDerivedRestrictedMorphismProperty_properties :
    SaturatedMultiplicativeSystem
        (rightDerivedRestrictedMorphismProperty hS F) ∧
      CompatibleWithTriangulation
        (rightDerivedRestrictedMorphismProperty hS F) := by
  sorry

theorem leftDerivedRestrictedMorphismProperty_properties :
    SaturatedMultiplicativeSystem
        (leftDerivedRestrictedMorphismProperty hS F) ∧
      CompatibleWithTriangulation
        (leftDerivedRestrictedMorphismProperty hS F) := by
  sorry

/-- A denominator in the derived domain is sent to an isomorphism. -/
theorem rightDerivedFunctor_inverts_restricted :
    (rightDerivedRestrictedMorphismProperty hS F).IsInvertedBy
      (rightDerivedFunctor S hS F) := by
  sorry

theorem leftDerivedFunctor_inverts_restricted :
    (leftDerivedRestrictedMorphismProperty hS F).IsInvertedBy
      (leftDerivedFunctor S hS F) := by
  sorry

end DerivedLocalization

end Formalization.Books.Derived.Unit14
