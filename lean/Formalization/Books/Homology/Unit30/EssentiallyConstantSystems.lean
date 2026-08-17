import Formalization.Books.Categories.Unit22.EssentiallyConstantSystems
import Formalization.Books.Homology.Unit04.KaroubianCategories
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

/-!
# Homological Algebra, Chapter 30: Essentially constant systems

This file records the three statements in the `Essentially constant systems`
section.  The category-theoretic notion of essential constancy is reused from
Categories, Chapter 22.  A direct-sum decomposition is represented by
Mathlib's `BinaryBiproductData`, and a cofinal or initial subcategory is
represented by the canonical full-subcategory inclusion.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit22

universe u v u' v'

namespace Formalization.Books.Homology.Unit30

/-! ## Splittings of essentially constant diagrams -/

/-- The filtered colimit-and-splitting condition in the first part of the
source lemma.  The cocone `c` is the source's object `X = colim M`. -/
def IndColimitSplitting
    {I : Type u} [Category.{v} I]
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    (M : I ⥤ A) : Prop :=
  ∃ (c : Cocone M),
    Nonempty (IsColimit c) ∧
      ∃ (P : ObjectProperty I),
        IsFiltered P.FullSubcategory ∧
          Functor.Final P.ι ∧
            ∀ i' : P.FullSubcategory,
              ∃ (X' Z' : A) (b : BinaryBiproductData X' Z')
                (e : b.bicone.pt ≅ M.obj (P.ι.obj i')),
                IsIso (b.bicone.inl ≫ e.hom ≫ c.ι.app (P.ι.obj i')) ∧
                  ∃ (i'' : P.FullSubcategory) (f : i' ⟶ i''),
                    b.bicone.inr ≫ e.hom ≫ M.map (P.ι.map f) = 0

/-- The cofiltered limit-and-splitting condition in the second part of the
source lemma.  The cone `c` is the source's object `X = lim M`. -/
def ProLimitSplitting
    {I : Type u} [Category.{v} I]
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    (M : I ⥤ A) : Prop :=
  ∃ (c : Cone M),
    Nonempty (IsLimit c) ∧
      ∃ (P : ObjectProperty I),
        IsCofiltered P.FullSubcategory ∧
          Functor.Initial P.ι ∧
            ∀ i' : P.FullSubcategory,
              ∃ (X' Z' : A) (b : BinaryBiproductData X' Z')
                (e : b.bicone.pt ≅ M.obj (P.ι.obj i')),
                IsIso (c.π.app (P.ι.obj i') ≫ e.inv ≫ b.bicone.fst) ∧
                  ∃ (i'' : P.FullSubcategory) (f : i'' ⟶ i'),
                    M.map (P.ι.map f) ≫ e.inv ≫ b.bicone.snd = 0

/-- A filtered essentially constant diagram in a preadditive Karoubian
category is characterized by a colimit and a cofinal filtered splitting. -/
theorem essentiallyConstantInd_iff_indColimitSplitting
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [IsIdempotentComplete A] (M : I ⥤ A) :
    IsEssentiallyConstantIndDiagram M ↔ IndColimitSplitting M := by
  sorry

/-- The dual characterization for cofiltered essentially constant diagrams. -/
theorem essentiallyConstantPro_iff_proLimitSplitting
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [IsIdempotentComplete A] (M : I ⥤ A) :
    IsEssentiallyConstantProDiagram M ↔ ProLimitSplitting M := by
  sorry

/-! ## Colimits and pointwise direct sums -/

/-- The pointwise direct sum of two diagrams in an additive category.

Mathlib exposes the pointwise bicone once binary biproducts are available.
The additive-category interface supplies finite biproducts, from which the
canonical binary-biproduct existence theorem gives the local instance needed
by that construction. -/
def pointwiseDirectSum
    {I : Type u} [Category.{v} I]
    {A : Type u'} [Category.{v'} A]
    [Formalization.Books.Homology.Unit03.AdditiveCategory A]
    (F G : I ⥤ A) : I ⥤ A := by
  letI : HasBinaryBiproducts A :=
    hasBinaryBiproducts_of_finite_biproducts (C := A)
  exact (pointwiseBinaryBiproductData F G).bicone.pt

/-- A colimit of a pointwise binary biproduct exists exactly when the two
component colimits exist. -/
theorem hasColimit_biprod_iff
    {I : Type u} [Category.{v} I]
    {A : Type u'} [Category.{v'} A]
    [Formalization.Books.Homology.Unit03.AdditiveCategory A]
    [IsIdempotentComplete A] (F G : I ⥤ A) :
    HasColimit (pointwiseDirectSum F G) ↔ HasColimit F ∧ HasColimit G := by
  sorry

/-- When they exist, the colimit of a pointwise binary biproduct is the
binary biproduct of the colimits. -/
theorem colimit_biprod_iso
    {I : Type u} [Category.{v} I]
    {A : Type u'} [Category.{v'} A]
    [Formalization.Books.Homology.Unit03.AdditiveCategory A]
    [IsIdempotentComplete A] (F G : I ⥤ A)
    [HasColimit (pointwiseDirectSum F G)] [HasColimit F] [HasColimit G] :
    ∃ (b : BinaryBiproductData (colimit F) (colimit G)),
      Nonempty (colimit (pointwiseDirectSum F G) ≅ b.bicone.pt) := by
  sorry

/-! ## Direct sums of essentially constant systems -/

/-- In a filtered additive Karoubian category, a pointwise direct sum is
essentially constant exactly when both summands are. -/
theorem essentiallyConstantInd_biprod_iff
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {A : Type u'} [Category.{v'} A]
    [Formalization.Books.Homology.Unit03.AdditiveCategory A]
    [IsIdempotentComplete A]
    (F G : I ⥤ A) :
    IsEssentiallyConstantIndDiagram (pointwiseDirectSum F G) ↔
      IsEssentiallyConstantIndDiagram F ∧
        IsEssentiallyConstantIndDiagram G := by
  sorry

end Formalization.Books.Homology.Unit30
