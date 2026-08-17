import Formalization.Books.Categories.Unit27.Localization
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Homological Algebra, Chapter 8: Localization

This file records the statements in the `Localization` section of
*Homological Algebra*.  The calculus-of-fractions declarations from
`Formalization.Books.Categories.Unit27.Localization` and Mathlib's canonical
preadditive localization construction are reused throughout.  In particular,
the common-denominator identities and their duals used in the source proof
are already available as `exists_common_left_denominator`,
`left_fraction_eq_iff_postcomp`, `left_fraction_comp`, and the corresponding
right-fraction declarations.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit27

universe v u

namespace Formalization.Books.Homology.Unit08

/-! ## Preadditive and additive localizations -/

/- Mathlib constructs the canonical structure in the left-calculus case. -/
theorem localization_preadditive_left
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Preadditive C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] [hW : LeftMultiplicativeSystem W] :
    ∃! p : Preadditive D, @Functor.Additive C D _ _ _ p L := by
  refine ⟨CategoryTheory.Localization.preadditive L W, ?_, ?_⟩
  · exact CategoryTheory.Localization.functor_additive L W
  · intro p hp
    sorry

/- The right-calculus statement is the dual part of the source lemma. -/
theorem localization_preadditive_right
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Preadditive C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] (hW : RightMultiplicativeSystem W) :
    ∃! p : Preadditive D, @Functor.Additive C D _ _ _ p L := by
  sorry

theorem localization_preadditive
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Preadditive C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W]
    (hW : LeftMultiplicativeSystem W ∨ RightMultiplicativeSystem W) :
    ∃! p : Preadditive D, @Functor.Additive C D _ _ _ p L := by
  sorry

theorem localization_additive_left
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] [hW : LeftMultiplicativeSystem W] :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      @Functor.Additive C D _ _ _ hD.toPreadditive L := by
  sorry

theorem localization_additive_right
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] [hW : RightMultiplicativeSystem W] :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      @Functor.Additive C D _ _ _ hD.toPreadditive L := by
  sorry

theorem localization_additive
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W]
    (hW : LeftMultiplicativeSystem W ∨ RightMultiplicativeSystem W) :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      @Functor.Additive C D _ _ _ hD.toPreadditive L := by
  sorry

/-! ## The kernel of the localization functor -/

/- `IsZero (L.obj X)` is the canonical categorical formulation of the source's
  assertion `Q(X) = 0`; in an additive category it is equivalent to equality
  with the chosen zero object. -/
theorem localization_zero_iff
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W]
    (hW : MultiplicativeSystem W) (X : C) :
    (IsZero (L.obj X) ↔ ∃ Y : C, W (0 : X ⟶ Y)) ∧
      (IsZero (L.obj X) ↔ ∃ Z : C, W (0 : Z ⟶ X)) := by
  sorry

/-! ## Kernels, cokernels, and exactness -/

/- `PreservesColimit (parallelPair f 0) L` and
  `PreservesLimit (parallelPair f 0) L` express that `L` commutes with the
  corresponding cokernel and kernel, respectively. -/
theorem localization_has_cokernels_of_left
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Abelian C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] (hW : LeftMultiplicativeSystem W) :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      HasCokernels D ∧
        ∀ {X Y : C} (f : X ⟶ Y),
          PreservesColimit (parallelPair f 0) L := by
  sorry

theorem localization_has_kernels_of_right
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Abelian C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] (hW : RightMultiplicativeSystem W) :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      HasKernels D ∧
        ∀ {X Y : C} (f : X ⟶ Y),
          PreservesLimit (parallelPair f 0) L := by
  sorry

theorem localization_is_abelian
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Abelian C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] (hW : MultiplicativeSystem W) :
    ∃ hD : Abelian D, exactFunctor C D L := by
  sorry

end Formalization.Books.Homology.Unit08
