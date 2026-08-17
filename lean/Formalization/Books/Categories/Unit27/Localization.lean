import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Categories, Chapter 27: Localization in categories

This file records the precise definitions and statements in the
`Localization in categories` section of `books/categories.tex`.  Mathlib's
calculus-of-fractions API is used throughout: in particular,
`HasLeftCalculusOfFractions` and `HasRightCalculusOfFractions` are the
canonical bundled forms of the left and right multiplicative-system axioms,
and the canonical localization constructions provide the fraction
categories, their functors, and their universal properties.
-/

namespace Formalization.Books.Categories.Unit27

open CategoryTheory
open CategoryTheory.Limits

universe u v u' v' w

noncomputable section

/-! ## Multiplicative systems -/

/- The LMS and RMS conditions are exactly Mathlib's left and right calculus
   classes.  Those classes extend `MorphismProperty.IsMultiplicative`, whose
   identity and composition fields are LMS1/RMS1, and package the respective
   Ore and cancellation conditions as LMS2/LMS3 or RMS2/RMS3. -/
abbrev LeftMultiplicativeSystem {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) : Prop :=
  W.HasLeftCalculusOfFractions

abbrev RightMultiplicativeSystem {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) : Prop :=
  W.HasRightCalculusOfFractions

abbrev MultiplicativeSystem {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) : Prop :=
  LeftMultiplicativeSystem W ∧ RightMultiplicativeSystem W

/-! ## Left calculus of fractions -/

/- Mathlib's `LeftFraction` is the source's pair `(f, s)`, and
   `LeftFraction.Localization` is the category of equivalence classes of
   such pairs.  Its category instance supplies the source's lemma that the
   displayed equivalence relation and composition make a category. -/
abbrev LeftFractionLocalization {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) :=
  MorphismProperty.LeftFraction.Localization W

abbrev leftLocalizationFunctor {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) [LeftMultiplicativeSystem W] :
    C ⥤ LeftFractionLocalization W :=
  MorphismProperty.LeftFraction.Localization.Q W

/- The book's notation `s⁻¹ f` is represented by the canonical hom induced by
   the corresponding Mathlib left fraction. -/
noncomputable def leftFractionHom {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (leftLocalizationFunctor W).obj X ⟶ (leftLocalizationFunctor W).obj Y :=
  MorphismProperty.LeftFraction.Localization.homMk
    (MorphismProperty.LeftFraction.mk f s hs)

/- The three elementary fraction identities displayed immediately after the
   fraction notation are recorded explicitly. -/
theorem left_fraction_postcompose_denominator {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' Y'' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (t : Y' ⟶ Y'')
    (hs : W s) (ht : W t) :
    leftFractionHom (f ≫ t) (s ≫ t) (W.comp_mem _ _ hs ht) =
      leftFractionHom f s hs := by
  sorry

theorem left_fraction_comp {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y' Z Z' : C} (f : X ⟶ Y') (g : Y' ⟶ Z') (s : Z ⟶ Z')
    (hs : W s) :
    leftFractionHom (f ≫ g) s hs =
      leftFractionHom f (𝟙 Y') (W.id_mem Y') ≫ leftFractionHom g s hs := by
  sorry

theorem left_fraction_change_source {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' Z : C} (f : X ⟶ Y') (s : Y ⟶ Y') (t : Z ⟶ Y) (hs : W s)
    (ht : W t) :
    leftFractionHom f (t ≫ s) (W.comp_mem _ _ ht hs) =
      leftFractionHom f s hs ≫ leftFractionHom (𝟙 Y) t ht := by
  sorry

/- A finite family of localized maps with common target admits a common
   denominator. -/
theorem exists_common_left_denominator {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {ι : Type w} [Finite ι] {X : ι → C} {Y : C}
    (g : ∀ i, (leftLocalizationFunctor W).obj (X i) ⟶
      (leftLocalizationFunctor W).obj Y) :
    ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
      ∀ i, g i = leftFractionHom (f i) s hs := by
  sorry

/- Equality of left fractions with the same denominator has both equivalent
   formulations in the source: an equalizing denominator in `W`, or an
   arbitrary postcomposition whose composite with the denominator lies in
   `W`. -/
theorem left_fraction_eq_iff_postcomp {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' : C} (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (leftFractionHom f s hs = leftFractionHom g s hs) ↔
      ∃ (Y'' : C) (t : Y' ⟶ Y'') (_ : W t), f ≫ t = g ≫ t := by
  sorry

theorem left_fraction_eq_iff_postcomp_of_denominator {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' : C} (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (leftFractionHom f s hs = leftFractionHom g s hs) ↔
      ∃ (Y'' : C) (a : Y' ⟶ Y'') (_ : f ≫ a = g ≫ a), W (s ≫ a) := by
  sorry

theorem left_fraction_postcomp_conditions_iff {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' : C} (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (∃ (Y'' : C) (t : Y' ⟶ Y'') (_ : W t), f ≫ t = g ≫ t) ↔
      ∃ (Y'' : C) (a : Y' ⟶ Y'') (_ : f ≫ a = g ≫ a), W (s ≫ a) := by
  sorry

/- The source's category `Y/S` is the canonical subcategory of `Under Y`
   whose objects have structural morphism in `W`. -/
abbrev LeftDenominatorCategory {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) (Y : C) :=
  MorphismProperty.Under W (⊤ : MorphismProperty C) Y

def leftDenominatorHomDiagram {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) (X Y : C) :
    LeftDenominatorCategory W Y ⥤ Type (max u v) where
  obj s := ULift.{u} (X ⟶ (s.right : C))
  map {s t} a := ↾(fun f : ULift.{u} (X ⟶ s.right) ↦
    ULift.up.{u} (f.down ≫ a.right))
  map_id s := by
    ext f
    cases f
    simp
  map_comp {s t r} a b := by
    ext f
    cases f
    simp [Category.assoc]

noncomputable def leftDenominatorHomColimit {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) (X Y : C) : Type (max u v) :=
  (Types.TypeMax.colimitCocone (leftDenominatorHomDiagram W X Y)).pt

noncomputable def leftDenominatorHomColimit_isColimit {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) (X Y : C) :
    IsColimit (Types.TypeMax.colimitCocone (leftDenominatorHomDiagram W X Y)) :=
  Types.TypeMax.colimitCoconeIsColimit _

theorem left_denominator_category_is_filtered {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W] (Y : C) :
    IsFiltered (LeftDenominatorCategory W Y) := by
  sorry

theorem left_localization_hom_is_filtered_colimit {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    (X Y : C) :
    Nonempty (((leftLocalizationFunctor W).obj X ⟶
      (leftLocalizationFunctor W).obj Y) ≃
      leftDenominatorHomColimit W X Y) := by
  sorry

/- Mathlib's `Q`, `Qiso`, and strict universal property are the source's
   localization functor, its inverses for denominators, and its universal
   factorization. -/
theorem left_localization_inverts {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y : C} (s : X ⟶ Y) (hs : W s) :
    IsIso ((leftLocalizationFunctor W).map s) := by
  exact MorphismProperty.LeftFraction.Localization.StrictUniversalPropertyFixedTarget.inverts
    W s hs

noncomputable def leftLocalizationLift {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {D : Type u'} [Category.{v'} D] (G : C ⥤ D) (hG : W.IsInvertedBy G) :
    LeftFractionLocalization W ⥤ D :=
  MorphismProperty.LeftFraction.Localization.StrictUniversalPropertyFixedTarget.lift G hG

theorem leftLocalizationLift_fac {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {D : Type u'} [Category.{v'} D] (G : C ⥤ D) (hG : W.IsInvertedBy G) :
    leftLocalizationFunctor W ⋙ leftLocalizationLift G hG = G :=
  MorphismProperty.LeftFraction.Localization.StrictUniversalPropertyFixedTarget.fac G hG

theorem leftLocalizationLift_unique {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {D : Type u'} [Category.{v'} D] (G₁ G₂ : LeftFractionLocalization W ⥤ D)
    (h : leftLocalizationFunctor W ⋙ G₁ = leftLocalizationFunctor W ⋙ G₂) :
    G₁ = G₂ :=
  MorphismProperty.LeftFraction.Localization.StrictUniversalPropertyFixedTarget.uniq G₁ G₂ h

theorem left_localization_universal_property {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {D : Type u'} [Category.{v'} D] (G : C ⥤ D) (hG : W.IsInvertedBy G) :
    ∃! H : LeftFractionLocalization W ⥤ D,
      leftLocalizationFunctor W ⋙ H = G := by
  refine ⟨leftLocalizationLift G hG, leftLocalizationLift_fac G hG, ?_⟩
  intro H hH
  exact leftLocalizationLift_unique H (leftLocalizationLift G hG) (hH.trans
    (leftLocalizationLift_fac G hG).symm)

theorem left_localization_preserves_finite_colimits {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [LeftMultiplicativeSystem W] :
    PreservesFiniteColimits (leftLocalizationFunctor W) := by
  sorry

/- The source's square-lifting lemma is stated using the same localization
   functor and the common-denominator fraction notation above. -/
theorem left_localization_lift_square {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : (leftLocalizationFunctor W).obj X ⟶ (leftLocalizationFunctor W).obj X')
    (b : (leftLocalizationFunctor W).obj Y ⟶ (leftLocalizationFunctor W).obj Y')
    (hcomm : (leftLocalizationFunctor W).map f ≫ b =
      a ≫ (leftLocalizationFunctor W).map f') :
    ∃ (X'' Y'' : C) (g : X ⟶ X'') (s : X' ⟶ X'') (h : Y ⟶ Y'')
      (t : Y' ⟶ Y'') (f'' : X'' ⟶ Y'') (hs : W s) (ht : W t),
      g ≫ f'' = f ≫ h ∧ s ≫ f'' = f' ≫ t ∧
        a = leftFractionHom g s hs ∧ b = leftFractionHom h t ht := by
  sorry

/-! ## Right calculus of fractions -/

/- The general Mathlib localization is the canonical common category of right
   fractions.  Right fractions and their maps are supplied by the same
   calculus-of-fractions module, with the opposite-category API proving the
   dual results.  Its category instance supplies the source's lemma that the
   right-fraction relation and composition make a category. -/
abbrev RightFractionLocalization {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) :=
  MorphismProperty.Localization W

abbrev rightLocalizationFunctor {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) : C ⥤ RightFractionLocalization W :=
  MorphismProperty.Q W

noncomputable def rightFractionHom {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} {X X' Y : C} (f : X' ⟶ Y) (s : X' ⟶ X)
    (hs : W s) :
    (rightLocalizationFunctor W).obj X ⟶ (rightLocalizationFunctor W).obj Y :=
  (MorphismProperty.RightFraction.mk s hs f).map
    (rightLocalizationFunctor W) (Localization.inverts _ W)

theorem right_fraction_precompose_denominator {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' X'' Y : C} (f : X' ⟶ Y) (s : X' ⟶ X)
    (t : X'' ⟶ X') (hs : W s) (ht : W t) :
    rightFractionHom (t ≫ f) (t ≫ s) (W.comp_mem _ _ ht hs) =
      rightFractionHom f s hs := by
  sorry

theorem right_fraction_comp {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y Z : C} (f : X' ⟶ Y) (s : X' ⟶ X)
    (g : Y ⟶ Z) (hs : W s) :
    rightFractionHom (f ≫ g) s hs =
      rightFractionHom f s hs ≫ rightFractionHom g (𝟙 Y)
        (W.id_mem Y) := by
  sorry

theorem right_fraction_change_target {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' X'' Y : C} (f : X' ⟶ Y) (s : X' ⟶ X) (t : X ⟶ X'')
    (hs : W s) (ht : W t) :
    rightFractionHom f (s ≫ t) (W.comp_mem _ _ hs ht) =
      rightFractionHom (𝟙 X) t ht ≫ rightFractionHom f s hs := by
  sorry

theorem exists_common_right_denominator {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {ι : Type w} [Finite ι] {Y : ι → C} {X : C}
    (g : ∀ i, (rightLocalizationFunctor W).obj X ⟶
      (rightLocalizationFunctor W).obj (Y i)) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
      ∀ i, g i = rightFractionHom (f i) s hs := by
  sorry

theorem right_fraction_eq_iff_precomp {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y : C} (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    (rightFractionHom f s hs = rightFractionHom g s hs) ↔
      ∃ (X'' : C) (t : X'' ⟶ X') (_ : W t), t ≫ f = t ≫ g := by
  sorry

theorem right_fraction_eq_iff_precomp_of_denominator {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y : C} (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    (rightFractionHom f s hs = rightFractionHom g s hs) ↔
      ∃ (X'' : C) (a : X'' ⟶ X') (_ : a ≫ f = a ≫ g), W (a ≫ s) := by
  sorry

theorem right_fraction_precomp_conditions_iff {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y : C} (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    (∃ (X'' : C) (t : X'' ⟶ X') (_ : W t), t ≫ f = t ≫ g) ↔
      ∃ (X'' : C) (a : X'' ⟶ X') (_ : a ≫ f = a ≫ g), W (a ≫ s) := by
  sorry

abbrev RightDenominatorCategory {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) (X : C) :=
  MorphismProperty.Over W (⊤ : MorphismProperty C) X

def rightDenominatorHomDiagram {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) (X Y : C) :
    (RightDenominatorCategory W X)ᵒᵖ ⥤ Type (max u v) where
  obj s := ULift.{u} ((s.unop.left : C) ⟶ Y)
  map {s t} a := ↾(fun f : ULift.{u} (s.unop.left ⟶ Y) ↦
    ULift.up.{u} (a.unop.left ≫ f.down))
  map_id s := by
    ext f
    cases f
    simp
  map_comp {s t r} a b := by
    ext f
    cases f
    simp [Category.assoc]

noncomputable def rightDenominatorHomColimit {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) (X Y : C) : Type (max u v) :=
  (Types.TypeMax.colimitCocone (rightDenominatorHomDiagram W X Y)).pt

noncomputable def rightDenominatorHomColimit_isColimit {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) (X Y : C) :
    IsColimit (Types.TypeMax.colimitCocone (rightDenominatorHomDiagram W X Y)) :=
  Types.TypeMax.colimitCoconeIsColimit _

theorem right_denominator_category_is_cofiltered {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W] (X : C) :
    IsCofiltered (RightDenominatorCategory W X) := by
  sorry

theorem right_localization_hom_is_filtered_colimit {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [RightMultiplicativeSystem W]
    (X Y : C) :
    Nonempty (((rightLocalizationFunctor W).obj X ⟶
      (rightLocalizationFunctor W).obj Y) ≃
      rightDenominatorHomColimit W X Y) := by
  sorry

theorem right_localization_inverts {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} {X Y : C} (s : X ⟶ Y) (hs : W s) :
    IsIso ((rightLocalizationFunctor W).map s) := by
  exact MorphismProperty.Q_inverts W s hs

noncomputable def rightLocalizationLift {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) (hG : W.IsInvertedBy G) : RightFractionLocalization W ⥤ D :=
  Localization.Construction.lift G hG

theorem rightLocalizationLift_fac {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) (hG : W.IsInvertedBy G) :
    rightLocalizationFunctor W ⋙ rightLocalizationLift G hG = G :=
  Localization.Construction.fac G hG

theorem rightLocalizationLift_unique {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} {D : Type u'} [Category.{v'} D]
    (G₁ G₂ : RightFractionLocalization W ⥤ D)
    (h : rightLocalizationFunctor W ⋙ G₁ = rightLocalizationFunctor W ⋙ G₂) :
    G₁ = G₂ :=
  Localization.Construction.uniq G₁ G₂ h

theorem right_localization_universal_property {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) (hG : W.IsInvertedBy G) :
    ∃! H : RightFractionLocalization W ⥤ D,
      rightLocalizationFunctor W ⋙ H = G := by
  refine ⟨rightLocalizationLift G hG, rightLocalizationLift_fac G hG, ?_⟩
  intro H hH
  exact rightLocalizationLift_unique H (rightLocalizationLift G hG) (hH.trans
    (rightLocalizationLift_fac G hG).symm)

theorem right_localization_preserves_finite_limits {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [RightMultiplicativeSystem W] :
    PreservesFiniteLimits (rightLocalizationFunctor W) := by
  sorry

theorem right_localization_lift_square {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : (rightLocalizationFunctor W).obj X ⟶ (rightLocalizationFunctor W).obj X')
    (b : (rightLocalizationFunctor W).obj Y ⟶ (rightLocalizationFunctor W).obj Y')
    (hcomm : (rightLocalizationFunctor W).map f ≫ b =
      a ≫ (rightLocalizationFunctor W).map f') :
    ∃ (X'' Y'' : C) (s : X'' ⟶ X) (t : Y'' ⟶ Y)
      (g : X'' ⟶ X') (h : Y'' ⟶ Y') (f'' : X'' ⟶ Y'') (hs : W s) (ht : W t),
      s ≫ f = f'' ≫ t ∧ f'' ≫ h = g ≫ f' ∧
        a = rightFractionHom g s hs ∧ b = rightFractionHom h t ht := by
  sorry

/-! ## Two-sided calculus and saturation -/

noncomputable def twoSidedLocalizationEquivalence {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    [RightMultiplicativeSystem W] (_hW : MultiplicativeSystem W) :
    LeftFractionLocalization W ≌ RightFractionLocalization W := by
  exact Localization.uniq (leftLocalizationFunctor W) (rightLocalizationFunctor W) W

/- MS4 is the extra middle-composite condition in the source. -/
def SaturatedMultiplicativeSystem {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) : Prop :=
  MultiplicativeSystem W ∧
    ∀ ⦃X Y Z T : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
      W (f ≫ g) → W (g ≫ h) → W g

theorem saturated_contains_isomorphisms {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} (hW : SaturatedMultiplicativeSystem W) :
    MorphismProperty.isomorphisms C ≤ W := by
  sorry

theorem isIso_of_adjacent_composites {C : Type u} [Category.{v} C]
    {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsIso (f ≫ g)] [IsIso (g ≫ h)] : IsIso g := by
  sorry

/- `invertedByLocalization` is the source's set `\hat S`, expressed as a
   morphism property in the original category. -/
def invertedByLocalization {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) : MorphismProperty C :=
  (MorphismProperty.isomorphisms (MorphismProperty.Localization W)).inverseImage
    (MorphismProperty.Q W)

/- `saturationClosure` is the source's set `S'` of arrows admitting a
   `W`-arrow on both sides. -/
def saturationClosure {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) : MorphismProperty C :=
  fun {X Y} f =>
    ∃ (Z : C) (g : Z ⟶ X) (T : C) (h : Y ⟶ T),
      W (g ≫ f) ∧ W (f ≫ h)

theorem invertedByLocalization_eq_saturationClosure {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} (hW : MultiplicativeSystem W) :
    invertedByLocalization W = saturationClosure W := by
  sorry

theorem saturationClosure_is_smallest {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} (hW : MultiplicativeSystem W) :
    W ≤ saturationClosure W ∧
      SaturatedMultiplicativeSystem (saturationClosure W) ∧
      ∀ V : MorphismProperty C, SaturatedMultiplicativeSystem V → W ≤ V →
        saturationClosure W ≤ V := by
  sorry

theorem invertedByLocalization_eq_of_saturated {C : Type u}
    [Category.{v} C] {W : MorphismProperty C}
    (hW : SaturatedMultiplicativeSystem W) :
    invertedByLocalization W = W := by
  sorry

end

end Formalization.Books.Categories.Unit27
