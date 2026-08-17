import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
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
  apply MorphismProperty.LeftFraction.Localization.homMk_eq_of_leftFractionRel
  exact ⟨Y'', 𝟙 _, t, by simp, by simp, by simpa using W.comp_mem _ _ hs ht⟩

private theorem left_fraction_postcompose_denominator_of_composite {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' Y'' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (t : Y' ⟶ Y'')
    (hs : W s) (hcomp : W (s ≫ t)) :
    leftFractionHom (f ≫ t) (s ≫ t) hcomp = leftFractionHom f s hs := by
  apply MorphismProperty.LeftFraction.Localization.homMk_eq_of_leftFractionRel
  exact ⟨Y'', 𝟙 _, t, by simp, by simp, by simpa using hcomp⟩

private theorem left_denominator_category_is_filtered_aux {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W] (Y : C) :
    IsFiltered (MorphismProperty.Under W (⊤ : MorphismProperty C) Y) := by
  have hne : Nonempty (MorphismProperty.Under W (⊤ : MorphismProperty C) Y) :=
    ⟨MorphismProperty.Under.mk (P := W) (Q := (⊤ : MorphismProperty C)) (X := Y)
      (𝟙 Y) (W.id_mem Y)⟩
  have hfiltered : IsFilteredOrEmpty (MorphismProperty.Under W
      (⊤ : MorphismProperty C) Y) := by
    refine ⟨?_, ?_⟩
    · intro j k
      obtain ⟨φ, hφ⟩ :=
        (MorphismProperty.RightFraction.mk j.hom j.prop k.hom).exists_leftFraction
      let z : MorphismProperty.Under W (⊤ : MorphismProperty C) Y :=
        MorphismProperty.Under.mk (P := W) (Q := (⊤ : MorphismProperty C)) (X := Y)
          (k.hom ≫ φ.s) (W.comp_mem _ _ k.prop φ.hs)
      exact ⟨z, MorphismProperty.Under.homMk φ.f hφ.symm,
        MorphismProperty.Under.homMk φ.s rfl, trivial⟩
    · intro j k f g
      obtain ⟨Z, t, ht, hfg⟩ :=
        MorphismProperty.HasLeftCalculusOfFractions.ext f.right g.right j.hom j.prop
          (by rw [MorphismProperty.Under.w f, MorphismProperty.Under.w g])
      let z : MorphismProperty.Under W (⊤ : MorphismProperty C) Y :=
        MorphismProperty.Under.mk (P := W) (Q := (⊤ : MorphismProperty C)) (X := Y)
          (k.hom ≫ t) (W.comp_mem _ _ k.prop ht)
      refine ⟨z, MorphismProperty.Under.homMk t rfl, ?_⟩
      apply MorphismProperty.Under.Hom.ext
      change f.right ≫ t = g.right ≫ t
      exact hfg
  exact { toIsFilteredOrEmpty := hfiltered, nonempty := hne }

theorem left_fraction_comp {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y' Z Z' : C} (f : X ⟶ Y') (g : Y' ⟶ Z') (s : Z ⟶ Z')
    (hs : W s) :
    leftFractionHom (f ≫ g) s hs =
      leftFractionHom f (𝟙 Y') (W.id_mem Y') ≫ leftFractionHom g s hs := by
  unfold leftFractionHom
  symm
  rw [MorphismProperty.LeftFraction.Localization.homMk_comp_homMk
    (W := W)
    (MorphismProperty.LeftFraction.mk f (𝟙 Y') (W.id_mem Y'))
    (MorphismProperty.LeftFraction.mk g s hs)
    (MorphismProperty.LeftFraction.mk g (𝟙 Z') (W.id_mem Z')) (by simp)]
  simp [MorphismProperty.LeftFraction.comp₀]

private theorem left_fraction_factor {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (leftLocalizationFunctor W).map f ≫
        leftFractionHom (𝟙 Y') s hs = leftFractionHom f s hs := by
  unfold leftFractionHom
  change (MorphismProperty.LeftFraction.Localization.Q W).map f ≫
      MorphismProperty.LeftFraction.Localization.Qinv s hs =
    MorphismProperty.LeftFraction.Localization.homMk
      (MorphismProperty.LeftFraction.mk f s hs)
  exact MorphismProperty.LeftFraction.Localization.Q_map_comp_Qinv f s hs

private theorem left_fraction_precompose_numerator {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X X' Y Y' : C} (a : X ⟶ X') (f : X' ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (leftLocalizationFunctor W).map a ≫ leftFractionHom f s hs =
      leftFractionHom (a ≫ f) s hs := by
  simpa [leftFractionHom, MorphismProperty.LeftFraction.Localization.Q_map,
    MorphismProperty.LeftFraction.ofHom] using
    (left_fraction_comp a f s hs).symm

theorem left_fraction_change_source {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' Z : C} (f : X ⟶ Y') (s : Y ⟶ Y') (t : Z ⟶ Y) (hs : W s)
    (ht : W t) :
    leftFractionHom f (t ≫ s) (W.comp_mem _ _ ht hs) =
      leftFractionHom f s hs ≫ leftFractionHom (𝟙 Y) t ht := by
  unfold leftFractionHom
  symm
  convert (MorphismProperty.LeftFraction.Localization.homMk_comp_homMk
    (W := W)
    (MorphismProperty.LeftFraction.mk f s hs)
    (MorphismProperty.LeftFraction.mk (𝟙 Y) t ht)
    (MorphismProperty.LeftFraction.mk (𝟙 Y') s hs) (by simp)) using 1
  simp [MorphismProperty.LeftFraction.comp₀]

/- A finite family of localized maps with common target admits a common
   denominator. -/
theorem exists_common_left_denominator {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {ι : Type w} [Finite ι] {X : ι → C} {Y : C}
    (g : ∀ i, (leftLocalizationFunctor W).obj (X i) ⟶
      (leftLocalizationFunctor W).obj Y) :
    ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
      ∀ i, g i = leftFractionHom (f i) s hs := by
  have hfiltered : IsFiltered (MorphismProperty.Under W (⊤ : MorphismProperty C) Y) :=
    left_denominator_category_is_filtered_aux Y
  classical
  let hι : Fintype ι := Fintype.ofFinite ι
  let hcat : FinCategory (Discrete ι) :=
    @CategoryTheory.finCategoryDiscreteOfFintype ι hι
  choose φ hφ using fun i =>
    CategoryTheory.Localization.exists_leftFraction
      (leftLocalizationFunctor W) W (g i)
  let d : ι → MorphismProperty.Under W (⊤ : MorphismProperty C) Y := fun i =>
    MorphismProperty.Under.mk (P := W) (Q := (⊤ : MorphismProperty C)) (X := Y)
      (φ i).s (φ i).hs
  obtain ⟨c⟩ := @IsFiltered.cocone_nonempty _ _ hfiltered _ _ hcat (Discrete.functor d)
  let s : Y ⟶ (c.pt.right : C) := c.pt.hom
  have hs : W s := c.pt.prop
  refine ⟨c.pt.right, s, hs,
    (fun i => (φ i).f ≫ (c.ι.app (Discrete.mk i)).right), ?_⟩
  intro i
  have hgi : g i = leftFractionHom (φ i).f (φ i).s (φ i).hs := by
    exact (hφ i).trans (MorphismProperty.LeftFraction.Localization.homMk_eq (φ i)).symm
  calc
    g i = leftFractionHom (φ i).f (φ i).s (φ i).hs := hgi
    _ = leftFractionHom ((φ i).f ≫ (c.ι.app (Discrete.mk i)).right)
        ((φ i).s ≫ (c.ι.app (Discrete.mk i)).right)
        (by
          have hden : (φ i).s ≫ (c.ι.app (Discrete.mk i)).right = s := by
            change (φ i).s ≫ (c.ι.app (Discrete.mk i)).right = c.pt.hom
            exact MorphismProperty.Under.w (c.ι.app (Discrete.mk i))
          rw [hden]
          exact hs) := by
      symm
      apply (left_fraction_postcompose_denominator_of_composite
        (φ i).f (φ i).s (c.ι.app (Discrete.mk i)).right (φ i).hs)
    _ = leftFractionHom ((φ i).f ≫ (c.ι.app (Discrete.mk i)).right) s hs := by
      have hden : (φ i).s ≫ (c.ι.app (Discrete.mk i)).right = s := by
        change (φ i).s ≫ (c.ι.app (Discrete.mk i)).right = c.pt.hom
        exact MorphismProperty.Under.w (c.ι.app (Discrete.mk i))
      simp [hden]

/- Equality of left fractions with the same denominator has both equivalent
   formulations in the source: an equalizing denominator in `W`, or an
   arbitrary postcomposition whose composite with the denominator lies in
   `W`. -/
theorem left_fraction_eq_iff_postcomp {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' : C} (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (leftFractionHom f s hs = leftFractionHom g s hs) ↔
      ∃ (Y'' : C) (t : Y' ⟶ Y'') (_ : W t), f ≫ t = g ≫ t := by
  constructor
  · intro h
    unfold leftFractionHom at h
    rw [← MorphismProperty.LeftFraction.Localization.Q_map_comp_Qinv f s hs,
      ← MorphismProperty.LeftFraction.Localization.Q_map_comp_Qinv g s hs] at h
    have hmap : (MorphismProperty.LeftFraction.Localization.Q W).map f =
        (MorphismProperty.LeftFraction.Localization.Q W).map g := by
      exact (cancel_mono (MorphismProperty.LeftFraction.Localization.Qinv s hs)).1 h
    exact (MorphismProperty.map_eq_iff_postcomp
      (L := leftLocalizationFunctor W) (W := W) f g).1 hmap
  · rintro ⟨Y'', t, ht, hfg⟩
    have hmap := (MorphismProperty.map_eq_iff_postcomp
      (L := leftLocalizationFunctor W) (W := W) f g).2 ⟨Y'', t, ht, hfg⟩
    unfold leftFractionHom
    rw [← MorphismProperty.LeftFraction.Localization.Q_map_comp_Qinv f s hs,
      ← MorphismProperty.LeftFraction.Localization.Q_map_comp_Qinv g s hs, hmap]

theorem left_fraction_eq_iff_postcomp_of_denominator {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' : C} (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (leftFractionHom f s hs = leftFractionHom g s hs) ↔
      ∃ (Y'' : C) (a : Y' ⟶ Y'') (_ : f ≫ a = g ≫ a), W (s ≫ a) := by
  constructor
  · intro h
    obtain ⟨Y'', t, ht, hfg⟩ := (left_fraction_eq_iff_postcomp f g s hs).1 h
    exact ⟨Y'', t, hfg, W.comp_mem _ _ hs ht⟩
  · rintro ⟨Y'', a, hfg, ha⟩
    unfold leftFractionHom
    apply MorphismProperty.LeftFraction.Localization.homMk_eq_of_leftFractionRel
    exact ⟨Y'', a, a, by simp, hfg, ha⟩

theorem left_fraction_postcomp_conditions_iff {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X Y Y' : C} (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (∃ (Y'' : C) (t : Y' ⟶ Y'') (_ : W t), f ≫ t = g ≫ t) ↔
      ∃ (Y'' : C) (a : Y' ⟶ Y'') (_ : f ≫ a = g ≫ a), W (s ≫ a) := by
  constructor
  · rintro ⟨Y'', t, ht, hfg⟩
    exact ⟨Y'', t, hfg, W.comp_mem _ _ hs ht⟩
  · rintro ⟨Y'', a, hfg, ha⟩
    obtain ⟨Z, t, ht, hfg'⟩ :=
      (left_fraction_eq_iff_postcomp f g s hs).1
        ((left_fraction_eq_iff_postcomp_of_denominator f g s hs).2
          ⟨Y'', a, hfg, ha⟩)
    exact ⟨Z, t, ht, hfg'⟩

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
  exact left_denominator_category_is_filtered_aux Y

theorem left_localization_hom_is_filtered_colimit {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    (X Y : C) :
    Nonempty (((leftLocalizationFunctor W).obj X ⟶
      (leftLocalizationFunctor W).obj Y) ≃
      leftDenominatorHomColimit W X Y) := by
  let c₀ := Types.TypeMax.colimitCocone (leftDenominatorHomDiagram W X Y)
  let fracCocone : Cocone (leftDenominatorHomDiagram W X Y) :=
    { pt := (leftLocalizationFunctor W).obj X ⟶ (leftLocalizationFunctor W).obj Y
      ι :=
        { app := fun d => ↾(fun z : ULift.{u} (X ⟶ (d.right : C)) =>
            leftFractionHom z.down d.hom d.prop)
          naturality := by
            intro d e a
            ext z
            cases z
            change leftFractionHom (_ ≫ a.right) e.hom e.prop =
              leftFractionHom _ d.hom d.prop
            have hden : d.hom ≫ a.right = e.hom :=
              MorphismProperty.Under.w a
            have hcomp : W (d.hom ≫ a.right) := by
              rw [hden]
              exact e.prop
            simpa [hden] using
              (left_fraction_postcompose_denominator_of_composite
                _ d.hom a.right d.prop hcomp) } }
  have hfrac : IsColimit fracCocone := by
    apply Types.FilteredColimit.isColimitOf (leftDenominatorHomDiagram W X Y) fracCocone
    · intro h
      obtain ⟨z, rfl⟩ :=
        MorphismProperty.LeftFraction.Localization.Hom.mk_surjective h
      refine ⟨MorphismProperty.Under.mk (P := W) (Q := (⊤ : MorphismProperty C))
        (X := Y) z.s z.hs, ULift.up z.f, ?_⟩
      rfl
    · intro d e z₁ z₂ h
      change leftFractionHom z₁.down d.hom d.prop =
        leftFractionHom z₂.down e.hom e.prop at h
      unfold leftFractionHom at h
      obtain ⟨Z, a, b, hst, hfg, hW⟩ :=
        (MorphismProperty.LeftFraction.Localization.homMk_eq_iff_leftFractionRel
          (MorphismProperty.LeftFraction.mk z₁.down d.hom d.prop)
          (MorphismProperty.LeftFraction.mk z₂.down e.hom e.prop)).1 h
      let k : LeftDenominatorCategory W Y :=
        MorphismProperty.Under.mk (P := W) (Q := (⊤ : MorphismProperty C)) (X := Y)
          (d.hom ≫ a) hW
      refine ⟨k, MorphismProperty.Under.homMk a rfl,
        MorphismProperty.Under.homMk b hst.symm, ?_⟩
      change ULift.up (z₁.down ≫ a) = ULift.up (z₂.down ≫ b)
      exact congrArg ULift.up hfg
  refine ⟨(IsColimit.coconePointUniqueUpToIso
    (leftDenominatorHomColimit_isColimit W X Y) hfrac).toEquiv.symm⟩

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
  have : RepresentablyCoflat (leftLocalizationFunctor W) :=
    { filtered := fun Z => by
        let Y : C := Z
        change IsFiltered (CostructuredArrow (leftLocalizationFunctor W)
          ((leftLocalizationFunctor W).obj Y))
        have hne : Nonempty (CostructuredArrow (leftLocalizationFunctor W)
            ((leftLocalizationFunctor W).obj Y)) :=
          ⟨CostructuredArrow.mk (𝟙 ((leftLocalizationFunctor W).obj Y))⟩
        have hfiltered : IsFilteredOrEmpty
            (CostructuredArrow (leftLocalizationFunctor W) ((leftLocalizationFunctor W).obj Y)) := by
          refine ⟨?_, ?_⟩
          · intro j k
            let X₂ : Bool → C := fun b =>
              match b with
              | false => j.left
              | true => k.left
            let g₂ : ∀ b, (leftLocalizationFunctor W).obj (X₂ b) ⟶
                (leftLocalizationFunctor W).obj Y := fun b =>
              match b with
              | false => j.hom
              | true => k.hom
            obtain ⟨Y', s, hs, f, hf⟩ :=
              exists_common_left_denominator (X := X₂) (Y := Y) g₂
            let q : CostructuredArrow (leftLocalizationFunctor W) ((leftLocalizationFunctor W).obj Y) :=
              CostructuredArrow.mk (leftFractionHom (𝟙 Y') s hs)
            refine ⟨q, CostructuredArrow.homMk (f false) ?_,
              CostructuredArrow.homMk (f true) ?_, trivial⟩
            · change (leftLocalizationFunctor W).map (f false) ≫
                leftFractionHom (𝟙 Y') s hs = j.hom
              rw [left_fraction_factor]
              simpa [g₂, X₂] using (hf false).symm
            · change (leftLocalizationFunctor W).map (f true) ≫
                leftFractionHom (𝟙 Y') s hs = k.hom
              rw [left_fraction_factor]
              simpa [g₂, X₂] using (hf true).symm
          · intro j k a b
            obtain ⟨φ, hφ⟩ :=
              CategoryTheory.Localization.exists_leftFraction
                (leftLocalizationFunctor W) W
                (show (leftLocalizationFunctor W).obj k.left ⟶
                  (leftLocalizationFunctor W).obj Y from k.hom)
            have hk : k.hom = leftFractionHom φ.f φ.s φ.hs := by
              exact hφ.trans
                (MorphismProperty.LeftFraction.Localization.homMk_eq φ).symm
            have heq :
                leftFractionHom (a.left ≫ φ.f) φ.s φ.hs =
                  leftFractionHom (b.left ≫ φ.f) φ.s φ.hs := by
              calc
                leftFractionHom (a.left ≫ φ.f) φ.s φ.hs =
                    (leftLocalizationFunctor W).map a.left ≫ k.hom := by
                      rw [hk]
                      convert (left_fraction_precompose_numerator
                        a.left φ.f φ.s φ.hs).symm using 1
                _ = j.hom := CostructuredArrow.w a
                _ = (leftLocalizationFunctor W).map b.left ≫ k.hom :=
                  (CostructuredArrow.w b).symm
                _ = leftFractionHom (b.left ≫ φ.f) φ.s φ.hs := by
                  rw [hk]
                  convert left_fraction_precompose_numerator b.left φ.f φ.s φ.hs using 1
            obtain ⟨Z', t, ht, hfg⟩ :=
              (left_fraction_eq_iff_postcomp (a.left ≫ φ.f) (b.left ≫ φ.f)
                φ.s φ.hs).1 heq
            let st := φ.s ≫ t
            have hst : W st := W.comp_mem _ _ φ.hs ht
            let q : CostructuredArrow (leftLocalizationFunctor W) ((leftLocalizationFunctor W).obj Y) :=
              CostructuredArrow.mk (leftFractionHom (𝟙 Z') st hst)
            have hq : (leftLocalizationFunctor W).map (φ.f ≫ t) ≫ q.hom = k.hom := by
              change (leftLocalizationFunctor W).map (φ.f ≫ t) ≫
                  leftFractionHom (𝟙 Z') st hst = k.hom
              calc
                (leftLocalizationFunctor W).map (φ.f ≫ t) ≫
                    leftFractionHom (𝟙 Z') st hst =
                    leftFractionHom (φ.f ≫ t) st hst :=
                  left_fraction_factor (φ.f ≫ t) st hst
                _ = leftFractionHom φ.f φ.s φ.hs :=
                  by
                    simpa [st] using
                      (left_fraction_postcompose_denominator_of_composite
                        φ.f φ.s t φ.hs hst)
                _ = k.hom := by simpa using hk.symm
            refine ⟨q, CostructuredArrow.homMk (φ.f ≫ t) hq, ?_⟩
            apply CostructuredArrow.hom_ext
            change a.left ≫ φ.f ≫ t = b.left ≫ φ.f ≫ t
            simpa [Category.assoc] using hfg
        exact { toIsFilteredOrEmpty := hfiltered, nonempty := hne } }
  exact preservesFiniteColimits_of_coflat (leftLocalizationFunctor W)

private theorem left_fraction_comp_right_map {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    {X A X' Y' : C} (g : X ⟶ A) (s : X' ⟶ A) (hs : W s)
    (f' : X' ⟶ Y') (ψ : MorphismProperty.LeftFraction W A Y')
    (hψ : f' ≫ ψ.s = s ≫ ψ.f) :
    leftFractionHom g s hs ≫ (leftLocalizationFunctor W).map f' =
      leftFractionHom (g ≫ ψ.f) ψ.s ψ.hs := by
  unfold leftFractionHom
  rw [MorphismProperty.LeftFraction.Localization.Q_map]
  rw [MorphismProperty.LeftFraction.Localization.homMk_comp_homMk
    (MorphismProperty.LeftFraction.mk g s hs)
    (MorphismProperty.LeftFraction.ofHom W f') ψ hψ]
  simp [MorphismProperty.LeftFraction.comp₀, MorphismProperty.LeftFraction.ofHom]

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
  obtain ⟨φa, ha⟩ :=
    CategoryTheory.Localization.exists_leftFraction
      (leftLocalizationFunctor W) W a
  obtain ⟨φb, hb⟩ :=
    CategoryTheory.Localization.exists_leftFraction
      (leftLocalizationFunctor W) W b
  have ha' : a = leftFractionHom φa.f φa.s φa.hs := by
    exact ha.trans (MorphismProperty.LeftFraction.Localization.homMk_eq φa).symm
  have hb' : b = leftFractionHom φb.f φb.s φb.hs := by
    exact hb.trans (MorphismProperty.LeftFraction.Localization.homMk_eq φb).symm
  obtain ⟨ψ, hψ⟩ :=
    (MorphismProperty.RightFraction.mk φa.s φa.hs f').exists_leftFraction
  have hfrac :
      leftFractionHom (f ≫ φb.f) φb.s φb.hs =
        leftFractionHom (φa.f ≫ ψ.f) ψ.s ψ.hs := by
    calc
      leftFractionHom (f ≫ φb.f) φb.s φb.hs =
          (leftLocalizationFunctor W).map f ≫ b := by
            rw [hb']
            exact (left_fraction_precompose_numerator f φb.f φb.s φb.hs).symm
      _ = a ≫ (leftLocalizationFunctor W).map f' := hcomm
      _ = leftFractionHom φa.f φa.s φa.hs ≫
          (leftLocalizationFunctor W).map f' := by rw [ha']
      _ = leftFractionHom (φa.f ≫ ψ.f) ψ.s ψ.hs :=
        left_fraction_comp_right_map φa.f φa.s φa.hs f' ψ hψ
  unfold leftFractionHom at hfrac
  obtain ⟨Y'', u, v, hden, hnum, hW⟩ :=
    (MorphismProperty.LeftFraction.Localization.homMk_eq_iff_leftFractionRel
      (MorphismProperty.LeftFraction.mk (f ≫ φb.f) φb.s φb.hs)
      (MorphismProperty.LeftFraction.mk (φa.f ≫ ψ.f) ψ.s ψ.hs)).1 hfrac
  refine ⟨φa.Y', Y'', φa.f, φa.s, φb.f ≫ u, φb.s ≫ u,
    ψ.f ≫ v, φa.hs, hW, ?_⟩
  refine ⟨?_, ?_, ha', ?_⟩
  · simpa [Category.assoc] using hnum.symm
  · calc
      φa.s ≫ ψ.f ≫ v = f' ≫ ψ.s ≫ v := by
        simpa [Category.assoc] using
          congrArg (fun k => k ≫ v) hψ.symm
      _ = f' ≫ (φb.s ≫ u) := by
        simpa [Category.assoc] using
          congrArg (fun k => f' ≫ k) hden.symm
  · exact hb'.trans
      (left_fraction_postcompose_denominator_of_composite
        φb.f φb.s u φb.hs hW).symm

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
    (W : MorphismProperty C) [RightMultiplicativeSystem W] :
    C ⥤ RightFractionLocalization W :=
  MorphismProperty.Q W

noncomputable def rightFractionHom {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y : C} (f : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    (rightLocalizationFunctor W).obj X ⟶ (rightLocalizationFunctor W).obj Y :=
  (MorphismProperty.RightFraction.mk s hs f).map
    (rightLocalizationFunctor W) (Localization.inverts _ W)

theorem right_fraction_precompose_denominator {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' X'' Y : C} (f : X' ⟶ Y) (s : X' ⟶ X)
    (t : X'' ⟶ X') (hs : W s) (ht : W t) :
    rightFractionHom (t ≫ f) (t ≫ s) (W.comp_mem _ _ ht hs) =
      rightFractionHom f s hs := by
  unfold rightFractionHom
  apply (MorphismProperty.RightFraction.map_eq_iff
    (rightLocalizationFunctor W) W
    (MorphismProperty.RightFraction.mk (t ≫ s) (W.comp_mem _ _ ht hs) (t ≫ f))
    (MorphismProperty.RightFraction.mk s hs f)).2
  exact ⟨X'', 𝟙 _, t, by simp, by simp,
    by simpa using W.comp_mem _ _ ht hs⟩

private theorem right_fraction_precompose_denominator_of_composite {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' X'' Y : C} (f : X' ⟶ Y) (s : X' ⟶ X)
    (t : X'' ⟶ X') (hs : W s) (hcomp : W (t ≫ s)) :
    rightFractionHom (t ≫ f) (t ≫ s) hcomp = rightFractionHom f s hs := by
  unfold rightFractionHom
  apply (MorphismProperty.RightFraction.map_eq_iff
    (rightLocalizationFunctor W) W
    (MorphismProperty.RightFraction.mk (t ≫ s) hcomp (t ≫ f))
    (MorphismProperty.RightFraction.mk s hs f)).2
  exact ⟨X'', 𝟙 _, t, by simp, by simp, by simpa using hcomp⟩

theorem right_fraction_comp {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y Z : C} (f : X' ⟶ Y) (s : X' ⟶ X)
    (g : Y ⟶ Z) (hs : W s) :
    rightFractionHom (f ≫ g) s hs =
      rightFractionHom f s hs ≫ rightFractionHom g (𝟙 Y)
        (W.id_mem Y) := by
  simp [rightFractionHom, MorphismProperty.RightFraction.map, Category.assoc]

theorem right_fraction_change_target {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' X'' Y : C} (f : X' ⟶ Y) (s : X' ⟶ X) (t : X ⟶ X'')
    (hs : W s) (ht : W t) :
      rightFractionHom f (s ≫ t) (W.comp_mem _ _ hs ht) =
      rightFractionHom (𝟙 X) t ht ≫ rightFractionHom f s hs := by
  have : IsIso ((rightLocalizationFunctor W).map (s ≫ t)) :=
    MorphismProperty.Q_inverts W (s ≫ t) (W.comp_mem _ _ hs ht)
  apply (cancel_epi ((rightLocalizationFunctor W).map (s ≫ t))).1
  have hst := MorphismProperty.RightFraction.map_s_comp_map
    (MorphismProperty.RightFraction.mk (s ≫ t) (W.comp_mem _ _ hs ht) f)
    (rightLocalizationFunctor W) (Localization.inverts _ W)
  have ht' := MorphismProperty.RightFraction.map_s_comp_map
    (MorphismProperty.RightFraction.mk t ht (𝟙 X))
    (rightLocalizationFunctor W) (Localization.inverts _ W)
  have hs' := MorphismProperty.RightFraction.map_s_comp_map
    (MorphismProperty.RightFraction.mk s hs f)
    (rightLocalizationFunctor W) (Localization.inverts _ W)
  unfold rightFractionHom
  rw [hst]
  rw [(rightLocalizationFunctor W).map_comp]
  have hright :
      (((rightLocalizationFunctor W).map s ≫
          (rightLocalizationFunctor W).map t) ≫
        (MorphismProperty.RightFraction.mk t ht (𝟙 X)).map
          (rightLocalizationFunctor W) (Localization.inverts _ W)) ≫
          (MorphismProperty.RightFraction.mk s hs f).map
            (rightLocalizationFunctor W) (Localization.inverts _ W) =
        (rightLocalizationFunctor W).map f := by
    calc
      (((rightLocalizationFunctor W).map s ≫
            (rightLocalizationFunctor W).map t) ≫
          (MorphismProperty.RightFraction.mk t ht (𝟙 X)).map
            (rightLocalizationFunctor W) (Localization.inverts _ W)) ≫
            (MorphismProperty.RightFraction.mk s hs f).map
              (rightLocalizationFunctor W) (Localization.inverts _ W) =
          ((rightLocalizationFunctor W).map s ≫
            ((rightLocalizationFunctor W).map t ≫
              (MorphismProperty.RightFraction.mk t ht (𝟙 X)).map
                (rightLocalizationFunctor W) (Localization.inverts _ W))) ≫
            (MorphismProperty.RightFraction.mk s hs f).map
              (rightLocalizationFunctor W) (Localization.inverts _ W) := by
                simp [Category.assoc]
      _ = ((rightLocalizationFunctor W).map s ≫
            (rightLocalizationFunctor W).map (𝟙 X)) ≫
            (MorphismProperty.RightFraction.mk s hs f).map
              (rightLocalizationFunctor W) (Localization.inverts _ W) := by
                rw [ht']
      _ = (rightLocalizationFunctor W).map s ≫
            (MorphismProperty.RightFraction.mk s hs f).map
              (rightLocalizationFunctor W) (Localization.inverts _ W) := by
                simp
      _ = (rightLocalizationFunctor W).map f := hs'
  simpa using hright.symm

private theorem right_denominator_category_is_cofiltered_aux {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [RightMultiplicativeSystem W] (X : C) :
    IsCofiltered (MorphismProperty.Over W (⊤ : MorphismProperty C) X) := by
  have hne : Nonempty (MorphismProperty.Over W (⊤ : MorphismProperty C) X) :=
    ⟨MorphismProperty.Over.mk (P := W) (Q := (⊤ : MorphismProperty C))
      (𝟙 X) (W.id_mem X)⟩
  have hcofiltered : IsCofilteredOrEmpty
      (MorphismProperty.Over W (⊤ : MorphismProperty C) X) := by
    refine ⟨?_, ?_⟩
    · intro j k
      obtain ⟨φ, hφ⟩ :=
        (MorphismProperty.LeftFraction.mk j.hom k.hom k.prop).exists_rightFraction
      let z : MorphismProperty.Over W (⊤ : MorphismProperty C) X :=
        MorphismProperty.Over.mk (P := W) (Q := (⊤ : MorphismProperty C))
          (φ.s ≫ j.hom) (W.comp_mem _ _ φ.hs j.prop)
      exact ⟨z, MorphismProperty.Over.homMk φ.s rfl trivial,
        MorphismProperty.Over.homMk φ.f hφ.symm trivial, trivial⟩
    · intro j k f g
      obtain ⟨Z, t, ht, hfg⟩ :=
        MorphismProperty.HasRightCalculusOfFractions.ext f.left g.left k.hom k.prop
          (by rw [MorphismProperty.Over.w f, MorphismProperty.Over.w g])
      let z : MorphismProperty.Over W (⊤ : MorphismProperty C) X :=
        MorphismProperty.Over.mk (P := W) (Q := (⊤ : MorphismProperty C))
          (t ≫ j.hom) (W.comp_mem _ _ ht j.prop)
      refine ⟨z, MorphismProperty.Over.homMk t rfl trivial, ?_⟩
      apply MorphismProperty.Over.Hom.ext
      change t ≫ f.left = t ≫ g.left
      exact hfg
  exact { toIsCofilteredOrEmpty := hcofiltered, nonempty := hne }

theorem exists_common_right_denominator {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {ι : Type w} [Finite ι] {Y : ι → C} {X : C}
    (g : ∀ i, (rightLocalizationFunctor W).obj X ⟶
      (rightLocalizationFunctor W).obj (Y i)) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
      ∀ i, g i = rightFractionHom (f i) s hs := by
  have hcofiltered : IsCofiltered (MorphismProperty.Over W
      (⊤ : MorphismProperty C) X) :=
    right_denominator_category_is_cofiltered_aux X
  classical
  let hι : Fintype ι := Fintype.ofFinite ι
  let hcat : FinCategory (Discrete ι) :=
    @CategoryTheory.finCategoryDiscreteOfFintype ι hι
  choose φ hφ using fun i =>
    CategoryTheory.Localization.exists_rightFraction
      (rightLocalizationFunctor W) W (g i)
  let d : ι → MorphismProperty.Over W (⊤ : MorphismProperty C) X := fun i =>
    MorphismProperty.Over.mk (P := W) (Q := (⊤ : MorphismProperty C))
      (φ i).s (φ i).hs
  obtain ⟨c⟩ :=
    @IsCofiltered.cone_nonempty _ _ hcofiltered _ _ hcat (Discrete.functor d)
  let s : (c.pt.left : C) ⟶ X := c.pt.hom
  have hs : W s := c.pt.prop
  refine ⟨c.pt.left, s, hs,
    (fun i => (c.π.app (Discrete.mk i)).left ≫ (φ i).f), ?_⟩
  intro i
  have hgi : g i = rightFractionHom (φ i).f (φ i).s (φ i).hs := by
    simpa [rightFractionHom] using hφ i
  have hden : (c.π.app (Discrete.mk i)).left ≫ (φ i).s = s := by
    change (c.π.app (Discrete.mk i)).left ≫ (φ i).s = c.pt.hom
    exact MorphismProperty.Over.w (c.π.app (Discrete.mk i))
  have hcomp : W ((c.π.app (Discrete.mk i)).left ≫ (φ i).s) := by
    rw [hden]
    exact hs
  calc
    g i = rightFractionHom (φ i).f (φ i).s (φ i).hs := hgi
    _ = rightFractionHom ((c.π.app (Discrete.mk i)).left ≫ (φ i).f)
        ((c.π.app (Discrete.mk i)).left ≫ (φ i).s) hcomp := by
      symm
      exact right_fraction_precompose_denominator_of_composite
        (φ i).f (φ i).s (c.π.app (Discrete.mk i)).left (φ i).hs hcomp
    _ = rightFractionHom ((c.π.app (Discrete.mk i)).left ≫ (φ i).f) s hs := by
      simp [hden]

theorem right_fraction_eq_iff_precomp {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y : C} (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    (rightFractionHom f s hs = rightFractionHom g s hs) ↔
      ∃ (X'' : C) (t : X'' ⟶ X') (_ : W t), t ≫ f = t ≫ g := by
  constructor
  · intro h
    have h' :
        (MorphismProperty.RightFraction.mk s hs f).map
            (rightLocalizationFunctor W) (Localization.inverts _ W) =
          (MorphismProperty.RightFraction.mk s hs g).map
            (rightLocalizationFunctor W) (Localization.inverts _ W) := by
      simpa [rightFractionHom] using h
    have hmap : (rightLocalizationFunctor W).map f =
        (rightLocalizationFunctor W).map g := by
      calc
        (rightLocalizationFunctor W).map f =
            (rightLocalizationFunctor W).map s ≫
              (MorphismProperty.RightFraction.mk s hs f).map
                (rightLocalizationFunctor W) (Localization.inverts _ W) := by
          symm
          exact MorphismProperty.RightFraction.map_s_comp_map
            (MorphismProperty.RightFraction.mk s hs f)
            (rightLocalizationFunctor W) (Localization.inverts _ W)
        _ = (rightLocalizationFunctor W).map s ≫
            (MorphismProperty.RightFraction.mk s hs g).map
              (rightLocalizationFunctor W) (Localization.inverts _ W) := by
          rw [h']
        _ = (rightLocalizationFunctor W).map g :=
          MorphismProperty.RightFraction.map_s_comp_map
            (MorphismProperty.RightFraction.mk s hs g)
            (rightLocalizationFunctor W) (Localization.inverts _ W)
    exact (MorphismProperty.map_eq_iff_precomp
      (L := rightLocalizationFunctor W) (W := W) f g).1 hmap
  · rintro ⟨X'', t, ht, hfg⟩
    have hmap : (rightLocalizationFunctor W).map f =
        (rightLocalizationFunctor W).map g :=
      (MorphismProperty.map_eq_iff_precomp
        (L := rightLocalizationFunctor W) (W := W) f g).2 ⟨X'', t, ht, hfg⟩
    unfold rightFractionHom
    dsimp [MorphismProperty.RightFraction.map]
    rw [hmap]

theorem right_fraction_eq_iff_precomp_of_denominator {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y : C} (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    (rightFractionHom f s hs = rightFractionHom g s hs) ↔
      ∃ (X'' : C) (a : X'' ⟶ X') (_ : a ≫ f = a ≫ g), W (a ≫ s) := by
  constructor
  · intro h
    obtain ⟨X'', t, ht, hfg⟩ :=
      (right_fraction_eq_iff_precomp f g s hs).1 h
    exact ⟨X'', t, hfg, W.comp_mem _ _ ht hs⟩
  · rintro ⟨X'', a, hfg, ha⟩
    unfold rightFractionHom
    apply (MorphismProperty.RightFraction.map_eq_iff
      (rightLocalizationFunctor W) W
      (MorphismProperty.RightFraction.mk s hs f)
      (MorphismProperty.RightFraction.mk s hs g)).2
    exact ⟨X'', a, a, rfl, hfg, ha⟩

theorem right_fraction_precomp_conditions_iff {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y : C} (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    (∃ (X'' : C) (t : X'' ⟶ X') (_ : W t), t ≫ f = t ≫ g) ↔
      ∃ (X'' : C) (a : X'' ⟶ X') (_ : a ≫ f = a ≫ g), W (a ≫ s) := by
  constructor
  · rintro ⟨X'', t, ht, hfg⟩
    exact ⟨X'', t, hfg, W.comp_mem _ _ ht hs⟩
  · rintro ⟨X'', a, hfg, ha⟩
    obtain ⟨Z, t, ht, hfg'⟩ :=
      (right_fraction_eq_iff_precomp f g s hs).1
        ((right_fraction_eq_iff_precomp_of_denominator f g s hs).2
          ⟨X'', a, hfg, ha⟩)
    exact ⟨Z, t, ht, hfg'⟩

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
  exact right_denominator_category_is_cofiltered_aux X

theorem right_localization_hom_is_filtered_colimit {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [RightMultiplicativeSystem W]
    (X Y : C) :
    Nonempty (((rightLocalizationFunctor W).obj X ⟶
      (rightLocalizationFunctor W).obj Y) ≃
      rightDenominatorHomColimit W X Y) := by
  have hcofiltered : IsCofiltered (RightDenominatorCategory W X) :=
    right_denominator_category_is_cofiltered_aux X
  have : IsCofiltered (RightDenominatorCategory W X) := hcofiltered
  have hfiltered : IsFiltered (RightDenominatorCategory W X)ᵒᵖ := inferInstance
  let c₀ := Types.TypeMax.colimitCocone (rightDenominatorHomDiagram W X Y)
  let fracCocone : Cocone (rightDenominatorHomDiagram W X Y) :=
    { pt := (rightLocalizationFunctor W).obj X ⟶ (rightLocalizationFunctor W).obj Y
      ι :=
        { app := fun d => ↾(fun z : ULift.{u} (d.unop.left ⟶ Y) =>
            rightFractionHom z.down d.unop.hom d.unop.prop)
          naturality := by
            intro d e a
            ext z
            cases z
            simp [rightDenominatorHomDiagram]
            change rightFractionHom (a.unop.left ≫ _) e.unop.hom e.unop.prop =
              rightFractionHom _ d.unop.hom d.unop.prop
            have hden := MorphismProperty.Over.w a.unop
            have hcomp : W (a.unop.left ≫ d.unop.hom) := by
              rw [hden]
              exact e.unop.prop
            simpa [hden] using
              (right_fraction_precompose_denominator_of_composite
                _ d.unop.hom a.unop.left d.unop.prop hcomp) } }
  have hfrac : IsColimit fracCocone := by
    apply Types.FilteredColimit.isColimitOf
      (rightDenominatorHomDiagram W X Y) fracCocone
    · intro h
      obtain ⟨φ, hφ⟩ :=
        CategoryTheory.Localization.exists_rightFraction
          (rightLocalizationFunctor W) W h
      obtain ⟨X', s, hs, f, rfl⟩ := φ.cases
      let d : RightDenominatorCategory W X :=
        MorphismProperty.Over.mk (P := W) (Q := (⊤ : MorphismProperty C)) s hs
      refine ⟨Opposite.op d, ULift.up f, ?_⟩
      change h = rightFractionHom f s hs
      simpa [rightFractionHom] using hφ
    · intro d e z₁ z₂ h
      change rightFractionHom z₁.down d.unop.hom d.unop.prop =
        rightFractionHom z₂.down e.unop.hom e.unop.prop at h
      unfold rightFractionHom at h
      obtain ⟨Z, a, b, hden, hfg, hW⟩ :=
        (MorphismProperty.RightFraction.map_eq_iff
          (rightLocalizationFunctor W) W
          (MorphismProperty.RightFraction.mk d.unop.hom d.unop.prop z₁.down)
          (MorphismProperty.RightFraction.mk e.unop.hom e.unop.prop z₂.down)).1 h
      let k₀ : RightDenominatorCategory W X :=
        MorphismProperty.Over.mk (P := W) (Q := (⊤ : MorphismProperty C))
          (a ≫ d.unop.hom) hW
      let u₀ : k₀ ⟶ d.unop :=
        MorphismProperty.Over.homMk a rfl trivial
      let v₀ : k₀ ⟶ e.unop :=
        MorphismProperty.Over.homMk b hden.symm trivial
      refine ⟨Opposite.op k₀, u₀.op, v₀.op, ?_⟩
      change ULift.up (a ≫ z₁.down) = ULift.up (b ≫ z₂.down)
      exact congrArg ULift.up hfg
  refine ⟨(IsColimit.coconePointUniqueUpToIso
    (rightDenominatorHomColimit_isColimit W X Y) hfrac).toEquiv.symm⟩

theorem right_localization_inverts {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X Y : C} (s : X ⟶ Y) (hs : W s) :
    IsIso ((rightLocalizationFunctor W).map s) := by
  exact MorphismProperty.Q_inverts W s hs

noncomputable def rightLocalizationLift {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) (hG : W.IsInvertedBy G) : RightFractionLocalization W ⥤ D :=
  Localization.Construction.lift G hG

theorem rightLocalizationLift_fac {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) (hG : W.IsInvertedBy G) :
    rightLocalizationFunctor W ⋙ rightLocalizationLift G hG = G :=
  Localization.Construction.fac G hG

theorem rightLocalizationLift_unique {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {D : Type u'} [Category.{v'} D]
    (G₁ G₂ : RightFractionLocalization W ⥤ D)
    (h : rightLocalizationFunctor W ⋙ G₁ = rightLocalizationFunctor W ⋙ G₂) :
    G₁ = G₂ :=
  Localization.Construction.uniq G₁ G₂ h

theorem right_localization_universal_property {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) (hG : W.IsInvertedBy G) :
    ∃! H : RightFractionLocalization W ⥤ D,
      rightLocalizationFunctor W ⋙ H = G := by
  refine ⟨rightLocalizationLift G hG, rightLocalizationLift_fac G hG, ?_⟩
  intro H hH
  exact rightLocalizationLift_unique H (rightLocalizationLift G hG) (hH.trans
    (rightLocalizationLift_fac G hG).symm)

private theorem right_fraction_factor {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y : C} (f : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    rightFractionHom (𝟙 X') s hs ≫ (rightLocalizationFunctor W).map f =
      rightFractionHom f s hs := by
  calc
    rightFractionHom (𝟙 X') s hs ≫ (rightLocalizationFunctor W).map f =
        rightFractionHom (𝟙 X') s hs ≫
          rightFractionHom f (𝟙 X') (W.id_mem X') := by
            congr 1
            simp [rightFractionHom, MorphismProperty.RightFraction.map]
    _ = rightFractionHom (𝟙 X' ≫ f) s hs :=
      (right_fraction_comp (𝟙 X') s f hs).symm
    _ = rightFractionHom f s hs := by simp

theorem right_localization_preserves_finite_limits {C : Type u}
    [Category.{v} C] {W : MorphismProperty C} [RightMultiplicativeSystem W] :
    PreservesFiniteLimits (rightLocalizationFunctor W) := by
  have : RepresentablyFlat (rightLocalizationFunctor W) :=
    { cofiltered := fun Z => by
        let X : C := (rightLocalizationFunctor W).objPreimage Z
        let e : (rightLocalizationFunctor W).obj X ≅ Z :=
          (rightLocalizationFunctor W).objObjPreimageIso Z
        apply (IsCofiltered.iff_of_equivalence (StructuredArrow.mapIso e)).1
        have hne : Nonempty (StructuredArrow
            ((rightLocalizationFunctor W).obj X) (rightLocalizationFunctor W)) :=
          ⟨StructuredArrow.mk (𝟙 ((rightLocalizationFunctor W).obj X))⟩
        have hcofiltered : IsCofilteredOrEmpty (StructuredArrow
            ((rightLocalizationFunctor W).obj X) (rightLocalizationFunctor W)) := by
          refine ⟨?_, ?_⟩
          · intro j k
            let X₂ : Bool → C := fun b =>
              match b with
              | false => j.right
              | true => k.right
            let g₂ : ∀ b, (rightLocalizationFunctor W).obj X ⟶
                (rightLocalizationFunctor W).obj (X₂ b) := fun b =>
              match b with
              | false => j.hom
              | true => k.hom
            obtain ⟨X', s, hs, f, hf⟩ :=
              exists_common_right_denominator (X := X) (Y := X₂) g₂
            let q : StructuredArrow ((rightLocalizationFunctor W).obj X)
                (rightLocalizationFunctor W) :=
              StructuredArrow.mk (rightFractionHom (𝟙 X') s hs)
            refine ⟨q, StructuredArrow.homMk (f false) ?_,
              StructuredArrow.homMk (f true) ?_, trivial⟩
            · change rightFractionHom (𝟙 X') s hs ≫
                (rightLocalizationFunctor W).map (f false) = j.hom
              rw [right_fraction_factor]
              simpa [g₂, X₂] using (hf false).symm
            · change rightFractionHom (𝟙 X') s hs ≫
                (rightLocalizationFunctor W).map (f true) = k.hom
              rw [right_fraction_factor]
              simpa [g₂, X₂] using (hf true).symm
          · intro j k a b
            obtain ⟨φ, hφ⟩ :=
              CategoryTheory.Localization.exists_rightFraction
                (rightLocalizationFunctor W) W j.hom
            obtain ⟨A, s, hs, f₀, rfl⟩ := φ.cases
            have hj : j.hom = rightFractionHom f₀ s hs := by
              simpa [rightFractionHom] using hφ
            have hsf : (rightLocalizationFunctor W).map s ≫ j.hom =
                (rightLocalizationFunctor W).map f₀ := by
              rw [hj]
              exact MorphismProperty.RightFraction.map_s_comp_map
                (MorphismProperty.RightFraction.mk s hs f₀)
                (rightLocalizationFunctor W) (Localization.inverts _ W)
            have hmap :
                (rightLocalizationFunctor W).map (f₀ ≫ a.right) =
                  (rightLocalizationFunctor W).map (f₀ ≫ b.right) := by
              calc
                (rightLocalizationFunctor W).map (f₀ ≫ a.right) =
                    (rightLocalizationFunctor W).map f₀ ≫
                      (rightLocalizationFunctor W).map a.right := by
                        rw [(rightLocalizationFunctor W).map_comp]
                _ = (rightLocalizationFunctor W).map s ≫ j.hom ≫
                      (rightLocalizationFunctor W).map a.right := by
                        rw [← Category.assoc, hsf]
                _ = (rightLocalizationFunctor W).map s ≫ k.hom := by
                        rw [StructuredArrow.w a]
                _ = (rightLocalizationFunctor W).map s ≫ j.hom ≫
                      (rightLocalizationFunctor W).map b.right := by
                        rw [StructuredArrow.w b]
                _ = (rightLocalizationFunctor W).map (f₀ ≫ b.right) := by
                        rw [← Category.assoc, hsf]
                        rw [(rightLocalizationFunctor W).map_comp]
            obtain ⟨Z', t, ht, hfg⟩ :=
              (MorphismProperty.map_eq_iff_precomp
                (L := rightLocalizationFunctor W) (W := W)
                (f₀ ≫ a.right) (f₀ ≫ b.right)).1 hmap
            let st := t ≫ s
            have hst : W st := W.comp_mem _ _ ht hs
            let q : StructuredArrow ((rightLocalizationFunctor W).obj X)
                (rightLocalizationFunctor W) :=
              StructuredArrow.mk (rightFractionHom (𝟙 Z') st hst)
            have hq :
                (rightFractionHom (𝟙 Z') st hst) ≫
                    (rightLocalizationFunctor W).map (t ≫ f₀) = j.hom := by
              calc
                _ = rightFractionHom (t ≫ f₀) st hst :=
                  right_fraction_factor (t ≫ f₀) st hst
                _ = rightFractionHom f₀ s hs := by
                  simpa [st] using
                    (right_fraction_precompose_denominator
                      f₀ s t hs ht)
                _ = j.hom := hj.symm
            refine ⟨q, StructuredArrow.homMk (t ≫ f₀) hq, ?_⟩
            apply StructuredArrow.hom_ext
            change (t ≫ f₀) ≫ a.right = (t ≫ f₀) ≫ b.right
            simpa [Category.assoc] using hfg
        exact { toIsCofilteredOrEmpty := hcofiltered, nonempty := hne } }
  exact preservesFiniteLimits_of_flat (rightLocalizationFunctor W)

private theorem right_fraction_postcompose_map {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X X' Y Y' : C} (g : X' ⟶ Y) (s : X' ⟶ X) (f : Y ⟶ Y') (hs : W s) :
    rightFractionHom g s hs ≫ (rightLocalizationFunctor W).map f =
      rightFractionHom (g ≫ f) s hs := by
  calc
    rightFractionHom g s hs ≫ (rightLocalizationFunctor W).map f =
        rightFractionHom g s hs ≫ rightFractionHom f (𝟙 Y) (W.id_mem Y) := by
          congr 1
          simp [rightFractionHom, MorphismProperty.RightFraction.map]
    _ = rightFractionHom (g ≫ f) s hs :=
      (right_fraction_comp g s f hs).symm

private theorem right_fraction_precompose_map {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [RightMultiplicativeSystem W]
    {X Y B Y' : C} (f : X ⟶ Y) (h : B ⟶ Y') (t : B ⟶ Y) (ht : W t)
    (ψ : MorphismProperty.RightFraction W X B)
    (hψ : ψ.s ≫ f = ψ.f ≫ t) :
    (rightLocalizationFunctor W).map f ≫ rightFractionHom h t ht =
      rightFractionHom (ψ.f ≫ h) ψ.s ψ.hs := by
  have : IsIso ((rightLocalizationFunctor W).map ψ.s) :=
    MorphismProperty.Q_inverts W ψ.s ψ.hs
  apply (cancel_epi ((rightLocalizationFunctor W).map ψ.s)).1
  have hψmap := MorphismProperty.RightFraction.map_s_comp_map
    (MorphismProperty.RightFraction.mk ψ.s ψ.hs (ψ.f ≫ h))
    (rightLocalizationFunctor W) (Localization.inverts _ W)
  have htmap := MorphismProperty.RightFraction.map_s_comp_map
    (MorphismProperty.RightFraction.mk t ht h)
    (rightLocalizationFunctor W) (Localization.inverts _ W)
  have htmap' : (rightLocalizationFunctor W).map t ≫
        rightFractionHom h t ht = (rightLocalizationFunctor W).map h := by
    unfold rightFractionHom
    exact htmap
  calc
    (rightLocalizationFunctor W).map ψ.s ≫
          ((rightLocalizationFunctor W).map f ≫ rightFractionHom h t ht) =
        (rightLocalizationFunctor W).map (ψ.s ≫ f) ≫
          rightFractionHom h t ht := by
            rw [(rightLocalizationFunctor W).map_comp]
            simp [Category.assoc]
    _ = (rightLocalizationFunctor W).map (ψ.f ≫ t) ≫
          rightFractionHom h t ht := by rw [hψ]
    _ = (rightLocalizationFunctor W).map ψ.f ≫
          ((rightLocalizationFunctor W).map t ≫ rightFractionHom h t ht) := by
            rw [(rightLocalizationFunctor W).map_comp]
            simp [Category.assoc]
    _ = (rightLocalizationFunctor W).map ψ.f ≫
          (rightLocalizationFunctor W).map h := by
            rw [htmap']
    _ = (rightLocalizationFunctor W).map (ψ.f ≫ h) := by
            rw [(rightLocalizationFunctor W).map_comp]
    _ = (rightLocalizationFunctor W).map ψ.s ≫
          rightFractionHom (ψ.f ≫ h) ψ.s ψ.hs := hψmap.symm

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
  obtain ⟨φa, ha⟩ :=
    CategoryTheory.Localization.exists_rightFraction
      (rightLocalizationFunctor W) W a
  obtain ⟨φb, hb⟩ :=
    CategoryTheory.Localization.exists_rightFraction
      (rightLocalizationFunctor W) W b
  obtain ⟨A, s, hs, g, rfl⟩ := φa.cases
  obtain ⟨B, t, ht, h, rfl⟩ := φb.cases
  have ha' : a = rightFractionHom g s hs := by
    simpa [rightFractionHom] using ha
  have hb' : b = rightFractionHom h t ht := by
    simpa [rightFractionHom] using hb
  obtain ⟨ψ, hψ⟩ :=
    (MorphismProperty.LeftFraction.mk f t ht).exists_rightFraction
  have hleft :
      rightFractionHom (ψ.f ≫ h) ψ.s ψ.hs =
        (rightLocalizationFunctor W).map f ≫ b := by
    rw [hb']
    exact (right_fraction_precompose_map f h t ht ψ hψ).symm
  have hright :
      rightFractionHom (g ≫ f') s hs =
        a ≫ (rightLocalizationFunctor W).map f' := by
    rw [ha']
    exact (right_fraction_postcompose_map g s f' hs).symm
  have hfrac :
      rightFractionHom (ψ.f ≫ h) ψ.s ψ.hs =
        rightFractionHom (g ≫ f') s hs := by
    calc
      rightFractionHom (ψ.f ≫ h) ψ.s ψ.hs =
          (rightLocalizationFunctor W).map f ≫ b := hleft
      _ = a ≫ (rightLocalizationFunctor W).map f' := hcomm
      _ = rightFractionHom (g ≫ f') s hs := hright.symm
  unfold rightFractionHom at hfrac
  obtain ⟨Z, u, v, hden, hnum, hW⟩ :=
    (MorphismProperty.RightFraction.map_eq_iff
      (rightLocalizationFunctor W) W
      (MorphismProperty.RightFraction.mk ψ.s ψ.hs (ψ.f ≫ h))
      (MorphismProperty.RightFraction.mk s hs (g ≫ f'))).1 hfrac
  have hv : W (v ≫ s) := by
    rw [← hden]
    exact hW
  refine ⟨Z, B, u ≫ ψ.s, t, v ≫ g, h, u ≫ ψ.f, hW, ht, ?_⟩
  refine ⟨?_, ?_, ?_, hb'⟩
  · simpa [Category.assoc] using congrArg (fun k => u ≫ k) hψ
  · simpa [Category.assoc] using hnum
  · calc
      a = rightFractionHom g s hs := ha'
      _ = rightFractionHom (v ≫ g) (v ≫ s) hv := by
        symm
        exact right_fraction_precompose_denominator_of_composite g s v hs hv
      _ = rightFractionHom (v ≫ g) (u ≫ ψ.s) hW := by simp [hden]

/-! ## Two-sided calculus and saturation -/

noncomputable def twoSidedLocalizationEquivalence {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [LeftMultiplicativeSystem W]
    (hW : MultiplicativeSystem W) :
    LeftFractionLocalization W ≌ RightFractionLocalization W := by
  letI : RightMultiplicativeSystem W := hW.2
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
  intro X Y f hf
  have : IsIso f := hf
  have : MultiplicativeSystem W := hW.1
  have : LeftMultiplicativeSystem W := hW.1.1
  have : RightMultiplicativeSystem W := hW.1.2
  apply hW.2 (inv f) f (inv f)
  · simpa using W.id_mem Y
  · simpa using W.id_mem X

theorem isIso_of_adjacent_composites {C : Type u} [Category.{v} C]
    {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsIso (f ≫ g)] [IsIso (g ≫ h)] : IsIso g := by
  let l : Z ⟶ Y := inv (f ≫ g) ≫ f
  let r : Z ⟶ Y := h ≫ inv (g ≫ h)
  have hl : l ≫ g = 𝟙 Z := by
    simp [l, Category.assoc]
  have hr : g ≫ r = 𝟙 Y := by
    dsimp [r]
    rw [← Category.assoc]
    exact IsIso.hom_inv_id (g ≫ h)
  have hlr : l = r := by
    calc
      l = l ≫ 𝟙 Y := by simp
      _ = l ≫ (g ≫ r) := by rw [hr]
      _ = (l ≫ g) ≫ r := by simp [Category.assoc]
      _ = r := by rw [hl]; simp
  exact IsIso.mk' ⟨l, hl, by rw [hlr]; exact hr⟩

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
  ext X Y f
  constructor
  · intro hf
    change IsIso ((MorphismProperty.Q W).map f) at hf
    have : IsIso ((MorphismProperty.Q W).map f) := hf
    have : LeftMultiplicativeSystem W := hW.1
    have : RightMultiplicativeSystem W := hW.2
    obtain ⟨φ, hφ⟩ :=
      CategoryTheory.Localization.exists_leftFraction
        (MorphismProperty.Q W) W (inv ((MorphismProperty.Q W).map f))
    obtain ⟨ψ, hψ⟩ :=
      CategoryTheory.Localization.exists_rightFraction
        (MorphismProperty.Q W) W (inv ((MorphismProperty.Q W).map f))
    have hleftid :
        (MorphismProperty.Q W).map f ≫
            φ.map (MorphismProperty.Q W) (MorphismProperty.Q_inverts W) = 𝟙 _ := by
      rw [← hφ]
      exact IsIso.hom_inv_id ((MorphismProperty.Q W).map f)
    have hrightid :
        ψ.map (MorphismProperty.Q W) (MorphismProperty.Q_inverts W) ≫
            (MorphismProperty.Q W).map f = 𝟙 _ := by
      rw [← hψ]
      exact IsIso.inv_hom_id ((MorphismProperty.Q W).map f)
    have hmapL :
        (MorphismProperty.Q W).map (f ≫ φ.f) =
          (MorphismProperty.Q W).map φ.s := by
      calc
        (MorphismProperty.Q W).map (f ≫ φ.f) =
            (MorphismProperty.Q W).map f ≫ (MorphismProperty.Q W).map φ.f := by
              rw [Functor.map_comp]
        _ = (MorphismProperty.Q W).map f ≫
            (φ.map (MorphismProperty.Q W) (MorphismProperty.Q_inverts W) ≫
              (MorphismProperty.Q W).map φ.s) := by
              rw [φ.map_comp_map_s]
        _ = (MorphismProperty.Q W).map φ.s := by
              rw [← Category.assoc, hleftid]
              simp
    have hmapR :
        (MorphismProperty.Q W).map (ψ.f ≫ f) =
          (MorphismProperty.Q W).map ψ.s := by
      calc
        (MorphismProperty.Q W).map (ψ.f ≫ f) =
            (MorphismProperty.Q W).map ψ.f ≫ (MorphismProperty.Q W).map f := by
              rw [Functor.map_comp]
        _ = ((MorphismProperty.Q W).map ψ.s ≫
            ψ.map (MorphismProperty.Q W) (MorphismProperty.Q_inverts W)) ≫
              (MorphismProperty.Q W).map f := by
              rw [ψ.map_s_comp_map]
        _ = (MorphismProperty.Q W).map ψ.s := by
              rw [Category.assoc, hrightid]
              simp
    obtain ⟨T, t, ht, hpost⟩ :=
      (MorphismProperty.map_eq_iff_postcomp (L := MorphismProperty.Q W) (W := W)
        (f ≫ φ.f) φ.s).1 hmapL
    obtain ⟨Z, g, hg, hpre⟩ :=
      (MorphismProperty.map_eq_iff_precomp (L := MorphismProperty.Q W) (W := W)
        (ψ.f ≫ f) ψ.s).1 hmapR
    refine ⟨Z, g ≫ ψ.f, T, φ.f ≫ t, ?_, ?_⟩
    · rw [Category.assoc, hpre]
      exact W.comp_mem _ _ hg ψ.hs
    · rw [← Category.assoc, hpost]
      exact W.comp_mem _ _ φ.hs ht
  · rintro ⟨Z, g, T, h, hgf, fh⟩
    change IsIso ((MorphismProperty.Q W).map f)
    have : IsIso ((MorphismProperty.Q W).map (g ≫ f)) :=
      MorphismProperty.Q_inverts W (g ≫ f) hgf
    have : IsIso ((MorphismProperty.Q W).map (f ≫ h)) :=
      MorphismProperty.Q_inverts W (f ≫ h) fh
    let l : (MorphismProperty.Q W).obj Y ⟶ (MorphismProperty.Q W).obj X :=
      inv ((MorphismProperty.Q W).map (g ≫ f)) ≫ (MorphismProperty.Q W).map g
    let r : (MorphismProperty.Q W).obj Y ⟶ (MorphismProperty.Q W).obj X :=
      (MorphismProperty.Q W).map h ≫ inv ((MorphismProperty.Q W).map (f ≫ h))
    have hl : l ≫ (MorphismProperty.Q W).map f = 𝟙 _ := by
      simp [l, Category.assoc]
    have hr : (MorphismProperty.Q W).map f ≫ r = 𝟙 _ := by
      dsimp [r]
      rw [← Category.assoc, ← (MorphismProperty.Q W).map_comp]
      exact IsIso.hom_inv_id ((MorphismProperty.Q W).map (f ≫ h))
    have hlr : l = r := by
      calc
        l = l ≫ 𝟙 _ := by simp
        _ = l ≫ ((MorphismProperty.Q W).map f ≫ r) := by rw [hr]
        _ = (l ≫ (MorphismProperty.Q W).map f) ≫ r := by simp [Category.assoc]
        _ = r := by rw [hl]; simp
    exact IsIso.mk' ⟨l, hl, by rw [hlr]; exact hr⟩

theorem saturationClosure_is_smallest {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} (hW : MultiplicativeSystem W) :
    W ≤ saturationClosure W ∧
      SaturatedMultiplicativeSystem (saturationClosure W) ∧
      ∀ V : MorphismProperty C, SaturatedMultiplicativeSystem V → W ≤ V →
        saturationClosure W ≤ V := by
  have hWle : W ≤ saturationClosure W := by
    intro X Y f hf
    exact ⟨X, 𝟙 X, Y, 𝟙 Y, by simpa using hf, by simpa using hf⟩
  have hEq := invertedByLocalization_eq_saturationClosure hW
  have hIso {X Y : C} (f : X ⟶ Y) (hf : saturationClosure W f) :
      IsIso ((MorphismProperty.Q W).map f) := by
    have hf' : saturationClosure W f := hf
    rw [← hEq] at hf'
    exact hf'
  have hS_of_iso {X Y : C} (f : X ⟶ Y)
      (hf : IsIso ((MorphismProperty.Q W).map f)) : saturationClosure W f := by
    rw [← hEq]
    exact hf
  have hleft : LeftMultiplicativeSystem (saturationClosure W) := by
    have : LeftMultiplicativeSystem W := hW.1
    refine
      { id_mem := ?_
        comp_mem := ?_
        exists_leftFraction := ?_
        ext := ?_ }
    · intro X
      exact hWle _ (W.id_mem X)
    · intro X Y Z f g hf hg
      apply hS_of_iso (f ≫ g)
      have : IsIso ((MorphismProperty.Q W).map f) := hIso f hf
      have : IsIso ((MorphismProperty.Q W).map g) := hIso g hg
      rw [Functor.map_comp]
      infer_instance
    · intro X Y φ
      rcases φ.hs with ⟨Z, a, T, b, hab, hba⟩
      obtain ⟨ψ, hψ⟩ :=
        (MorphismProperty.RightFraction.mk (φ.s ≫ b) hba φ.f).exists_leftFraction
      refine ⟨MorphismProperty.LeftFraction.mk (b ≫ ψ.f) ψ.s
        (hWle _ ψ.hs), ?_⟩
      simpa [Category.assoc] using hψ
    · intro X' X Y f₁ f₂ s hs h
      rcases hs with ⟨Z, a, T, b, hab, hba⟩
      obtain ⟨Y', t, ht, hfac⟩ :=
        hW.1.ext f₁ f₂ (a ≫ s) hab (by
          simpa [Category.assoc] using congrArg (fun k => a ≫ k) h)
      exact ⟨Y', t, hWle _ ht, hfac⟩
  have hright : RightMultiplicativeSystem (saturationClosure W) := by
    have : RightMultiplicativeSystem W := hW.2
    refine
      { id_mem := ?_
        comp_mem := ?_
        exists_rightFraction := ?_
        ext := ?_ }
    · intro X
      exact hWle _ (W.id_mem X)
    · intro X Y Z f g hf hg
      apply hS_of_iso (f ≫ g)
      have : IsIso ((MorphismProperty.Q W).map f) := hIso f hf
      have : IsIso ((MorphismProperty.Q W).map g) := hIso g hg
      rw [Functor.map_comp]
      infer_instance
    · intro X Y φ
      rcases φ.hs with ⟨Z, a, T, b, hab, hba⟩
      obtain ⟨ψ, hψ⟩ :=
        (MorphismProperty.LeftFraction.mk φ.f (a ≫ φ.s) hab).exists_rightFraction
      refine ⟨MorphismProperty.RightFraction.mk ψ.s (hWle _ ψ.hs) (ψ.f ≫ a), ?_⟩
      simpa [Category.assoc] using hψ
    · intro X Y Y' f₁ f₂ s hs h
      rcases hs with ⟨Z, a, T, b, hab, hba⟩
      obtain ⟨X', t, ht, hfac⟩ :=
        hW.2.ext f₁ f₂ (s ≫ b) hba (by
          simpa [Category.assoc] using congrArg (fun k => k ≫ b) h)
      exact ⟨X', t, hWle _ ht, hfac⟩
  have hMS4 : ∀ ⦃X Y Z T : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
      saturationClosure W (f ≫ g) → saturationClosure W (g ≫ h) →
        saturationClosure W g := by
    intro X Y Z T f g h hfg hgh
    apply hS_of_iso g
    have : IsIso ((MorphismProperty.Q W).map f ≫ (MorphismProperty.Q W).map g) := by
      rw [← (MorphismProperty.Q W).map_comp]
      exact hIso (f ≫ g) hfg
    have : IsIso ((MorphismProperty.Q W).map g ≫ (MorphismProperty.Q W).map h) := by
      rw [← (MorphismProperty.Q W).map_comp]
      exact hIso (g ≫ h) hgh
    exact isIso_of_adjacent_composites
      ((MorphismProperty.Q W).map f) ((MorphismProperty.Q W).map g)
      ((MorphismProperty.Q W).map h)
  refine ⟨hWle, ⟨⟨hleft, hright⟩, hMS4⟩, ?_⟩
  intro V hV hWV X Y f hf
  rcases hf with ⟨Z, g, T, h, hgf, fh⟩
  exact hV.2 g f h (hWV _ hgf) (hWV _ fh)

theorem invertedByLocalization_eq_of_saturated {C : Type u}
    [Category.{v} C] {W : MorphismProperty C}
    (hW : SaturatedMultiplicativeSystem W) :
    invertedByLocalization W = W := by
  have hclosure : saturationClosure W = W := by
    apply le_antisymm
    · intro X Y f hf
      rcases hf with ⟨Z, g, T, h, hgf, fh⟩
      exact hW.2 g f h hgf fh
    · intro X Y f hf
      exact ⟨X, 𝟙 X, Y, 𝟙 Y, by simpa using hf, by simpa using hf⟩
  calc
    invertedByLocalization W = saturationClosure W :=
      invertedByLocalization_eq_saturationClosure hW.1
    _ = W := hclosure

end

end Formalization.Books.Categories.Unit27
