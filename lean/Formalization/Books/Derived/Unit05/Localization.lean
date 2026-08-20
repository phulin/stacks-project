import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Formalization.Books.Categories.Unit27.Localization
import Formalization.Books.Derived.Unit04.ElementaryResults
import Formalization.Books.Homology.Unit08.Localization

/-!
# Derived Categories, Chapter 5: localization of triangulated categories

The source's localization process is expressed using Mathlib's canonical
morphism properties, calculus-of-fractions localizations, and induced
triangulated structures.  The declarations below record the source-facing
interfaces; substantive proofs are deferred to the proving stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit27
open Formalization.Books.Derived.Unit03
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u'

namespace Formalization.Books.Derived.Unit05

/-! ## Compatibility conditions -/

section Compatibility

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/- Mathlib's `IsCompatibleWithTriangulation` is exactly the source's MS5/MS6
   interface, with MS5 expressed for every integer shift. -/
abbrev CompatibleWithTriangulation (S : MorphismProperty C) :=
  MorphismProperty.IsCompatibleWithTriangulation S

/- The source's LMS2 and RMS2 are not separate Mathlib classes: the calculus
   classes package them together with the corresponding cancellation axiom.
   These two predicates retain the exact displayed Ore-square statements. -/
def LeftOreCondition (S : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z W : C⦄ (t : X ⟶ Z) (g : X ⟶ Y), S t →
    ∃ (s : Y ⟶ W) (f : Z ⟶ W), S s ∧ t ≫ f = g ≫ s

def RightOreCondition (S : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z W : C⦄ (g : X ⟶ Y) (s : Y ⟶ W), S s →
    ∃ (t : X ⟶ Z) (f : Z ⟶ W), S t ∧ t ≫ f = g ≫ s

theorem localization_conditions_contains_isomorphisms
    {S : MorphismProperty C} [S.ContainsIdentities] [CompatibleWithTriangulation S] :
    MorphismProperty.isomorphisms C ≤ S := by
  intro X Y f hf
  let T₁ : Triangle C :=
    Triangle.mk (0 : (0 : C) ⟶ X) (𝟙 X)
      (0 : X ⟶ (shiftFunctor C (1 : ℤ)).obj (0 : C))
  let T₂ : Triangle C :=
    Triangle.mk (0 : (0 : C) ⟶ X) f
      (0 : Y ⟶ (shiftFunctor C (1 : ℤ)).obj (0 : C))
  have hT₁ : T₁ ∈ distTriang C := by
    apply (Triangle.distinguished_iff_of_isZero₁ T₁ (isZero_zero _)).2
    dsimp [T₁]
    exact (inferInstance : IsIso (𝟙 X))
  have hT₂ : T₂ ∈ distTriang C := by
    apply (Triangle.distinguished_iff_of_isZero₁ T₂ (isZero_zero _)).2
    dsimp [T₂]
    exact hf
  have hex : ∃ c : X ⟶ Y, S c ∧
      𝟙 X ≫ c = 𝟙 X ≫ f ∧
        (0 : X ⟶ (shiftFunctor C (1 : ℤ)).obj (0 : C)) ≫
            (shiftFunctor C (1 : ℤ)).map (𝟙 (0 : C)) =
          c ≫ (0 : Y ⟶ (shiftFunctor C (1 : ℤ)).obj (0 : C)) := by
    obtain ⟨c, hc, h₂, h₃⟩ :=
      MorphismProperty.IsCompatibleWithTriangulation.compatible_with_triangulation
        T₁ T₂ hT₁ hT₂ (𝟙 (0 : C)) (𝟙 X) (S.id_mem _) (S.id_mem _) (by
          change (0 : (0 : C) ⟶ X) ≫ 𝟙 X = 𝟙 (0 : C) ≫ (0 : (0 : C) ⟶ X)
          simp)
    refine ⟨c, hc, ?_, ?_⟩
    · simpa only [T₁, T₂, Triangle.mk] using h₂
    · simpa only [T₁, T₂, Triangle.mk] using h₃
  obtain ⟨c, hc, h₂, h₃⟩ := hex
  rw [Category.id_comp, Category.id_comp] at h₂
  exact h₂ ▸ hc

theorem localization_conditions_ms2
    {S : MorphismProperty C} [S.IsMultiplicative]
    [CompatibleWithTriangulation S] :
    LeftOreCondition S ∧ RightOreCondition S := by
  sorry

/- The source's MS5 remark, recorded using the canonical shift-compatibility
   class and its equivalent one-way closure formulation under MS1 and MS6. -/
def AllIntegerShifts (S : MorphismProperty C) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), S f → ∀ n : ℤ, S (f⟦n⟧')

theorem ms5_iff_all_integer_shifts
    {S : MorphismProperty C} [S.IsMultiplicative]
    [CompatibleWithTriangulation S] :
    AllIntegerShifts S ↔ MorphismProperty.IsCompatibleWithShift S ℤ := by
  constructor
  · intro _
    infer_instance
  · intro _ X Y f hf n
    exact MorphismProperty.shift S hf n

end Compatibility

/-! ## Systems detected by exact and homological functors -/

section ExactFunctorLocalization

variable {C D : Type*} [Category* C] [Category* D]
  [AdditiveCategory C] [AdditiveCategory D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

def exactFunctorMorphismProperty (F : C ⥤ D) : MorphismProperty C :=
  (MorphismProperty.isomorphisms D).inverseImage F

set_option backward.isDefEq.respectTransparency false in
theorem exactFunctorMorphismProperty_saturated
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    SaturatedMultiplicativeSystem (exactFunctorMorphismProperty F) ∧
      CompatibleWithTriangulation (exactFunctorMorphismProperty F) := by
  let W := exactFunctorMorphismProperty F
  have hleft : W.HasLeftCalculusOfFractions := by
    refine { id_mem := ?_, comp_mem := ?_, exists_leftFraction := ?_, ext := ?_ }
    · intro X
      change IsIso (F.map (𝟙 X))
      infer_instance
    · intro X Y Z f g hf hg
      change IsIso (F.map f) at hf
      change IsIso (F.map g) at hg
      change IsIso (F.map (f ≫ g))
      rw [F.map_comp]
      infer_instance
    · intro X Y φ
      obtain ⟨s, hs, f⟩ := φ
      change IsIso (F.map s) at hs
      obtain ⟨Q, d, h, hT⟩ := distinguished_cocone_triangle s
      have hQ : IsZero (F.obj Q) := by
        apply Triangle.isZero₃_of_isIso₁ (F.mapTriangle.obj (Triangle.mk s d h))
          (F.map_distinguished _ hT)
        exact hs
      obtain ⟨Y', t, k, hT'⟩ := distinguished_cocone_triangle₂
        (h ≫ f⟦(1 : ℤ)⟧')
      obtain ⟨g, hg₁, hg₂⟩ := complete_distinguished_triangle_morphism₂
        (Triangle.mk s d h) (Triangle.mk t k (h ≫ f⟦(1 : ℤ)⟧')) hT hT' f (𝟙 Q) (by
          simpa only [Triangle.mk_mor₃, Triangle.mk_obj₁, Triangle.mk_obj₃] using
            (Category.id_comp (h ≫ (shiftFunctor C 1).map f)).symm)
      have ht : IsIso (F.map t) := by
        apply (Triangle.isZero₃_iff_isIso₁
          (F.mapTriangle.obj (Triangle.mk t k (h ≫ f⟦(1 : ℤ)⟧')))
          (F.map_distinguished _ hT')).1
        exact hQ
      exact ⟨MorphismProperty.LeftFraction.mk g t ht, hg₁.symm⟩
    · rintro X' X Y f₁ f₂ s hs h
      change IsIso (F.map s) at hs
      have hdiff : s ≫ (f₁ - f₂) = 0 := by
        rw [comp_sub, h, sub_self]
      obtain ⟨Q, d, k, hT⟩ := distinguished_cocone_triangle s
      have hQ : IsZero (F.obj Q) := by
        apply Triangle.isZero₃_of_isIso₁ (F.mapTriangle.obj (Triangle.mk s d k))
          (F.map_distinguished _ hT)
        exact hs
      obtain ⟨i, hi⟩ := Triangle.yoneda_exact₂ _ hT (f₁ - f₂) hdiff
      obtain ⟨Y', t, l, hT'⟩ := distinguished_cocone_triangle i
      have ht : IsIso (F.map t) := by
        apply (Triangle.isZero₁_iff_isIso₂
          (F.mapTriangle.obj (Triangle.mk i t l))
          (F.map_distinguished _ hT')).1
        exact hQ
      refine ⟨Y', t, ht, ?_⟩
      have eq := comp_distTriang_mor_zero₁₂ _ hT'
      simp only [Triangle.mk_mor₂] at hi
      simp only [Triangle.mk_mor₁, Triangle.mk_mor₂] at eq
      rw [← sub_eq_zero, ← sub_comp, hi]
      simp only [Category.assoc, eq, comp_zero]
  have hright : W.HasRightCalculusOfFractions := by
    refine { id_mem := ?_, comp_mem := ?_, exists_rightFraction := ?_, ext := ?_ }
    · intro X
      change IsIso (F.map (𝟙 X))
      infer_instance
    · intro X Y Z f g hf hg
      change IsIso (F.map f) at hf
      change IsIso (F.map g) at hg
      change IsIso (F.map (f ≫ g))
      rw [F.map_comp]
      infer_instance
    · intro X Y φ
      obtain ⟨f, s, hs⟩ := φ
      change IsIso (F.map s) at hs
      obtain ⟨Q, d, h, hT⟩ := distinguished_cocone_triangle s
      have hQ : IsZero (F.obj Q) := by
        apply Triangle.isZero₃_of_isIso₁ (F.mapTriangle.obj (Triangle.mk s d h))
          (F.map_distinguished _ hT)
        exact hs
      obtain ⟨X', t, k, hT'⟩ := distinguished_cocone_triangle₁ (f ≫ d)
      obtain ⟨g, hg₁, hg₂⟩ := complete_distinguished_triangle_morphism₁
        (Triangle.mk t (f ≫ d) k) (Triangle.mk s d h) hT' hT f (𝟙 Q) (by
          simpa only [Triangle.mk_mor₂] using (Category.comp_id (f ≫ d)))
      have ht : IsIso (F.map t) := by
        apply (Triangle.isZero₃_iff_isIso₁
          (F.mapTriangle.obj (Triangle.mk t (f ≫ d) k))
          (F.map_distinguished _ hT')).1
        exact hQ
      exact ⟨MorphismProperty.RightFraction.mk t ht g, hg₁⟩
    · rintro X Y Y' f₁ f₂ s hs h
      change IsIso (F.map s) at hs
      have hdiff : (f₁ - f₂) ≫ s = 0 := by
        rw [sub_comp, h, sub_self]
      obtain ⟨R, r, k, hT⟩ := distinguished_cocone_triangle₁ s
      have hR : IsZero (F.obj R) := by
        apply Triangle.isZero₁_of_isIso₂
          (F.mapTriangle.obj (Triangle.mk r s k))
          (F.map_distinguished _ hT)
        exact hs
      obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ hT (f₁ - f₂) hdiff
      obtain ⟨X', t, l, hT'⟩ := distinguished_cocone_triangle₁ q
      have ht : IsIso (F.map t) := by
        apply (Triangle.isZero₃_iff_isIso₁
          (F.mapTriangle.obj (Triangle.mk t q l))
          (F.map_distinguished _ hT')).1
        exact hR
      refine ⟨X', t, ht, ?_⟩
      have eq := comp_distTriang_mor_zero₁₂ _ hT'
      simp only [Triangle.mk_mor₁, Triangle.mk_mor₂] at hq eq
      rw [← sub_eq_zero, ← comp_sub, hq]
      simp only [← Category.assoc, eq, zero_comp]
  have hsat : SaturatedMultiplicativeSystem W := by
    refine ⟨⟨hleft, hright⟩, ?_⟩
    intro X Y Z T f g h hfg hgh
    change IsIso (F.map (f ≫ g)) at hfg
    change IsIso (F.map (g ≫ h)) at hgh
    change IsIso (F.map g)
    rw [F.map_comp] at hfg hgh
    let := hfg
    let := hgh
    exact isIso_of_adjacent_composites (F.map f) (F.map g) (F.map h)
  have hshift : W.IsCompatibleWithShift ℤ := by
    refine ⟨?_⟩
    intro n
    ext X Y f
    change IsIso (F.map ((shiftFunctor C n).map f)) ↔ IsIso (F.map f)
    constructor
    · intro hf
      let : IsIso (F.map ((shiftFunctor C n).map f)) := hf
      have : IsIso ((F.commShiftIso n).hom.app X) := inferInstance
      have : IsIso ((F.commShiftIso n).hom.app Y) := inferInstance
      have : IsIso (F.map ((shiftFunctor C n).map f) ≫
          (F.commShiftIso n).hom.app Y) := inferInstance
      have : IsIso ((shiftFunctor C n ⋙ F).map f) := by
        change IsIso (F.map ((shiftFunctor C n).map f))
        infer_instance
      have : IsIso ((F.commShiftIso n).hom.app X ≫
          (shiftFunctor D n).map (F.map f)) := by
        change IsIso ((F.commShiftIso n).hom.app X ≫ (F ⋙ shiftFunctor D n).map f)
        rw [← (F.commShiftIso n).hom.naturality f]
        infer_instance
      have : IsIso ((shiftFunctor D n).map (F.map f)) :=
        IsIso.of_isIso_comp_left
          ((F.commShiftIso n).hom.app X) ((shiftFunctor D n).map (F.map f))
      exact isIso_of_reflects_iso (F.map f) (shiftFunctor D n)
    · intro hf
      let : IsIso (F.map f) := hf
      have : IsIso ((F.commShiftIso n).hom.app X) := inferInstance
      have : IsIso ((F.commShiftIso n).hom.app Y) := inferInstance
      have : IsIso ((F.commShiftIso n).hom.app X ≫
          (shiftFunctor D n).map (F.map f)) := inferInstance
      have : IsIso ((F ⋙ shiftFunctor D n).map f) := by
        change IsIso ((shiftFunctor D n).map (F.map f))
        infer_instance
      have : IsIso (F.map ((shiftFunctor C n).map f) ≫
          (F.commShiftIso n).hom.app Y) := by
        change IsIso ((shiftFunctor C n ⋙ F).map f ≫
          (F.commShiftIso n).hom.app Y)
        rw [(F.commShiftIso n).hom.naturality f]
        infer_instance
      exact IsIso.of_isIso_comp_right
        (F.map ((shiftFunctor C n).map f)) ((F.commShiftIso n).hom.app Y)
  let : W.IsCompatibleWithShift ℤ := hshift
  have hcompat : CompatibleWithTriangulation W := by
    refine ⟨?_⟩
    intro T₁ T₂ hT₁ hT₂ a b ha hb comm
    change IsIso (F.map a) at ha
    change IsIso (F.map b) at hb
    obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
      T₁ T₂ hT₁ hT₂ a b comm
    let φ := Triangle.homMk T₁ T₂ a b c comm hc₂ hc₃
    refine ⟨c, ?_, hc₂, hc₃⟩
    change IsIso (F.map c)
    change IsIso (F.mapTriangle.map φ).hom₃
    apply isIso₃_of_isIso₁₂ (F.mapTriangle.map φ)
      (F.map_distinguished _ hT₁) (F.map_distinguished _ hT₂)
    · exact ha
    · exact hb
  exact ⟨by simpa [W] using hsat, by simpa [W] using hcompat⟩
end ExactFunctorLocalization

section HomologicalFunctorLocalization

variable {C A : Type*} [Category* C] [Category* A]
  [AdditiveCategory C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

def homologicalFunctorMorphismProperty (H : C ⥤ A) : MorphismProperty C :=
  fun _ _ f => ∀ i : ℤ, IsIso ((homologicalDegree H i).map f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem homologicalFunctorMorphismProperty_saturated
    (H : C ⥤ A) [H.IsHomological] :
    SaturatedMultiplicativeSystem (homologicalFunctorMorphismProperty H) ∧
      CompatibleWithTriangulation (homologicalFunctorMorphismProperty H) := by
  let : H.ShiftSequence ℤ := Functor.ShiftSequence.tautological H ℤ
  let W := homologicalFunctorMorphismProperty H
  let P := H.homologicalKernel
  have hW_trW : W = P.trW := by
    ext X Y f
    change (∀ i : ℤ, IsIso ((homologicalDegree H i).map f)) ↔ P.trW f
    change (∀ i : ℤ, IsIso ((H.shift i).map f)) ↔ P.trW f
    exact (H.mem_homologicalKernel_trW_iff f).symm
  have hleft : W.HasLeftCalculusOfFractions := by
    refine { id_mem := ?_, comp_mem := ?_, exists_leftFraction := ?_, ext := ?_ }
    · intro X
      change ∀ i : ℤ, IsIso ((homologicalDegree H i).map (𝟙 X))
      intro i
      infer_instance
    · intro X Y Z f g hf hg
      change ∀ i : ℤ, IsIso ((homologicalDegree H i).map (f ≫ g))
      intro i
      have := hf i
      have := hg i
      rw [Functor.map_comp]
      infer_instance
    · intro X Y φ
      obtain ⟨s, hs, f⟩ := φ
      have hs' : P.trW s := by
        exact hW_trW ▸ hs
      obtain ⟨Q, d, h, hT⟩ := distinguished_cocone_triangle s
      have hQ : P Q := (P.trW_iff_of_distinguished _ hT).1 hs'
      obtain ⟨Y', t, k, hT'⟩ := distinguished_cocone_triangle₂
        (h ≫ f⟦(1 : ℤ)⟧')
      obtain ⟨g, hg₁, hg₂⟩ := complete_distinguished_triangle_morphism₂
        (Triangle.mk s d h) (Triangle.mk t k (h ≫ f⟦(1 : ℤ)⟧')) hT hT' f (𝟙 Q) (by
          simpa only [Triangle.mk_mor₃, Triangle.mk_obj₁, Triangle.mk_obj₃] using
            (Category.id_comp (h ≫ (shiftFunctor C 1).map f)).symm)
      have ht' : P.trW t := by
        change P.trW (Triangle.mk t k (h ≫ f⟦(1 : ℤ)⟧')).mor₁
        exact (P.trW_iff_of_distinguished _ hT').2 hQ
      have ht : W t := by
        exact hW_trW.symm ▸ ht'
      exact ⟨MorphismProperty.LeftFraction.mk g t ht, hg₁.symm⟩
    · rintro X' X Y f₁ f₂ s hs h
      have hs' : P.trW s := by
        exact hW_trW ▸ hs
      have hdiff : s ≫ (f₁ - f₂) = 0 := by
        rw [comp_sub, h, sub_self]
      obtain ⟨Q, d, k, hT⟩ := distinguished_cocone_triangle s
      have hQ : P Q := (P.trW_iff_of_distinguished _ hT).1 hs'
      obtain ⟨i, hi⟩ := Triangle.yoneda_exact₂ _ hT (f₁ - f₂) hdiff
      obtain ⟨Y', t, l, hT'⟩ := distinguished_cocone_triangle i
      have ht' : P.trW t := by
        change P.trW (Triangle.mk i t l).mor₂
        exact (P.trW_iff_of_distinguished' _ hT').2 hQ
      have ht : W t := by
        exact hW_trW.symm ▸ ht'
      refine ⟨Y', t, ht, ?_⟩
      have eq := comp_distTriang_mor_zero₁₂ _ hT'
      simp only [Triangle.mk_mor₂] at hi
      simp only [Triangle.mk_mor₁, Triangle.mk_mor₂] at eq
      rw [← sub_eq_zero, ← sub_comp, hi]
      simp only [Category.assoc, eq, comp_zero]
  have hright : W.HasRightCalculusOfFractions := by
    refine { id_mem := ?_, comp_mem := ?_, exists_rightFraction := ?_, ext := ?_ }
    · intro X
      change ∀ i : ℤ, IsIso ((homologicalDegree H i).map (𝟙 X))
      intro i
      infer_instance
    · intro X Y Z f g hf hg
      change ∀ i : ℤ, IsIso ((homologicalDegree H i).map (f ≫ g))
      intro i
      have := hf i
      have := hg i
      rw [Functor.map_comp]
      infer_instance
    · intro X Y φ
      obtain ⟨f, s, hs⟩ := φ
      have hs' : P.trW s := by
        exact hW_trW ▸ hs
      obtain ⟨Q, d, h, hT⟩ := distinguished_cocone_triangle s
      have hQ : P Q := (P.trW_iff_of_distinguished _ hT).1 hs'
      obtain ⟨X', t, k, hT'⟩ := distinguished_cocone_triangle₁ (f ≫ d)
      obtain ⟨g, hg₁, hg₂⟩ := complete_distinguished_triangle_morphism₁
        (Triangle.mk t (f ≫ d) k) (Triangle.mk s d h) hT' hT f (𝟙 Q) (by
          simpa only [Triangle.mk_mor₂] using (Category.comp_id (f ≫ d)))
      have ht' : P.trW t := by
        change P.trW (Triangle.mk t (f ≫ d) k).mor₁
        exact (P.trW_iff_of_distinguished _ hT').2 hQ
      have ht : W t := by
        exact hW_trW.symm ▸ ht'
      exact ⟨MorphismProperty.RightFraction.mk t ht g, hg₁⟩
    · rintro X Y Y' f₁ f₂ s hs h
      have hs' : P.trW s := by
        exact hW_trW ▸ hs
      have hdiff : (f₁ - f₂) ≫ s = 0 := by
        rw [sub_comp, h, sub_self]
      obtain ⟨R, r, k, hT⟩ := distinguished_cocone_triangle₁ s
      have hR : P R := (P.trW_iff_of_distinguished' _ hT).1 hs'
      obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ hT (f₁ - f₂) hdiff
      obtain ⟨X', t, l, hT'⟩ := distinguished_cocone_triangle₁ q
      have ht' : P.trW t := by
        change P.trW (Triangle.mk t q l).mor₁
        exact (P.trW_iff_of_distinguished _ hT').2 hR
      have ht : W t := by
        exact hW_trW.symm ▸ ht'
      refine ⟨X', t, ht, ?_⟩
      have eq := comp_distTriang_mor_zero₁₂ _ hT'
      simp only [Triangle.mk_mor₁, Triangle.mk_mor₂] at hq eq
      rw [← sub_eq_zero, ← comp_sub, hq]
      simp only [← Category.assoc, eq, zero_comp]
  have hsat : SaturatedMultiplicativeSystem W := by
    refine ⟨⟨hleft, hright⟩, ?_⟩
    intro X Y Z T f g h hfg hgh
    change (∀ i : ℤ, IsIso ((homologicalDegree H i).map (f ≫ g))) at hfg
    change (∀ i : ℤ, IsIso ((homologicalDegree H i).map (g ≫ h))) at hgh
    change ∀ i : ℤ, IsIso ((homologicalDegree H i).map g)
    intro i
    have hfg' := hfg i
    have hgh' := hgh i
    rw [Functor.map_comp] at hfg' hgh'
    let := hfg'
    let := hgh'
    exact isIso_of_adjacent_composites
      ((homologicalDegree H i).map f)
      ((homologicalDegree H i).map g)
      ((homologicalDegree H i).map h)
  have hshift : W.IsCompatibleWithShift ℤ := by
    refine ⟨?_⟩
    intro n
    ext X Y f
    change (∀ i : ℤ, IsIso ((H.shift i).map ((shiftFunctor C n).map f))) ↔
      ∀ i : ℤ, IsIso ((H.shift i).map f)
    constructor
    · intro hf i
      let j : ℤ := i - n
      have hj : IsIso ((H.shift j).map ((shiftFunctor C n).map f)) := hf j
      let := hj
      let e := H.shiftIso n j i (by dsimp [j]; abel)
      have he : IsIso ((shiftFunctor C n ⋙ H.shift j).map f ≫ e.hom.app Y) := by
        change IsIso ((H.shift j).map ((shiftFunctor C n).map f) ≫ e.hom.app Y)
        infer_instance
      have he' := he
      rw [e.hom.naturality f] at he'
      let := he'
      exact IsIso.of_isIso_comp_left (e.hom.app X) ((H.shift i).map f)
    · intro hf i
      have hi : IsIso ((H.shift (n + i)).map f) := hf (n + i)
      let := hi
      let e := H.shiftIso n i (n + i) rfl
      have he : IsIso (e.hom.app X ≫ (H.shift (n + i)).map f) := by
        infer_instance
      have he' := he
      rw [← e.hom.naturality f] at he'
      have he'' : IsIso ((H.shift i).map ((shiftFunctor C n).map f) ≫ e.hom.app Y) := by
        change IsIso ((shiftFunctor C n ⋙ H.shift i).map f ≫ e.hom.app Y)
        exact he'
      let := he''
      exact IsIso.of_isIso_comp_right
        ((H.shift i).map ((shiftFunctor C n).map f)) (e.hom.app Y)
  let : W.IsCompatibleWithShift ℤ := hshift
  have hcompat : CompatibleWithTriangulation W := by
    refine ⟨?_⟩
    intro T₁ T₂ hT₁ hT₂ a b ha hb comm
    change (∀ i : ℤ, IsIso ((H.shift i).map a)) at ha
    change (∀ i : ℤ, IsIso ((H.shift i).map b)) at hb
    obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
      T₁ T₂ hT₁ hT₂ a b comm
    refine ⟨c, ?_, hc₂, hc₃⟩
    change ∀ i : ℤ, IsIso ((H.shift i).map c)
    intro i
    let φ : T₁ ⟶ T₂ := Triangle.homMk T₁ T₂ a b c comm hc₂ hc₃
    let R₁ := H.homologySequenceComposableArrows₅ T₁ i (i + 1) rfl
    let R₂ := H.homologySequenceComposableArrows₅ T₂ i (i + 1) rfl
    have h₁₀ : R₁.obj' 0 = (H.shift i).obj T₁.obj₁ := by rfl
    have h₁₁ : R₁.obj' 1 = (H.shift i).obj T₁.obj₂ := by rfl
    have h₁₂ : R₁.obj' 2 = (H.shift i).obj T₁.obj₃ := by rfl
    have h₁₃ : R₁.obj' 3 = (H.shift (i + 1)).obj T₁.obj₁ := by rfl
    have h₁₄ : R₁.obj' 4 = (H.shift (i + 1)).obj T₁.obj₂ := by rfl
    have h₁₅ : R₁.obj' 5 = (H.shift (i + 1)).obj T₁.obj₃ := by rfl
    have h₂₀ : R₂.obj' 0 = (H.shift i).obj T₂.obj₁ := by rfl
    have h₂₁ : R₂.obj' 1 = (H.shift i).obj T₂.obj₂ := by rfl
    have h₂₂ : R₂.obj' 2 = (H.shift i).obj T₂.obj₃ := by rfl
    have h₂₃ : R₂.obj' 3 = (H.shift (i + 1)).obj T₂.obj₁ := by rfl
    have h₂₄ : R₂.obj' 4 = (H.shift (i + 1)).obj T₂.obj₂ := by rfl
    have h₂₅ : R₂.obj' 5 = (H.shift (i + 1)).obj T₂.obj₃ := by rfl
    have hm₁₀ : R₁.map' 0 1 =
        eqToHom h₁₀ ≫ (H.shift i).map T₁.mor₁ ≫ eqToHom h₁₁.symm := by
      dsimp [R₁, Functor.homologySequenceComposableArrows₅,
        ComposableArrows.map', ComposableArrows.precomp,
        ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
      simp only [Category.id_comp, Category.comp_id]
    have hm₁₁ : R₁.map' 1 2 =
        eqToHom h₁₁ ≫ (H.shift i).map T₁.mor₂ ≫ eqToHom h₁₂.symm := by
      dsimp [R₁, Functor.homologySequenceComposableArrows₅,
        ComposableArrows.map', ComposableArrows.precomp,
        ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
      simp only [Category.id_comp, Category.comp_id]
    have hm₁₂ : R₁.map' 2 3 =
        eqToHom h₁₂ ≫ H.homologySequenceδ T₁ i (i + 1) rfl ≫ eqToHom h₁₃.symm := by
      dsimp [R₁, Functor.homologySequenceComposableArrows₅,
        ComposableArrows.map', ComposableArrows.precomp,
        ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
      simp only [Category.id_comp, Category.comp_id]
    have hm₁₃ : R₁.map' 3 4 =
        eqToHom h₁₃ ≫ (H.shift (i + 1)).map T₁.mor₁ ≫ eqToHom h₁₄.symm := by
      dsimp [R₁, Functor.homologySequenceComposableArrows₅,
        ComposableArrows.map', ComposableArrows.precomp,
        ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
      simp only [Category.id_comp, Category.comp_id]
    have hm₁₄ : R₁.map' 4 5 =
        eqToHom h₁₄ ≫ (H.shift (i + 1)).map T₁.mor₂ ≫ eqToHom h₁₅.symm := by
      dsimp [R₁, Functor.homologySequenceComposableArrows₅,
        ComposableArrows.map', ComposableArrows.precomp,
        ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
      simp only [Category.id_comp, Category.comp_id]
    have hm₂₀ : R₂.map' 0 1 =
        eqToHom h₂₀ ≫ (H.shift i).map T₂.mor₁ ≫ eqToHom h₂₁.symm := by
      dsimp [R₂, Functor.homologySequenceComposableArrows₅,
        ComposableArrows.map', ComposableArrows.precomp,
        ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
      simp only [Category.id_comp, Category.comp_id]
    have hm₂₁ : R₂.map' 1 2 =
        eqToHom h₂₁ ≫ (H.shift i).map T₂.mor₂ ≫ eqToHom h₂₂.symm := by
      dsimp [R₂, Functor.homologySequenceComposableArrows₅,
        ComposableArrows.map', ComposableArrows.precomp,
        ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
      simp only [Category.id_comp, Category.comp_id]
    have hm₂₂ : R₂.map' 2 3 =
        eqToHom h₂₂ ≫ H.homologySequenceδ T₂ i (i + 1) rfl ≫ eqToHom h₂₃.symm := by
      dsimp [R₂, Functor.homologySequenceComposableArrows₅,
        ComposableArrows.map', ComposableArrows.precomp,
        ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
      simp only [Category.id_comp, Category.comp_id]
    have hm₂₃ : R₂.map' 3 4 =
        eqToHom h₂₃ ≫ (H.shift (i + 1)).map T₂.mor₁ ≫ eqToHom h₂₄.symm := by
      dsimp [R₂, Functor.homologySequenceComposableArrows₅,
        ComposableArrows.map', ComposableArrows.precomp,
        ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
      simp only [Category.id_comp, Category.comp_id]
    have hm₂₄ : R₂.map' 4 5 =
        eqToHom h₂₄ ≫ (H.shift (i + 1)).map T₂.mor₂ ≫ eqToHom h₂₅.symm := by
      dsimp [R₂, Functor.homologySequenceComposableArrows₅,
        ComposableArrows.map', ComposableArrows.precomp,
        ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
      simp only [Category.id_comp, Category.comp_id]
    let ψ : R₁ ⟶ R₂ := ComposableArrows.homMk₅
      (eqToHom h₁₀ ≫ (H.shift i).map a ≫ eqToHom h₂₀.symm)
      (eqToHom h₁₁ ≫ (H.shift i).map b ≫ eqToHom h₂₁.symm)
      (eqToHom h₁₂ ≫ (H.shift i).map c ≫ eqToHom h₂₂.symm)
      (eqToHom h₁₃ ≫ (H.shift (i + 1)).map a ≫ eqToHom h₂₃.symm)
      (eqToHom h₁₄ ≫ (H.shift (i + 1)).map b ≫ eqToHom h₂₄.symm)
      (eqToHom h₁₅ ≫ (H.shift (i + 1)).map c ≫ eqToHom h₂₅.symm)
      (by
        rw [hm₁₀, hm₂₀]
        simpa only [eqToHom_trans, eqToHom_refl, Category.id_comp,
          Category.comp_id, Category.assoc, Functor.map_comp] using
          congrArg ((H.shift i).map) comm)
      (by
        rw [hm₁₁, hm₂₁]
        simpa only [eqToHom_trans, eqToHom_refl, Category.id_comp,
          Category.comp_id, Category.assoc, Functor.map_comp] using
          congrArg ((H.shift i).map) hc₂)
      (by
        rw [hm₁₂, hm₂₂]
        simpa [φ, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id,
          Category.assoc] using
          (H.homologySequenceδ_naturality T₁ T₂ φ i (i + 1) rfl).symm)
      (by
        rw [hm₁₃, hm₂₃]
        simpa only [eqToHom_trans, eqToHom_refl, Category.id_comp,
          Category.comp_id, Category.assoc, Functor.map_comp] using
          congrArg ((H.shift (i + 1)).map) comm)
      (by
        rw [hm₁₄, hm₂₄]
        simpa only [eqToHom_trans, eqToHom_refl, Category.id_comp,
          Category.comp_id, Category.assoc, Functor.map_comp] using
          congrArg ((H.shift (i + 1)).map) hc₂)
    have hR₁ : R₁.Exact := by
      exact H.homologySequenceComposableArrows₅_exact T₁ hT₁ i (i + 1) rfl
    have hR₂ : R₂.Exact := by
      exact H.homologySequenceComposableArrows₅_exact T₂ hT₂ i (i + 1) rfl
    have hψ := CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono'
      (n := 5) (k := 0) (by norm_num) hR₁ hR₂ ψ 0 1 2 3 4 rfl rfl rfl rfl rfl
      (by
      let := ha i
      dsimp [ψ]
      infer_instance)
      (by
      let := hb i
      dsimp [ψ]
      infer_instance)
      (by
      let := ha (i + 1)
      dsimp [ψ]
      infer_instance)
      (by
      let := hb (i + 1)
      dsimp [ψ]
      infer_instance)
    have hcomp : IsIso
        (eqToHom h₁₂ ≫ (H.shift i).map c ≫ eqToHom h₂₂.symm) := by
      simpa only [ψ, ComposableArrows.homMk₅_app_two] using hψ
    let := hcomp
    have hmid : IsIso
        ((H.shift i).map c ≫ eqToHom h₂₂.symm) :=
      IsIso.of_isIso_comp_left (eqToHom h₁₂)
        ((H.shift i).map c ≫ eqToHom h₂₂.symm)
    let := hmid
    exact IsIso.of_isIso_comp_right ((H.shift i).map c) (eqToHom h₂₂.symm)
  exact ⟨by simpa [W] using hsat, by simpa [W] using hcompat⟩
end HomologicalFunctorLocalization

/-! ## The localized pretriangulated structure and its universal property -/

section LocalizationConstruction

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {S : MorphismProperty C} [LeftMultiplicativeSystem S]
  [RightMultiplicativeSystem S] [CompatibleWithTriangulation S]

/- This predicate is the source's uniqueness condition: the canonical
   localized shift is used, and the localization functor is exact for the
   candidate pretriangulated structure. -/
def IsLocalizationPretriangulatedStructure
    (P : Pretriangulated S.Localization) : Prop :=
  letI : Pretriangulated S.Localization := P
  Functor.IsTriangulated S.Q

omit [RightMultiplicativeSystem S] in
theorem localization_pretriangulated_exists_unique :
    ∃! P : Pretriangulated S.Localization,
      IsLocalizationPretriangulatedStructure (S := S) P := by
  let P₀ : Pretriangulated S.Localization :=
    CategoryTheory.Triangulated.Localization.pretriangulated S.Q S
  have hP₀ : IsLocalizationPretriangulatedStructure (S := S) P₀ := by
    change (let : Pretriangulated S.Localization := P₀; Functor.IsTriangulated S.Q)
    let : Pretriangulated S.Localization := P₀
    infer_instance
  refine ⟨P₀, hP₀, ?_⟩
  intro P hP
  change (let : Pretriangulated S.Localization := P; Functor.IsTriangulated S.Q) at hP
  let : Pretriangulated S.Localization := P
  change Functor.IsTriangulated S.Q at hP
  let : Functor.IsTriangulated S.Q := hP
  let : S.Q.mapArrow.EssSurj := Localization.essSurj_mapArrow S.Q S
  have hPdist : P.distinguishedTriangles = S.Q.essImageDistTriang := by
    ext T
    exact Functor.distTriang_iff S.Q T
  have hP₀dist : P₀.distinguishedTriangles = S.Q.essImageDistTriang := by
    rfl
  have hdist : P.distinguishedTriangles = P₀.distinguishedTriangles := hPdist.trans hP₀dist.symm
  have hExt : ∀ (P₁ P₂ : Pretriangulated S.Localization),
      P₁.distinguishedTriangles = P₂.distinguishedTriangles → P₁ = P₂ := by
    intro P₁ P₂ h
    cases P₁
    cases P₂
    congr
  exact hExt P P₀ hdist

@[instance_reducible]
noncomputable def localizationFunctorCommShift : S.Q.CommShift ℤ :=
  inferInstance

omit [RightMultiplicativeSystem S] in
theorem localizationFunctor_exact : S.Q.IsTriangulated := by
  infer_instance

omit [RightMultiplicativeSystem S] in
theorem localization_triangulated [CategoryTheory.IsTriangulated C] :
    CategoryTheory.IsTriangulated S.Localization := by
  infer_instance

/- The construction and its factorization maps use the canonical localization
   construction. -/
noncomputable def localizationFactor {E : Type*} [Category* E]
    (F : C ⥤ E) (hF : S.IsInvertedBy F) : S.Localization ⥤ E :=
  Localization.Construction.lift F hF

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LeftMultiplicativeSystem S] [RightMultiplicativeSystem S]
    [CompatibleWithTriangulation S] in
theorem localizationFactor_fac {E : Type*} [Category* E]
    (F : C ⥤ E) (hF : S.IsInvertedBy F) :
    S.Q ⋙ localizationFactor (S := S) F hF = F :=
  Localization.Construction.fac F hF

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LeftMultiplicativeSystem S] [RightMultiplicativeSystem S]
    [CompatibleWithTriangulation S] in
theorem localizationFactor_unique {E : Type*} [Category* E]
    (F₁ F₂ : S.Localization ⥤ E)
    (h : S.Q ⋙ F₁ = S.Q ⋙ F₂) : F₁ = F₂ :=
  Localization.Construction.uniq F₁ F₂ h

def IsExactLocalizationFactor {D : Type*} [Category* D]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : S.Localization ⥤ D) : Prop :=
  ∃ hF : F.CommShift ℤ,
    letI : F.CommShift ℤ := hF
    F.IsTriangulated

omit [RightMultiplicativeSystem S] in
theorem homological_localizationFactor_isHomological
    {A : Type*} [Category* A] [Abelian A]
    (H : C ⥤ A) [H.IsHomological] (hH : S.IsInvertedBy H) :
    (localizationFactor (S := S) H hH).IsHomological := by
  let : Pretriangulated S.Localization :=
    CategoryTheory.Triangulated.Localization.pretriangulated S.Q S
  let : S.Q.IsTriangulated := localizationFunctor_exact (S := S)
  let : S.Q.mapArrow.EssSurj := Localization.essSurj_mapArrow S.Q S
  apply Functor.isHomological_of_localization S.Q (localizationFactor (S := S) H hH) H
  exact eqToIso (localizationFactor_fac (S := S) H hH)

theorem exact_localizationFactor_isExact
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : S.IsInvertedBy F) :
    IsExactLocalizationFactor
      (S := S) (localizationFactor (S := S) F hF) := by
  let prove (hR : RightMultiplicativeSystem S) :
      IsExactLocalizationFactor
        (S := S) (localizationFactor (S := S) F hF) := by
    let : Localization.Lifting S.Q S F (localizationFactor (S := S) F hF) :=
      ⟨eqToIso (localizationFactor_fac (S := S) F hF)⟩
    let : (localizationFactor (S := S) F hF).CommShift ℤ :=
      Functor.commShiftOfLocalization S.Q S ℤ F (localizationFactor (S := S) F hF)
    let : S.Q.mapArrow.EssSurj := Localization.essSurj_mapArrow S.Q S
    refine ⟨inferInstance, ?_⟩
    exact Functor.isTriangulated_of_precomp_iso
      (Localization.Lifting.iso S.Q S F (localizationFactor (S := S) F hF))
  exact prove (inferInstance : RightMultiplicativeSystem S)

end LocalizationConstruction

/-! ## Localization and full triangulated subcategories -/

section LocalizationSubcategory

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

def restrictedMorphismProperty (S : MorphismProperty C)
    (P : ObjectProperty C) : MorphismProperty P.FullSubcategory :=
  S.inverseImage P.ι

theorem restrictedMorphismProperty_saturated
    {S : MorphismProperty C} [CompatibleWithTriangulation S]
    (hS : SaturatedMultiplicativeSystem S) (P : ObjectProperty C)
    [P.IsTriangulated] :
    SaturatedMultiplicativeSystem (restrictedMorphismProperty S P) := by
  let : LeftMultiplicativeSystem S := hS.1.1
  let : RightMultiplicativeSystem S := hS.1.2
  let : AdditiveCategory P.FullSubcategory := {}
  let : AdditiveCategory S.Localization := {}
  let F : P.FullSubcategory ⥤ S.Localization := P.ι ⋙ S.Q
  have hF := exactFunctorMorphismProperty_saturated F
  have hEq : restrictedMorphismProperty S P = exactFunctorMorphismProperty F := by
    ext X Y f
    change S (P.ι.map f) ↔ IsIso (F.map f)
    change S (P.ι.map f) ↔ IsIso (S.Q.map (P.ι.map f))
    have hiff : S (P.ι.map f) ↔ invertedByLocalization S (P.ι.map f) := by
      rw [invertedByLocalization_eq_of_saturated hS]
    exact hiff.trans (by rfl)
  rw [hEq]
  exact hF.1

theorem restrictedMorphismProperty_compatible
    {S : MorphismProperty C} [CompatibleWithTriangulation S] [S.RespectsIso]
    (P : ObjectProperty C) [P.IsTriangulated] :
    CompatibleWithTriangulation (restrictedMorphismProperty S P) := by
  refine { condition := ?_, compatible_with_triangulation := ?_ }
  · intro n
    ext X Y f
    change S (P.ι.map ((shiftFunctor P.FullSubcategory n).map f)) ↔ S (P.ι.map f)
    rw [← MorphismProperty.cancel_left_of_respectsIso S ((P.ι.commShiftIso n).inv.app X)]
    rw [← P.ι.commShiftIso_inv_naturality f n]
    rw [MorphismProperty.cancel_right_of_respectsIso S ((shiftFunctor C n).map (P.ι.map f))
      ((P.ι.commShiftIso n).inv.app Y)]
    exact MorphismProperty.IsCompatibleWithShift.iff S (P.ι.map f) n
  · intro T₁ T₂ hT₁ hT₂ a b ha hb comm
    obtain ⟨c, hc, hc₂, hc₃⟩ :=
      MorphismProperty.IsCompatibleWithTriangulation.compatible_with_triangulation
        (P.ι.mapTriangle.obj T₁) (P.ι.mapTriangle.obj T₂)
        hT₁ hT₂ (P.ι.map a) (P.ι.map b) ha hb (by
          simpa only [Functor.mapTriangle_obj, Functor.map_comp] using! P.ι.congr_map comm)
    refine ⟨P.fullyFaithfulι.preimage c, ?_, ?_, ?_⟩
    · exact hc
    · apply P.ι.map_injective
      simpa only [Functor.mapTriangle_obj, Functor.map_comp, Functor.map_preimage] using! hc₂
    · apply P.ι.map_injective
      rw [← cancel_mono ((Functor.commShiftIso P.ι (1 : ℤ)).hom.app T₂.obj₁)]
      have hc₃' :
          (P.ι.map T₁.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).hom.app T₁.obj₁) ≫
              (shiftFunctor C (1 : ℤ)).map (P.ι.map a) =
            c ≫ (P.ι.map T₂.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).hom.app T₂.obj₁) := by
        simpa only [Functor.mapTriangle_obj, Triangle.mk_mor₃] using! hc₃
      simp only [Functor.map_comp, Functor.comp_obj, Category.assoc,
        Functor.commShiftIso_hom_naturality]
      rw [show P.ι.map (ObjectProperty.homMk c) = c by rfl]
      convert hc₃' using 1; simp only [Category.assoc]; rfl

noncomputable def fullSubcategoryLocalizationFunctor
    (S : MorphismProperty C) (P : ObjectProperty C) :
    (restrictedMorphismProperty S P).Localization ⥤ S.Localization :=
  Localization.Construction.lift (P.ι ⋙ S.Q) (by
    intro X Y f hf
    exact MorphismProperty.Q_inverts S (P.ι.map f) hf)

theorem fullSubcategoryLocalization_isEquivalence
    {S : MorphismProperty C} [CompatibleWithTriangulation S]
    (hS : SaturatedMultiplicativeSystem S) (P : ObjectProperty C)
    [P.IsTriangulated]
    (hP : ∀ X : C, ∃ (X' : P.FullSubcategory)
      (s : P.ι.obj X' ⟶ X), S s) :
    Functor.IsEquivalence (fullSubcategoryLocalizationFunctor S P) := by
  let : LeftMultiplicativeSystem S := hS.1.1
  let : RightMultiplicativeSystem S := hS.1.2
  let : AdditiveCategory P.FullSubcategory := {}
  let : AdditiveCategory S.Localization := {}
  have hWsat : SaturatedMultiplicativeSystem (restrictedMorphismProperty S P) :=
    restrictedMorphismProperty_saturated hS P
  let : LeftMultiplicativeSystem (restrictedMorphismProperty S P) := hWsat.1.1
  let : RightMultiplicativeSystem (restrictedMorphismProperty S P) := hWsat.1.2
  let F := fullSubcategoryLocalizationFunctor S P
  have map_right_fraction
      {X Y : P.FullSubcategory}
      (φ : (restrictedMorphismProperty S P).RightFraction X Y) :
      F.map (φ.map (restrictedMorphismProperty S P).Q
        (Localization.inverts (restrictedMorphismProperty S P).Q
          (restrictedMorphismProperty S P))) =
        (MorphismProperty.RightFraction.mk (P.ι.map φ.s) φ.hs
          (P.ι.map φ.f)).map S.Q (Localization.inverts S.Q S) := by
    have hmap_s :
        F.map ((restrictedMorphismProperty S P).Q.map φ.s) =
          S.Q.map (P.ι.map φ.s) := by
      rfl
    have hmap_f :
        F.map ((restrictedMorphismProperty S P).Q.map φ.f) =
          S.Q.map (P.ι.map φ.f) := by
      rfl
    let : IsIso (F.map ((restrictedMorphismProperty S P).Q.map φ.s)) := by
      rw [hmap_s]
      exact Localization.inverts S.Q S _ φ.hs
    apply (cancel_epi (F.map ((restrictedMorphismProperty S P).Q.map φ.s))).1
    rw [← F.map_comp, φ.map_s_comp_map, hmap_f, hmap_s]
    exact (MorphismProperty.RightFraction.map_s_comp_map
      (MorphismProperty.RightFraction.mk (P.ι.map φ.s) φ.hs
        (P.ι.map φ.f)) S.Q (Localization.inverts S.Q S)).symm
  have hfaithfulQ :
      ∀ {X Y : P.FullSubcategory} (f g :
        (restrictedMorphismProperty S P).Q.obj X ⟶
          (restrictedMorphismProperty S P).Q.obj Y),
        F.map f = F.map g → f = g := by
    intro X Y f g h
    obtain ⟨φ, hφ⟩ :=
      Localization.exists_rightFraction (restrictedMorphismProperty S P).Q
        (restrictedMorphismProperty S P) f
    obtain ⟨ψ, hψ⟩ :=
      Localization.exists_rightFraction (restrictedMorphismProperty S P).Q
        (restrictedMorphismProperty S P) g
    rw [hφ, hψ] at h ⊢
    have hmapφ := map_right_fraction φ
    have hmapψ := map_right_fraction ψ
    rw [hmapφ, hmapψ] at h
    obtain ⟨Z, t₁, t₂, hden, hnum, ht⟩ :=
      (MorphismProperty.RightFraction.map_eq_iff S.Q S
        (MorphismProperty.RightFraction.mk (P.ι.map φ.s) φ.hs
          (P.ι.map φ.f))
        (MorphismProperty.RightFraction.mk (P.ι.map ψ.s) ψ.hs
          (P.ι.map ψ.f))).1 h
    obtain ⟨Z', s, hs⟩ := hP Z
    apply (MorphismProperty.RightFraction.map_eq_iff
      (restrictedMorphismProperty S P).Q
      (restrictedMorphismProperty S P) φ ψ).2
    let u₁ := P.fullyFaithfulι.preimage (s ≫ t₁)
    let u₂ := P.fullyFaithfulι.preimage (s ≫ t₂)
    have hu₁ : P.ι.map u₁ = s ≫ t₁ := by
      change P.ι.map (ObjectProperty.homMk (s ≫ t₁)) = s ≫ t₁
      rfl
    have hu₂ : P.ι.map u₂ = s ≫ t₂ := by
      change P.ι.map (ObjectProperty.homMk (s ≫ t₂)) = s ≫ t₂
      rfl
    refine ⟨Z', u₁, u₂, ?_, ?_, ?_⟩
    · apply P.ι.map_injective
      change P.ι.map u₁ ≫ P.ι.map φ.s =
        P.ι.map u₂ ≫ P.ι.map ψ.s
      rw [hu₁, hu₂]
      simpa only [Category.assoc] using congrArg (fun k => s ≫ k) hden
    · apply P.ι.map_injective
      change P.ι.map u₁ ≫ P.ι.map φ.f =
        P.ι.map u₂ ≫ P.ι.map ψ.f
      rw [hu₁, hu₂]
      simpa only [Category.assoc] using congrArg (fun k => s ≫ k) hnum
    · change S (P.ι.map (u₁ ≫ φ.s))
      rw [Functor.map_comp, hu₁]
      have hst : S (s ≫ t₁ ≫ P.ι.map φ.s) := by
        simpa only [Category.assoc] using S.comp_mem _ _ hs ht
      simpa only [Category.assoc] using hst
  have hfullQ :
      ∀ {X Y : P.FullSubcategory}
        (f : F.obj ((restrictedMorphismProperty S P).Q.obj X) ⟶
          F.obj ((restrictedMorphismProperty S P).Q.obj Y)),
        ∃ g, F.map g = f := by
    intro X Y f
    change S.Q.obj (P.ι.obj X) ⟶ S.Q.obj (P.ι.obj Y) at f
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction S.Q S f
    obtain ⟨Z', s, hs⟩ := hP φ.X'
    let u := P.fullyFaithfulι.preimage (s ≫ φ.s)
    let v := P.fullyFaithfulι.preimage (s ≫ φ.f)
    have hu : restrictedMorphismProperty S P u := by
      change S (P.ι.map u)
      change S (P.ι.map (ObjectProperty.homMk (s ≫ φ.s)))
      rw [show P.ι.map (ObjectProperty.homMk (s ≫ φ.s)) = s ≫ φ.s by rfl]
      exact S.comp_mem _ _ hs φ.hs
    let ψ : (restrictedMorphismProperty S P).RightFraction X Y :=
      MorphismProperty.RightFraction.mk u hu v
    have hψ :
        (MorphismProperty.RightFraction.mk (P.ι.map ψ.s) ψ.hs
          (P.ι.map ψ.f)).map S.Q (Localization.inverts S.Q S) =
          φ.map S.Q (Localization.inverts S.Q S) := by
      apply (MorphismProperty.RightFraction.map_eq_iff S.Q S
        (MorphismProperty.RightFraction.mk (P.ι.map ψ.s) ψ.hs
          (P.ι.map ψ.f)) φ).2
      refine ⟨P.ι.obj Z', 𝟙 _, s, ?_, ?_, ?_⟩
      · change 𝟙 _ ≫ P.ι.map ψ.s = s ≫ φ.s
        simp only [Category.id_comp]
        change P.ι.map (ObjectProperty.homMk (s ≫ φ.s)) = s ≫ φ.s
        rfl
      · change 𝟙 _ ≫ P.ι.map ψ.f = s ≫ φ.f
        simp only [Category.id_comp]
        change P.ι.map (ObjectProperty.homMk (s ≫ φ.f)) = s ≫ φ.f
        rfl
      · dsimp [ψ, u]
        simp only [Category.id_comp]
        exact S.comp_mem _ _ hs φ.hs
    refine ⟨ψ.map (restrictedMorphismProperty S P).Q
      (Localization.inverts (restrictedMorphismProperty S P).Q
        (restrictedMorphismProperty S P)), ?_⟩
    rw [map_right_fraction ψ, hψ, hφ]
  have hfaithful : F.Faithful := {
    map_injective := by
      intro X Y f g h
      let X₀ := (restrictedMorphismProperty S P).Q.objPreimage X
      let Y₀ := (restrictedMorphismProperty S P).Q.objPreimage Y
      let eX := (restrictedMorphismProperty S P).Q.objObjPreimageIso X
      let eY := (restrictedMorphismProperty S P).Q.objObjPreimageIso Y
      have h' :
          F.map (eX.hom ≫ f ≫ eY.inv) =
            F.map (eX.hom ≫ g ≫ eY.inv) := by
        simp only [Functor.map_comp]
        rw [h]
      have h'' := hfaithfulQ
        (X := X₀) (Y := Y₀) (eX.hom ≫ f ≫ eY.inv)
        (eX.hom ≫ g ≫ eY.inv) h'
      apply (cancel_epi eX.hom).1
      apply (cancel_mono eY.inv).1
      simpa only [Category.assoc] using h''
    }
  have hfull : F.Full := {
    map_surjective := by
      intro X Y f
      let X₀ := (restrictedMorphismProperty S P).Q.objPreimage X
      let Y₀ := (restrictedMorphismProperty S P).Q.objPreimage Y
      let eX := (restrictedMorphismProperty S P).Q.objObjPreimageIso X
      let eY := (restrictedMorphismProperty S P).Q.objObjPreimageIso Y
      let f' := F.map eX.hom ≫ f ≫ F.map eY.inv
      obtain ⟨g, hg⟩ := hfullQ f'
      let g' := eX.inv ≫ g ≫ eY.hom
      refine ⟨g', ?_⟩
      calc
        F.map g' = F.map eX.inv ≫ F.map g ≫ F.map eY.hom := by
          dsimp [g']
          simp only [Functor.map_comp]
        _ = F.map eX.inv ≫ f' ≫ F.map eY.hom := by rw [hg]
        _ = f := by
          dsimp [f']
          have hX : F.map eX.inv ≫ F.map eX.hom = 𝟙 _ := by
            rw [← F.map_comp, eX.inv_hom_id, F.map_id]
          have hY : F.map eY.inv ≫ F.map eY.hom = 𝟙 _ := by
            rw [← F.map_comp, eY.inv_hom_id, F.map_id]
          calc
            F.map eX.inv ≫ (F.map eX.hom ≫ f ≫ F.map eY.inv) ≫ F.map eY.hom =
                (F.map eX.inv ≫ F.map eX.hom) ≫
                  (f ≫ (F.map eY.inv ≫ F.map eY.hom)) := by
              simp only [Category.assoc]
            _ = f := by simp only [hX, hY, Category.id_comp, Category.comp_id]
    }
  have hess : F.EssSurj := {
    mem_essImage := by
      intro Y
      obtain ⟨X, eX⟩ :
          ∃ X : C, Nonempty (S.Q.obj X ≅ Y) :=
        ⟨S.Q.objPreimage Y, ⟨S.Q.objObjPreimageIso Y⟩⟩
      obtain ⟨X', s, hs⟩ := hP X
      refine ⟨(restrictedMorphismProperty S P).Q.obj X', ⟨?_⟩⟩
      change S.Q.obj (P.ι.obj X') ≅ Y
      exact (Localization.isoOfHom S.Q S s hs) ≪≫ eX.some
    }
  change F.IsEquivalence
  exact { faithful := hfaithful, full := hfull, essSurj := hess }

theorem fullSubcategoryLocalization_isExact
    {S : MorphismProperty C} [LeftMultiplicativeSystem S]
    [RightMultiplicativeSystem S] [CompatibleWithTriangulation S]
    (P : ObjectProperty C) [P.IsTriangulated]
    [LeftMultiplicativeSystem (restrictedMorphismProperty S P)]
    [RightMultiplicativeSystem (restrictedMorphismProperty S P)]
    [CompatibleWithTriangulation (restrictedMorphismProperty S P)] :
    IsExactLocalizationFactor (S := restrictedMorphismProperty S P)
      (fullSubcategoryLocalizationFunctor S P) := by
  let F : P.FullSubcategory ⥤ S.Localization := P.ι ⋙ S.Q
  have hF : (restrictedMorphismProperty S P).IsInvertedBy F := by
    intro X Y f hf
    exact MorphismProperty.Q_inverts S (P.ι.map f) hf
  have h := exact_localizationFactor_isExact
    (S := restrictedMorphismProperty S P) F hF
  simpa [F, fullSubcategoryLocalizationFunctor, localizationFactor] using h

end LocalizationSubcategory

/-! ## The kernel of the localization functor -/

section LocalizationKernel

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {S : MorphismProperty C} [LeftMultiplicativeSystem S]
  [RightMultiplicativeSystem S] [CompatibleWithTriangulation S]

def IsZeroAfterLocalization (S : MorphismProperty C) (Z : C) : Prop :=
  IsZero (S.Q.obj Z)

def KernelLocalizationOutgoingZero (S : MorphismProperty C) (Z : C) : Prop :=
  ∃ Z' : C, S (0 : Z ⟶ Z')

def KernelLocalizationIncomingZero (S : MorphismProperty C) (Z : C) : Prop :=
  ∃ Z' : C, S (0 : Z' ⟶ Z)

def KernelLocalizationBiproductTriangle (S : MorphismProperty C) (Z : C) : Prop :=
  ∃ (Z' X Y : C) (f : X ⟶ Y) (g : Y ⟶ Z ⊞ Z')
    (h : Z ⊞ Z' ⟶ X⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C ∧ S f

def KernelLocalizationZeroToObject (S : MorphismProperty C) (Z : C) : Prop :=
  S (0 : (0 : C) ⟶ Z)

def KernelLocalizationObjectToZero (S : MorphismProperty C) (Z : C) : Prop :=
  S (0 : Z ⟶ (0 : C))

def KernelLocalizationTriangle (S : MorphismProperty C) (Z : C) : Prop :=
  ∃ (X Y : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ X⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C ∧ S f

theorem kernel_localization_characterization (Z : C) :
    (IsZeroAfterLocalization S Z ↔ KernelLocalizationOutgoingZero S Z) ∧
    (KernelLocalizationOutgoingZero S Z ↔ KernelLocalizationIncomingZero S Z) ∧
    (KernelLocalizationIncomingZero S Z ↔ KernelLocalizationBiproductTriangle S Z) ∧
    ∀ _hS : SaturatedMultiplicativeSystem S,
      (IsZeroAfterLocalization S Z ↔ KernelLocalizationZeroToObject S Z) ∧
      (KernelLocalizationZeroToObject S Z ↔ KernelLocalizationObjectToZero S Z) ∧
        (KernelLocalizationObjectToZero S Z ↔ KernelLocalizationTriangle S Z) := by
  let hzero := Formalization.Books.Homology.Unit08.localization_zero_iff
    (L := S.Q) (W := S)
    (⟨inferInstance, inferInstance⟩ : MultiplicativeSystem S) Z
  have hout : IsZeroAfterLocalization S Z ↔ KernelLocalizationOutgoingZero S Z := by
    simpa [IsZeroAfterLocalization, KernelLocalizationOutgoingZero] using hzero.1
  have hin : IsZeroAfterLocalization S Z ↔ KernelLocalizationIncomingZero S Z := by
    simpa [IsZeroAfterLocalization, KernelLocalizationIncomingZero] using hzero.2
  refine ⟨hout, hout.symm.trans hin, ?_, ?_⟩
  · constructor
    · intro hIn
      obtain ⟨Z', hZ'⟩ := hIn
      let T₀ := (Triangle.mk
        (biprod.inl : Z ⟶ Z ⊞ (Z'⟦(1 : ℤ)⟧))
        (biprod.snd : Z ⊞ (Z'⟦(1 : ℤ)⟧) ⟶ Z'⟦(1 : ℤ)⟧)
        (0 : Z'⟦(1 : ℤ)⟧ ⟶ Z⟦(1 : ℤ)⟧)).invRotate
      have hT₀ : T₀ ∈ distTriang C := by
        dsimp [T₀]
        exact inv_rot_of_distTriang _
          (Formalization.Books.Derived.Unit04.split_triangle_distinguished
            Z (Z'⟦(1 : ℤ)⟧))
      have hshift₁ : S ((0 : Z' ⟶ Z)⟦(1 : ℤ)⟧') :=
        S.shift hZ' (1 : ℤ)
      have hshift : S ((0 : Z' ⟶ Z)⟦(1 : ℤ)⟧'⟦(-1 : ℤ)⟧') :=
        S.shift hshift₁ (-1 : ℤ)
      have hfirst : S T₀.mor₁ := by
        change S (-(((0 : (Z'⟦(1 : ℤ)⟧) ⟶ Z⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧') ≫
          (shiftFunctorCompIsoId C (1 : ℤ) (-1) (by simp)).hom.app
            Z))
        have hmap : S ((shiftFunctor C (-1)).map
            (0 : (Z'⟦(1 : ℤ)⟧) ⟶ Z⟦(1 : ℤ)⟧)) := by
          simpa only [shift_zero_eq_zero] using hshift
        have hIso : S ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by simp)).hom.app Z) :=
          localization_conditions_contains_isomorphisms (S := S)
            _ (MorphismProperty.isomorphisms.infer_property _)
        have hcomp : S ((shiftFunctor C (-1)).map
            (0 : (Z'⟦(1 : ℤ)⟧) ⟶ Z⟦(1 : ℤ)⟧) ≫
            (shiftFunctorCompIsoId C (1 : ℤ) (-1) (by simp)).hom.app Z) :=
          S.comp_mem _ _ hmap hIso
        have hzero : (shiftFunctor C (-1)).map
            (0 : (Z'⟦(1 : ℤ)⟧) ⟶ Z⟦(1 : ℤ)⟧) ≫
            (shiftFunctorCompIsoId C (1 : ℤ) (-1) (by simp)).hom.app Z = 0 := by
          rw [Functor.map_zero, zero_comp]
        simpa only [hzero, neg_zero] using hcomp
      exact ⟨Z'⟦(1 : ℤ)⟧, T₀.obj₁, T₀.obj₂, T₀.mor₁, T₀.mor₂, T₀.mor₃,
        hT₀, hfirst⟩
    · intro hB
      obtain ⟨Z', X, Y, f, g, h, hT, hf⟩ := hB
      have hTQ : S.Q.mapTriangle.obj (Triangle.mk f g h) ∈ distTriang _ :=
        S.Q.map_distinguished _ hT
      have hQsum : IsZero (S.Q.obj (Z ⊞ Z')) := by
        apply Triangle.isZero₃_of_isIso₁ _ hTQ
        exact MorphismProperty.Q_inverts S f hf
      let hPres : PreservesBinaryBiproducts S.Q :=
        ⟨fun {X Y} => preservesBinaryBiproduct_of_preservesBiproduct S.Q X Y⟩
      have hBiprod : IsZero (S.Q.obj Z ⊞ S.Q.obj Z') :=
        hQsum.of_iso
          (@Functor.mapBiprod _ _ _ _ _ _ S.Q Z Z' _ _ hPres.preserves).symm
      obtain ⟨hQZ, _⟩ := (biprod_isZero_iff _ _).1 hBiprod
      exact hin.mp hQZ
  · intro hS
    have hSat := invertedByLocalization_eq_of_saturated (W := S) hS
    have hzeroTo : IsZeroAfterLocalization S Z ↔
        KernelLocalizationZeroToObject S Z := by
      constructor
      · intro hZ
        have hInv : invertedByLocalization S (0 : (0 : C) ⟶ Z) := by
          change IsIso (S.Q.map (0 : (0 : C) ⟶ Z))
          simpa only [Functor.map_zero] using
            (isIsoZero_iff_source_target_isZero _ _).2
              ⟨Functor.map_isZero S.Q (isZero_zero C), hZ⟩
        rw [hSat] at hInv
        exact hInv
      · intro h0
        have hInv : invertedByLocalization S (0 : (0 : C) ⟶ Z) := by
          rw [hSat]
          exact h0
        change IsIso (S.Q.map (0 : (0 : C) ⟶ Z)) at hInv
        let : IsIso (S.Q.map (0 : (0 : C) ⟶ Z)) := hInv
        exact IsZero.of_iso (Functor.map_isZero S.Q (isZero_zero C))
          (asIso (S.Q.map (0 : (0 : C) ⟶ Z))).symm
    have hObjTo : KernelLocalizationZeroToObject S Z ↔
        KernelLocalizationObjectToZero S Z := by
      constructor
      · intro h0
        have hZ : IsZeroAfterLocalization S Z := hzeroTo.mpr h0
        have hInv : invertedByLocalization S (0 : Z ⟶ (0 : C)) := by
          change IsIso (S.Q.map (0 : Z ⟶ (0 : C)))
          simpa only [Functor.map_zero] using
            (isIsoZero_iff_source_target_isZero _ _).2
              ⟨hZ, Functor.map_isZero S.Q (isZero_zero C)⟩
        rw [hSat] at hInv
        exact hInv
      · intro h0
        have hInv : invertedByLocalization S (0 : Z ⟶ (0 : C)) := by
          rw [hSat]
          exact h0
        change IsIso (S.Q.map (0 : Z ⟶ (0 : C))) at hInv
        let : IsIso (S.Q.map (0 : Z ⟶ (0 : C))) := hInv
        have hZ : IsZero (S.Q.obj Z) :=
          IsZero.of_iso (Functor.map_isZero S.Q (isZero_zero C))
            (asIso (S.Q.map (0 : Z ⟶ (0 : C))))
        exact hzeroTo.mp hZ
    have htriangle : KernelLocalizationObjectToZero S Z ↔
        KernelLocalizationTriangle S Z := by
      constructor
      · intro h0
        refine ⟨(0 : C), Z, (0 : (0 : C) ⟶ Z), 𝟙 Z,
          (0 : Z ⟶ (0 : C)⟦(1 : ℤ)⟧), contractible_distinguished₁ Z, ?_⟩
        exact hObjTo.mpr h0
      · rintro ⟨X, Y, f, g, h, hT, hf⟩
        have hTQ : S.Q.mapTriangle.obj (Triangle.mk f g h) ∈ distTriang _ :=
          S.Q.map_distinguished _ hT
        have hQZ : IsZero (S.Q.obj Z) := by
          apply Triangle.isZero₃_of_isIso₁ _ hTQ
          exact MorphismProperty.Q_inverts S f hf
        exact hObjTo.mp (hzeroTo.mp hQZ)
    exact ⟨hzeroTo, hObjTo, htriangle⟩

end LocalizationKernel

/-! ## Filtered categories of localized triangle morphisms -/

section LimitTriangles

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

def triangleMorphismProperty (S : MorphismProperty C) :
    MorphismProperty (Triangle C) :=
  fun _ _ φ => S φ.hom₁ ∧ S φ.hom₂ ∧ S φ.hom₃

abbrev TriangleLocalizationIndex (S : MorphismProperty C) (T : Triangle C) :=
  ObjectProperty.FullSubcategory
    (fun A : (triangleMorphismProperty S).Under
      (⊤ : MorphismProperty (Triangle C)) T => A.right ∈ distTriang C)

def triangleLocalizationIndexToObject₁
    (S : MorphismProperty C) (T : Triangle C) :
    TriangleLocalizationIndex S T ⥤ LeftDenominatorCategory S T.obj₁ where
  obj A :=
    MorphismProperty.Under.mk
      (P := S) (Q := (⊤ : MorphismProperty C)) (X := T.obj₁)
      A.obj.hom.hom₁ A.obj.prop.1
  map {A B} φ :=
    MorphismProperty.Under.homMk φ.hom.right.hom₁ (by
      change A.obj.hom.hom₁ ≫ φ.hom.right.hom₁ = B.obj.hom.hom₁
      exact congrArg (fun k => k.hom₁) (MorphismProperty.Under.w φ.hom))
  map_id A := by
    apply MorphismProperty.Under.Hom.ext
    rfl
  map_comp f g := by
    apply MorphismProperty.Under.Hom.ext
    rfl

def triangleLocalizationIndexToObject₂
    (S : MorphismProperty C) (T : Triangle C) :
    TriangleLocalizationIndex S T ⥤ LeftDenominatorCategory S T.obj₂ where
  obj A :=
    MorphismProperty.Under.mk
      (P := S) (Q := (⊤ : MorphismProperty C)) (X := T.obj₂)
      A.obj.hom.hom₂ A.obj.prop.2.1
  map {A B} φ :=
    MorphismProperty.Under.homMk φ.hom.right.hom₂ (by
      change A.obj.hom.hom₂ ≫ φ.hom.right.hom₂ = B.obj.hom.hom₂
      exact congrArg (fun k => k.hom₂) (MorphismProperty.Under.w φ.hom))
  map_id A := by
    apply MorphismProperty.Under.Hom.ext
    rfl
  map_comp f g := by
    apply MorphismProperty.Under.Hom.ext
    rfl

def triangleLocalizationIndexToObject₃
    (S : MorphismProperty C) (T : Triangle C) :
    TriangleLocalizationIndex S T ⥤ LeftDenominatorCategory S T.obj₃ where
  obj A :=
    MorphismProperty.Under.mk
      (P := S) (Q := (⊤ : MorphismProperty C)) (X := T.obj₃)
      A.obj.hom.hom₃ A.obj.prop.2.2
  map {A B} φ :=
    MorphismProperty.Under.homMk φ.hom.right.hom₃ (by
      change A.obj.hom.hom₃ ≫ φ.hom.right.hom₃ = B.obj.hom.hom₃
      exact congrArg (fun k => k.hom₃) (MorphismProperty.Under.w φ.hom))
  map_id A := by
    apply MorphismProperty.Under.Hom.ext
    rfl
  map_comp f g := by
    apply MorphismProperty.Under.Hom.ext
    rfl

private theorem triangle_morphism_property_of_first_two
    {S : MorphismProperty C} (hS : SaturatedMultiplicativeSystem S)
    [CompatibleWithTriangulation S]
    {A B : Triangle C} (hA : A ∈ distTriang C) (hB : B ∈ distTriang C)
    (φ : A ⟶ B) (hφ₁ : S φ.hom₁) (hφ₂ : S φ.hom₂) : S φ.hom₃ := by
  letI : LeftMultiplicativeSystem S := hS.1.1
  letI : RightMultiplicativeSystem S := hS.1.2
  have hφ₃ : IsIso ((S.Q.mapTriangle.map φ).hom₃) := by
    apply isIso₃_of_isIso₁₂ (S.Q.mapTriangle.map φ)
      (S.Q.map_distinguished A hA) (S.Q.map_distinguished B hB)
    · exact MorphismProperty.Q_inverts S φ.hom₁ hφ₁
    · exact MorphismProperty.Q_inverts S φ.hom₂ hφ₂
  have hφ₃'' : invertedByLocalization S φ.hom₃ := by
    change IsIso ((S.Q.mapTriangle.map φ).hom₃)
    exact hφ₃
  rw [invertedByLocalization_eq_of_saturated hS] at hφ₃''
  exact hφ₃''

private theorem triangle_morphism_property_of_last_two
    {S : MorphismProperty C} (hS : SaturatedMultiplicativeSystem S)
    [CompatibleWithTriangulation S]
    {A B : Triangle C} (hA : A ∈ distTriang C) (hB : B ∈ distTriang C)
    (φ : A ⟶ B) (hφ₂ : S φ.hom₂) (hφ₃ : S φ.hom₃) : S φ.hom₁ := by
  letI : LeftMultiplicativeSystem S := hS.1.1
  letI : RightMultiplicativeSystem S := hS.1.2
  have hφ₁ : IsIso ((S.Q.mapTriangle.map φ).hom₁) := by
    apply isIso₁_of_isIso₂₃ (S.Q.mapTriangle.map φ)
      (S.Q.map_distinguished A hA) (S.Q.map_distinguished B hB)
    · exact MorphismProperty.Q_inverts S φ.hom₂ hφ₂
    · exact MorphismProperty.Q_inverts S φ.hom₃ hφ₃
  have hφ₁' : invertedByLocalization S φ.hom₁ := by
    change IsIso ((S.Q.mapTriangle.map φ).hom₁)
    exact hφ₁
  rw [invertedByLocalization_eq_of_saturated hS] at hφ₁'
  exact hφ₁'

private theorem triangle_morphism_zero_refinement
    {S : MorphismProperty C} (hS : SaturatedMultiplicativeSystem S)
    [CompatibleWithTriangulation S]
    {A B : Triangle C} (hA : A ∈ distTriang C) (hB : B ∈ distTriang C)
    (φ : A ⟶ B)
    (hφ₁ : S.Q.map φ.hom₁ = S.Q.map (0 : A.obj₁ ⟶ B.obj₁))
    (hφ₂ : S.Q.map φ.hom₂ = S.Q.map (0 : A.obj₂ ⟶ B.obj₂))
    (hφ₃ : S.Q.map φ.hom₃ = S.Q.map (0 : A.obj₃ ⟶ B.obj₃)) :
    ∃ (D : Triangle C) (hD : D ∈ distTriang C) (ψ : B ⟶ D),
      triangleMorphismProperty S ψ ∧ φ ≫ ψ = 0 := by
  letI : LeftMultiplicativeSystem S := hS.1.1
  letI : RightMultiplicativeSystem S := hS.1.2
  obtain ⟨X₁, s₁, hs₁, hs₁zero⟩ :=
    (MorphismProperty.map_eq_iff_postcomp S.Q S φ.hom₁
      (0 : A.obj₁ ⟶ B.obj₁)).1 hφ₁
  obtain ⟨ψ₂, hf₂⟩ :=
    (MorphismProperty.RightFraction.mk s₁ hs₁ B.mor₁).exists_leftFraction
  let f₂ := ψ₂.f
  let s₂ := ψ₂.s
  have hs₂ : S s₂ := ψ₂.hs
  obtain ⟨X₂, t₂, ht₂, ht₂zero⟩ :=
    (MorphismProperty.map_eq_iff_postcomp S.Q S (φ.hom₂ ≫ s₂)
      0).1 (by
      rw [S.Q.map_comp, hφ₂, ← S.Q.map_comp, zero_comp])
  let s₂' := s₂ ≫ t₂
  let f₂' := f₂ ≫ t₂
  have hf₂' : B.mor₁ ≫ s₂' = s₁ ≫ f₂' := by
    dsimp [s₂', f₂']
    rw [← Category.assoc, ← Category.assoc]
    rw [show B.mor₁ ≫ s₂ = s₁ ≫ f₂ by simpa [f₂, s₂] using hf₂]
  have hs₂' : S s₂' := S.comp_mem _ _ hs₂ ht₂
  obtain ⟨D₀, g₀, h₀, hD₀⟩ := distinguished_cocone_triangle f₂'
  let D₀' := Triangle.mk f₂' g₀ h₀
  have hD₀' : D₀' ∈ distTriang C := hD₀
  obtain ⟨s₃, hs₃₂, hs₃₃⟩ :=
    complete_distinguished_triangle_morphism B D₀' hB hD₀' s₁ s₂' hf₂'
  let ψ₀ : B ⟶ D₀' := Triangle.homMk _ _ s₁ s₂' s₃ hf₂' hs₃₂ hs₃₃
  have hψ₀₃ : S s₃ :=
    triangle_morphism_property_of_first_two hS hB hD₀' ψ₀ hs₁ hs₂'
  obtain ⟨X₃, t₃, ht₃, ht₃zero⟩ :=
    (MorphismProperty.map_eq_iff_postcomp S.Q S
      (φ.hom₃ ≫ ψ₀.hom₃) (0 : A.obj₃ ⟶ D₀'.obj₃)).1 (by
      rw [S.Q.map_comp, hφ₃, ← S.Q.map_comp, zero_comp])
  obtain ⟨D, g, h, hD⟩ :=
    distinguished_cocone_triangle₁ (D₀'.mor₂ ≫ t₃)
  let D' := Triangle.mk g (D₀'.mor₂ ≫ t₃) h
  have hD' : D' ∈ distTriang C := hD
  have hobj₂ : D'.obj₂ = D₀'.obj₂ := rfl
  have hobj₃ : D'.obj₃ = X₃ := rfl
  let id₂ : D₀'.obj₂ ⟶ D'.obj₂ := eqToHom hobj₂.symm
  let ht₃' : D₀'.obj₃ ⟶ D'.obj₃ := t₃ ≫ eqToHom hobj₃.symm
  have hcomp₂ : D₀'.mor₂ ≫ ht₃' = id₂ ≫ D'.mor₂ := by
    cases hobj₂
    cases hobj₃
    change D₀'.mor₂ ≫ t₃ ≫ 𝟙 X₃ =
      𝟙 D₀'.obj₂ ≫ (D₀'.mor₂ ≫ t₃)
    simp
  let a := (complete_distinguished_triangle_morphism₁
    D₀' D' hD₀' hD' id₂ ht₃' hcomp₂).choose
  have ha₁ := (complete_distinguished_triangle_morphism₁
    D₀' D' hD₀' hD' id₂ ht₃' hcomp₂).choose_spec.1
  have ha₂ := (complete_distinguished_triangle_morphism₁
    D₀' D' hD₀' hD' id₂ ht₃' hcomp₂).choose_spec.2
  let ψ₁ : D₀' ⟶ D' := Triangle.homMk _ _ a id₂ ht₃' ha₁
    hcomp₂ ha₂
  have hid₂ : S id₂ := by
    apply saturated_contains_isomorphisms hS _
    exact MorphismProperty.isomorphisms.infer_property _
  have hht₃' : S ht₃' := by
    apply S.comp_mem _ _ ht₃
    apply saturated_contains_isomorphisms hS _
    exact MorphismProperty.isomorphisms.infer_property _
  have hψ₁₁ : S ψ₁.hom₁ := by
    apply triangle_morphism_property_of_last_two hS hD₀' hD' ψ₁
    · dsimp [ψ₁]
      exact hid₂
    · dsimp [ψ₁]
      change S ht₃'
      exact hht₃'
  let ψ := ψ₀ ≫ ψ₁
  have hψ₁₂ : S ψ₁.hom₂ := by
    dsimp [ψ₁]
    exact hid₂
  have hψ₁₃' : S ψ₁.hom₃ := by
    dsimp [ψ₁]
    change S ht₃'
    exact hht₃'
  have hψ : triangleMorphismProperty S ψ := by
    refine ⟨S.comp_mem _ _ hs₁ hψ₁₁, S.comp_mem _ _ hs₂' hψ₁₂, ?_⟩
    exact S.comp_mem _ _ hψ₀₃ hψ₁₃'
  refine ⟨D', hD', ψ₀ ≫ ψ₁, hψ, ?_⟩
  have hzero₁ : φ.hom₁ ≫ ψ₀.hom₁ = 0 := by
    change φ.hom₁ ≫ s₁ = 0
    rw [hs₁zero, zero_comp]
  have hzero₂ : φ.hom₂ ≫ ψ₀.hom₂ = 0 := by
    change φ.hom₂ ≫ s₂' = 0
    rw [← Category.assoc, ht₂zero, zero_comp]
  have hzero₃ : (φ.hom₃ ≫ ψ₀.hom₃) ≫ ht₃' = 0 := by
    change (φ.hom₃ ≫ ψ₀.hom₃) ≫
      (t₃ ≫ eqToHom hobj₃.symm) = 0
    rw [← Category.assoc, ht₃zero, zero_comp, zero_comp]
  apply Triangle.hom_ext
  · change φ.hom₁ ≫ (ψ₀.hom₁ ≫ ψ₁.hom₁) = 0
    rw [← Category.assoc, hzero₁, zero_comp]
  · change φ.hom₂ ≫ (ψ₀.hom₂ ≫ ψ₁.hom₂) = 0
    rw [← Category.assoc, hzero₂, zero_comp]
  · change φ.hom₃ ≫ (ψ₀.hom₃ ≫ ψ₁.hom₃) = 0
    rw [← Category.assoc]
    change (φ.hom₃ ≫ ψ₀.hom₃) ≫ ht₃' = 0
    exact hzero₃

theorem triangleLocalizationIndex_filtered
    {S : MorphismProperty C} (hS : SaturatedMultiplicativeSystem S)
    [CompatibleWithTriangulation S] (T : Triangle C) (hT : T ∈ distTriang C) :
    IsFiltered (TriangleLocalizationIndex S T) := by
  sorry

theorem triangleLocalizationIndex_evaluations_cofinal
    {S : MorphismProperty C} (hS : SaturatedMultiplicativeSystem S)
    [CompatibleWithTriangulation S] (T : Triangle C) (hT : T ∈ distTriang C) :
    Functor.Final (triangleLocalizationIndexToObject₁ S T) ∧
      Functor.Final (triangleLocalizationIndexToObject₂ S T) ∧
      Functor.Final (triangleLocalizationIndexToObject₃ S T) := by
  sorry

end LimitTriangles

end Formalization.Books.Derived.Unit05
