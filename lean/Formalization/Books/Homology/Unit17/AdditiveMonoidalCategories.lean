import Formalization.Books.Homology.Unit04.KaroubianCategories
import Formalization.Books.Categories.Unit43.MonoidalCategories
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.GradedObject.Braiding
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Homological Algebra, Chapter 17: Additive monoidal categories

This file records the source definition and its duality consequences.  The
monoidal and duality primitives are Mathlib's `MonoidalPreadditive` and
`ExactPairing`; the chapter-facing combined class only adds the finite-product
part of the source's additive-category hypothesis.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DirectSum

universe v u

namespace Formalization.Books.Homology.Unit17

/-! ## Additive monoidal categories -/

/-- An additive category equipped with a monoidal structure whose tensor is
additive in each variable.  `MonoidalPreadditive` is Mathlib's canonical
interface for the additivity of the two tensoring functors. -/
class AdditiveMonoidalCategory (C : Type u) [Category.{v} C]
    extends Formalization.Books.Homology.Unit03.AdditiveCategory C,
      MonoidalCategory C, MonoidalPreadditive C

instance additiveMonoidalCategory_to_additiveCategory
    (C : Type u) [Category.{v} C] [h : AdditiveMonoidalCategory C] :
    Formalization.Books.Homology.Unit03.AdditiveCategory C :=
  h.toAdditiveCategory

instance additiveMonoidalCategory_hasBinaryBiproducts
    (C : Type u) [Category.{v} C] [AdditiveMonoidalCategory C] :
    HasBinaryBiproducts C :=
  hasBinaryBiproducts_of_finite_biproducts C

/-! ## Duals and direct sums -/

/-- The direct sum of two left-dual pairs is again a left-dual pair. -/
theorem left_dual_biproduct
    {C : Type u} [Category.{v} C] [AdditiveMonoidalCategory C]
    {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    Nonempty (ExactPairing (X₁ ⊞ X₂) (Y₁ ⊞ Y₂)) := by sorry
/-
  have htransport {Xi Yi B A : C} [ExactPairing Xi Yi]
      (iX : Xi ⟶ B) (pX : B ⟶ Xi) (iY : Yi ⟶ A) (pY : A ⟶ Yi) :
      A ◁ η_ Xi Yi ≫ A ◁ (iX ⊗ₘ iY) ≫ (α_ A B A).inv ≫
          (pY ▷ B) ▷ A ≫ (α_ Yi B A).hom ≫
            Yi ◁ (pX ▷ A) ≫ (α_ Yi Xi A).inv ≫
              ε_ Xi Yi ▷ A ≫ (λ_ A).hom ≫ pY =
        A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫
            (pY ▷ B) ▷ Yi ≫
              (α_ Yi B Yi).hom ≫ Yi ◁ (B ◁ iY) ≫
              Yi ◁ (pX ▷ A) ≫ (α_ Yi Xi A).inv ≫
                ε_ Xi Yi ▷ A ≫ (λ_ A).hom ≫ pY := by
    rw [MonoidalCategory.tensorHom_def]
    simp only [MonoidalCategory.whiskerLeft_comp]
    simp [Category.assoc]
    rw [MonoidalCategory.associator_inv_naturality_right_assoc]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [MonoidalCategory.associator_naturality_right_assoc]
  have hmove {Xi Yi B A : C} [ExactPairing Xi Yi]
      (iX : Xi ⟶ B) (pX : B ⟶ Xi) (iY : Yi ⟶ A) (pY : A ⟶ Yi) :
      A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫
            (pY ▷ B) ▷ Yi ≫
              (α_ Yi B Yi).hom ≫ Yi ◁ (B ◁ iY) ≫
                Yi ◁ (pX ▷ A) ≫ (α_ Yi Xi A).inv ≫
                  ε_ Xi Yi ▷ A ≫ (λ_ A).hom ≫ pY =
        A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫
            (pY ▷ B) ▷ Yi ≫
              (α_ Yi B Yi).hom ≫
                Yi ◁ (pX ▷ Yi ≫ Xi ◁ iY) ≫
                  (α_ Yi Xi A).inv ≫ ε_ Xi Yi ▷ A ≫
                    (λ_ A).hom ≫ pY := by
    calc
      _ = A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom ≫
              (Yi ◁ (B ◁ iY) ≫ Yi ◁ (pX ▷ A)) ≫
                (α_ Yi Xi A).inv ≫ ε_ Xi Yi ▷ A ≫
                  (λ_ A).hom ≫ pY := by simp [Category.assoc]
      _ = A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom ≫
              Yi ◁ (B ◁ iY ≫ pX ▷ A) ≫
                (α_ Yi Xi A).inv ≫ ε_ Xi Yi ▷ A ≫
                  (λ_ A).hom ≫ pY := by
        rw [← MonoidalCategory.whiskerLeft_comp]
      _ = A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom ≫
              Yi ◁ (pX ▷ Yi ≫ Xi ◁ iY) ≫
                (α_ Yi Xi A).inv ≫ ε_ Xi Yi ▷ A ≫
                  (λ_ A).hom ≫ pY := by
        rw [MonoidalCategory.whisker_exchange]
  have hinner {Xi Yi B : C} [ExactPairing Xi Yi]
      (iX : Xi ⟶ B) (pX : B ⟶ Xi) (hi : iX ≫ pX = 𝟙 Xi) :
      Yi ◁ η_ Xi Yi ≫ Yi ◁ (iX ⊗ₘ (𝟙 Yi)) ≫
          (α_ Yi B Yi).inv ≫ ((𝟙 Yi ▷ B) ▷ Yi) ≫
            (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi) ≫
              (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫ (λ_ Yi).hom =
        (ρ_ Yi).hom := by
    calc
      _ = Yi ◁ η_ Xi Yi ≫ Yi ◁ ((iX ≫ pX) ⊗ₘ (𝟙 Yi)) ≫
          (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫ (λ_ Yi).hom := by
            monoidal
      _ = _ := by rw [hi]; simp
  have htensor {A B D : C} (f : 𝟙_ C ⟶ B ⊗ D) (g : A ⟶ D) :
      A ◁ f ≫ g ▷ (B ⊗ D) =
        g ▷ (𝟙_ C) ≫ D ◁ f := by
    calc
      A ◁ f ≫ g ▷ (B ⊗ D) =
          (𝟙 A ⊗ₘ f) ≫ (g ⊗ₘ 𝟙 (B ⊗ D)) := by
            simp [MonoidalCategory.tensorHom_def]
      _ = (𝟙 A ≫ g) ⊗ₘ (f ≫ 𝟙 (B ⊗ D)) := by
            rw [MonoidalCategory.tensorHom_comp_tensorHom]
      _ = g ⊗ₘ f := by simp
      _ = g ▷ (𝟙_ C) ≫ D ◁ f := by
            rw [MonoidalCategory.tensorHom_def]
  have houter {Xi Yi B A : C} [ExactPairing Xi Yi]
      (iX : Xi ⟶ B) (iY : Yi ⟶ A) (pY : A ⟶ Yi) :
      A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom =
          (pY ▷ (𝟙_ C)) ≫ Yi ◁ η_ Xi Yi ≫ Yi ◁ (iX ▷ Yi) ≫
          (α_ Yi B Yi).inv ≫ (α_ Yi B Yi).hom := by
    have hswap :
        A ◁ (iX ▷ Yi) ≫ pY ▷ (B ⊗ Yi) =
          pY ▷ (Xi ⊗ Yi) ≫ Yi ◁ (iX ▷ Yi) := by
      rw [MonoidalCategory.whisker_exchange]
    calc
      _ = A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          pY ▷ (B ⊗ Yi) := by
        rw [← MonoidalCategory.associator_inv_naturality_left_assoc]
        simp only [Iso.inv_hom_id, Category.comp_id]
      _ = A ◁ η_ Xi Yi ≫
          (pY ▷ (Xi ⊗ Yi) ≫ Yi ◁ (iX ▷ Yi)) := by
        simpa only [Category.assoc] using
          congrArg (fun k => A ◁ η_ Xi Yi ≫ k) hswap
      _ = (pY ▷ (𝟙_ C)) ≫ Yi ◁ η_ Xi Yi ≫ Yi ◁ (iX ▷ Yi) := by
        rw [← Category.assoc, htensor]
        simp only [Category.assoc]
      _ = _ := by simp [Category.assoc]
  have hslide {Xi Yi B A : C} [ExactPairing Xi Yi]
      (iX : Xi ⟶ B) (pX : B ⟶ Xi)
      (iY : Yi ⟶ A) (pY : A ⟶ Yi) :
      A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi) ≫
              (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫
                (𝟙_ C) ◁ iY ≫ (λ_ A).hom ≫ pY =
        (pY ▷ (𝟙_ C)) ≫
          (Yi ◁ η_ Xi Yi ≫ Yi ◁ (iX ▷ Yi) ≫
            (α_ Yi B Yi).inv ≫ ((𝟙 Yi ▷ B) ▷ Yi) ≫
              (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi) ≫
                (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫
                (λ_ Yi).hom) ≫ iY ≫ pY := by
    calc
      _ = (A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom) ≫
          Yi ◁ (pX ▷ Yi) ≫ (α_ Yi Xi Yi).inv ≫
            ε_ Xi Yi ▷ Yi ≫ (𝟙_ C) ◁ iY ≫ (λ_ A).hom ≫ pY := by
            simp [Category.assoc]
      _ = ((pY ▷ (𝟙_ C)) ≫ Yi ◁ η_ Xi Yi ≫ Yi ◁ (iX ▷ Yi) ≫
          (α_ Yi B Yi).inv ≫ (α_ Yi B Yi).hom) ≫
          Yi ◁ (pX ▷ Yi) ≫ (α_ Yi Xi Yi).inv ≫
            ε_ Xi Yi ▷ Yi ≫ (𝟙_ C) ◁ iY ≫ (λ_ A).hom ≫ pY := by
            rw [houter (iX := iX) (iY := iY) (pY := pY)]
      _ = _ := by
            simp [Category.assoc]
  have hassoc {Yi Xi A : C} (iY : Yi ⟶ A) :
      Yi ◁ (Xi ◁ iY) ≫ (α_ Yi Xi A).inv =
        (α_ Yi Xi Yi).inv ≫ (Yi ⊗ Xi) ◁ iY := by
    rw [MonoidalCategory.associator_inv_naturality_right Yi Xi iY]
  have heval {Yi Xi A : C} [ExactPairing Xi Yi] (iY : Yi ⟶ A) :
      (Yi ⊗ Xi) ◁ iY ≫ ε_ Xi Yi ▷ A =
        ε_ Xi Yi ▷ Yi ≫ (𝟙_ C) ◁ iY := by
    rw [MonoidalCategory.whisker_exchange]
  have heval_assoc {Yi Xi A : C} [ExactPairing Xi Yi]
      (iY : Yi ⟶ A) (pY : A ⟶ Yi) :
      (α_ Yi Xi Yi).inv ≫ (Yi ⊗ Xi) ◁ iY ≫
          ε_ Xi Yi ▷ A ≫ (λ_ A).hom ≫ pY =
        (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫
          (𝟙_ C) ◁ iY ≫ (λ_ A).hom ≫ pY := by
    calc
      _ = (α_ Yi Xi Yi).inv ≫
          ((Yi ⊗ Xi) ◁ iY ≫ ε_ Xi Yi ▷ A) ≫
            (λ_ A).hom ≫ pY := by simp [Category.assoc]
      _ = (α_ Yi Xi Yi).inv ≫
          (ε_ Xi Yi ▷ Yi ≫ (𝟙_ C) ◁ iY) ≫
            (λ_ A).hom ≫ pY := by rw [heval iY]
      _ = _ := by simp [Category.assoc]
  have hleft {Xi Yi B A : C} [ExactPairing Xi Yi]
      (iX : Xi ⟶ B) (pX : B ⟶ Xi)
      (iY : Yi ⟶ A) (pY : A ⟶ Yi)
      (hi : iX ≫ pX = 𝟙 Xi) (hj : iY ≫ pY = 𝟙 Yi) :
      A ◁ η_ Xi Yi ≫ A ◁ (iX ⊗ₘ iY) ≫ (α_ A B A).inv ≫
          (pY ▷ B) ▷ A ≫ (α_ Yi B A).hom ≫
            Yi ◁ (pX ▷ A) ≫ (α_ Yi Xi A).inv ≫
              ε_ Xi Yi ▷ A ≫ (λ_ A).hom ≫ pY =
        (ρ_ A).hom ≫ pY := by
    calc
      _ = A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom ≫ Yi ◁ (B ◁ iY) ≫
              Yi ◁ (pX ▷ A) ≫ (α_ Yi Xi A).inv ≫
                ε_ Xi Yi ▷ A ≫ (λ_ A).hom ≫ pY :=
        htransport iX pX iY pY
      _ = A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi ≫ Xi ◁ iY) ≫
              (α_ Yi Xi A).inv ≫ ε_ Xi Yi ▷ A ≫
                (λ_ A).hom ≫ pY := hmove iX pX iY pY
      _ = A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi) ≫
              (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫
                (𝟙_ C) ◁ iY ≫ (λ_ A).hom ≫ pY := by
        rw [MonoidalCategory.whiskerLeft_comp]
        simp only [Category.assoc]
        rw [MonoidalCategory.associator_inv_naturality_right_assoc Yi Xi iY]
        rw [heval_assoc iY pY]
      _ = (pY ▷ (𝟙_ C)) ≫
          (Yi ◁ η_ Xi Yi ≫ Yi ◁ (iX ▷ Yi) ≫
            (α_ Yi B Yi).inv ≫ ((𝟙 Yi ▷ B) ▷ Yi) ≫
              (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi) ≫
                (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫
                (λ_ Yi).hom) ≫ iY ≫ pY := hslide iX pX iY pY
      _ = (pY ▷ (𝟙_ C)) ≫
          (Yi ◁ η_ Xi Yi ≫ Yi ◁ (iX ⊗ₘ (𝟙 Yi)) ≫
            (α_ Yi B Yi).inv ≫ ((𝟙 Yi ▷ B) ▷ Yi) ≫
              (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi) ≫
                (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫
                  (λ_ Yi).hom) ≫ iY ≫ pY := by
            simp [MonoidalCategory.tensorHom_def, Category.assoc]
      _ = (pY ▷ (𝟙_ C)) ≫ (ρ_ Yi).hom ≫ iY ≫ pY := by
        rw [hinner iX pX hi]
      _ = (ρ_ A).hom ≫ pY := by
        simp [Category.assoc, hj]
  have hleft_zero {Xi Yi B A : C} [ExactPairing Xi Yi]
      (iX : Xi ⟶ B) (pX : B ⟶ Xi)
      (iY : Yi ⟶ A) (pY : A ⟶ Yi)
      (hi : iX ≫ pX = 𝟙 Xi) (hz : iY ≫ pY = 0) :
      A ◁ η_ Xi Yi ≫ A ◁ (iX ⊗ₘ iY) ≫ (α_ A B A).inv ≫
          (pY ▷ B) ▷ A ≫ (α_ Yi B A).hom ≫
            Yi ◁ (pX ▷ A) ≫ (α_ Yi Xi A).inv ≫
              ε_ Xi Yi ▷ A ≫ (λ_ A).hom ≫ pY = 0 := by
    calc
      _ = A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom ≫ Yi ◁ (B ◁ iY) ≫
              Yi ◁ (pX ▷ A) ≫ (α_ Yi Xi A).inv ≫
                ε_ Xi Yi ▷ A ≫ (λ_ A).hom ≫ pY :=
        htransport iX pX iY pY
      _ = A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi ≫ Xi ◁ iY) ≫
              (α_ Yi Xi A).inv ≫ ε_ Xi Yi ▷ A ≫
                (λ_ A).hom ≫ pY := hmove iX pX iY pY
      _ = A ◁ η_ Xi Yi ≫ A ◁ (iX ▷ Yi) ≫
          (α_ A B Yi).inv ≫ (pY ▷ B) ▷ Yi ≫
            (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi) ≫
              (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫
                (𝟙_ C) ◁ iY ≫ (λ_ A).hom ≫ pY := by
        rw [MonoidalCategory.whiskerLeft_comp]
        simp only [Category.assoc]
        rw [MonoidalCategory.associator_inv_naturality_right_assoc Yi Xi iY]
        rw [heval_assoc iY pY]
      _ = (pY ▷ (𝟙_ C)) ≫
          (Yi ◁ η_ Xi Yi ≫ Yi ◁ (iX ▷ Yi) ≫
            (α_ Yi B Yi).inv ≫ ((𝟙 Yi ▷ B) ▷ Yi) ≫
              (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi) ≫
                (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫
                (λ_ Yi).hom) ≫ iY ≫ pY := hslide iX pX iY pY
      _ = (pY ▷ (𝟙_ C)) ≫
          (Yi ◁ η_ Xi Yi ≫ Yi ◁ (iX ⊗ₘ (𝟙 Yi)) ≫
            (α_ Yi B Yi).inv ≫ ((𝟙 Yi ▷ B) ▷ Yi) ≫
              (α_ Yi B Yi).hom ≫ Yi ◁ (pX ▷ Yi) ≫
                (α_ Yi Xi Yi).inv ≫ ε_ Xi Yi ▷ Yi ≫
                  (λ_ Yi).hom) ≫ iY ≫ pY := by
            simp [MonoidalCategory.tensorHom_def, Category.assoc]
      _ = (pY ▷ (𝟙_ C)) ≫ (ρ_ Yi).hom ≫ iY ≫ pY := by
        rw [hinner iX pX hi]
      _ = 0 := by simp [hz]
  have hright {Xi Yi B A : C} [ExactPairing Xi Yi]
      (iX : Xi ⟶ B) (pX : B ⟶ Xi)
      (iY : Yi ⟶ A) (pY : A ⟶ Yi)
      (hi : iX ≫ pX = 𝟙 Xi) (hj : iY ≫ pY = 𝟙 Yi) :
      η_ Xi Yi ▷ B ≫ (iX ⊗ₘ iY) ▷ B ≫ (α_ B A B).hom ≫
          B ◁ (pY ▷ B) ≫ B ◁ (Yi ◁ pX) ≫
            B ◁ ε_ Xi Yi ≫ (ρ_ B).hom ≫ pX =
        (λ_ B).hom ≫ pX := by
    rw [MonoidalCategory.tensorHom_def]
    rw [MonoidalCategory.comp_whiskerRight]
    simp only [Category.assoc]
    rw [MonoidalCategory.associator_naturality_middle_assoc]
    rw [MonoidalCategory.associator_naturality_left_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.comp_whiskerRight]
    rw [hj]
    simp only [MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight,
      Category.id_comp]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    rw [MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [← MonoidalCategory.associator_naturality_right_assoc]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    calc
      _ = (𝟙_ C ◁ pX) ≫
          (η_ Xi Yi ▷ Xi ≫ (α_ Xi Yi Xi).hom ≫ Xi ◁ ε_ Xi Yi) ≫
            iX ▷ (𝟙_ C) ≫ (ρ_ B).hom ≫ pX := by simp [Category.assoc]
      _ = (𝟙_ C ◁ pX) ≫
          ((λ_ Xi).hom ≫ (ρ_ Xi).inv) ≫
            iX ▷ (𝟙_ C) ≫ (ρ_ B).hom ≫ pX := by
            rw [ExactPairing.evaluation_coevaluation]
      _ = (λ_ B).hom ≫ pX := by
            simp [Category.assoc, hi]
  have hcoh {A A' B B' D : C} (p : A ⟶ A') (r : B ⟶ B') :
      A ◁ (r ▷ D) ≫ (α_ A B' D).inv ≫ (p ▷ B') ▷ D =
        (α_ A B D).inv ≫ (p ▷ B) ▷ D ≫ (α_ A' B D).hom ≫
          A' ◁ (r ▷ D) ≫ (α_ A' B' D).inv := by
    calc
      _ = (α_ A B D).inv ≫ (A ◁ r) ▷ D ≫ (p ▷ B') ▷ D := by
        rw [MonoidalCategory.associator_inv_naturality_middle_assoc A r D]
      _ = (α_ A B D).inv ≫ (p ▷ B) ▷ D ≫
          (A' ◁ r) ▷ D := by
        rw [← MonoidalCategory.comp_whiskerRight]
        rw [MonoidalCategory.whisker_exchange]
        rw [MonoidalCategory.comp_whiskerRight]
      _ = _ := by
        rw [← MonoidalCategory.associator_naturality_middle_assoc]
        simp only [Iso.hom_inv_id]
        rw [Category.comp_id]
  have hright_zero {Xi Yi B A T : C} [ExactPairing Xi Yi]
      (iX : Xi ⟶ B) (pX : B ⟶ Xi) (iY : Yi ⟶ A) (pY : A ⟶ Yi)
      (q : B ⟶ T) (hi : iX ≫ pX = 𝟙 Xi) (hj : iY ≫ pY = 𝟙 Yi)
      (hq : iX ≫ q = 0) :
      η_ Xi Yi ▷ B ≫ (iX ⊗ₘ iY) ▷ B ≫ (α_ B A B).hom ≫
          B ◁ (pY ▷ B) ≫ B ◁ (Yi ◁ pX) ≫
            B ◁ ε_ Xi Yi ≫ (ρ_ B).hom ≫ q = 0 := by
    rw [MonoidalCategory.tensorHom_def]
    rw [MonoidalCategory.comp_whiskerRight]
    simp only [Category.assoc]
    rw [MonoidalCategory.associator_naturality_middle_assoc]
    rw [MonoidalCategory.associator_naturality_left_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.comp_whiskerRight]
    rw [hj]
    simp only [MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight,
      Category.id_comp]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    rw [MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [← MonoidalCategory.associator_naturality_right_assoc]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    calc
      _ = (𝟙_ C ◁ pX) ≫
          (η_ Xi Yi ▷ Xi ≫ (α_ Xi Yi Xi).hom ≫ Xi ◁ ε_ Xi Yi) ≫
            iX ▷ (𝟙_ C) ≫ (ρ_ B).hom ≫ q := by simp [Category.assoc]
      _ = (𝟙_ C ◁ pX) ≫
          ((λ_ Xi).hom ≫ (ρ_ Xi).inv) ≫
            iX ▷ (𝟙_ C) ≫ (ρ_ B).hom ≫ q := by
            rw [ExactPairing.evaluation_coevaluation]
      _ = 0 := by
            simp [Category.assoc, hq]
  let η : 𝟙_ C ⟶ (X₁ ⊞ X₂) ⊗ (Y₁ ⊞ Y₂) :=
    η_ X₁ Y₁ ≫ (biprod.inl ⊗ₘ biprod.inl) +
      η_ X₂ Y₂ ≫ (biprod.inr ⊗ₘ biprod.inr)
  let ε : (Y₁ ⊞ Y₂) ⊗ (X₁ ⊞ X₂) ⟶ 𝟙_ C :=
    (biprod.fst ▷ (X₁ ⊞ X₂)) ≫
        ((Y₁ : C) ◁ biprod.fst) ≫ ε_ X₁ Y₁ +
      (biprod.snd ▷ (X₁ ⊞ X₂)) ≫
        ((Y₂ : C) ◁ biprod.snd) ≫ ε_ X₂ Y₂
  refine ⟨ExactPairing.mk η ε ?_ ?_⟩
  · apply (cancel_mono (λ_ (Y₁ ⊞ Y₂)).hom).1
    apply biprod.hom_ext (X := Y₁) (Y := Y₂)
    · have h11 := hleft (iX := (biprod.inl : X₁ ⟶ X₁ ⊞ X₂))
          (pX := (biprod.fst : X₁ ⊞ X₂ ⟶ X₁))
          (iY := (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂))
          (pY := (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁)) (by simp) (by simp)
      simp [MonoidalCategory.tensorHom_def, Category.assoc,
        MonoidalCategory.whiskerLeft_comp] at h11
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc] at h11
      
      simp [η, ε, Category.assoc, MonoidalCategory.tensorHom_def,
        MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
        -MonoidalCategory.whisker_exchange_assoc, h11]
      have hfst := hcoh (D := Y₁ ⊞ Y₂) (p := (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁))
        (r := (biprod.fst : X₁ ⊞ X₂ ⟶ X₁))
      have hfst' := congrArg
        (fun k => k ≫ ε_ X₁ Y₁ ▷ (Y₁ ⊞ Y₂) ≫
          (λ_ (Y₁ ⊞ Y₂)).hom ≫ biprod.fst) hfst
      simp only [Category.assoc] at hfst'
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc]
      rw [h11]
      rw [← hfst']
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
        MonoidalCategory.associator_inv_naturality_right_assoc]
      simp only [MonoidalCategory.whisker_exchange_assoc]
      rw [← MonoidalCategory.associator_inv_naturality_left_assoc]
      rw [htensor]
      rw [MonoidalCategory.whisker_exchange_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      have hzero :
          Y₁ ◁ ((η_ X₂ Y₂ ≫ biprod.inr ▷ Y₂) ≫
            (X₁ ⊞ X₂) ◁ biprod.inr) ≫
              Y₁ ◁ biprod.fst ▷ (Y₁ ⊞ Y₂) = 0 := by
        rw [← MonoidalCategory.whiskerLeft_comp]
        rw [Category.assoc]
        rw [← MonoidalCategory.tensorHom_def' (biprod.fst : X₁ ⊞ X₂ ⟶ X₁)
          (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂)]
        rw [← MonoidalCategory.tensorHom_id]
        rw [Category.assoc]
        rw [MonoidalCategory.tensorHom_comp_tensorHom]
        simp
      have hzero_assoc :
          Y₁ ◁ ((η_ X₂ Y₂ ≫ biprod.inr ▷ Y₂) ≫
            (X₁ ⊞ X₂) ◁ biprod.inr) ≫
              Y₁ ◁ biprod.fst ▷ (Y₁ ⊞ Y₂) ≫
                (α_ Y₁ X₁ (Y₁ ⊞ Y₂)).inv ≫
                  ε_ X₁ Y₁ ▷ (Y₁ ⊞ Y₂) ≫
                    (λ_ (Y₁ ⊞ Y₂)).hom ≫ biprod.fst = 0 := by
        rw [← Category.assoc, hzero, zero_comp]
      rw [hzero_assoc]
      have hzero₂ :
          (Y₁ ⊞ Y₂) ◁ η_ X₁ Y₁ ≫
              (Y₁ ⊞ Y₂) ◁ biprod.inl ▷ Y₁ ≫
                (Y₁ ⊞ Y₂) ◁ (X₁ ⊞ X₂) ◁ biprod.inl ≫
                  (Y₁ ⊞ Y₂) ◁ biprod.snd ▷ (Y₁ ⊞ Y₂) = 0 := by
        rw [← MonoidalCategory.whiskerLeft_comp_assoc]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc]
        rw [← MonoidalCategory.whiskerLeft_comp]
        rw [Category.assoc]
        rw [← MonoidalCategory.tensorHom_def' (biprod.snd : X₁ ⊞ X₂ ⟶ X₂)
          (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂)]
        rw [← MonoidalCategory.tensorHom_id]
        rw [Category.assoc]
        rw [MonoidalCategory.tensorHom_comp_tensorHom]
        simp
      have hzero₂_assoc :
          (Y₁ ⊞ Y₂) ◁ η_ X₁ Y₁ ≫
              (Y₁ ⊞ Y₂) ◁ biprod.inl ▷ Y₁ ≫
                (Y₁ ⊞ Y₂) ◁ (X₁ ⊞ X₂) ◁ biprod.inl ≫
                  (Y₁ ⊞ Y₂) ◁ biprod.snd ▷ (Y₁ ⊞ Y₂) ≫
                    (α_ (Y₁ ⊞ Y₂) X₂ (Y₁ ⊞ Y₂)).inv ≫
                      biprod.snd ▷ X₂ ▷ (Y₁ ⊞ Y₂) ≫
                        ε_ X₂ Y₂ ▷ (Y₁ ⊞ Y₂) ≫
                          (λ_ (Y₁ ⊞ Y₂)).hom ≫ biprod.fst = 0 := by
        simpa only [Category.assoc, zero_comp] using
          congrArg
            (fun k => k ≫
              (α_ (Y₁ ⊞ Y₂) X₂ (Y₁ ⊞ Y₂)).inv ≫
                biprod.snd ▷ X₂ ▷ (Y₁ ⊞ Y₂) ≫
                  ε_ X₂ Y₂ ▷ (Y₁ ⊞ Y₂) ≫
                    (λ_ (Y₁ ⊞ Y₂)).hom ≫ biprod.fst) hzero₂
      rw [hzero₂_assoc]
      simp
      have hcross := hleft_zero (iX := (biprod.inr : X₂ ⟶ X₁ ⊞ X₂))
          (pX := (biprod.snd : X₁ ⊞ X₂ ⟶ X₂))
          (iY := (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂))
          (pY := (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂)) (by simp) (by simp)
      simp [MonoidalCategory.tensorHom_def, Category.assoc,
        MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
        ← MonoidalCategory.whisker_exchange_assoc] at hcross
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc] at hcross
      simpa [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_comp,
        Category.assoc] using congrArg (fun k => k ≫ biprod.fst) hcross
    · have h22 := hleft (iX := (biprod.inr : X₂ ⟶ X₁ ⊞ X₂))
          (pX := (biprod.snd : X₁ ⊞ X₂ ⟶ X₂))
          (iY := (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂))
          (pY := (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂)) (by simp) (by simp)
      simp [MonoidalCategory.tensorHom_def, Category.assoc,
        MonoidalCategory.whiskerLeft_comp] at h22
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc] at h22
      simp [η, ε, Category.assoc, MonoidalCategory.tensorHom_def,
        MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
        -MonoidalCategory.whisker_exchange_assoc, h22]
      have hsnd := hcoh (D := Y₁ ⊞ Y₂) (p := (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂))
        (r := (biprod.snd : X₁ ⊞ X₂ ⟶ X₂))
      have hsnd' := congrArg
        (fun k => k ≫ ε_ X₂ Y₂ ▷ (Y₁ ⊞ Y₂) ≫
          (λ_ (Y₁ ⊞ Y₂)).hom ≫ biprod.snd) hsnd
      simp only [Category.assoc] at hsnd'
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc]
      rw [h22]
      rw [← hsnd']
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
        MonoidalCategory.associator_inv_naturality_right_assoc]
      simp only [MonoidalCategory.whisker_exchange_assoc]
      rw [← MonoidalCategory.associator_inv_naturality_left_assoc]
      rw [← MonoidalCategory.associator_inv_naturality_right_assoc]
      simp only [Iso.inv_hom_id_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      rw [MonoidalCategory.whisker_exchange_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      have hzero :
          Y₂ ◁ ((η_ X₁ Y₁ ≫ biprod.inl ▷ Y₁) ≫
            (X₁ ⊞ X₂) ◁ biprod.inl) ≫
              Y₂ ◁ biprod.snd ▷ (Y₁ ⊞ Y₂) = 0 := by
        rw [← MonoidalCategory.whiskerLeft_comp]
        rw [Category.assoc]
        rw [← MonoidalCategory.tensorHom_def' (biprod.snd : X₁ ⊞ X₂ ⟶ X₂)
          (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂)]
        rw [← MonoidalCategory.tensorHom_id]
        rw [Category.assoc]
        rw [MonoidalCategory.tensorHom_comp_tensorHom]
        simp
      have hzero_assoc :
          Y₂ ◁ ((η_ X₁ Y₁ ≫ biprod.inl ▷ Y₁) ≫
            (X₁ ⊞ X₂) ◁ biprod.inl) ≫
              Y₂ ◁ biprod.snd ▷ (Y₁ ⊞ Y₂) ≫
                (α_ Y₂ X₂ (Y₁ ⊞ Y₂)).inv ≫
                  ε_ X₂ Y₂ ▷ (Y₁ ⊞ Y₂) ≫
                    (λ_ (Y₁ ⊞ Y₂)).hom ≫ biprod.snd = 0 := by
        rw [← Category.assoc, hzero, zero_comp]
      rw [hzero_assoc]
      have hzero₂ :
          (Y₁ ⊞ Y₂) ◁ η_ X₂ Y₂ ≫
              (Y₁ ⊞ Y₂) ◁ biprod.inr ▷ Y₂ ≫
                (Y₁ ⊞ Y₂) ◁ (X₁ ⊞ X₂) ◁ biprod.inr ≫
                  (Y₁ ⊞ Y₂) ◁ biprod.fst ▷ (Y₁ ⊞ Y₂) = 0 := by
        rw [← MonoidalCategory.whiskerLeft_comp_assoc]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc]
        rw [← MonoidalCategory.whiskerLeft_comp]
        rw [Category.assoc]
        rw [← MonoidalCategory.tensorHom_def' (biprod.fst : X₁ ⊞ X₂ ⟶ X₁)
          (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂)]
        rw [← MonoidalCategory.tensorHom_id]
        rw [Category.assoc]
        rw [MonoidalCategory.tensorHom_comp_tensorHom]
        simp
      have hzero₂_assoc :
          (Y₁ ⊞ Y₂) ◁ η_ X₂ Y₂ ≫
              (Y₁ ⊞ Y₂) ◁ biprod.inr ▷ Y₂ ≫
                (Y₁ ⊞ Y₂) ◁ (X₁ ⊞ X₂) ◁ biprod.inr ≫
                  (Y₁ ⊞ Y₂) ◁ biprod.fst ▷ (Y₁ ⊞ Y₂) ≫
                    (α_ (Y₁ ⊞ Y₂) X₁ (Y₁ ⊞ Y₂)).inv ≫
                      biprod.fst ▷ X₁ ▷ (Y₁ ⊞ Y₂) ≫
                        ε_ X₁ Y₁ ▷ (Y₁ ⊞ Y₂) ≫
                          (λ_ (Y₁ ⊞ Y₂)).hom ≫ biprod.snd = 0 := by
        simpa only [Category.assoc, zero_comp] using
          congrArg
            (fun k => k ≫
              (α_ (Y₁ ⊞ Y₂) X₁ (Y₁ ⊞ Y₂)).inv ≫
                biprod.fst ▷ X₁ ▷ (Y₁ ⊞ Y₂) ≫
                  ε_ X₁ Y₁ ▷ (Y₁ ⊞ Y₂) ≫
                    (λ_ (Y₁ ⊞ Y₂)).hom ≫ biprod.snd) hzero₂
      rw [hzero₂_assoc]
      simp
      have hcross := hleft_zero (iX := (biprod.inl : X₁ ⟶ X₁ ⊞ X₂))
          (pX := (biprod.fst : X₁ ⊞ X₂ ⟶ X₁))
          (iY := (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂))
          (pY := (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁)) (by simp) (by simp)
      simp [MonoidalCategory.tensorHom_def, Category.assoc,
        MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
        ← MonoidalCategory.whisker_exchange_assoc] at hcross
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc] at hcross
      simpa [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_comp,
        Category.assoc] using congrArg (fun k => k ≫ biprod.snd) hcross
  · apply (cancel_mono (ρ_ (X₁ ⊞ X₂)).hom).1
    apply biprod.hom_ext (X := X₁) (Y := X₂)
    · have hr11 := hright (iX := (biprod.inl : X₁ ⟶ X₁ ⊞ X₂))
          (pX := (biprod.fst : X₁ ⊞ X₂ ⟶ X₁))
          (iY := (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂))
          (pY := (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁)) (by simp) (by simp)
      simp [MonoidalCategory.tensorHom_def, Category.assoc,
        MonoidalCategory.comp_whiskerRight] at hr11
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc] at hr11
      simp [η, ε, Category.assoc, MonoidalCategory.tensorHom_def,
        MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight]
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc]
      rw [hr11]
      have hD := hright_zero (iX := (biprod.inr : X₂ ⟶ X₁ ⊞ X₂))
          (pX := (biprod.snd : X₁ ⊞ X₂ ⟶ X₂))
          (iY := (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂))
          (pY := (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂))
          (q := (biprod.fst : X₁ ⊞ X₂ ⟶ X₁)) (by simp) (by simp) (by simp)
      simp [MonoidalCategory.tensorHom_def, Category.assoc,
        MonoidalCategory.comp_whiskerRight] at hD
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc] at hD
      have hB : (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂) ▷ (X₁ ⊞ X₂) ≫
          (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁) ▷ (X₁ ⊞ X₂) = 0 := by
        rw [← MonoidalCategory.comp_whiskerRight]
        simp
      have hC : (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂) ▷ (X₁ ⊞ X₂) ≫
          (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂) ▷ (X₁ ⊞ X₂) = 0 := by
        rw [← MonoidalCategory.comp_whiskerRight]
        simp
      rw [hD]
      have hB' :
          η_ X₂ Y₂ ▷ (X₁ ⊞ X₂) ≫
              biprod.inr ▷ Y₂ ▷ (X₁ ⊞ X₂) ≫
                (α_ (X₁ ⊞ X₂) Y₂ (X₁ ⊞ X₂)).hom ≫
                  (X₁ ⊞ X₂) ◁
                    (biprod.inr ▷ (X₁ ⊞ X₂) ≫ biprod.fst ▷ (X₁ ⊞ X₂) ≫
                      Y₁ ◁ biprod.fst ≫ ε_ X₁ Y₁) ≫
                    (ρ_ (X₁ ⊞ X₂)).hom ≫ biprod.fst = 0 := by
        simpa [Category.assoc] using
          congrArg
            (fun k =>
              η_ X₂ Y₂ ▷ (X₁ ⊞ X₂) ≫
                biprod.inr ▷ Y₂ ▷ (X₁ ⊞ X₂) ≫
                  (α_ (X₁ ⊞ X₂) Y₂ (X₁ ⊞ X₂)).hom ≫
                    (X₁ ⊞ X₂) ◁ (k ≫ Y₁ ◁ biprod.fst ≫ ε_ X₁ Y₁) ≫
                      (ρ_ (X₁ ⊞ X₂)).hom ≫ biprod.fst) hB
      have hC' :
          η_ X₁ Y₁ ▷ (X₁ ⊞ X₂) ≫
              biprod.inl ▷ Y₁ ▷ (X₁ ⊞ X₂) ≫
                (α_ (X₁ ⊞ X₂) Y₁ (X₁ ⊞ X₂)).hom ≫
                  (X₁ ⊞ X₂) ◁
                    (biprod.inl ▷ (X₁ ⊞ X₂) ≫ biprod.snd ▷ (X₁ ⊞ X₂) ≫
                      Y₂ ◁ biprod.snd ≫ ε_ X₂ Y₂) ≫
                    (ρ_ (X₁ ⊞ X₂)).hom ≫ biprod.fst = 0 := by
        simpa [Category.assoc] using
          congrArg
            (fun k =>
              η_ X₁ Y₁ ▷ (X₁ ⊞ X₂) ≫
                biprod.inl ▷ Y₁ ▷ (X₁ ⊞ X₂) ≫
                  (α_ (X₁ ⊞ X₂) Y₁ (X₁ ⊞ X₂)).hom ≫
                    (X₁ ⊞ X₂) ◁ (k ≫ Y₂ ◁ biprod.snd ≫ ε_ X₂ Y₂) ≫
                      (ρ_ (X₁ ⊞ X₂)).hom ≫ biprod.fst) hC
      rw [hB', hC']
      simp
    · have hr22 := hright (iX := (biprod.inr : X₂ ⟶ X₁ ⊞ X₂))
          (pX := (biprod.snd : X₁ ⊞ X₂ ⟶ X₂))
          (iY := (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂))
          (pY := (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂)) (by simp) (by simp)
      simp [MonoidalCategory.tensorHom_def, Category.assoc,
        MonoidalCategory.comp_whiskerRight] at hr22
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc] at hr22
      simp [η, ε, Category.assoc, MonoidalCategory.tensorHom_def,
        MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight]
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc]
      sorry
/-- In a Karoubian additive monoidal category, both summands in a biproduct
decomposition of a left-dualizable object are left-dualizable. -/
 -/
theorem left_dual_of_biproduct_summand
    {C : Type u} [Category.{v} C] [AdditiveMonoidalCategory C]
    [IsIdempotentComplete C] {X Y X₁ X₂ : C} [ExactPairing X Y]
    (e : X ≅ X₁ ⊞ X₂) :
    (∃ Y₁ : C, Nonempty (ExactPairing X₁ Y₁)) ∧
      (∃ Y₂ : C, Nonempty (ExactPairing X₂ Y₂)) := by
  let : ExactPairing (X₁ ⊞ X₂) Y := exactPairingCongrLeft e.symm
  have hsummand {A : C} (i : A ⟶ X₁ ⊞ X₂) (p : X₁ ⊞ X₂ ⟶ A)
      (hip : i ≫ p = 𝟙 A) :
      ∃ B : C, Nonempty (ExactPairing A B) := by
    let : HasRightDual (X₁ ⊞ X₂) := ⟨Y⟩
    let a : (X₁ ⊞ X₂) ⟶ (X₁ ⊞ X₂) := p ≫ i
    have ha : a ≫ a = a := by
      dsimp [a]
      calc
        (p ≫ i) ≫ (p ≫ i) = p ≫ (i ≫ p) ≫ i := by simp [Category.assoc]
        _ = p ≫ (𝟙 A) ≫ i := by rw [hip]
        _ = p ≫ i := by simp
    let q : Y ⟶ Y := rightAdjointMate a
    have hq_def : q =
        (ρ_ Y).inv ≫ Y ◁ ExactPairing.coevaluation (X₁ ⊞ X₂) Y ≫
          Y ◁ (a ▷ Y) ≫ (α_ Y (X₁ ⊞ X₂) Y).inv ≫
            ExactPairing.evaluation (X₁ ⊞ X₂) Y ▷ Y ≫ (λ_ Y).hom := by
      rfl
    have hq : q ≫ q = q := by
      change aᘁ ≫ aᘁ = aᘁ
      rw [← comp_rightAdjointMate, ha]
    obtain ⟨B, j, r, hjr, hrj⟩ := IsIdempotentComplete.idempotents_split Y q hq
    let : IsSplitMono j := IsSplitMono.mk' { retraction := r, id := hjr }
    let : IsSplitMono i := IsSplitMono.mk' { retraction := p, id := hip }
    have htransport {U V W Z : C} [ExactPairing U V]
        (iU : U ⟶ W) (pU : W ⟶ U) (iV : V ⟶ Z) (pV : Z ⟶ V) :
        Z ◁ η_ U V ≫ Z ◁ (iU ⊗ₘ iV) ≫ (α_ Z W Z).inv ≫
            (pV ▷ W) ▷ Z ≫ (α_ V W Z).hom ≫
              V ◁ (pU ▷ Z) ≫ (α_ V U Z).inv ≫
                ε_ U V ▷ Z ≫ (λ_ Z).hom ≫ pV =
          Z ◁ η_ U V ≫ Z ◁ (iU ▷ V) ≫
            (α_ Z W V).inv ≫ (pV ▷ W) ▷ V ≫
              (α_ V W V).hom ≫ V ◁ (W ◁ iV) ≫
                V ◁ (pU ▷ Z) ≫ (α_ V U Z).inv ≫
                  ε_ U V ▷ Z ≫ (λ_ Z).hom ≫ pV := by
      rw [MonoidalCategory.tensorHom_def]
      simp only [MonoidalCategory.whiskerLeft_comp]
      simp [Category.assoc]
      rw [MonoidalCategory.associator_inv_naturality_right_assoc]
      rw [MonoidalCategory.whisker_exchange_assoc]
      rw [MonoidalCategory.associator_naturality_right_assoc]
    have hmove {U V W Z : C} [ExactPairing U V]
        (iU : U ⟶ W) (pU : W ⟶ U) (iV : V ⟶ Z) (pV : Z ⟶ V) :
        Z ◁ η_ U V ≫ Z ◁ (iU ▷ V) ≫
            (α_ Z W V).inv ≫ (pV ▷ W) ▷ V ≫
              (α_ V W V).hom ≫ V ◁ (W ◁ iV) ≫
                V ◁ (pU ▷ Z) ≫ (α_ V U Z).inv ≫
                  ε_ U V ▷ Z ≫ (λ_ Z).hom ≫ pV =
          Z ◁ η_ U V ≫ Z ◁ (iU ▷ V) ≫
            (α_ Z W V).inv ≫ (pV ▷ W) ▷ V ≫
              (α_ V W V).hom ≫ V ◁ (pU ▷ V ≫ U ◁ iV) ≫
                (α_ V U Z).inv ≫ ε_ U V ▷ Z ≫
                  (λ_ Z).hom ≫ pV := by
      calc
        _ = Z ◁ η_ U V ≫ Z ◁ (iU ▷ V) ≫
            (α_ Z W V).inv ≫ (pV ▷ W) ▷ V ≫
              (α_ V W V).hom ≫
                (V ◁ (W ◁ iV) ≫ V ◁ (pU ▷ Z)) ≫
                  (α_ V U Z).inv ≫ ε_ U V ▷ Z ≫
                    (λ_ Z).hom ≫ pV := by simp [Category.assoc]
        _ = Z ◁ η_ U V ≫ Z ◁ (iU ▷ V) ≫
            (α_ Z W V).inv ≫ (pV ▷ W) ▷ V ≫
              (α_ V W V).hom ≫
                V ◁ (W ◁ iV ≫ pU ▷ Z) ≫
                  (α_ V U Z).inv ≫ ε_ U V ▷ Z ≫
                    (λ_ Z).hom ≫ pV := by
          rw [← MonoidalCategory.whiskerLeft_comp]
        _ = _ := by rw [MonoidalCategory.whisker_exchange]
    have htensor {M N T : C} (f : 𝟙_ C ⟶ N ⊗ T) (g : M ⟶ T) :
        M ◁ f ≫ g ▷ (N ⊗ T) = g ▷ (𝟙_ C) ≫ T ◁ f := by
      calc
        M ◁ f ≫ g ▷ (N ⊗ T) =
            (𝟙 M ⊗ₘ f) ≫ (g ⊗ₘ 𝟙 (N ⊗ T)) := by
              simp [MonoidalCategory.tensorHom_def]
        _ = (𝟙 M ≫ g) ⊗ₘ (f ≫ 𝟙 (N ⊗ T)) := by
              rw [MonoidalCategory.tensorHom_comp_tensorHom]
        _ = g ⊗ₘ f := by simp
        _ = g ▷ (𝟙_ C) ≫ T ◁ f := by rw [MonoidalCategory.tensorHom_def]
    have houter {U V W Z : C} [ExactPairing U V]
        (iU : U ⟶ W) (iV : V ⟶ Z) (pV : Z ⟶ V) :
        Z ◁ η_ U V ≫ Z ◁ (iU ▷ V) ≫
            (α_ Z W V).inv ≫ (pV ▷ W) ▷ V ≫
              (α_ V W V).hom =
          (pV ▷ (𝟙_ C)) ≫ V ◁ η_ U V ≫ V ◁ (iU ▷ V) ≫
            (α_ V W V).inv ≫ (α_ V W V).hom := by
      rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      rw [← MonoidalCategory.associator_inv_naturality_left_assoc pV W V]
      calc
        _ = (Z ◁ (η_ U V ≫ iU ▷ V) ≫
            pV ▷ (W ⊗ V)) ≫
              (α_ V W V).inv ≫ (α_ V W V).hom := by simp [Category.assoc]
        _ = (pV ▷ (𝟙_ C) ≫
            V ◁ (η_ U V ≫ iU ▷ V)) ≫
              (α_ V W V).inv ≫ (α_ V W V).hom := by rw [htensor]
        _ = _ := by simp [Category.assoc]
    have hslide {U V W Z : C} [ExactPairing U V]
        (iU : U ⟶ W) (pU : W ⟶ U)
        (iV : V ⟶ Z) (pV : Z ⟶ V) :
        Z ◁ η_ U V ≫ Z ◁ (iU ▷ V) ≫
            (α_ Z W V).inv ≫ (pV ▷ W) ▷ V ≫
              (α_ V W V).hom ≫ V ◁ (pU ▷ V) ≫
                (α_ V U V).inv ≫ ε_ U V ▷ V ≫
                  (𝟙_ C) ◁ iV ≫ (λ_ Z).hom ≫ pV =
          (pV ▷ (𝟙_ C)) ≫
            (V ◁ η_ U V ≫ V ◁ (iU ▷ V) ≫
              (α_ V W V).inv ≫ ((𝟙 V ▷ W) ▷ V) ≫
                (α_ V W V).hom ≫ V ◁ (pU ▷ V) ≫
                  (α_ V U V).inv ≫ ε_ U V ▷ V ≫
                    (λ_ V).hom) ≫ iV ≫ pV := by
      calc
        _ = (Z ◁ η_ U V ≫ Z ◁ (iU ▷ V) ≫
            (α_ Z W V).inv ≫ (pV ▷ W) ▷ V ≫
              (α_ V W V).hom) ≫
          V ◁ (pU ▷ V) ≫ (α_ V U V).inv ≫
            ε_ U V ▷ V ≫ (𝟙_ C) ◁ iV ≫ (λ_ Z).hom ≫ pV := by
              simp [Category.assoc]
        _ = ((pV ▷ (𝟙_ C)) ≫ V ◁ η_ U V ≫ V ◁ (iU ▷ V) ≫
            (α_ V W V).inv ≫ (α_ V W V).hom) ≫
          V ◁ (pU ▷ V) ≫ (α_ V U V).inv ≫
            ε_ U V ▷ V ≫ (𝟙_ C) ◁ iV ≫ (λ_ Z).hom ≫ pV := by
              rw [houter (iU := iU) (iV := iV) (pV := pV)]
        _ = _ := by simp [Category.assoc]
    have hassoc {V U Z : C} (iV : V ⟶ Z) :
        V ◁ (U ◁ iV) ≫ (α_ V U Z).inv =
          (α_ V U V).inv ≫ (V ⊗ U) ◁ iV := by
      rw [MonoidalCategory.associator_inv_naturality_right V U iV]
    have heval {V U Z : C} [ExactPairing U V] (iV : V ⟶ Z) :
        (V ⊗ U) ◁ iV ≫ ExactPairing.evaluation U V ▷ Z =
          ExactPairing.evaluation U V ▷ V ≫ (𝟙_ C) ◁ iV := by
      rw [MonoidalCategory.whisker_exchange]
    have heval_assoc {V U Z : C} [ExactPairing U V]
        (iV : V ⟶ Z) (pV : Z ⟶ V) :
        (α_ V U V).inv ≫ (V ⊗ U) ◁ iV ≫
            ExactPairing.evaluation U V ▷ Z ≫ (λ_ Z).hom ≫ pV =
          (α_ V U V).inv ≫ ExactPairing.evaluation U V ▷ V ≫
            (𝟙_ C) ◁ iV ≫ (λ_ Z).hom ≫ pV := by
      calc
        _ = (α_ V U V).inv ≫
            ((V ⊗ U) ◁ iV ≫ ExactPairing.evaluation U V ▷ Z) ≫
              (λ_ Z).hom ≫ pV := by simp [Category.assoc]
        _ = (α_ V U V).inv ≫
            (ExactPairing.evaluation U V ▷ V ≫ (𝟙_ C) ◁ iV) ≫
              (λ_ Z).hom ≫ pV := by rw [heval iV]
        _ = _ := by simp [Category.assoc]
    have hmate :
        Y ◁ ExactPairing.coevaluation (X₁ ⊞ X₂) Y ≫
            Y ◁ (p ▷ Y) ≫ (α_ Y A Y).inv ≫
              ((𝟙 Y ▷ A) ▷ Y) ≫ (α_ Y A Y).hom ≫
                Y ◁ (i ▷ Y) ≫ (α_ Y (X₁ ⊞ X₂) Y).inv ≫
                  ExactPairing.evaluation (X₁ ⊞ X₂) Y ▷ Y ≫ (λ_ Y).hom =
      (ρ_ Y).hom ≫ q := by
      rw [hq_def]
      simp [a]
    have hcoev :
        ExactPairing.coevaluation (X₁ ⊞ X₂) Y ≫
            (X₁ ⊞ X₂) ◁ q =
          ExactPairing.coevaluation (X₁ ⊞ X₂) Y ≫ a ▷ Y := by
      change ExactPairing.coevaluation (X₁ ⊞ X₂) Y ≫
          (X₁ ⊞ X₂) ◁ rightAdjointMate a =
        ExactPairing.coevaluation (X₁ ⊞ X₂) Y ≫ a ▷ Y
      exact @coevaluation_comp_rightAdjointMate C _ _ (X₁ ⊞ X₂) (X₁ ⊞ X₂)
        ⟨Y⟩ ⟨Y⟩ a
    have hsnake_a :
        ExactPairing.coevaluation (X₁ ⊞ X₂) Y ▷ (X₁ ⊞ X₂) ≫
            (a ▷ Y) ▷ (X₁ ⊞ X₂) ≫
              (α_ (X₁ ⊞ X₂) Y (X₁ ⊞ X₂)).hom ≫
                (X₁ ⊞ X₂) ◁ ExactPairing.evaluation (X₁ ⊞ X₂) Y =
          (λ_ (X₁ ⊞ X₂)).hom ≫ a ≫
            (ρ_ (X₁ ⊞ X₂)).inv := by
      rw [MonoidalCategory.associator_naturality_left_assoc]
      rw [← MonoidalCategory.whisker_exchange]
      calc
        _ = (ExactPairing.coevaluation (X₁ ⊞ X₂) Y ▷ (X₁ ⊞ X₂) ≫
              (α_ (X₁ ⊞ X₂) Y (X₁ ⊞ X₂)).hom ≫
                (X₁ ⊞ X₂) ◁ ExactPairing.evaluation (X₁ ⊞ X₂) Y) ≫
            a ▷ (𝟙_ C) := by simp only [Category.assoc]
        _ = ((λ_ (X₁ ⊞ X₂)).hom ≫ (ρ_ (X₁ ⊞ X₂)).inv) ≫
            a ▷ (𝟙_ C) := by rw [ExactPairing.evaluation_coevaluation]
        _ = (λ_ (X₁ ⊞ X₂)).hom ≫ a ≫
            (ρ_ (X₁ ⊞ X₂)).inv := by simp [Category.assoc]
    have hright :
        ExactPairing.coevaluation (X₁ ⊞ X₂) Y ▷ A ≫
            (p ⊗ₘ r) ▷ A ≫ (α_ A B A).hom ≫
              A ◁ (j ▷ A) ≫ A ◁ (Y ◁ i) ≫
                A ◁ ExactPairing.evaluation (X₁ ⊞ X₂) Y ≫
                  (ρ_ A).hom ≫ i =
      (λ_ A).hom ≫ i := by
      rw [MonoidalCategory.tensorHom_def]
      rw [MonoidalCategory.comp_whiskerRight]
      simp only [Category.assoc]
      rw [MonoidalCategory.associator_naturality_middle_assoc]
      rw [MonoidalCategory.associator_naturality_left_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      rw [← MonoidalCategory.comp_whiskerRight]
      rw [hrj]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      rw [← MonoidalCategory.whisker_exchange_assoc]
      rw [MonoidalCategory.whiskerLeft_comp_assoc]
      rw [← MonoidalCategory.associator_naturality_middle_assoc]
      rw [← MonoidalCategory.whisker_exchange_assoc]
      rw [← MonoidalCategory.comp_whiskerRight_assoc]
      rw [congrArg (fun f => f ▷ A) hcoev]
      rw [← MonoidalCategory.associator_naturality_right_assoc]
      rw [← MonoidalCategory.whisker_exchange_assoc]
      rw [MonoidalCategory.comp_whiskerRight]
      calc
        _ = (𝟙_ C ◁ i) ≫
            (ExactPairing.coevaluation (X₁ ⊞ X₂) Y ▷ (X₁ ⊞ X₂) ≫
              a ▷ Y ▷ (X₁ ⊞ X₂) ≫
                (α_ (X₁ ⊞ X₂) Y (X₁ ⊞ X₂)).hom ≫
                  (X₁ ⊞ X₂) ◁ ExactPairing.evaluation (X₁ ⊞ X₂) Y) ≫
              p ▷ 𝟙_ C ≫ (ρ_ A).hom ≫ i := by
          simp only [Category.assoc]
        _ = (𝟙_ C ◁ i) ≫
            ((λ_ (X₁ ⊞ X₂)).hom ≫ a ≫ (ρ_ (X₁ ⊞ X₂)).inv) ≫
              p ▷ 𝟙_ C ≫ (ρ_ A).hom ≫ i := by rw [hsnake_a]
        _ = (λ_ A).hom ≫ i := by
          simp [Category.assoc]
          have hi : i ≫ a = i := by
            change i ≫ (p ≫ i) = i
            rw [← Category.assoc, hip, Category.id_comp]
          rw [← Category.assoc, hi]
          rw [← Category.assoc, hip, Category.id_comp]
    refine ⟨B, ⟨ExactPairing.mk
      (ExactPairing.coevaluation (X₁ ⊞ X₂) Y ≫ (p ⊗ₘ r))
      ((j ⊗ₘ i) ≫ ExactPairing.evaluation (X₁ ⊞ X₂) Y) ?_ ?_⟩⟩
    · let lhs : B ⊗ 𝟙_ C ⟶ 𝟙_ C ⊗ B :=
        B ◁ (ExactPairing.coevaluation (X₁ ⊞ X₂) Y ≫ (p ⊗ₘ r)) ≫
          (α_ B A B).inv ≫ ((j ⊗ₘ i) ≫ ExactPairing.evaluation (X₁ ⊞ X₂) Y) ▷ B
      let rhs : B ⊗ 𝟙_ C ⟶ 𝟙_ C ⊗ B := (ρ_ B).hom ≫ (λ_ B).inv
      let k : 𝟙_ C ⊗ B ⟶ Y := (λ_ B).hom ≫ j
      change lhs = rhs
      apply (cancel_mono k (g := lhs) (h := rhs)).1
      simp [lhs, rhs, k, MonoidalCategory.tensorHom_def, Category.assoc]
      have ht := htransport (iU := p) (pU := i) (iV := r) (pV := j)
      simp [MonoidalCategory.tensorHom_def, Category.assoc,
        MonoidalCategory.whiskerLeft_comp] at ht
      rw [ht]
      rw [hmove (iU := p) (pU := i) (iV := r) (pV := j)]
      rw [MonoidalCategory.whiskerLeft_comp]
      simp only [Category.assoc]
      rw [MonoidalCategory.associator_inv_naturality_right_assoc Y (X₁ ⊞ X₂) r]
      rw [heval_assoc r j]
      rw [hslide (iU := p) (pU := i) (iV := r) (pV := j)]
      rw [hmate]
      simp [Category.assoc, hrj]
      rw [← hrj]
      simp only [← Category.assoc, hjr, Category.id_comp]
    · let lhs : 𝟙_ C ⊗ A ⟶ A ⊗ 𝟙_ C :=
        (ExactPairing.coevaluation (X₁ ⊞ X₂) Y ≫ (p ⊗ₘ r)) ▷ A ≫
          (α_ A B A).hom ≫ A ◁ ((j ⊗ₘ i) ≫ ExactPairing.evaluation (X₁ ⊞ X₂) Y)
      let rhs : 𝟙_ C ⊗ A ⟶ A ⊗ 𝟙_ C := (λ_ A).hom ≫ (ρ_ A).inv
      let k : A ⊗ 𝟙_ C ⟶ X₁ ⊞ X₂ := (ρ_ A).hom ≫ i
      change lhs = rhs
      apply (cancel_mono k (g := lhs) (h := rhs)).1
      simpa [lhs, rhs, k, MonoidalCategory.tensorHom_def, Category.assoc] using hright
  constructor
  · apply hsummand (biprod.inl : X₁ ⟶ X₁ ⊞ X₂) (biprod.fst : X₁ ⊞ X₂ ⟶ X₁)
    simp
  · apply hsummand (biprod.inr : X₂ ⟶ X₁ ⊞ X₂) (biprod.snd : X₁ ⊞ X₂ ⟶ X₂)
    simp

/- The Hom-set equalities and functorial Hom bijections displayed in the
   source proof are the chapter's existing `leftDualHomEquiv` API; the theorem
   above records the source assertion without duplicating those proof steps. -/

/-! ## Graded vector spaces -/

/-- The category of integer-graded `F`-vector spaces. -/
abbrev GradedVectorSpace (F : Type u) [Field F] :=
  GradedObject ℤ (ModuleCat.{u} F)

/-- The graded tensor product object, whose degree `n` component is the
coproduct of `Vᵖ ⊗ Wᑫ` over `p + q = n`. -/
noncomputable abbrev gradedTensor (F : Type u) [Field F]
    (V W : GradedVectorSpace F) [GradedObject.HasTensor V W] :
    GradedVectorSpace F := GradedObject.Monoidal.tensorObj V W

/-- The unit graded vector space, concentrated in degree zero. -/
noncomputable abbrev gradedTensorUnit (F : Type u) [Field F] : GradedVectorSpace F :=
  GradedObject.Monoidal.tensorUnit

/-- The degree-zero component of the graded tensor unit is the ordinary
`F`-vector-space tensor unit. -/
noncomputable def gradedTensorUnitZeroIso (F : Type u) [Field F] :
    (gradedTensorUnit F) 0 ≅ 𝟙_ (ModuleCat.{u} F) :=
  GradedObject.Monoidal.tensorUnit₀

/-- Every nonzero component of the graded tensor unit is the zero module. -/
noncomputable def gradedTensorUnitNonzeroInitial
    (F : Type u) [Field F] (n : ℤ) (hn : n ≠ 0) :
    IsInitial ((gradedTensorUnit F) n) :=
  GradedObject.Monoidal.isInitialTensorUnitApply n hn

/- The generic graded-object construction supplies the usual associativity
   constraint and unit constraints for graded vector spaces.  The direction is
   the one used in the source, namely `U ⊗ (V ⊗ W) ≅ (U ⊗ V) ⊗ W`. -/
noncomputable def gradedAssociator
    (F : Type u) [Field F] (U V W : GradedVectorSpace F)
    [GradedObject.HasTensor U V]
    [GradedObject.HasTensor (gradedTensor F U V) W]
    [GradedObject.HasTensor V W]
    [GradedObject.HasTensor U (gradedTensor F V W)]
    [GradedObject.HasGoodTensor₁₂Tensor U V W]
    [GradedObject.HasGoodTensorTensor₂₃ U V W] :
    gradedTensor F U (gradedTensor F V W) ≅
      gradedTensor F (gradedTensor F U V) W :=
  (GradedObject.Monoidal.associator U V W).symm

noncomputable def gradedLeftUnitor
    (F : Type u) [Field F] (V : GradedVectorSpace F)
    [∀ X : ModuleCat.{u} F,
      PreservesColimit (Functor.empty.{0} (ModuleCat.{u} F))
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} F)).flip.obj X)] :
    gradedTensor F (gradedTensorUnit F) V ≅ V :=
  GradedObject.Monoidal.leftUnitor V

noncomputable def gradedRightUnitor
    (F : Type u) [Field F] (V : GradedVectorSpace F)
    [∀ X : ModuleCat.{u} F,
      PreservesColimit (Functor.empty.{0} (ModuleCat.{u} F))
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} F)).obj X)] :
    gradedTensor F V (gradedTensorUnit F) ≅ V :=
  GradedObject.Monoidal.rightUnitor V

noncomputable def gradedPlainCommutativity
    (F : Type u) [Field F] (V W : GradedVectorSpace F)
    [GradedObject.HasTensor V W] [GradedObject.HasTensor W V] :
    gradedTensor F V W ≅ gradedTensor F W V :=
  GradedObject.Monoidal.braiding V W

/-- The scalar appearing in the Koszul commutativity constraint. -/
def koszulSign (F : Type u) [Field F] (p q : ℤ) : F :=
  (-1 : F) ^ (p * q)

/-- The componentwise data expressing the signed commutativity constraint on
graded vector spaces.  The existence and coherence proof is left to the
theorem-statement stage, while the displayed component equation records the
source's precise sign convention. -/
structure GradedKoszulBraiding (F : Type u) [Field F]
    (V W : GradedVectorSpace F)
    [GradedObject.HasTensor V W] [GradedObject.HasTensor W V] where
  constraint : gradedTensor F V W ≅ gradedTensor F W V
  hom_on_component : ∀ (p q k : ℤ) (h : p + q = k),
    GradedObject.Monoidal.ιTensorObj V W p q k h ≫ constraint.hom k =
      (koszulSign F p q • (β_ (V p) (W q)).hom) ≫
        GradedObject.Monoidal.ιTensorObj W V q p k
          (by simpa only [add_comm] using h)

/- The source notes that both the unsigned and signed constraints satisfy the
   symmetric monoidal coherence diagrams. -/
structure GradedVectorSpaceSymmetricStructures (F : Type u) [Field F] where
  monoidal : MonoidalCategory (GradedVectorSpace F)
  unsigned : @SymmetricCategory (GradedVectorSpace F) _ monoidal
  signed : @SymmetricCategory (GradedVectorSpace F) _ monoidal

theorem graded_vector_space_monoidal_data
    (F : Type u) [Field F] :
    Nonempty (MonoidalCategory (GradedVectorSpace F)) := by
  exact ⟨inferInstance⟩

theorem graded_vector_space_symmetric_structures
    (F : Type u) [Field F] :
    Nonempty (GradedVectorSpaceSymmetricStructures F) := by
  exact ⟨{ monoidal := inferInstance, unsigned := inferInstance, signed := inferInstance }⟩

theorem graded_koszul_braiding_exists
    (F : Type u) [Field F] (V W : GradedVectorSpace F)
    [GradedObject.HasTensor V W] [GradedObject.HasTensor W V] :
    Nonempty (GradedKoszulBraiding F V W) := by
  have hsign (p q : ℤ) : koszulSign F p q * koszulSign F q p = 1 := by
    dsimp [koszulSign]
    rw [← zpow_add₀ (neg_ne_zero.mpr one_ne_zero)]
    rw [show p * q + q * p = 2 * (p * q) by ring, zpow_mul]
    simp
  let c : gradedTensor F V W ≅ gradedTensor F W V :=
    { hom := fun k => GradedObject.Monoidal.tensorObjDesc (fun p q h =>
          (koszulSign F p q • (β_ (V p) (W q)).hom) ≫
            GradedObject.Monoidal.ιTensorObj W V q p k
              (by simpa only [add_comm] using h))
      inv := fun k => GradedObject.Monoidal.tensorObjDesc (fun p q h =>
          (koszulSign F p q • (β_ (W p) (V q)).hom) ≫
            GradedObject.Monoidal.ιTensorObj V W q p k
              (by simpa only [add_comm] using h))
      hom_inv_id := by
        funext k
        apply GradedObject.Monoidal.tensorObj_ext
        intro p q h
        dsimp
        calc
          _ = koszulSign F p q • koszulSign F q p •
              GradedObject.Monoidal.ιTensorObj V W p q k h := by
            cat_disch
          _ = _ := by
            simp [smul_smul, hsign]
      inv_hom_id := by
        funext k
        apply GradedObject.Monoidal.tensorObj_ext
        intro p q h
        dsimp
        calc
          _ = koszulSign F p q • koszulSign F q p •
              GradedObject.Monoidal.ιTensorObj W V p q k h := by
            cat_disch
          _ = _ := by
            simp [smul_smul, hsign] }
  exact ⟨⟨c, by
    intro p q k h
    simp [c]
  ⟩⟩

/-! ## Duals of graded vector spaces -/

/-- The component pairings associated with a graded left-dual evaluation,
written as bilinear maps between opposite degrees, with injectivity in both
arguments. -/
structure GradedNondegeneratePairing (F : Type u) [Field F]
    (V W : GradedVectorSpace F) [MonoidalCategory (GradedVectorSpace F)]
    [ExactPairing V W] where
  pairing : ∀ n : ℤ, (W (-n) : Type u) →ₗ[F] Module.Dual F (V n : Type u)
  left_nondegenerate : ∀ n, Function.Injective (pairing n)
  right_nondegenerate : ∀ n, Function.Injective (LinearMap.flip (pairing n))

/-- If a graded vector space has a left dual, then it is finite-dimensional in
total degree and evaluation gives nondegenerate opposite-degree pairings. -/
theorem graded_left_dual_finite_and_nondegenerate
    (F : Type u) [Field F] [MonoidalCategory (GradedVectorSpace F)]
    {V W : GradedVectorSpace F} [ExactPairing V W] :
    Module.Finite F (⨁ n, (V n : Type u)) ∧
      Nonempty (GradedNondegeneratePairing F V W) := by
  sorry

end Formalization.Books.Homology.Unit17
