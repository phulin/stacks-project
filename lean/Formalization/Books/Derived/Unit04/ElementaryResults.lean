import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Homology.Unit04.KaroubianCategories
import Formalization.Books.Homology.Unit12.CohomologicalDeltaFunctors
import Formalization.Books.Derived.Unit03.Definitions

/-!
# Derived Categories, Chapter 4: elementary results on triangulated categories

This file records the definitions and theorem interfaces in the chapter.  The
proofs of the substantive results are deliberately deferred to the proving
stage; the constructions use Mathlib's canonical triangle, shift, limit,
subcategory, and functor interfaces whenever the source gives a construction.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit03
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit12
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w

namespace Formalization.Books.Derived.Unit04

/-! ## Composition, representability, and special triangles -/

section Pretriangulated

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The three consecutive composites in a distinguished triangle vanish. -/
theorem distinguished_triangle_compositions_zero
    (T : Triangle C) (hT : T ∈ distTriang C) :
    T.mor₁ ≫ T.mor₂ = 0 ∧
      T.mor₂ ≫ T.mor₃ = 0 ∧
      T.mor₃ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
  exact ⟨distinguished_triangle_comp_zero T hT,
    distinguished_triangle_comp_zero₂₃ T hT,
    distinguished_triangle_comp_zero₃₁ T hT⟩

/- The two representable assertions are already instances in Mathlib's
   `Triangulated.Yoneda` interface. -/

/-- `Hom(W, -)` is homological. -/
theorem representable_homological (W : C) :
    (preadditiveCoyoneda.obj (Opposite.op W)).IsHomological := by
  infer_instance

/-- `Hom(-, W)` is cohomological, in the opposite-category presentation. -/
theorem representable_cohomological (W : C) :
    (preadditiveYoneda.obj W).IsHomological := by
  infer_instance

/-! ### Two out of three for morphisms of triangles -/

/-- The third component of a triangle morphism is an isomorphism when the
first two components are. -/
theorem triangle_morphism_isIso₃
    {T T' : Triangle C} (φ : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (h₁ : IsIso φ.hom₁) (h₂ : IsIso φ.hom₂) : IsIso φ.hom₃ := by
  exact isIso₃_of_isIso₁₂ φ hT hT' h₁ h₂

/-- The middle component of a triangle morphism is an isomorphism when the
first and third components are. -/
theorem triangle_morphism_isIso₂
    {T T' : Triangle C} (φ : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (h₁ : IsIso φ.hom₁) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₂ := by
  exact isIso₂_of_isIso₁₃ φ hT hT' h₁ h₃

/-- The first component of a triangle morphism is an isomorphism when the
second and third components are. -/
theorem triangle_morphism_isIso₁
    {T T' : Triangle C} (φ : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (h₂ : IsIso φ.hom₂) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₁ := by
  exact isIso₁_of_isIso₂₃ φ hT hT' h₂ h₃

/-! ### The representable long exact sequence -/

/-- Exactness of the complete representable long sequence attached to a
triangle.  The three zero equations are included explicitly because
`ShortComplex.mk` records the zero-composite proof at each position. -/
def RepresentableLongExact
    {E : Type*} [Category* E] [Preadditive E] [HasZeroObject E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] (W : E) (T : Triangle E) : Prop :=
  let F := preadditiveCoyoneda.obj (Opposite.op W)
  ∀ n : ℤ,
    ∃ h₁₂ : (F.shift n).map T.mor₁ ≫ (F.shift n).map T.mor₂ = 0,
      ∃ h₂₃ : (F.shift n).map T.mor₂ ≫
          F.homologySequenceδ T n (n + 1) (by rfl) = 0,
        ∃ h₃₁ : F.homologySequenceδ T n (n + 1) (by rfl) ≫
            (F.shift (n + 1)).map T.mor₁ = 0,
          (ShortComplex.mk ((F.shift n).map T.mor₁)
              ((F.shift n).map T.mor₂) h₁₂).Exact ∧
            (ShortComplex.mk ((F.shift n).map T.mor₂)
              (F.homologySequenceδ T n (n + 1) (by rfl)) h₂₃).Exact ∧
            (ShortComplex.mk (F.homologySequenceδ T n (n + 1) (by rfl))
              ((F.shift (n + 1)).map T.mor₁) h₃₁).Exact

/-- A triangle is special when every representable long sequence is exact. -/
def SpecialTriangle
    {E : Type*} [Category* E] [Preadditive E] [HasZeroObject E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] (T : Triangle E) : Prop :=
  ∀ W : E, RepresentableLongExact W T

/-- The dual co-special condition, transported through the canonical opposite
triangle equivalence. -/
def CoSpecialTriangle
    {E : Type*} [Category* E] [Preadditive E] [HasZeroObject E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] (T : Triangle E) : Prop :=
  SpecialTriangle ((triangleOpEquivalence E).functor.obj (Opposite.op T))

/-- Specialness is invariant under a triangle morphism when any two component
maps are isomorphisms. -/
theorem special_triangle_two_out_of_three
    {T T' : Triangle C} (hT : SpecialTriangle T)
    (hT' : SpecialTriangle T') (φ : T ⟶ T')
    (h₁ : IsIso φ.hom₁) (h₂ : IsIso φ.hom₂) : IsIso φ.hom₃ := by
  dsimp [SpecialTriangle, RepresentableLongExact] at hT hT'
  have hshift : ∀ (W : C) (n : ℤ),
      IsIso (((preadditiveCoyoneda.obj (Opposite.op W)).shift n).map φ.hom₃) := by
    intro W n
    let F := preadditiveCoyoneda.obj (Opposite.op W)
    obtain ⟨h₁₂, h₂₃, h₃₁, e₁₂, e₂₃, e₃₁⟩ := hT W n
    obtain ⟨h₁₂', h₂₃', h₃₁', e₁₂', e₂₃', e₃₁'⟩ := hT' W n
    let R : ComposableArrows AddCommGrpCat 4 :=
      ComposableArrows.mk₄
        ((F.shift n).map T.mor₁)
        ((F.shift n).map T.mor₂)
        (F.homologySequenceδ T n (n + 1) (by rfl))
        ((F.shift (n + 1)).map T.mor₁)
    let R' : ComposableArrows AddCommGrpCat 4 :=
      ComposableArrows.mk₄
        ((F.shift n).map T'.mor₁)
        ((F.shift n).map T'.mor₂)
        (F.homologySequenceδ T' n (n + 1) (by rfl))
        ((F.shift (n + 1)).map T'.mor₁)
    have hR : R.Exact := by
      dsimp [R]
      exact ComposableArrows.exact_of_δ₀
        e₁₂.exact_toComposableArrows
        (ComposableArrows.exact_of_δ₀
          e₂₃.exact_toComposableArrows e₃₁.exact_toComposableArrows)
    have hR' : R'.Exact := by
      dsimp [R']
      exact ComposableArrows.exact_of_δ₀
        e₁₂'.exact_toComposableArrows
        (ComposableArrows.exact_of_δ₀
          e₂₃'.exact_toComposableArrows e₃₁'.exact_toComposableArrows)
    let α : R ⟶ R' := ComposableArrows.homMk
      (fun i => match i with
        | ⟨0, _⟩ => (F.shift n).map φ.hom₁
        | ⟨1, _⟩ => (F.shift n).map φ.hom₂
        | ⟨2, _⟩ => (F.shift n).map φ.hom₃
        | ⟨3, _⟩ => (F.shift (n + 1)).map φ.hom₁
        | ⟨4, _⟩ => (F.shift (n + 1)).map φ.hom₂)
      (by
        intro i hi
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases hi' with rfl | rfl | rfl | rfl
        · change (F.shift n).map T.mor₁ ≫ (F.shift n).map φ.hom₂ =
            (F.shift n).map φ.hom₁ ≫ (F.shift n).map T'.mor₁
          simpa only [Functor.map_comp] using
            congrArg ((F.shift n).map) φ.comm₁
        · change (F.shift n).map T.mor₂ ≫ (F.shift n).map φ.hom₃ =
            (F.shift n).map φ.hom₂ ≫ (F.shift n).map T'.mor₂
          simpa only [Functor.map_comp] using
            congrArg ((F.shift n).map) φ.comm₂
        · change F.homologySequenceδ T n (n + 1) (by rfl) ≫
            (F.shift (n + 1)).map φ.hom₁ =
            (F.shift n).map φ.hom₃ ≫
              F.homologySequenceδ T' n (n + 1) (by rfl)
          simpa only using
            (F.homologySequenceδ_naturality T T' φ n (n + 1) (by rfl)).symm
        · change (F.shift (n + 1)).map T.mor₁ ≫
              (F.shift (n + 1)).map φ.hom₂ =
            (F.shift (n + 1)).map φ.hom₁ ≫
              (F.shift (n + 1)).map T'.mor₁
          simpa only [Functor.map_comp] using
            congrArg ((F.shift (n + 1)).map) φ.comm₁)
    change IsIso ((F.shift n).map φ.hom₃)
    have hfive := CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR hR' α
        (by change Epi ((F.shift n).map φ.hom₁); infer_instance)
        (by change IsIso ((F.shift n).map φ.hom₂); infer_instance)
        (by change IsIso ((F.shift (n + 1)).map φ.hom₁); infer_instance)
        (by change Mono ((F.shift (n + 1)).map φ.hom₂); infer_instance)
    dsimp [α] at hfive
    change IsIso ((F.shift n).map φ.hom₃) at hfive
    exact hfive
  have hraw : ∀ W : C,
      IsIso ((preadditiveCoyoneda.obj (Opposite.op W)).map φ.hom₃) := by
    intro W
    let F := preadditiveCoyoneda.obj (Opposite.op W)
    change IsIso (F.map φ.hom₃)
    have h₀ := hshift W 0
    let _ : IsIso ((F.shift (0 : ℤ)).map φ.hom₃) := h₀
    let e := F.isoShiftZero ℤ
    have h : F.map φ.hom₃ = e.inv.app T.obj₃ ≫
        (F.shift (0 : ℤ)).map φ.hom₃ ≫ e.hom.app T'.obj₃ := by
      calc
        F.map φ.hom₃ = (𝟙 _ : F.obj T.obj₃ ⟶ F.obj T.obj₃) ≫ F.map φ.hom₃ := by simp
        _ = (e.inv.app T.obj₃ ≫ e.hom.app T.obj₃) ≫ F.map φ.hom₃ := by simp
        _ = e.inv.app T.obj₃ ≫ (e.hom.app T.obj₃ ≫ F.map φ.hom₃) := by simp
        _ = e.inv.app T.obj₃ ≫
            ((F.shift (0 : ℤ)).map φ.hom₃ ≫ e.hom.app T'.obj₃) := by
              rw [e.hom.naturality]
        _ = e.inv.app T.obj₃ ≫
            (F.shift (0 : ℤ)).map φ.hom₃ ≫ e.hom.app T'.obj₃ := by simp
    rw [h]
    infer_instance
  exact isIso_of_yoneda_map_bijective φ.hom₃ (by
    intro W
    let F := preadditiveCoyoneda.obj (Opposite.op W)
    let _ : IsIso (F.map φ.hom₃) := hraw W
    change Function.Bijective (fun x : W ⟶ T.obj₃ => x ≫ φ.hom₃)
    have hb := ConcreteCategory.bijective_of_isIso (f := F.map φ.hom₃)
    change Function.Bijective (fun x : W ⟶ T.obj₃ => x ≫ φ.hom₃) at hb
    exact hb)

/-- The middle component of a special-triangle morphism is an isomorphism when
the first and third components are. -/
theorem special_triangle_isIso₂
    {T T' : Triangle C} (hT : SpecialTriangle T)
    (hT' : SpecialTriangle T') (φ : T ⟶ T')
    (h₁ : IsIso φ.hom₁) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₂ := by
  dsimp [SpecialTriangle, RepresentableLongExact] at hT hT'
  have hshift : ∀ (W : C) (n : ℤ),
      IsIso (((preadditiveCoyoneda.obj (Opposite.op W)).shift n).map φ.hom₂) := by
    intro W n
    let F := preadditiveCoyoneda.obj (Opposite.op W)
    obtain ⟨_, _, _, _, _, e₃₁⟩ := hT W (n - 1)
    obtain ⟨h₁₂, h₂₃, _, e₁₂, e₂₃, _⟩ := hT W (n - 1 + 1)
    obtain ⟨_, _, _, _, _, e₃₁'⟩ := hT' W (n - 1)
    obtain ⟨h₁₂', h₂₃', _, e₁₂', e₂₃', _⟩ := hT' W (n - 1 + 1)
    let R : ComposableArrows AddCommGrpCat 4 :=
      ComposableArrows.mk₄
        (F.homologySequenceδ T (n - 1) (n - 1 + 1) (by rfl))
        ((F.shift (n - 1 + 1)).map T.mor₁)
        ((F.shift (n - 1 + 1)).map T.mor₂)
        (F.homologySequenceδ T (n - 1 + 1) (n - 1 + 1 + 1) (by rfl))
    let R' : ComposableArrows AddCommGrpCat 4 :=
      ComposableArrows.mk₄
        (F.homologySequenceδ T' (n - 1) (n - 1 + 1) (by rfl))
        ((F.shift (n - 1 + 1)).map T'.mor₁)
        ((F.shift (n - 1 + 1)).map T'.mor₂)
        (F.homologySequenceδ T' (n - 1 + 1) (n - 1 + 1 + 1) (by rfl))
    have hR : R.Exact := by
      dsimp [R]
      exact ComposableArrows.exact_of_δ₀
        e₃₁.exact_toComposableArrows
        (ComposableArrows.exact_of_δ₀
          e₁₂.exact_toComposableArrows e₂₃.exact_toComposableArrows)
    have hR' : R'.Exact := by
      dsimp [R']
      exact ComposableArrows.exact_of_δ₀
        e₃₁'.exact_toComposableArrows
        (ComposableArrows.exact_of_δ₀
          e₁₂'.exact_toComposableArrows e₂₃'.exact_toComposableArrows)
    let α : R ⟶ R' := ComposableArrows.homMk
      (fun i => match i with
        | ⟨0, _⟩ => (F.shift (n - 1)).map φ.hom₃
        | ⟨1, _⟩ => (F.shift (n - 1 + 1)).map φ.hom₁
        | ⟨2, _⟩ => (F.shift (n - 1 + 1)).map φ.hom₂
        | ⟨3, _⟩ => (F.shift (n - 1 + 1)).map φ.hom₃
        | ⟨4, _⟩ => (F.shift (n - 1 + 1 + 1)).map φ.hom₁)
      (by
        intro i hi
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases hi' with rfl | rfl | rfl | rfl
        · change F.homologySequenceδ T (n - 1) (n - 1 + 1) (by rfl) ≫
              (F.shift (n - 1 + 1)).map φ.hom₁ =
            (F.shift (n - 1)).map φ.hom₃ ≫
              F.homologySequenceδ T' (n - 1) (n - 1 + 1) (by rfl)
          simpa only using
            (F.homologySequenceδ_naturality T T' φ (n - 1) (n - 1 + 1) (by rfl)).symm
        · change (F.shift (n - 1 + 1)).map T.mor₁ ≫
              (F.shift (n - 1 + 1)).map φ.hom₂ =
            (F.shift (n - 1 + 1)).map φ.hom₁ ≫
              (F.shift (n - 1 + 1)).map T'.mor₁
          simpa only [Functor.map_comp] using
            congrArg ((F.shift (n - 1 + 1)).map) φ.comm₁
        · change (F.shift (n - 1 + 1)).map T.mor₂ ≫
              (F.shift (n - 1 + 1)).map φ.hom₃ =
            (F.shift (n - 1 + 1)).map φ.hom₂ ≫
              (F.shift (n - 1 + 1)).map T'.mor₂
          simpa only [Functor.map_comp] using
            congrArg ((F.shift (n - 1 + 1)).map) φ.comm₂
        · change F.homologySequenceδ T (n - 1 + 1) (n - 1 + 1 + 1) (by rfl) ≫
              (F.shift (n - 1 + 1 + 1)).map φ.hom₁ =
            (F.shift (n - 1 + 1)).map φ.hom₃ ≫
              F.homologySequenceδ T' (n - 1 + 1) (n - 1 + 1 + 1) (by rfl)
          simpa only using
            (F.homologySequenceδ_naturality T T' φ (n - 1 + 1)
              (n - 1 + 1 + 1) (by rfl)).symm)
    have hfive := CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR hR' α
      (by change Epi ((F.shift (n - 1)).map φ.hom₃); infer_instance)
      (by change IsIso ((F.shift (n - 1 + 1)).map φ.hom₁); infer_instance)
      (by change IsIso ((F.shift (n - 1 + 1)).map φ.hom₃); infer_instance)
      (by change Mono ((F.shift (n - 1 + 1 + 1)).map φ.hom₁); infer_instance)
    dsimp [α] at hfive
    change IsIso ((F.shift (n - 1 + 1)).map φ.hom₂) at hfive
    have hn : n - 1 + 1 = n := by omega
    rw [hn] at hfive
    exact hfive
  have hraw : ∀ W : C,
      IsIso ((preadditiveCoyoneda.obj (Opposite.op W)).map φ.hom₂) := by
    intro W
    let F := preadditiveCoyoneda.obj (Opposite.op W)
    change IsIso (F.map φ.hom₂)
    have h₀ := hshift W 0
    let _ : IsIso ((F.shift (0 : ℤ)).map φ.hom₂) := h₀
    let e := F.isoShiftZero ℤ
    have h : F.map φ.hom₂ = e.inv.app T.obj₂ ≫
        (F.shift (0 : ℤ)).map φ.hom₂ ≫ e.hom.app T'.obj₂ := by
      calc
        F.map φ.hom₂ = (𝟙 _ : F.obj T.obj₂ ⟶ F.obj T.obj₂) ≫ F.map φ.hom₂ := by simp
        _ = (e.inv.app T.obj₂ ≫ e.hom.app T.obj₂) ≫ F.map φ.hom₂ := by simp
        _ = e.inv.app T.obj₂ ≫ (e.hom.app T.obj₂ ≫ F.map φ.hom₂) := by simp
        _ = e.inv.app T.obj₂ ≫
            ((F.shift (0 : ℤ)).map φ.hom₂ ≫ e.hom.app T'.obj₂) := by
              rw [e.hom.naturality]
        _ = e.inv.app T.obj₂ ≫
            (F.shift (0 : ℤ)).map φ.hom₂ ≫ e.hom.app T'.obj₂ := by simp
    rw [h]
    infer_instance
  exact isIso_of_yoneda_map_bijective φ.hom₂ (by
    intro W
    let F := preadditiveCoyoneda.obj (Opposite.op W)
    let _ : IsIso (F.map φ.hom₂) := hraw W
    change Function.Bijective (fun x : W ⟶ T.obj₂ => x ≫ φ.hom₂)
    have hb := ConcreteCategory.bijective_of_isIso (f := F.map φ.hom₂)
    change Function.Bijective (fun x : W ⟶ T.obj₂ => x ≫ φ.hom₂) at hb
    exact hb)

/-- The first component of a special-triangle morphism is an isomorphism when
the second and third components are. -/
theorem special_triangle_isIso₁
    {T T' : Triangle C} (hT : SpecialTriangle T)
    (hT' : SpecialTriangle T') (φ : T ⟶ T')
    (h₂ : IsIso φ.hom₂) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₁ := by
  dsimp [SpecialTriangle, RepresentableLongExact] at hT hT'
  have hshift : ∀ (W : C) (n : ℤ),
      IsIso (((preadditiveCoyoneda.obj (Opposite.op W)).shift n).map φ.hom₁) := by
    intro W n
    let F := preadditiveCoyoneda.obj (Opposite.op W)
    obtain ⟨_, h₂₃prev, h₃₁prev, _, e₂₃prev, e₃₁prev⟩ := hT W (n - 1)
    obtain ⟨h₁₂, h₂₃, _, e₁₂, e₂₃, _⟩ := hT W (n - 1 + 1)
    obtain ⟨_, h₂₃prev', h₃₁prev', _, e₂₃prev', e₃₁prev'⟩ := hT' W (n - 1)
    obtain ⟨h₁₂', h₂₃', _, e₁₂', e₂₃', _⟩ := hT' W (n - 1 + 1)
    let R : ComposableArrows AddCommGrpCat 4 :=
      ComposableArrows.mk₄
        ((F.shift (n - 1)).map T.mor₂)
        (F.homologySequenceδ T (n - 1) (n - 1 + 1) (by rfl))
        ((F.shift (n - 1 + 1)).map T.mor₁)
        ((F.shift (n - 1 + 1)).map T.mor₂)
    let R' : ComposableArrows AddCommGrpCat 4 :=
      ComposableArrows.mk₄
        ((F.shift (n - 1)).map T'.mor₂)
        (F.homologySequenceδ T' (n - 1) (n - 1 + 1) (by rfl))
        ((F.shift (n - 1 + 1)).map T'.mor₁)
        ((F.shift (n - 1 + 1)).map T'.mor₂)
    have hR : R.Exact := by
      dsimp [R]
      exact ComposableArrows.exact_of_δ₀
        e₂₃prev.exact_toComposableArrows
        (ComposableArrows.exact_of_δ₀
          e₃₁prev.exact_toComposableArrows e₁₂.exact_toComposableArrows)
    have hR' : R'.Exact := by
      dsimp [R']
      exact ComposableArrows.exact_of_δ₀
        e₂₃prev'.exact_toComposableArrows
        (ComposableArrows.exact_of_δ₀
          e₃₁prev'.exact_toComposableArrows e₁₂'.exact_toComposableArrows)
    let α : R ⟶ R' := ComposableArrows.homMk
      (fun i => match i with
        | ⟨0, _⟩ => (F.shift (n - 1)).map φ.hom₂
        | ⟨1, _⟩ => (F.shift (n - 1)).map φ.hom₃
        | ⟨2, _⟩ => (F.shift (n - 1 + 1)).map φ.hom₁
        | ⟨3, _⟩ => (F.shift (n - 1 + 1)).map φ.hom₂
        | ⟨4, _⟩ => (F.shift (n - 1 + 1)).map φ.hom₃)
      (by
        intro i hi
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases hi' with rfl | rfl | rfl | rfl
        · change (F.shift (n - 1)).map T.mor₂ ≫
              (F.shift (n - 1)).map φ.hom₃ =
            (F.shift (n - 1)).map φ.hom₂ ≫
              (F.shift (n - 1)).map T'.mor₂
          simpa only [Functor.map_comp] using
            congrArg ((F.shift (n - 1)).map) φ.comm₂
        · change F.homologySequenceδ T (n - 1) (n - 1 + 1) (by rfl) ≫
              (F.shift (n - 1 + 1)).map φ.hom₁ =
            (F.shift (n - 1)).map φ.hom₃ ≫
              F.homologySequenceδ T' (n - 1) (n - 1 + 1) (by rfl)
          simpa only using
            (F.homologySequenceδ_naturality T T' φ (n - 1)
              (n - 1 + 1) (by rfl)).symm
        · change (F.shift (n - 1 + 1)).map T.mor₁ ≫
              (F.shift (n - 1 + 1)).map φ.hom₂ =
            (F.shift (n - 1 + 1)).map φ.hom₁ ≫
              (F.shift (n - 1 + 1)).map T'.mor₁
          simpa only [Functor.map_comp] using
            congrArg ((F.shift (n - 1 + 1)).map) φ.comm₁
        · change (F.shift (n - 1 + 1)).map T.mor₂ ≫
              (F.shift (n - 1 + 1)).map φ.hom₃ =
            (F.shift (n - 1 + 1)).map φ.hom₂ ≫
              (F.shift (n - 1 + 1)).map T'.mor₂
          simpa only [Functor.map_comp] using
            congrArg ((F.shift (n - 1 + 1)).map) φ.comm₂)
    have hfive := CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR hR' α
      (by change Epi ((F.shift (n - 1)).map φ.hom₂); infer_instance)
      (by change IsIso ((F.shift (n - 1)).map φ.hom₃); infer_instance)
      (by change IsIso ((F.shift (n - 1 + 1)).map φ.hom₂); infer_instance)
      (by change Mono ((F.shift (n - 1 + 1)).map φ.hom₃); infer_instance)
    dsimp [α] at hfive
    change IsIso ((F.shift (n - 1 + 1)).map φ.hom₁) at hfive
    have hn : n - 1 + 1 = n := by omega
    rw [hn] at hfive
    exact hfive
  have hraw : ∀ W : C,
      IsIso ((preadditiveCoyoneda.obj (Opposite.op W)).map φ.hom₁) := by
    intro W
    let F := preadditiveCoyoneda.obj (Opposite.op W)
    change IsIso (F.map φ.hom₁)
    have h₀ := hshift W 0
    let _ : IsIso ((F.shift (0 : ℤ)).map φ.hom₁) := h₀
    let e := F.isoShiftZero ℤ
    have h : F.map φ.hom₁ = e.inv.app T.obj₁ ≫
        (F.shift (0 : ℤ)).map φ.hom₁ ≫ e.hom.app T'.obj₁ := by
      calc
        F.map φ.hom₁ = (𝟙 _ : F.obj T.obj₁ ⟶ F.obj T.obj₁) ≫ F.map φ.hom₁ := by simp
        _ = (e.inv.app T.obj₁ ≫ e.hom.app T.obj₁) ≫ F.map φ.hom₁ := by simp
        _ = e.inv.app T.obj₁ ≫ (e.hom.app T.obj₁ ≫ F.map φ.hom₁) := by simp
        _ = e.inv.app T.obj₁ ≫
            ((F.shift (0 : ℤ)).map φ.hom₁ ≫ e.hom.app T'.obj₁) := by
              rw [e.hom.naturality]
        _ = e.inv.app T.obj₁ ≫
            (F.shift (0 : ℤ)).map φ.hom₁ ≫ e.hom.app T'.obj₁ := by simp
    rw [h]
    infer_instance
  exact isIso_of_yoneda_map_bijective φ.hom₁ (by
    intro W
    let F := preadditiveCoyoneda.obj (Opposite.op W)
    let _ : IsIso (F.map φ.hom₁) := hraw W
    change Function.Bijective (fun x : W ⟶ T.obj₁ => x ≫ φ.hom₁)
    have hb := ConcreteCategory.bijective_of_isIso (f := F.map φ.hom₁)
    change Function.Bijective (fun x : W ⟶ T.obj₁ => x ≫ φ.hom₁) at hb
    exact hb)

/-- The dual two-out-of-three statement for co-special triangles. -/
theorem coSpecial_triangle_two_out_of_three
    {T T' : Triangle C} (hT : CoSpecialTriangle T)
    (hT' : CoSpecialTriangle T') (φ : T ⟶ T')
    (h₁ : IsIso φ.hom₁) (h₂ : IsIso φ.hom₂) : IsIso φ.hom₃ := by
  dsimp [CoSpecialTriangle] at hT hT'
  let Top : Triangle Cᵒᵖ := (triangleOpEquivalence C).functor.obj (Opposite.op T)
  let Topp : Triangle Cᵒᵖ := (triangleOpEquivalence C).functor.obj (Opposite.op T')
  let phop : Topp ⟶ Top := (triangleOpEquivalence C).functor.map (Opposite.op φ)
  have h2op : IsIso phop.hom₂ := by
    change IsIso (φ.hom₂.op : Topp.obj₂ ⟶ Top.obj₂)
    exact (isIso_op_iff φ.hom₂).2 h₂
  have h3op : IsIso phop.hom₃ := by
    change IsIso (φ.hom₁.op : Topp.obj₃ ⟶ Top.obj₃)
    exact (isIso_op_iff φ.hom₁).2 h₁
  have h1op : IsIso phop.hom₁ :=
    special_triangle_isIso₁ (C := Cᵒᵖ) (T := Topp) (T' := Top)
      hT' hT phop h2op h3op
  have h1op' : IsIso (φ.hom₃.op : Topp.obj₁ ⟶ Top.obj₁) := by
    change IsIso (φ.hom₃.op : Topp.obj₁ ⟶ Top.obj₁) at h1op
    exact h1op
  let _ : IsIso φ.hom₃.op := h1op'
  exact isIso_of_op φ.hom₃

/-- The middle component of a co-special-triangle morphism is an isomorphism
when the first and third components are. -/
theorem coSpecial_triangle_isIso₂
    {T T' : Triangle C} (hT : CoSpecialTriangle T)
    (hT' : CoSpecialTriangle T') (φ : T ⟶ T')
    (h₁ : IsIso φ.hom₁) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₂ := by
  let Top : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T)
  let Topp : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T')
  let phop : Topp ⟶ Top :=
    (triangleOpEquivalence C).functor.map (Opposite.op φ)
  have hTopp : SpecialTriangle Topp := hT'
  have hTop : SpecialTriangle Top := hT
  have h1op : IsIso phop.hom₃ := by
    change IsIso (φ.hom₁.op : Topp.obj₃ ⟶ Top.obj₃)
    exact (isIso_op_iff φ.hom₁).2 h₁
  have h3op : IsIso phop.hom₁ := by
    change IsIso (φ.hom₃.op : Topp.obj₁ ⟶ Top.obj₁)
    exact (isIso_op_iff φ.hom₃).2 h₃
  exact (isIso_op_iff φ.hom₂).1
    (special_triangle_isIso₂ (C := Cᵒᵖ) (T := Topp) (T' := Top)
      hTopp hTop phop h3op h1op)

/-- The first component of a co-special-triangle morphism is an isomorphism
when the second and third components are. -/
theorem coSpecial_triangle_isIso₁
    {T T' : Triangle C} (hT : CoSpecialTriangle T)
    (hT' : CoSpecialTriangle T') (φ : T ⟶ T')
    (h₂ : IsIso φ.hom₂) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₁ := by
  let Top : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T)
  let Topp : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T')
  let phop : Topp ⟶ Top :=
    (triangleOpEquivalence C).functor.map (Opposite.op φ)
  have hTopp : SpecialTriangle Topp := hT'
  have hTop : SpecialTriangle Top := hT
  have h2op : IsIso phop.hom₂ := by
    change IsIso (φ.hom₂.op : Topp.obj₂ ⟶ Top.obj₂)
    exact (isIso_op_iff φ.hom₂).2 h₂
  have h3op : IsIso phop.hom₁ := by
    change IsIso (φ.hom₃.op : Topp.obj₁ ⟶ Top.obj₁)
    exact (isIso_op_iff φ.hom₃).2 h₃
  exact (isIso_op_iff φ.hom₁).1
    (special_triangle_two_out_of_three (C := Cᵒᵖ) (T := Topp) (T' := Top)
      hTopp hTop phop h3op h2op)

/-- Every distinguished triangle is special. -/
theorem distinguished_triangle_special
    (T : Triangle C) (hT : T ∈ distTriang C) : SpecialTriangle T := by
  intro W n
  let F := preadditiveCoyoneda.obj (Opposite.op W)
  refine ⟨F.homologySequence_comp T hT n, ?_, ?_, ?_, ?_, ?_⟩
  · exact F.comp_homologySequenceδ T hT n (n + 1) (by rfl)
  · exact F.homologySequenceδ_comp T hT n (n + 1) (by rfl)
  · exact F.homologySequence_exact₂ T hT n
  · exact F.homologySequence_exact₃ T hT n (n + 1) (by rfl)
  · exact F.homologySequence_exact₁ T hT n (n + 1) (by rfl)

/-- Every distinguished triangle is co-special. -/
theorem distinguished_triangle_coSpecial
    (T : Triangle C) (hT : T ∈ distTriang C) : CoSpecialTriangle T := by
  let Top : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T)
  change SpecialTriangle Top
  have hTop : Top ∈ distTriang Cᵒᵖ := op_distinguished T hT
  exact distinguished_triangle_special (C := Cᵒᵖ) Top hTop

/-! ## Square-zero, idempotents, and cones -/

/-- The middle component of the composite of two endomorphisms with zero first
and third components is zero. -/
theorem triangle_middle_composite_zero
    {T : Triangle C} (hT : T ∈ distTriang C)
    (φ ψ : T ⟶ T)
    (hφ₁ : φ.hom₁ = 0) (hφ₃ : φ.hom₃ = 0)
    (hψ₁ : ψ.hom₁ = 0) (hψ₃ : ψ.hom₃ = 0) :
    φ.hom₂ ≫ ψ.hom₂ = 0 := by
  sorry

/-- An idempotent pair on the ends of a distinguished triangle extends to an
idempotent endomorphism of the triangle. -/
theorem exists_idempotent_triangle_endomorphism
    {T : Triangle C} (hT : T ∈ distTriang C)
    (a : T.obj₁ ⟶ T.obj₁) (c : T.obj₃ ⟶ T.obj₃)
    (ha : a ≫ a = a) (hc : c ≫ c = c)
    (hcomm : T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T.mor₃) :
    ∃ (b : T.obj₂ ⟶ T.obj₂), b ≫ b = b ∧
      ∃ φ : T ⟶ T, φ.hom₁ = a ∧ φ.hom₂ = b ∧ φ.hom₃ = c := by
  sorry

/-- Every morphism has a distinguished cone triangle. -/
theorem distinguished_cone_exists {X Y : C} (f : X ⟶ Y) :
    ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C :=
  Pretriangulated.distinguished_cocone_triangle f

/-- Two distinguished cones of the same morphism are isomorphic by a triangle
isomorphism whose first two components are identities. -/
theorem distinguished_cone_unique
    {X Y Z Z' : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}
    {g' : Y ⟶ Z'} {h' : Z' ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hT' : Triangle.mk f g' h' ∈ distTriang C) :
    ∃ e : Triangle.mk f g h ≅ Triangle.mk f g' h',
      e.hom.hom₁ = 𝟙 X ∧ e.hom.hom₂ = 𝟙 Y := by
  sorry

/- The source's five vanishing conditions are a useful reusable interface for
   its uniqueness-of-the-third-arrow lemma. -/

/-- All morphisms between two specified objects vanish. -/
def HomIsZero (X Y : C) : Prop :=
  ∀ f : X ⟶ Y, f = 0

/-- Under any one of the five source vanishing hypotheses, the middle map of a
triangle morphism is determined by its first and third maps. -/
theorem triangle_middle_map_unique
    {T T' : Triangle C} (φ ψ : T ⟶ T')
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (hzero :
      HomIsZero T.obj₂ T'.obj₁ ∨
      HomIsZero T.obj₃ T'.obj₂ ∨
      (HomIsZero T.obj₁ T'.obj₁ ∧ HomIsZero T.obj₃ T'.obj₁) ∨
      (HomIsZero T.obj₃ T'.obj₁ ∧ HomIsZero T.obj₃ T'.obj₃) ∨
      (HomIsZero (T.obj₁⟦(1 : ℤ)⟧) T'.obj₃ ∧ HomIsZero T.obj₃ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := by
  sorry

/-! ## Zero objects, sums, and split triangles -/

/-- The three equivalent zero-cone criteria, with `IsZero Z` expressing the
invariant meaning of the source's phrase `Z = 0`. -/
theorem third_object_zero_characterization
    {X Y : C} (f : X ⟶ Y) :
    (IsIso f ↔
      Triangle.mk f (0 : Y ⟶ (0 : C))
          (0 : (0 : C) ⟶ X⟦(1 : ℤ)⟧) ∈ distTriang C) ∧
    (IsIso f ↔
      ∀ {Z : C} (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C → IsZero Z) := by
  sorry

/-- The direct sum of two triangles, using the canonical biproduct and the
shift comparison isomorphism for the third map. -/
noncomputable def shiftBiprodIso (X Y : C) :
    (shiftFunctor C (1 : ℤ)).obj (X ⊞ Y) ≅
      (shiftFunctor C (1 : ℤ)).obj X ⊞ (shiftFunctor C (1 : ℤ)).obj Y := by
  let F := shiftFunctor C (1 : ℤ)
  refine
    { hom := Functor.biprodComparison F X Y
      inv := Functor.biprodComparison' F X Y
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · dsimp [Functor.biprodComparison, Functor.biprodComparison']
    rw [biprod.lift_desc, ← F.map_comp, ← F.map_comp, ← F.map_add,
      biprod.total, F.map_id]
  · exact Functor.biprodComparison'_comp_biprodComparison F X Y

def directSumTriangle (T T' : Triangle C) : Triangle C :=
  Triangle.mk
    (biprod.map T.mor₁ T'.mor₁)
    (biprod.map T.mor₂ T'.mor₂)
    ((biprod.map T.mor₃ T'.mor₃) ≫
      (shiftBiprodIso T.obj₁ T'.obj₁).inv)

/-- A direct sum triangle is distinguished exactly when both summands are. -/
theorem direct_sum_triangle_distinguished_iff
    (T T' : Triangle C) :
    directSumTriangle T T' ∈ distTriang C ↔
      T ∈ distTriang C ∧ T' ∈ distTriang C := by
  sorry

/-- A right inverse of a morphism, in the categorical composition convention. -/
def TriangleRightInverse {Y Z : C} (g : Y ⟶ Z) (s : Z ⟶ Y) : Prop :=
  g ≫ s = 𝟙 Y

/-- If the third map of a distinguished triangle is zero, its second map has a
right inverse. -/
theorem distinguished_triangle_second_right_inverse
    {T : Triangle C} (hT : T ∈ distTriang C) (hzero : T.mor₃ = 0) :
    ∃ s : T.obj₃ ⟶ T.obj₂, TriangleRightInverse T.mor₂ s := by
  sorry

/-- A right inverse of the second map makes the biproduct comparison map an
isomorphism. -/
theorem split_triangle_biproduct_iso
    {T : Triangle C} (s : T.obj₃ ⟶ T.obj₂)
    (hs : TriangleRightInverse T.mor₂ s) :
    IsIso (biprod.desc T.mor₁ s) := by
  sorry

/-- The standard split triangle is distinguished. -/
theorem split_triangle_distinguished (X Z : C) :
    Triangle.mk (biprod.inl : X ⟶ X ⊞ Z)
      (biprod.snd : X ⊞ Z ⟶ Z)
      (0 : Z ⟶ X⟦(1 : ℤ)⟧) ∈ distTriang C := by
  simpa [binaryBiproductTriangle] using
    (binaryBiproductTriangle_distinguished X Z)

/-- A morphism is a projection followed by a coprojection up to isomorphism. -/
def ProjectionCoprojection {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ (K Z Q : C) (eX : X ≅ K ⊞ Z) (eY : Y ≅ Z ⊞ Q),
    f = eX.hom ≫ biprod.snd ≫ biprod.inl ≫ eY.inv

/-- For a split morphism, existence of a kernel, existence of a cokernel, and
the projection--coprojection normal form are equivalent. -/
theorem split_morphism_kernel_cokernel_iff
    {X Y : C} (f : X ⟶ Y) :
    (HasKernel f ↔ HasCokernel f) ∧
      (HasCokernel f ↔ ProjectionCoprojection f) := by
  sorry

end Pretriangulated

/-! ## Products, coproducts, and idempotent completeness -/

section ProductsAndIdempotents

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- A shift equivalence transports any existing product to the product of the
shifted family. -/
theorem shift_has_product
    {J : Type w} (X : J → C) [HasProduct X] :
    HasProduct (fun j => X j⟦(1 : ℤ)⟧) := by
  sorry

/-- The dual coproduct transport along a shift equivalence. -/
theorem shift_has_coproduct
    {J : Type w} (X : J → C) [HasCoproduct X] :
    HasCoproduct (fun j => X j⟦(1 : ℤ)⟧) := by
  sorry

/-- The shift comparison for a product is an isomorphism whenever the source
and shifted products exist. -/
theorem shift_product_comparison_isIso
    {J : Type w} (X : J → C)
    [HasProduct X] [HasProduct (fun j => X j⟦(1 : ℤ)⟧)] :
    IsIso (piComparison (shiftFunctor C (1 : ℤ)) X) := by
  sorry

/-- The dual shift comparison for a coproduct is an isomorphism whenever the
source and shifted coproducts exist. -/
theorem shift_coproduct_comparison_isIso
    {J : Type w} (X : J → C)
    [HasCoproduct X] [HasCoproduct (fun j => X j⟦(1 : ℤ)⟧)] :
    IsIso (sigmaComparison (shiftFunctor C (1 : ℤ)) X) := by
  sorry

/-- Products of distinguished triangles are distinguished. -/
theorem product_of_distinguished_triangles
    {J : Type w} (T : J → Triangle C)
    (hT : ∀ j, T j ∈ distTriang C)
    [HasProduct (fun j => (T j).obj₁)]
    [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)]
    [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)] :
    productTriangle T ∈ distTriang C :=
  productTriangle_distinguished T hT

/-- The canonical coproduct triangle, with the third map transported across
the shift--coproduct comparison. -/
def coproductTriangle
    {J : Type w} (T : J → Triangle C)
    [HasCoproduct (fun j => (T j).obj₁)]
    [HasCoproduct (fun j => (T j).obj₂)]
    [HasCoproduct (fun j => (T j).obj₃)]
    [HasCoproduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)] : Triangle C :=
  Triangle.mk
    (Limits.Sigma.map fun j => (T j).mor₁)
    (Limits.Sigma.map fun j => (T j).mor₂)
    ((Limits.Sigma.map fun j => (T j).mor₃) ≫
      sigmaComparison (shiftFunctor C (1 : ℤ)) (fun j => (T j).obj₁))

/-- Coproducts of distinguished triangles are distinguished. -/
theorem coproduct_of_distinguished_triangles
    {J : Type w} (T : J → Triangle C)
    (hT : ∀ j, T j ∈ distTriang C)
    [HasCoproduct (fun j => (T j).obj₁)]
    [HasCoproduct (fun j => (T j).obj₂)]
    [HasCoproduct (fun j => (T j).obj₃)]
    [HasCoproduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)] :
    coproductTriangle T ∈ distTriang C := by
  sorry

/-- Countable products imply that the preadditive triangulated category is
Karoubian. -/
theorem karoubian_of_countable_products
    [HasCountableProducts C] : IsIdempotentComplete C := by
  sorry

/-- Countable coproducts imply that the preadditive triangulated category is
Karoubian. -/
theorem karoubian_of_countable_coproducts
    [HasCountableCoproducts C] : IsIdempotentComplete C := by
  sorry

/-! ## The octahedral axiom and full subcategories -/

/-- The data of the three distinguished triangles and the octahedron used in
TR4 for a composable pair.  This is the canonical Mathlib `Octahedron` datum,
with only the three cone triangles made explicit at the source-facing level. -/
structure OctahedronWitness {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) where
  Qone : C
  Qtwo : C
  Qthree : C
  pone : Y ⟶ Qone
  done : Qone ⟶ X⟦(1 : ℤ)⟧
  ptwo : Z ⟶ Qtwo
  dtwo : Qtwo ⟶ X⟦(1 : ℤ)⟧
  pthree : Z ⟶ Qthree
  dthree : Qthree ⟶ Y⟦(1 : ℤ)⟧
  h₁₂ : Triangle.mk f pone done ∈ distTriang C
  h₁₃ : Triangle.mk (f ≫ g) ptwo dtwo ∈ distTriang C
  h₂₃ : Triangle.mk g pthree dthree ∈ distTriang C
  octahedron :
    Nonempty (Triangulated.Octahedron (C := C) (by rfl) h₁₂ h₂₃ h₁₃)

/-- The source's easier formulation of TR4 is equivalent to the canonical
octahedron axiom after replacing the three objects by isomorphic ones. -/
theorem easier_axiom_four_iff :
    CategoryTheory.IsTriangulated C ↔
      ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
        ∃ (X' Y' Z' : C) (eX : X' ≅ X) (eY : Y' ≅ Y) (eZ : Z' ≅ Z),
          Nonempty (OctahedronWitness
            (eX.hom ≫ f ≫ eY.inv) (eY.hom ≫ g ≫ eZ.inv)) := by
  sorry

/-- The source-facing closure condition for a full triangulated subcategory:
it contains shifted objects and contains a cone, up to the property's
isomorphism closure, for every morphism between its objects. -/
def FullTriangulatedSubcategoryCondition (P : ObjectProperty C) : Prop :=
  P.IsStableUnderShift ℤ ∧
    ∀ {X Y : C} (f : X ⟶ Y), P X → P Y →
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧ P.isoClosure Z

/-- Under the zero-object condition, the source's cone-and-shift criterion is
the canonical `ObjectProperty.IsTriangulated` class. -/
theorem full_subcategory_isTriangulated_iff
    (P : ObjectProperty C) [P.ContainsZero] :
    P.IsTriangulated ↔ FullTriangulatedSubcategoryCondition P := by
  sorry

/-- The distinguished triangles of the full subcategory are exactly the
ambient distinguished triangles whose three objects lie in the property. -/
def fullSubcategoryDistinguishedTriangles
    (P : ObjectProperty C) [P.IsTriangulated] :
    Set (Triangle P.FullSubcategory) :=
  Set.preimage P.ι.mapTriangle.obj (distTriang C)

end ProductsAndIdempotents

/-! ## Exact functors, homological functors, and δ-functors -/

section ExactFunctors

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [AdditiveCategory C] [AdditiveCategory D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- Exact functors are additive; this chapter assertion is the earlier
`Unit03.exact_functor_additive` interface. -/
theorem exact_functor_is_additive
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] : F.Additive :=
  exact_functor_additive F

/-- A fully faithful exact functor reflects distinguished triangles. -/
theorem exact_fully_faithful_reflects_distinguished
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful]
    (T : Triangle C) :
    F.mapTriangle.obj T ∈ distTriang D ↔ T ∈ distTriang C :=
  F.map_distinguished_iff T

/-- Exact functors compose. -/
theorem exact_functors_compose
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    {E : Type u'} [Category.{v'} E] [AdditiveCategory E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] (G : D ⥤ E) [G.CommShift ℤ] [G.IsTriangulated] :
    (F ⋙ G).IsTriangulated := by
  infer_instance

/-- Exact precomposition preserves homological functors. -/
theorem exact_precomposition_preserves_homological
    {A : Type u'} [Category.{v'} A] [Abelian A]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (H : D ⥤ A) [H.IsHomological] :
    (F ⋙ H).IsHomological := by
  infer_instance

/-- Exact postcomposition in an abelian target preserves homological functors. -/
theorem exact_postcomposition_preserves_homological
    {A B : Type u'} [Category.{v'} A] [Category.{v'} B]
    [Abelian A] [Abelian B]
    (H : D ⥤ A) [H.IsHomological] (G : A ⥤ B)
    (hG : IsExact G) :
    (H ⋙ G).IsHomological := by
  sorry

end ExactFunctors

/-! ## Delta-functors -/

section DeltaFunctors

variable {A A' B : Type u} [Category.{v} A] [Category.{v} A']
  [Category.{v} B] [Abelian A] [Abelian A'] [Abelian B]

variable {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [CategoryTheory.IsTriangulated D]

/-- Exact postcomposition carries a δ-functor to a δ-functor. -/
theorem exact_postcomposition_deltaFunctor
    {E : Type w} [Category.{v'} E] [AdditiveCategory E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] [CategoryTheory.IsTriangulated E]
    (F : A ⥤ D) (δ : DeltaFunctor F) (K : D ⥤ E)
    [K.CommShift ℤ] [K.IsTriangulated] :
    Nonempty (DeltaFunctor (F ⋙ K)) := by
  sorry

/-- Exact precomposition carries a δ-functor to a δ-functor. -/
theorem exact_precomposition_deltaFunctor
    (F : A ⥤ D) (δ : DeltaFunctor F) (K : A' ⥤ A)
    (hK : IsExact K) :
    Nonempty (DeltaFunctor (K ⋙ F)) := by
  sorry

/-- Postcomposing a homological functor with an exact abelian functor remains
homological. -/
theorem exact_abelian_postcomposition_homological
    (H : D ⥤ A) [H.IsHomological] (K : A ⥤ A')
    (hK : IsExact K) :
    (H ⋙ K).IsHomological := by
  sorry

/-- The degreewise cohomology of a δ-functor after a homological functor is a
cohomological δ-functor under the source's negative-degree vanishing
hypothesis. -/
theorem homological_compose_deltaFunctor
    (G : A ⥤ D) (δ : DeltaFunctor G) (H : D ⥤ B)
    [H.IsHomological]
    (hvanish : ∀ X : A,
      IsZero ((homologicalDegree H (-1 : ℤ)).obj (G.obj X))) :
    Nonempty (CohomologicalDeltaFunctor A B) := by
  sorry

end DeltaFunctors

/-! ## The 3 by 3 diagram -/

section ThreeByThree

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- All rows and columns of the source's 3 by 3 diagram, including the
commutativity conditions and the single anticommuting lower-right square.  The
bottom row and rightmost column use shift maps literally, so the source's
``obtained by applying [1]`` clause is part of the type. -/
structure ThreeByThreeDiagram
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y')
    (comm : f ≫ b = a ≫ f') where
  X'' : C
  Y'' : C
  Z : C
  Z' : C
  Z'' : C
  g : Y ⟶ Z
  h : Z ⟶ X⟦(1 : ℤ)⟧
  g' : Y' ⟶ Z'
  h' : Z' ⟶ X'⟦(1 : ℤ)⟧
  f'' : X'' ⟶ Y''
  g'' : Y'' ⟶ Z''
  h'' : Z'' ⟶ X''⟦(1 : ℤ)⟧
  a' : X' ⟶ X''
  a'' : X'' ⟶ X⟦(1 : ℤ)⟧
  b' : Y' ⟶ Y''
  b'' : Y'' ⟶ Y⟦(1 : ℤ)⟧
  c : Z ⟶ Z'
  c' : Z' ⟶ Z''
  c'' : Z'' ⟶ Z⟦(1 : ℤ)⟧
  row₀ : Triangle.mk f g h ∈ distTriang C
  row₁ : Triangle.mk f' g' h' ∈ distTriang C
  row₂ : Triangle.mk f'' g'' h'' ∈ distTriang C
  row₃ : Triangle.mk (f⟦(1 : ℤ)⟧') (g⟦(1 : ℤ)⟧')
      (h⟦(1 : ℤ)⟧') ∈ distTriang C
  col₀ : Triangle.mk a a' a'' ∈ distTriang C
  col₁ : Triangle.mk b b' b'' ∈ distTriang C
  col₂ : Triangle.mk c c' c'' ∈ distTriang C
  col₃ : Triangle.mk (a⟦(1 : ℤ)⟧') (a'⟦(1 : ℤ)⟧')
      (a''⟦(1 : ℤ)⟧') ∈ distTriang C
  comm₀₁ : g ≫ c = b ≫ g'
  comm₀₂ : h ≫ a⟦(1 : ℤ)⟧' = c ≫ h'
  comm₁₀ : f' ≫ b' = a' ≫ f''
  comm₁₁ : g' ≫ c' = b' ≫ g''
  comm₁₂ : h' ≫ a'⟦(1 : ℤ)⟧' = c' ≫ h''
  comm₂₀ : f'' ≫ b'' = a'' ≫ f⟦(1 : ℤ)⟧'
  comm₂₁ : g'' ≫ c'' = b'' ≫ g⟦(1 : ℤ)⟧'
  anti₂₂ : h'' ≫ a''⟦(1 : ℤ)⟧' = -(c'' ≫ h⟦(1 : ℤ)⟧')

/-- TR4 completes every commutative square to the source's 3 by 3 diagram. -/
theorem three_by_three_completion
    [CategoryTheory.IsTriangulated C]
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') :
    Nonempty (ThreeByThreeDiagram f f' a b comm) := by
  sorry

end ThreeByThree

end Formalization.Books.Derived.Unit04
