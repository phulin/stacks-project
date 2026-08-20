import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Homology.ShortComplex.Ab
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
  [HasShift C ℤ]
  [hAdditive : ∀ n : ℤ, (shiftFunctor C n).Additive]
  [hPretriangulated : Pretriangulated C]

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
    {E : Type*} [Category* E] [Preadditive E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    (W : E) (T : Triangle E) : Prop :=
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
    {E : Type*} [Category* E] [Preadditive E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    (T : Triangle E) : Prop :=
  ∀ W : E, RepresentableLongExact W T

/-- The dual co-special condition, transported through the canonical opposite
triangle equivalence. -/
def CoSpecialTriangle
    {E : Type*} [Category* E] [Preadditive E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    (T : Triangle E) : Prop :=
  SpecialTriangle ((triangleOpEquivalence E).functor.obj (Opposite.op T))

omit [Pretriangulated C] in
/-- Specialness is invariant under a triangle morphism when any two component
maps are isomorphisms. -/
lemma special_triangle_two_out_of_three
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

omit [Pretriangulated C] in
/-- The middle component of a special-triangle morphism is an isomorphism when
the first and third components are. -/
lemma special_triangle_isIso₂
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

omit [Pretriangulated C] in
/-- The first component of a special-triangle morphism is an isomorphism when
the second and third components are. -/
lemma special_triangle_isIso₁
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

set_option maxHeartbeats 1000000 in
/-- The dual two-out-of-three statement for co-special triangles. -/
theorem coSpecial_triangle_two_out_of_three
    {T T' : Triangle C} (hT : CoSpecialTriangle T)
    (hT' : CoSpecialTriangle T') (φ : T ⟶ T')
    (h₁ : IsIso φ.hom₁) (h₂ : IsIso φ.hom₂) : IsIso φ.hom₃ := by
  let : AdditiveCategory Cᵒᵖ :=
    { toPreadditive := inferInstance
      toHasFiniteProducts := inferInstance }
  let : Pretriangulated Cᵒᵖ := inferInstance
  let Top : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T)
  let Topp : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T')
  let phop : Topp ⟶ Top :=
    (triangleOpEquivalence C).functor.map (Opposite.op φ)
  have h2op : IsIso phop.hom₂ := by
    change IsIso (φ.hom₂.op : Topp.obj₂ ⟶ Top.obj₂)
    exact (isIso_op_iff φ.hom₂).2 h₂
  have h3op : IsIso phop.hom₃ := by
    change IsIso (φ.hom₁.op : Topp.obj₃ ⟶ Top.obj₃)
    exact (isIso_op_iff φ.hom₁).2 h₁
  have hTopp : SpecialTriangle Topp := hT'
  have hTop : SpecialTriangle Top := hT
  have h1op : IsIso phop.hom₁ :=
    special_triangle_isIso₁ (C := Cᵒᵖ) (T := Topp) (T' := Top)
      hTopp hTop phop h2op h3op
  have h1op' : IsIso (φ.hom₃.op : Topp.obj₁ ⟶ Top.obj₁) := by
    change IsIso (φ.hom₃.op : Topp.obj₁ ⟶ Top.obj₁) at h1op
    exact h1op
  let _ : IsIso φ.hom₃.op := h1op'
  exact isIso_of_op φ.hom₃
/-
  let Top : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T)
  let Topp : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T')
  let phop : Topp ⟶ Top :=
    { hom₁ := φ.hom₃.op
      hom₂ := φ.hom₂.op
      hom₃ := φ.hom₁.op
      comm₁ := Quiver.Hom.unop_inj φ.comm₂.symm
      comm₂ := Quiver.Hom.unop_inj φ.comm₁.symm
      comm₃ := by
        dsimp [Top, Topp, triangleOpEquivalence, TriangleOpEquivalence.functor]
        rw [Category.assoc, ← Functor.map_comp, ← op_comp, ← φ.comm₃, op_comp,
          Functor.map_comp, opShiftFunctorEquivalence_counitIso_inv_naturality_assoc]
        dsimp
        rfl }
  have h2op : IsIso phop.hom₂ := by
    change IsIso (φ.hom₂.op : Topp.obj₂ ⟶ Top.obj₂)
    exact (isIso_op_iff φ.hom₂).2 h₂
  have h3op : IsIso phop.hom₃ := by
    change IsIso (φ.hom₁.op : Topp.obj₃ ⟶ Top.obj₃)
    exact (isIso_op_iff φ.hom₁).2 h₁
  have hTopp : SpecialTriangle Topp := hT'
  have hTop : SpecialTriangle Top := hT
  refine (isIso_op_iff φ.hom₃).1 ?_
  exact special_triangle_isIso₁_apply hTopp hTop phop h2op h3op
-/
/- Prior attempt:
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
-/

set_option maxHeartbeats 1000000 in
/-- The middle component of a co-special-triangle morphism is an isomorphism
when the first and third components are. -/
theorem coSpecial_triangle_isIso₂
    {T T' : Triangle C} (hT : CoSpecialTriangle T)
    (hT' : CoSpecialTriangle T') (φ : T ⟶ T')
    (h₁ : IsIso φ.hom₁) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₂ := by
  let : AdditiveCategory Cᵒᵖ :=
    { toPreadditive := inferInstance
      toHasFiniteProducts := inferInstance }
  let : Pretriangulated Cᵒᵖ := inferInstance
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
  refine (isIso_op_iff φ.hom₂).1 ?_
  exact special_triangle_isIso₂ (C := Cᵒᵖ) (T := Topp) (T' := Top)
    hTopp hTop phop h3op h1op
/- Prior attempt:
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
-/

set_option maxHeartbeats 1000000 in
/-- The first component of a co-special-triangle morphism is an isomorphism
when the second and third components are. -/
theorem coSpecial_triangle_isIso₁
    {T T' : Triangle C} (hT : CoSpecialTriangle T)
    (hT' : CoSpecialTriangle T') (φ : T ⟶ T')
    (h₂ : IsIso φ.hom₂) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₁ := by
  let : AdditiveCategory Cᵒᵖ :=
    { toPreadditive := inferInstance
      toHasFiniteProducts := inferInstance }
  let : Pretriangulated Cᵒᵖ := inferInstance
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
  refine (isIso_op_iff φ.hom₁).1 ?_
  exact special_triangle_two_out_of_three (C := Cᵒᵖ) (T := Topp) (T' := Top)
    hTopp hTop phop h3op h2op
/- Prior attempt:
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
-/
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

set_option maxHeartbeats 1000000 in
/-- Every distinguished triangle is co-special. -/
theorem distinguished_triangle_coSpecial
    (T : Triangle C) (hT : T ∈ distTriang C) : CoSpecialTriangle T := by
  let : AdditiveCategory Cᵒᵖ :=
    { toPreadditive := inferInstance
      toHasFiniteProducts := inferInstance }
  let : Pretriangulated Cᵒᵖ := inferInstance
  let Top : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T)
  change SpecialTriangle Top
  have hTop : Top ∈ distTriang Cᵒᵖ := op_distinguished T hT
  exact distinguished_triangle_special (C := Cᵒᵖ) Top hTop
/- Prior attempt:
  let Top : Triangle Cᵒᵖ :=
    (triangleOpEquivalence C).functor.obj (Opposite.op T)
  change SpecialTriangle Top
  have hTop : Top ∈ distTriang Cᵒᵖ := op_distinguished T hT
  exact distinguished_triangle_special (C := Cᵒᵖ) Top hTop
-/

/-! ## Square-zero, idempotents, and cones -/

/-- The middle component of the composite of two endomorphisms with zero first
and third components is zero. -/
theorem triangle_middle_composite_zero
    {T : Triangle C} (hT : T ∈ distTriang C)
    (φ ψ : T ⟶ T)
    (_ : φ.hom₁ = 0) (hφ₃ : φ.hom₃ = 0)
    (hψ₁ : ψ.hom₁ = 0) (_ : ψ.hom₃ = 0) :
    φ.hom₂ ≫ ψ.hom₂ = 0 := by
  have hψ : T.mor₁ ≫ ψ.hom₂ = 0 := by
    rw [ψ.comm₁, hψ₁, zero_comp]
  obtain ⟨α, hα⟩ := T.yoneda_exact₂ hT ψ.hom₂ hψ
  have hφ : φ.hom₂ ≫ T.mor₂ = 0 := by
    rw [← φ.comm₂, hφ₃, comp_zero]
  obtain ⟨β, hβ⟩ := T.coyoneda_exact₂ hT φ.hom₂ hφ
  calc
    φ.hom₂ ≫ ψ.hom₂ = (β ≫ T.mor₁) ≫ (T.mor₂ ≫ α) := by rw [hβ, hα]
    _ = β ≫ (T.mor₁ ≫ T.mor₂) ≫ α := by simp only [Category.assoc]
    _ = 0 := by rw [comp_distTriang_mor_zero₁₂ _ hT, zero_comp, comp_zero]

/-- An idempotent pair on the ends of a distinguished triangle extends to an
idempotent endomorphism of the triangle. -/
theorem exists_idempotent_triangle_endomorphism
    {T : Triangle C} (hT : T ∈ distTriang C)
    (a : T.obj₁ ⟶ T.obj₁) (c : T.obj₃ ⟶ T.obj₃)
    (ha : a ≫ a = a) (hc : c ≫ c = c)
    (hcomm : T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T.mor₃) :
    ∃ (b : T.obj₂ ⟶ T.obj₂), b ≫ b = b ∧
      ∃ φ : T ⟶ T, φ.hom₁ = a ∧ φ.hom₂ = b ∧ φ.hom₃ = c := by
  obtain ⟨b', hb'₁, hb'₂⟩ :=
    complete_distinguished_triangle_morphism₂ T T hT hT a c hcomm
  let d : T.obj₂ ⟶ T.obj₂ := b' ≫ b' - b'
  have hd₁ : T.mor₁ ≫ d = 0 := by
    dsimp [d]
    rw [comp_sub, ← Category.assoc, hb'₁, Category.assoc, hb'₁, ← Category.assoc, ha,
      sub_self]
  have hd₂ : d ≫ T.mor₂ = 0 := by
    dsimp [d]
    rw [sub_comp, Category.assoc, ← hb'₂, ← Category.assoc, ← hb'₂, Category.assoc, hc,
      sub_self]
  let δ : T ⟶ T := Triangle.homMk T T 0 d 0
    (by simpa using hd₁) (by simpa using hd₂.symm) (by simp)
  have hdd : d ≫ d = 0 := by
    have h := triangle_middle_composite_zero hT δ δ (by rfl) (by rfl) (by rfl) (by rfl)
    exact h
  have hxd : b' ≫ d = d ≫ b' := by
    simp only [d, comp_sub, sub_comp, Category.assoc]
  let q : T.obj₂ ⟶ T.obj₂ := b' + b' - 𝟙 _
  have hqd : q ≫ d = d ≫ q := by
    dsimp [q]
    simp only [comp_sub, sub_comp, add_comp, comp_add, Category.id_comp, Category.comp_id,
      hxd]
  have hqqd : (q ≫ d) ≫ (q ≫ d) = 0 := by
    calc
      (q ≫ d) ≫ (q ≫ d) = q ≫ ((d ≫ q) ≫ d) := by simp only [Category.assoc]
      _ = q ≫ ((q ≫ d) ≫ d) := by rw [← hqd]
      _ = 0 := by simp only [Category.assoc, hdd, comp_zero]
  have hbase : b' ≫ b' = b' + d := by
    dsimp [d]
    abel
  have hbq : b' ≫ q = q ≫ b' := by
    dsimp [q]
    simp only [comp_sub, sub_comp, add_comp, comp_add, Category.id_comp, Category.comp_id]
  have hbq' : b' ≫ q = b' + d + d := by
    dsimp [q]
    simp only [comp_sub, comp_add, Category.comp_id]
    rw [hbase]
    abel
  have hxkd : b' ≫ (q ≫ d) = b' ≫ d := by
    calc
      b' ≫ (q ≫ d) = (b' ≫ q) ≫ d := by simp only [Category.assoc]
      _ = (b' + d + d) ≫ d := by rw [hbq']
      _ = b' ≫ d := by
        simp only [add_comp, hdd, add_zero]
  have hqdb : (q ≫ d) ≫ b' = b' ≫ d := by
    calc
      (q ≫ d) ≫ b' = q ≫ (d ≫ b') := by simp only [Category.assoc]
      _ = q ≫ (b' ≫ d) := by rw [hxd]
      _ = (q ≫ b') ≫ d := by simp only [Category.assoc]
      _ = (b' ≫ q) ≫ d := by rw [← hbq]
      _ = b' ≫ (q ≫ d) := by simp only [Category.assoc]
      _ = b' ≫ d := hxkd
  let k : T.obj₂ ⟶ T.obj₂ := q ≫ d
  have hkk : k ≫ k = 0 := by
    change (q ≫ d) ≫ (q ≫ d) = 0
    exact hqqd
  have hrel : d - b' ≫ k - k ≫ b' + k = 0 := by
    rw [show b' ≫ k = b' ≫ (q ≫ d) by rfl, hxkd,
      show k ≫ b' = (q ≫ d) ≫ b' by rfl, hqdb]
    change d - b' ≫ d - b' ≫ d + q ≫ d = 0
    dsimp [q]
    simp only [sub_comp, add_comp, Category.id_comp]
    abel
  let b : T.obj₂ ⟶ T.obj₂ := b' - k
  have hb : b ≫ b = b := by
    calc
      b ≫ b = b' + d - b' ≫ k - k ≫ b' + k ≫ k := by
        dsimp [b]
        simp only [sub_comp, comp_sub]
        rw [hbase]
        abel
      _ = b' + d - b' ≫ k - k ≫ b' := by
        rw [hkk]
        simp only [add_zero]
      _ = b' - k := by
        calc
          b' + d - b' ≫ k - k ≫ b' =
              b' + (d - b' ≫ k - k ≫ b' + k) - k := by abel
          _ = b' + 0 - k := by rw [hrel]
          _ = b' - k := by simp
      _ = b := by rfl
  have hk₁ : T.mor₁ ≫ k = 0 := by
    change T.mor₁ ≫ (q ≫ d) = 0
    have hq₁ : T.mor₁ ≫ q = (a + a - 𝟙 _) ≫ T.mor₁ := by
      dsimp [q]
      simp only [comp_sub, sub_comp, add_comp, comp_add, Category.id_comp, Category.comp_id,
        hb'₁]
    rw [← Category.assoc, hq₁, Category.assoc, hd₁]
    simp only [comp_zero]
  have hk₂ : k ≫ T.mor₂ = 0 := by
    change (q ≫ d) ≫ T.mor₂ = 0
    rw [Category.assoc, hd₂, comp_zero]
  have hb₁ : T.mor₁ ≫ b = a ≫ T.mor₁ := by
    dsimp [b]
    rw [comp_sub, hb'₁, hk₁, sub_zero]
  have hb₂ : T.mor₂ ≫ c = b ≫ T.mor₂ := by
    dsimp [b]
    rw [sub_comp, hk₂, sub_zero]
    exact hb'₂
  let φ : T ⟶ T := Triangle.homMk T T a b c hb₁ hb₂ hcomm
  refine ⟨b, hb, φ, rfl, rfl, rfl⟩

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
  let e := Pretriangulated.isoTriangleOfIso₁₂
    (Triangle.mk f g h) (Triangle.mk f g' h') hT hT' (Iso.refl X) (Iso.refl Y)
    (by
      change f ≫ 𝟙 Y = 𝟙 X ≫ f
      simp)
  refine ⟨e, ?_, ?_⟩
  · change (Iso.refl X).hom = 𝟙 X
    rfl
  · change (Iso.refl Y).hom = 𝟙 Y
    rfl

/- The source's five vanishing conditions are a useful reusable interface for
   its uniqueness-of-the-third-arrow lemma. -/

/-- All morphisms between two specified objects vanish. -/
def HomIsZero (X Y : C) : Prop :=
  ∀ f : X ⟶ Y, f = 0

/-- Under any one of the five source vanishing hypotheses, the middle map of a
triangle morphism is determined by its first and third maps. -/
theorem triangle_middle_map_unique
    {T T' : Triangle C} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (φ ψ : T ⟶ T')
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
  constructor
  · constructor
    · intro hf
      exact (Triangle.distinguished_iff_of_isZero₃ _
        (isZero_zero C)).2 hf
    · intro hT
      exact (Triangle.distinguished_iff_of_isZero₃ _
        (isZero_zero C)).1 hT
  · constructor
    · intro hf Z g h hT
      exact (Triangle.isZero₃_iff_isIso₁ _ hT).2 hf
    · intro hP
      obtain ⟨Z, g, h, hT⟩ := distinguished_cone_exists f
      exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hP g h hT)

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

private lemma exact_of_retract_addCommGrp
    {S S' : ShortComplex AddCommGrpCat} (φ : S ⟶ S') (ψ : S' ⟶ S)
    (hφψ : φ ≫ ψ = 𝟙 S) (hS' : S'.Exact) : S.Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  have hx' : S'.g (φ.τ₂ x) = 0 := by
    have h := congrArg (fun k => k x) φ.comm₂₃
    simpa [ConcreteCategory.comp_apply, hx] using h
  obtain ⟨x', hx'⟩ := (ShortComplex.ab_exact_iff S').1 hS' (φ.τ₂ x) hx'
  refine ⟨ψ.τ₁ x', ?_⟩
  have h₁ := congrArg (fun k => k x') ψ.comm₁₂
  have h₁' : S.f (ψ.τ₁ x') = ψ.τ₂ (S'.f x') := by
    simpa [ConcreteCategory.comp_apply] using h₁
  rw [hx'] at h₁'
  have h₂ := congrArg (fun k => k x) (congrArg (fun k => k.τ₂) hφψ)
  have h₂' : ψ.τ₂ (φ.τ₂ x) = x := by
    simpa [ConcreteCategory.comp_apply] using h₂
  exact h₁'.trans h₂'

private lemma isComplex_of_retract_addCommGrp
    {n : ℕ} {S S' : ComposableArrows AddCommGrpCat n}
    (φ : S ⟶ S') (ψ : S' ⟶ S) (hφψ : φ ≫ ψ = 𝟙 S)
    (hS' : S'.IsComplex) : S.IsComplex := by
  refine ⟨?_⟩
  intro i hi
  let i₀ : Fin (n + 1) := ⟨i, by omega⟩
  let i₁ : Fin (n + 1) := ⟨i + 1, by omega⟩
  let i₂ : Fin (n + 1) := ⟨i + 2, by omega⟩
  have hcomp :
      φ.app i₂ ≫ ψ.app i₂ = 𝟙 _ := by
    have h := congrArg (fun k => k.app i₂) hφψ
    change φ.app i₂ ≫ ψ.app i₂ = 𝟙 _ at h
    exact h
  calc
    S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) =
        S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) ≫
          φ.app i₂ ≫ ψ.app i₂ := by
      calc
        S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) =
            S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) ≫ 𝟙 _ := by simp
        _ = S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) ≫
              (φ.app i₂ ≫ ψ.app i₂) := by rw [hcomp]
    _ = S.map' i (i + 1) ≫ φ.app i₁ ≫
          S'.map' (i + 1) (i + 2) ≫ ψ.app i₂ := by
      rw [reassoc_of% (ComposableArrows.naturality' φ (i + 1) (i + 2))]
    _ = φ.app i₀ ≫ S'.map' i (i + 1) ≫
          S'.map' (i + 1) (i + 2) ≫ ψ.app i₂ := by
      rw [reassoc_of% (ComposableArrows.naturality' φ i (i + 1))]
    _ = 0 := by rw [reassoc_of% (hS'.zero i hi), zero_comp]; simp

private lemma exact_of_retract_composableArrows
    {n : ℕ} {S S' : ComposableArrows AddCommGrpCat n}
    (φ : S ⟶ S') (ψ : S' ⟶ S) (hφψ : φ ≫ ψ = 𝟙 S)
    (hS' : S'.Exact) : S.Exact := by
  let hS := isComplex_of_retract_addCommGrp φ ψ hφψ hS'.toIsComplex
  refine { toIsComplex := hS, exact := ?_ }
  intro i hi
  let i₀ : Fin (n + 1) := ⟨i, by omega⟩
  let i₁ : Fin (n + 1) := ⟨i + 1, by omega⟩
  let i₂ : Fin (n + 1) := ⟨i + 2, by omega⟩
  let a := ComposableArrows.scMap φ hS hS'.toIsComplex i
  let b := ComposableArrows.scMap ψ hS'.toIsComplex hS i
  have hab : a ≫ b = 𝟙 _ := by
    apply ShortComplex.hom_ext
    · have h := congrArg (fun k => k.app i₀) hφψ
      change φ.app i₀ ≫ ψ.app i₀ = 𝟙 _ at h
      simpa [a, b] using h
    · have h := congrArg (fun k => k.app i₁) hφψ
      change φ.app i₁ ≫ ψ.app i₁ = 𝟙 _ at h
      simpa [a, b] using h
    · have h := congrArg (fun k => k.app i₂) hφψ
      change φ.app i₂ ≫ ψ.app i₂ = 𝟙 _ at h
      simpa [a, b] using h
  exact exact_of_retract_addCommGrp a b hab (hS'.exact i hi)

omit [Pretriangulated C] in
private lemma special_of_retract
    {T T' : Triangle C} (hT' : SpecialTriangle T')
    (φ : T ⟶ T') (ψ : T' ⟶ T) (hφψ : φ ≫ ψ = 𝟙 T) :
    SpecialTriangle T := by
  dsimp [SpecialTriangle, RepresentableLongExact] at hT' ⊢
  intro W n
  let F := preadditiveCoyoneda.obj (Opposite.op W)
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
        simpa only [Functor.map_comp] using congrArg ((F.shift n).map) φ.comm₁
      · change (F.shift n).map T.mor₂ ≫ (F.shift n).map φ.hom₃ =
          (F.shift n).map φ.hom₂ ≫ (F.shift n).map T'.mor₂
        simpa only [Functor.map_comp] using congrArg ((F.shift n).map) φ.comm₂
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
  let β : R' ⟶ R := ComposableArrows.homMk
    (fun i => match i with
      | ⟨0, _⟩ => (F.shift n).map ψ.hom₁
      | ⟨1, _⟩ => (F.shift n).map ψ.hom₂
      | ⟨2, _⟩ => (F.shift n).map ψ.hom₃
      | ⟨3, _⟩ => (F.shift (n + 1)).map ψ.hom₁
      | ⟨4, _⟩ => (F.shift (n + 1)).map ψ.hom₂)
    (by
      intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi' with rfl | rfl | rfl | rfl
      · change (F.shift n).map T'.mor₁ ≫ (F.shift n).map ψ.hom₂ =
          (F.shift n).map ψ.hom₁ ≫ (F.shift n).map T.mor₁
        simpa only [Functor.map_comp] using congrArg ((F.shift n).map) ψ.comm₁
      · change (F.shift n).map T'.mor₂ ≫ (F.shift n).map ψ.hom₃ =
          (F.shift n).map ψ.hom₂ ≫ (F.shift n).map T.mor₂
        simpa only [Functor.map_comp] using congrArg ((F.shift n).map) ψ.comm₂
      · change F.homologySequenceδ T' n (n + 1) (by rfl) ≫
          (F.shift (n + 1)).map ψ.hom₁ =
          (F.shift n).map ψ.hom₃ ≫
            F.homologySequenceδ T n (n + 1) (by rfl)
        simpa only using
          (F.homologySequenceδ_naturality T' T ψ n (n + 1) (by rfl)).symm
      · change (F.shift (n + 1)).map T'.mor₁ ≫
            (F.shift (n + 1)).map ψ.hom₂ =
          (F.shift (n + 1)).map ψ.hom₁ ≫
            (F.shift (n + 1)).map T.mor₁
        simpa only [Functor.map_comp] using
          congrArg ((F.shift (n + 1)).map) ψ.comm₁)
  have hφψ₁ : φ.hom₁ ≫ ψ.hom₁ = 𝟙 _ := by
    have h := congrArg (fun k => k.hom₁) hφψ
    change φ.hom₁ ≫ ψ.hom₁ = 𝟙 _ at h
    exact h
  have hφψ₂ : φ.hom₂ ≫ ψ.hom₂ = 𝟙 _ := by
    have h := congrArg (fun k => k.hom₂) hφψ
    change φ.hom₂ ≫ ψ.hom₂ = 𝟙 _ at h
    exact h
  have hφψ₃ : φ.hom₃ ≫ ψ.hom₃ = 𝟙 _ := by
    have h := congrArg (fun k => k.hom₃) hφψ
    change φ.hom₃ ≫ ψ.hom₃ = 𝟙 _ at h
    exact h
  have hαβ : α ≫ β = 𝟙 R := by
    apply ComposableArrows.hom_ext₄
    · change (F.shift n).map φ.hom₁ ≫ (F.shift n).map ψ.hom₁ = 𝟙 _
      rw [← Functor.map_comp, hφψ₁]
      simp
    · change (F.shift n).map φ.hom₂ ≫ (F.shift n).map ψ.hom₂ = 𝟙 _
      rw [← Functor.map_comp, hφψ₂]
      simp
    · change (F.shift n).map φ.hom₃ ≫ (F.shift n).map ψ.hom₃ = 𝟙 _
      rw [← Functor.map_comp, hφψ₃]
      simp
    · change (F.shift (n + 1)).map φ.hom₁ ≫
          (F.shift (n + 1)).map ψ.hom₁ = 𝟙 _
      rw [← Functor.map_comp, hφψ₁]
      simp
    · change (F.shift (n + 1)).map φ.hom₂ ≫
          (F.shift (n + 1)).map ψ.hom₂ = 𝟙 _
      rw [← Functor.map_comp, hφψ₂]
      simp
  have hR : R.Exact := exact_of_retract_composableArrows α β hαβ hR'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (F.shift n).map T.mor₁ ≫ (F.shift n).map T.mor₂ = 0
    have h := hR.toIsComplex.zero 0
    dsimp [R] at h
    exact h
  · change (F.shift n).map T.mor₂ ≫
        F.homologySequenceδ T n (n + 1) (by rfl) = 0
    have h := hR.toIsComplex.zero 1
    dsimp [R] at h
    exact h
  · change F.homologySequenceδ T n (n + 1) (by rfl) ≫
        (F.shift (n + 1)).map T.mor₁ = 0
    have h := hR.toIsComplex.zero 2
    dsimp [R] at h
    exact h
  · have h := hR.exact 0
    change ShortComplex.Exact
      (ShortComplex.mk ((F.shift n).map T.mor₁) ((F.shift n).map T.mor₂) _) at h
    exact h
  · have h := hR.exact 1
    change ShortComplex.Exact
      (ShortComplex.mk ((F.shift n).map T.mor₂)
        (F.homologySequenceδ T n (n + 1) (by rfl)) _) at h
    exact h
  · have h := hR.exact 2
    change ShortComplex.Exact
      (ShortComplex.mk (F.homologySequenceδ T n (n + 1) (by rfl))
        ((F.shift (n + 1)).map T.mor₁) _) at h
    exact h

private lemma shiftBiprodIso_inl
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (X Y : C) :
    biprod.inl ≫ (shiftBiprodIso X Y).inv =
      (shiftFunctor C (1 : ℤ)).map (biprod.inl : X ⟶ X ⊞ Y) := by
  apply (cancel_mono (shiftBiprodIso X Y).hom).1
  dsimp [shiftBiprodIso]
  simp [Functor.biprodComparison, Functor.biprodComparison']

private lemma shiftBiprodIso_inr
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (X Y : C) :
    biprod.inr ≫ (shiftBiprodIso X Y).inv =
      (shiftFunctor C (1 : ℤ)).map (biprod.inr : Y ⟶ X ⊞ Y) := by
  apply (cancel_mono (shiftBiprodIso X Y).hom).1
  dsimp [shiftBiprodIso]
  simp [Functor.biprodComparison, Functor.biprodComparison']

private lemma shiftBiprodIso_fst
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (X Y : C) :
    (shiftBiprodIso X Y).inv ≫
        (shiftFunctor C (1 : ℤ)).map (biprod.fst : X ⊞ Y ⟶ X) =
      (biprod.fst : (shiftFunctor C (1 : ℤ)).obj X ⊞
        (shiftFunctor C (1 : ℤ)).obj Y ⟶ (shiftFunctor C (1 : ℤ)).obj X) := by
  apply biprod.hom_ext'
  · dsimp [shiftBiprodIso]
    rw [← Category.assoc, Functor.inl_biprodComparison', ←
      (shiftFunctor C (1 : ℤ)).map_comp]
    simp
  · dsimp [shiftBiprodIso]
    rw [← Category.assoc, Functor.inr_biprodComparison', ←
      (shiftFunctor C (1 : ℤ)).map_comp]
    simp

private lemma shiftBiprodIso_snd
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (X Y : C) :
    (shiftBiprodIso X Y).inv ≫
        (shiftFunctor C (1 : ℤ)).map (biprod.snd : X ⊞ Y ⟶ Y) =
      (biprod.snd : (shiftFunctor C (1 : ℤ)).obj X ⊞
        (shiftFunctor C (1 : ℤ)).obj Y ⟶ (shiftFunctor C (1 : ℤ)).obj Y) := by
  apply biprod.hom_ext'
  · dsimp [shiftBiprodIso]
    rw [← Category.assoc, Functor.inl_biprodComparison', ←
      (shiftFunctor C (1 : ℤ)).map_comp]
    simp
  · dsimp [shiftBiprodIso]
    rw [← Category.assoc, Functor.inr_biprodComparison', ←
      (shiftFunctor C (1 : ℤ)).map_comp]
    simp

private def directSumInl (T T' : Triangle C) : T ⟶ directSumTriangle T T' := by
  dsimp [directSumTriangle]
  exact Triangle.homMk _ _ biprod.inl biprod.inl biprod.inl
    (by
      change T.mor₁ ≫ (biprod.inl : T.obj₂ ⟶ T.obj₂ ⊞ T'.obj₂) =
        biprod.inl ≫ biprod.map T.mor₁ T'.mor₁
      rw [biprod.inl_map])
    (by
      change T.mor₂ ≫ (biprod.inl : T.obj₃ ⟶ T.obj₃ ⊞ T'.obj₃) =
        biprod.inl ≫ biprod.map T.mor₂ T'.mor₂
      rw [biprod.inl_map])
    (by
      change T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map
          (biprod.inl : T.obj₁ ⟶ T.obj₁ ⊞ T'.obj₁) =
        biprod.inl ≫ (biprod.map T.mor₃ T'.mor₃ ≫
          (shiftBiprodIso T.obj₁ T'.obj₁).inv)
      rw [biprod.inl_map_assoc, shiftBiprodIso_inl])

private def directSumInr (T T' : Triangle C) : T' ⟶ directSumTriangle T T' := by
  dsimp [directSumTriangle]
  exact Triangle.homMk _ _ biprod.inr biprod.inr biprod.inr
    (by
      change T'.mor₁ ≫ (biprod.inr : T'.obj₂ ⟶ T.obj₂ ⊞ T'.obj₂) =
        biprod.inr ≫ biprod.map T.mor₁ T'.mor₁
      rw [biprod.inr_map])
    (by
      change T'.mor₂ ≫ (biprod.inr : T'.obj₃ ⟶ T.obj₃ ⊞ T'.obj₃) =
        biprod.inr ≫ biprod.map T.mor₂ T'.mor₂
      rw [biprod.inr_map])
    (by
      change T'.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map
          (biprod.inr : T'.obj₁ ⟶ T.obj₁ ⊞ T'.obj₁) =
        biprod.inr ≫ (biprod.map T.mor₃ T'.mor₃ ≫
          (shiftBiprodIso T.obj₁ T'.obj₁).inv)
      rw [biprod.inr_map_assoc, shiftBiprodIso_inr])

private def directSumFst (T T' : Triangle C) : directSumTriangle T T' ⟶ T := by
  dsimp [directSumTriangle]
  exact Triangle.homMk _ _ biprod.fst biprod.fst biprod.fst
    (by
      change (biprod.map T.mor₁ T'.mor₁) ≫
          (biprod.fst : T.obj₂ ⊞ T'.obj₂ ⟶ T.obj₂) =
        biprod.fst ≫ T.mor₁
      rw [biprod.map_fst])
    (by
      change (biprod.map T.mor₂ T'.mor₂) ≫
          (biprod.fst : T.obj₃ ⊞ T'.obj₃ ⟶ T.obj₃) =
        biprod.fst ≫ T.mor₂
      rw [biprod.map_fst])
    (by
      change (biprod.map T.mor₃ T'.mor₃ ≫
          (shiftBiprodIso T.obj₁ T'.obj₁).inv) ≫
          (shiftFunctor C (1 : ℤ)).map
            (biprod.fst : T.obj₁ ⊞ T'.obj₁ ⟶ T.obj₁) =
        biprod.fst ≫ T.mor₃
      rw [Category.assoc, shiftBiprodIso_fst, biprod.map_fst])

private def directSumSnd (T T' : Triangle C) : directSumTriangle T T' ⟶ T' := by
  dsimp [directSumTriangle]
  exact Triangle.homMk _ _ biprod.snd biprod.snd biprod.snd
    (by
      change (biprod.map T.mor₁ T'.mor₁) ≫
          (biprod.snd : T.obj₂ ⊞ T'.obj₂ ⟶ T'.obj₂) =
        biprod.snd ≫ T'.mor₁
      rw [biprod.map_snd])
    (by
      change (biprod.map T.mor₂ T'.mor₂) ≫
          (biprod.snd : T.obj₃ ⊞ T'.obj₃ ⟶ T'.obj₃) =
        biprod.snd ≫ T'.mor₂
      rw [biprod.map_snd])
    (by
      change (biprod.map T.mor₃ T'.mor₃ ≫
          (shiftBiprodIso T.obj₁ T'.obj₁).inv) ≫
          (shiftFunctor C (1 : ℤ)).map
            (biprod.snd : T.obj₁ ⊞ T'.obj₁ ⟶ T'.obj₁) =
        biprod.snd ≫ T'.mor₃
      rw [Category.assoc, shiftBiprodIso_snd, biprod.map_snd])

private lemma directSumInl_fst (T T' : Triangle C) :
    directSumInl T T' ≫ directSumFst T T' = 𝟙 T := by
  apply Triangle.hom_ext
  · change biprod.inl ≫ biprod.fst = 𝟙 _
    simp
  · change biprod.inl ≫ biprod.fst = 𝟙 _
    simp
  · change biprod.inl ≫ biprod.fst = 𝟙 _
    simp

private lemma directSumInr_snd (T T' : Triangle C) :
    directSumInr T T' ≫ directSumSnd T T' = 𝟙 T' := by
  apply Triangle.hom_ext
  · change biprod.inr ≫ biprod.snd = 𝟙 _
    simp
  · change biprod.inr ≫ biprod.snd = 𝟙 _
    simp
  · change biprod.inr ≫ biprod.snd = 𝟙 _
    simp

private def productBiprodIso (f : WalkingPair → C) :
    (∏ᶜ f) ≅ f WalkingPair.left ⊞ f WalkingPair.right where
  hom := biprod.lift (Pi.π f WalkingPair.left) (Pi.π f WalkingPair.right)
  inv := Pi.lift (fun j => WalkingPair.casesOn j biprod.fst biprod.snd)
  hom_inv_id := by
    apply Pi.hom_ext
    intro j
    cases j <;> simp
  inv_hom_id := by
    apply biprod.hom_ext
    · simp
    · simp

private def directSumProductTriangleIso (T T' : Triangle C) :
    productTriangle (fun j : WalkingPair => WalkingPair.casesOn j T T') ≅
      directSumTriangle T T' := by
  let e₁ := productBiprodIso
    (fun j => (WalkingPair.casesOn j T T' : Triangle C).obj₁)
  let e₂ := productBiprodIso
    (fun j => (WalkingPair.casesOn j T T' : Triangle C).obj₂)
  let e₃ := productBiprodIso
    (fun j => (WalkingPair.casesOn j T T' : Triangle C).obj₃)
  refine Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_
  · change
      Limits.Pi.map
          (fun j => (WalkingPair.casesOn j T T' : Triangle C).mor₁) ≫ e₂.hom =
        e₁.hom ≫ biprod.map T.mor₁ T'.mor₁
    apply biprod.hom_ext
    · simp only [e₁, e₂, productBiprodIso]
      rw [Category.assoc, biprod.lift_fst, Pi.map_π]
      simp [Category.assoc]
    · simp only [e₁, e₂, productBiprodIso]
      rw [Category.assoc, biprod.lift_snd, Pi.map_π]
      simp [Category.assoc]
  · change
      Limits.Pi.map
          (fun j => (WalkingPair.casesOn j T T' : Triangle C).mor₂) ≫ e₃.hom =
        e₂.hom ≫ biprod.map T.mor₂ T'.mor₂
    apply biprod.hom_ext
    · simp only [e₂, e₃, productBiprodIso]
      rw [Category.assoc, biprod.lift_fst, Pi.map_π]
      simp [Category.assoc]
    · simp only [e₂, e₃, productBiprodIso]
      rw [Category.assoc, biprod.lift_snd, Pi.map_π]
      simp [Category.assoc]
  · change
      (Limits.Pi.map
          (fun j => (WalkingPair.casesOn j T T' : Triangle C).mor₃) ≫
          inv (piComparison (shiftFunctor C (1 : ℤ))
            (fun j => (WalkingPair.casesOn j T T' : Triangle C).obj₁))) ≫
          (shiftFunctor C (1 : ℤ)).map e₁.hom =
        e₃.hom ≫ biprod.map T.mor₃ T'.mor₃ ≫
          (shiftBiprodIso T.obj₁ T'.obj₁).inv
    let e₁s := productBiprodIso
      (fun j => (shiftFunctor C (1 : ℤ)).obj
        ((WalkingPair.casesOn j T T' : Triangle C).obj₁))
    have hcomp :
        (shiftFunctor C (1 : ℤ)).map e₁.hom ≫
            (shiftBiprodIso T.obj₁ T'.obj₁).hom =
          piComparison (shiftFunctor C (1 : ℤ))
              (fun j => (WalkingPair.casesOn j T T' : Triangle C).obj₁) ≫
            e₁s.hom := by
      apply biprod.hom_ext
      · simp only [e₁, productBiprodIso]
        dsimp [shiftBiprodIso]
        rw [Category.assoc, Functor.biprodComparison_fst, ← Functor.map_comp,
          biprod.lift_fst]
        simp [e₁s, productBiprodIso]
      · simp only [e₁, productBiprodIso]
        dsimp [shiftBiprodIso]
        rw [Category.assoc, Functor.biprodComparison_snd, ← Functor.map_comp,
          biprod.lift_snd]
        simp [e₁s, productBiprodIso]
    have hmap :
        Limits.Pi.map
              (fun j => (WalkingPair.casesOn j T T' : Triangle C).mor₃) ≫
            e₁s.hom =
          e₃.hom ≫ biprod.map T.mor₃ T'.mor₃ := by
      apply biprod.hom_ext
      · simp [e₁s, e₃, productBiprodIso, Category.assoc]
      · simp [e₁s, e₃, productBiprodIso, Category.assoc]
    apply (cancel_mono (shiftBiprodIso T.obj₁ T'.obj₁).hom).1
    calc
      ((Limits.Pi.map
          (fun j => (WalkingPair.casesOn j T T' : Triangle C).mor₃) ≫
          inv (piComparison (shiftFunctor C (1 : ℤ))
            (fun j => (WalkingPair.casesOn j T T' : Triangle C).obj₁))) ≫
          (shiftFunctor C (1 : ℤ)).map e₁.hom) ≫
          (shiftBiprodIso T.obj₁ T'.obj₁).hom =
        Limits.Pi.map
              (fun j => (WalkingPair.casesOn j T T' : Triangle C).mor₃) ≫
            inv (piComparison (shiftFunctor C (1 : ℤ))
              (fun j => (WalkingPair.casesOn j T T' : Triangle C).obj₁)) ≫
            (shiftFunctor C (1 : ℤ)).map e₁.hom ≫
              (shiftBiprodIso T.obj₁ T'.obj₁).hom := by
          simp only [Category.assoc]
      _ = Limits.Pi.map
              (fun j => (WalkingPair.casesOn j T T' : Triangle C).mor₃) ≫
            inv (piComparison (shiftFunctor C (1 : ℤ))
              (fun j => (WalkingPair.casesOn j T T' : Triangle C).obj₁)) ≫
            piComparison (shiftFunctor C (1 : ℤ))
              (fun j => (WalkingPair.casesOn j T T' : Triangle C).obj₁) ≫
            e₁s.hom := by rw [hcomp]
      _ = Limits.Pi.map
              (fun j => (WalkingPair.casesOn j T T' : Triangle C).mor₃) ≫
            e₁s.hom := by simp
      _ = e₃.hom ≫ biprod.map T.mor₃ T'.mor₃ := hmap
      _ = (e₃.hom ≫ biprod.map T.mor₃ T'.mor₃ ≫
          (shiftBiprodIso T.obj₁ T'.obj₁).inv) ≫
          (shiftBiprodIso T.obj₁ T'.obj₁).hom := by simp

/-- A direct sum triangle is distinguished exactly when both summands are. -/
theorem direct_sum_triangle_distinguished_iff
    (T T' : Triangle C) :
    directSumTriangle T T' ∈ distTriang C ↔
      T ∈ distTriang C ∧ T' ∈ distTriang C := by
  constructor
  · intro hDS
    have hDSpecial := distinguished_triangle_special (directSumTriangle T T') hDS
    have hTspecial : SpecialTriangle T :=
      special_of_retract hDSpecial (directSumInl T T') (directSumFst T T')
        (directSumInl_fst T T')
    have hT'special : SpecialTriangle T' :=
      special_of_retract hDSpecial (directSumInr T T') (directSumSnd T T')
        (directSumInr_snd T T')
    obtain ⟨Q, g, h, hQ⟩ := distinguished_cocone_triangle T.mor₁
    let U : Triangle C := Triangle.mk T.mor₁ g h
    have hU : U ∈ distTriang C := hQ
    let φ : directSumTriangle T T' ⟶ U :=
      completeDistinguishedTriangleMorphism _ _ hDS hU biprod.fst biprod.fst (by
        change (biprod.map T.mor₁ T'.mor₁) ≫
            (biprod.fst : T.obj₂ ⊞ T'.obj₂ ⟶ T.obj₂) =
          (biprod.fst : T.obj₁ ⊞ T'.obj₁ ⟶ T.obj₁) ≫ T.mor₁
        rw [biprod.map_fst])
    let μ : T ⟶ U := directSumInl T T' ≫ φ
    have hμ₁ : μ.hom₁ = 𝟙 _ := by
      change biprod.inl ≫ biprod.fst = 𝟙 _
      simp
    have hμ₂ : μ.hom₂ = 𝟙 _ := by
      change biprod.inl ≫ biprod.fst = 𝟙 _
      simp
    dsimp [U] at hμ₁ hμ₂
    have hμ₃ : IsIso μ.hom₃ :=
      special_triangle_two_out_of_three hTspecial
        (distinguished_triangle_special U hU) μ
        (by
          change IsIso (biprod.inl ≫
            (biprod.fst : T.obj₁ ⊞ T'.obj₁ ⟶ T.obj₁))
          simp only [biprod.inl_fst]
          exact ⟨⟨𝟙 _, by simp⟩⟩)
        (by
          change IsIso (biprod.inl ≫
            (biprod.fst : T.obj₂ ⊞ T'.obj₂ ⟶ T.obj₂))
          simp only [biprod.inl_fst]
          exact ⟨⟨𝟙 _, by simp⟩⟩)
    have hμ : IsIso μ := by
      apply Triangle.isIso_of_isIsos μ
      · change IsIso (biprod.inl ≫
          (biprod.fst : T.obj₁ ⊞ T'.obj₁ ⟶ T.obj₁))
        simp only [biprod.inl_fst]
        exact ⟨⟨𝟙 _, by simp⟩⟩
      · change IsIso (biprod.inl ≫
          (biprod.fst : T.obj₂ ⊞ T'.obj₂ ⟶ T.obj₂))
        simp only [biprod.inl_fst]
        exact ⟨⟨𝟙 _, by simp⟩⟩
      · exact hμ₃
    have hT : T ∈ distTriang C :=
      isomorphic_distinguished _ hU _ (asIso μ)
    obtain ⟨Q', g', h', hQ'⟩ := distinguished_cocone_triangle T'.mor₁
    let U' : Triangle C := Triangle.mk T'.mor₁ g' h'
    have hU' : U' ∈ distTriang C := hQ'
    let φ' : directSumTriangle T T' ⟶ U' :=
      completeDistinguishedTriangleMorphism _ _ hDS hU' biprod.snd biprod.snd (by
        change (biprod.map T.mor₁ T'.mor₁) ≫
            (biprod.snd : T.obj₂ ⊞ T'.obj₂ ⟶ T'.obj₂) =
          (biprod.snd : T.obj₁ ⊞ T'.obj₁ ⟶ T'.obj₁) ≫ T'.mor₁
        rw [biprod.map_snd])
    let μ' : T' ⟶ U' := directSumInr T T' ≫ φ'
    have hμ'₁ : μ'.hom₁ = 𝟙 _ := by
      change biprod.inr ≫ biprod.snd = 𝟙 _
      simp
    have hμ'₂ : μ'.hom₂ = 𝟙 _ := by
      change biprod.inr ≫ biprod.snd = 𝟙 _
      simp
    dsimp [U'] at hμ'₁ hμ'₂
    have hμ'₃ : IsIso μ'.hom₃ :=
      special_triangle_two_out_of_three hT'special
        (distinguished_triangle_special U' hU') μ'
        (by
          change IsIso (biprod.inr ≫
            (biprod.snd : T.obj₁ ⊞ T'.obj₁ ⟶ T'.obj₁))
          simp only [biprod.inr_snd]
          exact ⟨⟨𝟙 _, by simp⟩⟩)
        (by
          change IsIso (biprod.inr ≫
            (biprod.snd : T.obj₂ ⊞ T'.obj₂ ⟶ T'.obj₂))
          simp only [biprod.inr_snd]
          exact ⟨⟨𝟙 _, by simp⟩⟩)
    have hμ' : IsIso μ' := by
      apply Triangle.isIso_of_isIsos μ'
      · change IsIso (biprod.inr ≫
          (biprod.snd : T.obj₁ ⊞ T'.obj₁ ⟶ T'.obj₁))
        simp only [biprod.inr_snd]
        exact ⟨⟨𝟙 _, by simp⟩⟩
      · change IsIso (biprod.inr ≫
          (biprod.snd : T.obj₂ ⊞ T'.obj₂ ⟶ T'.obj₂))
        simp only [biprod.inr_snd]
        exact ⟨⟨𝟙 _, by simp⟩⟩
      · exact hμ'₃
    have hT' : T' ∈ distTriang C :=
      isomorphic_distinguished _ hU' _ (asIso μ')
    exact ⟨hT, hT'⟩
  · rintro ⟨hT, hT'⟩
    apply (distinguished_iff_of_iso (directSumProductTriangleIso T T')).mp
    apply productTriangle_distinguished
    intro j
    cases j
    · exact hT
    · exact hT'

/-- If the third map of a distinguished triangle is zero, its second map has a
right inverse. -/
theorem distinguished_triangle_second_right_inverse
    {T : Triangle C} (hT : T ∈ distTriang C) (hzero : T.mor₃ = 0) :
    ∃ s : T.obj₃ ⟶ T.obj₂, s ≫ T.mor₂ = 𝟙 T.obj₃ := by
  obtain ⟨e, _, he₂⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hzero
  refine ⟨biprod.inr ≫ e.inv, ?_⟩
  simp only [Category.assoc, he₂, e.inv_hom_id_assoc, biprod.inr_snd]

/-- A right inverse of the second map makes the biproduct comparison map an
isomorphism. -/
theorem split_triangle_biproduct_iso
    {T : Triangle C} (hT : T ∈ distTriang C) (s : T.obj₃ ⟶ T.obj₂)
    (hs : s ≫ T.mor₂ = 𝟙 T.obj₃) :
    IsIso (biprod.desc T.mor₁ s) := by
  change s ≫ T.mor₂ = 𝟙 T.obj₃ at hs
  have hzero : T.mor₃ = 0 := by
    calc
      T.mor₃ = 𝟙 T.obj₃ ≫ T.mor₃ := by simp
      _ = (s ≫ T.mor₂) ≫ T.mor₃ := by rw [hs]
      _ = 0 := by rw [Category.assoc, comp_distTriang_mor_zero₂₃ T hT, comp_zero]
  have hfactor : (𝟙 T.obj₂ - T.mor₂ ≫ s) ≫ T.mor₂ = 0 := by
    rw [sub_comp, Category.id_comp, Category.assoc, hs, Category.comp_id, sub_self]
  obtain ⟨f, hf⟩ := T.coyoneda_exact₂ hT (𝟙 T.obj₂ - T.mor₂ ≫ s) hfactor
  have hmono : Mono T.mor₁ := T.mono₁ hT hzero
  have hf₁ : T.mor₁ ≫ f = 𝟙 T.obj₁ := by
    rw [← cancel_mono T.mor₁]
    calc
      (T.mor₁ ≫ f) ≫ T.mor₁ = T.mor₁ ≫ (f ≫ T.mor₁) := by simp [Category.assoc]
      _ = T.mor₁ ≫ (𝟙 T.obj₂ - T.mor₂ ≫ s) := by rw [← hf]
      _ = T.mor₁ := by
        rw [comp_sub, Category.comp_id, ← Category.assoc,
          show T.mor₁ ≫ T.mor₂ = 0 from comp_distTriang_mor_zero₁₂ T hT]
        simp
      _ = 𝟙 T.obj₁ ≫ T.mor₁ := by simp
  have hsf : s ≫ f = 0 := by
    rw [← cancel_mono T.mor₁]
    calc
      (s ≫ f) ≫ T.mor₁ = s ≫ (f ≫ T.mor₁) := by simp [Category.assoc]
      _ = s ≫ (𝟙 T.obj₂ - T.mor₂ ≫ s) := by rw [← hf]
      _ = 0 := by
        rw [comp_sub, Category.comp_id, ← Category.assoc,
          show s ≫ T.mor₂ = 𝟙 T.obj₃ from hs]
        simp
      _ = 0 ≫ T.mor₁ := by simp
  let r : T.obj₂ ⟶ T.obj₁ ⊞ T.obj₃ := biprod.lift f T.mor₂
  let d : T.obj₁ ⊞ T.obj₃ ⟶ T.obj₂ := biprod.desc T.mor₁ s
  have hdr : d ≫ r = 𝟙 _ := by
    dsimp [d, r]
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp only [biprod.inl_desc_assoc, Category.assoc, biprod.lift_fst, hf₁,
          biprod.inl_fst, Category.comp_id]
      · simp only [biprod.inl_desc_assoc, Category.assoc, biprod.lift_snd,
          comp_distTriang_mor_zero₁₂ T hT, biprod.inl_snd,
          Category.id_comp]
    · apply biprod.hom_ext
      · simp only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst, hsf,
          biprod.inr_fst, Category.comp_id]
      · simp only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_snd, hs,
          biprod.inr_snd, Category.id_comp]
  have hrd : r ≫ d = 𝟙 _ := by
    dsimp [r, d]
    rw [biprod.lift_desc, ← hf]
    simp
  exact ⟨⟨r, hdr, hrd⟩⟩

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

private lemma projectionCoprojection_of_hasKernel
    {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    ProjectionCoprojection f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (kernel.ι f)
  have hki : Mono (kernel.ι f) := by
    change Mono (Fork.ι (limit.cone (parallelPair f 0)))
    exact Fork.IsLimit.mono (limit.isLimit (parallelPair f 0))
  have hzero : h = 0 := by
    apply (Triangle.mk (kernel.ι f) g h).mor₃_eq_zero_of_mono₁ hT
    change Mono (kernel.ι f)
    exact hki
  obtain ⟨eX, heX₁, heX₂⟩ :=
    exists_iso_binaryBiproduct_of_distTriang (Triangle.mk (kernel.ι f) g h) hT hzero
  change X ≅ kernel f ⊞ Z at eX
  change kernel.ι f ≫ eX.hom = (biprod.inl : kernel f ⟶ kernel f ⊞ Z) at heX₁
  change g = eX.hom ≫ (biprod.snd : kernel f ⊞ Z ⟶ Z) at heX₂
  obtain ⟨q, hq⟩ :=
    (Triangle.mk (kernel.ι f) g h).yoneda_exact₂ hT f (kernel.condition f)
  change Z ⟶ Y at q
  change f = g ≫ q at hq
  have hfactor : f = eX.hom ≫ biprod.snd ≫ q := by
    calc
      f = g ≫ q := hq
      _ = eX.hom ≫ biprod.snd ≫ q := by
        rw [heX₂]
        rw [Category.assoc]
  have hqmono : Mono q := by
    rw [mono_iff_cancel_zero]
    intro A a ha
    have hkill : (a ≫ biprod.inr ≫ eX.inv) ≫ f = 0 := by
      calc
        (a ≫ biprod.inr ≫ eX.inv) ≫ f =
            (a ≫ biprod.inr ≫ eX.inv) ≫
              (eX.hom ≫ biprod.snd ≫ q) :=
          congrArg (fun k : X ⟶ Y => (a ≫ biprod.inr ≫ eX.inv) ≫ k) hfactor
        _ = 0 := by simp [Category.assoc, ha]
    obtain ⟨l, hl⟩ := kernel.lift' f (a ≫ biprod.inr ≫ eX.inv) hkill
    have hla : l ≫ (biprod.inl : kernel f ⟶ kernel f ⊞ Z) =
        a ≫ (biprod.inr : Z ⟶ kernel f ⊞ Z) := by
      calc
        l ≫ (biprod.inl : kernel f ⟶ kernel f ⊞ Z) =
            l ≫ kernel.ι f ≫ eX.hom := by rw [heX₁]
        _ = (a ≫ biprod.inr ≫ eX.inv) ≫ eX.hom := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ eX.hom) hl
        _ = a ≫ biprod.inr := by simp
    calc
      a = a ≫ 𝟙 _ := by simp
      _ = a ≫ biprod.inr ≫ biprod.snd := by simp
      _ = l ≫ biprod.inl ≫ biprod.snd := by
        simpa only [Category.assoc] using
          (congrArg (fun k => k ≫ biprod.snd) hla).symm
      _ = 0 := by simp
  obtain ⟨Q, r, s, hU⟩ := distinguished_cocone_triangle q
  have hszero : s = 0 := by
    apply (Triangle.mk q r s).mor₃_eq_zero_of_mono₁ hU
    exact hqmono
  obtain ⟨eY, heY₁, heY₂⟩ :=
    exists_iso_binaryBiproduct_of_distTriang (Triangle.mk q r s) hU hszero
  change Y ≅ Z ⊞ Q at eY
  change q ≫ eY.hom = (biprod.inl : Z ⟶ Z ⊞ Q) at heY₁
  have hq' : q = (biprod.inl : Z ⟶ Z ⊞ Q) ≫ eY.inv := by
    rw [← cancel_mono eY.hom]
    simp [heY₁]
  refine ⟨kernel f, Z, Q, eX, eY, ?_⟩
  calc
    f = eX.hom ≫ biprod.snd ≫ q := hfactor
    _ = eX.hom ≫ biprod.snd ≫ biprod.inl ≫ eY.inv := by rw [hq']

private lemma projectionCoprojection_of_hasCokernel
    {X Y : C} (f : X ⟶ Y) [HasCokernel f] :
    ProjectionCoprojection f := by
  obtain ⟨A, g, h, hT⟩ := distinguished_cocone_triangle₁ (cokernel.π f)
  have hzero : h = 0 := by
    apply (Triangle.mk g (cokernel.π f) h).mor₃_eq_zero_of_epi₂ hT
    change Epi (cokernel.π f)
    infer_instance
  obtain ⟨eY, heY₁, heY₂⟩ :=
    exists_iso_binaryBiproduct_of_distTriang (Triangle.mk g (cokernel.π f) h) hT hzero
  change Y ≅ A ⊞ cokernel f at eY
  change g ≫ eY.hom = (biprod.inl : A ⟶ A ⊞ cokernel f) at heY₁
  change cokernel.π f = eY.hom ≫
    (biprod.snd : A ⊞ cokernel f ⟶ cokernel f) at heY₂
  obtain ⟨p, hp⟩ :=
    (Triangle.mk g (cokernel.π f) h).coyoneda_exact₂ hT f (cokernel.condition f)
  change X ⟶ A at p
  change f = p ≫ g at hp
  have hp_epi : Epi p := by
    rw [epi_iff_cancel_zero]
    intro B d hd
    let c := eY.hom ≫ biprod.fst ≫ d
    change Y ⟶ B at c
    have hc : f ≫ c = 0 := by
      calc
        f ≫ c = (p ≫ g) ≫ c :=
          congrArg (fun k : X ⟶ Y => k ≫ c) hp
        _ = p ≫ (g ≫ eY.hom) ≫ biprod.fst ≫ d := by
          simp only [c, Category.assoc]
        _ = p ≫ (biprod.inl : A ⟶ A ⊞ cokernel f) ≫ biprod.fst ≫ d := by
          rw [heY₁]
        _ = 0 := by simp [hd]
    obtain ⟨l, hl⟩ := cokernel.desc' f c hc
    calc
      d = g ≫ c := by
        calc
          d = (biprod.inl : A ⟶ A ⊞ cokernel f) ≫ biprod.fst ≫ d := by simp
          _ = (g ≫ eY.hom) ≫ biprod.fst ≫ d := by rw [heY₁]
          _ = g ≫ c := by simp only [c, Category.assoc]
      _ = g ≫ cokernel.π f ≫ l := by
        simpa only [Category.assoc] using
          (congrArg (fun k : Y ⟶ B => g ≫ k) hl).symm
      _ = 0 := by
        have hcomp : g ≫ cokernel.π f = 0 :=
          comp_distTriang_mor_zero₁₂ _ hT
        calc
          g ≫ cokernel.π f ≫ l = (g ≫ cokernel.π f) ≫ l := by
            rw [Category.assoc]
          _ = 0 := by rw [hcomp]; simp
  obtain ⟨K, a, b, hU⟩ := distinguished_cocone_triangle₁ p
  have hszero : b = 0 := by
    apply (Triangle.mk a p b).mor₃_eq_zero_of_epi₂ hU
    change Epi p
    exact hp_epi
  obtain ⟨eX, heX₁, heX₂⟩ :=
    exists_iso_binaryBiproduct_of_distTriang (Triangle.mk a p b) hU hszero
  change X ≅ K ⊞ A at eX
  change p = eX.hom ≫ (biprod.snd : K ⊞ A ⟶ A) at heX₂
  have hg : g = (biprod.inl : A ⟶ A ⊞ cokernel f) ≫ eY.inv := by
    rw [← cancel_mono eY.hom]
    simp [heY₁]
  refine ⟨K, A, cokernel f, eX, eY, ?_⟩
  calc
    f = p ≫ g := hp
    _ = eX.hom ≫ biprod.snd ≫ g := by
      rw [heX₂]
      rw [Category.assoc]
    _ = eX.hom ≫ biprod.snd ≫ biprod.inl ≫ eY.inv := by rw [hg]

/-- For a split morphism, existence of a kernel, existence of a cokernel, and
the projection--coprojection normal form are equivalent. -/
theorem split_morphism_kernel_cokernel_iff
    {X Y : C} (f : X ⟶ Y) :
    (HasKernel f ↔ HasCokernel f) ∧
      (HasCokernel f ↔ ProjectionCoprojection f) := by
  constructor
  · constructor
    · intro h
      let : HasKernel f := h
      obtain ⟨K, Z, Q, eX, eY, hf⟩ := projectionCoprojection_of_hasKernel f
      rw [hf]
      infer_instance
    · intro h
      let : HasCokernel f := h
      obtain ⟨K, Z, Q, eX, eY, hf⟩ := projectionCoprojection_of_hasCokernel f
      rw [hf]
      infer_instance
  · constructor
    · intro h
      let : HasCokernel f := h
      exact projectionCoprojection_of_hasCokernel f
    · rintro ⟨K, Z, Q, eX, eY, hf⟩
      rw [hf]
      infer_instance

end Pretriangulated

/-! ## Products, coproducts, and idempotent completeness -/

section ProductsAndIdempotents

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ]
  [hAdditive : ∀ n : ℤ, (shiftFunctor C n).Additive]
  [hPretriangulated : Pretriangulated C]

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- A shift equivalence transports any existing product to the product of the
shifted family. -/
lemma shift_has_product
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {J : Type w} (X : J → C) [HasProduct X] :
    HasProduct (fun j => X j⟦(1 : ℤ)⟧) := by
  let : HasLimit (Discrete.functor X ⋙ shiftFunctor C (1 : ℤ)) :=
    CategoryTheory.Adjunction.hasLimit_comp_equivalence
      (Discrete.functor X) (shiftFunctor C (1 : ℤ))
  exact hasLimit_of_iso
    (Discrete.compNatIsoDiscrete X (shiftFunctor C (1 : ℤ)))

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The dual coproduct transport along a shift equivalence. -/
lemma shift_has_coproduct
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {J : Type w} (X : J → C) [HasCoproduct X] :
    HasCoproduct (fun j => X j⟦(1 : ℤ)⟧) := by
  let : HasColimit (Discrete.functor X ⋙ shiftFunctor C (1 : ℤ)) :=
    CategoryTheory.Adjunction.hasColimit_comp_equivalence
      (Discrete.functor X) (shiftFunctor C (1 : ℤ))
  exact hasColimit_of_iso
    (Discrete.compNatIsoDiscrete X (shiftFunctor C (1 : ℤ))).symm

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The shift comparison for a product is an isomorphism whenever the source
and shifted products exist. -/
lemma shift_product_comparison_isIso
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {J : Type w} (X : J → C)
    [HasProduct X] [HasProduct (fun j => X j⟦(1 : ℤ)⟧)] :
    IsIso (piComparison (shiftFunctor C (1 : ℤ)) X) := by
  infer_instance

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The dual shift comparison for a coproduct is an isomorphism whenever the
source and shifted coproducts exist. -/
lemma shift_coproduct_comparison_isIso
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {J : Type w} (X : J → C)
    [HasCoproduct X] [HasCoproduct (fun j => X j⟦(1 : ℤ)⟧)] :
    IsIso (sigmaComparison (shiftFunctor C (1 : ℤ)) X) := by
  infer_instance

/-- Products of distinguished triangles are distinguished. -/
/- The source assumes only the three products.  This wrapper installs the
   shifted first product supplied by the preceding shift lemma before using
   Mathlib's canonical product triangle. -/
def productTriangleOf
    {J : Type w} (T : J → Triangle C)
    [HasProduct (fun j => (T j).obj₁)]
    [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)] : Triangle C := by
  letI : HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧) :=
    shift_has_product (fun j => (T j).obj₁)
  exact productTriangle T

theorem product_of_distinguished_triangles
    {J : Type w} (T : J → Triangle C)
    (hT : ∀ j, T j ∈ distTriang C)
    [HasProduct (fun j => (T j).obj₁)]
    [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)] :
    productTriangleOf T ∈ distTriang C := by
  let hshift : HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧) :=
    shift_has_product (fun j => (T j).obj₁)
  simpa [productTriangleOf] using
    @productTriangle_distinguished C _ _ _ _ _ _ J T hT _ _ _ hshift

/-- The canonical coproduct triangle, with the third map transported across
the shift--coproduct comparison. -/
def coproductTriangle
    {J : Type w} (T : J → Triangle C)
    [HasCoproduct (fun j => (T j).obj₁)]
    [HasCoproduct (fun j => (T j).obj₂)]
    [HasCoproduct (fun j => (T j).obj₃)] : Triangle C := by
  letI : HasCoproduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧) :=
    shift_has_coproduct (fun j => (T j).obj₁)
  exact Triangle.mk
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
    [HasCoproduct (fun j => (T j).obj₃)] :
    coproductTriangle T ∈ distTriang C := by
  let : AdditiveCategory Cᵒᵖ :=
    { toPreadditive := inferInstance
      toHasFiniteProducts := inferInstance }
  let : Pretriangulated Cᵒᵖ := inferInstance
  let Top : J → Triangle Cᵒᵖ := fun j =>
    (triangleOpEquivalence C).functor.obj (Opposite.op (T j))
  let : HasProduct (fun j => (Top j).obj₁) := by
    change HasProduct (fun j => Opposite.op (T j).obj₃)
    infer_instance
  let : HasProduct (fun j => (Top j).obj₂) := by
    change HasProduct (fun j => Opposite.op (T j).obj₂)
    infer_instance
  let : HasProduct (fun j => (Top j).obj₃) := by
    change HasProduct (fun j => Opposite.op (T j).obj₁)
    infer_instance
  let : HasProduct (fun j => (Top j).obj₁⟦(1 : ℤ)⟧) :=
    shift_has_product (fun j => (Top j).obj₁)
  have hTop : ∀ j, Top j ∈ distTriang Cᵒᵖ := by
    intro j
    exact op_distinguished (T j) (hT j)
  let P : Triangle Cᵒᵖ := productTriangle Top
  have hP : P ∈ distTriang Cᵒᵖ := by
    exact productTriangle_distinguished Top hTop
  let U : Triangle C :=
    ((triangleOpEquivalence C).inverse.obj P).unop
  have hU : U ∈ distTriang C := by
    exact unop_distinguished P hP
  let e₁ : (coproductTriangle T).obj₁ ≅ U.obj₁ :=
    (opCoproductIsoProduct (fun j => (T j).obj₁)).unop.symm
  let e₂ : (coproductTriangle T).obj₂ ≅ U.obj₂ :=
    (opCoproductIsoProduct (fun j => (T j).obj₂)).unop.symm
  let e₃ : (coproductTriangle T).obj₃ ≅ U.obj₃ :=
    (opCoproductIsoProduct (fun j => (T j).obj₃)).unop.symm
  dsimp [coproductTriangle] at e₁ e₂ e₃
  change (∐ fun j => (T j).obj₁) ≅ U.obj₁ at e₁
  change (∐ fun j => (T j).obj₂) ≅ U.obj₂ at e₂
  change (∐ fun j => (T j).obj₃) ≅ U.obj₃ at e₃
  have he₁ι (j : J) :
      Sigma.ι (fun j => (T j).obj₁) j ≫ e₁.hom =
        (Pi.π (fun j => (Top j).obj₃) j).unop := by
    change Sigma.ι (fun j => (T j).obj₁) j ≫
        (opCoproductIsoProduct (fun j => (T j).obj₁)).inv.unop =
      (Pi.π (fun j => Opposite.op (T j).obj₁) j).unop
    apply Quiver.Hom.op_inj
    simpa only [op_comp, Quiver.Hom.op_unop] using
      (opCoproductIsoProduct_inv_comp_ι (fun j => (T j).obj₁) j)
  have he₂ι (j : J) :
      Sigma.ι (fun j => (T j).obj₂) j ≫ e₂.hom =
        (Pi.π (fun j => (Top j).obj₂) j).unop := by
    change Sigma.ι (fun j => (T j).obj₂) j ≫
        (opCoproductIsoProduct (fun j => (T j).obj₂)).inv.unop =
      (Pi.π (fun j => Opposite.op (T j).obj₂) j).unop
    apply Quiver.Hom.op_inj
    simpa only [op_comp, Quiver.Hom.op_unop] using
      (opCoproductIsoProduct_inv_comp_ι (fun j => (T j).obj₂) j)
  have he₃ι (j : J) :
      Sigma.ι (fun j => (T j).obj₃) j ≫ e₃.hom =
        (Pi.π (fun j => (Top j).obj₁) j).unop := by
    change Sigma.ι (fun j => (T j).obj₃) j ≫
        (opCoproductIsoProduct (fun j => (T j).obj₃)).inv.unop =
      (Pi.π (fun j => Opposite.op (T j).obj₃) j).unop
    apply Quiver.Hom.op_inj
    simpa only [op_comp, Quiver.Hom.op_unop] using
      (opCoproductIsoProduct_inv_comp_ι (fun j => (T j).obj₃) j)
  have hU₁mor : U.mor₁ =
      (Limits.Pi.map (f := fun j => Opposite.op (T j).obj₂)
        (g := fun j => Opposite.op (T j).obj₁)
        (fun j => (T j).mor₁.op)).unop := by
    rfl
  have hU₂mor : U.mor₂ =
      (Limits.Pi.map (f := fun j => Opposite.op (T j).obj₃)
        (g := fun j => Opposite.op (T j).obj₂)
        (fun j => (T j).mor₂.op)).unop := by
    rfl
  have hcomm₁ : (coproductTriangle T).mor₁ ≫ e₂.hom =
      e₁.hom ≫ U.mor₁ := by
    dsimp [U, P, Top]
    dsimp [coproductTriangle]
    change (Limits.Sigma.map (f := fun j => (T j).obj₁)
      (g := fun j => (T j).obj₂) (fun j => (T j).mor₁)) ≫ e₂.hom =
      e₁.hom ≫ U.mor₁
    apply Sigma.hom_ext
    intro j
    let q₁ : (T j).obj₁ ⟶ U.obj₁ :=
      (Pi.π (fun j => (Top j).obj₃) j).unop
    let q₂ : (T j).obj₂ ⟶ U.obj₂ :=
      (Pi.π (fun j => (Top j).obj₂) j).unop
    have hpi₁ :
        q₁ ≫ U.mor₁ = (T j).mor₁ ≫ q₂ := by
      rw [hU₁mor]
      apply Quiver.Hom.op_inj
      change
        (Limits.Pi.map (f := fun j => Opposite.op (T j).obj₂)
          (g := fun j => Opposite.op (T j).obj₁)
          (fun j => (T j).mor₁.op)) ≫
            Pi.π (fun j => Opposite.op (T j).obj₁) j =
          Pi.π (fun j => Opposite.op (T j).obj₂) j ≫ (T j).mor₁.op
      exact Limits.Pi.map_π (fun j => (T j).mor₁.op) j
    calc
      Sigma.ι (fun j => (T j).obj₁) j ≫
          Limits.Sigma.map (fun j => (T j).mor₁) ≫ e₂.hom =
          ((T j).mor₁ ≫ Sigma.ι (fun j => (T j).obj₂) j) ≫ e₂.hom := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ e₂.hom)
            (Limits.Sigma.ι_map (f := fun j => (T j).obj₁)
              (g := fun j => (T j).obj₂) (fun j => (T j).mor₁) j)
      _ = (T j).mor₁ ≫ q₂ := by
        simpa only [q₂, Category.assoc] using
          congrArg (fun k => (T j).mor₁ ≫ k) (he₂ι j)
      _ = q₁ ≫ U.mor₁ := by
        exact hpi₁.symm
      _ = Sigma.ι (fun j => (T j).obj₁) j ≫ e₁.hom ≫ U.mor₁ := by
        simpa only [q₁, Category.assoc] using
          (congrArg (fun k => k ≫ U.mor₁) (he₁ι j)).symm
  have hcomm₂ : (coproductTriangle T).mor₂ ≫ e₃.hom =
      e₂.hom ≫ U.mor₂ := by
    dsimp [U, P, Top]
    dsimp [coproductTriangle]
    change (Limits.Sigma.map (f := fun j => (T j).obj₂)
      (g := fun j => (T j).obj₃) (fun j => (T j).mor₂)) ≫ e₃.hom =
      e₂.hom ≫ U.mor₂
    apply Sigma.hom_ext
    intro j
    let q₂ : (T j).obj₂ ⟶ U.obj₂ :=
      (Pi.π (fun j => (Top j).obj₂) j).unop
    let q₃ : (T j).obj₃ ⟶ U.obj₃ :=
      (Pi.π (fun j => (Top j).obj₁) j).unop
    have hpi₂ :
        (T j).mor₂ ≫ q₃ = q₂ ≫ U.mor₂ := by
      rw [hU₂mor]
      apply Quiver.Hom.op_inj
      change
        Pi.π (fun j => Opposite.op (T j).obj₃) j ≫ (T j).mor₂.op =
          (Limits.Pi.map (f := fun j => Opposite.op (T j).obj₃)
          (g := fun j => Opposite.op (T j).obj₂)
          (fun j => (T j).mor₂.op)) ≫
            Pi.π (fun j => Opposite.op (T j).obj₂) j
      exact (Limits.Pi.map_π (fun j => (T j).mor₂.op) j).symm
    calc
      Sigma.ι (fun j => (T j).obj₂) j ≫
          Limits.Sigma.map (fun j => (T j).mor₂) ≫ e₃.hom =
          ((T j).mor₂ ≫ Sigma.ι (fun j => (T j).obj₃) j) ≫ e₃.hom := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ e₃.hom)
            (Limits.Sigma.ι_map (f := fun j => (T j).obj₂)
              (g := fun j => (T j).obj₃) (fun j => (T j).mor₂) j)
      _ = (T j).mor₂ ≫ q₃ := by
        simpa only [q₃, Category.assoc] using
          congrArg (fun k => (T j).mor₂ ≫ k) (he₃ι j)
      _ = q₂ ≫ U.mor₂ := by
        exact hpi₂
      _ = Sigma.ι (fun j => (T j).obj₂) j ≫ e₂.hom ≫ U.mor₂ := by
        simpa only [q₂, Category.assoc] using
          (congrArg (fun k => k ≫ U.mor₂) (he₂ι j)).symm
  have hcomm₃ : (coproductTriangle T).mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' =
      e₃.hom ≫ U.mor₃ := by
    let : HasCoproduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧) :=
      shift_has_coproduct (fun j => (T j).obj₁)
    dsimp [coproductTriangle]
    change
      ((Limits.Sigma.map (fun j => (T j).mor₃) ≫
          sigmaComparison (shiftFunctor C (1 : ℤ))
            (fun j => (T j).obj₁)) ≫ e₁.hom⟦(1 : ℤ)⟧') =
        e₃.hom ≫ U.mor₃
    apply Sigma.hom_ext
    intro j
    have hσ :
        Sigma.ι (fun j => (shiftFunctor C (1 : ℤ)).obj ((T j).obj₁)) j ≫
            sigmaComparison (shiftFunctor C (1 : ℤ))
              (fun j => (T j).obj₁) =
          (shiftFunctor C (1 : ℤ)).map
            (Sigma.ι (fun j => (T j).obj₁) j) := by
      dsimp [sigmaComparison]
      simp
    let q₁ : (T j).obj₁ ⟶ U.obj₁ :=
      (Pi.π (fun j => (Top j).obj₃) j).unop
    let q₃ : (T j).obj₃ ⟶ U.obj₃ :=
      (Pi.π (fun j => (Top j).obj₁) j).unop
    have hpi₃ :
        (T j).mor₃ ≫ (shiftFunctor C (1 : ℤ)).map q₁ =
          q₃ ≫ U.mor₃ := by
      apply Quiver.Hom.op_inj
      dsimp [q₁, q₃]
      apply Quiver.Hom.unop_inj
      simp only [unop_comp, Quiver.Hom.unop_op]
      have huπ :=
        opShiftFunctorEquivalence_unitIso_inv_naturality (C := C) (1 : ℤ)
          (Pi.π (fun j => (Top j).obj₁) j)
      have huπ' := congrArg Quiver.Hom.unop huπ
      simp only [unop_comp, Quiver.Hom.unop_op] at huπ'
      change
        (T j).mor₃ ≫ (shiftFunctor C (1 : ℤ)).map
            (Pi.π (fun j => (Top j).obj₃) j).unop =
          (Pi.π (fun j => (Top j).obj₁) j).unop ≫
            ((opShiftFunctorEquivalence C (1 : ℤ)).unitIso.inv.app
                (∏ᶜ fun j => (Top j).obj₁)).unop ≫
              (shiftFunctor C (1 : ℤ)).map
                ((Limits.Pi.map (fun j => (Top j).mor₃) ≫
                  inv (piComparison (shiftFunctor Cᵒᵖ (1 : ℤ))
                    (fun j => (Top j).obj₁))).unop)
      have hunit := congrArg
        (fun k => k ≫ (shiftFunctor C (1 : ℤ)).map
          ((Limits.Pi.map (fun j => (Top j).mor₃) ≫
            inv (piComparison (shiftFunctor Cᵒᵖ (1 : ℤ))
              (fun j => (Top j).obj₁))).unop)) huπ'.symm
      have hunit' :
          (Pi.π (fun j => (Top j).obj₁) j).unop ≫
              ((opShiftFunctorEquivalence C (1 : ℤ)).unitIso.inv.app
                (∏ᶜ fun j => (Top j).obj₁)).unop ≫
            (shiftFunctor C (1 : ℤ)).map
              ((Limits.Pi.map (fun j => (Top j).mor₃) ≫
                inv (piComparison (shiftFunctor Cᵒᵖ (1 : ℤ))
                  (fun j => (Top j).obj₁))).unop) =
          ((opShiftFunctorEquivalence C (1 : ℤ)).unitIso.inv.app
              (Top j).obj₁).unop ≫
            (shiftFunctor C (1 : ℤ)).map
              ((shiftFunctor Cᵒᵖ (1 : ℤ)).map
                (Pi.π (fun j => (Top j).obj₁) j)).unop ≫
            (shiftFunctor C (1 : ℤ)).map
              ((Limits.Pi.map (fun j => (Top j).mor₃) ≫
                inv (piComparison (shiftFunctor Cᵒᵖ (1 : ℤ))
                  (fun j => (Top j).obj₁))).unop) := by
        simpa only [Category.assoc] using hunit
      rw [hunit']
      rw [← Functor.map_comp, ← unop_comp]
      have hQ :
          ((Limits.Pi.map (fun j => (Top j).mor₃) ≫
              inv (piComparison (shiftFunctor Cᵒᵖ (1 : ℤ))
                (fun j => (Top j).obj₁))) ≫
            (shiftFunctor Cᵒᵖ (1 : ℤ)).map
              (Pi.π (fun j => (Top j).obj₁) j)) =
        Pi.π (fun j => (Top j).obj₃) j ≫ (Top j).mor₃ := by
        rw [Category.assoc, inv_piComparison_comp_map_π,
          Limits.Pi.map_π]
      rw [hQ]
      simp only [unop_comp, Functor.map_comp]
      have hcancel :
          ((opShiftFunctorEquivalence C (1 : ℤ)).unitIso.inv.app
              (Top j).obj₁).unop ≫
            (shiftFunctor C (1 : ℤ)).map ((Top j).mor₃.unop) =
          (T j).mor₃ := by
        change
          ((opShiftFunctorEquivalence C (1 : ℤ)).unitIso.inv.app
              (Opposite.op (T j).obj₃)).unop ≫
            (shiftFunctor C (1 : ℤ)).map
              (opShiftFunctorEquivalenceSymmHomEquiv
                (C := C) (n := (1 : ℤ))
                (X := Opposite.op (T j).obj₁)
                (Y := Opposite.op (T j).obj₃) (T j).mor₃.op).unop =
            (T j).mor₃
        exact opShiftFunctorEquivalenceSymmHomEquiv_left_inv
            (C := C) (n := (1 : ℤ))
            (X := Opposite.op (T j).obj₁)
            (Y := Opposite.op (T j).obj₃) (f := (T j).mor₃.op)
      rw [← Category.assoc, hcancel]
      rfl
    calc
      Sigma.ι (fun j => (T j).obj₃) j ≫
          ((Limits.Sigma.map (fun j => (T j).mor₃) ≫
            sigmaComparison (shiftFunctor C (1 : ℤ))
              (fun j => (T j).obj₁)) ≫
            (shiftFunctor C (1 : ℤ)).map e₁.hom) =
          ((T j).mor₃ ≫
            Sigma.ι (fun j => (shiftFunctor C (1 : ℤ)).obj
              ((T j).obj₁)) j ≫
              sigmaComparison (shiftFunctor C (1 : ℤ))
                (fun j => (T j).obj₁)) ≫
            (shiftFunctor C (1 : ℤ)).map e₁.hom := by
        simpa only [Category.assoc] using
          congrArg
            (fun k => k ≫ sigmaComparison (shiftFunctor C (1 : ℤ))
              (fun j => (T j).obj₁) ≫
              (shiftFunctor C (1 : ℤ)).map e₁.hom)
            (Limits.Sigma.ι_map (f := fun j => (T j).obj₃)
              (g := fun j => (shiftFunctor C (1 : ℤ)).obj ((T j).obj₁))
              (fun j => (T j).mor₃) j)
      _ = ((T j).mor₃ ≫
            (shiftFunctor C (1 : ℤ)).map
              (Sigma.ι (fun j => (T j).obj₁) j)) ≫
            (shiftFunctor C (1 : ℤ)).map e₁.hom := by
        simpa only [Category.assoc] using
          congrArg
            (fun k => (T j).mor₃ ≫ k ≫
              (shiftFunctor C (1 : ℤ)).map e₁.hom) hσ
      _ = (T j).mor₃ ≫
          (shiftFunctor C (1 : ℤ)).map
            (Sigma.ι (fun j => (T j).obj₁) j ≫ e₁.hom) := by
        rw [Functor.map_comp]
        simp only [Category.assoc]
      _ = (T j).mor₃ ≫
          (shiftFunctor C (1 : ℤ)).map q₁ := by
        simpa only [q₁] using
          congrArg
            (fun k => (T j).mor₃ ≫ (shiftFunctor C (1 : ℤ)).map k)
            (he₁ι j)
      _ = q₃ ≫ U.mor₃ := hpi₃
      _ = Sigma.ι (fun j => (T j).obj₃) j ≫ e₃.hom ≫ U.mor₃ := by
        simpa only [q₃, Category.assoc] using
          (congrArg (fun k => k ≫ U.mor₃) (he₃ι j)).symm
  exact isomorphic_distinguished _ hU _
    (Triangle.isoMk (coproductTriangle T) U e₁ e₂ e₃ hcomm₁ hcomm₂ hcomm₃)

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

/-- The source's easier formulation of TR4 is equivalent to the canonical
octahedron axiom after replacing the three objects by isomorphic ones. -/
theorem easier_axiom_four_iff :
    CategoryTheory.IsTriangulated C ↔
      ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
        ∃ (X' Y' Z' : C) (eX : X' ≅ X) (eY : Y' ≅ Y) (eZ : Z' ≅ Z),
          ∃ (Qone Qtwo Qthree : C)
            (pone : Y' ⟶ Qone) (done : Qone ⟶ X'⟦(1 : ℤ)⟧)
            (ptwo : Z' ⟶ Qtwo) (dtwo : Qtwo ⟶ X'⟦(1 : ℤ)⟧)
            (pthree : Z' ⟶ Qthree) (dthree : Qthree ⟶ Y'⟦(1 : ℤ)⟧),
            ∃ (h₁₂ : Triangle.mk (eX.hom ≫ f ≫ eY.inv) pone done ∈ distTriang C)
              (h₁₃ : Triangle.mk
                ((eX.hom ≫ f ≫ eY.inv) ≫ (eY.hom ≫ g ≫ eZ.inv)) ptwo dtwo ∈
                distTriang C)
              (h₂₃ : Triangle.mk (eY.hom ≫ g ≫ eZ.inv) pthree dthree ∈
                distTriang C),
              Nonempty (Triangulated.Octahedron (C := C) (by rfl) h₁₂ h₂₃ h₁₃) := by
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
bottom row and rightmost column use Mathlib's canonical triangle shift, so the
signs and shift comparison maps in the source's ``obtained by applying [1]``
clause are part of the type. -/
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
  row₃ : (Triangle.shiftFunctor C (1 : ℤ)).obj (Triangle.mk f g h) ∈
      distTriang C
  col₀ : Triangle.mk a a' a'' ∈ distTriang C
  col₁ : Triangle.mk b b' b'' ∈ distTriang C
  col₂ : Triangle.mk c c' c'' ∈ distTriang C
  col₃ : (Triangle.shiftFunctor C (1 : ℤ)).obj (Triangle.mk a a' a'') ∈
      distTriang C
  comm₀₁ : g ≫ c = b ≫ g'
  comm₀₂ : h ≫ a⟦(1 : ℤ)⟧' = c ≫ h'
  comm₁₀ : f' ≫ b' = a' ≫ f''
  comm₁₁ : g' ≫ c' = b' ≫ g''
  comm₁₂ : h' ≫ a'⟦(1 : ℤ)⟧' = c' ≫ h''
  comm₂₀ : f'' ≫ b'' = a'' ≫
      ((Triangle.shiftFunctor C (1 : ℤ)).obj (Triangle.mk f g h)).mor₁
  comm₂₁ : g'' ≫ c'' = b'' ≫
      ((Triangle.shiftFunctor C (1 : ℤ)).obj (Triangle.mk f g h)).mor₂
  anti₂₂ : h'' ≫
      ((Triangle.shiftFunctor C (1 : ℤ)).obj (Triangle.mk a a' a'')).mor₃ =
      -(c'' ≫ ((Triangle.shiftFunctor C (1 : ℤ)).obj (Triangle.mk f g h)).mor₃)

/-- TR4 completes every commutative square to the source's 3 by 3 diagram. -/
theorem three_by_three_completion
    [CategoryTheory.IsTriangulated C]
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') :
    Nonempty (ThreeByThreeDiagram f f' a b comm) := by
  sorry

end ThreeByThree

end Formalization.Books.Derived.Unit04
