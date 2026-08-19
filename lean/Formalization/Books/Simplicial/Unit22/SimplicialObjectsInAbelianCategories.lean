import Formalization.Books.Simplicial.Unit21.LeftAdjointsToSkeletonFunctors
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Simplicial Methods, Chapter 22: Simplicial objects in abelian categories

This file records the constructions and interfaces in the source section.  Kan
extensions and the finite direct sums are kept in the canonical Mathlib form;
the index types below make the source's surjective, injective, and image
conditions explicit.
-/

namespace Formalization.Books.Simplicial.Unit22

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial
open scoped ZeroObject

universe v u

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-! ## The abelian functor-category facts -/

theorem simplicialObject_abelian {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (Abelian (SimplicialObject C)) :=
  ⟨inferInstance⟩

/- The covariant presentation uses the canonical functor-category instance;
   `CosimplicialObject C` has a separate reducible category instance in
   Mathlib, so keeping this type explicit avoids an instance ambiguity. -/
theorem cosimplicialObject_abelian {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (Abelian (SimplexCategory ⥤ C)) :=
  ⟨inferInstance⟩

theorem simplicial_mono_iff_componentwise
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    Mono f ↔ ∀ n, Mono (f.app n) := by
  simpa using
    (NatTrans.mono_iff_mono_app (f := f) :
      Mono f ↔ ∀ n : SimplexCategoryᵒᵖ, Mono (f.app n))

theorem cosimplicial_mono_iff_componentwise
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : SimplexCategory ⥤ C} (f : X ⟶ Y) :
    Mono f ↔ ∀ n, Mono (f.app n) := by
  simpa using
    (NatTrans.mono_iff_mono_app (f := f) :
      Mono f ↔ ∀ n : SimplexCategory, Mono (f.app n))

theorem simplicial_epi_iff_componentwise
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    Epi f ↔ ∀ n, Epi (f.app n) := by
  simpa using
    (NatTrans.epi_iff_epi_app (f := f) :
      Epi f ↔ ∀ n : SimplexCategoryᵒᵖ, Epi (f.app n))

theorem cosimplicial_epi_iff_componentwise
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : SimplexCategory ⥤ C} (f : X ⟶ Y) :
    Epi f ↔ ∀ n, Epi (f.app n) := by
  simpa using
    (NatTrans.epi_iff_epi_app (f := f) :
      Epi f ↔ ∀ n : SimplexCategory, Epi (f.app n))

def simplicialEvaluationShortComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (SimplicialObject C)} (n : SimplexCategoryᵒᵖ) :
    ShortComplex C :=
  ((evaluation (SimplexCategoryᵒᵖ) C).obj n).mapShortComplex.obj S

def cosimplicialEvaluationShortComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (SimplexCategory ⥤ C)} (n : SimplexCategory) :
    ShortComplex C :=
  ((evaluation SimplexCategory C).obj n).mapShortComplex.obj S

theorem simplicial_exact_iff_componentwise
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (SimplicialObject C)) :
    S.Exact ↔ ∀ n, (simplicialEvaluationShortComplex (S := S) n).Exact := by
  let F : ∀ n : SimplexCategoryᵒᵖ, SimplicialObject C ⥤ C :=
    fun n => (evaluation (SimplexCategoryᵒᵖ) C).obj n
  have hF : JointlyReflectIsomorphisms F := by
    constructor
    intro X Y f
    dsimp [F] at *
    exact NatIso.isIso_of_isIso_app f
  simpa only [F, simplicialEvaluationShortComplex, Functor.mapShortComplex_obj] using
    hF.exact_iff S

theorem cosimplicial_exact_iff_componentwise
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (SimplexCategory ⥤ C)) :
    S.Exact ↔ ∀ n, (cosimplicialEvaluationShortComplex (S := S) n).Exact := by
  let F : ∀ n : SimplexCategory, (SimplexCategory ⥤ C) ⥤ C :=
    fun n => (evaluation SimplexCategory C).obj n
  have hF : JointlyReflectIsomorphisms F := by
    constructor
    intro X Y f
    dsimp [F] at *
    exact NatIso.isIso_of_isIso_app f
  simpa only [F, cosimplicialEvaluationShortComplex, Functor.mapShortComplex_obj] using
    hF.exact_iff S

/-! ## The concentrated truncated object -/

abbrev topTruncatedSimplex (k : ℕ) : SimplexCategory.Truncated k :=
  ⟨⦋k⦌, le_rfl⟩

noncomputable def concentratedTruncatedValue
    {C : Type u} [Category.{v} C] [HasZeroObject C]
    (A : C) (k : ℕ) (X : SimplexCategory.Truncated k) : C :=
  if X.obj.len = k then A else 0

noncomputable def concentratedTruncatedMap
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (A : C) (k : ℕ)
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y) :
    concentratedTruncatedValue A k X.unop ⟶
      concentratedTruncatedValue A k Y.unop := by
  classical
  by_cases hXY : X = Y
  · subst Y
    by_cases hx : X.unop.obj.len = k
    · by_cases hf : f = 𝟙 X
      · simpa [concentratedTruncatedValue, hx] using (𝟙 A)
      · simpa [concentratedTruncatedValue, hx] using (0 : A ⟶ A)
    · simpa [concentratedTruncatedValue, hx] using
        (0 : (0 : C) ⟶ (0 : C))
  · exact 0

theorem concentratedTruncatedMap_id
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (A : C) (k : ℕ) (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    concentratedTruncatedMap A k (𝟙 X) = 𝟙 _ := by
  classical
  have hcast_id : ∀ {B : C} (h : B = A) (p : (A ⟶ A) = (B ⟶ B)),
      cast p (𝟙 A) = 𝟙 B := by
    intro B h p
    subst B
    cases p
    rfl
  have hcast_zero : ∀ {B : C} (h : B = 0)
      (p : ((0 : C) ⟶ (0 : C)) = (B ⟶ B)),
      cast p (0 : (0 : C) ⟶ (0 : C)) = 𝟙 B := by
    intro B h p
    subst B
    cases p
    exact (isZero_zero C).eq_of_src _ _
  simp only [concentratedTruncatedMap]
  split
  · simp_all
    split
    · apply hcast_id
      simp_all [concentratedTruncatedValue]
    · apply hcast_zero
      simp_all [concentratedTruncatedValue]
  · simp_all

theorem concentratedTruncatedMap_comp
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (A : C) (k : ℕ) {X Y Z : (SimplexCategory.Truncated k)ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    concentratedTruncatedMap A k (f ≫ g) =
      concentratedTruncatedMap A k f ≫ concentratedTruncatedMap A k g := by
  classical
  have obj_eq_of_len_eq {P Q : (SimplexCategory.Truncated k)ᵒᵖ}
      (h : P.unop.obj.len = Q.unop.obj.len) : P = Q := by
    apply Opposite.unop_injective
    apply ObjectProperty.FullSubcategory.ext
    exact SimplexCategory.ext h
  have value_isZero_of_ne_top {P : (SimplexCategory.Truncated k)ᵒᵖ}
      (hP : P.unop.obj.len ≠ k) :
      IsZero (concentratedTruncatedValue A k P.unop) := by
    simpa [concentratedTruncatedValue, hP] using (isZero_zero C)
  have map_eq_zero_of_source_not_top {P Q : (SimplexCategory.Truncated k)ᵒᵖ}
      (u : P ⟶ Q) (hP : P.unop.obj.len ≠ k) :
      concentratedTruncatedMap A k u = 0 :=
    (value_isZero_of_ne_top hP).eq_of_src _ _
  have map_eq_zero_of_target_not_top {P Q : (SimplexCategory.Truncated k)ᵒᵖ}
      (u : P ⟶ Q) (hQ : Q.unop.obj.len ≠ k) :
      concentratedTruncatedMap A k u = 0 :=
    (value_isZero_of_ne_top hQ).eq_of_tgt _ _
  have hcast_zero_id : ∀ {B : C} (h : B = A) (p : (A ⟶ A) = (B ⟶ B)),
      cast p (0 : A ⟶ A) = 0 := by
    intro B h p
    subst B
    cases p
    rfl
  have map_eq_zero_of_ne_id {P : (SimplexCategory.Truncated k)ᵒᵖ}
      (u : P ⟶ P) (hu : u ≠ 𝟙 P) (hP : P.unop.obj.len = k) :
      concentratedTruncatedMap A k u = 0 := by
    simp only [concentratedTruncatedMap]
    split
    · simp_all
      apply hcast_zero_id
      simp_all [concentratedTruncatedValue]
    · simp_all
  have hcomp_top_obj {P Q : (SimplexCategory.Truncated k)ᵒᵖ}
      (u : P ⟶ Q) (v : Q ⟶ P) (h : u ≫ v = 𝟙 P)
      (hP : P.unop.obj.len = k) : P = Q := by
    have h' : v.unop.hom ≫ u.unop.hom = 𝟙 P.unop.obj := by
      simpa using congrArg (fun w => w.hom) (congrArg Quiver.Hom.unop h)
    let _ : IsSplitMono v.unop.hom := IsSplitMono.mk' ⟨u.unop.hom, h'⟩
    have hlen : P.unop.obj.len ≤ Q.unop.obj.len :=
      SimplexCategory.len_le_of_mono v.unop.hom
    have hQ : Q.unop.obj.len = k :=
      le_antisymm Q.unop.property (by simpa [hP] using hlen)
    have hPQ : P = Q := obj_eq_of_len_eq (hP.trans hQ.symm)
    exact hPQ
  have hcomp_top_end {P : (SimplexCategory.Truncated k)ᵒᵖ}
      (u v : P ⟶ P) (h : u ≫ v = 𝟙 P) (hP : P.unop.obj.len = k) :
      u = 𝟙 P ∧ v = 𝟙 P := by
    have h' : v.unop.hom ≫ u.unop.hom = 𝟙 P.unop.obj := by
      simpa using congrArg (fun w => w.hom) (congrArg Quiver.Hom.unop h)
    let _ : IsSplitMono v.unop.hom := IsSplitMono.mk' ⟨u.unop.hom, h'⟩
    have hv' : v.unop.hom = 𝟙 _ := SimplexCategory.eq_id_of_mono _
    have hv'' : v.unop = 𝟙 P.unop := by
      apply ObjectProperty.hom_ext _
      exact hv'
    have hv : v = 𝟙 P := by
      apply Quiver.Hom.unop_inj
      simpa using hv''
    refine ⟨?_, hv⟩
    rw [hv, Category.comp_id] at h
    exact h
  have map_eq_zero_of_ne_top {P Q : (SimplexCategory.Truncated k)ᵒᵖ}
      (u : P ⟶ Q) (h : P.unop.obj.len ≠ k ∨ Q.unop.obj.len ≠ k) :
      concentratedTruncatedMap A k u = 0 := by
    rcases h with h | h
    · exact map_eq_zero_of_source_not_top u h
    · exact map_eq_zero_of_target_not_top u h
  by_cases hXY : X = Y
  · subst Y
    by_cases hXZ : X = Z
    · subst Z
      by_cases hXtop : X.unop.obj.len = k
      · by_cases hf : f = 𝟙 X
        · by_cases hg : g = 𝟙 X
          · subst f
            subst g
            simp only [Category.id_comp, concentratedTruncatedMap_id]
          · have hcomp : f ≫ g ≠ 𝟙 X := by
              intro h
              exact hg (hcomp_top_end f g h hXtop).2
            rw [map_eq_zero_of_ne_id (f ≫ g) hcomp hXtop,
              hf, concentratedTruncatedMap_id,
              map_eq_zero_of_ne_id g hg hXtop,
              comp_zero]
        · have hcomp : f ≫ g ≠ 𝟙 X := by
            intro h
            exact hf (hcomp_top_end f g h hXtop).1
          rw [map_eq_zero_of_ne_id (f ≫ g) hcomp hXtop,
            map_eq_zero_of_ne_id f hf hXtop, zero_comp]
      · rw [map_eq_zero_of_source_not_top (f ≫ g) hXtop,
          map_eq_zero_of_source_not_top f hXtop,
          map_eq_zero_of_source_not_top g hXtop, zero_comp]
    · have hcompzero : concentratedTruncatedMap A k (f ≫ g) = 0 := by
        by_cases hXtop : X.unop.obj.len = k
        · have hZnot : Z.unop.obj.len ≠ k := by
            intro hZtop
            exact hXZ (obj_eq_of_len_eq (hXtop.trans hZtop.symm))
          exact map_eq_zero_of_target_not_top (f ≫ g) hZnot
        · exact map_eq_zero_of_source_not_top (f ≫ g) hXtop
      have hgzero : concentratedTruncatedMap A k g = 0 := by
        apply map_eq_zero_of_ne_top
        by_cases hXtop : X.unop.obj.len = k
        · right
          intro hZtop
          exact hXZ (obj_eq_of_len_eq (hXtop.trans hZtop.symm))
        · left
          exact hXtop
      rw [hcompzero, hgzero, comp_zero]
  · by_cases hYZ : Y = Z
    · subst Z
      have hfzero : concentratedTruncatedMap A k f = 0 := by
        apply map_eq_zero_of_ne_top
        by_cases hXtop : X.unop.obj.len = k
        · right
          intro hYtop
          exact hXY (obj_eq_of_len_eq (hXtop.trans hYtop.symm))
        · left
          exact hXtop
      have hcompzero : concentratedTruncatedMap A k (f ≫ g) = 0 := by
        apply map_eq_zero_of_ne_top
        by_cases hXtop : X.unop.obj.len = k
        · right
          intro hYtop
          exact hXY (obj_eq_of_len_eq (hXtop.trans hYtop.symm))
        · left
          exact hXtop
      rw [hcompzero, hfzero, zero_comp]
    · have hfzero : concentratedTruncatedMap A k f = 0 := by
        apply map_eq_zero_of_ne_top
        by_cases hXtop : X.unop.obj.len = k
        · right
          intro hYtop
          exact hXY (obj_eq_of_len_eq (hXtop.trans hYtop.symm))
        · left
          exact hXtop
      have hgzero : concentratedTruncatedMap A k g = 0 := by
        apply map_eq_zero_of_ne_top
        by_cases hYtop : Y.unop.obj.len = k
        · right
          intro hZtop
          exact hYZ (obj_eq_of_len_eq (hYtop.trans hZtop.symm))
        · left
          exact hYtop
      have hcompzero : concentratedTruncatedMap A k (f ≫ g) = 0 := by
        by_cases hXZ : X = Z
        · subst Z
          by_cases hXtop : X.unop.obj.len = k
          · apply map_eq_zero_of_ne_id
            intro h
            exact hXY (hcomp_top_obj f g h hXtop)
            exact hXtop
          · exact map_eq_zero_of_source_not_top (f ≫ g) hXtop
        · apply map_eq_zero_of_ne_top
          by_cases hXtop : X.unop.obj.len = k
          · right
            intro hZtop
            exact hXZ (obj_eq_of_len_eq (hXtop.trans hZtop.symm))
          · left
            exact hXtop
      rw [hcompzero, hfzero, hgzero, zero_comp]

noncomputable def concentratedTruncatedObject
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (A : C) (k : ℕ) : SimplicialObject.Truncated C k where
  obj X := concentratedTruncatedValue A k X.unop
  map := fun {_X _Y} f => concentratedTruncatedMap A k f
  map_id := concentratedTruncatedMap_id A k
  map_comp := concentratedTruncatedMap_comp A k

@[simp]
theorem concentratedTruncatedObject_top
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (A : C) (k : ℕ) :
    (concentratedTruncatedObject A k).obj (op (topTruncatedSimplex k)) = A := by
  simp [concentratedTruncatedObject, concentratedTruncatedValue,
    topTruncatedSimplex]

theorem concentratedTruncatedObject_lt
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (A : C) (k i : ℕ) (hi : i < k) :
    (concentratedTruncatedObject A k).obj
        (op (⟨⦋i⦌, by simpa using Nat.le_of_lt hi⟩ :
          SimplexCategory.Truncated k)) = 0 := by
  have hne : i ≠ k := Nat.ne_of_lt hi
  simp [concentratedTruncatedObject, concentratedTruncatedValue, hne]

theorem concentratedTruncatedObject_map_of_ne_id
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (A : C) (k : ℕ) {X : (SimplexCategory.Truncated k)ᵒᵖ}
    (f : X ⟶ X) (hf : f ≠ 𝟙 X) :
    (concentratedTruncatedObject A k).map f = 0 := by
  change concentratedTruncatedMap A k f = 0
  unfold concentratedTruncatedMap
  have hcast_zero : ∀ {B : C} (h : B = A) (p : (A ⟶ A) = (B ⟶ B)),
      cast p (0 : A ⟶ A) = 0 := by
    intro B h p
    subst B
    cases p
    rfl
  have hcast_zero_zero : ∀ {B : C} (h : B = 0)
      (p : ((0 : C) ⟶ (0 : C)) = (B ⟶ B)),
      cast p (0 : (0 : C) ⟶ (0 : C)) = 0 := by
    intro B h p
    subst B
    cases p
    rfl
  by_cases hX : X.unop.obj.len = k
  · simp only [dif_pos hX, dif_neg hf]
    exact hcast_zero (B := concentratedTruncatedValue A k X.unop)
      (by simp [concentratedTruncatedValue, hX]) _
  · simp only [dif_neg hX]
    exact hcast_zero_zero (B := concentratedTruncatedValue A k X.unop)
      (by simp [concentratedTruncatedValue, hX]) _

/-! ## Mapping descriptions and the two Kan extensions -/

/- The quantification over every lower simplex map is the generator-free form
   of the source's conditions `dᵏᵢ ≫ f = 0`; it also handles `k = 0` without
   introducing a degree `-1`. -/
def truncatedIncomingCondition
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (A : C) (k : ℕ) (V : SimplicialObject.Truncated C k)
    (f : A ⟶ V.obj (op (topTruncatedSimplex k))) : Prop :=
  ∀ {j : ℕ} (hj : j < k) (φ : ⦋j⦌ ⟶ ⦋k⦌),
    f ≫ V.map (SimplexCategory.Truncated.Hom.tr φ
      (ha := by simpa using Nat.le_of_lt hj) (hb := by simp)).op = 0

/- Dually, this is the generator-free form of the source's conditions
   `f ≫ s⁽ᵏ⁻¹⁾ᵢ = 0`. -/
def truncatedOutgoingCondition
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (A : C) (k : ℕ) (V : SimplicialObject.Truncated C k)
    (f : V.obj (op (topTruncatedSimplex k)) ⟶ A) : Prop :=
  ∀ {j : ℕ} (hj : j < k) (φ : ⦋k⦌ ⟶ ⦋j⦌),
    V.map (SimplexCategory.Truncated.Hom.tr φ
      (ha := by simp) (hb := by simpa using Nat.le_of_lt hj)).op ≫ f = 0

theorem concentratedTruncated_hom_equiv_in
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) (V : SimplicialObject.Truncated C k) :
    Nonempty ((concentratedTruncatedObject A k ⟶ V) ≃
      {f : A ⟶ V.obj (op (topTruncatedSimplex k)) //
        truncatedIncomingCondition A k V f}) := by
  classical
  let U := concentratedTruncatedObject A k
  let T := op (topTruncatedSimplex k)
  have obj_eq_of_len_eq {P Q : (SimplexCategory.Truncated k)ᵒᵖ}
      (h : P.unop.obj.len = Q.unop.obj.len) : P = Q := by
    apply Opposite.unop_injective
    apply ObjectProperty.FullSubcategory.ext
    exact SimplexCategory.ext h
  have U_obj_eq_zero {X : (SimplexCategory.Truncated k)ᵒᵖ} (hX : X ≠ T) :
      U.obj X = 0 := by
    have hlen : X.unop.obj.len ≠ k := by
      intro h
      apply hX
      apply obj_eq_of_len_eq
      simpa [T, topTruncatedSimplex] using h
    simp [U, concentratedTruncatedObject, concentratedTruncatedValue, hlen]
  have U_map_zero_of_src {X Y : (SimplexCategory.Truncated k)ᵒᵖ}
      (hX : X ≠ T) (q : X ⟶ Y) : U.map q = 0 := by
    have hI : IsZero (U.obj X) := by
      simpa only [U_obj_eq_zero hX] using (isZero_zero C)
    exact hI.eq_of_src _ _
  have U_map_zero_of_tgt {X Y : (SimplexCategory.Truncated k)ᵒᵖ}
      (hY : Y ≠ T) (q : X ⟶ Y) : U.map q = 0 := by
    have hI : IsZero (U.obj Y) := by
      simpa only [U_obj_eq_zero hY] using (isZero_zero C)
    exact hI.eq_of_tgt _ _
  have eTop : U.obj T = A := by
    change (concentratedTruncatedObject A k).obj (op (topTruncatedSimplex k)) = A
    exact concentratedTruncatedObject_top A k
  let app (g : A ⟶ V.obj T) (X : (SimplexCategory.Truncated k)ᵒᵖ) :
      U.obj X ⟶ V.obj X :=
    if hX : X = T then
      eqToHom ((congrArg U.obj hX).trans eTop) ≫
        g ≫ eqToHom (congrArg V.obj hX.symm)
    else 0
  have app_top (g : A ⟶ V.obj T) : app g T = eqToHom eTop ≫ g := by
    dsimp [app]
    simp
  have app_zero (g : A ⟶ V.obj T) {X : (SimplexCategory.Truncated k)ᵒᵖ}
      (hX : X ≠ T) : app g X = 0 := by
    simp [app, hX]
  have incoming_any (g : A ⟶ V.obj T)
      (hg : truncatedIncomingCondition A k V g)
      {Y : (SimplexCategory.Truncated k)ᵒᵖ} (hY : Y ≠ T) (q : T ⟶ Y) :
      g ≫ V.map q = 0 := by
    let Z := Y.unop
    let j := Z.obj.len
    have hjle : j ≤ k := Z.property
    have hjlt : j < k := by
      apply lt_of_le_of_ne hjle
      intro h
      apply hY
      apply obj_eq_of_len_eq
      simpa [T, Z, j, topTruncatedSimplex] using h
    let Z' : SimplexCategory.Truncated k :=
      ⟨⦋j⦌, by simpa [j] using hjle⟩
    have e : Z' = Y.unop := by
      apply ObjectProperty.FullSubcategory.ext
      exact SimplexCategory.ext (by simp [Z', Z, j])
    let eop : op Z' = Y := congrArg op e
    let q' : T ⟶ op Z' := q ≫ eqToHom eop.symm
    let φ : ⦋j⦌ ⟶ ⦋k⦌ := q'.unop.hom
    have hq' : q' =
        (SimplexCategory.Truncated.Hom.tr φ
          (ha := by simpa [j] using hjle) (hb := by simp)).op := by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      rfl
    have hq : q = q' ≫ eqToHom eop := by
      dsimp [q']
      simp
    rw [hq, hq', V.map_comp, ← Category.assoc]
    rw [hg hjlt φ]
    simp
  have top_end_zero (g : A ⟶ V.obj T)
      (hg : truncatedIncomingCondition A k V g)
      {q : T ⟶ T} (hq : q ≠ 𝟙 T) : g ≫ V.map q = 0 := by
    cases k with
    | zero =>
        have hi : Function.Injective q.unop.hom.toOrderHom := by
          intro x y hxy
          exact (Fin.eq_zero x).trans (Fin.eq_zero y).symm
        have hmono : Mono q.unop.hom :=
          (SimplexCategory.mono_iff_injective).mpr hi
        have hqbase : q.unop.hom = 𝟙 _ :=
          SimplexCategory.eq_id_of_mono _
        exfalso
        apply hq
        apply Quiver.Hom.unop_inj
        apply ObjectProperty.hom_ext
        exact hqbase
    | succ k =>
        by_cases hs : Function.Surjective q.unop.hom.toOrderHom
        · by_cases hi : Function.Injective q.unop.hom.toOrderHom
          · have hmono : Mono q.unop.hom :=
              (SimplexCategory.mono_iff_injective).mpr hi
            have hqbase : q.unop.hom = 𝟙 _ :=
              SimplexCategory.eq_id_of_mono _
            exfalso
            apply hq
            apply Quiver.Hom.unop_inj
            apply ObjectProperty.hom_ext
            exact hqbase
          · obtain ⟨i, θ, hfac⟩ :=
              SimplexCategory.eq_σ_comp_of_not_injective q.unop.hom hi
            change ⦋k⦌ ⟶ ⦋k + 1⦌ at θ
            let σ' := SimplexCategory.Truncated.Hom.tr (n := k + 1)
              (SimplexCategory.σ i)
                (ha := by simp) (hb := by simp)
            let θ' := SimplexCategory.Truncated.Hom.tr (n := k + 1) θ
                (ha := by simp) (hb := by simp)
            have hfac' : q = θ'.op ≫ σ'.op := by
              apply Quiver.Hom.unop_inj
              apply ObjectProperty.hom_ext
              exact hfac
            rw [hfac', V.map_comp, ← Category.assoc]
            rw [hg (by simp) θ]
            simp
        · obtain ⟨i, θ, hfac⟩ :=
            SimplexCategory.eq_comp_δ_of_not_surjective q.unop.hom hs
          change ⦋k + 1⦌ ⟶ ⦋k⦌ at θ
          dsimp [T, topTruncatedSimplex] at q
          let θ' := SimplexCategory.Truncated.Hom.tr (n := k + 1) θ
              (ha := by simp) (hb := by simp)
          let δ' := SimplexCategory.Truncated.Hom.tr (n := k + 1)
              (SimplexCategory.δ i)
                (ha := by simp) (hb := by simp)
          have hfac' : q = δ'.op ≫ θ'.op := by
            apply Quiver.Hom.unop_inj
            apply ObjectProperty.hom_ext
            exact hfac
          rw [hfac', V.map_comp, ← Category.assoc]
          rw [hg (by simp) (SimplexCategory.δ i)]
          simp
  let nat_of_app (g : A ⟶ V.obj T)
      (hg : truncatedIncomingCondition A k V g) : U ⟶ V :=
    { app := app g
      naturality := by
        intro X Y q
        by_cases hX : X = T
        · subst X
          by_cases hY : Y = T
          · subst Y
            by_cases hq : q = 𝟙 T
            · subst q
              rw [U.map_id, app_top]
              simp
            · rw [concentratedTruncatedObject_map_of_ne_id A k q hq,
                app_top]
              simp only [zero_comp]
              rw [Category.assoc, top_end_zero g hg hq]
              simp
          · rw [U_map_zero_of_tgt hY, app_zero g hY, app_top]
            simp only [zero_comp]
            rw [Category.assoc, incoming_any g hg hY q]
            simp
        · by_cases hY : Y = T
          · rw [U_map_zero_of_src hX, app_zero g hX]
            simp
          · rw [U_map_zero_of_src hX, app_zero g hX,
              app_zero g hY]
            simp }
  have alpha_app_zero (α : U ⟶ V)
      {X : (SimplexCategory.Truncated k)ᵒᵖ} (hX : X ≠ T) : α.app X = 0 := by
    have hI : IsZero (U.obj X) := by
      simpa only [U_obj_eq_zero hX] using (isZero_zero C)
    exact hI.eq_of_src _ _
  refine ⟨{
    toFun := fun α =>
      ⟨eqToHom eTop.symm ≫ α.app T, by
        intro j hj φ
        let q := (SimplexCategory.Truncated.Hom.tr φ
          (ha := by simpa using Nat.le_of_lt hj) (hb := by simp)).op
        have hq : T ≠ op (⟨⦋j⦌, by simpa using Nat.le_of_lt hj⟩ :
            SimplexCategory.Truncated k) := by
          intro h
          apply Nat.ne_of_lt hj
          have := congrArg (fun Z => Z.unop.obj.len) h
          simpa [T, topTruncatedSimplex] using this.symm
        have hnat := α.naturality q
        have hq' : op (⟨⦋j⦌, by simpa using Nat.le_of_lt hj⟩ :
            SimplexCategory.Truncated k) ≠ T := hq.symm
        rw [U_map_zero_of_tgt hq'] at hnat
        simpa [q, Category.assoc] using
          congrArg (fun z => eqToHom eTop.symm ≫ z) hnat.symm⟩
    invFun := fun f => nat_of_app f.1 f.2
    left_inv := by
      intro α
      apply NatTrans.ext
      funext X
      dsimp [nat_of_app]
      change app (eqToHom eTop.symm ≫ α.app T) X = α.app X
      by_cases hX : X = T
      · subst X
        rw [app_top]
        simp
      · rw [app_zero _ hX, alpha_app_zero α hX]
    right_inv := by
      intro f
      apply Subtype.ext
      dsimp [nat_of_app]
      change eqToHom eTop.symm ≫ app f.1 T = f.1
      rw [app_top]
      simp }⟩

theorem concentratedTruncated_hom_equiv_out
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) (V : SimplicialObject.Truncated C k) :
    Nonempty ((V ⟶ concentratedTruncatedObject A k) ≃
      {f : V.obj (op (topTruncatedSimplex k)) ⟶ A //
        truncatedOutgoingCondition A k V f}) := by
  classical
  let U := concentratedTruncatedObject A k
  let T := op (topTruncatedSimplex k)
  have obj_eq_of_len_eq {P Q : (SimplexCategory.Truncated k)ᵒᵖ}
      (h : P.unop.obj.len = Q.unop.obj.len) : P = Q := by
    apply Opposite.unop_injective
    apply ObjectProperty.FullSubcategory.ext
    exact SimplexCategory.ext h
  have U_obj_eq_zero {X : (SimplexCategory.Truncated k)ᵒᵖ} (hX : X ≠ T) :
      U.obj X = 0 := by
    have hlen : X.unop.obj.len ≠ k := by
      intro h
      apply hX
      apply obj_eq_of_len_eq
      simpa [T, topTruncatedSimplex] using h
    simp [U, concentratedTruncatedObject, concentratedTruncatedValue, hlen]
  have U_map_zero_of_src {X Y : (SimplexCategory.Truncated k)ᵒᵖ}
      (hX : X ≠ T) (q : X ⟶ Y) : U.map q = 0 := by
    have hI : IsZero (U.obj X) := by
      simpa only [U_obj_eq_zero hX] using (isZero_zero C)
    exact hI.eq_of_src _ _
  have U_map_zero_of_tgt {X Y : (SimplexCategory.Truncated k)ᵒᵖ}
      (hY : Y ≠ T) (q : X ⟶ Y) : U.map q = 0 := by
    have hI : IsZero (U.obj Y) := by
      simpa only [U_obj_eq_zero hY] using (isZero_zero C)
    exact hI.eq_of_tgt _ _
  have eTop : U.obj T = A := by
    change (concentratedTruncatedObject A k).obj (op (topTruncatedSimplex k)) = A
    exact concentratedTruncatedObject_top A k
  let app (g : V.obj T ⟶ A) (X : (SimplexCategory.Truncated k)ᵒᵖ) :
      V.obj X ⟶ U.obj X :=
    if hX : X = T then
      eqToHom (congrArg V.obj hX) ≫ g ≫
        eqToHom ((congrArg U.obj hX).trans eTop).symm
    else 0
  have app_top (g : V.obj T ⟶ A) :
      app g T = g ≫ eqToHom eTop.symm := by
    dsimp [app]
    simp
  have app_zero (g : V.obj T ⟶ A) {X : (SimplexCategory.Truncated k)ᵒᵖ}
      (hX : X ≠ T) : app g X = 0 := by
    simp [app, hX]
  have outgoing_any (g : V.obj T ⟶ A)
      (hg : truncatedOutgoingCondition A k V g)
      {X : (SimplexCategory.Truncated k)ᵒᵖ} (hX : X ≠ T) (q : X ⟶ T) :
      V.map q ≫ g = 0 := by
    let Z := X.unop
    let j := Z.obj.len
    have hjle : j ≤ k := Z.property
    have hjlt : j < k := by
      apply lt_of_le_of_ne hjle
      intro h
      apply hX
      apply obj_eq_of_len_eq
      simpa [T, Z, j, topTruncatedSimplex] using h
    let Z' : SimplexCategory.Truncated k :=
      ⟨⦋j⦌, by simpa [j] using hjle⟩
    have e : Z' = X.unop := by
      apply ObjectProperty.FullSubcategory.ext
      exact SimplexCategory.ext (by simp [Z', Z, j])
    let eop : op Z' = X := congrArg op e
    let q' : op Z' ⟶ T := eqToHom eop.symm ≫ q
    let φ : ⦋k⦌ ⟶ ⦋j⦌ := q'.unop.hom
    have hq' : q' =
        (SimplexCategory.Truncated.Hom.tr φ
          (ha := by simp) (hb := by simpa [j] using hjle)).op := by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      rfl
    have hq : q = eqToHom eop ≫ q' := by
      dsimp [q']
      simp
    rw [hq, V.map_comp, Category.assoc, hq']
    rw [hg hjlt φ]
    simp
  have top_end_zero (g : V.obj T ⟶ A)
      (hg : truncatedOutgoingCondition A k V g)
      {q : T ⟶ T} (hq : q ≠ 𝟙 T) : V.map q ≫ g = 0 := by
    cases k with
    | zero =>
        have hi : Function.Injective q.unop.hom.toOrderHom := by
          intro x y hxy
          exact (Fin.eq_zero x).trans (Fin.eq_zero y).symm
        have hmono : Mono q.unop.hom :=
          (SimplexCategory.mono_iff_injective).mpr hi
        have hqbase : q.unop.hom = 𝟙 _ :=
          SimplexCategory.eq_id_of_mono _
        exfalso
        apply hq
        apply Quiver.Hom.unop_inj
        apply ObjectProperty.hom_ext
        exact hqbase
    | succ k =>
        by_cases hs : Function.Surjective q.unop.hom.toOrderHom
        · by_cases hi : Function.Injective q.unop.hom.toOrderHom
          · have hmono : Mono q.unop.hom :=
              (SimplexCategory.mono_iff_injective).mpr hi
            have hqbase : q.unop.hom = 𝟙 _ :=
              SimplexCategory.eq_id_of_mono _
            exfalso
            apply hq
            apply Quiver.Hom.unop_inj
            apply ObjectProperty.hom_ext
            exact hqbase
          · obtain ⟨i, θ, hfac⟩ :=
              SimplexCategory.eq_σ_comp_of_not_injective q.unop.hom hi
            change ⦋k⦌ ⟶ ⦋k + 1⦌ at θ
            let σ' := SimplexCategory.Truncated.Hom.tr (n := k + 1)
              (SimplexCategory.σ i) (ha := by simp) (hb := by simp)
            let θ' := SimplexCategory.Truncated.Hom.tr (n := k + 1) θ
              (ha := by simp) (hb := by simp)
            have hfac' : q = θ'.op ≫ σ'.op := by
              apply Quiver.Hom.unop_inj
              apply ObjectProperty.hom_ext
              exact hfac
            rw [hfac', V.map_comp, Category.assoc]
            rw [hg (by simp) (SimplexCategory.σ i)]
            simp
        · obtain ⟨i, θ, hfac⟩ :=
            SimplexCategory.eq_comp_δ_of_not_surjective q.unop.hom hs
          change ⦋k + 1⦌ ⟶ ⦋k⦌ at θ
          dsimp [T, topTruncatedSimplex] at q
          let θ' := SimplexCategory.Truncated.Hom.tr (n := k + 1) θ
            (ha := by simp) (hb := by simp)
          let δ' := SimplexCategory.Truncated.Hom.tr (n := k + 1)
            (SimplexCategory.δ i) (ha := by simp) (hb := by simp)
          have hfac' : q = δ'.op ≫ θ'.op := by
            apply Quiver.Hom.unop_inj
            apply ObjectProperty.hom_ext
            exact hfac
          rw [hfac', V.map_comp, Category.assoc]
          rw [hg (by simp) θ]
          simp
  let nat_of_app (g : V.obj T ⟶ A)
      (hg : truncatedOutgoingCondition A k V g) : V ⟶ U :=
    { app := app g
      naturality := by
        intro X Y q
        by_cases hX : X = T
        · subst X
          by_cases hY : Y = T
          · subst Y
            by_cases hq : q = 𝟙 T
            · subst q
              rw [V.map_id, app_top, U.map_id]
              simp
            · rw [app_top, concentratedTruncatedObject_map_of_ne_id A k q hq]
              simp only [comp_zero]
              rw [← Category.assoc, top_end_zero g hg hq]
              simp
          · rw [app_zero g hY, U_map_zero_of_tgt hY]
            simp
        · by_cases hY : Y = T
          · subst Y
            rw [app_zero g hX, app_top]
            simp only [zero_comp]
            rw [← Category.assoc, outgoing_any g hg hX q]
            simp
          · rw [app_zero g hX, app_zero g hY]
            simp }
  have alpha_app_zero (α : V ⟶ U)
      {X : (SimplexCategory.Truncated k)ᵒᵖ} (hX : X ≠ T) : α.app X = 0 := by
    have hI : IsZero (U.obj X) := by
      simpa only [U_obj_eq_zero hX] using (isZero_zero C)
    exact hI.eq_of_tgt _ _
  refine ⟨{
    toFun := fun α =>
      ⟨α.app T ≫ eqToHom eTop, by
        intro j hj φ
        let q := (SimplexCategory.Truncated.Hom.tr (n := k) φ
          (ha := by simp) (hb := by simpa using Nat.le_of_lt hj)).op
        have hq : op (⟨⦋j⦌, by simpa using Nat.le_of_lt hj⟩ :
            SimplexCategory.Truncated k) ≠ T := by
          intro h
          apply Nat.ne_of_lt hj
          have hlen := congrArg (fun Z => Z.unop.obj.len) h
          simpa [T, topTruncatedSimplex] using hlen
        have hαzero : α.app (op (⟨⦋j⦌, by simpa using Nat.le_of_lt hj⟩ :
            SimplexCategory.Truncated k)) = 0 := alpha_app_zero α hq
        have hnat := α.naturality q
        have hnat' : V.map q ≫ α.app T = 0 := by
          simpa only [hαzero, zero_comp] using hnat
        dsimp [q] at hnat'
        simpa only [Category.assoc, zero_comp] using
          congrArg (fun z => z ≫ eqToHom eTop) hnat'⟩
    invFun := fun f => nat_of_app f.1 f.2
    left_inv := by
      intro α
      apply NatTrans.ext
      funext X
      dsimp [nat_of_app]
      change app (α.app T ≫ eqToHom eTop) X = α.app X
      by_cases hX : X = T
      · subst X
        rw [app_top]
        simp
      · rw [app_zero _ hX, alpha_app_zero α hX]
    right_inv := by
      intro f
      apply Subtype.ext
      dsimp [nat_of_app]
      change app f.1 T ≫ eqToHom eTop = f.1
      rw [app_top]
      simp }⟩

noncomputable def truncatedCoskeletonObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) : SimplicialObject C :=
  let U := concentratedTruncatedObject A k
  letI : Unit19.HasCoskeleton k U :=
    Unit19.has_coskeleton_of_has_finite_limits k U
  Unit19.coskeleton k U

noncomputable def eilenbergMacLaneObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) : SimplicialObject C :=
  (Unit21.leftAdjoint (C := C) k).obj (concentratedTruncatedObject A k)

/-! ## Finite index sets and the direct-sum formulas -/

abbrev SurjectiveSimplexIndex (n k : ℕ) :=
  {α : ⦋n⦌ ⟶ ⦋k⦌ // Epi α}

noncomputable instance surjectiveSimplexIndexFintype (n k : ℕ) :
    Fintype (SurjectiveSimplexIndex n k) := Fintype.ofFinite _

abbrev InjectiveSimplexIndex (k n : ℕ) :=
  {β : ⦋k⦌ ⟶ ⦋n⦌ // Mono β}

noncomputable instance injectiveSimplexIndexFintype (k n : ℕ) :
    Fintype (InjectiveSimplexIndex k n) := Fintype.ofFinite _

noncomputable abbrev eilenbergMacLaneDegreeDirectSum
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (A : C) (k n : ℕ) :=
  ∐ fun _ : SurjectiveSimplexIndex n k => A

noncomputable abbrev coskeletonDegreeDirectSum
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (A : C) (k n : ℕ) :=
  ∐ fun _ : InjectiveSimplexIndex k n => A

noncomputable def surjectiveDirectSumMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    eilenbergMacLaneDegreeDirectSum A k n ⟶
    eilenbergMacLaneDegreeDirectSum A k m :=
  by
    classical
    exact
      (biproduct.isoCoproduct (fun _ : SurjectiveSimplexIndex n k => A)).inv ≫
        biproduct.matrix (fun α α' =>
          if h : Epi (φ ≫ α.1) then
            if α' = (⟨φ ≫ α.1, h⟩ : SurjectiveSimplexIndex m k) then 𝟙 A else 0
          else 0) ≫
        (biproduct.isoCoproduct (fun _ : SurjectiveSimplexIndex m k => A)).hom

noncomputable def injectiveDirectSumMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    coskeletonDegreeDirectSum A k n ⟶ coskeletonDegreeDirectSum A k m :=
  by
    classical
    exact
      (biproduct.isoCoproduct (fun _ : InjectiveSimplexIndex k n => A)).inv ≫
        biproduct.matrix (fun β β' =>
          if β.1 = β'.1 ≫ φ then 𝟙 A else 0) ≫
        (biproduct.isoCoproduct (fun _ : InjectiveSimplexIndex k m => A)).hom

noncomputable def canonicalCoefficientMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k n : ℕ) :
    eilenbergMacLaneDegreeDirectSum A k n ⟶ coskeletonDegreeDirectSum A k n :=
  by
    classical
    exact
      (biproduct.isoCoproduct (fun _ : SurjectiveSimplexIndex n k => A)).inv ≫
        biproduct.matrix (fun α β =>
          if β.1 ≫ α.1 = 𝟙 _ then 𝟙 A else 0) ≫
        (biproduct.isoCoproduct (fun _ : InjectiveSimplexIndex k n => A)).hom

theorem eilenbergMacLane_degree_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k n : ℕ) :
    Nonempty ((eilenbergMacLaneObject A k).obj (op ⦋n⦌) ≅
      eilenbergMacLaneDegreeDirectSum A k n) := by
  classical
  let U : SimplicialObject.Truncated C k := concentratedTruncatedObject A k
  let I := Unit21.leftSkeletonIndex k n
  let D := Unit21.leftSkeletonDiagram k n U
  let E : C := ∐ (fun _ : SurjectiveSimplexIndex n k => A)
  have eTop : U.obj (op (topTruncatedSimplex k)) = A := by
    change (concentratedTruncatedObject A k).obj (op (topTruncatedSimplex k)) = A
    exact concentratedTruncatedObject_top A k
  have topObjEq {X : I} (hX : X.left = op (topTruncatedSimplex k)) :
      X.left.unop = topTruncatedSimplex k := by
    simpa using congrArg Opposite.unop hX
  let topMap : ∀ {X : I}, X.left = op (topTruncatedSimplex k) →
      (⦋n⦌ ⟶ ⦋k⦌) := fun {X} hX => by
    exact X.hom.unop ≫
      eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
        (topObjEq hX))
  have topObjValueEq {X : I} (hX : X.left = op (topTruncatedSimplex k)) :
      D.obj X = A := by
    have hx : X.left.unop.obj.len = k := by
      rw [topObjEq hX]
    change U.obj X.left = A
    simp [U, concentratedTruncatedObject, concentratedTruncatedValue, hx]
  let leg : ∀ X : I, D.obj X ⟶ E := fun X => by
    by_cases hX : X.left = op (topTruncatedSimplex k)
    · by_cases hα : Epi (topMap hX)
      · let α : SurjectiveSimplexIndex n k := ⟨topMap hX, hα⟩
        exact eqToHom (topObjValueEq hX) ≫
          Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) α
      · exact 0
    · exact 0
  have map_zero_of_nontrivial {X Y : I} (f : X ⟶ Y)
      (hXY : X.left = Y.left) (hf : f.left ≠ eqToHom hXY) : D.map f = 0 := by
    let q := eqToHom hXY.symm ≫ f.left
    have hq : q ≠ 𝟙 Y.left := by
      intro hq
      apply hf
      calc
        f.left = 𝟙 _ ≫ f.left := by simp
        _ = (eqToHom hXY ≫ eqToHom hXY.symm) ≫ f.left := by simp
        _ = eqToHom hXY ≫ q := by simp [q]
        _ = eqToHom hXY ≫ 𝟙 _ := by rw [hq]
        _ = _ := by simp
    change U.map f.left = 0
    have hfac : f.left = eqToHom hXY ≫ q := by simp [q]
    rw [hfac, U.map_comp, concentratedTruncatedObject_map_of_ne_id A k q hq]
    simp
  let c : Cocone D := Cocone.mk E
    { app := fun X => leg X
      naturality := by
        intro X Y f
        by_cases hX : X.left = op (topTruncatedSimplex k)
        · by_cases hY : Y.left = op (topTruncatedSimplex k)
          · have hrel :
                topMap hX =
                  topMap hY ≫
                    (eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                      (topObjEq (X := Y) hY)).symm ≫
                     f.left.unop.hom ≫
                     eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                      (topObjEq (X := X) hX))) := by
              have hbase : Y.hom.unop ≫ f.left.unop.hom = X.hom.unop := by
                simpa using congrArg Quiver.Hom.unop f.w
              simpa [topMap, Category.assoc] using
                congrArg (fun z => z ≫
                  eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                    (topObjEq (X := X) hX))) hbase.symm
            by_cases hαX : Epi (topMap hX)
            · let q : ⦋k⦌ ⟶ ⦋k⦌ :=
                eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                  (topObjEq (X := Y) hY)).symm ≫
                f.left.unop.hom ≫
                eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                  (topObjEq (X := X) hX))
              have hq : Epi q := by
                let : Epi (topMap hX) := hαX
                have hfac : topMap hY ≫ q = topMap hX := by
                  simpa [q] using hrel.symm
                exact epi_of_epi_fac hfac
              have hqid : q = 𝟙 _ := SimplexCategory.eq_id_of_epi q
              have hXY : X.left = Y.left := hX.trans hY.symm
              have hflbase :
                  f.left.unop.hom =
                    eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                      (topObjEq (X := Y) hY)) ≫
                    eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                      (topObjEq (X := X) hX)).symm := by
                calc
                  f.left.unop.hom =
                      𝟙 _ ≫ f.left.unop.hom ≫ 𝟙 _ := by simp
                  _ = (eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                        (topObjEq (X := Y) hY)) ≫
                        eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                          (topObjEq (X := Y) hY)).symm) ≫
                        f.left.unop.hom ≫
                        (eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                          (topObjEq (X := X) hX)) ≫
                        eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                          (topObjEq (X := X) hX)).symm) := by simp
                  _ = eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                        (topObjEq (X := Y) hY)) ≫ q ≫
                        eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                          (topObjEq (X := X) hX)).symm := by simp [q, Category.assoc]
                  _ = eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                        (topObjEq (X := Y) hY)) ≫ 𝟙 _ ≫
                        eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                          (topObjEq (X := X) hX)).symm := by rw [hqid]
                  _ = _ := by simp
              have hfl : f.left = eqToHom hXY := by
                apply Quiver.Hom.unop_inj
                apply ObjectProperty.hom_ext
                simpa using hflbase
              have hobj : X = Y := by
                apply CostructuredArrow.obj_ext X Y hXY
                simpa [hfl] using f.w
              subst Y
              have hf : f = 𝟙 X := by
                apply CostructuredArrow.ext
                simpa using hfl
              subst f
              simp [leg, hX]
            · by_cases hαY : Epi (topMap hY)
              · have hfl_ne : f.left ≠ eqToHom (by
                    exact hX.trans hY.symm) := by
                  intro hfl
                  have heq : topMap hX = topMap hY := by
                    simpa [hfl] using hrel
                  apply hαX
                  simpa [heq] using hαY
                have hzero := map_zero_of_nontrivial f
                  (hX.trans hY.symm) hfl_ne
                simp [leg, hX, hY, hαX, hαY, hzero]
              · simp [leg, hX, hY, hαX, hαY]
          · by_cases hαX : Epi (topMap hX)
            · have hbase : Y.hom.unop ≫ f.left.unop.hom = X.hom.unop := by
                simpa using congrArg Quiver.Hom.unop f.w
              let q := f.left.unop.hom ≫
                eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                  (topObjEq (X := X) hX))
              have hfac : Y.hom.unop ≫ q = topMap hX := by
                dsimp [q]
                simpa [topMap, Category.assoc] using
                  congrArg (fun z => z ≫
                    eqToHom (congrArg (fun Z : SimplexCategory.Truncated k => Z.obj)
                      (topObjEq (X := X) hX))) hbase
              let : Epi (topMap hX) := hαX
              have hq : Epi q := epi_of_epi_fac hfac
              have hle : k ≤ Y.left.unop.obj.len := SimplexCategory.le_of_epi q
              have hlt : Y.left.unop.obj.len < k := by
                apply lt_of_le_of_ne Y.left.unop.property
                intro hlen
                apply hY
                apply Opposite.unop_injective
                apply ObjectProperty.FullSubcategory.ext
                exact SimplexCategory.ext hlen
              exact (Nat.not_lt_of_ge hle hlt).elim
            · simp [leg, hX, hY, hαX]
        · by_cases hY : Y.left = op (topTruncatedSimplex k)
          · have hI : IsZero (D.obj X) := by
              change IsZero (U.obj X.left)
              have hlen : X.left.unop.obj.len ≠ k := by
                intro hlen
                apply hX
                apply Opposite.unop_injective
                apply ObjectProperty.FullSubcategory.ext
                exact SimplexCategory.ext hlen
              simpa [U, concentratedTruncatedObject, concentratedTruncatedValue, hlen] using
                (isZero_zero C)
            exact hI.eq_of_src _ _
          · simp [leg, hX, hY, U, D]
    }
  have cocone_ι_zero {s : Cocone D} {X : I}
      (hX : X.left = op (topTruncatedSimplex k))
      (hα : ¬Epi (topMap hX)) : s.ι.app X = 0 := by
    cases k with
    | zero =>
        exfalso
        apply hα
        rw [SimplexCategory.epi_iff_surjective]
        intro y
        exact ⟨0, (Fin.eq_zero _).trans (Fin.eq_zero _).symm⟩
    | succ k =>
        have hns : ¬Function.Surjective (topMap hX).toOrderHom := by
          intro hs
          apply hα
          exact SimplexCategory.epi_iff_surjective.mpr hs
        obtain ⟨i, θ, hfac⟩ :=
          SimplexCategory.eq_comp_δ_of_not_surjective (topMap hX) hns
        let δ' := SimplexCategory.Truncated.Hom.tr (n := k + 1)
          (SimplexCategory.δ i) (ha := by simp) (hb := by simp)
        let Yleft : (SimplexCategory.Truncated (k + 1))ᵒᵖ :=
          op ⟨⦋k⦌, by simp⟩
        let Yhom : (Unit21.leftSkeletonInclusion (k + 1)).obj Yleft ⟶ op ⦋n⦌ := by
          exact eqToHom (by rfl) ≫ θ.op
        let Y : I := CostructuredArrow.mk Yhom
        let q : X.left ⟶ Y.left := eqToHom hX ≫ δ'.op
        let f : X ⟶ Y := CostructuredArrow.homMk q (by
          apply Quiver.Hom.unop_inj
          dsimp [q, Y, Yhom, Yleft, δ']
          have htop : X.hom.unop ≫
              eqToHom (congrArg (fun Z : SimplexCategory.Truncated (k + 1) => Z.obj)
                (topObjEq hX)) = θ ≫ SimplexCategory.δ i := by
            simpa [topMap] using hfac
          have hbase : θ ≫ SimplexCategory.δ i ≫
              eqToHom (congrArg (fun Z : SimplexCategory.Truncated (k + 1) => Z.obj)
                (topObjEq hX)).symm = X.hom.unop := by
            rw [← Category.assoc, ← htop]
            simp
          simpa [Category.assoc] using hbase)
        have hzero : D.map f = 0 := by
          have hI : IsZero (D.obj Y) := by
            change IsZero (U.obj Y.left)
            simpa [Y, Yleft, U, concentratedTruncatedObject, concentratedTruncatedValue] using
              (isZero_zero C)
          exact hI.eq_of_tgt _ _
        have hnat := s.ι.naturality f
        simpa [hzero] using hnat.symm
  have hc : IsColimit c := by
    let Xα (α : SurjectiveSimplexIndex n k) : I := by
      let a : (SimplexCategory.Truncated k)ᵒᵖ := op (topTruncatedSimplex k)
      let h : (Unit21.leftSkeletonInclusion k).obj a ⟶ op ⦋n⦌ := by
        exact eqToHom (by rfl) ≫ α.1.op
      exact CostructuredArrow.mk h
    let desc (s : Cocone D) : E ⟶ s.pt :=
      (coproductIsCoproduct (fun _ : SurjectiveSimplexIndex n k => A)).desc
        (Cocone.mk s.pt
          { app := fun α =>
              eqToHom (topObjValueEq (X := Xα α.as) (by simp [Xα])).symm ≫
                s.ι.app (Xα α.as)
            naturality := by
              intro α β f
              cases α with
              | mk a =>
                cases β with
                | mk b =>
                  have hab : a = b := Discrete.eq_of_hom f
                  subst b
                  simp })
    let fac : ∀ (s : Cocone D) (X : I), leg X ≫ desc s = s.ι.app X := by
      intro s X
      by_cases hX : X.left = op (topTruncatedSimplex k)
      · by_cases hαX : Epi (topMap hX)
        · let α : SurjectiveSimplexIndex n k := ⟨topMap hX, hαX⟩
          have hXZ : X = Xα α := by
            have hleft : X.left = (Xα α).left := by
              simpa [Xα] using hX
            apply CostructuredArrow.obj_ext X (Xα α) hleft
            apply Quiver.Hom.unop_inj
            dsimp [Xα, α, topMap]
            simp [Category.assoc]
          rw [hXZ]
          have hleft : (Xα α).left = op (topTruncatedSimplex k) := by
            simp [Xα]
          have hmap : topMap hleft = α.1 := by
            simp [topMap, Xα, α]
          have hα' : Epi (topMap hleft) := by
            rw [hmap]
            exact α.2
          have hleg : leg (Xα α) =
              eqToHom (topObjValueEq hleft) ≫
                Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) α := by
            dsimp [leg]
            rw [dif_pos hleft, dif_pos hα']
            simp [hmap]
          change leg (Xα α) ≫ desc s = s.ι.app (Xα α)
          rw [hleg]
          have hdesc :
              Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) α ≫ desc s =
                eqToHom (topObjValueEq hleft).symm ≫ s.ι.app (Xα α) := by
            simpa [desc, Xα, α] using
              (coproductIsCoproduct (fun _ : SurjectiveSimplexIndex n k => A)).fac
                (Cocone.mk s.pt
                  { app := fun β =>
                      eqToHom (topObjValueEq (X := Xα β.as) (by simp [Xα])).symm ≫
                        s.ι.app (Xα β.as)
                    naturality := by
                      intro β γ f
                      cases β with
                      | mk b =>
                        cases γ with
                        | mk c =>
                          have hbc : b = c := Discrete.eq_of_hom f
                          subst c
                          simp }) ⟨α⟩
          rw [Category.assoc, hdesc]
          simp
        · have hs := cocone_ι_zero (s := s) hX hαX
          simp [leg, desc, hX, hαX, hs]
      · have hI : IsZero (D.obj X) := by
          change IsZero (U.obj X.left)
          have hlen : X.left.unop.obj.len ≠ k := by
            intro hlen
            apply hX
            apply Opposite.unop_injective
            apply ObjectProperty.FullSubcategory.ext
            exact SimplexCategory.ext hlen
          simpa [U, concentratedTruncatedObject, concentratedTruncatedValue, hlen] using
            (isZero_zero C)
        exact hI.eq_of_src _ _
    let uniq : ∀ (s : Cocone D) (m : E ⟶ s.pt),
        (∀ X, leg X ≫ m = s.ι.app X) → m = desc s := by
      intro s m hm
      apply (coproductIsCoproduct (fun _ : SurjectiveSimplexIndex n k => A)).hom_ext
      intro α
      let a : SurjectiveSimplexIndex n k := α.as
      let Xa : I := Xα a
      have hleft : Xa.left = op (topTruncatedSimplex k) := by
        simp [Xa, Xα]
      have hmap : topMap hleft = a.1 := by
        simp [topMap, Xa, Xα, a]
      have hα : Epi (topMap hleft) := by
        rw [hmap]
        exact a.2
      have hleg : leg Xa =
          eqToHom (topObjValueEq hleft) ≫
            Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) a := by
        dsimp [leg]
        rw [dif_pos hleft, dif_pos hα]
        simp [hmap]
      have hm' := hm Xa
      change leg Xa ≫ m = s.ι.app Xa at hm'
      rw [hleg] at hm'
      have hdesc :
          Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) a ≫ desc s =
            eqToHom (topObjValueEq hleft).symm ≫ s.ι.app Xa := by
        simpa [desc, Xa, Xα, a] using
          (coproductIsCoproduct (fun _ : SurjectiveSimplexIndex n k => A)).fac
            (Cocone.mk s.pt
              { app := fun β =>
                  eqToHom (topObjValueEq (X := Xα β.as) (by simp [Xα])).symm ≫
                    s.ι.app (Xα β.as)
                naturality := by
                  intro β γ f
                  cases β with
                  | mk b =>
                    cases γ with
                    | mk c =>
                      have hbc : b = c := Discrete.eq_of_hom f
                      subst c
                      simp }) ⟨a⟩
      change Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) a ≫ m =
        Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) a ≫ desc s
      rw [hdesc]
      have hm_reassoc :
          eqToHom (topObjValueEq hleft) ≫
              Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) a ≫ m =
            s.ι.app Xa := by
        simpa [Category.assoc] using hm'
      calc
        Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) a ≫ m =
            𝟙 _ ≫ Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) a ≫ m := by simp
        _ = (eqToHom (topObjValueEq hleft).symm ≫
              eqToHom (topObjValueEq hleft)) ≫
            Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) a ≫ m := by simp
        _ = eqToHom (topObjValueEq hleft).symm ≫
            (eqToHom (topObjValueEq hleft) ≫
              Sigma.ι (fun _ : SurjectiveSimplexIndex n k => A) a ≫ m) := by
              simp
        _ = eqToHom (topObjValueEq hleft).symm ≫ s.ι.app Xa := by
          rw [hm_reassoc]
    exact { desc := desc, fac := fac, uniq := uniq }
  let hD := Unit21.has_left_skeleton_colimit_of_has_finite_colimits k n U
  let := hD
  let eColim : E ≅ Unit21.leftSkeletonColimit k n U hD :=
    hc.coconePointUniqueUpToIso (colimit.isColimit D)
  let eKan :=
    (Unit21.leftAdjoint_obj_iso_colimit k n U hD).some
  exact ⟨eKan ≪≫ eColim.symm⟩

theorem eilenbergMacLane_map_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    ∃ (e_m : (eilenbergMacLaneObject A k).obj (op ⦋m⦌) ≅
        eilenbergMacLaneDegreeDirectSum A k m)
      (e_n : (eilenbergMacLaneObject A k).obj (op ⦋n⦌) ≅
        eilenbergMacLaneDegreeDirectSum A k n),
      e_n.hom ≫ surjectiveDirectSumMap A k m n φ =
        (eilenbergMacLaneObject A k).map φ.op ≫ e_m.hom := by
  sorry

theorem coskeleton_degree_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k n : ℕ) :
    Nonempty ((truncatedCoskeletonObject A k).obj (op ⦋n⦌) ≅
      coskeletonDegreeDirectSum A k n) := by
  sorry

theorem coskeleton_map_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    ∃ (e_m : (truncatedCoskeletonObject A k).obj (op ⦋m⦌) ≅
        coskeletonDegreeDirectSum A k m)
      (e_n : (truncatedCoskeletonObject A k).obj (op ⦋n⦌) ≅
        coskeletonDegreeDirectSum A k n),
      e_n.hom ≫ injectiveDirectSumMap A k m n φ =
        (truncatedCoskeletonObject A k).map φ.op ≫ e_m.hom := by
  sorry

noncomputable def canonicalEilenbergMacLaneMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    eilenbergMacLaneObject A k ⟶ truncatedCoskeletonObject A k := by
  let U := concentratedTruncatedObject A k
  letI : Unit19.HasCoskeleton k U :=
    Unit19.has_coskeleton_of_has_finite_limits k U
  have hIso : IsIso (Unit19.coskeletonCounit k U) :=
    Unit19.recover_coskeleton k U
  letI := hIso
  let V := Unit19.coskeleton k U
  change (Unit21.leftAdjoint (C := C) k).obj U ⟶ V
  refine (Unit21.leftAdjointHomEquiv k U V).symm ?_
  exact @inv _ _ _ _ (Unit19.coskeletonCounit k U) hIso

theorem canonical_map_degree_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k n : ℕ) :
    ∃ (eₗ : (eilenbergMacLaneObject A k).obj (op ⦋n⦌) ≅
        eilenbergMacLaneDegreeDirectSum A k n)
      (eᵣ : (truncatedCoskeletonObject A k).obj (op ⦋n⦌) ≅
        coskeletonDegreeDirectSum A k n),
      eₗ.inv ≫ (canonicalEilenbergMacLaneMap A k).app (op ⦋n⦌) ≫ eᵣ.hom =
        canonicalCoefficientMap A k n := by
  sorry

theorem canonical_map_mono
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    Mono (canonicalEilenbergMacLaneMap A k) := by
  sorry

/-! ## Eilenberg--Mac Lane objects -/

noncomputable def eilenbergMacLane
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) : SimplicialObject C :=
  eilenbergMacLaneObject A k

theorem eilenbergMacLane_is_left_skeleton
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    eilenbergMacLane A k = eilenbergMacLaneObject A k := rfl

/-! ## The extension between consecutive Eilenberg--Mac Lane objects -/

/- The source's phrase “image `[k]`” is taken to mean the standard initial
   face, represented by `δ_{k+1}`; this is the index-set inclusion needed for
   the displayed short exact sequence. -/
def extensionImageProperty {k n : ℕ} (α : ⦋n⦌ ⟶ ⦋k + 1⦌) : Prop :=
  Epi α ∨ ∃ (e : ⦋n⦌ ⟶ ⦋k⦌),
    Epi e ∧ e ≫ SimplexCategory.δ (Fin.last (k + 1)) = α

abbrev ExtensionSimplexIndex (n k : ℕ) :=
  {α : ⦋n⦌ ⟶ ⦋k + 1⦌ // extensionImageProperty α}

noncomputable instance extensionSimplexIndexFintype (n k : ℕ) :
    Fintype (ExtensionSimplexIndex n k) := Fintype.ofFinite _

noncomputable abbrev extensionDegreeDirectSum
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (A : C) (k n : ℕ) :=
  ∐ fun _ : ExtensionSimplexIndex n k => A

noncomputable def extensionDirectSumMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    extensionDegreeDirectSum A k n ⟶ extensionDegreeDirectSum A k m :=
  by
    classical
    exact
      (biproduct.isoCoproduct (fun _ : ExtensionSimplexIndex n k => A)).inv ≫
        biproduct.matrix (fun α α' =>
          if h : extensionImageProperty (φ ≫ α.1) then
            if α' = (⟨φ ≫ α.1, h⟩ : ExtensionSimplexIndex m k) then 𝟙 A else 0
          else 0) ≫
        (biproduct.isoCoproduct (fun _ : ExtensionSimplexIndex m k => A)).hom

noncomputable def extensionObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) : SimplicialObject C :=
  eilenbergMacLaneObject A k ⊞ eilenbergMacLaneObject A (k + 1)

theorem extension_degree_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k n : ℕ) :
    Nonempty ((extensionObject A k).obj (op ⦋n⦌) ≅
      extensionDegreeDirectSum A k n) := by
  sorry

theorem extension_map_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    ∃ (e_m : (extensionObject A k).obj (op ⦋m⦌) ≅
        extensionDegreeDirectSum A k m)
      (e_n : (extensionObject A k).obj (op ⦋n⦌) ≅
        extensionDegreeDirectSum A k n),
      e_n.hom ≫ extensionDirectSumMap A k m n φ =
        (extensionObject A k).map φ.op ≫ e_m.hom := by
  sorry

noncomputable def extensionInclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    eilenbergMacLaneObject A k ⟶ extensionObject A k :=
  biprod.inl

noncomputable def extensionProjection
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    extensionObject A k ⟶ eilenbergMacLaneObject A (k + 1) :=
  biprod.snd

noncomputable def extensionShortComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) : ShortComplex (SimplicialObject C) :=
  ShortComplex.mk (extensionInclusion A k) (extensionProjection A k)
    (biprod.inl_snd)

theorem extension_short_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    (extensionShortComplex A k).ShortExact := by
  sorry

theorem extension_termwise_split_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    let S := simplicialEvaluationShortComplex
      (S := extensionShortComplex A k) n
    S.ShortExact ∧ IsSplitMono S.f ∧ IsSplitEpi S.g := by
  sorry

/-! ## The colimit of the abelian skeleta -/

noncomputable def abelianSkeletonObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (V : SimplicialObject C) (n : ℕ) : SimplicialObject C :=
  (Unit21.leftAdjoint (C := C) n).obj
    ((SimplicialObject.truncation n).obj V)

noncomputable def abelianSkeletonTransition
    {C : Type u} [Category.{v} C] [Abelian C]
    (V : SimplicialObject C) {m n : ℕ} (h : m ≤ n) :
    abelianSkeletonObject V m ⟶ abelianSkeletonObject V n := by
  let T := SimplicialObject.Truncated.trunc C n m h
  let η := Unit21.leftAdjointUnit n ((SimplicialObject.truncation n).obj V)
  let q : (SimplicialObject.truncation m).obj V ⟶
      (SimplicialObject.truncation m).obj (abelianSkeletonObject V n) :=
    (SimplicialObject.truncationCompTrunc h).inv.app V ≫
      T.map η ≫
      (SimplicialObject.truncationCompTrunc h).hom.app
        (abelianSkeletonObject V n)
  exact (Unit21.leftAdjointHomEquiv m
    ((SimplicialObject.truncation m).obj V)
    (abelianSkeletonObject V n)).symm q

theorem abelianSkeletonTransition_id
    {C : Type u} [Category.{v} C] [Abelian C]
    (V : SimplicialObject C) (n : ℕ) :
    abelianSkeletonTransition V (le_rfl : n ≤ n) = 𝟙 _ := by
  sorry

theorem abelianSkeletonTransition_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (V : SimplicialObject C) {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) :
    abelianSkeletonTransition V (hlm.trans hmn) =
      abelianSkeletonTransition V hlm ≫ abelianSkeletonTransition V hmn := by
  sorry

noncomputable def abelianSkeletonTower
    {C : Type u} [Category.{v} C] [Abelian C]
    (V : SimplicialObject C) : ℕ ⥤ SimplicialObject C where
  obj n := abelianSkeletonObject V n
  map f := abelianSkeletonTransition V (leOfHom f)
  map_id n := abelianSkeletonTransition_id V n
  map_comp f g := abelianSkeletonTransition_comp V (leOfHom f) (leOfHom g)

theorem abelianSkeletonTransition_counit
    {C : Type u} [Category.{v} C] [Abelian C]
    (V : SimplicialObject C) {m n : ℕ} (h : m ≤ n) :
    (abelianSkeletonTower V).map (homOfLE h) ≫
        Unit21.leftAdjointCounit n V =
      Unit21.leftAdjointCounit m V := by
  sorry

noncomputable def abelianSkeletonCocone
    {C : Type u} [Category.{v} C] [Abelian C]
    (V : SimplicialObject C) : Cocone (abelianSkeletonTower V) where
  pt := V
  ι := NatTrans.ofSequence
    (fun n => Unit21.leftAdjointCounit n V)
    (fun n => by
      change (abelianSkeletonTower V).map (homOfLE (Nat.le_add_right n 1)) ≫
          Unit21.leftAdjointCounit (n + 1) V =
        Unit21.leftAdjointCounit n V ≫ 𝟙 V
      rw [Category.comp_id]
      exact abelianSkeletonTransition_counit V (Nat.le_add_right n 1))

theorem abelianSkeleton_is_colimit
    {C : Type u} [Category.{v} C] [Abelian C]
    (V : SimplicialObject C) :
    Nonempty (IsColimit (abelianSkeletonCocone V)) := by
  sorry

theorem abelianSkeleton_transition_mono
    {C : Type u} [Category.{v} C] [Abelian C]
    (V : SimplicialObject C) {m n : ℕ} (h : m ≤ n) :
    Mono ((abelianSkeletonTower V).map (homOfLE h)) := by
  sorry

end Formalization.Books.Simplicial.Unit22
