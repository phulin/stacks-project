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
  sorry

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
  sorry

theorem concentratedTruncated_hom_equiv_out
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) (V : SimplicialObject.Truncated C k) :
    Nonempty ((V ⟶ concentratedTruncatedObject A k) ≃
      {f : V.obj (op (topTruncatedSimplex k)) ⟶ A //
        truncatedOutgoingCondition A k V f}) := by
  sorry

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
  sorry

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
