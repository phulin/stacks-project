import Formalization.Books.Simplicial.Unit22.SimplicialObjectsInAbelianCategories
import Formalization.Books.Homology.Unit13.Complexes
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Simplicial Methods, Chapter 23: Simplicial objects and chain complexes

The source's `Ch_{≥ 0}(𝒜)` is represented by Mathlib's canonical
`ChainComplex 𝒜 ℕ`.  This is the concrete nonnegative-index model of the
full subcategory of integer-indexed chain complexes used in the Homology
chapter; it keeps the degree formula `s(U).X n = U _⦋n⦌` definitionally
visible.  Normalized terms and degenerate terms use the normalized subobjects
and last-face factorization from Chapter 18.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit23

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Simplicial.Unit18
open Formalization.Books.Simplicial.Unit22
open Opposite
open HomologicalComplex
open scoped _root_.Simplicial
open scoped ZeroObject

universe v u

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-! ## The associated (Moore) chain complex -/

/-- The alternating boundary in degree `n+1` of a simplicial object. -/
def associatedBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    U.obj (op ⦋n + 1⦌) ⟶ U.obj (op ⦋n⦌) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • U.δ i

/- The displayed cancellation identity in the source is the only
   proposition needed to build the complex; its proof is the standard
   face-face cancellation. -/
theorem associatedBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    associatedBoundary U (n + 1) ≫ associatedBoundary U n = 0 := by
  simpa [associatedBoundary, AlgebraicTopology.AlternatingFaceMapComplex.objD] using
    (AlgebraicTopology.AlternatingFaceMapComplex.d_squared U n)

/-- The associated nonnegative chain complex `s(U)` (the Moore complex). -/
noncomputable def associatedChainComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of
    (fun n => U.obj (op ⦋n⦌))
    (associatedBoundary U)
    (associatedBoundary_comp U)

@[simp]
theorem associatedChainComplex_X
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (associatedChainComplex U).X n = U.obj (op ⦋n⦌) :=
  rfl

@[simp]
theorem associatedChainComplex_d
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (associatedChainComplex U).d (n + 1) n = associatedBoundary U n :=
  by simp [associatedChainComplex]

theorem associatedBoundary_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    f.app (op ⦋n + 1⦌) ≫ associatedBoundary V n =
      associatedBoundary U n ≫ f.app (op ⦋n⦌) := by
  simp only [associatedBoundary, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  congr 1
  symm
  exact SimplicialObject.δ_naturality f i

theorem associatedChainComplexMap_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.down ℕ).Rel i j →
      f.app (op ⦋i⦌) ≫ (associatedChainComplex V).d i j =
        (associatedChainComplex U).d i j ≫ f.app (op ⦋j⦌) := by
  intro i j hij
  simp only [ComplexShape.down_Rel] at hij
  subst i
  simpa only [associatedChainComplex_X, associatedChainComplex_d] using
    associatedBoundary_naturality f j

/-- The chain map induced by a morphism of simplicial objects. -/
def associatedChainComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    associatedChainComplex U ⟶ associatedChainComplex V :=
  { f := fun n => f.app (op ⦋n⦌)
    comm' := associatedChainComplexMap_comm f }

@[simp]
theorem associatedChainComplexMap_f
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (associatedChainComplexMap f).f n = f.app (op ⦋n⦌) :=
  rfl

/-- The functor `s : Simp(𝒜) ⥤ Ch_{≥0}(𝒜)`. -/
def associatedChainComplexFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimplicialObject C ⥤ ChainComplex C ℕ where
  obj U := associatedChainComplex U
  map f := associatedChainComplexMap f
  map_id U := by
    ext n
    rfl
  map_comp f g := by
    ext n
    rfl

theorem associatedChainComplexFunctor_exact
    {C : Type u} [Category.{v} C] [Abelian C] :
    exactFunctor (SimplicialObject C) (ChainComplex C ℕ)
      (associatedChainComplexFunctor C) := by
  rw [exactFunctor_iff]
  constructor
  · refine ⟨?_⟩
    intro J _ _
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    change PreservesLimitsOfShape J
      ((evaluation (SimplexCategoryᵒᵖ) C).obj (op ⦋n⦌))
    infer_instance
  · refine ⟨?_⟩
    intro J _ _
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape J
      ((evaluation (SimplexCategoryᵒᵖ) C).obj (op ⦋n⦌))
    infer_instance

/-! ## The extension and Eilenberg--Mac Lane homology statements -/

private theorem simplex_epi_of_comp_epi
    {X Y Z : SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hcomp : Epi (f ≫ g)) : Epi g := by
  apply (SimplexCategory.epi_iff_surjective).2
  intro z
  obtain ⟨x, hx⟩ :=
    (SimplexCategory.epi_iff_surjective).1 hcomp z
  refine ⟨f.toOrderHom x, ?_⟩
  simpa only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply] using hx

private theorem simplex_last_factorization
    {X Y : SimplexCategory} {m k : ℕ}
    (f : X ⟶ Y) (q : Y ⟶ ⦋m⦌) (e : X ⟶ ⦋k⦌) (hepi : Epi e)
    (hm : m = k + 1)
    (h : HEq (f ≫ q) (e ≫ SimplexCategory.δ (Fin.last (k + 1)))) :
    Epi q ∨ ∃ (q' : Y ⟶ ⦋k⦌), Epi q' ∧
      HEq q (q' ≫ SimplexCategory.δ (Fin.last (k + 1))) ∧ f ≫ q' = e := by
  classical
  subst m
  have h' : f ≫ q = e ≫ SimplexCategory.δ (Fin.last (k + 1)) :=
    eq_of_heq h
  by_cases hq : Epi q
  · exact Or.inl hq
  · right
    have hqns : ¬Function.Surjective q.toOrderHom := by
      intro hsurj
      exact hq ((SimplexCategory.epi_iff_surjective).2 hsurj)
    have hfactor := SimplexCategory.eq_comp_δ_of_not_surjective q hqns
    let i : Fin (k + 2) := hfactor.choose
    let hfactor_i := hfactor.choose_spec
    let q' : Y ⟶ ⦋k⦌ := hfactor_i.choose
    have hfactor_q := hfactor_i.choose_spec
    have hqfac : q = q' ≫ SimplexCategory.δ i := hfactor_q
    have he : Function.Surjective e.toOrderHom :=
      (SimplexCategory.epi_iff_surjective).1 hepi
    have hi : i = Fin.last (k + 1) := by
      apply Fin.eq_last_of_not_lt
      intro hilast
      let j : Fin (k + 1) := ⟨i.1, hilast⟩
      obtain ⟨x, hx⟩ := he j
      have hqx : q.toOrderHom (f.toOrderHom x) =
          (SimplexCategory.δ (Fin.last (k + 1))).toOrderHom j := by
        have h'' := congrArg (fun t : X ⟶ ⦋k + 1⦌ => t.toOrderHom x) h'
        rw [SimplexCategory.comp_toOrderHom,
          SimplexCategory.comp_toOrderHom] at h''
        simpa [Function.comp_apply, j, hx] using h''
      have hqfac' := congrArg
        (fun t : Y ⟶ ⦋k + 1⦌ => t.toOrderHom (f.toOrderHom x)) hqfac
      rw [SimplexCategory.comp_toOrderHom] at hqfac'
      have hδlast :
          (SimplexCategory.δ (Fin.last (k + 1))).toOrderHom j = i := by
        change (Fin.last (k + 1)).succAbove j = i
        rw [Fin.succAbove_of_castSucc_lt]
        · apply Fin.ext
          rfl
        · dsimp [j]
          exact hilast
      have hi' : (SimplexCategory.δ i).toOrderHom
          (q'.toOrderHom (f.toOrderHom x)) = i :=
        hqfac'.symm.trans (hqx.trans hδlast)
      have hi'' : i.succAbove
          (q'.toOrderHom (f.toOrderHom x)) = i := by
        change (SimplexCategory.δ i).toOrderHom
            (q'.toOrderHom (f.toOrderHom x)) = i
        exact hi'
      exact Fin.succAbove_ne i _ hi''
    rw [hi] at hqfac
    have hq' : Function.Surjective q'.toOrderHom := by
      intro y
      obtain ⟨x, hx⟩ := he y
      refine ⟨f.toOrderHom x, ?_⟩
      have h'' := congrArg (fun t : X ⟶ ⦋k + 1⦌ => t.toOrderHom x) h'
      rw [SimplexCategory.comp_toOrderHom,
        SimplexCategory.comp_toOrderHom] at h''
      rw [hqfac] at h''
      rw [SimplexCategory.comp_toOrderHom] at h''
      simp only [OrderHom.comp_coe, Function.comp_apply] at h''
      rw [hx] at h''
      exact ((SimplexCategory.mono_iff_injective).1
        (inferInstance : Mono (SimplexCategory.δ (Fin.last (k + 1))))) h''
    refine ⟨q', (SimplexCategory.epi_iff_surjective).2 hq',
      heq_of_eq hqfac, ?_⟩
    apply (cancel_mono (SimplexCategory.δ (Fin.last (k + 1)))).1
    rw [Category.assoc, ← hqfac, h']

private theorem extensionImageProperty_of_comp
    {k m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (q : ⦋n⦌ ⟶ ⦋k + 1⦌)
    (h : extensionImageProperty (f ≫ q)) : extensionImageProperty q := by
  rcases h with h | ⟨e, hepi, he⟩
  · exact Or.inl (simplex_epi_of_comp_epi f q h)
  · rcases simplex_last_factorization f q e hepi rfl (heq_of_eq he.symm) with hq | hq
    · exact Or.inl hq
    · exact Or.inr ⟨hq.choose, hq.choose_spec.1,
        (eq_of_heq hq.choose_spec.2.1).symm⟩

/- The source's extension is not the biproduct of two Eilenberg--Mac Lane
   objects: precomposition can send a `[k + 1]` summand to a `[k]` summand.
   The Chapter 22 degreewise carrier and map already encode this cross-term,
   so use them directly here. -/
noncomputable def eilenbergMacLaneExtension
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) : SimplicialObject C :=
  { obj := fun n => extensionDegreeDirectSum A k n.unop.len
    map := fun {X Y} f =>
      let φ : ⦋Y.unop.len⦌ ⟶ ⦋X.unop.len⦌ := by
        simpa only [SimplexCategory.mk_len] using f.unop
      extensionDirectSumMap A k Y.unop.len X.unop.len φ
    map_id := by
      intro X
      classical
      let e := biproduct.isoCoproduct
        (fun _ : ExtensionSimplexIndex (unop X).len k => A)
      let M : (⨁ fun _ : ExtensionSimplexIndex (unop X).len k => A) ⟶
          (⨁ fun _ : ExtensionSimplexIndex (unop X).len k => A) :=
        biproduct.matrix (fun α α' =>
          if h : extensionImageProperty ((𝟙 (unop X)) ≫ α.1) then
            if α' = (⟨(𝟙 (unop X)) ≫ α.1, h⟩ :
                ExtensionSimplexIndex (unop X).len k)
            then 𝟙 A else 0
          else 0)
      change e.inv ≫ M ≫ e.hom = _
      rw [← e.inv_hom_id, ← Category.assoc, cancel_mono e.hom]
      suffices hM : M = 𝟙 _ by simp [hM]
      apply (biproduct.matrixEquiv
        (f := fun _ : ExtensionSimplexIndex (unop X).len k => A)
        (g := fun _ : ExtensionSimplexIndex (unop X).len k => A)).injective
      funext α α'
      simp [M, biproduct.matrixEquiv, biproduct.components]
      rw [if_pos α.property]
      by_cases h : α' = α
      · subst α'
        rw [biproduct.ι_π]
        simp
      · have h'' : ¬ α = α' := by
          intro hh
          exact h hh.symm
        rw [biproduct.ι_π, if_neg h, dif_neg h'']
    map_comp := by
      intro X Y Z f g
      classical
      let eX := biproduct.isoCoproduct
        (fun _ : ExtensionSimplexIndex (unop X).len k => A)
      let eY := biproduct.isoCoproduct
        (fun _ : ExtensionSimplexIndex (unop Y).len k => A)
      let eZ := biproduct.isoCoproduct
        (fun _ : ExtensionSimplexIndex (unop Z).len k => A)
      let Mf : (⨁ fun _ : ExtensionSimplexIndex (unop X).len k => A) ⟶
          (⨁ fun _ : ExtensionSimplexIndex (unop Y).len k => A) :=
        biproduct.matrix (fun α α' =>
          if h : extensionImageProperty (f.unop ≫ α.1) then
            if α' = (⟨f.unop ≫ α.1, h⟩ :
                ExtensionSimplexIndex (unop Y).len k)
            then 𝟙 A else 0
          else 0)
      let Mg : (⨁ fun _ : ExtensionSimplexIndex (unop Y).len k => A) ⟶
          (⨁ fun _ : ExtensionSimplexIndex (unop Z).len k => A) :=
        biproduct.matrix (fun α α' =>
          if h : extensionImageProperty (g.unop ≫ α.1) then
            if α' = (⟨g.unop ≫ α.1, h⟩ :
                ExtensionSimplexIndex (unop Z).len k)
            then 𝟙 A else 0
          else 0)
      let Mfg : (⨁ fun _ : ExtensionSimplexIndex (unop X).len k => A) ⟶
          (⨁ fun _ : ExtensionSimplexIndex (unop Z).len k => A) :=
        biproduct.matrix (fun α α' =>
          if h : extensionImageProperty (g.unop ≫ f.unop ≫ α.1) then
            if α' = (⟨g.unop ≫ f.unop ≫ α.1, h⟩ :
                ExtensionSimplexIndex (unop Z).len k)
            then 𝟙 A else 0
          else 0)
      change eX.inv ≫ Mfg ≫ eZ.hom =
        (eX.inv ≫ Mf ≫ eY.hom) ≫ (eY.inv ≫ Mg ≫ eZ.hom)
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [cancel_epi eX.inv, ← Category.assoc, cancel_mono eZ.hom]
      apply (biproduct.matrixEquiv
        (f := fun _ : ExtensionSimplexIndex (unop X).len k => A)
        (g := fun _ : ExtensionSimplexIndex (unop Z).len k => A)).injective
      funext α α'
      simp [Mfg, Mf, Mg, biproduct.matrixEquiv, biproduct.components,
        biproduct.matrix]
      rw [biproduct.lift_desc_assoc]
      rw [Preadditive.sum_comp]
      by_cases hcomp : extensionImageProperty
          (g.unop ≫ (f.unop ≫ α.1))
      · have hcomp' : extensionImageProperty
            (g.unop ≫ f.unop ≫ α.1) := by
          simpa only [Category.assoc] using hcomp
        have hfa : extensionImageProperty (f.unop ≫ α.1) :=
          extensionImageProperty_of_comp g.unop (f.unop ≫ α.1) hcomp
        let β : ExtensionSimplexIndex (unop Y).len k :=
          ⟨f.unop ≫ α.1, hfa⟩
        have hgb : extensionImageProperty (g.unop ≫ β.1) := by
          simpa only [β, Category.assoc] using hcomp
        rw [Fintype.sum_eq_single β]
        · simp [β, hfa, hgb]
        · intro x hx
          simp only [dif_pos hfa]
          by_cases hxe : x = β
          · exact (hx hxe).elim
          · have hxe' : ¬x =
                (⟨f.unop ≫ α.1, hfa⟩ : ExtensionSimplexIndex (unop Y).len k) := by
              intro h'
              apply hx
              simpa [β] using h'
            simp [hxe']
      · have hcomp' : ¬extensionImageProperty
            (g.unop ≫ f.unop ≫ α.1) := by
          simpa only [Category.assoc] using hcomp
        by_cases hfa : extensionImageProperty (f.unop ≫ α.1)
        · let β : ExtensionSimplexIndex (unop Y).len k :=
            ⟨f.unop ≫ α.1, hfa⟩
          have hgb : ¬extensionImageProperty (g.unop ≫ β.1) := by
            intro hgb
            apply hcomp'
            simpa only [β, Category.assoc] using hgb
          rw [Fintype.sum_eq_single β]
          · simp [β, hfa, hgb]
          · intro x hx
            simp only [dif_pos hfa]
            by_cases hxe : x = β
            · exact (hx hxe).elim
            · have hxe' : ¬x =
                  (⟨f.unop ≫ α.1, hfa⟩ : ExtensionSimplexIndex (unop Y).len k) := by
                intro h'
                apply hx
                simpa [β] using h'
              simp [hxe']
        · simp [hfa, hcomp']
  }

theorem eilenbergMacLaneExtension_acyclic
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    (associatedChainComplex (eilenbergMacLaneExtension A k)).Acyclic := by
  sorry

/- The textbook says only "integer" in the next two lemmas, while its
   definition of `K(A,k)` has the necessary hypothesis `k ≥ 0`.  The natural
   Lean interface therefore uses `k : ℕ`. -/
theorem eilenbergMacLane_homology_at
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    Nonempty ((associatedChainComplex (eilenbergMacLane A k)).homology k ≅ A) := by
  sorry

theorem eilenbergMacLane_homology_vanishes
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k i : ℕ) (hi : i ≠ k) :
    IsZero ((associatedChainComplex (eilenbergMacLane A k)).homology i) := by
  sorry

/-! ## The normalized chain complex -/

/-- The signed last-face differential on normalized terms. -/
def normalizedBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    normalizedObject U (n + 1) ⟶ normalizedObject U n :=
  (-1 : ℤ) ^ (n + 1) • normalizedLastFace U n

theorem normalizedBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    normalizedBoundary U (n + 1) ≫ normalizedBoundary U n = 0 := by
  have h : normalizedLastFace U (n + 1) ≫ normalizedLastFace U n = 0 := by
    apply (cancel_mono (normalizedSubobject U n).arrow).1
    rw [Category.assoc, normalizedLastFace_arrow U n, ← Category.assoc,
      normalizedLastFace_arrow U (n + 1)]
    simp only [Category.assoc, zero_comp]
    have hδ :
        U.δ (Fin.last (n + 1 + 1)) ≫ U.δ (Fin.last (n + 1)) =
          U.δ (Fin.castSucc (Fin.last (n + 1))) ≫ U.δ (Fin.last (n + 1)) := by
      simpa using (U.δ_comp_δ_self (i := Fin.last (n + 1))).symm
    rw [hδ]
    change
      (Finset.univ.inf (fun i : Fin (n + 2) => kernelSubobject (U.δ i.castSucc))).arrow ≫
        U.δ (Fin.castSucc (Fin.last (n + 1))) ≫ U.δ (Fin.last (n + 1)) = 0
    let hfac := Subobject.finset_inf_arrow_factors (s := Finset.univ)
      (P := fun i : Fin (n + 2) => kernelSubobject (U.δ i.castSucc))
      (Fin.last (n + 1)) (by simp)
    rw [← Subobject.factorThru_arrow _ _ hfac]
    let f :=
      Subobject.factorThru
        (kernelSubobject (U.δ (Fin.castSucc (Fin.last (n + 1)))))
        (Finset.univ.inf (fun i : Fin (n + 2) => kernelSubobject (U.δ i.castSucc))).arrow hfac
    have hk := kernelSubobject_arrow_comp (f := U.δ (Fin.castSucc (Fin.last (n + 1))))
    simpa only [Category.assoc, comp_zero, zero_comp] using
      congrArg (fun q => f ≫ q ≫ U.δ (Fin.last (n + 1))) hk
  simp [normalizedBoundary, h]

/-- The normalized chain complex `N(U)`. -/
noncomputable def normalizedChainComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of
    (fun n => normalizedObject U n)
    (normalizedBoundary U)
    (normalizedBoundary_comp U)

@[simp]
theorem normalizedChainComplex_X
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (normalizedChainComplex U).X n = normalizedObject U n :=
  rfl

@[simp]
theorem normalizedChainComplex_d
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (normalizedChainComplex U).d (n + 1) n = normalizedBoundary U n :=
  by simp [normalizedChainComplex]

theorem normalizedBoundary_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    normalizedSubobjectMap f (n + 1) ≫ normalizedBoundary V n =
      normalizedBoundary U n ≫ normalizedSubobjectMap f n := by
  simp only [normalizedBoundary, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  apply (cancel_mono (normalizedSubobject V n).arrow).1
  rw [Category.assoc, normalizedLastFace_arrow]
  rw [← Category.assoc, normalizedSubobjectMap_arrow]
  rw [Category.assoc]
  rw [SimplicialObject.δ_def]
  rw [← f.naturality (SimplexCategory.δ (Fin.last (n + 1))).op]
  rw [Category.assoc, normalizedSubobjectMap_arrow]
  rw [← Category.assoc (normalizedLastFace U n)
    ((normalizedSubobject U n).arrow) (f.app (op ⦋n⦌))]
  rw [normalizedLastFace_arrow]
  simp only [SimplicialObject.δ_def, Category.assoc]

theorem normalizedChainComplexMap_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.down ℕ).Rel i j →
      normalizedSubobjectMap f i ≫ (normalizedChainComplex V).d i j =
        (normalizedChainComplex U).d i j ≫ normalizedSubobjectMap f j := by
  intro i j hij
  simp only [ComplexShape.down_Rel] at hij
  subst i
  simpa only [normalizedChainComplex_X, normalizedChainComplex_d] using
    normalizedBoundary_naturality f j

/-- The chain map induced on normalized complexes. -/
def normalizedChainComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    normalizedChainComplex U ⟶ normalizedChainComplex V :=
  { f := fun n => normalizedSubobjectMap f n
    comm' := normalizedChainComplexMap_comm f }

def normalizedChainComplexFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimplicialObject C ⥤ ChainComplex C ℕ where
  obj U := normalizedChainComplex U
  map f := normalizedChainComplexMap f
  map_id U := by
    ext n
    exact normalizedSubobjectMap_id U n
  map_comp f g := by
    ext n
    exact normalizedSubobjectMap_comp f g n

theorem normalizedChainComplexFunctor_exact
    {C : Type u} [Category.{v} C] [Abelian C] :
    exactFunctor (SimplicialObject C) (ChainComplex C ℕ)
      (normalizedChainComplexFunctor C) := by
  /- Prior attempt: the associated-complex evaluation proof does not apply to
     normalized terms.  After `exactFunctor_iff`, evaluation leaves the
     targets
     `PreservesLimitsOfShape J
       (normalizedChainComplexFunctor C ⋙ eval C (ComplexShape.down ℕ) n)`
     and the corresponding colimit targets; these are not definitionally the
     ordinary simplicial degree-evaluation functors.

     rw [exactFunctor_iff]
     constructor
     · refine ⟨?_⟩
       intro J _ _
       apply HomologicalComplex.preservesLimitsOfShape_of_eval
       intro n
       change PreservesLimitsOfShape J
         ((evaluation (SimplexCategoryᵒᵖ) C).obj (op ⦋n⦌))
       infer_instance
     · refine ⟨?_⟩
       intro J _ _
       apply HomologicalComplex.preservesColimitsOfShape_of_eval
       intro n
       change PreservesColimitsOfShape J
         ((evaluation (SimplexCategoryᵒᵖ) C).obj (op ⦋n⦌))
       infer_instance -/
  sorry

/-! ## The canonical map from normalized to associated complexes -/

theorem normalized_to_associated_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    ∀ i j : ℕ, (ComplexShape.down ℕ).Rel i j →
      (normalizedSubobject U i).arrow ≫ (associatedChainComplex U).d i j =
        (normalizedChainComplex U).d i j ≫
          (normalizedSubobject U j).arrow := by
  sorry

/-- The canonical inclusion `N(U) ⟶ s(U)`. -/
def normalizedToAssociated
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    normalizedChainComplex U ⟶ associatedChainComplex U :=
  { f := fun n => (normalizedSubobject U n).arrow
    comm' := normalized_to_associated_comm U }

theorem normalizedToAssociated_component
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (normalizedToAssociated U).f n = (normalizedSubobject U n).arrow :=
  rfl

theorem normalized_eilenbergMacLane_at
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    Nonempty (normalizedObject (eilenbergMacLane A k) k ≅ A) := by
  sorry

theorem normalized_eilenbergMacLane_vanishes
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k i : ℕ) (hi : i ≠ k) :
    IsZero (normalizedObject (eilenbergMacLane A k) i) := by
  sorry

theorem normalizedToAssociated_split
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    IsSplitMono (normalizedToAssociated U) := by
  sorry

/-! ## The degenerate subcomplex and the splitting -/

/-- Indices for the source's direct sum of normalized terms mapping
surjectively into degree `n`. -/
abbrev DegenerateIndex (n : ℕ) :=
  Σ m : Fin n, SurjectiveSimplexIndex n m.1

noncomputable instance degenerateIndexFintype (n : ℕ) :
    Fintype (DegenerateIndex n) := Fintype.ofFinite _

noncomputable def degenerateSummand
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) : C :=
  ∐ fun a : DegenerateIndex n => normalizedObject U a.1.1

noncomputable def degenerateSummandMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    degenerateSummand U n ⟶ U.obj (op ⦋n⦌) :=
  Sigma.desc (fun a =>
    (normalizedSubobject U a.1.1).arrow ≫ U.map a.2.1.op)

/- The image of the displayed direct-sum map is the source's `D(U)_n`. -/
noncomputable def degenerateSubobject
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) : Subobject (U.obj (op ⦋n⦌)) :=
  imageSubobject (degenerateSummandMap U n)

noncomputable abbrev degenerateObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) : C :=
  degenerateSubobject U n

/- Precomposition by an epimorphism does not change an image subobject in a
   balanced category.  `Subobject.imageSubobject_comp_le_epi_of_epi` supplies
   the comparison epi; the reverse inequality below is the small missing
   bridge needed when a proof starts on the generators of an image. -/
private theorem imageSubobject_comp_eq_of_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} (e : X ⟶ Y) [Epi e] (f : Y ⟶ Z) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  let h := imageSubobject_comp_le e f
  apply le_antisymm h
  let q := Subobject.ofLE (imageSubobject (e ≫ f)) (imageSubobject f) h
  letI : Epi q := imageSubobject_comp_le_epi_of_epi e f
  letI : IsIso q := isIso_of_mono_of_epi q
  exact Subobject.le_of_comm (inv q) (by simp [q])

/- The alternative source description uses all lower-degree terms rather than
   only normalized summands.  It is deliberately placed before the boundary
   construction: after the equality below has been proved, boundary stability
   can be checked on arbitrary lower-degree generators without trying to
   normalize each face separately. -/
noncomputable def fullDegenerateSummand
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) : C :=
  ∐ fun a : DegenerateIndex n => U.obj (op ⦋a.1.1⦌)

noncomputable def fullDegenerateSummandMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    fullDegenerateSummand U n ⟶ U.obj (op ⦋n⦌) :=
  Sigma.desc (fun a => U.map a.2.1.op)

/-
Proof roadmap for `degenerateSubobject_eq_full`:

* For the easy inclusion, define

    `j : degenerateSummand U n ⟶ fullDegenerateSummand U n :=
      Sigma.map (fun a => (normalizedSubobject U a.1.1).arrow)`.

  `Sigma.map_ι` and `Sigma.ι_desc` show
  `j ≫ fullDegenerateSummandMap U n = degenerateSummandMap U n`.
  Apply `imageSubobject_comp_le` (or `imageSubobject_le` with that equation)
  to obtain `degenerateSubobject U n ≤ imageSubobject
  (fullDegenerateSummandMap U n)`.
* For the reverse inclusion, choose `s` and `hs : IsNormalizedSplitting s`
  from `abelian_category_has_normalized_splitting U` in
  `Formalization/Books/Simplicial/Unit18/SplittingSimplicialObjects.lean`.
  For each outer index `a : DegenerateIndex n`, define a map
  `U.obj (op ⟦a.1.1⟧) ⟶ degenerateObject U n` with
  `s.desc (op ⟦a.1.1⟧)`.  On a splitting index
  `A : SimplicialObject.Splitting.IndexSet (op ⟦a.1.1⟧)`, first use the
  iso supplied by `hs.1 A.1.unop.len` to replace `s.N ...` by
  `normalizedObject U A.1.unop.len`, and then use the coproduct injection
  indexed by the composite epi `a.2.1 ≫ A.e` followed by
  `factorThruImageSubobject (degenerateSummandMap U n)`.
* The composite really is a `DegenerateIndex n`: use
  `SimplexCategory.len_le_of_epi A.e` and `a.1.2` to prove
  `A.1.unop.len < n`, and use `epi_comp` for `a.2.1 ≫ A.e`.  If Lean does
  not identify `A.1.unop` with `⟦A.1.unop.len⟧` definitionally, obtain the
  object equality by `SimplexCategory.ext` and insert the resulting
  `eqToHom`; finish index equalities with `Splitting.IndexSet.ext`.
* Assemble these maps with an outer `Sigma.desc`, call the result `r`, and
  prove

    `r ≫ (degenerateSubobject U n).arrow = fullDegenerateSummandMap U n`.

  Use `Sigma.hom_ext`, then `s.hom_ext'`; on every splitting summand the
  equation is exactly `s.ι_desc`, `s.cofan_inj_eq`, `Sigma.ι_desc`, and
  `imageSubobject_arrow_comp`, together with `U.map_comp`.
  `imageSubobject_le _ r` gives the reverse inclusion, and `le_antisymm`
  finishes.  The splitting declarations are in
  `Mathlib/AlgebraicTopology/SimplicialObject/Split.lean`; the image
  declarations are in `Mathlib/CategoryTheory/Subobject/Limits.lean`.

Do not try to prove the reverse inclusion by a bare comparison of the two
coproduct domains: the full summand contains whole objects `U_m`, so the
normalized splitting (and its `desc` universal property) is precisely the
missing map into the normalized-generator image.
-/
theorem degenerateSubobject_eq_full
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    degenerateSubobject U n = imageSubobject (fullDegenerateSummandMap U n) := by
  sorry

/- In `AddCommGrpCat`, this equality is the categorical form of the source's
   statement that degenerate terms are sums of degenerate simplices. -/

/-
Proof roadmap for `degenerateBoundary_factors`:

* Rewrite both degenerate subobjects with `degenerateSubobject_eq_full`.
  It is enough to show that the image of
  `(fullDegenerateSummandMap U (n + 1)) ≫ associatedBoundary U n` lies in
  the target image: precompose the desired map by the epi
  `factorThruImageSubobject (fullDegenerateSummandMap U (n + 1))`, use
  `imageSubobject_arrow_comp`, and remove that epi with the local lemma
  `imageSubobject_comp_eq_of_epi`.
* Use `Sigma.hom_ext` and expand `associatedBoundary`.  Fix
  `a : DegenerateIndex (n + 1)`, with epi
  `e := a.2.1 : ⟦n + 1⟧ ⟶ ⟦a.1.1⟧`.
  If `a.1.1 < n`, factor every `SimplexCategory.δ i ≫ e` through its
  categorical image.  Its epi part has target length at most `a.1.1 < n`
  by `SimplexCategory.len_le_of_mono`/`len_le_of_epi`; it therefore supplies
  a `DegenerateIndex n`.  Map `U.obj (op ⟦a.1.1⟧)` first along the mono
  part (contravariantly), then into that full degenerate summand.  The
  equations are `image.fac`, `U.map_comp`, and `Sigma.ι_desc`.
* The only exceptional case is `a.1.1 = n`.  Use
  `SimplexCategory.eq_σ_of_epi e` from
  `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean` to write
  `e = SimplexCategory.σ j`.  In the alternating sum, the terms
  `i = j.castSucc` and `i = j.succ` are both the identity by
  `SimplexCategory.δ_comp_σ_self` and `δ_comp_σ_succ`, and their
  coefficients cancel.  For `i` on either side, use
  `δ_comp_σ_of_le` or `δ_comp_σ_of_gt` to expose a surjection
  to degree `n - 1`, hence a target generator.  Split the finite sum with
  `Fin.sum_univ_succ` (twice at `j`) so the cancellation is explicit.
* Assemble the component factorizations by `Sigma.desc` and addition into a
  map `fullDegenerateSummand U (n + 1) ⟶ degenerateObject U n`.
  Apply `imageSubobject_le` to its arrow equation, transport back across the
  two `degenerateSubobject_eq_full` equalities, and conclude `Factors` with
  `Subobject.factors_iff` (or directly with `factorThru`).

Factoring every `δ i ≫ e` uniformly is a dead end: when `e : [n+1] ↠ [n]`,
the two identity composites are not degenerate individually; only their
opposite signed terms cancel.
-/

theorem degenerateBoundary_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U n).Factors
      ((degenerateSubobject U (n + 1)).arrow ≫ associatedBoundary U n) := by
  sorry

noncomputable def degenerateBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    degenerateObject U (n + 1) ⟶ degenerateObject U n :=
  (degenerateSubobject U n).factorThru
    ((degenerateSubobject U (n + 1)).arrow ≫ associatedBoundary U n)
    (degenerateBoundary_factors U n)

@[reassoc]
theorem degenerateBoundary_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    degenerateBoundary U n ≫ (degenerateSubobject U n).arrow =
      (degenerateSubobject U (n + 1)).arrow ≫ associatedBoundary U n :=
  Subobject.factorThru_arrow _ _ _

/-
Proof roadmap for `degenerateBoundary_comp`:

Cancel the mono `(degenerateSubobject U n).arrow`.  Reassociate, rewrite the
rightmost boundary with `degenerateBoundary_arrow`, then rewrite the remaining
boundary with `degenerateBoundary_arrow_assoc`.  The goal becomes

  `(degenerateSubobject U (n + 2)).arrow ≫
      associatedBoundary U (n + 1) ≫ associatedBoundary U n = 0`.

Close it with `associatedBoundary_comp U n`, `Category.assoc`, `comp_zero`,
and `zero_comp`.  No image calculation is needed after the arrow lemma; in
particular, unfolding either `Subobject.factorThru` is counterproductive.
-/

theorem degenerateBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    degenerateBoundary U (n + 1) ≫ degenerateBoundary U n = 0 := by
  sorry

/-- The degenerate subcomplex `D(U) ⊂ s(U)`. -/
noncomputable def degenerateChainComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of
    (fun n => degenerateObject U n)
    (degenerateBoundary U)
    (degenerateBoundary_comp U)

@[simp]
theorem degenerateChainComplex_d
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (degenerateChainComplex U).d (n + 1) n = degenerateBoundary U n := by
  simp [degenerateChainComplex]

theorem degenerate_to_associated_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    ∀ i j : ℕ, (ComplexShape.down ℕ).Rel i j →
      (degenerateSubobject U i).arrow ≫ (associatedChainComplex U).d i j =
        (degenerateChainComplex U).d i j ≫
          (degenerateSubobject U j).arrow := by
  intro i j hij
  simp only [ComplexShape.down_Rel] at hij
  subst i
  simpa only [associatedChainComplex_d, degenerateChainComplex_d] using
    (degenerateBoundary_arrow U j).symm

/-- The canonical inclusion of the degenerate subcomplex in the associated
complex.  This map is part of the splitting interface: without it an abstract
isomorphism `s(U) ≅ N(U) ⊞ D(U)` cannot say which summand is degenerate. -/
noncomputable def degenerateToAssociated
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    degenerateChainComplex U ⟶ associatedChainComplex U :=
  { f := fun n => (degenerateSubobject U n).arrow
    comm' := degenerate_to_associated_comm U }

@[simp]
theorem degenerateToAssociated_component
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (degenerateToAssociated U).f n = (degenerateSubobject U n).arrow :=
  rfl

/-
Proof roadmap for `degenerateSubobject_map_factors`:

* Work on the normalized generators; the full-generator equality is not
  needed here.  Define

    `r : degenerateSummand U n ⟶ degenerateObject V n :=
      Sigma.desc (fun a =>
        normalizedSubobjectMap f a.1.1 ≫
        Sigma.ι (fun b : DegenerateIndex n => normalizedObject V b.1.1) a ≫
        factorThruImageSubobject (degenerateSummandMap V n))`.

* By `Sigma.hom_ext`, `Sigma.ι_desc`, `normalizedSubobjectMap_arrow`, and
  naturality of `f` at `a.2.1.op`, prove

    `r ≫ (degenerateSubobject V n).arrow =
      degenerateSummandMap U n ≫ f.app (op ⦋n⦌)`.

  Use `imageSubobject_arrow_comp` for the last factor and orient naturality as
  `f.naturality a.2.1.op`.
* Apply `imageSubobject_le` to this equation.  To pass from the image of the
  generator composite to the image of
  `(degenerateSubobject U n).arrow ≫ f.app ...`, precompose the latter by
  the epi `factorThruImageSubobject (degenerateSummandMap U n)`, simplify
  with `imageSubobject_arrow_comp`, and use
  `imageSubobject_comp_eq_of_epi`.  Convert the resulting subobject
  inequality to `Factors` with `Subobject.factors_iff`/`factorThru`.

The important universe instantiation is unchanged throughout:
`C : Type u`, `Category.{v} C`; `Sigma.ι` is the finite coproduct in this
same `C`, not a coproduct in `AddCommGrpCat`.
-/

theorem degenerateSubobject_map_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (degenerateSubobject V n).Factors
      ((degenerateSubobject U n).arrow ≫ f.app (op ⦋n⦌)) := by
  sorry

noncomputable def degenerateSubobjectMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    degenerateObject U n ⟶ degenerateObject V n :=
  (degenerateSubobject V n).factorThru
    ((degenerateSubobject U n).arrow ≫ f.app (op ⦋n⦌))
    (degenerateSubobject_map_factors f n)

theorem degenerateSubobjectMap_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    degenerateSubobjectMap f n ≫ (degenerateSubobject V n).arrow =
      (degenerateSubobject U n).arrow ≫ f.app (op ⦋n⦌) :=
  Subobject.factorThru_arrow _ _ _

/-
Proof roadmap for `degenerateChainComplexMap_comm`:

Introduce `i`, `j`, and the shape relation, simplify
`ComplexShape.down_Rel`, and substitute `i = j + 1`.  Cancel the mono
`(degenerateSubobject V j).arrow`.  On the left, use
`degenerateBoundary_arrow` and then `degenerateSubobjectMap_arrow` in degree
`j + 1`; on the right, use `degenerateSubobjectMap_arrow` in degree `j` and
`degenerateBoundary_arrow_assoc`.  After reassociation the sole middle
equality is

  `f.app (op ⦋j + 1⦌) ≫ associatedBoundary V j =
    associatedBoundary U j ≫ f.app (op ⦋j⦌)`,

which is exactly `associatedBoundary_naturality f j`.  Normalize the two
complex differentials first with `degenerateChainComplex_d`; do not unfold
`degenerateSubobjectMap` or `degenerateBoundary`.
-/

theorem degenerateChainComplexMap_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.down ℕ).Rel i j →
      degenerateSubobjectMap f i ≫ (degenerateChainComplex V).d i j =
        (degenerateChainComplex U).d i j ≫ degenerateSubobjectMap f j := by
  sorry

noncomputable def degenerateChainComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    degenerateChainComplex U ⟶ degenerateChainComplex V :=
  { f := fun n => degenerateSubobjectMap f n
    comm' := degenerateChainComplexMap_comm f }

theorem degenerateChainComplexMap_id
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    degenerateChainComplexMap (𝟙 U) = 𝟙 (degenerateChainComplex U) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degenerateSubobjectMap (𝟙 U) n = 𝟙 _
  apply (cancel_mono (degenerateSubobject U n).arrow).1
  rw [degenerateSubobjectMap_arrow]
  simp

theorem degenerateChainComplexMap_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V W : SimplicialObject C} (f : U ⟶ V) (g : V ⟶ W) :
    degenerateChainComplexMap (f ≫ g) =
      degenerateChainComplexMap f ≫ degenerateChainComplexMap g := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degenerateSubobjectMap (f ≫ g) n =
    degenerateSubobjectMap f n ≫ degenerateSubobjectMap g n
  apply (cancel_mono (degenerateSubobject W n).arrow).1
  rw [degenerateSubobjectMap_arrow]
  simp only [Category.assoc]
  rw [degenerateSubobjectMap_arrow]
  rw [← Category.assoc, degenerateSubobjectMap_arrow]
  simp [Category.assoc]

def degenerateChainComplexFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimplicialObject C ⥤ ChainComplex C ℕ where
  obj U := degenerateChainComplex U
  map f := degenerateChainComplexMap f
  map_id U := by
    exact degenerateChainComplexMap_id U
  map_comp f g := by
    exact degenerateChainComplexMap_comp f g

theorem normalized_and_degenerate_decomposition
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    Nonempty (associatedChainComplex U ≅
      normalizedChainComplex U ⊞ degenerateChainComplex U) := by
  sorry

theorem normalized_to_associated_is_split
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    IsSplitMono (normalizedToAssociated U) :=
  normalizedToAssociated_split U

theorem normalized_to_associated_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    QuasiIso (normalizedToAssociated U) := by
  sorry

theorem degenerateChainComplex_acyclic
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    (degenerateChainComplex U).Acyclic := by
  sorry

end Formalization.Books.Simplicial.Unit23
