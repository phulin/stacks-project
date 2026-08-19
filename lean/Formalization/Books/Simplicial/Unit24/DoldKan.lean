import Formalization.Books.Simplicial.Unit23.SimplicialObjectsAndChainComplexes
import Mathlib.CategoryTheory.Equivalence

/-!
# Simplicial Methods, Chapter 24: Dold--Kan

The source's `N` is the normalized chain-complex functor from Chapter 23.
This file records the formal criterion used in the proof and the reverse
construction on a nonnegative chain complex.  The finite coproducts below are
indexed by epimorphisms in the simplex category; this is the categorical form
of the source's maps whose image is an initial segment `[k]`.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit24

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Simplicial.Unit18
open Formalization.Books.Simplicial.Unit22
open Formalization.Books.Simplicial.Unit23
open Opposite
open HomologicalComplex
open scoped _root_.Simplicial
open scoped ZeroObject

universe v u

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-! ## Faithfulness and reflection of the normalized functor -/

theorem normalizedChainComplexFunctor_faithful
    {C : Type u} [Category.{v} C] [Abelian C] :
    (normalizedChainComplexFunctor C).Faithful := by
  refine ⟨?_⟩
  intro U V f g hfg
  obtain ⟨s, hs⟩ := abelian_category_has_normalized_splitting U
  apply s.hom_ext f g
  intro n
  rcases hs.1 n with ⟨e, he⟩
  have hN : normalizedSubobjectMap f n = normalizedSubobjectMap g n := by
    exact congrArg (fun k => k.f n) hfg
  change s.ι n ≫ f.app (op ⦋n⦌) = s.ι n ≫ g.app (op ⦋n⦌)
  rw [← he]
  simp only [Category.assoc]
  rw [← normalizedSubobjectMap_arrow f n, ← normalizedSubobjectMap_arrow g n, hN]

theorem normalizedChainComplexFunctor_reflects_monomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hf : Mono ((normalizedChainComplexFunctor C).map f)) :
    Mono f := by
  rw [simplicial_mono_iff_componentwise]
  intro n
  let _ : Mono ((normalizedChainComplexFunctor C).map f) := hf
  have hstd : ∀ k : ℕ, Mono (f.app (op ⦋k⦌)) :=
    normalized_reflects_monomorphism f (fun k => by
      change Mono (((normalizedChainComplexFunctor C).map f).f k)
      infer_instance)
  simpa only [SimplexCategory.mk_len] using (hstd n.unop.len)

theorem normalizedChainComplexFunctor_reflects_epimorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hf : Epi ((normalizedChainComplexFunctor C).map f)) :
    Epi f := by
  rw [simplicial_epi_iff_componentwise]
  intro n
  let _ : Epi ((normalizedChainComplexFunctor C).map f) := hf
  have hstd : ∀ k : ℕ, Epi (f.app (op ⦋k⦌)) :=
    normalized_reflects_epimorphism f (fun k => by
      change Epi (((normalizedChainComplexFunctor C).map f).f k)
      infer_instance)
  simpa only [SimplexCategory.mk_len] using (hstd n.unop.len)

theorem normalizedChainComplexFunctor_reflects_isomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hf : IsIso ((normalizedChainComplexFunctor C).map f)) :
    IsIso f := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  let _ : IsIso ((normalizedChainComplexFunctor C).map f) := hf
  have hstd : ∀ k : ℕ, IsIso (f.app (op ⦋k⦌)) :=
    normalized_reflects_isomorphism f (fun k => by
      change IsIso (((normalizedChainComplexFunctor C).map f).f k)
      infer_instance)
  simpa only [SimplexCategory.mk_len] using (hstd n.unop.len)

/-! ## The abstract quasi-inverse criterion -/

theorem exact_faithful_essentially_surjective_quasi_inverse
    {A : Type u} {B : Type v} [Category.{v, u} A] [Category.{u, v} B]
    [Abelian A] [Abelian B]
    (N : A ⥤ B) (S : B ⥤ A)
    (hN : exactFunctor A B N) (hS : exactFunctor B A S)
    (g : S ⋙ N ≅ 𝟭 B) (hfaithful : N.Faithful) (hessentiallySurjective : S.EssSurj) :
    N.IsEquivalence ∧ S.IsEquivalence := by
  let _ := hN
  let _ := hS
  let _ : N.Faithful := hfaithful
  have hNfull : N.Full := by
    constructor
    intro X Y f
    obtain ⟨X', ⟨eX⟩⟩ := hessentiallySurjective.mem_essImage X
    obtain ⟨Y', ⟨eY⟩⟩ := hessentiallySurjective.mem_essImage Y
    let h : X' ⟶ Y' :=
      (g.app X').inv ≫ N.map eX.hom ≫ f ≫ N.map eY.inv ≫ (g.app Y').hom
    refine ⟨eX.inv ≫ S.map h ≫ eY.hom, ?_⟩
    have hmap : N.map (S.map h) =
        (g.app X').hom ≫ h ≫ (g.app Y').inv := by
      apply (cancel_mono (g.app Y').hom).1
      simpa using (g.hom.naturality h)
    simp only [Functor.map_comp]
    rw [hmap]
    simp [h]
  have hNess : N.EssSurj := by
    constructor
    intro Y
    exact ⟨S.obj Y, ⟨g.app Y⟩⟩
  have hNeq : N.IsEquivalence :=
    { faithful := hfaithful, full := hNfull, essSurj := hNess }
  let _ : N.IsEquivalence := hNeq
  have hSNeq : (S ⋙ N).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso g).2 inferInstance
  let _ : (S ⋙ N).IsEquivalence := hSNeq
  exact ⟨hNeq, Functor.isEquivalence_of_comp_right S N⟩

/-! ## The reverse construction -/

/-- A source index in degree `X`: an epimorphism from `X` onto `[k]`. -/
abbrev DoldKanIndex (X : SimplexCategory) :=
  Σ k : Fin (X.len + 1), {α : X ⟶ ⦋k.1⦌ // Epi α}

noncomputable instance doldKanIndexFintype (X : SimplexCategory) :
    Fintype (DoldKanIndex X) := Fintype.ofFinite _

/-- The degree-`X` direct sum in the reverse Dold--Kan construction. -/
noncomputable def doldKanDegree
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (X : SimplexCategory) : C :=
  ∐ fun a : DoldKanIndex X => A.X a.1.1

@[simp]
theorem doldKanDegree_at_standard_simplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    doldKanDegree A ⦋n⦌ =
      ∐ fun a : DoldKanIndex ⦋n⦌ => A.X a.1.1 :=
  rfl

/-- The map on one source summand in the four cases of the source definition.

The `HEq` tests are needed because the target `[k]` varies with the index.
They express equality of the composite with the same-index map, or with the
last coface after dropping the index by one. -/
noncomputable def doldKanComponentMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) (b : DoldKanIndex X) :
    A.X a.1.1 ⟶ A.X b.1.1 :=
  by
    classical
    exact
      if h : a.1.1 = b.1.1 then
        if hcomp : HEq b.2.1 (f ≫ a.2.1) then
          eqToHom (congrArg A.X h)
        else 0
      else if h : a.1.1 = b.1.1 + 1 then
        if hcomp : HEq (f ≫ a.2.1)
            (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1))) then
          (-1 : ℤ) ^ a.1.1 • A.d a.1.1 b.1.1
        else 0
      else 0

theorem doldKanComponentMap_same_degree
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) (b : DoldKanIndex X)
    (hdegree : a.1.1 = b.1.1)
    (hcomp : HEq b.2.1 (f ≫ a.2.1)) :
    doldKanComponentMap A f a b = eqToHom (congrArg A.X hdegree) := by
  simp [doldKanComponentMap, hdegree, hcomp]

theorem doldKanComponentMap_drop_degree
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) (b : DoldKanIndex X)
    (hdegree : a.1.1 = b.1.1 + 1)
    (hcomp : HEq (f ≫ a.2.1)
      (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1)))) :
    doldKanComponentMap A f a b =
      (-1 : ℤ) ^ a.1.1 • A.d a.1.1 b.1.1 := by
  simp [doldKanComponentMap, hdegree, hcomp]

theorem doldKanComponentMap_zero_of_other_case
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) (b : DoldKanIndex X)
    (hdegree : a.1.1 ≠ b.1.1)
    (hdrop : a.1.1 ≠ b.1.1 + 1) :
    doldKanComponentMap A f a b = 0 := by
  simp [doldKanComponentMap, hdegree, hdrop]

private theorem doldKanComponentMap_drop_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : SimplexCategory} (A : ChainComplex C ℕ) (f : X ⟶ Y)
    (a : DoldKanIndex Y) (b : DoldKanIndex X)
    (hdegree : a.1.1 = b.1.1 + 1)
    (hcomp : ¬HEq (f ≫ a.2.1)
      (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1)))) :
    doldKanComponentMap A f a b = 0 := by
  unfold doldKanComponentMap
  split <;> simp_all

/-- The map induced by `f : X ⟶ Y`, from the `Y`-degree to the `X`-degree. -/
noncomputable def doldKanMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y) :
    doldKanDegree A Y ⟶ doldKanDegree A X :=
  Sigma.desc (fun a =>
    ∑ b : DoldKanIndex X,
      doldKanComponentMap A f a b ≫
        Sigma.ι (fun b : DoldKanIndex X => A.X b.1.1) b)

private theorem sigma_hom_ext_of_π
    {C : Type u} [Category.{v} C] [Abelian C]
    {J : Type} [Fintype J] [DecidableEq J] (F : J → C) {Z : C}
    (u w : Z ⟶ ∐ F)
    (h : ∀ j, u ≫ Sigma.π F j = w ≫ Sigma.π F j) :
    u = w := by
  classical
  let e := biproduct.isoCoproduct F
  apply (cancel_mono e.inv).1
  apply biproduct.hom_ext
  intro j
  have hp : e.inv ≫ biproduct.π F j = Sigma.π F j := by
    apply Sigma.hom_ext
    intro i
    simp [e, biproduct.isoCoproduct_inv, biproduct.ι_π, Sigma.ι_π]
  rw [Category.assoc, hp, Category.assoc, hp]
  exact h j

private theorem doldKanMap_summand
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) :
    (Sigma.ι (fun a : DoldKanIndex Y => A.X a.1.1) a :
      A.X a.1.1 ⟶ doldKanDegree A Y) ≫ doldKanMap A f =
      ∑ b : DoldKanIndex X,
        doldKanComponentMap A f a b ≫
          (Sigma.ι (fun b : DoldKanIndex X => A.X b.1.1) b :
            A.X b.1.1 ⟶ doldKanDegree A X) := by
  simp only [doldKanMap, Sigma.ι_desc]
  rfl

private theorem doldKanMap_summand_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) (d : DoldKanIndex X) :
    ((Sigma.ι (fun a : DoldKanIndex Y => A.X a.1.1) a :
      A.X a.1.1 ⟶ doldKanDegree A Y) ≫ doldKanMap A f) ≫
        (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
          doldKanDegree A X ⟶ A.X d.1.1) =
      ∑ b : DoldKanIndex X,
        (doldKanComponentMap A f a b ≫
          (Sigma.ι (fun b : DoldKanIndex X => A.X b.1.1) b :
            A.X b.1.1 ⟶ doldKanDegree A X)) ≫
          (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
            doldKanDegree A X ⟶ A.X d.1.1) := by
  have h := congrArg
    (fun q => q ≫
      (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
        doldKanDegree A X ⟶ A.X d.1.1))
    (doldKanMap_summand A f a)
  apply h.trans
  rw [Preadditive.sum_comp]

private theorem doldKanMap_component_projection
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y : SimplexCategory} (f : X ⟶ Y)
    (a : DoldKanIndex Y) (d : DoldKanIndex X) :
    ((Sigma.ι (fun a : DoldKanIndex Y => A.X a.1.1) a :
      A.X a.1.1 ⟶ doldKanDegree A Y) ≫ doldKanMap A f) ≫
        (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
          doldKanDegree A X ⟶ A.X d.1.1) =
      doldKanComponentMap A f a d := by
  rw [doldKanMap_summand_comp]
  rw [Fintype.sum_eq_single d]
  · simp
  · intro b hb
    rw [Category.assoc]
    simp [Sigma.ι_π, hb]

private theorem doldKanMap_two_summand_projection
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y Z : SimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : DoldKanIndex Z) (d : DoldKanIndex X) :
    (((Sigma.ι (fun a : DoldKanIndex Z => A.X a.1.1) a :
      A.X a.1.1 ⟶ doldKanDegree A Z) ≫ doldKanMap A g) ≫
        doldKanMap A f) ≫
      (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
        doldKanDegree A X ⟶ A.X d.1.1) =
      ∑ b : DoldKanIndex Y,
        doldKanComponentMap A g a b ≫ doldKanComponentMap A f b d := by
  rw [Category.assoc
    ((Sigma.ι (fun a : DoldKanIndex Z => A.X a.1.1) a :
      A.X a.1.1 ⟶ doldKanDegree A Z) ≫ doldKanMap A g)
    (doldKanMap A f)
    (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d)]
  have h :
      ((Sigma.ι (fun a : DoldKanIndex Z => A.X a.1.1) a :
        A.X a.1.1 ⟶ doldKanDegree A Z) ≫ doldKanMap A g) ≫
          (doldKanMap A f ≫
            (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
              doldKanDegree A X ⟶ A.X d.1.1)) =
        (∑ b : DoldKanIndex Y,
          doldKanComponentMap A g a b ≫
            (Sigma.ι (fun b : DoldKanIndex Y => A.X b.1.1) b :
              A.X b.1.1 ⟶ doldKanDegree A Y)) ≫
          (doldKanMap A f ≫
            (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
              doldKanDegree A X ⟶ A.X d.1.1)) := by
    rw [doldKanMap_summand]
    rfl
  apply h.trans
  have hsum :
      (∑ b : DoldKanIndex Y,
        doldKanComponentMap A g a b ≫
          (Sigma.ι (fun b : DoldKanIndex Y => A.X b.1.1) b :
            A.X b.1.1 ⟶ doldKanDegree A Y)) ≫
          (doldKanMap A f ≫
            (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
              doldKanDegree A X ⟶ A.X d.1.1)) =
        ∑ b : DoldKanIndex Y,
          (doldKanComponentMap A g a b ≫
            (Sigma.ι (fun b : DoldKanIndex Y => A.X b.1.1) b :
              A.X b.1.1 ⟶ doldKanDegree A Y)) ≫
            (doldKanMap A f ≫
              (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
                doldKanDegree A X ⟶ A.X d.1.1)) := by
    rw [Preadditive.sum_comp]
  apply hsum.trans
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (doldKanComponentMap A g a b ≫
        (Sigma.ι (fun b : DoldKanIndex Y => A.X b.1.1) b :
          A.X b.1.1 ⟶ doldKanDegree A Y)) ≫
        (doldKanMap A f ≫
          (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
            doldKanDegree A X ⟶ A.X d.1.1)) =
      doldKanComponentMap A g a b ≫
        (((Sigma.ι (fun b : DoldKanIndex Y => A.X b.1.1) b :
          A.X b.1.1 ⟶ doldKanDegree A Y) ≫ doldKanMap A f) ≫
            (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
              doldKanDegree A X ⟶ A.X d.1.1)) := by
          calc
            (doldKanComponentMap A g a b ≫
                (Sigma.ι (fun b : DoldKanIndex Y => A.X b.1.1) b :
                  A.X b.1.1 ⟶ doldKanDegree A Y)) ≫
                (doldKanMap A f ≫
                  (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
                    doldKanDegree A X ⟶ A.X d.1.1)) =
              doldKanComponentMap A g a b ≫
                ((Sigma.ι (fun b : DoldKanIndex Y => A.X b.1.1) b :
                  A.X b.1.1 ⟶ doldKanDegree A Y) ≫
                  (doldKanMap A f ≫
                    (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
                      doldKanDegree A X ⟶ A.X d.1.1))) :=
              Category.assoc _ _ _
            _ = doldKanComponentMap A g a b ≫
                (((Sigma.ι (fun b : DoldKanIndex Y => A.X b.1.1) b :
                  A.X b.1.1 ⟶ doldKanDegree A Y) ≫ doldKanMap A f) ≫
                  (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d :
                    doldKanDegree A X ⟶ A.X d.1.1)) := by
              exact congrArg (fun k => doldKanComponentMap A g a b ≫ k)
                (Category.assoc
                  (Sigma.ι (fun b : DoldKanIndex Y => A.X b.1.1) b)
                  (doldKanMap A f)
                  (Sigma.π (fun b : DoldKanIndex X => A.X b.1.1) d)).symm
    _ = doldKanComponentMap A g a b ≫
        doldKanComponentMap A f b d := by
      rw [doldKanMap_component_projection]

private theorem doldKanComponentMap_id_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X : SimplexCategory}
    (a b : DoldKanIndex X) (h : b ≠ a) :
    doldKanComponentMap A (𝟙 X) a b = 0 := by
  classical
  by_cases hab : a.1.1 = b.1.1
  · have hcomp : ¬HEq b.2.1 ((𝟙 X) ≫ a.2.1) := by
      intro hcomp
      have hba : b = a := by
        have hfin : b.1 = a.1 := by
          apply Fin.ext
          exact hab.symm
        have hval : HEq b.2.1 a.2.1 := by
          simpa only [Category.id_comp] using hcomp
        apply Sigma.ext
        · exact hfin
        · have hp : (fun α : X ⟶ ⦋b.1.1⦌ => Epi α) ≍
            (fun α : X ⟶ ⦋a.1.1⦌ => Epi α) := by
            have hnat : b.1.1 = a.1.1 := congrArg Fin.val hfin
            rw [hnat]
          exact (Subtype.heq_iff_coe_heq (type_eq_of_heq hval) hp).2 hval
      exact h hba
    have hcomp' : ¬HEq b.2.1 a.2.1 := by
      simpa only [Category.id_comp] using hcomp
    simp [doldKanComponentMap, hab, hcomp']
  · by_cases hdrop : a.1.1 = b.1.1 + 1
    · have hcomp : ¬HEq ((𝟙 X) ≫ a.2.1)
          (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1))) := by
        intro hcomp
        have hobj : (⦋a.1.1⦌ : SimplexCategory) =
            ⦋b.1.1 + 1⦌ :=
          congrArg (fun n : ℕ => ⦋n⦌) hdrop
        have hcomp_eq : ((𝟙 X) ≫ a.2.1) ≫ eqToHom hobj =
            b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1)) := by
          apply eq_of_heq
          exact (comp_eqToHom_heq ((𝟙 X) ≫ a.2.1) hobj).trans hcomp
        have hcomp_epi : Epi (((𝟙 X) ≫ a.2.1) ≫ eqToHom hobj) :=
          epi_comp' (epi_comp' (inferInstance : Epi (𝟙 X)) a.2.2)
            (inferInstance : Epi (eqToHom hobj))
        have hbd_epi : Epi (b.2.1 ≫
            SimplexCategory.δ (Fin.last (b.1.1 + 1))) :=
          hcomp_eq ▸ hcomp_epi
        have hδepi : Epi (SimplexCategory.δ (Fin.last (b.1.1 + 1))) :=
          @epi_of_epi _ _ _ _ _ b.2.1
            (SimplexCategory.δ (Fin.last (b.1.1 + 1))) hbd_epi
        have hlen := @SimplexCategory.len_le_of_epi _ _
          (SimplexCategory.δ (Fin.last (b.1.1 + 1))) hδepi
        dsimp at hlen
        omega
      have hcomp' : ¬HEq a.2.1
          (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1))) := by
        simpa only [Category.id_comp] using hcomp
      simp [doldKanComponentMap, hdrop, hcomp']
    · simp [doldKanComponentMap, hab, hdrop]

private theorem doldKanComponentMap_id_self
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X : SimplexCategory}
    (a : DoldKanIndex X) :
    doldKanComponentMap A (𝟙 X) a a = 𝟙 _ := by
  rw [doldKanComponentMap_same_degree A (𝟙 X) a a rfl (by simp)]
  simp

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

private theorem simplex_last_coface_heq {m n : ℕ} (h : m = n) :
    HEq (SimplexCategory.δ (Fin.last (m + 1)))
      (SimplexCategory.δ (Fin.last (n + 1))) := by
  subst n
  rfl

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
    refine ⟨q', (SimplexCategory.epi_iff_surjective).2 hq', heq_of_eq hqfac, ?_⟩
    apply (cancel_mono (SimplexCategory.δ (Fin.last (k + 1)))).1
    rw [Category.assoc, ← hqfac, h']

private theorem heq_comp_same
    {X Y Z : SimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) {k : ℕ}
    {c : Z ⟶ ⦋k⦌} {b : Y ⟶ ⦋k⦌} {d : X ⟶ ⦋k⦌}
    (h₁ : HEq b (g ≫ c)) (h₂ : HEq d (f ≫ b)) :
    HEq d ((f ≫ g) ≫ c) := by
  have h₁' : b = g ≫ c := eq_of_heq h₁
  have h₂' : d = f ≫ b := eq_of_heq h₂
  apply heq_of_eq
  calc
    d = f ≫ b := h₂'
    _ = f ≫ (g ≫ c) := by rw [h₁']
    _ = (f ≫ g) ≫ c := (Category.assoc _ _ _).symm

private theorem heq_comp_drop_right
    {X Y Z : SimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) {k : ℕ}
    {c : Z ⟶ ⦋k + 1⦌} {b : Y ⟶ ⦋k + 1⦌} {d : X ⟶ ⦋k⦌}
    (h₁ : HEq b (g ≫ c))
    (h₂ : HEq (f ≫ b) (d ≫ SimplexCategory.δ (Fin.last (k + 1)))) :
    HEq ((f ≫ g) ≫ c) (d ≫ SimplexCategory.δ (Fin.last (k + 1))) := by
  have h₁' : b = g ≫ c := eq_of_heq h₁
  have h₂' : f ≫ b = d ≫ SimplexCategory.δ (Fin.last (k + 1)) :=
    eq_of_heq h₂
  apply heq_of_eq
  calc
    (f ≫ g) ≫ c = f ≫ (g ≫ c) := Category.assoc _ _ _
    _ = f ≫ b := by rw [h₁']
    _ = d ≫ SimplexCategory.δ (Fin.last (k + 1)) := h₂'

private theorem heq_trans_explicit
    {α β γ : Sort u} {a : α} {b : β} {c : γ}
    (h₁ : HEq a b) (h₂ : HEq b c) : HEq a c :=
  HEq.trans h₁ h₂

private theorem heq_cancel_mono_trans
    {C : Type u} [Category.{v} C]
    {X Y Z X' Y' Z' : C}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    {W W' : C} (m : W ⟶ W')
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (hg : HEq g g') (h₁ : HEq (f ≫ g) m)
    (h₂ : HEq m (f' ≫ g')) [Mono g] : HEq f f' := by
  cases hX
  cases hY
  cases hZ
  have hgg : g = g' := eq_of_heq hg
  have hcomp : f ≫ g = f' ≫ g' :=
    eq_of_heq (heq_trans_explicit h₁ h₂)
  apply heq_of_eq
  apply (cancel_mono g).1
  simpa [hgg] using hcomp

private theorem doldKanComponentMap_comp_sum_gap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y Z : SimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : DoldKanIndex Z) (d : DoldKanIndex X)
    (h₀ : c.1.1 ≠ d.1.1) (h₁ : c.1.1 ≠ d.1.1 + 1) :
    (∑ b : DoldKanIndex Y,
      doldKanComponentMap A g c b ≫ doldKanComponentMap A f b d) = 0 := by
  classical
  rw [Fintype.sum_eq_zero]
  intro b
  by_cases hcb : c.1.1 = b.1.1
  · by_cases hbd : b.1.1 = d.1.1
    · exfalso
      apply h₀
      omega
    · by_cases hbdrop : b.1.1 = d.1.1 + 1
      · exfalso
        apply h₁
        omega
      · rw [doldKanComponentMap_zero_of_other_case A f b d hbd hbdrop, comp_zero]
  · by_cases hcbdrop : c.1.1 = b.1.1 + 1
    · by_cases hbd : b.1.1 = d.1.1
      · exfalso
        apply h₁
        omega
      · by_cases hbdrop : b.1.1 = d.1.1 + 1
        · by_cases hgc : HEq (g ≫ c.2.1)
              (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1)))
          · by_cases hfd : HEq (f ≫ b.2.1)
                (d.2.1 ≫ SimplexCategory.δ (Fin.last (d.1.1 + 1)))
            · rw [doldKanComponentMap_drop_degree A g c b hcbdrop hgc]
              rw [doldKanComponentMap_drop_degree A f b d hbdrop hfd]
              simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
                HomologicalComplex.d_comp_d]
              simp
            · have hfzero : doldKanComponentMap A f b d = 0 :=
                doldKanComponentMap_drop_zero A f b d hbdrop hfd
              simp [hfzero]
          · have hgzero : doldKanComponentMap A g c b = 0 :=
              doldKanComponentMap_drop_zero A g c b hcbdrop hgc
            simp [hgzero]
        · simp [doldKanComponentMap_zero_of_other_case A f b d hbd hbdrop]
    · simp [doldKanComponentMap_zero_of_other_case A g c b hcb hcbdrop]

private theorem doldKanComponentMap_comp_sum_same_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y Z : SimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : DoldKanIndex Z) (d : DoldKanIndex X)
    (hcd : c.1.1 = d.1.1)
    (hcomp : ¬HEq d.2.1 ((f ≫ g) ≫ c.2.1)) :
    (∑ b : DoldKanIndex Y,
      doldKanComponentMap A g c b ≫ doldKanComponentMap A f b d) = 0 := by
  classical
  rw [Fintype.sum_eq_zero]
  intro b
  by_cases hcb : c.1.1 = b.1.1
  · by_cases hgb : HEq b.2.1 (g ≫ c.2.1)
    · by_cases hbd : b.1.1 = d.1.1
      · by_cases hfd : HEq d.2.1 (f ≫ b.2.1)
        · exfalso
          apply hcomp
          have hbcobj : (⦋b.1.1⦌ : SimplexCategory) = ⦋c.1.1⦌ :=
            (congrArg (fun n : ℕ => ⦋n⦌) hcb).symm
          have h₁ : HEq (f ≫ b.2.1) (f ≫ (g ≫ c.2.1)) := by
            exact heq_comp rfl rfl hbcobj HEq.rfl hgb
          have h₂ : HEq ((f ≫ g) ≫ c.2.1)
              (f ≫ (g ≫ c.2.1)) := heq_of_eq (Category.assoc _ _ _)
          exact hfd.trans (h₁.trans h₂.symm)
        · rw [show doldKanComponentMap A f b d = 0 by
            simp [doldKanComponentMap, hbd, hfd], comp_zero]
      · by_cases hbdrop : b.1.1 = d.1.1 + 1
        · exfalso
          omega
        · rw [doldKanComponentMap_zero_of_other_case A f b d hbd hbdrop,
            comp_zero]
    · rw [show doldKanComponentMap A g c b = 0 by
        simp [doldKanComponentMap, hcb, hgb], zero_comp]
  · by_cases hcbdrop : c.1.1 = b.1.1 + 1
    · by_cases hbd : b.1.1 = d.1.1
      · exfalso
        omega
      · by_cases hbdrop : b.1.1 = d.1.1 + 1
        · exfalso
          omega
        · rw [doldKanComponentMap_zero_of_other_case A f b d hbd hbdrop,
            comp_zero]
    · rw [doldKanComponentMap_zero_of_other_case A g c b hcb hcbdrop,
        zero_comp]

private theorem doldKanComponentMap_comp_sum_same
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y Z : SimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : DoldKanIndex Z) (d : DoldKanIndex X)
    (hcd : c.1.1 = d.1.1)
    (hcomp : HEq d.2.1 ((f ≫ g) ≫ c.2.1)) :
    (∑ b : DoldKanIndex Y,
      doldKanComponentMap A g c b ≫ doldKanComponentMap A f b d) =
      doldKanComponentMap A (f ≫ g) c d := by
  classical
  have hd_epi : Epi d.2.1 := d.2.2
  have hobj : (⦋c.1.1⦌ : SimplexCategory) = ⦋d.1.1⦌ :=
    congrArg (fun n : ℕ => ⦋n⦌) hcd
  have hcomp_eq : d.2.1 =
      ((f ≫ g) ≫ c.2.1) ≫ eqToHom hobj := by
    apply eq_of_heq
    exact hcomp.trans (comp_eqToHom_heq ((f ≫ g) ≫ c.2.1) hobj).symm
  have hcomp_eq_epi : Epi (((f ≫ g) ≫ c.2.1) ≫ eqToHom hobj) :=
    hcomp_eq ▸ hd_epi
  have hcomp_epi : Epi ((f ≫ g) ≫ c.2.1) :=
    (epi_comp_iff_of_isIso ((f ≫ g) ≫ c.2.1) (eqToHom hobj)).1 hcomp_eq_epi
  have hassoc_epi : Epi (f ≫ (g ≫ c.2.1)) := by
    simpa only [Category.assoc] using hcomp_epi
  let q := g ≫ c.2.1
  have hq_epi : Epi q := simplex_epi_of_comp_epi f q hassoc_epi
  let kY : Fin (Y.len + 1) :=
    ⟨c.1.1, by
      have hlen := @SimplexCategory.len_le_of_epi _ _ q hq_epi
      dsimp [q] at hlen ⊢
      omega⟩
  let b₀ : DoldKanIndex Y := ⟨kY, ⟨q, hq_epi⟩⟩
  rw [Fintype.sum_eq_single b₀]
  · have hgb : HEq b₀.2.1 (g ≫ c.2.1) := by rfl
    have hfd : HEq d.2.1 (f ≫ b₀.2.1) := by
      simpa only [b₀, q, Category.assoc, hcd] using hcomp
    rw [doldKanComponentMap_same_degree A g c b₀ (by rfl) hgb,
      doldKanComponentMap_same_degree A f b₀ d
        (by simp [b₀, kY, hcd]) hfd]
    rw [doldKanComponentMap_same_degree A (f ≫ g) c d hcd hcomp]
    simp
  · intro b hb
    by_cases hcb : c.1.1 = b.1.1
    · by_cases hgb : HEq b.2.1 (g ≫ c.2.1)
      · have hbb₀ : b = b₀ := by
          apply Sigma.ext
          · apply Fin.ext
            change b.1.1 = c.1.1
            exact hcb.symm
          · have hval : HEq b.2.1 b₀.2.1 := by
              simpa [b₀, q] using hgb
            have hnat : b.1.1 = b₀.1.1 := by
              change b.1.1 = c.1.1
              exact hcb.symm
            have hp : (fun α : Y ⟶ ⦋b.1.1⦌ => Epi α) ≍
                (fun α : Y ⟶ ⦋b₀.1.1⦌ => Epi α) := by
              rw [hnat]
            exact (Subtype.heq_iff_coe_heq (type_eq_of_heq hval) hp).2 hval
        exact (hb hbb₀).elim
      · rw [show doldKanComponentMap A g c b = 0 by
          simp [doldKanComponentMap, hcb, hgb], zero_comp]
    · by_cases hcbdrop : c.1.1 = b.1.1 + 1
      · by_cases hbd : b.1.1 = d.1.1
        · exfalso
          omega
        · by_cases hbdrop : b.1.1 = d.1.1 + 1
          · exfalso
            omega
          · rw [doldKanComponentMap_zero_of_other_case A f b d hbd hbdrop,
              comp_zero]
      · rw [doldKanComponentMap_zero_of_other_case A g c b hcb hcbdrop,
          zero_comp]
private theorem doldKanComponentMap_comp_sum_drop_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y Z : SimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : DoldKanIndex Z) (d : DoldKanIndex X)
    (hcd : c.1.1 = d.1.1 + 1)
    (hcomp : ¬HEq ((f ≫ g) ≫ c.2.1)
      (d.2.1 ≫ SimplexCategory.δ (Fin.last (d.1.1 + 1)))) :
    (∑ b : DoldKanIndex Y,
      doldKanComponentMap A g c b ≫ doldKanComponentMap A f b d) = 0 := by
  classical
  rw [Fintype.sum_eq_zero]
  intro b
  by_cases hcb : c.1.1 = b.1.1
  · by_cases hgb : HEq b.2.1 (g ≫ c.2.1)
    · by_cases hbd : b.1.1 = d.1.1
      · exfalso
        omega
      · by_cases hbdrop : b.1.1 = d.1.1 + 1
        · by_cases hfd : HEq (f ≫ b.2.1)
              (d.2.1 ≫ SimplexCategory.δ (Fin.last (d.1.1 + 1)))
          · exfalso
            apply hcomp
            have hbcobj : (⦋b.1.1⦌ : SimplexCategory) = ⦋c.1.1⦌ :=
              (congrArg (fun n : ℕ => ⦋n⦌) hcb).symm
            have h₁ : HEq (f ≫ b.2.1) (f ≫ (g ≫ c.2.1)) := by
              exact heq_comp rfl rfl hbcobj HEq.rfl hgb
            have h₂ : HEq ((f ≫ g) ≫ c.2.1)
                (f ≫ (g ≫ c.2.1)) := heq_of_eq (Category.assoc _ _ _)
            exact h₂.trans (h₁.symm.trans hfd)
          · rw [show doldKanComponentMap A f b d = 0 by
              exact doldKanComponentMap_drop_zero A f b d hbdrop hfd, comp_zero]
        · rw [doldKanComponentMap_zero_of_other_case A f b d hbd hbdrop,
            comp_zero]
    · rw [show doldKanComponentMap A g c b = 0 by
        simp [doldKanComponentMap, hcb, hgb], zero_comp]
  · by_cases hcbdrop : c.1.1 = b.1.1 + 1
    · by_cases hbd : b.1.1 = d.1.1
      · by_cases hgc : HEq (g ≫ c.2.1)
            (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1)))
        · by_cases hfd : HEq d.2.1 (f ≫ b.2.1)
          · exfalso
            apply hcomp
            have hcbobj : (⦋c.1.1⦌ : SimplexCategory) =
                ⦋b.1.1 + 1⦌ := congrArg (fun n : ℕ => ⦋n⦌) hcbdrop
            have hbdobj : (⦋b.1.1⦌ : SimplexCategory) = ⦋d.1.1⦌ :=
              congrArg (fun n : ℕ => ⦋n⦌) hbd
            have hbdplus : (⦋b.1.1 + 1⦌ : SimplexCategory) =
                ⦋d.1.1 + 1⦌ := congrArg (fun n : ℕ => ⦋n + 1⦌) hbd
            have h₁ : HEq (f ≫ (g ≫ c.2.1))
                (f ≫ (b.2.1 ≫
                  SimplexCategory.δ (Fin.last (b.1.1 + 1)))) :=
              heq_comp rfl rfl hcbobj HEq.rfl hgc
            have h₂ : HEq ((f ≫ b.2.1) ≫
                SimplexCategory.δ (Fin.last (b.1.1 + 1)))
                (d.2.1 ≫ SimplexCategory.δ (Fin.last (d.1.1 + 1))) :=
              heq_comp rfl hbdobj hbdplus hfd.symm
                (simplex_last_coface_heq hbd)
            have h₃ : HEq ((f ≫ g) ≫ c.2.1)
                (f ≫ (g ≫ c.2.1)) := heq_of_eq (Category.assoc _ _ _)
            have h₄ : HEq (f ≫ (b.2.1 ≫
                SimplexCategory.δ (Fin.last (b.1.1 + 1))))
                ((f ≫ b.2.1) ≫
                  SimplexCategory.δ (Fin.last (b.1.1 + 1))) :=
              heq_of_eq (Category.assoc _ _ _).symm
            exact h₃.trans (h₁.trans (h₄.trans h₂))
          · rw [show doldKanComponentMap A f b d = 0 by
              simp [doldKanComponentMap, hbd, hfd], comp_zero]
        · rw [show doldKanComponentMap A g c b = 0 by
            exact doldKanComponentMap_drop_zero A g c b hcbdrop hgc, zero_comp]
      · by_cases hbdrop : b.1.1 = d.1.1 + 1
        · exfalso
          omega
        · rw [doldKanComponentMap_zero_of_other_case A f b d hbd hbdrop,
            comp_zero]
    · rw [doldKanComponentMap_zero_of_other_case A g c b hcb hcbdrop,
        zero_comp]

private theorem doldKanComponentMap_comp_sum_drop
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y Z : SimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : DoldKanIndex Z) (d : DoldKanIndex X)
    (hcd : c.1.1 = d.1.1 + 1)
    (hcomp : HEq ((f ≫ g) ≫ c.2.1)
      (d.2.1 ≫ SimplexCategory.δ (Fin.last (d.1.1 + 1)))) :
    (∑ b : DoldKanIndex Y,
      doldKanComponentMap A g c b ≫ doldKanComponentMap A f b d) =
      doldKanComponentMap A (f ≫ g) c d := by
  classical
  have hfac : HEq (f ≫ (g ≫ c.2.1))
      (d.2.1 ≫ SimplexCategory.δ (Fin.last (d.1.1 + 1))) := by
    simpa only [Category.assoc] using hcomp
  let q := g ≫ c.2.1
  by_cases hq : Epi q
  · have hq_epi : Epi q := hq
    let kY : Fin (Y.len + 1) :=
      ⟨c.1.1, by
        have hlen := @SimplexCategory.len_le_of_epi _ _ q hq_epi
        dsimp [q] at hlen ⊢
        omega⟩
    let b₀ : DoldKanIndex Y := ⟨kY, ⟨q, hq_epi⟩⟩
    rw [Fintype.sum_eq_single b₀]
    · have hgb : HEq b₀.2.1 (g ≫ c.2.1) := by rfl
      have hfd : HEq (f ≫ b₀.2.1)
          (d.2.1 ≫ SimplexCategory.δ (Fin.last (d.1.1 + 1))) := by
        simpa only [b₀, q, Category.assoc] using hfac
      rw [doldKanComponentMap_same_degree A g c b₀ (by rfl) hgb,
        doldKanComponentMap_drop_degree A f b₀ d
          (by simp [b₀, kY, hcd]) hfd,
        doldKanComponentMap_drop_degree A (f ≫ g) c d hcd hcomp]
      simp [b₀, kY, hcd]
    · intro b hb
      by_cases hcb : c.1.1 = b.1.1
      · by_cases hgb : HEq b.2.1 (g ≫ c.2.1)
        · have hbb₀ : b = b₀ := by
            apply Sigma.ext
            · apply Fin.ext
              change b.1.1 = c.1.1
              exact hcb.symm
            · have hval : HEq b.2.1 b₀.2.1 := by
                simpa [b₀, q] using hgb
              have hnat : b.1.1 = b₀.1.1 := by
                change b.1.1 = c.1.1
                exact hcb.symm
              have hp : (fun α : Y ⟶ ⦋b.1.1⦌ => Epi α) ≍
                  (fun α : Y ⟶ ⦋b₀.1.1⦌ => Epi α) := by
                rw [hnat]
              exact (Subtype.heq_iff_coe_heq (type_eq_of_heq hval) hp).2 hval
          exact (hb hbb₀).elim
        · rw [show doldKanComponentMap A g c b = 0 by
            simp [doldKanComponentMap, hcb, hgb], zero_comp]
      · by_cases hcbdrop : c.1.1 = b.1.1 + 1
        · by_cases hbd : b.1.1 = d.1.1
          · by_cases hgc : HEq (g ≫ c.2.1)
                (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1)))
            · have hδepi : Epi (SimplexCategory.δ (Fin.last (b.1.1 + 1))) := by
                have hobj : (⦋c.1.1⦌ : SimplexCategory) =
                    ⦋b.1.1 + 1⦌ := congrArg (fun n : ℕ => ⦋n⦌) hcbdrop
                have hqeq : q ≫ eqToHom hobj =
                    b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1)) := by
                  apply eq_of_heq
                  exact (comp_eqToHom_heq q hobj).trans hgc
                have hqeq_epi : Epi (q ≫ eqToHom hobj) :=
                  epi_comp' hq (inferInstance : Epi (eqToHom hobj))
                have hbd_epi : Epi (b.2.1 ≫
                    SimplexCategory.δ (Fin.last (b.1.1 + 1))) :=
                  hqeq ▸ hqeq_epi
                exact @epi_of_epi _ _ _ _ _ b.2.1
                  (SimplexCategory.δ (Fin.last (b.1.1 + 1))) hbd_epi
              have hlen := @SimplexCategory.len_le_of_epi _ _
                (SimplexCategory.δ (Fin.last (b.1.1 + 1))) hδepi
              dsimp at hlen
              omega
            · rw [show doldKanComponentMap A g c b = 0 by
                exact doldKanComponentMap_drop_zero A g c b hcbdrop hgc, zero_comp]
          · by_cases hbdrop : b.1.1 = d.1.1 + 1
            · exfalso
              omega
            · rw [doldKanComponentMap_zero_of_other_case A f b d hbd hbdrop,
                comp_zero]
        · rw [doldKanComponentMap_zero_of_other_case A g c b hcb hcbdrop,
            zero_comp]
  · rcases simplex_last_factorization f q d.2.1 d.2.2 hcd hfac with hq' | hq'
    · exact (hq hq').elim
    · rcases hq' with ⟨q', hq', hqfac, hfq⟩
      let kY : Fin (Y.len + 1) :=
        ⟨d.1.1, by
          have hlen := @SimplexCategory.len_le_of_epi _ _ q' hq'
          dsimp at hlen ⊢
          omega⟩
      let b₀ : DoldKanIndex Y := ⟨kY, ⟨q', hq'⟩⟩
      rw [Fintype.sum_eq_single b₀]
      · have hgc : HEq (g ≫ c.2.1)
            (b₀.2.1 ≫ SimplexCategory.δ (Fin.last (d.1.1 + 1))) := by
          simpa only [b₀, q] using hqfac
        have hfd : HEq d.2.1 (f ≫ b₀.2.1) := by
          simpa only [b₀] using heq_of_eq hfq.symm
        rw [doldKanComponentMap_drop_degree A g c b₀ hcd hgc,
          doldKanComponentMap_same_degree A f b₀ d (by rfl) hfd,
          doldKanComponentMap_drop_degree A (f ≫ g) c d hcd hcomp]
        simp [b₀, kY]
      · intro b hb
        by_cases hcb : c.1.1 = b.1.1
        · by_cases hgb : HEq b.2.1 (g ≫ c.2.1)
          · have hqepi : Epi q := by
              have hobj : (⦋b.1.1⦌ : SimplexCategory) = ⦋c.1.1⦌ :=
                (congrArg (fun n : ℕ => ⦋n⦌) hcb).symm
              have hbq : b.2.1 = q ≫ eqToHom hobj.symm := by
                apply eq_of_heq
                exact hgb.trans (comp_eqToHom_heq q hobj.symm).symm
              have hqeq_epi : Epi (q ≫ eqToHom hobj.symm) :=
                hbq ▸ b.2.2
              exact (epi_comp_iff_of_isIso q (eqToHom hobj.symm)).1 hqeq_epi
            exact (hq hqepi).elim
          · rw [show doldKanComponentMap A g c b = 0 by
              simp [doldKanComponentMap, hcb, hgb], zero_comp]
        · by_cases hcbdrop : c.1.1 = b.1.1 + 1
          · by_cases hbd : b.1.1 = d.1.1
            · by_cases hgc : HEq (g ≫ c.2.1)
                  (b.2.1 ≫ SimplexCategory.δ (Fin.last (b.1.1 + 1)))
              · have hbb₀ : b = b₀ := by
                  apply Sigma.ext
                  · apply Fin.ext
                    change b.1.1 = d.1.1
                    exact hbd
                  · have hqfac' : HEq (g ≫ c.2.1)
                        (b₀.2.1 ≫
                          SimplexCategory.δ (Fin.last (d.1.1 + 1))) := by
                      simpa only [b₀, q] using hqfac
                    have hbdobj : (⦋b.1.1⦌ : SimplexCategory) = ⦋d.1.1⦌ :=
                      congrArg (fun n : ℕ => ⦋n⦌) hbd
                    have hbdplus : (⦋b.1.1 + 1⦌ : SimplexCategory) =
                        ⦋d.1.1 + 1⦌ := congrArg (fun n : ℕ => ⦋n + 1⦌) hbd
                    have hbeq : HEq b.2.1 b₀.2.1 := by
                      apply heq_cancel_mono_trans
                        b.2.1
                        (SimplexCategory.δ (Fin.last (b.1.1 + 1)))
                        b₀.2.1
                        (SimplexCategory.δ (Fin.last (d.1.1 + 1)))
                        (g ≫ c.2.1) rfl hbdobj hbdplus
                        (simplex_last_coface_heq hbd)
                      · exact hgc.symm
                      · exact hqfac'
                    have hnat : b.1.1 = b₀.1.1 := by
                      change b.1.1 = d.1.1
                      exact hbd
                    have hp : (fun α : Y ⟶ ⦋b.1.1⦌ => Epi α) ≍
                        (fun α : Y ⟶ ⦋b₀.1.1⦌ => Epi α) := by
                      rw [hnat]
                    exact (Subtype.heq_iff_coe_heq (type_eq_of_heq hbeq) hp).2 hbeq
                exact (hb hbb₀).elim
              · rw [show doldKanComponentMap A g c b = 0 by
                  exact doldKanComponentMap_drop_zero A g c b hcbdrop hgc, zero_comp]
            · by_cases hbdrop : b.1.1 = d.1.1 + 1
              · exfalso
                omega
              · rw [doldKanComponentMap_zero_of_other_case A f b d hbd hbdrop,
                  comp_zero]
          · rw [doldKanComponentMap_zero_of_other_case A g c b hcb hcbdrop,
              zero_comp]

theorem doldKanMap_id
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (X : SimplexCategory) :
    doldKanMap A (𝟙 X) = 𝟙 (doldKanDegree A X) := by
  classical
  apply Sigma.hom_ext
  intro a
  rw [doldKanMap_summand]
  rw [Fintype.sum_eq_single a]
  · rw [doldKanComponentMap_id_self, Category.id_comp]
    change Sigma.ι (fun b : DoldKanIndex X => A.X b.1.1) a =
      Sigma.ι (fun b : DoldKanIndex X => A.X b.1.1) a ≫
        𝟙 (∐ fun b : DoldKanIndex X => A.X b.1.1)
    rw [Category.comp_id]
  · intro b hb
    rw [doldKanComponentMap_id_zero A a b hb, zero_comp]

theorem doldKanMap_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) {X Y Z : SimplexCategory}
  (f : X ⟶ Y) (g : Y ⟶ Z) :
    doldKanMap A (f ≫ g) = doldKanMap A g ≫ doldKanMap A f := by
  classical
  apply Sigma.hom_ext
  intro c
  change (Sigma.ι (fun b : DoldKanIndex Z => A.X b.1.1) c ≫
      doldKanMap A (f ≫ g) :
        A.X c.1.1 ⟶ ∐ fun a : DoldKanIndex X => A.X a.1.1) =
    (Sigma.ι (fun b : DoldKanIndex Z => A.X b.1.1) c ≫
      (doldKanMap A g ≫ doldKanMap A f) :
        A.X c.1.1 ⟶ ∐ fun a : DoldKanIndex X => A.X a.1.1)
  apply sigma_hom_ext_of_π (fun a : DoldKanIndex X => A.X a.1.1)
  intro d
  change ((Sigma.ι (fun b : DoldKanIndex Z => A.X b.1.1) c :
      A.X c.1.1 ⟶ doldKanDegree A Z) ≫ doldKanMap A (f ≫ g)) ≫
      (Sigma.π (fun a : DoldKanIndex X => A.X a.1.1) d :
        doldKanDegree A X ⟶ A.X d.1.1) =
    ((Sigma.ι (fun b : DoldKanIndex Z => A.X b.1.1) c :
      A.X c.1.1 ⟶ doldKanDegree A Z) ≫
      (doldKanMap A g ≫ doldKanMap A f)) ≫
      (Sigma.π (fun a : DoldKanIndex X => A.X a.1.1) d :
        doldKanDegree A X ⟶ A.X d.1.1)
  rw [← Category.assoc
    (Sigma.ι (fun b : DoldKanIndex Z => A.X b.1.1) c)
    (doldKanMap A g) (doldKanMap A f)]
  rw [doldKanMap_component_projection]
  rw [doldKanMap_two_summand_projection]
  by_cases hdegree : c.1.1 = d.1.1
  · by_cases hcomp : HEq d.2.1 ((f ≫ g) ≫ c.2.1)
    · exact (doldKanComponentMap_comp_sum_same A f g c d hdegree hcomp).symm
    · have hz : doldKanComponentMap A (f ≫ g) c d = 0 := by
        have hcomp' : ¬HEq d.2.1 (f ≫ (g ≫ c.2.1)) := by
          simpa only [Category.assoc] using hcomp
        simp [doldKanComponentMap, hdegree, hcomp']
      rw [hz]
      exact (doldKanComponentMap_comp_sum_same_zero A f g c d hdegree hcomp).symm
  · by_cases hdrop : c.1.1 = d.1.1 + 1
    · by_cases hcomp : HEq ((f ≫ g) ≫ c.2.1)
          (d.2.1 ≫ SimplexCategory.δ (Fin.last (d.1.1 + 1)))
      · exact (doldKanComponentMap_comp_sum_drop A f g c d hdrop hcomp).symm
      · have hz : doldKanComponentMap A (f ≫ g) c d = 0 := by
          exact doldKanComponentMap_drop_zero A (f ≫ g) c d hdrop hcomp
        rw [hz]
        exact (doldKanComponentMap_comp_sum_drop_zero A f g c d hdrop hcomp).symm
    · have hz : doldKanComponentMap A (f ≫ g) c d = 0 := by
        exact doldKanComponentMap_zero_of_other_case A (f ≫ g) c d hdegree hdrop
      rw [hz]
      exact (doldKanComponentMap_comp_sum_gap A f g c d hdegree hdrop).symm

/-- The simplicial object `S(A_•)` from the source's reverse construction. -/
noncomputable def doldKanSimplicialObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) : SimplicialObject C where
  obj X := doldKanDegree A X.unop
  map {X Y} f := doldKanMap A f.unop
  map_id X := doldKanMap_id A X.unop
  map_comp f g := by
    change doldKanMap A (g.unop ≫ f.unop) =
      doldKanMap A f.unop ≫ doldKanMap A g.unop
    exact doldKanMap_comp A g.unop f.unop

@[simp]
theorem doldKanSimplicialObject_obj
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    (doldKanSimplicialObject A).obj (op ⦋n⦌) = doldKanDegree A ⦋n⦌ :=
  rfl

/-! ## The identity and degenerate summands -/

/-- The index in degree `n` represented by `id_[n]`. -/
def doldKanIdentityIndex (n : ℕ) : DoldKanIndex ⦋n⦌ :=
  ⟨⟨n, Nat.lt_succ_self n⟩, ⟨𝟙 _, inferInstance⟩⟩

abbrev DoldKanDegenerateIndex (n : ℕ) :=
  {a : DoldKanIndex ⦋n⦌ // a.1.1 < n}

noncomputable instance doldKanDegenerateIndexFintype (n : ℕ) :
    Fintype (DoldKanDegenerateIndex n) := Fintype.ofFinite _

noncomputable def doldKanDegenerateDegree
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) : C :=
  ∐ fun a : DoldKanDegenerateIndex n => A.X a.1.1.1

/-- The inclusion of the source's degenerate summands into the full degree. -/
noncomputable def doldKanDegenerateInclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    doldKanDegenerateDegree A n ⟶ doldKanDegree A ⦋n⦌ :=
  Sigma.desc (fun a =>
    Sigma.ι (fun b : DoldKanIndex ⦋n⦌ => A.X b.1.1) a.1)

noncomputable def doldKanIdentitySummand
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    A.X n ⟶ doldKanDegree A ⦋n⦌ :=
  Sigma.ι (fun a : DoldKanIndex ⦋n⦌ => A.X a.1.1) (doldKanIdentityIndex n)

theorem doldKanIndex_eq_identity_of_degree_ge
    {n : ℕ} (a : DoldKanIndex ⦋n⦌) (h : n ≤ a.1.1) :
    a = doldKanIdentityIndex n := by
  rcases a with ⟨⟨k, hk⟩, α⟩
  change n ≤ k at h
  change k < n + 1 at hk
  have hk' : k = n := by omega
  subst k
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · apply heq_of_eq
    apply Subtype.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.eq_id_of_injective
    have hsurj : Function.Surjective α.val.toOrderHom :=
      (SimplexCategory.epi_iff_surjective).1 α.property
    simpa only [SimplexCategory.len_mk] using
      (Finite.injective_iff_surjective.mpr hsurj)

theorem doldKanIndex_degree_ge_iff_identity
    {n : ℕ} (a : DoldKanIndex ⦋n⦌) :
    n ≤ a.1.1 ↔ a = doldKanIdentityIndex n := by
  constructor
  · exact doldKanIndex_eq_identity_of_degree_ge a
  · intro h
    rw [h]
    rfl

theorem doldKan_identity_degenerate_decomposition
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    Nonempty (doldKanDegree A ⦋n⦌ ≅
      A.X n ⊞ doldKanDegenerateDegree A n) := by
  sorry

/-- The differential on the identity summand described in the source. -/
def doldKanIdentityDifferential
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    A.X (n + 1) ⟶ A.X n :=
  (-1 : ℤ) ^ (n + 1) • A.d (n + 1) n

theorem doldKanIdentitySummand_face_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) (i : Fin (n + 2))
    (hi : i ≠ Fin.last (n + 1)) :
    doldKanIdentitySummand A (n + 1) ≫
        doldKanMap A (SimplexCategory.δ i) = 0 := by
  sorry

theorem doldKanIdentitySummand_last_face
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    doldKanIdentitySummand A (n + 1) ≫
        doldKanMap A (SimplexCategory.δ (Fin.last (n + 1))) =
      doldKanIdentityDifferential A n ≫ doldKanIdentitySummand A n := by
  sorry

theorem doldKan_normalized_degree_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    Nonempty (normalizedObject (doldKanSimplicialObject A) n ≅ A.X n) := by
  sorry

theorem doldKan_normalized_differential_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (n : ℕ) :
    ∃ (e₁ : normalizedObject (doldKanSimplicialObject A) (n + 1) ≅ A.X (n + 1))
      (e₀ : normalizedObject (doldKanSimplicialObject A) n ≅ A.X n),
      e₁.inv ≫ (normalizedChainComplex (doldKanSimplicialObject A)).d (n + 1) n ≫
          e₀.hom = doldKanIdentityDifferential A n := by
  sorry

theorem doldKan_normalized_identity_differential
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) :
    Nonempty (normalizedChainComplex (doldKanSimplicialObject A) ≅ A) := by
  sorry

/-! ## Functoriality in the chain complex -/

/-- The degreewise map induced by a chain map on the reverse construction. -/
noncomputable def doldKanChainMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℕ} (f : A ⟶ B) (X : SimplexCategory) :
    doldKanDegree A X ⟶ doldKanDegree B X :=
  Sigma.desc (fun a =>
    f.f a.1.1 ≫ Sigma.ι (fun b : DoldKanIndex X => B.X b.1.1) a)

theorem doldKanChainMap_id
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) (X : SimplexCategory) :
    doldKanChainMap (𝟙 A) X = 𝟙 (doldKanDegree A X) := by
  sorry

theorem doldKanChainMap_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : ChainComplex C ℕ} (f : A ⟶ B) (g : B ⟶ D)
    (X : SimplexCategory) :
    doldKanChainMap (f ≫ g) X =
      doldKanChainMap f X ≫ doldKanChainMap g X := by
  sorry

theorem doldKanChainMap_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℕ} (f : A ⟶ B)
    {X Y : SimplexCategory} (g : X ⟶ Y) :
    doldKanMap A g ≫ doldKanChainMap f X =
      doldKanChainMap f Y ≫ doldKanMap B g := by
  sorry

/-! ## The comparison `S(N(U)) ⟶ U` -/

/-- The source's summandwise map from `S(N(U))` to `U`. -/
noncomputable def normalizedDoldKanComparisonComponent
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (X : SimplexCategory) :
    doldKanDegree (normalizedChainComplex U) X ⟶ U.obj (op X) :=
  Sigma.desc (fun a =>
    (normalizedSubobject U a.1.1).arrow ≫ U.map a.2.1.op)

theorem normalizedDoldKanComparison_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) {X Y : SimplexCategory} (f : X ⟶ Y) :
    doldKanMap (normalizedChainComplex U) f ≫
        normalizedDoldKanComparisonComponent U X =
      normalizedDoldKanComparisonComponent U Y ≫ U.map f.op := by
  sorry

/-- The natural map `S(N(U)) ⟶ U` used in the proof of Dold--Kan. -/
def normalizedDoldKanComparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    doldKanSimplicialObject (normalizedChainComplex U) ⟶ U :=
  { app := fun X => normalizedDoldKanComparisonComponent U X.unop
    naturality := by
      intro X Y f
      exact normalizedDoldKanComparison_naturality U f.unop }

@[simp]
theorem normalizedDoldKanComparison_app_standard
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (normalizedDoldKanComparison U).app (op ⦋n⦌) =
      normalizedDoldKanComparisonComponent U ⦋n⦌ :=
  rfl

theorem normalizedDoldKanComparison_isIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    IsIso (normalizedDoldKanComparison U) := by
  sorry

/-- The reverse Dold--Kan functor on chain complexes. -/
def doldKanExtension
    (C : Type u) [Category.{v} C] [Abelian C] :
    ChainComplex C ℕ ⥤ SimplicialObject C where
  obj A := doldKanSimplicialObject A
  map f :=
    { app := fun X => doldKanChainMap f X.unop
      naturality := by
        intro X Y g
        exact doldKanChainMap_naturality f g.unop }
  map_id A := by
    ext X
    exact doldKanChainMap_id A X.unop
  map_comp f g := by
    ext X
    exact doldKanChainMap_comp f g X.unop

theorem doldKanExtension_exact
    {C : Type u} [Category.{v} C] [Abelian C] :
    exactFunctor (ChainComplex C ℕ) (SimplicialObject C)
      (doldKanExtension C) := by
  sorry

@[simp]
theorem doldKanExtension_obj
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℕ) :
    (doldKanExtension C).obj A = doldKanSimplicialObject A :=
  rfl

/-! ## The normalization functor and the Dold--Kan equivalence -/

theorem doldKan_normalization_is_equivalence
    {C : Type u} [Category.{v} C] [Abelian C] :
    (normalizedChainComplexFunctor C).IsEquivalence := by
  sorry

theorem doldKan_extension_is_equivalence
    {C : Type u} [Category.{v} C] [Abelian C] :
    (doldKanExtension C).IsEquivalence := by
  sorry

theorem doldKan_extension_normalization_iso_exists
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (doldKanExtension C ⋙ normalizedChainComplexFunctor C ≅
      𝟭 (ChainComplex C ℕ)) := by
  sorry

theorem normalization_doldKan_extension_iso_exists
    {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (normalizedChainComplexFunctor C ⋙ doldKanExtension C ≅
      𝟭 (SimplicialObject C)) := by
  sorry

/-- A categorical equivalence realizing the Dold--Kan theorem. -/
noncomputable def doldKanEquivalence
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimplicialObject C ≌ ChainComplex C ℕ := by
  letI : (normalizedChainComplexFunctor C).IsEquivalence :=
    doldKan_normalization_is_equivalence
  exact (normalizedChainComplexFunctor C).asEquivalence

end Formalization.Books.Simplicial.Unit24
