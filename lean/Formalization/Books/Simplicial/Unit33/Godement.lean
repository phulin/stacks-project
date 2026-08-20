import Formalization.Books.Simplicial.Unit20.Augmentations
import Formalization.Books.Simplicial.Unit26.Homotopies
import Mathlib.CategoryTheory.Whiskering

/-!
# Simplicial Methods, Chapter 33: Preparation for standard resolutions

The constructions in this file are expressed in the category of endofunctors.
The source's degreewise maps are kept explicit, while the existence statements
use Mathlib's `SimplicialObject` interface.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit33

open CategoryTheory
open CategoryTheory.SimplicialObject
open Opposite

universe v u v' u' uA vA uB vB uC vC

/-! ## Iterated endofunctors and the Godement maps -/

/-- The composite of `n` copies of an endofunctor, with the empty composite
equal to the identity functor. -/
def iteratedEndofunctor {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => Y ⋙ iteratedEndofunctor Y n

/-- The degree `n` endofunctor in Example 33.1 is the composite of `n + 1`
copies of `Y`. -/
def godementDegree {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (n : ℕ) : C ⥤ C :=
  iteratedEndofunctor Y (n + 1)

theorem godementDegree_add {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (n m : ℕ) :
    godementDegree Y (n + m + 1) =
      godementDegree Y n ⋙ godementDegree Y m := by
  change iteratedEndofunctor Y ((n + m + 1) + 1) =
    iteratedEndofunctor Y (n + 1) ⋙ iteratedEndofunctor Y (m + 1)
  induction n with
  | zero =>
    simp only [Nat.zero_add]
    change iteratedEndofunctor Y (m + 1 + 1) =
      (Y ⋙ 𝟭 C) ⋙ iteratedEndofunctor Y (m + 1)
    change Y ⋙ iteratedEndofunctor Y (m + 1) =
      (Y ⋙ 𝟭 C) ⋙ iteratedEndofunctor Y (m + 1)
    rw [Functor.comp_id]
  | succ n ih =>
    have h : (n + 1 + m + 1) + 1 = (n + m + 1 + 1) + 1 := by omega
    rw [h]
    change Y ⋙ iteratedEndofunctor Y (n + m + 1 + 1) =
      (Y ⋙ iteratedEndofunctor Y (n + 1)) ⋙
        iteratedEndofunctor Y (m + 1)
    rw [ih]
    rfl

theorem iteratedEndofunctor_add {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (a b : ℕ) :
    iteratedEndofunctor Y (a + b) =
      iteratedEndofunctor Y a ⋙ iteratedEndofunctor Y b := by
  induction a with
  | zero => simp [iteratedEndofunctor, Functor.id_comp]
  | succ a ih =>
    have hab : a + 1 + b = (a + b) + 1 := by omega
    rw [hab]
    simp only [iteratedEndofunctor]
    rw [ih]
    rfl

theorem godementFace_domain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y (n + 1) =
      iteratedEndofunctor Y j ⋙ Y ⋙ iteratedEndofunctor Y (n - j) := by
  have h : n + 1 = (j : ℕ) + 1 + (n - (j : ℕ)) := by omega
  conv_lhs =>
    rw [h]
  rw [iteratedEndofunctor_add Y ((j : ℕ) + 1) (n - (j : ℕ))]
  rw [iteratedEndofunctor_add Y (j : ℕ) 1]
  simp [iteratedEndofunctor, Functor.comp_id, Functor.assoc]

theorem godementFace_codomain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y n =
      iteratedEndofunctor Y j ⋙ 𝟭 C ⋙ iteratedEndofunctor Y (n - j) := by
  have h : n = (j : ℕ) + (n - (j : ℕ)) := by omega
  conv_lhs =>
    rw [h]
  rw [iteratedEndofunctor_add Y (j : ℕ) (n - (j : ℕ))]
  rfl

theorem godementDegeneracy_domain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y (n + 1) =
      iteratedEndofunctor Y j ⋙ Y ⋙ iteratedEndofunctor Y (n - j) := by
  exact godementFace_domain_decomposition Y n j

theorem godementDegeneracy_codomain_decomposition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (n : ℕ) (j : Fin (n + 1)) :
    iteratedEndofunctor Y (n + 2) =
      iteratedEndofunctor Y j ⋙ (Y ⋙ Y) ⋙ iteratedEndofunctor Y (n - j) := by
  have h : n + 2 = (j : ℕ) + 2 + (n - (j : ℕ)) := by omega
  conv_lhs =>
    rw [h]
  rw [iteratedEndofunctor_add Y ((j : ℕ) + 2) (n - (j : ℕ))]
  rw [iteratedEndofunctor_add Y (j : ℕ) 2]
  simp [iteratedEndofunctor, Functor.comp_id, Functor.assoc]

/-- The source's `d^n_j`, expressed as a natural transformation in the
category of endofunctors. -/
def godementFace {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) {n : ℕ} (j : Fin (n + 1)) :
    godementDegree Y n ⟶ iteratedEndofunctor Y n := by
  let raw :
      (iteratedEndofunctor Y j ⋙ Y ⋙ iteratedEndofunctor Y (n - j)) ⟶
        (iteratedEndofunctor Y j ⋙ 𝟭 C ⋙ iteratedEndofunctor Y (n - j)) :=
    Functor.whiskerLeft (iteratedEndofunctor Y j)
      (Functor.whiskerRight d (iteratedEndofunctor Y (n - j)))
  exact eqToHom (godementFace_domain_decomposition Y n j) ≫ raw ≫
    eqToHom (godementFace_codomain_decomposition Y n j).symm

/-- The source's `s^n_j`, expressed as a natural transformation in the
category of endofunctors. -/
def godementDegeneracy {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (s : Y ⟶ Y ⋙ Y) {n : ℕ} (j : Fin (n + 1)) :
    godementDegree Y n ⟶ godementDegree Y (n + 1) := by
  let raw :
      (iteratedEndofunctor Y j ⋙ Y ⋙ iteratedEndofunctor Y (n - j)) ⟶
        (iteratedEndofunctor Y j ⋙ (Y ⋙ Y) ⋙
          iteratedEndofunctor Y (n - j)) :=
    Functor.whiskerLeft (iteratedEndofunctor Y j)
      (Functor.whiskerRight s (iteratedEndofunctor Y (n - j)))
  exact eqToHom (godementDegeneracy_domain_decomposition Y n j) ≫ raw ≫
    eqToHom (godementDegeneracy_codomain_decomposition Y n j).symm

/-! ## The hypotheses and the canonical simplicial-object interface -/

/-- The two unit equations and the coassociativity equation in Lemma 33.2. -/
structure GodementEquations {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) : Prop where
  left_unit : s ≫ Functor.whiskerRight d Y = 𝟙 Y
  right_unit : s ≫ Functor.whiskerLeft Y d = 𝟙 Y
  coassoc : s ≫ Functor.whiskerRight s Y = s ≫ Functor.whiskerLeft Y s

def godementSimplicialFace {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (n : ℕ) (j : Fin (n + 2)) :
    godementDegree Y (n + 1) ⟶ godementDegree Y n :=
  godementFace Y d j

def godementSimplicialDegeneracy {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (s : Y ⟶ Y ⋙ Y) (n : ℕ) (j : Fin (n + 1)) :
    godementDegree Y n ⟶ godementDegree Y (n + 1) :=
  godementDegeneracy Y s j

structure GodementSimplicialData {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) where
  object : SimplicialObject (C ⥤ C)
  object_obj : ∀ n,
    object.obj (op (SimplexCategory.mk n)) = godementDegree Y n
  face_def : ∀ n (j : Fin (n + 2)),
    eqToHom (object_obj (n + 1)).symm ≫ object.δ j ≫
        eqToHom (object_obj n) = godementSimplicialFace Y d n j
  degeneracy_def : ∀ n (j : Fin (n + 1)),
    eqToHom (object_obj n).symm ≫ object.σ j ≫
        eqToHom (object_obj (n + 1)) =
      godementSimplicialDegeneracy Y s n j

/-! The unique map from degree zero to degree `n` is useful when spelling out
the section constructed later in this chapter. -/

def simplicialUnitMap {D : Type u} [Category.{v} D]
    (U : SimplicialObject D) (n : ℕ) :
    U.obj (op (SimplexCategory.mk 0)) ⟶
      U.obj (op (SimplexCategory.mk n)) :=
  U.map (SimplexCategory.const (SimplexCategory.mk n)
    (SimplexCategory.mk 0) 0).op

def godementUnitMap {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (data : GodementSimplicialData Y d s) (n : ℕ) :
    godementDegree Y 0 ⟶ godementDegree Y n :=
  eqToHom (data.object_obj 0).symm ≫
    simplicialUnitMap data.object n ≫ eqToHom (data.object_obj n)

theorem godementUnitMap_zero {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (data : GodementSimplicialData Y d s) :
    godementUnitMap Y d s data 0 = 𝟙 (godementDegree Y 0) := by
  dsimp [godementUnitMap]
  simp [simplicialUnitMap]

theorem godement_simplicial_data
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementSimplicialData Y d s) := by
  let D : Formalization.Books.Simplicial.Unit02.SimplexCategoryGeneratorData
      (C := (C ⥤ C)ᵒᵖ) :=
    { obj := fun n => op (godementDegree Y n)
      δ := fun i => op (godementSimplicialFace Y d _ i)
      σ := fun i => op (godementSimplicialDegeneracy Y s _ i)
      δ_comp_δ := by
        intro n i j hij
        change op (godementSimplicialFace Y d (n + 1) j.succ ≫
          godementSimplicialFace Y d n i) =
          op (godementSimplicialFace Y d (n + 1) i.castSucc ≫
            godementSimplicialFace Y d n j)
        congr 1
        have hij' : (i : ℕ) ≤ (j : ℕ) := hij
        have hji : (j : ℕ) + 1 ≤ n + 2 := by omega
        have hsum : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) := by omega
        have hsum' : n + 1 - (i : ℕ) =
            (n + 1 - (j : ℕ)) + ((j : ℕ) - (i : ℕ)) := by omega
        have hj1 : iteratedEndofunctor Y ((j : ℕ) + 1) =
            iteratedEndofunctor Y (i : ℕ) ⋙ Y ⋙
              iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) := by
          have h : (j : ℕ) + 1 = (i : ℕ) + 1 + ((j : ℕ) - (i : ℕ)) := by
            omega
          rw [h, iteratedEndofunctor_add, iteratedEndofunctor_add]
          simp [iteratedEndofunctor, Functor.assoc, Functor.id_comp,
            Functor.comp_id]
        have hj : iteratedEndofunctor Y (j : ℕ) =
            iteratedEndofunctor Y (i : ℕ) ⋙
              iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) := by
          calc
            iteratedEndofunctor Y (j : ℕ) =
                iteratedEndofunctor Y ((i : ℕ) + ((j : ℕ) - (i : ℕ))) := by
                  exact congrArg (iteratedEndofunctor Y) hsum
            _ = iteratedEndofunctor Y (i : ℕ) ⋙
                iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) :=
              iteratedEndofunctor_add Y (i : ℕ) ((j : ℕ) - (i : ℕ))
        have hjY : Y ⋙ iteratedEndofunctor Y (j : ℕ) =
            iteratedEndofunctor Y (i : ℕ) ⋙ Y ⋙
              iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) := by
          change iteratedEndofunctor Y ((j : ℕ) + 1) = _
          exact hj1
        have hmid : iteratedEndofunctor Y (n + 1 - (i : ℕ)) =
            iteratedEndofunctor Y (n + 1 - (j : ℕ)) ⋙
              iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) := by
          rw [hsum', iteratedEndofunctor_add]
        have hbig : iteratedEndofunctor Y (n + 1 + 1 - (i : ℕ)) =
            iteratedEndofunctor Y (n + 1 - (j : ℕ)) ⋙ Y ⋙
              iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) := by
          have h : n + 1 + 1 - (i : ℕ) =
              (n + 1 - (j : ℕ)) + 1 + ((j : ℕ) - (i : ℕ)) := by
            omega
          rw [h, iteratedEndofunctor_add, iteratedEndofunctor_add]
          simp [iteratedEndofunctor, Functor.assoc, Functor.id_comp,
            Functor.comp_id]
        have hsmall : n + 1 + 1 - ((j : ℕ) + 1) =
            n + 1 - (j : ℕ) := by omega
        have hp1 := godementFace_domain_decomposition Y (n + 2) j.succ
        have hq1 := godementFace_codomain_decomposition Y (n + 2) j.succ
        have hp2 := godementFace_domain_decomposition Y (n + 1) i
        have hq2 := godementFace_codomain_decomposition Y (n + 1) i
        have hp3 := godementFace_domain_decomposition Y (n + 2) i.castSucc
        have hq3 := godementFace_codomain_decomposition Y (n + 2) i.castSucc
        have hp4 := godementFace_domain_decomposition Y (n + 1) j
        have hq4 := godementFace_codomain_decomposition Y (n + 1) j
        dsimp [godementSimplicialFace, godementFace, godementDegree,
          iteratedEndofunctor]
        simp only [Category.assoc, CategoryTheory.eqToHom_trans,
          CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
          CategoryTheory.eqToHom_app,
          CategoryTheory.eqToHom_naturality_assoc,
          CategoryTheory.eqToHom_naturality, Functor.assoc,
          CategoryTheory.eqToHom_map, Functor.comp_map,
          Functor.comp_id, Functor.id_comp, Functor.map_id, Functor.map_comp,
          Functor.whiskerLeft_comp, Functor.whiskerRight_comp,
          Functor.associator, Functor.leftUnitor, Functor.rightUnitor]
        ext X
        have hdd := d.naturality
          ((iteratedEndofunctor Y ((j : ℕ) - (i : ℕ))).map
            (d.app ((iteratedEndofunctor Y (↑i : ℕ)).obj X)))
        have hdd' := congrArg
          (fun f => (iteratedEndofunctor Y (n + 1 - (j : ℕ))).map f) hdd
        have hFsource :
            Y ⋙ Y ⋙ Y ⋙ iteratedEndofunctor Y n =
              iteratedEndofunctor Y (i : ℕ) ⋙ Y ⋙
                iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) ⋙ Y ⋙
                iteratedEndofunctor Y (n + 1 - (j : ℕ)) := by
          calc
            Y ⋙ Y ⋙ Y ⋙ iteratedEndofunctor Y n =
                iteratedEndofunctor Y 1 ⋙ iteratedEndofunctor Y 1 ⋙
                  iteratedEndofunctor Y 1 ⋙ iteratedEndofunctor Y n := by
                    simp [iteratedEndofunctor, Functor.comp_id, Functor.assoc]
            _ = iteratedEndofunctor Y (1 + 1 + 1 + n) := by
              rw [iteratedEndofunctor_add, iteratedEndofunctor_add,
                iteratedEndofunctor_add]
              rfl
            _ = iteratedEndofunctor Y ((i : ℕ) + 1 +
                  ((j : ℕ) - (i : ℕ)) + 1 + (n + 1 - (j : ℕ))) := by
              congr 1 <;> omega
            _ = iteratedEndofunctor Y (i : ℕ) ⋙ Y ⋙
                  iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) ⋙ Y ⋙
                  iteratedEndofunctor Y (n + 1 - (j : ℕ)) := by
              rw [iteratedEndofunctor_add, iteratedEndofunctor_add,
                iteratedEndofunctor_add, iteratedEndofunctor_add]
              simp [iteratedEndofunctor, Functor.comp_id, Functor.assoc]
        have hFtarget :
            Y ⋙ iteratedEndofunctor Y n =
              iteratedEndofunctor Y (i : ℕ) ⋙
                iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) ⋙
                iteratedEndofunctor Y (n + 1 - (j : ℕ)) := by
          calc
            Y ⋙ iteratedEndofunctor Y n =
                iteratedEndofunctor Y 1 ⋙ iteratedEndofunctor Y n := by
              change Y ⋙ iteratedEndofunctor Y n =
                (Y ⋙ 𝟭 C) ⋙ iteratedEndofunctor Y n
              rw [Functor.comp_id]
            _ = iteratedEndofunctor Y (1 + n) :=
              (iteratedEndofunctor_add Y 1 n).symm
            _ = iteratedEndofunctor Y ((i : ℕ) + ((j : ℕ) - (i : ℕ)) +
                  (n + 1 - (j : ℕ))) := by
              congr 1 <;> omega
            _ = iteratedEndofunctor Y (i : ℕ) ⋙
                  iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) ⋙
                  iteratedEndofunctor Y (n + 1 - (j : ℕ)) := by
              rw [iteratedEndofunctor_add, iteratedEndofunctor_add]
              rfl
        apply eq_of_heq
        have hdj := CategoryTheory.eqToHom_naturality_assoc
          (fun F : C ⥤ C => d.app (F.obj X)) hjY (𝟙 _)
        have hdj' := CategoryTheory.eqToHom_naturality_assoc
          (fun F : C ⥤ C => d.app (F.obj X)) hj (𝟙 _)
        simp only [Category.comp_id, Category.id_comp] at hdj hdj'
        have hdjMap := congrArg
          (fun f => (iteratedEndofunctor Y (n + 1 - (j : ℕ))).map f) hdj
        simp only [Category.assoc, Functor.map_comp] at hdjMap
        have hmidD := CategoryTheory.eqToHom_naturality_assoc
          (fun F : C ⥤ C => F.map
            (d.app ((iteratedEndofunctor Y (i : ℕ)).obj X))) hmid (𝟙 _)
        have hbigD := CategoryTheory.eqToHom_naturality_assoc
          (fun F : C ⥤ C => F.map
            (d.app ((iteratedEndofunctor Y (i : ℕ)).obj X))) hbig (𝟙 _)
        have hmidMap := Functor.congr_hom hmid
          (d.app ((iteratedEndofunctor Y (i : ℕ)).obj X))
        have hbigMap := Functor.congr_hom hbig
          (d.app ((iteratedEndofunctor Y (i : ℕ)).obj X))
        try rw [← hmidMap]
        try rw [← hbigMap]
        try rw [hsmall] at *
        simpa only [Category.assoc, CategoryTheory.eqToHom_trans,
          CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
          CategoryTheory.eqToHom_app, NatTrans.comp_app,
          CategoryTheory.eqToHom_comp_heq, CategoryTheory.comp_eqToHom_heq,
          Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Functor.comp_obj, Functor.id_obj, heq_eq_eq,
          CategoryTheory.eqToHom_naturality_assoc,
          CategoryTheory.eqToHom_naturality, Functor.assoc,
          Functor.comp_id, Functor.id_comp, Functor.map_comp,
          Functor.whiskerLeft_comp, Functor.whiskerRight_comp,
          Functor.associator, Functor.leftUnitor, Functor.rightUnitor,
          hp1, hq1, hp2, hq2, hp3, hq3, hp4, hq4, hFsource, hFtarget,
          hj, hjY, hmid, hbig, hsmall, hdj, hdj', hdjMap, hmidD, hbigD,
          hmidMap, hbigMap] using hdd'.symm
      δ_comp_σ_of_le := by
        intro n i j hij
        change op (godementSimplicialDegeneracy Y s (n + 1) j.succ ≫
          godementSimplicialFace Y d (n + 1) i.castSucc) =
          op (godementSimplicialFace Y d n i ≫
            godementSimplicialDegeneracy Y s n j)
        congr 1
        ext X
        dsimp [godementSimplicialFace, godementSimplicialDegeneracy,
          godementFace, godementDegeneracy, godementDegree]
        have hji : (j : ℕ) + 1 ≤ n + 2 := by omega
        have h1 : n + 1 - ((j : ℕ) + 1) = n - (j : ℕ) := by omega
        have h2 : n + 1 + 1 - (i : ℕ) = 1 + (n + 1 - (i : ℕ)) := by omega
        have hij' : (i : ℕ) ≤ (j : ℕ) := Fin.le_iff_val_le_val.mp hij
        have hsum : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) := by omega
        have hsum' : n + 1 - (i : ℕ) =
            (n + 1 - (j : ℕ)) + ((j : ℕ) - (i : ℕ)) := by omega
        have hj : iteratedEndofunctor Y (j : ℕ) =
            iteratedEndofunctor Y (i : ℕ) ⋙
              iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) := by
          calc
            iteratedEndofunctor Y (j : ℕ) =
                iteratedEndofunctor Y ((i : ℕ) + ((j : ℕ) - (i : ℕ))) := by
                  congr 1 <;> omega
            _ = iteratedEndofunctor Y (i : ℕ) ⋙
                iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) :=
              iteratedEndofunctor_add Y (i : ℕ) ((j : ℕ) - (i : ℕ))
        have hjY : Y ⋙ iteratedEndofunctor Y (j : ℕ) =
            iteratedEndofunctor Y (i : ℕ) ⋙ Y ⋙
              iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) := by
          change iteratedEndofunctor Y ((j : ℕ) + 1) = _
          have h : (j : ℕ) + 1 = (i : ℕ) + 1 + ((j : ℕ) - (i : ℕ)) := by omega
          rw [h, iteratedEndofunctor_add, iteratedEndofunctor_add]
          simp [iteratedEndofunctor, Functor.assoc, Functor.id_comp,
            Functor.comp_id]
        have hj1 : iteratedEndofunctor Y ((j : ℕ) + 1) =
            iteratedEndofunctor Y (i : ℕ) ⋙ Y ⋙
              iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) := by
          have h : (j : ℕ) + 1 = (i : ℕ) + 1 + ((j : ℕ) - (i : ℕ)) := by omega
          rw [h, iteratedEndofunctor_add, iteratedEndofunctor_add]
          simp [iteratedEndofunctor, Functor.assoc, Functor.id_comp,
            Functor.comp_id]
        have hmid : iteratedEndofunctor Y (n + 1 - (i : ℕ)) =
            iteratedEndofunctor Y (n + 1 - (j : ℕ)) ⋙
              iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) := by
          rw [hsum', iteratedEndofunctor_add]
        have hbig : iteratedEndofunctor Y (n + 1 + 1 - (i : ℕ)) =
            iteratedEndofunctor Y (n + 1 - (j : ℕ)) ⋙ Y ⋙
              iteratedEndofunctor Y ((j : ℕ) - (i : ℕ)) := by
          have h : n + 1 + 1 - (i : ℕ) =
              (n + 1 - (j : ℕ)) + 1 + ((j : ℕ) - (i : ℕ)) := by omega
          rw [h, iteratedEndofunctor_add, iteratedEndofunctor_add]
          simp [iteratedEndofunctor, Functor.assoc, Functor.id_comp,
            Functor.comp_id]
        have hp1 := godementDegeneracy_domain_decomposition Y (n + 1) j.succ
        have hq1 := godementDegeneracy_codomain_decomposition Y (n + 1) j.succ
        have hp2 := godementFace_domain_decomposition Y (n + 2) i.castSucc
        have hq2 := godementFace_codomain_decomposition Y (n + 2) i.castSucc
        have hp3 := godementFace_domain_decomposition Y (n + 1) i
        have hq3 := godementFace_codomain_decomposition Y (n + 1) i
        have hp4 := godementDegeneracy_domain_decomposition Y n j
        have hq4 := godementDegeneracy_codomain_decomposition Y n j
        have hss := s.naturality
          ((iteratedEndofunctor Y ((j : ℕ) - (i : ℕ))).map
            (d.app ((iteratedEndofunctor Y (i : ℕ)).obj X)))
        have hss' := congrArg
          (fun f => (iteratedEndofunctor Y (n - (j : ℕ))).map f) hss
        have hsjY := CategoryTheory.eqToHom_naturality_assoc
          (fun F : C ⥤ C => s.app (F.obj X)) hj1 (𝟙 _)
        have hsj := CategoryTheory.eqToHom_naturality_assoc
          (fun F : C ⥤ C => s.app (F.obj X)) hj (𝟙 _)
        simp only [Category.comp_id, Category.id_comp] at hsjY hsj
        have hsjYMap := congrArg
          (fun f => (iteratedEndofunctor Y (n - (j : ℕ))).map f) hsjY
        have hsjMap := congrArg
          (fun f => (iteratedEndofunctor Y (n - (j : ℕ))).map f) hsj
        simp only [Category.assoc, Functor.map_comp] at hsjYMap hsjMap
        have htailF : iteratedEndofunctor Y (n + 1 - ((j : ℕ) + 1)) =
            iteratedEndofunctor Y (n - (j : ℕ)) := by
          congr 1 <;> omega
        have htailS := Functor.congr_hom htailF
          (s.app ((iteratedEndofunctor Y ((j : ℕ) + 1)).obj X))
        have hmidMap := Functor.congr_hom hmid
          (d.app ((iteratedEndofunctor Y (i : ℕ)).obj X))
        have hbigMap := Functor.congr_hom hbig
          (d.app ((iteratedEndofunctor Y (i : ℕ)).obj X))
        apply eq_of_heq
        try rw [← hmidMap]
        try rw [← hbigMap]
        simpa only [Category.assoc, CategoryTheory.eqToHom_trans,
          CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
          CategoryTheory.eqToHom_app, Category.comp_id, Category.id_comp,
          CategoryTheory.eqToHom_comp_heq, CategoryTheory.comp_eqToHom_heq,
          Functor.comp_obj, Functor.id_obj, heq_eq_eq,
          CategoryTheory.eqToHom_map,
          Functor.assoc, Functor.comp_id, Functor.id_comp, Functor.map_comp,
          CategoryTheory.eqToHom_naturality_assoc,
          CategoryTheory.eqToHom_naturality, Functor.whiskerLeft_comp,
          Functor.whiskerRight_comp, Functor.associator,
          Functor.leftUnitor, Functor.rightUnitor, hji, h1, h2, hsum,
          hsum', hj, hjY, hj1, hmid, hbig, hp1, hq1, hp2, hq2, hp3, hq3,
          hp4, hq4, hsjY, hsj, hsjYMap, hsjMap, htailF, htailS,
          hmidMap, hbigMap] using hss'.symm
      δ_comp_σ_self := by
        intro n i
        change op (godementSimplicialDegeneracy Y s n i ≫
          godementSimplicialFace Y d n i.castSucc) = op (𝟙 _)
        congr 1
        let p : iteratedEndofunctor Y (n + 1) =
            iteratedEndofunctor Y (↑i) ⋙ Y ⋙
              iteratedEndofunctor Y (n - ↑i) :=
          godementDegeneracy_domain_decomposition Y n i
        let q : iteratedEndofunctor Y (n + 1) =
            iteratedEndofunctor Y (↑i.castSucc) ⋙ 𝟭 C ⋙
              iteratedEndofunctor Y (n + 1 - ↑i.castSucc) :=
          godementFace_codomain_decomposition Y (n + 1) i.castSucc
        let r :
            (iteratedEndofunctor Y (↑i) ⋙ (𝟭 C ⋙ Y) ⋙
                iteratedEndofunctor Y (n - ↑i)) =
              (iteratedEndofunctor Y (↑i) ⋙ 𝟭 C ⋙
                iteratedEndofunctor Y ((n + 1) - ↑i)) := by
          have hi : (n + 1) - (↑i : ℕ) = 1 + (n - (↑i : ℕ)) := by omega
          rw [hi, iteratedEndofunctor_add]
          simp [Functor.id_comp, Functor.comp_id, iteratedEndofunctor]
        let a : iteratedEndofunctor Y (n + 2) =
            iteratedEndofunctor Y (↑i) ⋙ (Y ⋙ Y) ⋙
              iteratedEndofunctor Y (n - ↑i) :=
          godementDegeneracy_codomain_decomposition Y n i
        let b : iteratedEndofunctor Y (n + 2) =
            iteratedEndofunctor Y (↑i.castSucc) ⋙ Y ⋙
              iteratedEndofunctor Y (n + 1 - ↑i.castSucc) :=
          godementFace_domain_decomposition Y (n + 1) i.castSucc
        let m :
            (iteratedEndofunctor Y (↑i) ⋙ (Y ⋙ Y) ⋙
                iteratedEndofunctor Y (n - ↑i)) =
              (iteratedEndofunctor Y (↑i) ⋙ Y ⋙
                iteratedEndofunctor Y (n + 1 - ↑i.castSucc)) := by
          have hi : n + 1 - (↑i.castSucc : ℕ) = 1 + (n - (↑i : ℕ)) := by
            simpa using (show n + 1 - (↑i : ℕ) = 1 + (n - (↑i : ℕ)) by omega)
          rw [hi, iteratedEndofunctor_add]
          simp [Functor.assoc, Functor.comp_id, iteratedEndofunctor]
        let S :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
            (Functor.whiskerRight s (iteratedEndofunctor Y (n - ↑i)))
        let T :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
            (Functor.whiskerRight (Functor.whiskerRight d Y)
              (iteratedEndofunctor Y (n - ↑i)))
        let D' :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
            (Functor.whiskerRight d
              (iteratedEndofunctor Y (n + 1 - ↑i.castSucc)))
        have hmid : S ≫ eqToHom m ≫ D' = S ≫ T ≫ eqToHom r := by
          ext X
          have inner : (eqToHom m).app X ≫ D'.app X =
              T.app X ≫ (eqToHom r).app X := by
            dsimp [S, T, D']
            have hi : n + 1 - (↑i : ℕ) = 1 + (n - (↑i : ℕ)) := by omega
            simp [Functor.assoc, Functor.id_comp]
            have hiF : iteratedEndofunctor Y (n + 1 - (↑i.castSucc : ℕ)) =
                Y ⋙ iteratedEndofunctor Y (n - (↑i : ℕ)) := by
              have hsub : n + 1 - (↑i.castSucc : ℕ) =
                  1 + (n - (↑i : ℕ)) := by
                simpa using (show n + 1 - (↑i : ℕ) =
                  1 + (n - (↑i : ℕ)) by omega)
              rw [hsub, iteratedEndofunctor_add]
              simp [iteratedEndofunctor, Functor.assoc, Functor.id_comp]
            have hn := CategoryTheory.eqToHom_naturality_assoc
              (fun F : C ⥤ C => F.map (d.app ((iteratedEndofunctor Y (↑i : ℕ)).obj X)))
              hiF.symm (𝟙 _)
            simpa [m, r, hiF, Category.assoc, Functor.assoc,
              Functor.id_comp, Functor.comp_id, Functor.map_comp]
              using hn.symm
          simpa [Category.assoc] using
            congrArg (fun z => S.app X ≫ z) inner
        have hm : eqToHom a.symm ≫ eqToHom b = eqToHom m := by
          rw [CategoryTheory.eqToHom_trans]
        have hcoh :
            godementSimplicialDegeneracy Y s n i ≫
                godementSimplicialFace Y d n i.castSucc =
              eqToHom p ≫
                Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
                  (Functor.whiskerRight
                    (s ≫ Functor.whiskerRight d Y)
                    (iteratedEndofunctor Y (n - ↑i))) ≫
                eqToHom r ≫ eqToHom q.symm := by
          have hraw :
              godementSimplicialDegeneracy Y s n i ≫
                  godementSimplicialFace Y d n i.castSucc =
                eqToHom p ≫ S ≫ eqToHom a.symm ≫ eqToHom b ≫ D' ≫
                  eqToHom q.symm := by
            simp only [godementDegree, S, D', godementSimplicialFace,
              godementSimplicialDegeneracy, godementFace, godementDegeneracy]
            apply eq_of_heq
            simp [Category.assoc, CategoryTheory.eqToHom_trans,
              CategoryTheory.eqToHom_trans_assoc,
              CategoryTheory.eqToHom_refl, Functor.assoc,
              Functor.id_comp, Functor.comp_id, Functor.whiskerLeft_comp,
              Functor.whiskerRight_comp]
          have hhm :
              eqToHom p ≫ S ≫ eqToHom a.symm ≫ eqToHom b ≫ D' ≫
                  eqToHom q.symm =
                eqToHom p ≫ S ≫ eqToHom m ≫ D' ≫ eqToHom q.symm := by
            simpa only [Category.assoc] using
              congrArg (fun z => eqToHom p ≫ S ≫ z ≫ D' ≫ eqToHom q.symm) hm
          have hmid' :
              eqToHom p ≫ S ≫ eqToHom m ≫ D' ≫ eqToHom q.symm =
                eqToHom p ≫ S ≫ T ≫ eqToHom r ≫ eqToHom q.symm := by
            simpa only [Category.assoc] using
              congrArg (fun z => eqToHom p ≫ z ≫ eqToHom q.symm) hmid
          have hST : S ≫ T =
              Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
                (Functor.whiskerRight
                  (s ≫ Functor.whiskerRight d Y)
                  (iteratedEndofunctor Y (n - ↑i))) := by
            simp [S, T, Functor.whiskerLeft_comp,
              Functor.whiskerRight_comp, Functor.assoc]
          rw [hraw, hhm, hmid']
          simpa [godementDegree, Category.assoc,
            CategoryTheory.eqToHom_trans,
            CategoryTheory.eqToHom_trans_assoc,
            CategoryTheory.eqToHom_refl] using
            congrArg (fun z => eqToHom p ≫ z ≫ eqToHom r ≫ eqToHom q.symm) hST
        rw [hcoh]
        have hu := congrArg
          (fun z => eqToHom p ≫
            Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
              (Functor.whiskerRight z (iteratedEndofunctor Y (n - ↑i))) ≫
            eqToHom r ≫ eqToHom q.symm) h.left_unit
        rw [hu]
        simp [godementDegree, Category.assoc, Functor.whiskerLeft_comp,
          Functor.whiskerRight_comp, Functor.assoc,
          CategoryTheory.eqToHom_trans,
          CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Functor.associator,
          Functor.leftUnitor, Functor.rightUnitor, r]
      δ_comp_σ_succ := by
        intro n i
        change op (godementSimplicialDegeneracy Y s n i ≫
          godementSimplicialFace Y d n i.succ) = op (𝟙 _)
        congr 1
        let p : iteratedEndofunctor Y (n + 1) =
            iteratedEndofunctor Y (↑i) ⋙ Y ⋙ iteratedEndofunctor Y (n - ↑i) := by
          change iteratedEndofunctor Y (n + 1) = _
          exact godementDegeneracy_domain_decomposition Y n i
        let q : iteratedEndofunctor Y (n + 1) =
            iteratedEndofunctor Y (↑i.succ) ⋙ 𝟭 C ⋙
              iteratedEndofunctor Y (n + 1 - ↑i.succ) :=
          godementFace_codomain_decomposition Y (n + 1) i.succ
        have htail : n + 1 - (↑i.succ : ℕ) = n - (↑i : ℕ) := by
          have hi : (↑i.succ : ℕ) = (↑i : ℕ) + 1 := rfl
          rw [hi]
          omega
        have htail' : n + 1 - ((↑i : ℕ) + 1) = n - (↑i : ℕ) := by omega
        have htailF : iteratedEndofunctor Y (n + 1 - ((↑i : ℕ) + 1)) =
            iteratedEndofunctor Y (n - (↑i : ℕ)) := by
          congr 1 <;> omega
        let r :
            (iteratedEndofunctor Y (↑i) ⋙ (Y ⋙ 𝟭 C) ⋙
                iteratedEndofunctor Y (n - ↑i)) =
            (iteratedEndofunctor Y (↑i.succ) ⋙ 𝟭 C ⋙
                iteratedEndofunctor Y (n + 1 - ↑i.succ)) := by
          rw [htail]
          have hcomm : iteratedEndofunctor Y (↑i) ⋙ Y =
              Y ⋙ iteratedEndofunctor Y (↑i) := by
            calc
              iteratedEndofunctor Y (↑i) ⋙ Y =
                  iteratedEndofunctor Y (↑i) ⋙ iteratedEndofunctor Y 1 := by
                    simp [iteratedEndofunctor, Functor.comp_id]
              _ = iteratedEndofunctor Y ((↑i) + 1) :=
                (iteratedEndofunctor_add Y (↑i) 1).symm
              _ = iteratedEndofunctor Y (1 + (↑i : ℕ)) := by
                congr 1 <;> omega
              _ = iteratedEndofunctor Y 1 ⋙ iteratedEndofunctor Y (↑i) :=
                iteratedEndofunctor_add Y 1 (↑i)
              _ = Y ⋙ iteratedEndofunctor Y (↑i) := by
                simp [iteratedEndofunctor, Functor.comp_id]
          have hs : iteratedEndofunctor Y (↑i.succ) =
              iteratedEndofunctor Y (↑i) ⋙ Y := by
            calc
              iteratedEndofunctor Y (↑i.succ) =
                  Y ⋙ iteratedEndofunctor Y (↑i) := by
                    simp [iteratedEndofunctor]
              _ = iteratedEndofunctor Y (↑i) ⋙ Y := hcomm.symm
          rw [hs]
          simp only [Functor.assoc]
        let a : iteratedEndofunctor Y (n + 2) =
            iteratedEndofunctor Y (↑i) ⋙ (Y ⋙ Y) ⋙
              iteratedEndofunctor Y (n - ↑i) := by
          change iteratedEndofunctor Y (n + 2) = _
          exact godementDegeneracy_codomain_decomposition Y n i
        let b : iteratedEndofunctor Y (n + 2) =
            iteratedEndofunctor Y (↑i.succ) ⋙ Y ⋙
              iteratedEndofunctor Y (n + 1 - ↑i.succ) :=
          godementFace_domain_decomposition Y (n + 1) i.succ
        let m :
            (iteratedEndofunctor Y (↑i) ⋙ (Y ⋙ Y) ⋙
                iteratedEndofunctor Y (n - ↑i)) =
            (iteratedEndofunctor Y (↑i.succ) ⋙ Y ⋙
                iteratedEndofunctor Y (n + 1 - ↑i.succ)) := by
          rw [htail]
          have hcomm : iteratedEndofunctor Y (↑i) ⋙ Y =
              Y ⋙ iteratedEndofunctor Y (↑i) := by
            calc
              iteratedEndofunctor Y (↑i) ⋙ Y =
                  iteratedEndofunctor Y (↑i) ⋙ iteratedEndofunctor Y 1 := by
                    simp [iteratedEndofunctor, Functor.comp_id]
              _ = iteratedEndofunctor Y ((↑i) + 1) :=
                (iteratedEndofunctor_add Y (↑i) 1).symm
              _ = iteratedEndofunctor Y (1 + (↑i : ℕ)) := by
                congr 1 <;> omega
              _ = iteratedEndofunctor Y 1 ⋙ iteratedEndofunctor Y (↑i) :=
                iteratedEndofunctor_add Y 1 (↑i)
              _ = Y ⋙ iteratedEndofunctor Y (↑i) := by
                simp [iteratedEndofunctor, Functor.comp_id]
          have hs : iteratedEndofunctor Y (↑i.succ) =
              iteratedEndofunctor Y (↑i) ⋙ Y := by
            calc
              iteratedEndofunctor Y (↑i.succ) =
                  Y ⋙ iteratedEndofunctor Y (↑i) := by
                    simp [iteratedEndofunctor]
              _ = iteratedEndofunctor Y (↑i) ⋙ Y := hcomm.symm
          rw [hs]
          simp only [Functor.assoc]
        let S :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
            (Functor.whiskerRight s (iteratedEndofunctor Y (n - ↑i)))
        let T :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
            (Functor.whiskerRight (Functor.whiskerLeft Y d)
              (iteratedEndofunctor Y (n - ↑i)))
        let D' :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i.succ))
            (Functor.whiskerRight d
              (iteratedEndofunctor Y (n + 1 - ↑i.succ)))
        have hmid : S ≫ eqToHom m ≫ D' = S ≫ T ≫ eqToHom r := by
          ext X
          have inner : (eqToHom m).app X ≫ D'.app X =
              T.app X ≫ (eqToHom r).app X := by
            dsimp [S, T, D']
            simp [Functor.assoc, Functor.id_comp, Functor.comp_id]
            have hcomm : iteratedEndofunctor Y (↑i) ⋙ Y =
                Y ⋙ iteratedEndofunctor Y (↑i) := by
              calc
                iteratedEndofunctor Y (↑i) ⋙ Y =
                    iteratedEndofunctor Y (↑i) ⋙ iteratedEndofunctor Y 1 := by
                      simp [iteratedEndofunctor, Functor.comp_id]
                _ = iteratedEndofunctor Y ((↑i) + 1) :=
                  (iteratedEndofunctor_add Y (↑i) 1).symm
                _ = iteratedEndofunctor Y (1 + (↑i : ℕ)) := by
                  congr 1 <;> omega
                _ = iteratedEndofunctor Y 1 ⋙ iteratedEndofunctor Y (↑i) :=
                  iteratedEndofunctor_add Y 1 (↑i)
                _ = Y ⋙ iteratedEndofunctor Y (↑i) := by
                  simp [iteratedEndofunctor, Functor.comp_id]
            have hn := CategoryTheory.eqToHom_naturality_assoc
              (fun F : C ⥤ C =>
                (iteratedEndofunctor Y (n - (↑i : ℕ))).map
                  (d.app (F.obj X))) hcomm (𝟙 _)
            simpa [S, m, r, hcomm, htail, htail', htailF, iteratedEndofunctor, Category.assoc,
              Functor.assoc, Functor.id_comp, Functor.comp_id,
              Functor.map_comp] using hn.symm
          simpa [Category.assoc] using
            congrArg (fun z => S.app X ≫ z) inner
        have hm : eqToHom a.symm ≫ eqToHom b = eqToHom m := by
          rw [CategoryTheory.eqToHom_trans]
        have hcoh :
            godementSimplicialDegeneracy Y s n i ≫
                godementSimplicialFace Y d n i.succ =
              eqToHom p ≫
                Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
                  (Functor.whiskerRight
                    (s ≫ Functor.whiskerLeft Y d)
                    (iteratedEndofunctor Y (n - ↑i))) ≫
                eqToHom r ≫ eqToHom q.symm := by
          have hraw :
              godementSimplicialDegeneracy Y s n i ≫
                  godementSimplicialFace Y d n i.succ =
                eqToHom p ≫ S ≫ eqToHom a.symm ≫ eqToHom b ≫ D' ≫
                  eqToHom q.symm := by
            simp only [godementDegree, S, D', godementSimplicialFace,
              godementSimplicialDegeneracy, godementFace, godementDegeneracy]
            apply eq_of_heq
            simp [Category.assoc, CategoryTheory.eqToHom_trans,
              CategoryTheory.eqToHom_trans_assoc,
              CategoryTheory.eqToHom_refl, Functor.assoc,
              Functor.id_comp, Functor.comp_id, Functor.whiskerLeft_comp,
              Functor.whiskerRight_comp]
          have hhm :
              eqToHom p ≫ S ≫ eqToHom a.symm ≫ eqToHom b ≫ D' ≫
                  eqToHom q.symm =
                eqToHom p ≫ S ≫ eqToHom m ≫ D' ≫ eqToHom q.symm := by
            simpa only [Category.assoc] using
              congrArg (fun z => eqToHom p ≫ S ≫ z ≫ D' ≫ eqToHom q.symm) hm
          have hmid' :
              eqToHom p ≫ S ≫ eqToHom m ≫ D' ≫ eqToHom q.symm =
                eqToHom p ≫ S ≫ T ≫ eqToHom r ≫ eqToHom q.symm := by
            simpa only [Category.assoc] using
              congrArg (fun z => eqToHom p ≫ z ≫ eqToHom q.symm) hmid
          have hST : S ≫ T =
              Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
                (Functor.whiskerRight
                  (s ≫ Functor.whiskerLeft Y d)
                  (iteratedEndofunctor Y (n - ↑i))) := by
            simp [S, T, Functor.whiskerLeft_comp,
              Functor.whiskerRight_comp, Functor.assoc]
          rw [hraw, hhm, hmid']
          simpa [godementDegree, Category.assoc, CategoryTheory.eqToHom_trans,
            CategoryTheory.eqToHom_trans_assoc,
            CategoryTheory.eqToHom_refl] using
            congrArg (fun z => eqToHom p ≫ z ≫ eqToHom r ≫ eqToHom q.symm) hST
        rw [hcoh]
        have hu := congrArg
          (fun z => eqToHom p ≫
            Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
              (Functor.whiskerRight z (iteratedEndofunctor Y (n - ↑i))) ≫
            eqToHom r ≫ eqToHom q.symm) h.right_unit
        simpa [godementDegree, Category.assoc, Functor.whiskerLeft_comp,
          Functor.whiskerRight_comp, Functor.assoc,
          CategoryTheory.eqToHom_trans,
          CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, r]
          using hu
      δ_comp_σ_of_gt := by
        intro n i j hji
        simp [godementSimplicialFace, godementSimplicialDegeneracy,
          godementFace, godementDegeneracy]
      σ_comp_σ := by
        intro n i j hij
        simp [godementSimplicialDegeneracy, godementDegeneracy] }
  let U := Formalization.Books.Simplicial.Unit02.simplicialObjectOfGeneratorData D
  have hobj : ∀ n, U.obj (op (SimplexCategory.mk n)) = godementDegree Y n := by
    intro n
    rfl
  refine ⟨{ object := U, object_obj := hobj, face_def := ?_, degeneracy_def := ?_ }⟩
  · intro n j
    change eqToHom _ ≫ U.map (SimplexCategory.δ j).op ≫
      eqToHom _ = godementSimplicialFace Y d n j
    dsimp [U, Formalization.Books.Simplicial.Unit02.simplicialObjectOfGeneratorData]
    rw [Formalization.Books.Simplicial.Unit02.simplexCategoryFunctorOfGeneratorData_map_δ]
    cases hobj n
    cases hobj (n + 1)
    simp [D, godementSimplicialFace]
  · intro n j
    change eqToHom _ ≫ U.map (SimplexCategory.σ j).op ≫
      eqToHom _ = godementSimplicialDegeneracy Y s n j
    dsimp [U, Formalization.Books.Simplicial.Unit02.simplicialObjectOfGeneratorData]
    rw [Formalization.Books.Simplicial.Unit02.simplexCategoryFunctorOfGeneratorData_map_σ]
    cases hobj n
    cases hobj (n + 1)
    simp [D, godementSimplicialDegeneracy]

/- The attempted direct proof is retained pending a coherence-oriented rewrite.
  let D : Formalization.Books.Simplicial.Unit02.SimplexCategoryGeneratorData
      (C := (C ⥤ C)ᵒᵖ) :=
    { obj := fun n => op (godementDegree Y n)
      δ := fun i => op (godementSimplicialFace Y d _ i)
      σ := fun i => op (godementSimplicialDegeneracy Y s _ i)
      δ_comp_δ := by
        intro n i j hij
        change op (godementSimplicialFace Y d (n + 1) j.succ ≫
          godementSimplicialFace Y d n i) =
          op (godementSimplicialFace Y d (n + 1) i.castSucc ≫
            godementSimplicialFace Y d n j)
        congr 1
        ext X
        dsimp [godementSimplicialFace, godementFace]
        dsimp [godementDegree]
        have hij' : (i : ℕ) ≤ (j : ℕ) := hij
        have hji : (j : ℕ) + 1 ≤ n + 2 := by omega
        simp [Category.assoc, CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_app]
      δ_comp_σ_of_le := by
        intro n i j hij
        change op (godementSimplicialDegeneracy Y s (n + 1) j.succ ≫
          godementSimplicialFace Y d (n + 1) i.castSucc) =
          op (godementSimplicialFace Y d n i ≫
            godementSimplicialDegeneracy Y s n j)
        congr 1
        ext X
        dsimp [godementSimplicialFace, godementSimplicialDegeneracy,
          godementFace, godementDegeneracy, godementDegree]
        have hji : (j : ℕ) + 1 ≤ n + 2 := by omega
        have h1 : n + 1 - ((j : ℕ) + 1) = n - (j : ℕ) := by omega
        have h2 : n + 1 + 1 - (i : ℕ) = 1 + (n + 1 - (i : ℕ)) := by omega
        simp [Category.assoc, CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_app]
      δ_comp_σ_self := by
        intro n i
        change op (godementSimplicialDegeneracy Y s n i ≫
          godementSimplicialFace Y d n i.castSucc) = op (𝟙 _)
        congr 1
        let p : godementDegree Y n =
            iteratedEndofunctor Y (↑i) ⋙ Y ⋙
              iteratedEndofunctor Y (n - ↑i) := by
          change iteratedEndofunctor Y (n + 1) = _
          exact godementDegeneracy_domain_decomposition Y n i
        let q : godementDegree Y n =
            iteratedEndofunctor Y (↑i.castSucc) ⋙ 𝟭 C ⋙
              iteratedEndofunctor Y (n + 1 - ↑i.castSucc) := by
          change iteratedEndofunctor Y (n + 1) = _
          exact godementFace_codomain_decomposition Y (n + 1) i.castSucc
        let r :
            (iteratedEndofunctor Y (↑i) ⋙ (𝟭 C ⋙ Y) ⋙
                iteratedEndofunctor Y (n - ↑i)) =
              (iteratedEndofunctor Y (↑i) ⋙ 𝟭 C ⋙
                iteratedEndofunctor Y ((n + 1) - ↑i)) := by
          have hi : (n + 1) - (↑i : ℕ) = 1 + (n - (↑i : ℕ)) := by omega
          rw [hi, iteratedEndofunctor_add]
          simp [Functor.id_comp, Functor.comp_id, iteratedEndofunctor]
        let a : godementDegree Y (n + 1) =
            iteratedEndofunctor Y (↑i) ⋙ (Y ⋙ Y) ⋙
              iteratedEndofunctor Y (n - ↑i) := by
          change iteratedEndofunctor Y (n + 2) = _
          exact godementDegeneracy_codomain_decomposition Y n i
        let b : godementDegree Y (n + 1) =
            iteratedEndofunctor Y (↑i.castSucc) ⋙ Y ⋙
              iteratedEndofunctor Y (n + 1 - ↑i.castSucc) := by
          change iteratedEndofunctor Y (n + 2) = _
          exact godementFace_domain_decomposition Y (n + 1) i.castSucc
        let m :
            (iteratedEndofunctor Y (↑i) ⋙ (Y ⋙ Y) ⋙
                iteratedEndofunctor Y (n - ↑i)) =
              (iteratedEndofunctor Y (↑i) ⋙ Y ⋙
                iteratedEndofunctor Y (n + 1 - ↑i.castSucc)) := by
          have hi : n + 1 - (↑i.castSucc : ℕ) = 1 + (n - (↑i : ℕ)) := by
            simpa using (show n + 1 - (↑i : ℕ) = 1 + (n - (↑i : ℕ)) by omega)
          rw [hi, iteratedEndofunctor_add]
          simp [Functor.assoc, Functor.comp_id, iteratedEndofunctor]
        let S :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
            (Functor.whiskerRight s (iteratedEndofunctor Y (n - ↑i)))
        let T :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
            (Functor.whiskerRight (Functor.whiskerRight d Y)
              (iteratedEndofunctor Y (n - ↑i)))
        let D' :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
            (Functor.whiskerRight d
              (iteratedEndofunctor Y (n + 1 - ↑i.castSucc)))
        have hmid : S ≫ eqToHom m ≫ D' = S ≫ T ≫ eqToHom r := by
          ext X
          have inner : (eqToHom m).app X ≫ D'.app X =
              T.app X ≫ (eqToHom r).app X := by
            dsimp [S, T, D']
            have hi : n + 1 - (↑i : ℕ) = 1 + (n - (↑i : ℕ)) := by omega
            simp [Functor.assoc, Functor.id_comp]
            have hiF : iteratedEndofunctor Y (n + 1 - (↑i.castSucc : ℕ)) =
                Y ⋙ iteratedEndofunctor Y (n - (↑i : ℕ)) := by
              have hsub : n + 1 - (↑i.castSucc : ℕ) =
                  1 + (n - (↑i : ℕ)) := by
                simpa using (show n + 1 - (↑i : ℕ) =
                  1 + (n - (↑i : ℕ)) by omega)
              rw [hsub, iteratedEndofunctor_add]
              simp [iteratedEndofunctor, Functor.assoc, Functor.id_comp]
            have hn := CategoryTheory.eqToHom_naturality_assoc
              (fun F : C ⥤ C => F.map (d.app ((iteratedEndofunctor Y (↑i : ℕ)).obj X)))
              hiF.symm (𝟙 _)
            simpa [m, r, hiF, Category.assoc, Functor.assoc,
              Functor.id_comp, Functor.comp_id, Functor.map_comp]
              using hn.symm
          simpa [Category.assoc] using
            congrArg (fun z => S.app X ≫ z) inner
        have hm : eqToHom a.symm ≫ eqToHom b = eqToHom m := by
          rw [CategoryTheory.eqToHom_trans]
        have hcoh :
            godementSimplicialDegeneracy Y s n i ≫
                godementSimplicialFace Y d n i.castSucc =
              eqToHom p ≫
                Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
                  (Functor.whiskerRight
                    (s ≫ Functor.whiskerRight d Y)
                    (iteratedEndofunctor Y (n - ↑i))) ≫
                eqToHom r ≫ eqToHom q.symm := by
          have hraw :
              godementSimplicialDegeneracy Y s n i ≫
                  godementSimplicialFace Y d n i.castSucc =
                eqToHom p ≫ S ≫ eqToHom a.symm ≫ eqToHom b ≫ D' ≫
                  eqToHom q.symm := by
            dsimp [p, q, S, D', godementSimplicialFace,
              godementSimplicialDegeneracy, godementFace, godementDegeneracy]
            simp
          have hhm :
              eqToHom p ≫ S ≫ eqToHom a.symm ≫ eqToHom b ≫ D' ≫
                  eqToHom q.symm =
                eqToHom p ≫ S ≫ eqToHom m ≫ D' ≫ eqToHom q.symm := by
            simpa only [Category.assoc] using
              congrArg (fun z => eqToHom p ≫ S ≫ z ≫ D' ≫ eqToHom q.symm) hm
          have hmid' :
              eqToHom p ≫ S ≫ eqToHom m ≫ D' ≫ eqToHom q.symm =
                eqToHom p ≫ S ≫ T ≫ eqToHom r ≫ eqToHom q.symm := by
            simpa only [Category.assoc] using
              congrArg (fun z => eqToHom p ≫ z ≫ eqToHom q.symm) hmid
          have hST : S ≫ T =
              Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
                (Functor.whiskerRight
                  (s ≫ Functor.whiskerRight d Y)
                  (iteratedEndofunctor Y (n - ↑i))) := by
            simp [S, T, Functor.whiskerLeft_comp,
              Functor.whiskerRight_comp, Functor.assoc]
          rw [hraw, hhm, hmid']
          simpa only [Category.assoc] using
            congrArg (fun z => eqToHom p ≫ z ≫ eqToHom r ≫ eqToHom q.symm) hST
        rw [hcoh]
        have hu := congrArg
          (fun z => eqToHom p ≫
            Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
              (Functor.whiskerRight z (iteratedEndofunctor Y (n - ↑i))) ≫
            eqToHom r ≫ eqToHom q.symm) h.left_unit
        simpa [Category.assoc, Functor.whiskerLeft_comp,
          Functor.whiskerRight_comp, Functor.assoc,
          CategoryTheory.eqToHom_trans,
          CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Functor.associator,
          Functor.leftUnitor, Functor.rightUnitor, r]
          using hu
      δ_comp_σ_succ := by
        intro n i
        change op (godementSimplicialDegeneracy Y s n i ≫
          godementSimplicialFace Y d n i.succ) = op (𝟙 _)
        congr 1
        ext X
        dsimp [godementSimplicialFace, godementSimplicialDegeneracy,
          godementFace, godementDegeneracy, godementDegree]
        simp [Category.assoc, CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_app]
        let p : godementDegree Y n =
            iteratedEndofunctor Y (↑i) ⋙ Y ⋙ iteratedEndofunctor Y (n - ↑i) := by
          change iteratedEndofunctor Y (n + 1) = _
          exact godementDegeneracy_domain_decomposition Y n i
        let q : godementDegree Y n =
            iteratedEndofunctor Y (↑i.succ) ⋙ 𝟭 C ⋙
              iteratedEndofunctor Y (n - ↑i) := by
          change iteratedEndofunctor Y (n + 1) = _
          have hi : (↑i.succ : ℕ) = (↑i : ℕ) + 1 := rfl
          have hk : n + 1 - (↑i.succ : ℕ) = n - (↑i : ℕ) := by omega
          simpa [hk] using
            (godementFace_codomain_decomposition Y (n + 1) i.succ)
        let r :
            (iteratedEndofunctor Y (↑i) ⋙ (Y ⋙ 𝟭 C) ⋙
                iteratedEndofunctor Y (n - ↑i)) =
              (iteratedEndofunctor Y (↑i.succ) ⋙ 𝟭 C ⋙
                iteratedEndofunctor Y (n - ↑i)) := by
          have hcomm : iteratedEndofunctor Y (↑i) ⋙ Y =
              Y ⋙ iteratedEndofunctor Y (↑i) := by
            calc
              iteratedEndofunctor Y (↑i) ⋙ Y =
                  iteratedEndofunctor Y (↑i) ⋙ iteratedEndofunctor Y 1 := by
                    simp [iteratedEndofunctor, Functor.comp_id]
              _ = iteratedEndofunctor Y ((↑i) + 1) :=
                (iteratedEndofunctor_add Y (↑i) 1).symm
              _ = iteratedEndofunctor Y (1 + (↑i : ℕ)) := by
                congr 1 <;> omega
              _ = iteratedEndofunctor Y 1 ⋙ iteratedEndofunctor Y (↑i) :=
                iteratedEndofunctor_add Y 1 (↑i)
              _ = Y ⋙ iteratedEndofunctor Y (↑i) := by
                simp [iteratedEndofunctor, Functor.comp_id]
          have hs : iteratedEndofunctor Y (↑i.succ) =
              iteratedEndofunctor Y (↑i) ⋙ Y := by
            calc
              iteratedEndofunctor Y (↑i.succ) =
                  Y ⋙ iteratedEndofunctor Y (↑i) := by
                    simp [iteratedEndofunctor]
              _ = iteratedEndofunctor Y (↑i) ⋙ Y := hcomm.symm
          rw [hs]
          simp only [Functor.assoc]
        let a : godementDegree Y (n + 1) =
            iteratedEndofunctor Y (↑i) ⋙ (Y ⋙ Y) ⋙
              iteratedEndofunctor Y (n - ↑i) := by
          change iteratedEndofunctor Y (n + 2) = _
          exact godementDegeneracy_codomain_decomposition Y n i
        let b : godementDegree Y (n + 1) =
            iteratedEndofunctor Y (↑i.succ) ⋙ Y ⋙
              iteratedEndofunctor Y (n - ↑i) := by
          change iteratedEndofunctor Y (n + 2) = _
          have hi : (↑i.succ : ℕ) = (↑i : ℕ) + 1 := rfl
          have hk : n + 1 - (↑i.succ : ℕ) = n - (↑i : ℕ) := by omega
          simpa [hk] using
            (godementFace_domain_decomposition Y (n + 1) i.succ)
        let m :
            (iteratedEndofunctor Y (↑i) ⋙ (Y ⋙ Y) ⋙
                iteratedEndofunctor Y (n - ↑i)) =
              (iteratedEndofunctor Y (↑i.succ) ⋙ Y ⋙
                iteratedEndofunctor Y (n - ↑i)) := by
          have hcomm : iteratedEndofunctor Y (↑i) ⋙ Y =
              Y ⋙ iteratedEndofunctor Y (↑i) := by
            calc
              iteratedEndofunctor Y (↑i) ⋙ Y =
                  iteratedEndofunctor Y (↑i) ⋙ iteratedEndofunctor Y 1 := by
                    simp [iteratedEndofunctor, Functor.comp_id]
              _ = iteratedEndofunctor Y ((↑i) + 1) :=
                (iteratedEndofunctor_add Y (↑i) 1).symm
              _ = iteratedEndofunctor Y (1 + (↑i : ℕ)) := by
                congr 1 <;> omega
              _ = iteratedEndofunctor Y 1 ⋙ iteratedEndofunctor Y (↑i) :=
                iteratedEndofunctor_add Y 1 (↑i)
              _ = Y ⋙ iteratedEndofunctor Y (↑i) := by
                simp [iteratedEndofunctor, Functor.comp_id]
          have hs : iteratedEndofunctor Y (↑i.succ) =
              iteratedEndofunctor Y (↑i) ⋙ Y := by
            calc
              iteratedEndofunctor Y (↑i.succ) =
                  Y ⋙ iteratedEndofunctor Y (↑i) := by
                    simp [iteratedEndofunctor]
              _ = iteratedEndofunctor Y (↑i) ⋙ Y := hcomm.symm
          rw [hs]
          simp only [Functor.assoc]
        let S :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
            (Functor.whiskerRight s (iteratedEndofunctor Y (n - ↑i)))
        let T :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
            (Functor.whiskerRight (Functor.whiskerLeft Y d)
              (iteratedEndofunctor Y (n - ↑i)))
        let D' :=
          Functor.whiskerLeft (iteratedEndofunctor Y (↑i.succ))
            (Functor.whiskerRight d (iteratedEndofunctor Y (n - ↑i)))
        have hmid : S ≫ eqToHom m ≫ D' = S ≫ T ≫ eqToHom r := by
          ext X
          have inner : (eqToHom m).app X ≫ D'.app X =
              T.app X ≫ (eqToHom r).app X := by
            dsimp [S, T, D']
            simp [Functor.assoc, Functor.id_comp, Functor.comp_id]
            have hcomm : iteratedEndofunctor Y (↑i) ⋙ Y =
                Y ⋙ iteratedEndofunctor Y (↑i) := by
              calc
                iteratedEndofunctor Y (↑i) ⋙ Y =
                    iteratedEndofunctor Y (↑i) ⋙ iteratedEndofunctor Y 1 := by
                      simp [iteratedEndofunctor, Functor.comp_id]
                _ = iteratedEndofunctor Y ((↑i) + 1) :=
                  (iteratedEndofunctor_add Y (↑i) 1).symm
                _ = iteratedEndofunctor Y (1 + (↑i : ℕ)) := by
                  congr 1 <;> omega
                _ = iteratedEndofunctor Y 1 ⋙ iteratedEndofunctor Y (↑i) :=
                  iteratedEndofunctor_add Y 1 (↑i)
                _ = Y ⋙ iteratedEndofunctor Y (↑i) := by
                  simp [iteratedEndofunctor, Functor.comp_id]
            have hn := CategoryTheory.eqToHom_naturality_assoc
              (fun F : C ⥤ C =>
                (iteratedEndofunctor Y (n - (↑i : ℕ))).map
                  (d.app (F.obj X))) hcomm (𝟙 _)
            simpa [S, m, r, hcomm, htail, iteratedEndofunctor, Category.assoc,
              Functor.assoc, Functor.id_comp, Functor.comp_id,
              Functor.map_comp] using hn.symm
          simpa [Category.assoc] using
            congrArg (fun z => S.app X ≫ z) inner
        have hm : eqToHom a.symm ≫ eqToHom b = eqToHom m := by
          rw [CategoryTheory.eqToHom_trans]
        have hcoh :
            godementSimplicialDegeneracy Y s n i ≫
                godementSimplicialFace Y d n i.succ =
              eqToHom p ≫
                Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
                  (Functor.whiskerRight
                    (s ≫ Functor.whiskerLeft Y d)
                    (iteratedEndofunctor Y (n - ↑i))) ≫
                eqToHom r ≫ eqToHom q.symm := by
          have hraw :
              godementSimplicialDegeneracy Y s n i ≫
                  godementSimplicialFace Y d n i.succ =
                eqToHom p ≫ S ≫ eqToHom a.symm ≫ eqToHom b ≫ D' ≫
                  eqToHom q.symm := by
            dsimp [p, q, S, D', godementSimplicialFace,
              godementSimplicialDegeneracy, godementFace, godementDegeneracy]
            simp
          have hhm :
              eqToHom p ≫ S ≫ eqToHom a.symm ≫ eqToHom b ≫ D' ≫
                  eqToHom q.symm =
                eqToHom p ≫ S ≫ eqToHom m ≫ D' ≫ eqToHom q.symm := by
            simpa only [Category.assoc] using
              congrArg (fun z => eqToHom p ≫ S ≫ z ≫ D' ≫ eqToHom q.symm) hm
          have hmid' :
              eqToHom p ≫ S ≫ eqToHom m ≫ D' ≫ eqToHom q.symm =
                eqToHom p ≫ S ≫ T ≫ eqToHom r ≫ eqToHom q.symm := by
            simpa only [Category.assoc] using
              congrArg (fun z => eqToHom p ≫ z ≫ eqToHom q.symm) hmid
          have hST : S ≫ T =
              Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
                (Functor.whiskerRight
                  (s ≫ Functor.whiskerLeft Y d)
                  (iteratedEndofunctor Y (n - ↑i))) := by
            simp [S, T, Functor.whiskerLeft_comp,
              Functor.whiskerRight_comp, Functor.assoc]
          rw [hraw, hhm, hmid']
          simpa only [Category.assoc] using
            congrArg (fun z => eqToHom p ≫ z ≫ eqToHom r ≫ eqToHom q.symm) hST
        rw [hcoh]
        have hu := congrArg
          (fun z => eqToHom p ≫
            Functor.whiskerLeft (iteratedEndofunctor Y (↑i))
              (Functor.whiskerRight z (iteratedEndofunctor Y (n - ↑i))) ≫
            eqToHom r ≫ eqToHom q.symm) h.right_unit
        simpa [Category.assoc, Functor.whiskerLeft_comp,
          Functor.whiskerRight_comp, Functor.assoc,
          CategoryTheory.eqToHom_trans,
          CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, r]
          using hu
      δ_comp_σ_of_gt := by
        intro n i j hji
        simp [godementSimplicialFace, godementSimplicialDegeneracy,
          godementFace, godementDegeneracy]
      σ_comp_σ := by
        intro n i j hij
        simp [godementSimplicialDegeneracy, godementDegeneracy] }
  let U := Formalization.Books.Simplicial.Unit02.simplicialObjectOfGeneratorData D
  refine ⟨{ object := U, object_obj := ?_, face_def := ?_, degeneracy_def := ?_ }⟩
  · intro n
    simpa [U, D] using
      (Formalization.Books.Simplicial.Unit02.simplicialObjectOfGeneratorData_obj D n)
  · intro n j
    simp [U, D, godementSimplicialFace]
  · intro n j
    simp [U, D, godementSimplicialDegeneracy]

-/

theorem godement_simplicial_object
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (SimplicialObject (C ⥤ C)) := by
  rcases godement_simplicial_data Y d s h with ⟨data⟩
  exact ⟨data.object⟩

/-- The degree-zero transformation used as the augmentation datum in Lemma 33.2.
The resulting simplicial augmentation is stored in `GodementAugmentationData`. -/
def godementAugmentation {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) : Y ⟶ 𝟭 C := d

/-- The canonical component of the augmentation in every degree. -/
def godementAugmentationComponent {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) : (n : ℕ) →
      godementDegree Y n ⟶ 𝟭 C
  | 0 => (Functor.rightUnitor Y).hom ≫ d
  | n + 1 =>
      Functor.whiskerLeft Y (godementAugmentationComponent Y d n) ≫
        Functor.whiskerRight d (𝟭 C) ≫ (Functor.leftUnitor (𝟭 C)).hom

structure GodementAugmentationData {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) where
  /-- The simplicial object whose degrees are the iterated endofunctors. -/
  simplicial : GodementSimplicialData Y d s
  /-- The augmentation as an actual morphism of simplicial objects. -/
  augmentation :
    Formalization.Books.Simplicial.Unit20.Augmentation
      simplicial.object (𝟭 C)
  component : ∀ n, godementDegree Y n ⟶ 𝟭 C
  component_zero : component 0 = godementAugmentationComponent Y d 0
  component_formula : ∀ n,
    eqToHom (simplicial.object_obj n).symm ≫
        augmentation.app (op (SimplexCategory.mk n)) = component n
  face_naturality : ∀ {n} (i : Fin (n + 2)),
    godementFace Y d (n := n + 1) i ≫ component n = component (n + 1)
  degeneracy_naturality : ∀ {n} (i : Fin (n + 1)),
    godementDegeneracy Y s (n := n) i ≫ component (n + 1) = component n

theorem godement_augmentation_condition
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementAugmentationData Y d s) := by
  rcases godement_simplicial_data Y d s h with ⟨data⟩
  let ε₀ : data.object.obj (op (SimplexCategory.mk 0)) ⟶ 𝟭 C :=
    eqToHom (data.object_obj 0) ≫ godementAugmentationComponent Y d 0
  have hface :
      godementFace Y d (n := 1) (0 : Fin 2) =
      godementFace Y d (n := 1) (1 : Fin 2) := by
    ext X
    have hp0 := godementFace_domain_decomposition Y 1 (0 : Fin 2)
    have hq0 := godementFace_codomain_decomposition Y 1 (0 : Fin 2)
    have hp1 := godementFace_domain_decomposition Y 1 (1 : Fin 2)
    have hq1 := godementFace_codomain_decomposition Y 1 (1 : Fin 2)
    dsimp [godementFace, godementDegree, iteratedEndofunctor]
    cases hp0
    cases hq0
    cases hp1
    cases hq1
    simp [Category.assoc, CategoryTheory.eqToHom_trans_assoc,
      CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl,
      CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_naturality_assoc,
      iteratedEndofunctor, Functor.assoc, Functor.comp_id, Functor.id_comp,
      Functor.map_comp,
      Functor.associator, Functor.leftUnitor, Functor.rightUnitor,
      d.naturality]
  have hface' :
      godementSimplicialFace Y d 0 (0 : Fin 2) =
        godementSimplicialFace Y d 0 (1 : Fin 2) := hface
  have hε₀ :
      data.object.δ (0 : Fin 2) ≫ ε₀ =
        data.object.δ (1 : Fin 2) ≫ ε₀ := by
    have h0 := data.face_def 0 (0 : Fin 2)
    have h1 := data.face_def 0 (1 : Fin 2)
    have h0' := congrArg
      (fun z => eqToHom (data.object_obj 1) ≫ z) h0
    have h1' := congrArg
      (fun z => eqToHom (data.object_obj 1) ≫ z) h1
    have hh0 : data.object.δ (0 : Fin 2) ≫ eqToHom (data.object_obj 0) =
        eqToHom (data.object_obj 1) ≫ godementSimplicialFace Y d 0 0 := by
      simpa [Category.assoc] using h0'
    have hh1 : data.object.δ (1 : Fin 2) ≫ eqToHom (data.object_obj 0) =
        eqToHom (data.object_obj 1) ≫ godementSimplicialFace Y d 0 1 := by
      simpa [Category.assoc] using h1'
    dsimp [ε₀]
    conv_lhs => rw [← Category.assoc]
    conv_rhs => rw [← Category.assoc]
    rw [hh0, hh1, hface']
  have haugment : ∀ (n : SimplexCategory)
      (g₁ g₂ : SimplexCategory.mk 0 ⟶ n),
      data.object.map g₁.op ≫ ε₀ = data.object.map g₂.op ≫ ε₀ := by
    intro n g₁ g₂
    rw [SimplexCategory.eq_const_of_zero g₁,
      SimplexCategory.eq_const_of_zero g₂]
    rcases le_total (g₁.toOrderHom 0) (g₂.toOrderHom 0) with hle | hge
    · let e := SimplexCategory.mkOfLe (g₁.toOrderHom 0) (g₂.toOrderHom 0) hle
      have he0 : SimplexCategory.δ (0 : Fin 2) ≫ e =
          SimplexCategory.const _ _ (g₂.toOrderHom 0) := by
        apply SimplexCategory.Hom.ext_zero_left
        rfl
      have he1 : SimplexCategory.δ (1 : Fin 2) ≫ e =
          SimplexCategory.const _ _ (g₁.toOrderHom 0) := by
        apply SimplexCategory.Hom.ext_zero_left
        rfl
      rw [← he1, ← he0]
      have hd := hε₀
      change data.object.map (SimplexCategory.δ (0 : Fin 2)).op ≫ ε₀ =
        data.object.map (SimplexCategory.δ (1 : Fin 2)).op ≫ ε₀ at hd
      simpa only [op_comp, data.object.map_comp, Category.assoc] using
        congrArg (fun k => data.object.map e.op ≫ k) hd.symm
    · let e := SimplexCategory.mkOfLe (g₂.toOrderHom 0) (g₁.toOrderHom 0) hge
      have he0 : SimplexCategory.δ (0 : Fin 2) ≫ e =
          SimplexCategory.const _ _ (g₁.toOrderHom 0) := by
        apply SimplexCategory.Hom.ext_zero_left
        rfl
      have he1 : SimplexCategory.δ (1 : Fin 2) ≫ e =
          SimplexCategory.const _ _ (g₂.toOrderHom 0) := by
        apply SimplexCategory.Hom.ext_zero_left
        rfl
      rw [← he0, ← he1]
      have hd := hε₀
      change data.object.map (SimplexCategory.δ (0 : Fin 2)).op ≫ ε₀ =
        data.object.map (SimplexCategory.δ (1 : Fin 2)).op ≫ ε₀ at hd
      simpa only [op_comp, data.object.map_comp, Category.assoc] using
        congrArg (fun k => data.object.map e.op ≫ k) hd
  let ε : Formalization.Books.Simplicial.Unit20.Augmentation
      data.object (𝟭 C) :=
    (SimplicialObject.augment data.object (𝟭 C) ε₀ haugment).hom
  let component : ∀ n, godementDegree Y n ⟶ 𝟭 C := fun n =>
    eqToHom (data.object_obj n).symm ≫
      ε.app (op (SimplexCategory.mk n))
  have hε₀_app :
      ε.app (op (SimplexCategory.mk 0)) = ε₀ := by
    dsimp [ε]
    exact SimplicialObject.augment_hom_zero data.object (𝟭 C) ε₀ _
  refine ⟨{
    simplicial := data
    augmentation := ε
    component := component
    component_zero := ?_
    component_formula := ?_
    face_naturality := ?_
    degeneracy_naturality := ?_ }⟩
  · change eqToHom (data.object_obj 0).symm ≫
      ε.app (op (SimplexCategory.mk 0)) =
        godementAugmentationComponent Y d 0
    rw [hε₀_app]
    dsimp [ε₀]
    simp [Category.assoc]
  · intro n
    rfl
  · intro n i
    dsimp [component]
    change godementSimplicialFace Y d n i ≫
      eqToHom (data.object_obj n).symm ≫
        ε.app (op (SimplexCategory.mk n)) = _
    rw [← data.face_def n i]
    have hn := ε.naturality (SimplexCategory.δ i).op
    have hn' : data.object.map (SimplexCategory.δ i).op ≫
        ε.app (op (SimplexCategory.mk n)) =
      ε.app (op (SimplexCategory.mk (n + 1))) ≫ 𝟙 (𝟭 C) := by
      exact hn
    have hn'' := congrArg
      (fun z => eqToHom (data.object_obj (n + 1)).symm ≫ z) hn'
    have hid : ε.app (op (SimplexCategory.mk (n + 1))) ≫ 𝟙 (𝟭 C) =
        ε.app (op (SimplexCategory.mk (n + 1))) := Category.comp_id _
    rw [hid] at hn''
    simpa only [SimplicialObject.δ, Category.assoc, Category.comp_id,
      Category.id_comp,
      CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_trans,
      CategoryTheory.eqToHom_refl] using hn''
  · intro n i
    dsimp [component]
    change godementSimplicialDegeneracy Y s n i ≫
      eqToHom (data.object_obj (n + 1)).symm ≫
        ε.app (op (SimplexCategory.mk (n + 1))) = _
    rw [← data.degeneracy_def n i]
    have hn := ε.naturality (SimplexCategory.σ i).op
    have hn' : data.object.map (SimplexCategory.σ i).op ≫
        ε.app (op (SimplexCategory.mk (n + 1))) =
      ε.app (op (SimplexCategory.mk n)) ≫ 𝟙 (𝟭 C) := by
      exact hn
    have hn'' := congrArg
      (fun z => eqToHom (data.object_obj n).symm ≫ z) hn'
    have hid : ε.app (op (SimplexCategory.mk n)) ≫ 𝟙 (𝟭 C) =
        ε.app (op (SimplexCategory.mk n)) := Category.comp_id _
    rw [hid] at hn''
    simpa only [SimplicialObject.σ, Category.assoc, Category.comp_id,
      Category.id_comp,
      CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_trans,
      CategoryTheory.eqToHom_refl] using hn''

/-! ## Functoriality and sections -/

/-- Whiskering a Godement degree by `F` and `G`. -/
def godementWhiskeredDegree {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (n : ℕ) : A ⥤ B :=
  F ⋙ godementDegree Y n ⋙ G

def godementWhiskeredFace {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (d : Y ⟶ 𝟭 C)
    {n : ℕ} (j : Fin (n + 1)) :
    godementWhiskeredDegree F Y G n ⟶ F ⋙ iteratedEndofunctor Y n ⋙ G :=
  Functor.whiskerRight (Functor.whiskerLeft F (godementFace Y d j)) G

def godementWhiskeredDegeneracy {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (s : Y ⟶ Y ⋙ Y)
    {n : ℕ} (j : Fin (n + 1)) :
    godementWhiskeredDegree F Y G n ⟶
      godementWhiskeredDegree F Y G (n + 1) :=
  Functor.whiskerRight (Functor.whiskerLeft F (godementDegeneracy Y s j)) G

def godementWhiskeredSimplicialFace {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (d : Y ⟶ 𝟭 C)
    (n : ℕ) (j : Fin (n + 2)) :
    godementWhiskeredDegree F Y G (n + 1) ⟶
      godementWhiskeredDegree F Y G n :=
  godementWhiskeredFace F Y G d j

def godementWhiskeredSimplicialDegeneracy
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (s : Y ⟶ Y ⋙ Y)
    (n : ℕ) (j : Fin (n + 1)) :
    godementWhiskeredDegree F Y G n ⟶
      godementWhiskeredDegree F Y G (n + 1) :=
  godementWhiskeredDegeneracy F Y G s j

def godementWhiskeredAugmentationComponent
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (d : Y ⟶ 𝟭 C) (n : ℕ) :
    godementWhiskeredDegree F Y G n ⟶ F ⋙ G := by
  exact
    Functor.whiskerRight
      (Functor.whiskerLeft F (godementAugmentationComponent Y d n)) G ≫
      (Functor.associator F (𝟭 C) G).hom ≫
      Functor.whiskerLeft F (Functor.rightUnitor G).hom

structure GodementWhiskeredSimplicialData
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) where
  object : SimplicialObject (A ⥤ B)
  object_obj : ∀ n,
    object.obj (op (SimplexCategory.mk n)) = godementWhiskeredDegree F Y G n
  face_def : ∀ n (j : Fin (n + 2)),
    eqToHom (object_obj (n + 1)).symm ≫ object.δ j ≫
        eqToHom (object_obj n) =
      godementWhiskeredSimplicialFace F Y G d n j
  degeneracy_def : ∀ n (j : Fin (n + 1)),
    eqToHom (object_obj n).symm ≫ object.σ j ≫
        eqToHom (object_obj (n + 1)) =
      godementWhiskeredSimplicialDegeneracy F Y G s n j

/-! The functorial example carries the canonical degreewise maps above as an
augmentation of the whiskered simplicial object. -/

structure GodementWhiskeredAugmentationData
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) where
  /-- The simplicial object receiving the augmentation. -/
  simplicial : GodementWhiskeredSimplicialData F Y G d s
  /-- The augmentation of the whiskered simplicial object. -/
  augmentation :
    Formalization.Books.Simplicial.Unit20.Augmentation
      simplicial.object (F ⋙ G)
  component : ∀ n, godementWhiskeredDegree F Y G n ⟶ F ⋙ G
  component_def : ∀ n,
    component n = godementWhiskeredAugmentationComponent F Y G d n
  component_formula : ∀ n,
    eqToHom (simplicial.object_obj n).symm ≫
        augmentation.app (op (SimplexCategory.mk n)) = component n
  face_naturality : ∀ {n} (i : Fin (n + 2)),
    godementWhiskeredSimplicialFace F Y G d n i ≫ component n =
      component (n + 1)
  degeneracy_naturality : ∀ {n} (i : Fin (n + 1)),
    godementWhiskeredSimplicialDegeneracy F Y G s n i ≫ component (n + 1) =
      component n

theorem godement_functorial
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementWhiskeredSimplicialData F Y G d s) ∧
      Nonempty (SimplicialObject (A ⥤ B)) := by
  rcases godement_simplicial_data Y d s h with ⟨data⟩
  let WL := (Functor.whiskeringLeft A C C).obj F
  let WR := (Functor.whiskeringRight A C B).obj G
  let W : (C ⥤ C) ⥤ (A ⥤ B) := WL ⋙ WR
  let object : SimplicialObject (A ⥤ B) :=
    ((SimplicialObject.whiskering (C ⥤ C) (A ⥤ B)).obj W).obj data.object
  have hobj : ∀ n,
      object.obj (op (SimplexCategory.mk n)) =
        godementWhiskeredDegree F Y G n := by
    intro n
    simpa [object, W, WL, WR, godementWhiskeredDegree,
      data.object_obj n, Category.assoc, Functor.assoc]
  have hobj_eq (n : ℕ) :
      eqToHom (hobj n) = W.map (eqToHom (data.object_obj n)) := by
    change eqToHom (hobj n) = W.map (eqToHom (data.object_obj n))
    rw [CategoryTheory.eqToHom_map]
    rfl
  have hobj_eq_symm (n : ℕ) :
      eqToHom (hobj n).symm = W.map (eqToHom (data.object_obj n).symm) := by
    change eqToHom (hobj n).symm = W.map (eqToHom (data.object_obj n).symm)
    rw [CategoryTheory.eqToHom_map]
    rfl
  have hsimp : GodementWhiskeredSimplicialData F Y G d s := by
    refine {
      object := object
      object_obj := hobj
      face_def := ?_
      degeneracy_def := ?_ }
    · intro n j
      have hf := congrArg W.map (data.face_def n j)
      convert hf using 1
      · simp [object, W, WL, WR, hobj, Category.assoc,
          CategoryTheory.eqToHom_map, godementWhiskeredDegree,
          godementWhiskeredSimplicialFace, godementWhiskeredFace,
          Functor.whiskerLeft_comp, Functor.whiskerRight_comp,
          Functor.assoc, Functor.whiskerLeft, Functor.whiskerRight]
      · apply heq_of_eq
        ext X
        dsimp [Functor.whiskerRight, Functor.whiskerLeft]
        simp [object, W, WL, WR, hobj, Category.assoc,
          CategoryTheory.eqToHom_map, SimplicialObject.whiskering_obj_obj_δ,
          Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.whiskerRight_app]
        congr 1
      · apply heq_of_eq
        ext X
        simp [godementWhiskeredSimplicialFace, godementWhiskeredFace,
          godementSimplicialFace, W, WL, WR, Functor.whiskerLeft,
          Functor.whiskerRight]
        change G.map ((godementFace Y d j).app (F.obj X)) =
          G.map ((godementFace Y d j).app (F.obj X))
        rfl
    · intro n j
      have hs := congrArg W.map (data.degeneracy_def n j)
      convert hs using 1
      · simp [object, W, WL, WR, hobj, Category.assoc,
          CategoryTheory.eqToHom_map, godementWhiskeredDegree,
          godementWhiskeredSimplicialDegeneracy, godementWhiskeredDegeneracy,
          Functor.whiskerLeft_comp, Functor.whiskerRight_comp,
          Functor.assoc, Functor.whiskerLeft, Functor.whiskerRight]
      · apply heq_of_eq
        ext X
        dsimp [Functor.whiskerRight, Functor.whiskerLeft]
        simp [object, W, WL, WR, hobj, Category.assoc,
          CategoryTheory.eqToHom_map, SimplicialObject.whiskering_obj_obj_σ,
          Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.whiskerRight_app]
        congr 1
      · apply heq_of_eq
        ext X
        rfl
  exact ⟨⟨hsimp⟩, ⟨object⟩⟩

theorem godement_whiskered_augmentation_condition
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementWhiskeredAugmentationData F Y G d s) := by
  rcases godement_augmentation_condition Y d s h with ⟨base⟩
  let WL := (Functor.whiskeringLeft A C C).obj F
  let WR := (Functor.whiskeringRight A C B).obj G
  let W : (C ⥤ C) ⥤ (A ⥤ B) := WL ⋙ WR
  let K : W.obj (𝟭 C) ⟶ F ⋙ G :=
    (Functor.associator F (𝟭 C) G).hom ≫
      Functor.whiskerLeft F (Functor.rightUnitor G).hom
  let object : SimplicialObject (A ⥤ B) :=
    ((SimplicialObject.whiskering (C ⥤ C) (A ⥤ B)).obj W).obj
      base.simplicial.object
  have hobj : ∀ n,
      object.obj (op (SimplexCategory.mk n)) =
        godementWhiskeredDegree F Y G n := by
    intro n
    simpa [object, W, WL, WR, godementWhiskeredDegree,
      base.simplicial.object_obj n, Category.assoc, Functor.assoc]
  have hobj_eq (n : ℕ) :
      eqToHom (hobj n) = W.map (eqToHom (base.simplicial.object_obj n)) := by
    change eqToHom (hobj n) = W.map (eqToHom (base.simplicial.object_obj n))
    rw [CategoryTheory.eqToHom_map]
    rfl
  have hobj_eq_symm (n : ℕ) :
      eqToHom (hobj n).symm =
        W.map (eqToHom (base.simplicial.object_obj n).symm) := by
    change eqToHom (hobj n).symm =
      W.map (eqToHom (base.simplicial.object_obj n).symm)
    rw [CategoryTheory.eqToHom_map]
    rfl
  let rawAug : object ⟶
      ((SimplicialObject.whiskering (C ⥤ C) (A ⥤ B)).obj W).obj
        ((SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) :=
    ((SimplicialObject.whiskering (C ⥤ C) (A ⥤ B)).obj W).map
      base.augmentation
  let Ksim :
      ((SimplicialObject.whiskering (C ⥤ C) (A ⥤ B)).obj W).obj
          ((SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) ⟶
        (SimplicialObject.const (A ⥤ B)).obj (F ⋙ G) :=
    { app := fun _ => K
      naturality := by
        intro n m f
        change W.map (((SimplicialObject.const (C ⥤ C)).obj (𝟭 C)).map f) ≫ K =
          K ≫ ((SimplicialObject.const (A ⥤ B)).obj (F ⋙ G)).map f
        rw [show ((SimplicialObject.const (C ⥤ C)).obj (𝟭 C)).map f =
            𝟙 (𝟭 C) by rfl]
        rw [show ((SimplicialObject.const (A ⥤ B)).obj (F ⋙ G)).map f =
            𝟙 (F ⋙ G) by rfl]
        simp }
  let augmentation : object ⟶ (SimplicialObject.const (A ⥤ B)).obj (F ⋙ G) :=
    rawAug ≫ Ksim
  let component : ∀ n, godementWhiskeredDegree F Y G n ⟶ F ⋙ G := fun n =>
    eqToHom (hobj n).symm ≫ augmentation.app (op (SimplexCategory.mk n))
  have hcanonical : ∀ n,
      godementFace Y d (n := n + 1) (0 : Fin (n + 2)) ≫
          godementAugmentationComponent Y d n =
        godementAugmentationComponent Y d (n + 1) := by
    intro n
    have hraw :
        Functor.whiskerRight d (godementDegree Y n) ≫
            godementAugmentationComponent Y d n =
          Functor.whiskerLeft Y (godementAugmentationComponent Y d n) ≫
            Functor.whiskerRight d (𝟭 C) ≫ (Functor.leftUnitor (𝟭 C)).hom := by
      ext X
      simp only [NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.comp_map,
        Functor.leftUnitor_hom_app]
      change (godementDegree Y n).map (d.app X) ≫
          (godementAugmentationComponent Y d n).app X =
        (godementAugmentationComponent Y d n).app (Y.obj X) ≫
          (𝟭 C).map (d.app X) ≫ 𝟙 ((𝟭 C).obj X)
      simpa only [Functor.id_obj, Functor.id_map, Category.comp_id] using
        (godementAugmentationComponent Y d n).naturality (d.app X)
    have hface_aug :
        godementFace Y d (n := n + 1) (0 : Fin (n + 2)) ≫
            godementAugmentationComponent Y d n =
          Functor.whiskerRight d (godementDegree Y n) ≫
            godementAugmentationComponent Y d n := by
      let hp := godementFace_domain_decomposition Y (n + 1) (0 : Fin (n + 2))
      let hq := godementFace_codomain_decomposition Y (n + 1) (0 : Fin (n + 2))
      let raw := Functor.whiskerLeft (iteratedEndofunctor Y 0)
        (Functor.whiskerRight d (iteratedEndofunctor Y (n + 1 - 0)))
      have hconj : Functor.whiskerRight d (godementDegree Y n) =
          eqToHom hp ≫ raw ≫ eqToHom hq.symm := by
        apply (CategoryTheory.conj_eqToHom_iff_heq _ _ hp hq).2
        dsimp [raw, godementDegree, iteratedEndofunctor]
        rfl
      have hface : godementFace Y d (n := n + 1) (0 : Fin (n + 2)) =
          eqToHom hp ≫ raw ≫ eqToHom hq.symm := by
        dsimp [godementFace, hp, hq, raw]
        congr 1 <;> apply Subsingleton.elim
      rw [hface, ← hconj]
      rfl
    calc
      _ = Functor.whiskerRight d (godementDegree Y n) ≫
          godementAugmentationComponent Y d n := hface_aug
      _ = _ := hraw
  have hbase_component : ∀ n,
      base.component n = godementAugmentationComponent Y d n := by
    intro n
    induction n with
    | zero => exact base.component_zero
    | succ n ih =>
        rw [← base.face_naturality (i := (0 : Fin (n + 2))), ih,
          hcanonical]
  have hface_def : ∀ n (j : Fin (n + 2)),
      eqToHom (hobj (n + 1)).symm ≫ object.δ j ≫ eqToHom (hobj n) =
        godementWhiskeredSimplicialFace F Y G d n j := by
    intro n j
    have hf := congrArg W.map (base.simplicial.face_def n j)
    convert hf using 1
    · simp [object, W, WL, WR, hobj, Category.assoc,
        CategoryTheory.eqToHom_map, godementWhiskeredDegree,
        godementWhiskeredSimplicialFace, godementWhiskeredFace,
        Functor.whiskerLeft_comp, Functor.whiskerRight_comp,
        Functor.assoc, Functor.whiskerLeft, Functor.whiskerRight]
    · apply heq_of_eq
      ext X
      dsimp [Functor.whiskerRight, Functor.whiskerLeft]
      simp [object, W, WL, WR, hobj, Category.assoc,
        CategoryTheory.eqToHom_map, SimplicialObject.whiskering_obj_obj_δ,
        Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app]
      congr 1
    · apply heq_of_eq
      ext X
      simp [godementWhiskeredSimplicialFace, godementWhiskeredFace,
        godementSimplicialFace, W, WL, WR, Functor.whiskerLeft,
        Functor.whiskerRight]
      change G.map ((godementFace Y d j).app (F.obj X)) =
        G.map ((godementFace Y d j).app (F.obj X))
      rfl
  have hdeg_def : ∀ n (j : Fin (n + 1)),
      eqToHom (hobj n).symm ≫ object.σ j ≫ eqToHom (hobj (n + 1)) =
        godementWhiskeredSimplicialDegeneracy F Y G s n j := by
    intro n j
    have hs := congrArg W.map (base.simplicial.degeneracy_def n j)
    convert hs using 1
    · simp [object, W, WL, WR, hobj, Category.assoc,
        CategoryTheory.eqToHom_map, godementWhiskeredDegree,
        godementWhiskeredSimplicialDegeneracy, godementWhiskeredDegeneracy,
        Functor.whiskerLeft_comp, Functor.whiskerRight_comp,
        Functor.assoc, Functor.whiskerLeft, Functor.whiskerRight]
    · apply heq_of_eq
      ext X
      dsimp [Functor.whiskerRight, Functor.whiskerLeft]
      simp [object, W, WL, WR, hobj, Category.assoc,
        CategoryTheory.eqToHom_map, SimplicialObject.whiskering_obj_obj_σ,
        Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app]
      congr 1
    · apply heq_of_eq
      ext X
      rfl
  refine ⟨{
    simplicial := {
      object := object
      object_obj := hobj
      face_def := hface_def
      degeneracy_def := hdeg_def }
    augmentation := augmentation
    component := component
    component_def := ?_
    component_formula := ?_
    face_naturality := ?_
    degeneracy_naturality := ?_ }⟩
  · intro n
    have hc := congrArg W.map (base.component_formula n)
    rw [hbase_component n] at hc
    have hcK := congrArg (fun t => t ≫ K) hc
    dsimp [component, augmentation, rawAug]
    rw [hobj_eq_symm n]
    ext X
    change
      (W.map (eqToHom (base.simplicial.object_obj n).symm)).app X ≫
      (W.map (base.augmentation.app (op (SimplexCategory.mk n)))).app X ≫
            K.app X =
        G.map ((godementAugmentationComponent Y d n).app (F.obj X)) ≫
          𝟙 (G.obj (F.obj X)) ≫ 𝟙 (G.obj (F.obj X))
    have hk := congrArg (fun z => z.app X) hcK
    simp only [Functor.map_comp, NatTrans.comp_app,
      Category.comp_id, Category.id_comp] at hk
    dsimp [W, WL, WR, K] at hk
    simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_hom_app, NatTrans.comp_app,
      Category.comp_id, Category.id_comp] at hk
    dsimp [W, WL, WR, K]
    simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_hom_app, NatTrans.comp_app,
      Category.comp_id, Category.id_comp]
    exact hk
  · intro n
    rfl
  · intro n i
    dsimp [component]
    change godementWhiskeredSimplicialFace F Y G d n i ≫
      eqToHom (hobj n).symm ≫
        augmentation.app (op (SimplexCategory.mk n)) = _
    rw [← hface_def n i]
    have hn := augmentation.naturality (SimplexCategory.δ i).op
    have hn' : object.map (SimplexCategory.δ i).op ≫
        augmentation.app (op (SimplexCategory.mk n)) =
      augmentation.app (op (SimplexCategory.mk (n + 1))) ≫ 𝟙 (F ⋙ G) := by
      exact hn
    have hn'' := congrArg
      (fun z => eqToHom (hobj (n + 1)).symm ≫ z) hn'
    have hid : augmentation.app (op (SimplexCategory.mk (n + 1))) ≫
        𝟙 (F ⋙ G) = augmentation.app (op (SimplexCategory.mk (n + 1))) :=
      Category.comp_id _
    rw [hid] at hn''
    simpa only [SimplicialObject.δ, Category.assoc, Category.comp_id,
      Category.id_comp, CategoryTheory.eqToHom_trans_assoc,
      CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl] using hn''
  · intro n i
    dsimp [component]
    change godementWhiskeredSimplicialDegeneracy F Y G s n i ≫
      eqToHom (hobj (n + 1)).symm ≫
        augmentation.app (op (SimplexCategory.mk (n + 1))) = _
    rw [← hdeg_def n i]
    have hn := augmentation.naturality (SimplexCategory.σ i).op
    have hn' : object.map (SimplexCategory.σ i).op ≫
        augmentation.app (op (SimplexCategory.mk (n + 1))) =
      augmentation.app (op (SimplexCategory.mk n)) ≫ 𝟙 (F ⋙ G) := by
      exact hn
    have hn'' := congrArg
      (fun z => eqToHom (hobj n).symm ≫ z) hn'
    have hid : augmentation.app (op (SimplexCategory.mk n)) ≫
        𝟙 (F ⋙ G) = augmentation.app (op (SimplexCategory.mk n)) :=
      Category.comp_id _
    rw [hid] at hn''
    simpa only [SimplicialObject.σ, Category.assoc, Category.comp_id,
      Category.id_comp, CategoryTheory.eqToHom_trans_assoc,
      CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl] using hn''

theorem godement_functorial_with_augmentation
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s) :
    Nonempty (GodementWhiskeredSimplicialData F Y G d s) ∧
      Nonempty (GodementWhiskeredAugmentationData F Y G d s) := by
  exact ⟨(godement_functorial F Y G d s h).1,
    godement_whiskered_augmentation_condition F Y G d s h⟩

def godementZeroMap {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) :
    F ⋙ Y ⋙ G ⟶ godementWhiskeredDegree F Y G 0 :=
  Functor.whiskerRight
    (Functor.whiskerLeft F (Functor.rightUnitor Y).inv) G

/-- The degree-zero augmentation after transporting the explicit source
`F ⋙ Y ⋙ G` to the chosen degree-zero object. -/
def godementWhiskeredDegreeZeroAugmentation
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B) (d : Y ⟶ 𝟭 C) :
    F ⋙ Y ⋙ G ⟶ F ⋙ G :=
  godementZeroMap F Y G ≫
    godementWhiskeredAugmentationComponent F Y G d 0

/-! This is the component formula used in the proof of the section lemma. -/

def godementWhiskeredSectionComponent
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (data : GodementWhiskeredSimplicialData F Y G d s)
    (h₀ : F ⋙ G ⟶ F ⋙ Y ⋙ G) (n : ℕ) :
    F ⋙ G ⟶ godementWhiskeredDegree F Y G n :=
  h₀ ≫ godementZeroMap F Y G ≫ eqToHom (data.object_obj 0).symm ≫
    simplicialUnitMap data.object n ≫ eqToHom (data.object_obj n)

/-! A section is recorded as an actual morphism of simplicial objects.  The
degreewise component structure below is retained as the explicit source-facing
normal form for calculations with the Godement maps. -/

structure GodementAugmentationSection
    {D : Type u} [Category.{v} D]
    (U : SimplicialObject D) (X : D)
    (ε : Formalization.Books.Simplicial.Unit20.Augmentation U X) where
  map : (SimplicialObject.const D).obj X ⟶ U
  section_condition : map ≫ ε = 𝟙 ((SimplicialObject.const D).obj X)

theorem godement_section_morphism
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (data : GodementWhiskeredAugmentationData F Y G d s)
    (h₀ : F ⋙ G ⟶ F ⋙ Y ⋙ G)
    (h₀_condition : h₀ ≫ godementWhiskeredDegreeZeroAugmentation F Y G d =
      𝟙 (F ⋙ G)) :
    Nonempty (GodementAugmentationSection data.simplicial.object
      (F ⋙ G) data.augmentation) := by
  let h0 : F ⋙ G ⟶ data.simplicial.object.obj
      (op (SimplexCategory.mk 0)) :=
    h₀ ≫ godementZeroMap F Y G ≫
      eqToHom (data.simplicial.object_obj 0).symm
  let q : ∀ n : SimplexCategoryᵒᵖ,
      op (SimplexCategory.mk 0) ⟶ n :=
    fun n => (SimplexCategory.const n.unop
      (SimplexCategory.mk 0) 0).op
  let app : ∀ n : SimplexCategoryᵒᵖ, F ⋙ G ⟶
      data.simplicial.object.obj n := fun n =>
    h0 ≫ data.simplicial.object.map (q n)
  let map : (SimplicialObject.const (A ⥤ B)).obj (F ⋙ G) ⟶
      data.simplicial.object :=
    { app := app
      naturality := by
        intro X Y f
        let qX := q X
        let qY := q Y
        have hq : qY = qX ≫ f := by
          dsimp [q, qX, qY]
          apply Quiver.Hom.unop_inj
          change SimplexCategory.const Y.unop (SimplexCategory.mk 0) 0 =
            f.unop ≫ SimplexCategory.const X.unop
              (SimplexCategory.mk 0) 0
          exact (SimplexCategory.eq_const_to_zero _).symm
        have hconst :
            ((SimplicialObject.const (A ⥤ B)).obj (F ⋙ G)).map f =
              𝟙 (F ⋙ G) := by
          simp
        change ((SimplicialObject.const (A ⥤ B)).obj (F ⋙ G)).map f ≫
            (h0 ≫ data.simplicial.object.map qY) =
          (h0 ≫ data.simplicial.object.map qX) ≫
            data.simplicial.object.map f
        rw [hconst, hq, Functor.map_comp]
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ data.simplicial.object.map qX ≫
            data.simplicial.object.map f) (Category.id_comp h0) }
  refine ⟨{ map := map, section_condition := ?_ }⟩
  apply SimplicialObject.hom_ext
  intro n
  have hn := data.augmentation.naturality (q n)
  have hconst :
      ((SimplicialObject.const (A ⥤ B)).obj (F ⋙ G)).map (q n) =
        𝟙 (F ⋙ G) := by
    simp
  rw [hconst] at hn
  have hzero :
      eqToHom (data.simplicial.object_obj 0).symm ≫
          data.augmentation.app (op (SimplexCategory.mk 0)) =
        godementWhiskeredAugmentationComponent F Y G d 0 := by
    rw [data.component_formula 0, data.component_def 0]
  change app n ≫ data.augmentation.app n = 𝟙 (F ⋙ G)
  dsimp [app]
  rw [Category.assoc, hn]
  have hid : (h0 ≫ data.augmentation.app
      (op (SimplexCategory.mk 0))) ≫ 𝟙 (F ⋙ G) =
      h0 ≫ data.augmentation.app (op (SimplexCategory.mk 0)) :=
    Category.comp_id _
  rw [← Category.assoc, hid]
  have hz := congrArg
    (fun z => h₀ ≫ godementZeroMap F Y G ≫ z) hzero
  dsimp [h0]
  have hz' :
      (h₀ ≫ godementZeroMap F Y G ≫
          eqToHom (data.simplicial.object_obj 0).symm) ≫
          data.augmentation.app (op (SimplexCategory.mk 0)) =
        h₀ ≫ godementZeroMap F Y G ≫
          godementWhiskeredAugmentationComponent F Y G d 0 := by
    simpa only [Category.assoc] using hz
  rw [hz']
  simpa [godementWhiskeredDegreeZeroAugmentation, Category.assoc] using
    h₀_condition

structure GodementSection {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (h₀ : F ⋙ G ⟶ F ⋙ Y ⋙ G) where
  component : ∀ n, F ⋙ G ⟶ godementWhiskeredDegree F Y G n
  component_zero : component 0 =
    h₀ ≫ godementZeroMap F Y G
  face_naturality : ∀ {n} (i : Fin (n + 2)),
    component (n + 1) ≫ godementWhiskeredSimplicialFace F Y G d n i =
      component n
  degeneracy_naturality : ∀ {n} (i : Fin (n + 1)),
    component n ≫ godementWhiskeredSimplicialDegeneracy F Y G s n i =
      component (n + 1)
  augmentation : ∀ n,
    component n ≫ godementWhiskeredAugmentationComponent F Y G d n = 𝟙 (F ⋙ G)

theorem godement_section_components
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (G : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (h₀ : F ⋙ G ⟶ F ⋙ Y ⋙ G)
    (h₀_condition :
      h₀ ≫ godementWhiskeredDegreeZeroAugmentation F Y G d =
        𝟙 (F ⋙ G))
    (h : GodementEquations Y d s) :
    Nonempty (GodementSection F Y G d s h₀) := by
  rcases godement_functorial_with_augmentation F Y G d s h with
    ⟨_, ⟨data⟩⟩
  let component : ∀ n, F ⋙ G ⟶ godementWhiskeredDegree F Y G n := fun n =>
    godementWhiskeredSectionComponent F Y G d s data.simplicial h₀ n
  let h0 : F ⋙ G ⟶ data.simplicial.object.obj
      (op (SimplexCategory.mk 0)) :=
    h₀ ≫ godementZeroMap F Y G ≫
      eqToHom (data.simplicial.object_obj 0).symm
  let q : ∀ n : SimplexCategoryᵒᵖ,
      op (SimplexCategory.mk 0) ⟶ n :=
    fun n => (SimplexCategory.const n.unop
      (SimplexCategory.mk 0) 0).op
  refine ⟨{
    component := component
    component_zero := ?_
    face_naturality := ?_
    degeneracy_naturality := ?_
    augmentation := ?_ }⟩
  · dsimp [component, godementWhiskeredSectionComponent]
    simp [simplicialUnitMap, Category.assoc]
  · intro n i
    dsimp [component, godementWhiskeredSectionComponent]
    have hq : q (op (SimplexCategory.mk n)) =
        q (op (SimplexCategory.mk (n + 1))) ≫
          (SimplexCategory.δ i).op := by
      dsimp [q]
      apply Quiver.Hom.unop_inj
      change SimplexCategory.const (SimplexCategory.mk n)
          (SimplexCategory.mk 0) 0 =
        SimplexCategory.δ i ≫
          SimplexCategory.const (SimplexCategory.mk (n + 1))
            (SimplexCategory.mk 0) 0
      exact (SimplexCategory.eq_const_to_zero _).symm
    have hmap : data.simplicial.object.map
          (q (op (SimplexCategory.mk (n + 1)))) ≫
          data.simplicial.object.map (SimplexCategory.δ i).op =
        data.simplicial.object.map (q (op (SimplexCategory.mk n))) := by
      rw [← data.simplicial.object.map_comp, hq]
    have hf := data.simplicial.face_def n i
    have hf' := congrArg
      (fun z => eqToHom (data.simplicial.object_obj (n + 1)) ≫ z) hf
    have hf'' : eqToHom (data.simplicial.object_obj (n + 1)) ≫
        godementWhiskeredSimplicialFace F Y G d n i =
      data.simplicial.object.δ i ≫
        eqToHom (data.simplicial.object_obj n) := by
      simpa only [Category.assoc, CategoryTheory.eqToHom_trans,
        CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
        Category.id_comp] using hf'.symm
    have hmap' : simplicialUnitMap data.simplicial.object (n + 1) ≫
          data.simplicial.object.map (SimplexCategory.δ i).op =
        simplicialUnitMap data.simplicial.object n := by
      change data.simplicial.object.map
          (q (op (SimplexCategory.mk (n + 1)))) ≫
          data.simplicial.object.map (SimplexCategory.δ i).op =
        data.simplicial.object.map (q (op (SimplexCategory.mk n)))
      exact hmap
    simp only [SimplicialObject.δ, Category.assoc]
    rw [hf'']
    change
      h₀ ≫ godementZeroMap F Y G ≫
        eqToHom (data.simplicial.object_obj 0).symm ≫
        simplicialUnitMap data.simplicial.object (n + 1) ≫
        data.simplicial.object.map (SimplexCategory.δ i).op ≫
        eqToHom (data.simplicial.object_obj n) =
      h₀ ≫ godementZeroMap F Y G ≫
        eqToHom (data.simplicial.object_obj 0).symm ≫
        simplicialUnitMap data.simplicial.object n ≫
        eqToHom (data.simplicial.object_obj n)
    simpa only [Category.assoc] using
      congrArg (fun z => h₀ ≫ godementZeroMap F Y G ≫
        eqToHom (data.simplicial.object_obj 0).symm ≫ z ≫
        eqToHom (data.simplicial.object_obj n)) hmap'
  · intro n i
    dsimp [component, godementWhiskeredSectionComponent]
    have hq : q (op (SimplexCategory.mk (n + 1))) =
        q (op (SimplexCategory.mk n)) ≫
          (SimplexCategory.σ i).op := by
      dsimp [q]
      apply Quiver.Hom.unop_inj
      change SimplexCategory.const (SimplexCategory.mk (n + 1))
          (SimplexCategory.mk 0) 0 =
        SimplexCategory.σ i ≫
          SimplexCategory.const (SimplexCategory.mk n)
            (SimplexCategory.mk 0) 0
      exact (SimplexCategory.eq_const_to_zero _).symm
    have hmap : data.simplicial.object.map
          (q (op (SimplexCategory.mk n))) ≫
          data.simplicial.object.map (SimplexCategory.σ i).op =
        data.simplicial.object.map
          (q (op (SimplexCategory.mk (n + 1)))) := by
      rw [← data.simplicial.object.map_comp, hq]
    have hs := data.simplicial.degeneracy_def n i
    have hs' := congrArg
      (fun z => eqToHom (data.simplicial.object_obj n) ≫ z) hs
    have hs'' : eqToHom (data.simplicial.object_obj n) ≫
        godementWhiskeredSimplicialDegeneracy F Y G s n i =
      data.simplicial.object.σ i ≫
        eqToHom (data.simplicial.object_obj (n + 1)) := by
      simpa only [Category.assoc, CategoryTheory.eqToHom_trans,
        CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
        Category.id_comp] using hs'.symm
    have hmap' : simplicialUnitMap data.simplicial.object n ≫
          data.simplicial.object.map (SimplexCategory.σ i).op =
        simplicialUnitMap data.simplicial.object (n + 1) := by
      change data.simplicial.object.map
          (q (op (SimplexCategory.mk n))) ≫
          data.simplicial.object.map (SimplexCategory.σ i).op =
        data.simplicial.object.map
          (q (op (SimplexCategory.mk (n + 1))))
      exact hmap
    simp only [SimplicialObject.σ, Category.assoc]
    rw [hs'']
    change
      h₀ ≫ godementZeroMap F Y G ≫
        eqToHom (data.simplicial.object_obj 0).symm ≫
        simplicialUnitMap data.simplicial.object n ≫
        data.simplicial.object.map (SimplexCategory.σ i).op ≫
        eqToHom (data.simplicial.object_obj (n + 1)) =
      h₀ ≫ godementZeroMap F Y G ≫
        eqToHom (data.simplicial.object_obj 0).symm ≫
        simplicialUnitMap data.simplicial.object (n + 1) ≫
        eqToHom (data.simplicial.object_obj (n + 1))
    simpa only [Category.assoc] using
      congrArg (fun z => h₀ ≫ godementZeroMap F Y G ≫
        eqToHom (data.simplicial.object_obj 0).symm ≫ z ≫
        eqToHom (data.simplicial.object_obj (n + 1))) hmap'
  · intro n
    dsimp [component, godementWhiskeredSectionComponent]
    have hzero :
        eqToHom (data.simplicial.object_obj 0).symm ≫
            data.augmentation.app (op (SimplexCategory.mk 0)) =
          godementWhiskeredAugmentationComponent F Y G d 0 := by
      rw [data.component_formula 0, data.component_def 0]
    have hn := data.augmentation.naturality
      (q (op (SimplexCategory.mk n)))
    have hconst :
        ((SimplicialObject.const (A ⥤ B)).obj (F ⋙ G)).map
            (q (op (SimplexCategory.mk n))) = 𝟙 (F ⋙ G) := by
      simp
    rw [hconst] at hn
    have hcomp :
        data.augmentation.app (op (SimplexCategory.mk n)) =
          eqToHom (data.simplicial.object_obj n) ≫
            godementWhiskeredAugmentationComponent F Y G d n := by
      have hc := data.component_formula n
      rw [data.component_def n] at hc
      have hc' := congrArg
        (fun z => eqToHom (data.simplicial.object_obj n) ≫ z) hc
      simpa only [Category.assoc, CategoryTheory.eqToHom_trans,
        CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
        Category.id_comp] using hc'
    have hn' : data.simplicial.object.map
          (q (op (SimplexCategory.mk n))) ≫
          data.augmentation.app (op (SimplexCategory.mk n)) =
        data.augmentation.app (op (SimplexCategory.mk 0)) := by
      have hid : data.augmentation.app (op (SimplexCategory.mk 0)) ≫
          𝟙 (F ⋙ G) = data.augmentation.app
            (op (SimplexCategory.mk 0)) := Category.comp_id _
      rw [hid] at hn
      exact hn
    have hunit : simplicialUnitMap data.simplicial.object n ≫
          data.augmentation.app (op (SimplexCategory.mk n)) =
        data.augmentation.app (op (SimplexCategory.mk 0)) := by
      change data.simplicial.object.map
          (q (op (SimplexCategory.mk n))) ≫
          data.augmentation.app (op (SimplexCategory.mk n)) = _
      exact hn'
    simp only [Category.assoc]
    rw [← hcomp, hunit]
    have hid : (h₀ ≫ godementZeroMap F Y G ≫
        eqToHom (data.simplicial.object_obj 0).symm) ≫
        data.augmentation.app (op (SimplexCategory.mk 0)) =
      h₀ ≫ godementZeroMap F Y G ≫
        godementWhiskeredAugmentationComponent F Y G d 0 := by
      have hz := congrArg
        (fun z => h₀ ≫ godementZeroMap F Y G ≫ z) hzero
      simpa only [Category.assoc] using hz
    rw [hid]
    simpa [godementWhiskeredDegreeZeroAugmentation, Category.assoc] using
      h₀_condition

/-! ## The two-map homotopy and the before/after maps -/

def godementOuterAugmentationComponent {B : Type uB} {C : Type uC}
    [Category.{vB} B] [Category.{vC} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (G : C ⥤ B) (n : ℕ) :
    godementDegree Y n ⋙ G ⟶ G :=
  Functor.whiskerRight (godementAugmentationComponent Y d n) G ≫
    (Functor.leftUnitor G).hom

def godementInnerAugmentationComponent {A : Type uA} {C : Type uC}
    [Category.{vA} A] [Category.{vC} C]
    (F : A ⥤ C) (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (n : ℕ) :
    F ⋙ godementDegree Y n ⟶ F :=
  Functor.whiskerLeft F (godementAugmentationComponent Y d n) ≫
    (Functor.rightUnitor F).hom

/-! The following two structures spell out, degree by degree, the assertion
that the given families are morphisms of simplicial objects and commute with
the augmentation. -/

structure GodementOuterMorphism {B : Type uB} {C : Type uC}
    [Category.{vB} B] [Category.{vC} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (G G' : C ⥤ B) (a : G ⟶ G')
    (aₙ : ∀ n, godementDegree Y n ⋙ G ⟶ godementDegree Y n ⋙ G') where
  face : ∀ {n} (j : Fin (n + 2)),
    aₙ (n + 1) ≫ Functor.whiskerRight
        (godementFace Y d (n := n + 1) j) G' =
      Functor.whiskerRight (godementFace Y d (n := n + 1) j) G ≫ aₙ n
  degeneracy : ∀ {n} (j : Fin (n + 1)),
    aₙ n ≫ Functor.whiskerRight (godementDegeneracy Y s j) G' =
      Functor.whiskerRight (godementDegeneracy Y s j) G ≫ aₙ (n + 1)
  augmentation : ∀ n,
    aₙ n ≫ godementOuterAugmentationComponent Y d G' n =
      godementOuterAugmentationComponent Y d G n ≫ a

structure GodementInnerMorphism {A : Type uA} {C : Type uC}
    [Category.{vA} A] [Category.{vC} C]
    (F F' : A ⥤ C) (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (b : F ⟶ F')
    (bₙ : ∀ n, F ⋙ godementDegree Y n ⟶ F' ⋙ godementDegree Y n) where
  face : ∀ {n} (j : Fin (n + 2)),
    bₙ (n + 1) ≫ Functor.whiskerLeft F'
        (godementFace Y d (n := n + 1) j) =
      Functor.whiskerLeft F (godementFace Y d (n := n + 1) j) ≫ bₙ n
  degeneracy : ∀ {n} (j : Fin (n + 1)),
    bₙ n ≫ Functor.whiskerLeft F'
        (godementDegeneracy Y s j) =
      Functor.whiskerLeft F (godementDegeneracy Y s j) ≫ bₙ (n + 1)
  augmentation : ∀ n,
    bₙ n ≫ godementInnerAugmentationComponent F' Y d n =
      godementInnerAugmentationComponent F Y d n ≫ b

/-- The five degreewise conditions for the source's simplicial homotopy. -/
structure GodementDegreewiseHomotopy {D : Type u} [Category.{v} D]
    {X Y : ℕ → D}
    (faceX : ∀ n, Fin (n + 2) → (X (n + 1) ⟶ X n))
    (degenX : ∀ n, Fin (n + 1) → (X n ⟶ X (n + 1)))
    (faceY : ∀ n, Fin (n + 2) → (Y (n + 1) ⟶ Y n))
    (degenY : ∀ n, Fin (n + 1) → (Y n ⟶ Y (n + 1)))
    (left right : ∀ n, (X n ⟶ Y n)) where
  h : ∀ n, Fin (n + 2) → (X n ⟶ Y n)
  endpoint_zero : ∀ n, h n 0 = left n
  endpoint_last : ∀ n, h n (Fin.last (n + 1)) = right n
  face_of_gt {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
      (hji : j.castSucc < i) :
    h (n + 1) i ≫ faceY n j =
      faceX n j ≫ h n (i.pred hji.ne_zero)
  face_of_le {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
      (hij : i ≤ j.castSucc) :
    h (n + 1) i ≫ faceY n j =
      faceX n j ≫ h n
        (i.castPred (Fin.ne_last_of_lt
          (lt_of_le_of_lt hij j.castSucc_lt_succ)))
  degeneracy_of_gt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
      (hji : j.castSucc < i) :
    h n i ≫ degenY n j = degenX n j ≫ h (n + 1) i.succ
  degeneracy_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
      (hij : i ≤ j.castSucc) :
    h n i ≫ degenY n j = degenX n j ≫ h (n + 1) i.castSucc

abbrev GodementWhiskeredHomotopy {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F F' : A ⥤ C) (Y : C ⥤ C) (G G' : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (left right : ∀ n,
      godementWhiskeredDegree F Y G n ⟶
        godementWhiskeredDegree F' Y G' n) :=
  GodementDegreewiseHomotopy
    (godementWhiskeredSimplicialFace F Y G d)
    (godementWhiskeredSimplicialDegeneracy F Y G s)
    (godementWhiskeredSimplicialFace F' Y G' d)
    (godementWhiskeredSimplicialDegeneracy F' Y G' s) left right

abbrev GodementSelfHomotopy {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (left right : ∀ n, godementDegree Y n ⟶ godementDegree Y n) :=
  GodementDegreewiseHomotopy
    (fun n j => godementFace Y d (n := n + 1) j)
    (fun n j => godementDegeneracy Y s (n := n) j)
    (fun n j => godementFace Y d (n := n + 1) j)
    (fun n j => godementDegeneracy Y s (n := n) j) left right

/-! The two endpoint maps in Lemma 33.5. -/

def godementTwoMapLeft
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F F' : A ⥤ C) (Y : C ⥤ C) (G G' : C ⥤ B)
    (a : G ⟶ G')
    (bₙ : ∀ n, F ⋙ godementDegree Y n ⟶ F' ⋙ godementDegree Y n)
    (n : ℕ) :
    godementWhiskeredDegree F Y G n ⟶
      godementWhiskeredDegree F' Y G' n :=
  Functor.whiskerRight (bₙ n) G ≫
    Functor.whiskerLeft (F' ⋙ godementDegree Y n) a

def godementTwoMapRight
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F F' : A ⥤ C) (Y : C ⥤ C) (G G' : C ⥤ B)
    (aₙ : ∀ n, godementDegree Y n ⋙ G ⟶ godementDegree Y n ⋙ G')
    (b : F ⟶ F') (n : ℕ) :
    godementWhiskeredDegree F Y G n ⟶
      godementWhiskeredDegree F' Y G' n :=
  Functor.whiskerLeft F (aₙ n) ≫
    Functor.whiskerRight b (godementDegree Y n ⋙ G')

theorem godement_two_maps_homotopic
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    (F F' : A ⥤ C) (Y : C ⥤ C) (G G' : C ⥤ B)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s)
    (a : G ⟶ G')
    (aₙ : ∀ n, godementDegree Y n ⋙ G ⟶ godementDegree Y n ⋙ G')
    (ha : GodementOuterMorphism Y d s G G' a aₙ)
    (b : F ⟶ F')
    (bₙ : ∀ n, F ⋙ godementDegree Y n ⟶ F' ⋙ godementDegree Y n)
    (hb : GodementInnerMorphism F F' Y d s b bₙ) :
    Nonempty (GodementWhiskeredHomotopy F F' Y G G' d s
      (godementTwoMapLeft F F' Y G G' a bₙ)
      (godementTwoMapRight F F' Y G G' aₙ b)) := by
  sorry

def godementBeforeMap {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (f : 𝟭 C ⟶ 𝟭 C) (n : ℕ) :
    godementDegree Y n ⟶ godementDegree Y n :=
  (Functor.leftUnitor (godementDegree Y n)).inv ≫
    Functor.whiskerRight f (godementDegree Y n) ≫
    (Functor.leftUnitor (godementDegree Y n)).hom

def godementAfterMap {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (f : 𝟭 C ⟶ 𝟭 C) (n : ℕ) :
    godementDegree Y n ⟶ godementDegree Y n :=
  (Functor.rightUnitor (godementDegree Y n)).inv ≫
    Functor.whiskerLeft (godementDegree Y n) f ≫
    (Functor.rightUnitor (godementDegree Y n)).hom

/-! After transporting across the unitors, the two maps in the final source
lemma are endomorphisms of each explicit degree. -/

structure GodementSelfMorphism {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (f : 𝟭 C ⟶ 𝟭 C) (maps : ∀ n, godementDegree Y n ⟶ godementDegree Y n) where
  face : ∀ {n} (j : Fin (n + 2)),
    maps (n + 1) ≫ godementFace Y d (n := n + 1) j =
      godementFace Y d (n := n + 1) j ≫ maps n
  degeneracy : ∀ {n} (j : Fin (n + 1)),
    maps n ≫ godementDegeneracy Y s (n := n) j =
      godementDegeneracy Y s (n := n) j ≫ maps (n + 1)
  augmentation : ∀ n,
    maps n ≫ godementAugmentationComponent Y d n =
      godementAugmentationComponent Y d n ≫ f

/-! An actual morphism of the packaged simplicial objects, with its
degreewise components transported to the explicit Godement degrees. -/

structure GodementActualSelfMorphism {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (data : GodementAugmentationData Y d s)
    (f : 𝟭 C ⟶ 𝟭 C)
    (maps : ∀ n, godementDegree Y n ⟶ godementDegree Y n) where
  map : data.simplicial.object ⟶ data.simplicial.object
  component : ∀ n,
    eqToHom (data.simplicial.object_obj n).symm ≫
        map.app (op (SimplexCategory.mk n)) ≫
        eqToHom (data.simplicial.object_obj n) = maps n
  augmentation : map ≫ data.augmentation =
    data.augmentation ≫ (SimplicialObject.const (C ⥤ C)).map f

theorem godement_before_after_maps
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s)
    (f : 𝟭 C ⟶ 𝟭 C) :
    Nonempty (GodementSelfMorphism Y d s f
      (fun n => godementBeforeMap Y f n)) ∧
    Nonempty (GodementSelfMorphism Y d s f
      (fun n => godementAfterMap Y f n)) := by
  sorry

theorem godement_before_after_actual_maps
    {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (data : GodementAugmentationData Y d s) (f : 𝟭 C ⟶ 𝟭 C) :
    Nonempty (GodementActualSelfMorphism Y d s data f
      (fun n => godementBeforeMap Y f n)) ∧
    Nonempty (GodementActualSelfMorphism Y d s data f
      (fun n => godementAfterMap Y f n)) := by
  sorry

theorem godement_before_after_augmentation
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (f : 𝟭 C ⟶ 𝟭 C) :
    (∀ n, godementBeforeMap Y f n ≫ godementAugmentationComponent Y d n =
      godementAugmentationComponent Y d n ≫ f) ∧
    (∀ n, godementAfterMap Y f n ≫ godementAugmentationComponent Y d n =
      godementAugmentationComponent Y d n ≫ f) := by
  sorry

theorem godement_before_after_homotopic
    {C : Type u} [Category.{v} C] (Y : C ⥤ C)
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (h : GodementEquations Y d s)
    (f : 𝟭 C ⟶ 𝟭 C) :
    Nonempty (GodementSelfHomotopy Y d s
      (fun n => godementBeforeMap Y f n)
      (fun n => godementAfterMap Y f n)) := by
  sorry

theorem godement_before_after_actual_homotopic
    {C : Type u} [Category.{v} C]
    (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (data : GodementAugmentationData Y d s) (f : 𝟭 C ⟶ 𝟭 C) :
    Nonempty (Σ before : GodementActualSelfMorphism
        Y d s data f
        (fun n => godementBeforeMap Y f n),
      Σ after : GodementActualSelfMorphism
        Y d s data f
        (fun n => godementAfterMap Y f n),
        Formalization.Books.Simplicial.Unit26.Homotopy
          before.map after.map) := by
  sorry

end Formalization.Books.Simplicial.Unit33
