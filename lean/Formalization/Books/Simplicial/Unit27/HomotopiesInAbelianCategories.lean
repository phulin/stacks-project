import Formalization.Books.Simplicial.Unit23.SimplicialObjectsAndChainComplexes
import Formalization.Books.Simplicial.Unit26.Homotopies
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Simplicial Methods, Chapter 27: Homotopies in abelian categories

This file records the chain-homotopy calculation attached to Section 27 of
the source.  The additive Moore complex is defined here because the source
starts with an additive category, while the earlier normalized complex API
is available under the stronger abelian hypothesis.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit27

open CategoryTheory
open Formalization.Books.Homology.Unit03
open Formalization.Books.Simplicial.Unit26
open Formalization.Books.Simplicial.Unit23
open HomologicalComplex
open Opposite
open scoped _root_.Simplicial

universe v u

/-! ## The additive Moore complex `s(U)`

The source's preceding construction is stated for abelian categories, but its
alternating-face formula only needs a preadditive category.  We retain that
more general construction here so that the opening hypothesis of this section
is represented faithfully; normalization remains restricted to abelian
categories below.
-/

/-- The alternating face differential in the additive Moore complex. -/
def additiveAssociatedBoundary
    {C : Type u} [Category.{v} C] [Preadditive C]
    (U : SimplicialObject C) (n : ℕ) :
    U.obj (op ⦋n + 1⦌) ⟶ U.obj (op ⦋n⦌) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • U.δ i

/-- The alternating face maps square to zero. -/
theorem additiveAssociatedBoundary_comp
    {C : Type u} [Category.{v} C] [Preadditive C]
    (U : SimplicialObject C) (n : ℕ) :
    additiveAssociatedBoundary U (n + 1) ≫ additiveAssociatedBoundary U n = 0 := by
  exact AlgebraicTopology.AlternatingFaceMapComplex.d_squared U n

/-- The source's associated chain complex `s(U)` in an additive category. -/
noncomputable def additiveAssociatedChainComplex
    {C : Type u} [Category.{v} C] [Preadditive C]
    (U : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of
    (fun n => U.obj (op ⦋n⦌))
    (additiveAssociatedBoundary U)
    (additiveAssociatedBoundary_comp U)

@[simp]
theorem additiveAssociatedChainComplex_X
    {C : Type u} [Category.{v} C] [Preadditive C]
    (U : SimplicialObject C) (n : ℕ) :
    (additiveAssociatedChainComplex U).X n = U.obj (op ⦋n⦌) :=
  rfl

@[simp]
theorem additiveAssociatedChainComplex_d
    {C : Type u} [Category.{v} C] [Preadditive C]
    (U : SimplicialObject C) (n : ℕ) :
    (additiveAssociatedChainComplex U).d (n + 1) n = additiveAssociatedBoundary U n := by
  simp [additiveAssociatedChainComplex]

theorem additiveAssociatedBoundary_naturality
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    f.app (op ⦋n + 1⦌) ≫ additiveAssociatedBoundary V n =
      additiveAssociatedBoundary U n ≫ f.app (op ⦋n⦌) := by
  simp only [additiveAssociatedBoundary, CategoryTheory.Preadditive.comp_sum,
    CategoryTheory.Preadditive.sum_comp, CategoryTheory.Preadditive.comp_zsmul,
    CategoryTheory.Preadditive.zsmul_comp]
  simp

theorem additiveAssociatedChainComplexMap_comm
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.down ℕ).Rel i j →
      f.app (op ⦋i⦌) ≫ (additiveAssociatedChainComplex V).d i j =
        (additiveAssociatedChainComplex U).d i j ≫ f.app (op ⦋j⦌) := by
  intro i j hij
  simp only [ComplexShape.down_Rel] at hij
  subst i
  simpa [additiveAssociatedChainComplex_d] using additiveAssociatedBoundary_naturality f j

/-- The chain map `s(f)` induced by a map of simplicial objects. -/
def additiveAssociatedChainComplexMap
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    additiveAssociatedChainComplex U ⟶ additiveAssociatedChainComplex V :=
  { f := fun n => f.app (op ⦋n⦌)
    comm' := additiveAssociatedChainComplexMap_comm f }

@[simp]
theorem additiveAssociatedChainComplexMap_f
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (additiveAssociatedChainComplexMap f).f n = f.app (op ⦋n⦌) :=
  rfl

/-! ## The explicit homotopy component -/

/-- The degree-`n` component in the source's formula
`s(h)_n = Σᵢ (-1)^(i+1) h_(n+1,i+1) sᵢ`. -/
def additiveAssociatedHomotopyComponent
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) (n : ℕ) :
    U.obj (op ⦋n⦌) ⟶ V.obj (op ⦋n + 1⦌) :=
  ∑ i : Fin (n + 1),
    (-1 : ℤ) ^ ((i : ℕ) + 1) •
      (U.σ i ≫ H.h (n + 1) i.castSucc.succ)

/-- The component attached directly to a cylinder homotopy. -/
noncomputable def additiveAssociatedHomotopyComponentOfCylinder
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : CylinderHomotopy a b) (n : ℕ) :
    U.obj (op ⦋n⦌) ⟶ V.obj (op ⦋n + 1⦌) :=
  additiveAssociatedHomotopyComponent
    (cylinderHomotopy_to_degreewise H) n

/- The next two interfaces record the two double sums displayed in the
   source.  The remaining face/degeneracy rearrangement is summarized by the
   boundary equations below; splitting off degree zero makes the bottom of a
   nonnegative complex explicit. -/
theorem additiveAssociatedHomotopyComponent_boundary_expansion
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) (n : ℕ) :
    additiveAssociatedHomotopyComponent H n ≫ additiveAssociatedBoundary V n =
      ∑ j : Fin (n + 2), ∑ i : Fin (n + 1),
          (-1 : ℤ) ^ ((j : ℕ) + (i : ℕ) + 1) •
          (U.σ i ≫ H.h (n + 1) i.castSucc.succ ≫ V.δ j) := by
  simp only [additiveAssociatedHomotopyComponent, additiveAssociatedBoundary,
    CategoryTheory.Preadditive.comp_sum, CategoryTheory.Preadditive.sum_comp,
    CategoryTheory.Preadditive.comp_zsmul, CategoryTheory.Preadditive.zsmul_comp,
    smul_smul, ← Finset.sum_zsmul, ← pow_add]
  simp [Category.assoc, add_assoc]

theorem additiveAssociatedHomotopyComponent_previous_boundary_expansion
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) (n : ℕ) :
    additiveAssociatedBoundary U n ≫
          additiveAssociatedHomotopyComponent H n =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 2),
          (-1 : ℤ) ^ ((i : ℕ) + 1 + (j : ℕ)) •
          (U.δ j ≫ U.σ i ≫ H.h (n + 1) i.castSucc.succ) := by
  simp only [additiveAssociatedBoundary, additiveAssociatedHomotopyComponent,
    CategoryTheory.Preadditive.comp_sum, CategoryTheory.Preadditive.sum_comp,
    CategoryTheory.Preadditive.comp_zsmul, CategoryTheory.Preadditive.zsmul_comp,
    smul_smul, ← Finset.sum_zsmul, ← pow_add]

theorem additiveAssociatedHomotopyComponent_zero_equation
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) :
    additiveAssociatedHomotopyComponent H 0 ≫ additiveAssociatedBoundary V 0 =
      a.app (op ⦋0⦌) - b.app (op ⦋0⦌) := by
  rw [additiveAssociatedHomotopyComponent_boundary_expansion]
  simp [H.face_of_gt, H.face_of_le, H.h_zero]
  rw [← SimplicialObject.σ_naturality_assoc b, ← SimplicialObject.δ_naturality b]
  rw [U.δ_comp_σ_self'_assoc (i := 0) (j := 0) (by ext; rfl),
    U.δ_comp_σ_succ'_assoc (i := 0) (j := 1) (by ext; rfl)]
  have hlast : (1 : Fin 2) = Fin.last 1 := by ext; rfl
  rw [hlast, H.h_last 0]
  simp [sub_eq_add_neg, add_comm]

private noncomputable def degreewiseHomotopyToSimplicialHomotopy
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) :
    CategoryTheory.SimplicialObject.Homotopy a b := {
    h := fun {n} i => U.σ i ≫ H.h (n + 1) i.castSucc.succ
    h_zero_comp_δ_zero := by
      intro n
      let i : Fin (n + 3) := (Fin.castSucc (0 : Fin (n + 1))).succ
      have hpos : (0 : Fin (n + 2)).castSucc < i := by simp [i]
      have hface := H.face_of_gt (n := n) i (0 : Fin (n + 2)) hpos
      have hpred : i.pred (Fin.ne_zero_of_lt hpos) = (0 : Fin (n + 2)) := by
        apply Fin.ext
        rfl
      rw [hpred] at hface
      simp only [Category.assoc]
      rw [hface]
      rw [H.h_zero n]
      rw [U.δ_comp_σ_self'_assoc (i := 0) (j := 0) (by ext; rfl)]
    h_last_comp_δ_last := by
      intro n
      let i : Fin (n + 3) := (Fin.last n).castSucc.succ
      let j : Fin (n + 2) := Fin.last (n + 1)
      have hle : i ≤ j.castSucc := by simp [i, j]
      have hface := H.face_of_le (n := n) i j hle
      have hcast :
          i.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt hle j.castSucc_lt_succ)) =
            Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      rw [hcast] at hface
      simp only [Category.assoc]
      rw [hface]
      rw [U.δ_comp_σ_succ'_assoc (i := Fin.last n) (j := Fin.last (n + 1)) (by ext; rfl)]
      simp [H.h_last]
    h_succ_comp_δ_castSucc_of_lt := by
      intro n i j hij
      have hgt : i.castSucc.castSucc < j.succ.castSucc.succ := by
        apply Fin.val_fin_lt.mpr
        have hij' : (i : ℕ) ≤ (j : ℕ) := Fin.le_iff_val_le_val.mp hij
        exact hij'.trans_lt (Nat.lt_succ_of_le (Nat.le_succ _))
      have hface := H.face_of_gt (n := n + 1)
        (i := j.succ.castSucc.succ) (j := i.castSucc) hgt
      have hpred :
          (j.succ.castSucc.succ).pred (Fin.ne_zero_of_lt hgt) =
            j.castSucc.succ := by
        apply Fin.ext
        rfl
      rw [hpred] at hface
      simp only [Category.assoc]
      rw [hface, U.δ_comp_σ_of_le_assoc hij]
    h_succ_comp_δ_castSucc_succ := by
      intro n j
      have hface₁ := H.face_of_gt (n := n + 1)
        (i := j.succ.castSucc.succ) (j := j.castSucc.succ) (by simp)
      have hpred₁ :
          (j.succ.castSucc.succ).pred
              (Fin.ne_zero_of_lt (show (j.castSucc.succ).castSucc <
                j.succ.castSucc.succ by simp)) =
            j.castSucc.succ := by
        apply Fin.ext
        rfl
      rw [hpred₁] at hface₁
      have hface₂ := H.face_of_le (n := n + 1)
        (i := j.castSucc.castSucc.succ) (j := j.castSucc.succ) (by simp)
      have hpred₂ :
          (j.castSucc.castSucc.succ).castPred
              (Fin.ne_last_of_lt (lt_of_le_of_lt (by simp)
                (j.castSucc.succ).castSucc_lt_succ)) =
            j.castSucc.succ := by
        apply Fin.ext
        rfl
      rw [hpred₂] at hface₂
      have hJ : j.castSucc.succ = j.succ.castSucc := by
        apply Fin.ext
        rfl
      simp only [Category.assoc]
      rw [hface₁]
      rw [hJ, U.δ_comp_σ_self_assoc (i := j.succ)]
      rw [← hJ, hface₂, U.δ_comp_σ_succ_assoc (i := j.castSucc)]
    h_castSucc_comp_δ_succ_of_lt := by
      intro n i j hji
      have hle : j.castSucc.castSucc.succ ≤ i.succ.castSucc := by
        have hle₀ : j.castSucc.castSucc < i.succ :=
          (Fin.castSucc_lt_succ_iff).2 (le_of_lt hji)
        exact (Fin.succ_le_castSucc_iff).2 hle₀
      have hface := H.face_of_le (n := n + 1)
        (i := j.castSucc.castSucc.succ) (j := i.succ) hle
      have hpred :
          (j.castSucc.castSucc.succ).castPred
              (Fin.ne_last_of_lt (lt_of_le_of_lt hle i.succ.castSucc_lt_succ)) =
            j.castSucc.succ := by
        apply Fin.ext
        rfl
      rw [hpred] at hface
      simp only [Category.assoc]
      rw [hface, U.δ_comp_σ_of_gt_assoc hji]
    h_comp_σ_castSucc_of_le := by
      intro n i j hij
      have hgt : i.castSucc.castSucc < j.castSucc.succ := by
        apply Fin.val_fin_lt.mpr
        have hij' : (i : ℕ) ≤ (j : ℕ) := Fin.le_iff_val_le_val.mp hij
        simpa using Nat.lt_succ_of_le hij'
      have hface := H.degeneracy_of_gt (n := n + 1)
        (i := j.castSucc.succ) (j := i.castSucc) hgt
      have hidx : j.castSucc.succ.succ = j.succ.castSucc.succ := by
        apply Fin.ext
        simp
      rw [hidx] at hface
      simp only [Category.assoc]
      rw [hface, U.σ_comp_σ_assoc hij]
    h_comp_σ_succ_of_lt := by
      intro n i j hji
      have hji' : (j : ℕ) ≤ (i : ℕ) := Fin.le_iff_val_le_val.mp hji
      have hle : j.castSucc.succ ≤ i.succ.castSucc := by
        apply Fin.val_fin_le.mpr
        simpa using Nat.succ_le_succ hji'
      have hface := H.degeneracy_of_le (n := n + 1)
        (i := j.castSucc.succ) (j := i.succ) hle
      have hidx :
          (j.castSucc.succ).castSucc = j.castSucc.castSucc.succ := by
        apply Fin.ext
        simp
      rw [hidx] at hface
      simp only [Category.assoc]
      rw [hface, ← U.σ_comp_σ_assoc hji] }

theorem additiveAssociatedHomotopyComponent_succ_equation
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) (n : ℕ) :
    additiveAssociatedHomotopyComponent H (n + 1) ≫
          additiveAssociatedBoundary V (n + 1) +
    additiveAssociatedBoundary U n ≫
          additiveAssociatedHomotopyComponent H n =
      a.app (op ⦋n + 1⦌) - b.app (op ⦋n + 1⦌) := by
  let G := degreewiseHomotopyToSimplicialHomotopy H
  let K := G.toChainHomotopy
  have hcomm := K.comm (n + 1)
  rw [dNext_eq (f := K.hom) (i' := n) (w := by simp),
    prevD_eq (f := K.hom) (j' := n + 2) (w := by simp)] at hcomm
  have hK_n : K.hom n (n + 1) = additiveAssociatedHomotopyComponent H n := by
    change CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom G n (n + 1) = _
    rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
    simp [G, degreewiseHomotopyToSimplicialHomotopy,
      additiveAssociatedHomotopyComponent]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [pow_succ, mul_comm]
  have hK_succ :
      K.hom (n + 1) (n + 2) = additiveAssociatedHomotopyComponent H (n + 1) := by
    change CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom G (n + 1) (n + 2) = _
    rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
    simp [G, degreewiseHomotopyToSimplicialHomotopy,
      additiveAssociatedHomotopyComponent]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [pow_succ, mul_comm]
  rw [hK_n, hK_succ] at hcomm
  simp only [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.alternatingFaceMapComplex_map_f] at hcomm
  have hcomm' :
      a.app (op ⦋n + 1⦌) =
        additiveAssociatedBoundary U n ≫
            additiveAssociatedHomotopyComponent H n +
          additiveAssociatedHomotopyComponent H (n + 1) ≫
            additiveAssociatedBoundary V (n + 1) +
          b.app (op ⦋n + 1⦌) := by
    simpa [additiveAssociatedBoundary] using hcomm
  rw [hcomm']
  abel

/-- The displayed formula gives a chain homotopy between the two associated
chain maps.  The component equation is the source's
`d_{n+1} s(h)_n + s(h)_{n-1} d_n = a_n - b_n` calculation. -/
theorem additiveAssociatedChainHomotopy_exists
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) :
    ∃ K : _root_.Homotopy
        (additiveAssociatedChainComplexMap a)
        (additiveAssociatedChainComplexMap b),
      ∀ n : ℕ,
        K.hom n (n + 1) = additiveAssociatedHomotopyComponent H n := by
  let G := degreewiseHomotopyToSimplicialHomotopy H
  refine ⟨G.toChainHomotopy, ?_⟩
  intro n
  change CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom G n (n + 1) = _
  rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  simp [G, degreewiseHomotopyToSimplicialHomotopy,
    additiveAssociatedHomotopyComponent]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pow_succ, mul_comm]

/-- In particular, the two associated chain maps are homotopic. -/
theorem additiveAssociatedChainHomotopy_of_degreewise
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) :
    Nonempty (_root_.Homotopy
      (additiveAssociatedChainComplexMap a)
      (additiveAssociatedChainComplexMap b)) := by
  rcases additiveAssociatedChainHomotopy_exists H with ⟨K, _⟩
  exact ⟨K⟩

/-- A cylinder homotopy induces the explicit chain homotopy above. -/
theorem additiveAssociatedChainHomotopy_of_cylinder
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : CylinderHomotopy a b) :
    Nonempty (_root_.Homotopy
      (additiveAssociatedChainComplexMap a)
      (additiveAssociatedChainComplexMap b)) := by
  exact additiveAssociatedChainHomotopy_of_degreewise
    (cylinderHomotopy_to_degreewise H)

theorem additiveAssociatedChainHomotopy_of_cylinder_with_components
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : CylinderHomotopy a b) :
    ∃ K : _root_.Homotopy
        (additiveAssociatedChainComplexMap a)
        (additiveAssociatedChainComplexMap b),
      ∀ n : ℕ,
        K.hom n (n + 1) = additiveAssociatedHomotopyComponentOfCylinder H n := by
  rcases additiveAssociatedChainHomotopy_exists
      (cylinderHomotopy_to_degreewise H) with ⟨K, hK⟩
  exact ⟨K, hK⟩

/-! ## The source's homotopy and homotopy-equivalence assertions -/

/-- A simplicial homotopy induces a homotopy of additive Moore complexes. -/
theorem additiveAssociatedChainMap_homotopic
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Formalization.Books.Simplicial.Unit26.Homotopic a b) :
    Nonempty (_root_.Homotopy
      (additiveAssociatedChainComplexMap a)
      (additiveAssociatedChainComplexMap b)) := by
  induction H with
  | rel a b h =>
      rcases h with ⟨h⟩
      exact ⟨CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy h⟩
  | refl a =>
      exact ⟨_root_.Homotopy.ofEq rfl⟩
  | symm a b h ih =>
      exact ⟨ih.some.symm⟩
  | trans a b c h₁ h₂ ih₁ ih₂ =>
      exact ⟨ih₁.some.trans ih₂.some⟩

theorem normalizedChainMap_homotopic
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Formalization.Books.Simplicial.Unit26.Homotopic a b) :
    Nonempty (_root_.Homotopy
      (normalizedChainComplexMap a)
      (normalizedChainComplexMap b)) := by
  induction H with
  | rel a b h =>
      rcases h with ⟨h⟩
      obtain ⟨sV⟩ := (normalizedToAssociated_split V).exists_splitMono
      let rV : associatedChainComplex V ⟶ normalizedChainComplex V := sV.retraction
      let L := CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy h
      let hhom : ∀ i j, (associatedChainComplex U).X i ⟶
          (associatedChainComplex V).X j := fun i j => by
        change U.obj (op ⦋i⦌) ⟶ V.obj (op ⦋j⦌)
        exact L.hom i j
      have hK : _root_.Homotopy
          (associatedChainComplexMap a) (associatedChainComplexMap b) := {
        hom := hhom
        zero := fun i j hij => by
          change L.hom i j = 0
          exact L.zero i j hij
        comm := fun i => by
          cases i with
          | zero =>
              rw [Homotopy.dNext_zero_chainComplex,
                Homotopy.prevD_chainComplex, zero_add]
              rw [associatedChainComplex_d]
              have hL := L.comm 0
              rw [Homotopy.dNext_zero_chainComplex,
                Homotopy.prevD_chainComplex, zero_add] at hL
              rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d] at hL
              convert hL using 1
              all_goals simp [hhom, associatedBoundary,
                AlgebraicTopology.AlternatingFaceMapComplex.objD]
              all_goals rfl
          | succ n =>
              rw [Homotopy.dNext_succ_chainComplex,
                Homotopy.prevD_chainComplex]
              rw [associatedChainComplex_d, associatedChainComplex_d]
              have hL := L.comm (n + 1)
              rw [Homotopy.dNext_succ_chainComplex,
                Homotopy.prevD_chainComplex] at hL
              rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
                AlgebraicTopology.alternatingFaceMapComplex_obj_d] at hL
              convert hL using 1
              all_goals simp [hhom, associatedBoundary,
                AlgebraicTopology.AlternatingFaceMapComplex.objD]
              all_goals rfl
      }
      have hnat (f : U ⟶ V) :
          normalizedToAssociated U ≫ associatedChainComplexMap f =
            normalizedChainComplexMap f ≫ normalizedToAssociated V := by
        apply HomologicalComplex.Hom.ext
        funext n
        change
          (Formalization.Books.Simplicial.Unit18.normalizedSubobject U n).arrow ≫
              f.app (op ⦋n⦌) =
            Formalization.Books.Simplicial.Unit18.normalizedSubobjectMap f n ≫
              (Formalization.Books.Simplicial.Unit18.normalizedSubobject V n).arrow
        exact
          (Formalization.Books.Simplicial.Unit18.normalizedSubobjectMap_arrow f n).symm
      have hcomp := (hK.compRight rV).compLeft (normalizedToAssociated U)
      rw [← Category.assoc] at hcomp
      rw [← Category.assoc] at hcomp
      rw [hnat a, hnat b] at hcomp
      dsimp [rV] at hcomp
      refine ⟨?_⟩
      simpa only [Category.assoc, sV.id, Category.comp_id] using hcomp
  | refl a =>
      exact ⟨_root_.Homotopy.ofEq rfl⟩
  | symm a b h ih =>
      exact ⟨ih.some.symm⟩
  | trans a b c h₁ h₂ ih₁ ih₂ =>
      exact ⟨ih₁.some.trans ih₂.some⟩

theorem additiveAssociatedChainMap_homotopyEquivalence
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : SimplicialObject C} {a : U ⟶ V}
    (H : Formalization.Books.Simplicial.Unit26.IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences C (ComplexShape.down ℕ)
      (additiveAssociatedChainComplexMap a) := by
  rcases H with ⟨b, hba, hab⟩
  have hba' := (additiveAssociatedChainMap_homotopic hba).some
  have hab' := (additiveAssociatedChainMap_homotopic hab).some
  have hcomp_ba :
      additiveAssociatedChainComplexMap b ≫ additiveAssociatedChainComplexMap a =
        additiveAssociatedChainComplexMap (b ≫ a) := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  have hcomp_ab :
      additiveAssociatedChainComplexMap a ≫ additiveAssociatedChainComplexMap b =
        additiveAssociatedChainComplexMap (a ≫ b) := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  have hid_V :
      additiveAssociatedChainComplexMap (𝟙 V) =
        𝟙 (additiveAssociatedChainComplex V) := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  have hid_U :
      additiveAssociatedChainComplexMap (𝟙 U) =
        𝟙 (additiveAssociatedChainComplex U) := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  have hbaK : _root_.Homotopy
      (additiveAssociatedChainComplexMap b ≫ additiveAssociatedChainComplexMap a)
      (𝟙 (additiveAssociatedChainComplex V)) := by
    rw [hcomp_ba, ← hid_V]
    exact hba'
  have habK : _root_.Homotopy
      (additiveAssociatedChainComplexMap a ≫ additiveAssociatedChainComplexMap b)
      (𝟙 (additiveAssociatedChainComplex U)) := by
    rw [hcomp_ab, ← hid_U]
    exact hab'
  change ∃ e : HomotopyEquiv (additiveAssociatedChainComplex U)
      (additiveAssociatedChainComplex V),
    e.hom = additiveAssociatedChainComplexMap a
  let e : HomotopyEquiv (additiveAssociatedChainComplex U)
      (additiveAssociatedChainComplex V) :=
    { hom := additiveAssociatedChainComplexMap a
      inv := additiveAssociatedChainComplexMap b
      homotopyHomInvId := habK
      homotopyInvHomId := hbaK }
  exact ⟨e, rfl⟩

theorem normalizedChainMap_homotopyEquivalence
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} {a : U ⟶ V}
    (H : Formalization.Books.Simplicial.Unit26.IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences C (ComplexShape.down ℕ)
      (normalizedChainComplexMap a) := by
  rcases H with ⟨b, hba, hab⟩
  have hba' := (normalizedChainMap_homotopic hba).some
  have hab' := (normalizedChainMap_homotopic hab).some
  have hcomp_ba :
      normalizedChainComplexMap b ≫ normalizedChainComplexMap a =
        normalizedChainComplexMap (b ≫ a) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact
      (Formalization.Books.Simplicial.Unit18.normalizedSubobjectMap_comp b a n).symm
  have hcomp_ab :
      normalizedChainComplexMap a ≫ normalizedChainComplexMap b =
        normalizedChainComplexMap (a ≫ b) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact
      (Formalization.Books.Simplicial.Unit18.normalizedSubobjectMap_comp a b n).symm
  have hid_V :
      normalizedChainComplexMap (𝟙 V) =
        𝟙 (normalizedChainComplex V) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact Formalization.Books.Simplicial.Unit18.normalizedSubobjectMap_id V n
  have hid_U :
      normalizedChainComplexMap (𝟙 U) =
        𝟙 (normalizedChainComplex U) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact Formalization.Books.Simplicial.Unit18.normalizedSubobjectMap_id U n
  have hbaK : _root_.Homotopy
      (normalizedChainComplexMap b ≫ normalizedChainComplexMap a)
      (𝟙 (normalizedChainComplex V)) := by
    rw [hcomp_ba, ← hid_V]
    exact hba'
  have habK : _root_.Homotopy
      (normalizedChainComplexMap a ≫ normalizedChainComplexMap b)
      (𝟙 (normalizedChainComplex U)) := by
    rw [hcomp_ab, ← hid_U]
    exact hab'
  change ∃ e : HomotopyEquiv (normalizedChainComplex U)
      (normalizedChainComplex V),
    e.hom = normalizedChainComplexMap a
  let e : HomotopyEquiv (normalizedChainComplex U)
      (normalizedChainComplex V) :=
    { hom := normalizedChainComplexMap a
      inv := normalizedChainComplexMap b
      homotopyHomInvId := habK
      homotopyInvHomId := hbaK }
  exact ⟨e, rfl⟩

end Formalization.Books.Simplicial.Unit27
