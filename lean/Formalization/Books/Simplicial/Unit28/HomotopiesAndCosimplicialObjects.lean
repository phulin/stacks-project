import Formalization.Books.Simplicial.Unit14.HomFromSimplicialSetsIntoCosimplicialObjects
import Formalization.Books.Simplicial.Unit25.DoldKanForCosimplicialObjects
import Formalization.Books.Simplicial.Unit26.Homotopies
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Opposite
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.Logic.Relation

/-!
# Simplicial Methods, Chapter 28: Homotopies and cosimplicial objects

This file uses the finite-product `Hom` construction from Chapter 14 and the
degreewise homotopy data from the source.  The latter is retained without any
finite-product hypothesis, while the former is used for the original cylinder
definition.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit28

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Simplicial.Unit14
open Formalization.Books.Simplicial.Unit25
open Formalization.Books.Simplicial.Unit26
open Formalization.Books.Homology.Unit03
open Opposite
open scoped _root_.Simplicial

universe v u v' u'

/-! ## The interval, its endpoint maps, and the cylinder definition -/

abbrev interval : SSet.{0} := Δ[1]

abbrev intervalFinite : Unit13.FiniteNonemptySimplicialSet (interval : SSet.{0}) :=
  Unit13.standardSimplex_finite_nonempty 1

/- The source's endpoint map is evaluation at the constant simplex. -/
noncomputable def homotopyEndpoint
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    (V : CosimplicialObject C) (ε : Fin 2) :
    hom interval V intervalFinite ⟶ V where
  app X := by
    let _ : Finite ((interval : SSet.{0}).obj (op X)) := by
      simpa only [SimplexCategory.mk_len] using (intervalFinite X.len).1
    exact Pi.π (fun _ : (interval : SSet.{0}).obj (op X) => V.obj X)
      (SSet.stdSimplex.const 1 ε (op X))
  naturality := by
    intro X Y f
    let _ : Finite ((interval : SSet.{0}).obj (op X)) := by
      simpa only [SimplexCategory.mk_len] using (intervalFinite X.len).1
    let _ : Finite ((interval : SSet.{0}).obj (op Y)) := by
      simpa only [SimplexCategory.mk_len] using (intervalFinite Y.len).1
    change
      homMapAt interval V intervalFinite f ≫
          Pi.π (fun _ : (interval : SSet.{0}).obj (op Y) => V.obj Y)
            (SSet.stdSimplex.const 1 ε (op Y)) =
        Pi.π (fun _ : (interval : SSet.{0}).obj (op X) => V.obj X)
            (SSet.stdSimplex.const 1 ε (op X)) ≫ V.map f
    have hε :
        (interval : SSet.{0}).map f.op (SSet.stdSimplex.const 1 ε (op Y)) =
          SSet.stdSimplex.const 1 ε (op X) := by
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      rfl
    change
      Pi.map' (interval.map f.op) (fun _ => V.map f) ≫
          Pi.π (fun _ : (interval : SSet.{0}).obj (op Y) => V.obj Y)
            (SSet.stdSimplex.const 1 ε (op Y)) =
        Pi.π (fun _ : (interval : SSet.{0}).obj (op X) => V.obj X)
            (SSet.stdSimplex.const 1 ε (op X)) ≫ V.map f
    rw [Pi.map'_comp_π]
    simp [hε]

noncomputable def homotopyEndpoint₀
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    (V : CosimplicialObject C) : hom interval V intervalFinite ⟶ V :=
  homotopyEndpoint V 0

noncomputable def homotopyEndpoint₁
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    (V : CosimplicialObject C) : hom interval V intervalFinite ⟶ V :=
  homotopyEndpoint V 1

structure CylinderHomotopy
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {U V : CosimplicialObject C} (a b : U ⟶ V) where
  h : U ⟶ hom interval V intervalFinite
  h₀ : h ≫ homotopyEndpoint₀ V = a
  h₁ : h ≫ homotopyEndpoint₁ V = b

/-! ## The category-independent, componentwise definition -/

structure DegreewiseHomotopy
    {C : Type u} [Category.{v} C]
    {U V : CosimplicialObject C} (a b : U ⟶ V) where
  h (n : ℕ) (α : (interval : SSet.{0}) _⦋n⦌) :
    U.obj (SimplexCategory.mk n) ⟶ V.obj (SimplexCategory.mk n)
  h_zero (n : ℕ) :
    h n (SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n))) =
      a.app (SimplexCategory.mk n)
  h_one (n : ℕ) :
    h n (SSet.stdSimplex.const 1 1 (op (SimplexCategory.mk n))) =
      b.app (SimplexCategory.mk n)
  naturality {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
      (α : (interval : SSet.{0}) _⦋m⦌) :
    U.map f ≫ h m α =
      h n ((interval : SSet.{0}).map f.op α) ≫ V.map f

theorem cylinderHomotopy_to_degreewise
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : CylinderHomotopy a b) : Nonempty (DegreewiseHomotopy a b) := by
  refine ⟨{
    h := fun n α => by
      let _ : Finite ((interval : SSet.{0}).obj (op (SimplexCategory.mk n))) := by
        simpa only [SimplexCategory.mk_len] using (intervalFinite n).1
      exact H.h.app (SimplexCategory.mk n) ≫
        Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk n)) =>
          V.obj (SimplexCategory.mk n)) α
    h_zero := by
      intro n
      let _ : Finite ((interval : SSet.{0}).obj (op (SimplexCategory.mk n))) := by
        simpa only [SimplexCategory.mk_len] using (intervalFinite n).1
      have h₀ := congrArg (fun k => k.app (SimplexCategory.mk n)) H.h₀
      change
        H.h.app (SimplexCategory.mk n) ≫
            Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk n)) =>
              V.obj (SimplexCategory.mk n))
              (SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n))) =
          a.app (SimplexCategory.mk n) at h₀
      exact h₀
    h_one := by
      intro n
      let _ : Finite ((interval : SSet.{0}).obj (op (SimplexCategory.mk n))) := by
        simpa only [SimplexCategory.mk_len] using (intervalFinite n).1
      have h₁ := congrArg (fun k => k.app (SimplexCategory.mk n)) H.h₁
      change
        H.h.app (SimplexCategory.mk n) ≫
            Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk n)) =>
              V.obj (SimplexCategory.mk n))
              (SSet.stdSimplex.const 1 1 (op (SimplexCategory.mk n))) =
          b.app (SimplexCategory.mk n) at h₁
      exact h₁
    naturality := by
      intro n m f α
      let _ : Finite ((interval : SSet.{0}).obj (op (SimplexCategory.mk n))) := by
        simpa only [SimplexCategory.mk_len] using (intervalFinite n).1
      let _ : Finite ((interval : SSet.{0}).obj (op (SimplexCategory.mk m))) := by
        simpa only [SimplexCategory.mk_len] using (intervalFinite m).1
      dsimp
      change
        U.map f ≫ H.h.app (SimplexCategory.mk m) ≫
            Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk m)) =>
              V.obj (SimplexCategory.mk m)) α =
          (H.h.app (SimplexCategory.mk n) ≫
            Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk n)) =>
              V.obj (SimplexCategory.mk n))
              ((interval : SSet.{0}).map f.op α)) ≫ V.map f
      calc
        U.map f ≫ H.h.app (SimplexCategory.mk m) ≫
              Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk m)) =>
                V.obj (SimplexCategory.mk m)) α =
            (U.map f ≫ H.h.app (SimplexCategory.mk m)) ≫
              Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk m)) =>
                V.obj (SimplexCategory.mk m)) α := by
          exact (Category.assoc _ _ _).symm
        _ = (H.h.app (SimplexCategory.mk n) ≫
              (hom interval V intervalFinite).map f) ≫
              Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk m)) =>
                V.obj (SimplexCategory.mk m)) α := by
          rw [H.h.naturality f]
        _ = (H.h.app (SimplexCategory.mk n) ≫
              homMapAt interval V intervalFinite f) ≫
              Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk m)) =>
                V.obj (SimplexCategory.mk m)) α := by
          rfl
        _ = (H.h.app (SimplexCategory.mk n) ≫
              Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk n)) =>
                V.obj (SimplexCategory.mk n))
                ((interval : SSet.{0}).map f.op α)) ≫ V.map f := by
          calc
            (H.h.app (SimplexCategory.mk n) ≫ homMapAt interval V intervalFinite f) ≫
                Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk m)) =>
                  V.obj (SimplexCategory.mk m)) α =
              H.h.app (SimplexCategory.mk n) ≫
                (homMapAt interval V intervalFinite f ≫
                  Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk m)) =>
                    V.obj (SimplexCategory.mk m)) α) := Category.assoc _ _ _
            _ = H.h.app (SimplexCategory.mk n) ≫
                (Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk n)) =>
                  V.obj (SimplexCategory.mk n))
                  ((interval : SSet.{0}).map f.op α) ≫ V.map f) := by
              change
                H.h.app (SimplexCategory.mk n) ≫
                  (Pi.map' (interval.map f.op) (fun _ => V.map f) ≫
                    Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk m)) =>
                      V.obj (SimplexCategory.mk m)) α) = _
              have hπ :
                  (Pi.map' (interval.map f.op) (fun _ => V.map f)) ≫
                      Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk m)) =>
                        V.obj (SimplexCategory.mk m)) α =
                    Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk n)) =>
                      V.obj (SimplexCategory.mk n))
                      ((interval : SSet.{0}).map f.op α) ≫ V.map f :=
                Pi.map'_comp_π
                  (f := fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk n)) =>
                    V.obj (SimplexCategory.mk n))
                  (g := fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk m)) =>
                    V.obj (SimplexCategory.mk m))
                  (p := interval.map f.op) (q := fun _ => V.map f) α
              exact congrArg (fun k => H.h.app (SimplexCategory.mk n) ≫ k) hπ
            _ = (H.h.app (SimplexCategory.mk n) ≫
                Pi.π (fun _ : (interval : SSet.{0}).obj (op (SimplexCategory.mk n)) =>
                  V.obj (SimplexCategory.mk n))
                  ((interval : SSet.{0}).map f.op α)) ≫ V.map f :=
              (Category.assoc _ _ _).symm
  }⟩

theorem degreewise_to_cylinderHomotopy
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) : Nonempty (CylinderHomotopy a b) := by
  refine ⟨{
    h := {
      app := by
        intro X
        let _ : Finite ((interval : SSet.{0}).obj (op X)) := by
          simpa only [SimplexCategory.mk_len] using (intervalFinite X.len).1
        exact Pi.lift (fun α => H.h X.len α)
      naturality := by
        intro X Y f
        let _ : Finite ((interval : SSet.{0}).obj (op X)) := by
          simpa only [SimplexCategory.mk_len] using (intervalFinite X.len).1
        let _ : Finite ((interval : SSet.{0}).obj (op Y)) := by
          simpa only [SimplexCategory.mk_len] using (intervalFinite Y.len).1
        dsimp
        apply Pi.hom_ext
        intro α
        change
          (U.map f ≫ Pi.lift (fun α => H.h Y.len α)) ≫ Pi.π _ α =
            (Pi.lift (fun α => H.h X.len α) ≫
              Pi.map' (interval.map f.op) (fun _ => V.map f)) ≫ Pi.π _ α
        rw [Category.assoc, Pi.lift_π, Category.assoc, Pi.map'_comp_π,
          ← Category.assoc, Pi.lift_π]
        exact H.naturality f α
    }
    h₀ := by
      ext X
      let _ : Finite ((interval : SSet.{0}).obj (op X)) := by
        simpa only [SimplexCategory.mk_len] using (intervalFinite X.len).1
      dsimp
      change
        Pi.lift (fun α => H.h X.len α) ≫
            Pi.π (fun _ : (interval : SSet.{0}).obj (op X) => V.obj X)
              (SSet.stdSimplex.const 1 0 (op X)) =
          a.app X
      rw [Pi.lift_π]
      exact H.h_zero X.len
    h₁ := by
      ext X
      let _ : Finite ((interval : SSet.{0}).obj (op X)) := by
        simpa only [SimplexCategory.mk_len] using (intervalFinite X.len).1
      dsimp
      change
        Pi.lift (fun α => H.h X.len α) ≫
            Pi.π (fun _ : (interval : SSet.{0}).obj (op X) => V.obj X)
              (SSet.stdSimplex.const 1 1 (op X)) =
          b.app X
      rw [Pi.lift_π]
      exact H.h_one X.len
  }⟩

theorem cylinderHomotopy_iff_degreewise
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {U V : CosimplicialObject C} {a b : U ⟶ V} :
    Nonempty (CylinderHomotopy a b) ↔ Nonempty (DegreewiseHomotopy a b) := by
  constructor
  · rintro ⟨H⟩
    exact cylinderHomotopy_to_degreewise H
  · rintro ⟨H⟩
    exact degreewise_to_cylinderHomotopy H

/-! ## The generated homotopy relation -/

def OneStepHomotopy
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    (a b : U ⟶ V) : Prop :=
  Nonempty (DegreewiseHomotopy a b)

def Homotopic
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    (a b : U ⟶ V) : Prop :=
  Relation.EqvGen (fun a b : U ⟶ V => OneStepHomotopy a b) a b

theorem oneStepHomotopy_iff_cylinderHomotopy
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {U V : CosimplicialObject C} {a b : U ⟶ V} :
    OneStepHomotopy a b ↔ Nonempty (CylinderHomotopy a b) := by
  rw [OneStepHomotopy, cylinderHomotopy_iff_degreewise]

theorem homotopicOfHomotopy
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    {a b : U ⟶ V} (H : DegreewiseHomotopy a b) : Homotopic a b :=
  Relation.EqvGen.rel a b (show OneStepHomotopy a b from ⟨H⟩)

theorem homotopic_is_equivalence
    {C : Type u} [Category.{v} C] (U V : CosimplicialObject C) :
    Equivalence (fun a b : U ⟶ V => Homotopic a b) := by
  exact Relation.EqvGen.is_equivalence _

theorem homotopic_refl
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    (a : U ⟶ V) : Homotopic a a :=
  Relation.EqvGen.refl a

theorem homotopic_symm
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    {a b : U ⟶ V} (h : Homotopic a b) : Homotopic b a := by
  exact (homotopic_is_equivalence U V).symm h

theorem homotopic_trans
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    {a b c : U ⟶ V} (hab : Homotopic a b) (hbc : Homotopic b c) :
    Homotopic a c := by
  exact (homotopic_is_equivalence U V).trans hab hbc

def trivialDegreewiseHomotopy
    {C : Type u} [Category.{v} C]
    {U V : CosimplicialObject C} (a : U ⟶ V) :
    DegreewiseHomotopy a a where
  h n _ := a.app (SimplexCategory.mk n)
  h_zero n := rfl
  h_one n := rfl
  naturality f _ := by simpa using a.naturality f

theorem trivialOneStepHomotopy
    {C : Type u} [Category.{v} C]
    {U V : CosimplicialObject C} (a : U ⟶ V) : OneStepHomotopy a a :=
  ⟨trivialDegreewiseHomotopy a⟩

/-! ## Opposite objects and comparison with simplicial homotopies -/

def oppositeCosimplicialObject
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C) :
    SimplicialObject Cᵒᵖ where
  obj X := op (U.obj X.unop)
  map f := (U.map f.unop).op
  map_id X := by
    change (U.map (𝟙 X.unop)).op = 𝟙 (op (U.obj X.unop))
    rw [U.map_id]
    rfl
  map_comp := by
    intro X Y Z f g
    change
      (U.map (g.unop ≫ f.unop)).op =
        (U.map f.unop).op ≫ (U.map g.unop).op
    rw [U.map_comp, op_comp]

def oppositeCosimplicialMap
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    (a : U ⟶ V) : oppositeCosimplicialObject V ⟶
      oppositeCosimplicialObject U where
  app X := (a.app X.unop).op
  naturality X Y f := by
    change
      (V.map f.unop).op ≫ (a.app Y.unop).op =
        (a.app X.unop).op ≫ (U.map f.unop).op
    simpa [op_comp] using
      (congrArg (fun k => k.op) (a.naturality f.unop)).symm

/-- Recover a cosimplicial map from a map between the opposite simplicial
objects. -/
def unoppositeCosimplicialMap
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    (a : oppositeCosimplicialObject V ⟶ oppositeCosimplicialObject U) :
    U ⟶ V where
  app X := (a.app (op X)).unop
  naturality X Y f := by
    have h := a.naturality f.op
    simpa [oppositeCosimplicialObject, op_comp] using
      (congrArg (fun k => k.unop) h).symm

@[simp]
theorem unoppositeCosimplicialMap_oppositeCosimplicialMap
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    (a : U ⟶ V) :
    unoppositeCosimplicialMap (oppositeCosimplicialMap a) = a := by
  ext X
  rfl

@[simp]
theorem oppositeCosimplicialMap_unoppositeCosimplicialMap
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    (a : oppositeCosimplicialObject V ⟶ oppositeCosimplicialObject U) :
    oppositeCosimplicialMap (unoppositeCosimplicialMap a) = a := by
  ext X
  rfl

theorem compareHomotopies
    {C : Type u} [Category.{v} C]
    {U V : CosimplicialObject C} {a b : U ⟶ V} :
    Nonempty (DegreewiseHomotopy a b) ↔
      Nonempty (Formalization.Books.Simplicial.Unit26.DegreewiseHomotopy
        (oppositeCosimplicialMap a) (oppositeCosimplicialMap b)) := by
  constructor
  · rintro ⟨H⟩
    refine ⟨{
      h := fun n i => (H.h n (intervalSimplex n i)).op
      h_zero := by
        intro n
        change (H.h n (intervalSimplex n 0)).op = (b.app (SimplexCategory.mk n)).op
        have hz : intervalSimplex n 0 =
            SSet.stdSimplex.const 1 1 (op (SimplexCategory.mk n)) := by
          apply SSet.stdSimplex.ext
          intro j
          rw [intervalSimplex_zero_is_constant_one n j]
          rfl
        rw [hz]
        exact congrArg (fun k => k.op) (H.h_one n)
      h_last := by
        intro n
        change (H.h n (intervalSimplex n (Fin.last (n + 1)))).op =
          (a.app (SimplexCategory.mk n)).op
        have hl : intervalSimplex n (Fin.last (n + 1)) =
            SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n)) := by
          apply SSet.stdSimplex.ext
          intro j
          rw [intervalSimplex_last_is_constant_zero n j]
          rfl
        rw [hl]
        exact congrArg (fun k => k.op) (H.h_zero n)
      face_of_gt := by
        intro n i j hji
        have hindex :
            (interval : SSet.{0}).map (SimplexCategory.δ j).op
                (intervalSimplex (n + 1) i) =
              intervalSimplex n (i.pred (Fin.ne_zero_of_lt hji)) := by
          change (Δ[1] : SSet.{0}).δ j (SSet.stdSimplex.objMk₁ i) = _
          exact SSet.stdSimplex.δ_objMk₁_of_lt i j hji
        simpa [SimplicialObject.δ, oppositeCosimplicialObject, op_comp, hindex] using
          congrArg (fun k => k.op)
            (H.naturality (SimplexCategory.δ j) (intervalSimplex (n + 1) i))
      face_of_le := by
        intro n i j hij
        have hindex :
            (interval : SSet.{0}).map (SimplexCategory.δ j).op
                (intervalSimplex (n + 1) i) =
              intervalSimplex n
                (i.castPred (Fin.ne_last_of_lt
                  (lt_of_le_of_lt hij j.castSucc_lt_succ))) := by
          change (Δ[1] : SSet.{0}).δ j (SSet.stdSimplex.objMk₁ i) = _
          exact SSet.stdSimplex.δ_objMk₁_of_le i j hij
        simpa [SimplicialObject.δ, oppositeCosimplicialObject, op_comp, hindex] using
          congrArg (fun k => k.op)
            (H.naturality (SimplexCategory.δ j) (intervalSimplex (n + 1) i))
      degeneracy_of_gt := by
        intro n i j hji
        have hindex :
            (interval : SSet.{0}).map (SimplexCategory.σ j).op
                (intervalSimplex n i) = intervalSimplex (n + 1) i.succ := by
          change (Δ[1] : SSet.{0}).σ j (SSet.stdSimplex.objMk₁ i) = _
          exact SSet.stdSimplex.σ_objMk₁_of_lt i j hji
        simpa [SimplicialObject.σ, oppositeCosimplicialObject, op_comp, hindex] using
          congrArg (fun k => k.op)
            (H.naturality (SimplexCategory.σ j) (intervalSimplex n i))
      degeneracy_of_le := by
        intro n i j hij
        have hindex :
            (interval : SSet.{0}).map (SimplexCategory.σ j).op
                (intervalSimplex n i) = intervalSimplex (n + 1) i.castSucc := by
          change (Δ[1] : SSet.{0}).σ j (SSet.stdSimplex.objMk₁ i) = _
          exact SSet.stdSimplex.σ_objMk₁_of_le i j hij
        simpa [SimplicialObject.σ, oppositeCosimplicialObject, op_comp, hindex] using
          congrArg (fun k => k.op)
            (H.naturality (SimplexCategory.σ j) (intervalSimplex n i))
    }⟩
  · rintro ⟨H⟩
    let hh : ∀ (n : ℕ), (interval : SSet.{0}) _⦋n⦌ →
        (U.obj (SimplexCategory.mk n) ⟶ V.obj (SimplexCategory.mk n)) :=
      fun n α =>
        (H.h n (Function.invFun (intervalSimplex n) α)).unop
    have hinv : ∀ (n : ℕ) (i : Fin (n + 2)),
        Function.invFun
            ((intervalSimplex.{0} n) :
              Fin (n + 2) → (interval : SSet.{0}) _⦋n⦌)
            (intervalSimplex.{0} n i) = i := by
      intro n i
      let : Nonempty ((interval : SSet.{0}) _⦋n⦌) :=
        interval_degree_finite_nonempty n |>.2
      apply (intervalSimplex_bijective.{0} n).1
      rw [Function.leftInverse_invFun (intervalSimplex_bijective.{0} n).1]
    have hδ : ∀ {n : ℕ} (j : Fin (n + 2))
        (α : (interval : SSet.{0}) _⦋n + 1⦌),
        U.map (SimplexCategory.δ j) ≫ hh (n + 1) α =
          hh n ((interval : SSet.{0}).map (SimplexCategory.δ j).op α) ≫
            V.map (SimplexCategory.δ j) := by
      intro n j α
      let : Nonempty ((interval : SSet.{0}) _⦋n + 1⦌) :=
        interval_degree_finite_nonempty (n + 1) |>.2
      let i := Function.invFun (intervalSimplex (n + 1)) α
      have hi : intervalSimplex (n + 1) i = α := by
        exact Function.rightInverse_invFun (intervalSimplex_bijective (n + 1)).2 α
      by_cases hji : j.castSucc < i
      · have hindex :
            (interval : SSet.{0}).map (SimplexCategory.δ j).op
                (intervalSimplex (n + 1) i) =
              intervalSimplex n (i.pred (Fin.ne_zero_of_lt hji)) := by
          change (Δ[1] : SSet.{0}).δ j (SSet.stdSimplex.objMk₁ i) = _
          exact SSet.stdSimplex.δ_objMk₁_of_lt i j hji
        rw [← hi]
        rw [hindex]
        dsimp [hh]
        rw [hinv (n + 1) i, hinv n (i.pred (Fin.ne_zero_of_lt hji))]
        simpa [SimplicialObject.δ, oppositeCosimplicialObject, op_comp] using
          congrArg (fun q => q.unop) (H.face_of_gt i j hji)
      · have hij : i ≤ j.castSucc := le_of_not_gt hji
        have hindex :
            (interval : SSet.{0}).map (SimplexCategory.δ j).op
                (intervalSimplex (n + 1) i) =
              intervalSimplex n
                (i.castPred (Fin.ne_last_of_lt
                  (lt_of_le_of_lt hij j.castSucc_lt_succ))) := by
          change (Δ[1] : SSet.{0}).δ j (SSet.stdSimplex.objMk₁ i) = _
          exact SSet.stdSimplex.δ_objMk₁_of_le i j hij
        rw [← hi]
        rw [hindex]
        dsimp [hh]
        rw [hinv (n + 1) i,
          hinv n (i.castPred (Fin.ne_last_of_lt
            (lt_of_le_of_lt hij j.castSucc_lt_succ)))]
        simpa [SimplicialObject.δ, oppositeCosimplicialObject, op_comp] using
          congrArg (fun q => q.unop) (H.face_of_le i j hij)
    have hσ : ∀ {n : ℕ} (j : Fin (n + 1))
        (α : (interval : SSet.{0}) _⦋n⦌),
        U.map (SimplexCategory.σ j) ≫ hh n α =
          hh (n + 1) ((interval : SSet.{0}).map (SimplexCategory.σ j).op α) ≫
            V.map (SimplexCategory.σ j) := by
      intro n j α
      let : Nonempty ((interval : SSet.{0}) _⦋n⦌) :=
        interval_degree_finite_nonempty n |>.2
      let i := Function.invFun (intervalSimplex n) α
      have hi : intervalSimplex n i = α := by
        exact Function.rightInverse_invFun (intervalSimplex_bijective n).2 α
      by_cases hji : j.castSucc < i
      · have hindex :
            (interval : SSet.{0}).map (SimplexCategory.σ j).op
                (intervalSimplex n i) = intervalSimplex (n + 1) i.succ := by
          change (Δ[1] : SSet.{0}).σ j (SSet.stdSimplex.objMk₁ i) = _
          exact SSet.stdSimplex.σ_objMk₁_of_lt i j hji
        rw [← hi]
        rw [hindex]
        dsimp [hh]
        rw [hinv n i, hinv (n + 1) i.succ]
        simpa [SimplicialObject.σ, oppositeCosimplicialObject, op_comp] using
          congrArg (fun q => q.unop) (H.degeneracy_of_gt i j hji)
      · have hij : i ≤ j.castSucc := le_of_not_gt hji
        have hindex :
            (interval : SSet.{0}).map (SimplexCategory.σ j).op
                (intervalSimplex n i) = intervalSimplex (n + 1) i.castSucc := by
          change (Δ[1] : SSet.{0}).σ j (SSet.stdSimplex.objMk₁ i) = _
          exact SSet.stdSimplex.σ_objMk₁_of_le i j hij
        rw [← hi]
        rw [hindex]
        dsimp [hh]
        rw [hinv n i, hinv (n + 1) i.castSucc]
        simpa [SimplicialObject.σ, oppositeCosimplicialObject, op_comp] using
          congrArg (fun q => q.unop) (H.degeneracy_of_le i j hij)
    have hnat : ∀ {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
        (α : (interval : SSet.{0}) _⦋m⦌),
        U.map f ≫ hh m α =
          hh n ((interval : SSet.{0}).map f.op α) ≫ V.map f := by
      let P : ℕ → Prop := fun k =>
        ∀ n m, k = n + m →
          ∀ (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
            (α : (interval : SSet.{0}) _⦋m⦌),
            U.map f ≫ hh m α =
              hh n ((interval : SSet.{0}).map f.op α) ≫ V.map f
      have hP : ∀ k, P k := by
        intro k
        induction k using Nat.strong_induction_on with
        | h k ih =>
          intro n m hnm f α
          by_cases hni : Function.Injective f.toOrderHom
          · by_cases hns : Function.Surjective f.toOrderHom
            · have hcard : n + 1 = m + 1 := by
                simpa using Nat.card_congr
                  (Equiv.ofBijective f.toOrderHom ⟨hni, hns⟩)
              have hnm' : n = m := by omega
              subst m
              have hmono : Mono f := (SimplexCategory.mono_iff_injective).mpr hni
              rw [SimplexCategory.eq_id_of_mono f, U.map_id, V.map_id,
                Category.id_comp, Category.comp_id]
              have hα :
                  (interval : SSet.{0}).map (𝟙 (op (SimplexCategory.mk n))) α = α := by
                simp
              have hα' :
                  (interval : SSet.{0}).map (𝟙 (SimplexCategory.mk n)).op α = α := by
                simp
              rw [hα']
            · cases m with
              | zero =>
                exfalso
                apply hns
                intro y
                exact ⟨0, (Fin.eq_zero _).trans (Fin.eq_zero y).symm⟩
              | succ m =>
                obtain ⟨i, f', hf⟩ :=
                  SimplexCategory.eq_comp_δ_of_not_surjective f hns
                have hi := ih (n + m) (by omega) n m rfl f'
                  ((interval : SSet.{0}).map (SimplexCategory.δ i).op α)
                rw [hf, U.map_comp, Category.assoc, hδ i α]
                rw [← Category.assoc, hi]
                have hcomp :
                    (interval : SSet.{0}).map (f' ≫ SimplexCategory.δ i).op α =
                      (interval : SSet.{0}).map f'.op
                        ((interval : SSet.{0}).map (SimplexCategory.δ i).op α) := by
                  rw [op_comp, Functor.map_comp]
                  rfl
                rw [hcomp, V.map_comp]
                simp only [Category.assoc]
          · cases n with
            | zero =>
              exfalso
              apply hni
              intro x y hxy
              exact (Fin.eq_zero x).trans (Fin.eq_zero y).symm
            | succ n =>
              obtain ⟨i, f', hf⟩ :=
                SimplexCategory.eq_σ_comp_of_not_injective f hni
              have hi := ih (n + m) (by omega) n m rfl f' α
              rw [hf, U.map_comp, Category.assoc]
              rw [hi]
              rw [← Category.assoc, hσ i ((interval : SSet.{0}).map f'.op α)]
              have hcomp :
                  (interval : SSet.{0}).map (SimplexCategory.σ i ≫ f').op α =
                    (interval : SSet.{0}).map (SimplexCategory.σ i).op
                      ((interval : SSet.{0}).map f'.op α) := by
                rw [op_comp, Functor.map_comp]
                rfl
              rw [hcomp, V.map_comp]
              simp only [Category.assoc]
      intro n m f α
      exact hP (n + m) n m rfl f α
    refine ⟨{
      h := hh
      h_zero := by
        intro n
        have hl : intervalSimplex n (Fin.last (n + 1)) =
            SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n)) := by
          apply SSet.stdSimplex.ext
          intro j
          rw [intervalSimplex_last_is_constant_zero n j]
          rfl
        have hi : Function.invFun (intervalSimplex n)
            (SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n))) =
              Fin.last (n + 1) := by
          rw [← hl]
          exact hinv n (Fin.last (n + 1))
        dsimp [hh]
        rw [hi]
        simpa [oppositeCosimplicialMap, oppositeCosimplicialObject] using
          congrArg (fun q => q.unop) (H.h_last n)
      h_one := by
        intro n
        have hz : intervalSimplex n 0 =
            SSet.stdSimplex.const 1 1 (op (SimplexCategory.mk n)) := by
          apply SSet.stdSimplex.ext
          intro j
          rw [intervalSimplex_zero_is_constant_one n j]
          rfl
        have hi : Function.invFun (intervalSimplex n)
            (SSet.stdSimplex.const 1 1 (op (SimplexCategory.mk n))) = 0 := by
          rw [← hz]
          exact hinv n 0
        dsimp [hh]
        rw [hi]
        simpa [oppositeCosimplicialMap, oppositeCosimplicialObject] using
          congrArg (fun q => q.unop) (H.h_zero n)
      naturality := by
        intro n m f α
        exact hnat f α
    }⟩

private theorem eqvGen_map {A B : Type*} {r : A → A → Prop}
    {s : B → B → Prop} (F : A → B)
    (hF : ∀ {a b}, r a b → s (F a) (F b)) {a b : A}
    (h : Relation.EqvGen r a b) : Relation.EqvGen s (F a) (F b) := by
  induction h with
  | rel a b h => exact Relation.EqvGen.rel _ _ (hF h)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem homotopic_iff_opposite_homotopic
    {C : Type u} [Category.{v} C]
    {U V : CosimplicialObject C} {a b : U ⟶ V} :
    Homotopic a b ↔
      Formalization.Books.Simplicial.Unit26.Homotopic
        (oppositeCosimplicialMap a) (oppositeCosimplicialMap b) := by
  constructor
  · intro h
    apply eqvGen_map oppositeCosimplicialMap (a := a) (b := b) _ h
    intro q r hqr
    rcases (compareHomotopies).1 hqr with ⟨H⟩
    exact ⟨Formalization.Books.Simplicial.Unit26.degreewiseHomotopyToHomotopy H⟩
  · intro h
    have mapped : Homotopic
        (unoppositeCosimplicialMap (oppositeCosimplicialMap a))
        (unoppositeCosimplicialMap (oppositeCosimplicialMap b)) :=
      eqvGen_map unoppositeCosimplicialMap (a := oppositeCosimplicialMap a)
      (b := oppositeCosimplicialMap b) (s := fun q r => OneStepHomotopy q r)
      (fun {q r} hqr => by
        rcases hqr with ⟨H⟩
        have HD :=
          Formalization.Books.Simplicial.Unit26.homotopyToDegreewiseHomotopy H
        have Hop : Nonempty
            (Formalization.Books.Simplicial.Unit26.DegreewiseHomotopy
              (oppositeCosimplicialMap (unoppositeCosimplicialMap q))
              (oppositeCosimplicialMap (unoppositeCosimplicialMap r))) := by
          simpa using ⟨HD⟩
        exact (compareHomotopies).2 Hop) h
    simpa using mapped

/-! ## Functoriality, in covariant and contravariant forms -/

def mapDegreewiseHomotopy
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) (F : C ⥤ D) :
    DegreewiseHomotopy
      (((CosimplicialObject.whiskering C D).obj F).map a)
      (((CosimplicialObject.whiskering C D).obj F).map b) where
  h n α := F.map (H.h n α)
  h_zero n := by
    change F.map (H.h n _) = F.map (a.app (SimplexCategory.mk n))
    exact congrArg F.map (H.h_zero n)
  h_one n := by
    change F.map (H.h n _) = F.map (b.app (SimplexCategory.mk n))
    exact congrArg F.map (H.h_one n)
  naturality f α := by
    change F.map (U.map f) ≫ F.map (H.h _ α) =
      F.map (H.h _ _) ≫ F.map (V.map f)
    simpa only [Functor.map_comp] using congrArg F.map (H.naturality f α)

theorem map_homotopic
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {U V : CosimplicialObject C} {a b : U ⟶ V} (H : Homotopic a b)
    (F : C ⥤ D) :
    Homotopic
      (((CosimplicialObject.whiskering C D).obj F).map a)
      (((CosimplicialObject.whiskering C D).obj F).map b) := by
  apply eqvGen_map
    (fun q : U ⟶ V => ((CosimplicialObject.whiskering C D).obj F).map q)
    (a := a) (b := b) _ H
  rintro q r ⟨K⟩
  exact ⟨mapDegreewiseHomotopy K F⟩

/- The componentwise construction also gives the original cylinder notion
   whenever both source and target categories have finite products. -/
theorem map_cylinderHomotopy
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {D : Type u'} [Category.{v'} D] [HasFiniteProducts D]
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : Nonempty (CylinderHomotopy a b)) (F : C ⥤ D) :
    Nonempty (CylinderHomotopy
      (((CosimplicialObject.whiskering C D).obj F).map a)
      (((CosimplicialObject.whiskering C D).obj F).map b)) := by
  rcases H with ⟨H⟩
  exact degreewise_to_cylinderHomotopy
    (mapDegreewiseHomotopy (cylinderHomotopy_to_degreewise H).some F)

def contravariantSimplicialObject
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ Dᵒᵖ) (U : CosimplicialObject C) : SimplicialObject D :=
  ((SimplicialObject.whiskering Cᵒᵖ D).obj F.leftOp).obj
    (oppositeCosimplicialObject U)

def contravariantSimplicialMap
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {U V : CosimplicialObject C} (F : C ⥤ Dᵒᵖ) (a : U ⟶ V) :
    contravariantSimplicialObject F V ⟶ contravariantSimplicialObject F U :=
  ((SimplicialObject.whiskering Cᵒᵖ D).obj F.leftOp).map
    (oppositeCosimplicialMap a)
def contravariantCosimplicialObject
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ Dᵒᵖ) (U : SimplicialObject C) : CosimplicialObject D where
  obj X := unop (F.obj (U.obj (op X)))
  map f := (F.map (U.map f.op)).unop
  map_id X := by
    change
      (F.map (U.map (𝟙 (op X)))).unop =
        𝟙 (unop (F.obj (U.obj (op X))))
    rw [U.map_id, F.map_id]
    rfl
  map_comp := by
    intro X Y Z f g
    change
      (F.map (U.map (g.op ≫ f.op))).unop =
        (F.map (U.map f.op)).unop ≫
          (F.map (U.map g.op)).unop
    rw [U.map_comp, F.map_comp, unop_comp]

def contravariantCosimplicialMap
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {U V : SimplicialObject C} (F : C ⥤ Dᵒᵖ) (a : U ⟶ V) :
    contravariantCosimplicialObject F V ⟶ contravariantCosimplicialObject F U where
  app X := (F.map (a.app (op X))).unop
  naturality X Y f := by
    change
      (F.map (V.map f.op)).unop ≫ (F.map (a.app (op Y))).unop =
        (F.map (a.app (op X))).unop ≫ (F.map (U.map f.op)).unop
    have h := congrArg F.map (a.naturality f.op)
    simpa only [Functor.map_comp, unop_comp] using
      congrArg (fun k => k.unop) h.symm

lemma functorialHomotopy
    {D : Type u} [Category.{v} D] {D' : Type u'} [Category.{v'} D']
    {U V : SimplicialObject D} {a b : U ⟶ V}
    (H : Formalization.Books.Simplicial.Unit26.Homotopic a b)
    (F : D ⥤ D') :
    Formalization.Books.Simplicial.Unit26.Homotopic
      (((SimplicialObject.whiskering D D').obj F).map a)
      (((SimplicialObject.whiskering D D').obj F).map b) := by
  exact Formalization.Books.Simplicial.Unit26.map_homotopic H F

private theorem mapSimplicialHomotopic
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Formalization.Books.Simplicial.Unit26.Homotopic a b)
    (F : CategoryTheory.Functor C D) :
    Formalization.Books.Simplicial.Unit26.Homotopic
      (((SimplicialObject.whiskering C D).obj F).map a)
      (((SimplicialObject.whiskering C D).obj F).map b) := by
  apply eqvGen_map
    (fun q : U ⟶ V => ((SimplicialObject.whiskering C D).obj F).map q)
    (a := a) (b := b) _ H
  rintro q r ⟨K⟩
  exact ⟨Formalization.Books.Simplicial.Unit26.degreewiseHomotopyToHomotopy
    (Formalization.Books.Simplicial.Unit26.mapDegreewiseHomotopy
      (Formalization.Books.Simplicial.Unit26.homotopyToDegreewiseHomotopy K) F)⟩

theorem functorialCosimplicialHomotopy
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {U V : CosimplicialObject C} {a b : U ⟶ V} (H : Homotopic a b)
    (F : C ⥤ C') : Homotopic
      (((CosimplicialObject.whiskering C C').obj F).map a)
      (((CosimplicialObject.whiskering C C').obj F).map b) := by
  exact map_homotopic H F

theorem functorialContravariantSimplicialHomotopy
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Formalization.Books.Simplicial.Unit26.Homotopic a b)
    (F : C ⥤ Dᵒᵖ) :
    Homotopic
      (contravariantCosimplicialMap F a)
      (contravariantCosimplicialMap F b) := by
  apply eqvGen_map (fun q : U ⟶ V => contravariantCosimplicialMap F q)
    (a := a) (b := b) _ H
  rintro q r ⟨K⟩
  let KD := Formalization.Books.Simplicial.Unit26.homotopyToDegreewiseHomotopy K
  let KF := Formalization.Books.Simplicial.Unit26.mapDegreewiseHomotopy KD F
  have Kop : Nonempty (Formalization.Books.Simplicial.Unit26.DegreewiseHomotopy
      (oppositeCosimplicialMap (contravariantCosimplicialMap F q))
      (oppositeCosimplicialMap (contravariantCosimplicialMap F r))) := by
    simpa [contravariantCosimplicialMap, contravariantCosimplicialObject,
      oppositeCosimplicialMap, oppositeCosimplicialObject, KF, KD] using ⟨KF⟩
  exact (compareHomotopies).2 Kop

theorem functorialContravariantCosimplicialHomotopy
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {U V : CosimplicialObject C} {a b : U ⟶ V} (H : Homotopic a b)
    (F : C ⥤ Dᵒᵖ) :
    Formalization.Books.Simplicial.Unit26.Homotopic
      (contravariantSimplicialMap F a)
      (contravariantSimplicialMap F b) := by
  apply eqvGen_map (fun q : U ⟶ V => contravariantSimplicialMap F q)
    (a := a) (b := b) _ H
  rintro q r ⟨K⟩
  rcases (compareHomotopies (a := q) (b := r)).1 ⟨K⟩ with ⟨Kop⟩
  let KF := Formalization.Books.Simplicial.Unit26.mapDegreewiseHomotopy Kop F.leftOp
  have Kcontra : Formalization.Books.Simplicial.Unit26.DegreewiseHomotopy
      (contravariantSimplicialMap F q) (contravariantSimplicialMap F r) := by
    simpa [contravariantSimplicialMap, contravariantSimplicialObject,
      oppositeCosimplicialMap, oppositeCosimplicialObject, KF] using KF
  exact ⟨Formalization.Books.Simplicial.Unit26.degreewiseHomotopyToHomotopy Kcontra⟩

/-! ## Homotopy equivalences -/

def IsHomotopyEquivalence
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    (a : U ⟶ V) : Prop :=
  ∃ b : V ⟶ U, Homotopic (b ≫ a) (𝟙 V) ∧ Homotopic (a ≫ b) (𝟙 U)

def HomotopyEquivalent
    {C : Type u} [Category.{v} C] (U V : CosimplicialObject C) : Prop :=
  ∃ a : U ⟶ V, IsHomotopyEquivalence a

/-! ## The split Čech conerve / pushout example -/

def splitPushoutArrowHom
    {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : f ≫ s = 𝟙 X) : Arrow.mk f ⟶ Arrow.mk f :=
  Arrow.homMk (𝟙 X) (s ≫ f) (by
    simpa [Category.assoc] using (congrArg (fun k => k ≫ f) hs).symm)

noncomputable def splitPushoutSelfMap
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] :
    f.cechConerve ⟶ f.cechConerve :=
  Arrow.mapCechConerve (splitPushoutArrowHom f.hom s hs)

noncomputable def splitPushoutHomotopyComponent
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]
    (n : ℕ) (α : (interval : SSet.{0}).obj (op (SimplexCategory.mk n))) :
    widePushout f.left (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom) ⟶
      widePushout f.left (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom) :=
  WidePushout.desc (WidePushout.head _)
    (fun i : Fin (n + 1) => if α i = 0 then
      s ≫ WidePushout.head (B := f.left)
        (objs := fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)
      else WidePushout.ι (B := f.left)
        (objs := fun _ : Fin (n + 1) => f.right) (fun _ => f.hom) i)
    (fun i : Fin (n + 1) => by
      by_cases h : α i = 0
      · rw [if_pos h, ← Category.assoc, hs, Category.id_comp]
      · rw [if_neg h]
        exact WidePushout.arrow_ι (B := f.left)
          (objs := fun _ : Fin (n + 1) => f.right) (fun _ => f.hom) i)

theorem splitPushoutSelfMap_ι
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] (n : ℕ)
    (i : Fin (n + 1)) :
    WidePushout.ι (B := f.left) (objs := fun _ : Fin (n + 1) => f.right)
        (fun _ => f.hom) i ≫ (splitPushoutSelfMap f s hs).app (SimplexCategory.mk n) =
      (s ≫ f.hom) ≫ WidePushout.ι (B := f.left)
        (objs := fun _ : Fin (n + 1) => f.right) (fun _ => f.hom) i := by
  dsimp [splitPushoutSelfMap, splitPushoutArrowHom, Arrow.mapCechConerve]
  simp only [Arrow.homMk_right]
  exact WidePushout.ι_desc (fun _ : Fin (n + 1) => f.hom)
    ((𝟙 f.left) ≫ WidePushout.head (fun _ : Fin (n + 1) => f.hom))
    (fun i => (s ≫ f.hom) ≫ WidePushout.ι (fun _ : Fin (n + 1) => f.hom) i) _ i

theorem splitPushoutSelfMap_head
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] (X : SimplexCategory) :
    WidePushout.head (B := f.left) (objs := fun _ : Fin (X.len + 1) => f.right)
        (fun _ => f.hom) ≫ (splitPushoutSelfMap f s hs).app X =
      WidePushout.head (B := f.left) (objs := fun _ : Fin (X.len + 1) => f.right)
        (fun _ => f.hom) := by
  dsimp [splitPushoutSelfMap, splitPushoutArrowHom, Arrow.mapCechConerve]
  simp only [Arrow.homMk_left, Arrow.homMk_right]
  exact (WidePushout.head_desc (fun _ : Fin (X.len + 1) => f.hom)
    ((𝟙 f.left) ≫ WidePushout.head (fun _ : Fin (X.len + 1) => f.hom))
    (fun i => (s ≫ f.hom) ≫ WidePushout.ι (fun _ : Fin (X.len + 1) => f.hom) i) _).trans
      (Category.id_comp _)

theorem splitPushoutHomotopyComponent_zero
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] (n : ℕ) :
    splitPushoutHomotopyComponent f s hs n
      (SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n))) =
        (splitPushoutSelfMap f s hs).app (SimplexCategory.mk n) := by
  apply WidePushout.hom_ext (fun _ : Fin (n + 1) => f.hom)
  · intro i
    dsimp [splitPushoutHomotopyComponent]
    rw [WidePushout.ι_desc]
    have hc : SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n)) i = 0 := rfl
    rw [if_pos hc]
    have hfirst : s ≫ WidePushout.head (B := f.left)
        (objs := fun _ : Fin (n + 1) => f.right) (fun _ => f.hom) =
      (s ≫ f.hom) ≫ WidePushout.ι (B := f.left)
        (objs := fun _ : Fin (n + 1) => f.right) (fun _ => f.hom) i := by
      simpa [Category.assoc] using congrArg (fun k => s ≫ k)
        (WidePushout.arrow_ι (fun _ : Fin (n + 1) => f.hom) i).symm
    exact hfirst.trans (splitPushoutSelfMap_ι f s hs n i).symm
  · dsimp [splitPushoutHomotopyComponent]
    rw [WidePushout.head_desc]
    exact splitPushoutSelfMap_head f s hs (SimplexCategory.mk n) |>.symm

theorem splitPushoutHomotopyComponent_one
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] (n : ℕ) :
    splitPushoutHomotopyComponent f s hs n
      (SSet.stdSimplex.const 1 1 (op (SimplexCategory.mk n))) =
        (𝟙 f.cechConerve : f.cechConerve ⟶ f.cechConerve).app
          (SimplexCategory.mk n) := by
  apply WidePushout.hom_ext (fun _ : Fin (n + 1) => f.hom)
  · intro i
    dsimp [splitPushoutHomotopyComponent]
    rw [WidePushout.ι_desc]
    have hc : ¬ SSet.stdSimplex.const 1 1 (op (SimplexCategory.mk n)) i = 0 := by
      change ¬ (1 : Fin 2) = 0
      simp
    rw [if_neg hc]
    change WidePushout.ι _ i = WidePushout.ι _ i ≫ 𝟙 _
    simp
  · dsimp [splitPushoutHomotopyComponent]
    rw [WidePushout.head_desc]
    change WidePushout.head _ = WidePushout.head _ ≫ 𝟙 _
    simp

noncomputable def splitPushoutDegreewiseHomotopy
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] :
    DegreewiseHomotopy (splitPushoutSelfMap f s hs) (𝟙 f.cechConerve) where
  h := splitPushoutHomotopyComponent f s hs
  h_zero := splitPushoutHomotopyComponent_zero f s hs
  h_one := splitPushoutHomotopyComponent_one f s hs
  naturality := by
    intro n m g α
    apply WidePushout.hom_ext (fun _ : Fin (n + 1) => f.hom)
    · intro i
      dsimp [splitPushoutHomotopyComponent, Arrow.cechConerve]
      simp only [← Category.assoc, WidePushout.ι_desc]
      by_cases hα : α (g.toOrderHom i) = 0
      · rw [if_pos hα]
        have hα' : ((interval : SSet.{0}).map g.op α) i = 0 := hα
        rw [if_pos hα']
        simp only [Category.assoc, WidePushout.head_desc]
      · rw [if_neg hα]
        have hα' : ¬ ((interval : SSet.{0}).map g.op α) i = 0 := hα
        rw [if_neg hα']
        exact (WidePushout.ι_desc (fun _ : Fin (n + 1) => f.hom)
          (WidePushout.head (fun _ : Fin (m + 1) => f.hom))
          (fun i => WidePushout.ι (fun _ : Fin (m + 1) => f.hom) (g.toOrderHom i)) _ i).symm
    · dsimp [splitPushoutHomotopyComponent, Arrow.cechConerve]
      simp only [← Category.assoc, WidePushout.head_desc]

theorem splitPushoutSelfMap_homotopic_identity
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] :
    Homotopic (splitPushoutSelfMap f s hs) (𝟙 f.cechConerve) := by
  exact homotopicOfHomotopy (splitPushoutDegreewiseHomotopy f s hs)

noncomputable def splitPushoutRetraction
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] :
    f.cechConerve ⟶ (CosimplicialObject.const C).obj f.left where
  app X := WidePushout.desc (𝟙 f.left) (fun _ => s) (fun _ => hs)
  naturality X Y g := by
    apply WidePushout.hom_ext (fun _ : Fin (X.len + 1) => f.hom)
    · intro i
      dsimp [Arrow.cechConerve]
      simp only [← Category.assoc, WidePushout.ι_desc]
      simp
    · dsimp [Arrow.cechConerve]
      simp only [← Category.assoc, WidePushout.head_desc]
      simp

theorem splitPushout_homotopy_equivalent_constant
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] :
    HomotopyEquivalent f.cechConerve
      ((CosimplicialObject.const C).obj f.left) := by
  let a := splitPushoutRetraction f s hs
  let b : (CosimplicialObject.const C).obj f.left ⟶ f.cechConerve :=
    f.augmentedCechConerve.hom
  refine ⟨a, b, ?_, ?_⟩
  · have hba : b ≫ a = 𝟙 ((CosimplicialObject.const C).obj f.left) := by
      ext X
      dsimp [a, b, splitPushoutRetraction]
      change WidePushout.head (fun _ : Fin (X.len + 1) => f.hom) ≫
        WidePushout.desc (𝟙 f.left) (fun _ => s) _ = 𝟙 f.left
      rw [WidePushout.head_desc]
    rw [hba]
    exact homotopic_refl _
  · have hab : a ≫ b = splitPushoutSelfMap f s hs := by
      ext X
      apply WidePushout.hom_ext (fun _ : Fin (X.len + 1) => f.hom)
      · intro i
        dsimp [a, b, splitPushoutRetraction]
        change WidePushout.ι (fun _ : Fin (X.len + 1) => f.hom) i ≫
          (WidePushout.desc (𝟙 f.left) (fun _ => s) _ ≫
            WidePushout.head (fun _ : Fin (X.len + 1) => f.hom)) = _
        rw [← Category.assoc, WidePushout.ι_desc]
        rw [splitPushoutSelfMap_ι]
        simpa [Category.assoc] using congrArg (fun k => s ≫ k)
          (WidePushout.arrow_ι (fun _ : Fin (X.len + 1) => f.hom) i).symm
      · dsimp [a, b, splitPushoutRetraction]
        change WidePushout.head (fun _ : Fin (X.len + 1) => f.hom) ≫
          (WidePushout.desc (𝟙 f.left) (fun _ => s) _ ≫
            WidePushout.head (fun _ : Fin (X.len + 1) => f.hom)) = _
        rw [← Category.assoc, WidePushout.head_desc]
        exact (Category.id_comp _).trans (splitPushoutSelfMap_head f s hs X).symm
    exact hab.symm ▸ splitPushoutSelfMap_homotopic_identity f s hs

/-! ## The cosimplicial Dold--Kan homotopy interfaces -/

/- The associated cochain complex only uses the preadditive structure.  The
   source's homotopy statements below retain its additive-category
   hypothesis. -/
def associatedCochainBoundaryAdditive
    {C : Type u} [Category.{v} C] [Preadditive C]
    (U : CosimplicialObject C) (n : ℕ) :
    U.obj ⦋n⦌ ⟶ U.obj ⦋n + 1⦌ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • U.δ i

theorem associatedCochainBoundaryAdditive_comp
    {C : Type u} [Category.{v} C] [Preadditive C]
    (U : CosimplicialObject C) (n : ℕ) :
    associatedCochainBoundaryAdditive U n ≫
        associatedCochainBoundaryAdditive U (n + 1) = 0 := by
  exact AlgebraicTopology.AlternatingCofaceMapComplex.d_squared U n

def associatedCochainComplexAdditive
    {C : Type u} [Category.{v} C] [Preadditive C]
    (U : CosimplicialObject C) : CochainComplex C ℕ :=
  CochainComplex.of
    (fun n => U.obj ⦋n⦌)
    (associatedCochainBoundaryAdditive U)
    (associatedCochainBoundaryAdditive_comp U)

theorem associatedCochainMapAdditive_comm
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel i j →
      f.app ⦋i⦌ ≫ (associatedCochainComplexAdditive V).d i j =
        (associatedCochainComplexAdditive U).d i j ≫ f.app ⦋j⦌ := by
  intro i j hij
  exact (AlgebraicTopology.AlternatingCofaceMapComplex.map f).comm i j

def associatedCochainMapAdditive
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    associatedCochainComplexAdditive U ⟶ associatedCochainComplexAdditive V :=
  { f := fun n => f.app ⦋n⦌
    comm' := associatedCochainMapAdditive_comm f }

private theorem unop_alt_complex_d
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (U : CosimplicialObject C) (n : ℕ) :
    ((HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).obj
      (op ((AlgebraicTopology.alternatingFaceMapComplex Cᵒᵖ).obj
        (oppositeCosimplicialObject U)))).d n (n + 1) =
      associatedCochainBoundaryAdditive U n := by
  change (((AlgebraicTopology.alternatingFaceMapComplex Cᵒᵖ).obj
    (oppositeCosimplicialObject U)).d (n + 1) n).unop = _
  simp only [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, unop_sum, unop_zsmul,
    associatedCochainBoundaryAdditive]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1

@[simp]
private theorem associatedCochainComplexAdditive_d
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (U : CosimplicialObject C) (n : ℕ) :
    (associatedCochainComplexAdditive U).d n (n + 1) =
      associatedCochainBoundaryAdditive U n := by
  exact CochainComplex.of_d (fun n => U.obj ⦋n⦌)
    (associatedCochainBoundaryAdditive U) n

private theorem associatedCochainMap_oneStep
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (K : DegreewiseHomotopy a b) :
    Nonempty (_root_.Homotopy
      (associatedCochainMapAdditive a)
      (associatedCochainMapAdditive b)) := by
  rcases (compareHomotopies (a := a) (b := b)).1 ⟨K⟩ with ⟨Kop⟩
  let H := degreewiseHomotopyToHomotopy Kop
  let hc := CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy H
  let hu := _root_.Homotopy.unop hc
  let AU := (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).obj
    (op ((AlgebraicTopology.alternatingFaceMapComplex Cᵒᵖ).obj
      (oppositeCosimplicialObject U)))
  let AV := (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).obj
    (op ((AlgebraicTopology.alternatingFaceMapComplex Cᵒᵖ).obj
      (oppositeCosimplicialObject V)))
  let au : AU ⟶ AV := (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
    (((AlgebraicTopology.alternatingFaceMapComplex Cᵒᵖ).map
      (oppositeCosimplicialMap a)).op)
  let bu : AU ⟶ AV := (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
    (((AlgebraicTopology.alternatingFaceMapComplex Cᵒᵖ).map
      (oppositeCosimplicialMap b)).op)
  let hu' : _root_.Homotopy au bu := hu
  let hh : ∀ i j, (associatedCochainComplexAdditive U).X i ⟶
      (associatedCochainComplexAdditive V).X j := fun i j ↦ hu'.hom i j
  refine ⟨{
    hom := hh
    zero := fun i j hij ↦ by
      dsimp [hh]
      exact hu'.zero i j hij
    comm := fun n ↦ ?_
  }⟩
  have hcomm := hu'.comm n
  cases n with
  | zero =>
      have hd := dNext_eq (c := (ComplexShape.down ℕ).symm)
        (C := AU) (D := AV) hu'.hom (i' := 1) (by rfl)
      have hp := prevD_eq_zero (c := (ComplexShape.down ℕ).symm)
        (C := AU) (D := AV) hu'.hom 0 (by
          simp [ComplexShape.prev])
      rw [hd, hp] at hcomm
      simp only [add_zero] at hcomm
      rw [unop_alt_complex_d] at hcomm
      have hd' := _root_.Homotopy.dNext_cochainComplex
        (P := associatedCochainComplexAdditive U)
        (Q := associatedCochainComplexAdditive V) hh 0
      have hp' := _root_.Homotopy.prevD_zero_cochainComplex
        (P := associatedCochainComplexAdditive U)
        (Q := associatedCochainComplexAdditive V) hh
      rw [hd', hp']
      simp only [add_zero]
      rw [associatedCochainComplexAdditive_d]
      convert hcomm using 1 <;> simp [hh, hu', hu, hc, H, au, bu, AU, AV,
        associatedCochainMapAdditive, associatedCochainComplexAdditive,
        HomologicalComplex.unopFunctor, HomologicalComplex.unop,
        oppositeCosimplicialMap, oppositeCosimplicialObject,
        Quiver.Hom.unop_op] <;> rfl
  | succ n =>
      have hd := dNext_eq (c := (ComplexShape.down ℕ).symm)
        (C := AU) (D := AV) hu'.hom (i' := n + 2) (by
          change n + 1 + 1 = n + 2
          omega)
      have hp := prevD_eq (c := (ComplexShape.down ℕ).symm)
        (C := AU) (D := AV) hu'.hom (j' := n) (by
          change n + 1 = n + 1
          rfl)
      rw [hd, hp] at hcomm
      rw [unop_alt_complex_d, unop_alt_complex_d] at hcomm
      have hd' := _root_.Homotopy.dNext_cochainComplex
        (P := associatedCochainComplexAdditive U)
        (Q := associatedCochainComplexAdditive V) hh (n + 1)
      have hp' := _root_.Homotopy.prevD_succ_cochainComplex
        (P := associatedCochainComplexAdditive U)
        (Q := associatedCochainComplexAdditive V) hh n
      rw [hd', hp']
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [associatedCochainComplexAdditive_d,
        associatedCochainComplexAdditive_d]
      convert hcomm using 1 <;> simp [hh, hu', hu, hc, H, au, bu, AU, AV,
        associatedCochainMapAdditive, associatedCochainComplexAdditive,
        HomologicalComplex.unopFunctor, HomologicalComplex.unop,
        oppositeCosimplicialMap, oppositeCosimplicialObject,
        Quiver.Hom.unop_op] <;> rfl

theorem associatedCochainMap_homotopic
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : Homotopic a b) :
    Nonempty (_root_.Homotopy
      (associatedCochainMapAdditive a)
      (associatedCochainMapAdditive b)) := by
  refine Relation.EqvGen.recOn H ?_ ?_ ?_ ?_
  · intro x y h
    rcases h with ⟨K⟩
    exact associatedCochainMap_oneStep K
  · intro x
    exact ⟨_root_.Homotopy.ofEq rfl⟩
  · intro x y h ih
    rcases ih with ⟨K⟩
    exact ⟨K.symm⟩
  · intro x y z hxy hyz ihxy ihyz
    rcases ihxy with ⟨Kxy⟩
    rcases ihyz with ⟨Kyz⟩
    exact ⟨Kxy.trans Kyz⟩

theorem normalizedCochainMap_homotopic
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : Homotopic a b) :
    Nonempty (_root_.Homotopy
      (normalizedCochainMap a) (normalizedCochainMap b)) := by
  letI : AdditiveCategory C :=
    { toPreadditive := inferInstance
      toHasFiniteProducts := inferInstance }
  rcases associatedCochainMap_homotopic H with ⟨K⟩
  rcases normalizedCochain_decomposition_exists (C := C) with ⟨D⟩
  rcases D.decomposition with ⟨e⟩
  let A := Formalization.Books.Simplicial.Unit24.cosimplicialAssociatedCochainFunctor C
  let Q := Formalization.Books.Simplicial.Unit24.normalizedCochainFunctor C
  let B := Formalization.Books.Simplicial.Unit24.cochainFunctorBiproduct D.degenerate Q
  let K0 : _root_.Homotopy (A.map a) (A.map b) := K
  let jU : Q.obj U ⟶ B.obj U := biprod.inr
  let qV : B.obj V ⟶ Q.obj V := biprod.snd
  let iU : Q.obj U ⟶ A.obj U := jU ≫ (e.app U).inv
  let pV : A.obj V ⟶ Q.obj V := (e.app V).hom ≫ qV
  let K' := (K0.compLeft iU).compRight pV
  have eq_map (f : U ⟶ V) :
      (iU ≫ A.map f) ≫ pV = normalizedCochainMap f := by
    calc
      _ = iU ≫ (A.map f ≫ (e.app V).hom) ≫ qV := by
        simp [pV, Category.assoc]
      _ = iU ≫ ((e.app U).hom ≫ B.map f) ≫ qV := by
        have hn : A.map f ≫ (e.app V).hom =
            (e.app U).hom ≫ B.map f := e.hom.naturality f
        rw [hn]
      _ = _ := by
        simp [iU, jU, qV, A, B, Q,
          Formalization.Books.Simplicial.Unit24.cochainFunctorBiproduct,
          Formalization.Books.Simplicial.Unit24.normalizedCochainFunctor,
          Category.assoc]
  exact ⟨(_root_.Homotopy.ofEq (eq_map a).symm).trans
    (K'.trans (_root_.Homotopy.ofEq (eq_map b)))⟩

private theorem associatedCochainMapAdditive_id
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (U : CosimplicialObject C) :
    associatedCochainMapAdditive (𝟙 U) =
      𝟙 (associatedCochainComplexAdditive U) := by
  ext n
  rfl

private theorem associatedCochainMapAdditive_comp
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V W : CosimplicialObject C} (f : U ⟶ V) (g : V ⟶ W) :
    associatedCochainMapAdditive (f ≫ g) =
      associatedCochainMapAdditive f ≫ associatedCochainMapAdditive g := by
  ext n
  rfl

theorem associatedCochainMap_homotopy_equivalence
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : CosimplicialObject C} (a : U ⟶ V)
    (H : IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℕ)
      (associatedCochainMapAdditive a) := by
  rcases H with ⟨b, hba, hab⟩
  rcases associatedCochainMap_homotopic hba with ⟨Kba⟩
  rcases associatedCochainMap_homotopic hab with ⟨Kab⟩
  let e : HomotopyEquiv (associatedCochainComplexAdditive U)
      (associatedCochainComplexAdditive V) :=
    { hom := associatedCochainMapAdditive a
      inv := associatedCochainMapAdditive b
      homotopyHomInvId := by
        simpa only [associatedCochainMapAdditive_comp,
          associatedCochainMapAdditive_id] using Kab
      homotopyInvHomId := by
        simpa only [associatedCochainMapAdditive_comp,
          associatedCochainMapAdditive_id] using Kba }
  exact e.homotopyEquivalences_hom

theorem normalizedCochainMap_homotopy_equivalence
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (a : U ⟶ V)
    (H : IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℕ)
      (normalizedCochainMap a) := by
  rcases H with ⟨b, hba, hab⟩
  rcases normalizedCochainMap_homotopic hba with ⟨Kba⟩
  rcases normalizedCochainMap_homotopic hab with ⟨Kab⟩
  let e : HomotopyEquiv (normalizedCochainComplex U)
      (normalizedCochainComplex V) :=
    { hom := normalizedCochainMap a
      inv := normalizedCochainMap b
      homotopyHomInvId := by
        simpa only [normalizedCochainMap_comp,
          normalizedCochainMap_id] using Kab
      homotopyInvHomId := by
        simpa only [normalizedCochainMap_comp,
          normalizedCochainMap_id] using Kba }
  exact e.homotopyEquivalences_hom

end Formalization.Books.Simplicial.Unit28
