import Formalization.Books.Simplicial.Unit14.HomFromSimplicialSetsIntoCosimplicialObjects
import Formalization.Books.Simplicial.Unit25.DoldKanForCosimplicialObjects
import Formalization.Books.Simplicial.Unit26.Homotopies
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Homology.Homotopy
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
      letI : Nonempty ((interval : SSet.{0}) _⦋n⦌) :=
        interval_degree_finite_nonempty n |>.2
      apply (intervalSimplex_bijective.{0} n).1
      rw [Function.leftInverse_invFun (intervalSimplex_bijective.{0} n).1]
    have hδ : ∀ {n : ℕ} (j : Fin (n + 2))
        (α : (interval : SSet.{0}) _⦋n + 1⦌),
        U.map (SimplexCategory.δ j) ≫ hh (n + 1) α =
          hh n ((interval : SSet.{0}).map (SimplexCategory.δ j).op α) ≫
            V.map (SimplexCategory.δ j) := by
      intro n j α
      letI : Nonempty ((interval : SSet.{0}) _⦋n + 1⦌) :=
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
      letI : Nonempty ((interval : SSet.{0}) _⦋n⦌) :=
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
                simpa using congrArg (fun g => g α)
                  (interval.map_id (op (SimplexCategory.mk n)))
              have hα' :
                  (interval : SSet.{0}).map (𝟙 (SimplexCategory.mk n)).op α = α := by
                simpa only [op_id] using hα
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

theorem homotopic_iff_opposite_homotopic
    {C : Type u} [Category.{v} C]
    {U V : CosimplicialObject C} {a b : U ⟶ V} :
    Homotopic a b ↔
      Formalization.Books.Simplicial.Unit26.Homotopic
        (oppositeCosimplicialMap a) (oppositeCosimplicialMap b) := by
  sorry

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
  sorry

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
    (F : C ⥤ Dᵒᵖ) (U : CosimplicialObject C) : SimplicialObject D where
  obj X := unop (F.obj (U.obj X.unop))
  map f := (F.map (U.map f.unop)).unop
  map_id X := by
    change
      (F.map (U.map (𝟙 X.unop))).unop =
        𝟙 (unop (F.obj (U.obj X.unop)))
    rw [U.map_id, F.map_id]
    rfl
  map_comp := by
    intro X Y Z f g
    change
      (F.map (U.map (g.unop ≫ f.unop))).unop =
        (F.map (U.map f.unop)).unop ≫
          (F.map (U.map g.unop)).unop
    rw [U.map_comp, F.map_comp, unop_comp]

def contravariantSimplicialMap
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {U V : CosimplicialObject C} (F : C ⥤ Dᵒᵖ) (a : U ⟶ V) :
    contravariantSimplicialObject F V ⟶ contravariantSimplicialObject F U where
  app X := (F.map (a.app X.unop)).unop
  naturality X Y f := by
    change
      (F.map (V.map f.unop)).unop ≫ (F.map (a.app Y.unop)).unop =
        (F.map (a.app X.unop)).unop ≫ (F.map (U.map f.unop)).unop
    have h := congrArg F.map (a.naturality f.unop)
    simpa only [Functor.map_comp, unop_comp] using
      congrArg (fun k => k.unop) h.symm

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
  sorry

theorem functorialContravariantCosimplicialHomotopy
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {U V : CosimplicialObject C} {a b : U ⟶ V} (H : Homotopic a b)
    (F : C ⥤ Dᵒᵖ) :
    Formalization.Books.Simplicial.Unit26.Homotopic
      (contravariantSimplicialMap F a)
      (contravariantSimplicialMap F b) := by
  sorry

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

theorem splitPushoutSelfMap_homotopic_identity
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] :
    Homotopic (splitPushoutSelfMap f s hs) (𝟙 f.cechConerve) := by
  sorry

theorem splitPushout_homotopy_equivalent_constant
    {C : Type u} [Category.{v} C] (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : f.hom ≫ s = 𝟙 f.left)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] :
    HomotopyEquivalent f.cechConerve
      ((CosimplicialObject.const C).obj f.left) := by
  sorry

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
  sorry

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
  sorry

def associatedCochainMapAdditive
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : CosimplicialObject C} (f : U ⟶ V) :
    associatedCochainComplexAdditive U ⟶ associatedCochainComplexAdditive V :=
  { f := fun n => f.app ⦋n⦌
    comm' := associatedCochainMapAdditive_comm f }

theorem associatedCochainMap_homotopic
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : Homotopic a b) :
    Nonempty (_root_.Homotopy
      (associatedCochainMapAdditive a)
      (associatedCochainMapAdditive b)) := by
  sorry

theorem normalizedCochainMap_homotopic
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : Homotopic a b) :
    Nonempty (_root_.Homotopy
      (normalizedCochainMap a) (normalizedCochainMap b)) := by
  sorry

theorem associatedCochainMap_homotopy_equivalence
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : CosimplicialObject C} (a : U ⟶ V)
    (H : IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℕ)
      (associatedCochainMapAdditive a) := by
  sorry

theorem normalizedCochainMap_homotopy_equivalence
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (a : U ⟶ V)
    (H : IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℕ)
      (normalizedCochainMap a) := by
  sorry

end Formalization.Books.Simplicial.Unit28
