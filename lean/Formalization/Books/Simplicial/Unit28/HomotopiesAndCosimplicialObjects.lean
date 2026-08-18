import Formalization.Books.Simplicial.Unit14.HomFromSimplicialSetsIntoCosimplicialObjects
import Formalization.Books.Simplicial.Unit25.DoldKanForCosimplicialObjects
import Formalization.Books.Simplicial.Unit26.Homotopies
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
  sorry

theorem degreewise_to_cylinderHomotopy
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) : Nonempty (CylinderHomotopy a b) := by
  sorry

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

theorem homotopicOfHomotopy
    {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
    {a b : U ⟶ V} (H : DegreewiseHomotopy a b) : Homotopic a b :=
  Relation.EqvGen.rel a b ⟨H⟩

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
  sorry

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
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
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
   source calls this the additive case; `HasFiniteBiproducts` is retained on
   the theorem interfaces below to match that terminology. -/
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
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
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
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    {U V : CosimplicialObject C} (a : U ⟶ V)
    (H : IsHomotopyEquivalence a) :
    Nonempty (_root_.HomotopyEquiv
      (associatedCochainComplexAdditive U)
      (associatedCochainComplexAdditive V)) := by
  sorry

theorem normalizedCochainMap_homotopy_equivalence
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : CosimplicialObject C} (a : U ⟶ V)
    (H : IsHomotopyEquivalence a) :
    Nonempty (_root_.HomotopyEquiv
      (normalizedCochainComplex U) (normalizedCochainComplex V)) := by
  sorry

end Formalization.Books.Simplicial.Unit28
