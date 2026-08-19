import Formalization.Books.Simplicial.Unit13.ProductsWithSimplicialSets
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne
import Mathlib.CategoryTheory.Quotient
import Mathlib.Logic.Relation

/-!
# Simplicial Methods, Chapter 26: Homotopies

The canonical combinatorial homotopy of `SimplicialObject` is Mathlib's
`SimplicialObject.Homotopy`.  This file records the source's cylinder
description, its degree-preserving component convention, the generated
homotopy relation, and the applications to Čech nerves and products.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit26

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite
open scoped _root_.Simplicial

universe v u v' u' w

/-! ## The simplicial interval and the cylinder description -/

/-- The `i`th `n`-simplex of `Δ[1]`, in the source's indexing. -/
def intervalSimplex (n : ℕ) (i : Fin (n + 2)) :
    (Δ[1] : SSet.{u}) _⦋n⦌ :=
  SSet.stdSimplex.objMk₁ i

theorem intervalSimplex_bijective (n : ℕ) :
    Function.Bijective (intervalSimplex n) := by
  exact SSet.stdSimplex.objMk₁_bijective

theorem interval_degree_finite_nonempty (n : ℕ) :
    Finite ((Δ[1] : SSet.{u}) _⦋n⦌) ∧
      Nonempty ((Δ[1] : SSet.{u}) _⦋n⦌) :=
  Unit13.standardSimplex_finite_nonempty 1 n

theorem intervalSimplex_apply (n : ℕ) (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    intervalSimplex n i j = if j.castSucc < i then 0 else 1 := by
  rfl

theorem intervalSimplex_zero_is_constant_one (n : ℕ) :
    ∀ j : Fin (n + 1), intervalSimplex n 0 j = 1 := by
  intro j
  simp [intervalSimplex, SSet.stdSimplex.objMk₁_apply]

theorem intervalSimplex_last_is_constant_zero (n : ℕ) :
    ∀ j : Fin (n + 1), intervalSimplex n (Fin.last (n + 1)) j = 0 := by
  intro j
  simp [intervalSimplex, SSet.stdSimplex.objMk₁_apply]

theorem pointSimplex_subsingleton (n : ℕ) :
    Subsingleton ((Δ[0] : SSet.{u}) _⦋n⦌) := by
  constructor
  intro x y
  apply SSet.stdSimplex.objEquiv.injective
  exact Subsingleton.elim _ _

theorem pointSimplex_finite_nonempty (n : ℕ) :
    Finite ((Δ[0] : SSet.{u}) _⦋n⦌) ∧
      Nonempty ((Δ[0] : SSet.{u}) _⦋n⦌) :=
  Unit13.standardSimplex_finite_nonempty 0 n

/-- The two vertex inclusions `Δ[0] ⟶ Δ[1]`. -/
noncomputable def intervalVertex (ε : Fin 2) :
    (Δ[0] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) :=
  SSet.const (SSet.stdSimplex.obj₀Equiv.symm ε)

/-- The coproducts used to form `U × Δ[1]` degree by degree. -/
theorem intervalCoproducts
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) :
    Unit13.HasDegreewiseCoproducts (Δ[1] : SSet.{u}) U :=
  fun n => Unit13.degreewiseCoproductInstance (Δ[1] : SSet.{u}) U
    (Unit13.standardSimplex_finite_nonempty 1) n

/-- The source's product `U × Δ[1]`, using the established coproduct-based
product with a simplicial set. -/
noncomputable def intervalCylinder
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) : SimplicialObject C :=
  Unit13.simplicialSetProductOf (Δ[1] : SSet.{u}) U
    (intervalCoproducts U)

/-! The degenerate interval `Δ[0]` gives back the original simplicial object,
up to the canonical chosen-product isomorphism. -/

theorem pointCoproducts
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) :
    Unit13.HasDegreewiseCoproducts (Δ[0] : SSet.{u}) U :=
  fun n => Unit13.degreewiseCoproductInstance (Δ[0] : SSet.{u}) U
    (Unit13.standardSimplex_finite_nonempty 0) n

noncomputable def pointCylinder
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) : SimplicialObject C :=
  Unit13.simplicialSetProductOf (Δ[0] : SSet.{u}) U (pointCoproducts U)

theorem pointCylinder_iso
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) : Nonempty (pointCylinder U ≅ U) := by
  let α : pointCylinder U ⟶ U := {
    app := fun X =>
      let _ : HasCoproduct
          (fun _ : (Δ[0] : SSet.{u}).obj X => U.obj X) :=
        Unit13.degreewiseCoproductInstanceAt (pointCoproducts U) X
      Sigma.desc (fun _ => 𝟙 (U.obj X))
    naturality := by
      intro X Y f
      let _ : HasCoproduct
          (fun _ : (Δ[0] : SSet.{u}).obj X => U.obj X) :=
        Unit13.degreewiseCoproductInstanceAt (pointCoproducts U) X
      let _ : HasCoproduct
          (fun _ : (Δ[0] : SSet.{u}).obj Y => U.obj Y) :=
        Unit13.degreewiseCoproductInstanceAt (pointCoproducts U) Y
      change
        Sigma.desc (fun z =>
            U.map f ≫ Sigma.ι (fun _ : (Δ[0] : SSet.{u}).obj Y => U.obj Y)
              ((Δ[0] : SSet.{u}).map f z)) ≫
          Sigma.desc (fun _ => 𝟙 (U.obj Y)) =
        Sigma.desc (fun _ => 𝟙 (U.obj X)) ≫ U.map f
      apply Sigma.hom_ext
      intro z
      simp }
  let β : U ⟶ pointCylinder U := {
    app := fun X =>
      let _ : HasCoproduct
          (fun _ : (Δ[0] : SSet.{u}).obj X => U.obj X) :=
        Unit13.degreewiseCoproductInstanceAt (pointCoproducts U) X
      Sigma.ι (fun _ : (Δ[0] : SSet.{u}).obj X => U.obj X)
        (SSet.stdSimplex.const 0 0 X)
    naturality := by
      intro X Y f
      let _ : HasCoproduct
          (fun _ : (Δ[0] : SSet.{u}).obj X => U.obj X) :=
        Unit13.degreewiseCoproductInstanceAt (pointCoproducts U) X
      let _ : HasCoproduct
          (fun _ : (Δ[0] : SSet.{u}).obj Y => U.obj Y) :=
        Unit13.degreewiseCoproductInstanceAt (pointCoproducts U) Y
      change
        U.map f ≫ Sigma.ι (fun _ : (Δ[0] : SSet.{u}).obj Y => U.obj Y)
            (SSet.stdSimplex.const 0 0 Y) =
          Sigma.ι (fun _ : (Δ[0] : SSet.{u}).obj X => U.obj X)
            (SSet.stdSimplex.const 0 0 X) ≫
          Sigma.desc (fun z =>
            U.map f ≫ Sigma.ι (fun _ : (Δ[0] : SSet.{u}).obj Y => U.obj Y)
              ((Δ[0] : SSet.{u}).map f z))
      have hc :
          (Δ[0] : SSet.{u}).map f (SSet.stdSimplex.const 0 0 X) =
            SSet.stdSimplex.const 0 0 Y := by
        apply SSet.stdSimplex.objEquiv.injective
        apply SimplexCategory.Hom.ext
        rfl
      rw [Sigma.ι_desc, hc] }
  refine ⟨{ hom := α, inv := β, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply NatTrans.ext
    funext X
    let _ : HasCoproduct
        (fun _ : (Δ[0] : SSet.{u}).obj X => U.obj X) :=
      Unit13.degreewiseCoproductInstanceAt (pointCoproducts U) X
    let _ : Subsingleton ((Δ[0] : SSet.{u}).obj X) := by
      simpa only [SimplexCategory.mk_len] using pointSimplex_subsingleton X.unop.len
    change
      Sigma.desc (fun _ => 𝟙 (U.obj X)) ≫
          Sigma.ι (fun _ : (Δ[0] : SSet.{u}).obj X => U.obj X)
            (SSet.stdSimplex.const 0 0 X) = 𝟙 _
    apply Sigma.hom_ext
    intro z
    have hz : z = SSet.stdSimplex.const 0 0 X := Subsingleton.elim _ _
    subst z
    simp
  · apply NatTrans.ext
    funext X
    let _ : HasCoproduct
        (fun _ : (Δ[0] : SSet.{u}).obj X => U.obj X) :=
      Unit13.degreewiseCoproductInstanceAt (pointCoproducts U) X
    change
      Sigma.ι (fun _ : (Δ[0] : SSet.{u}).obj X => U.obj X)
          (SSet.stdSimplex.const 0 0 X) ≫
        Sigma.desc (fun _ => 𝟙 (U.obj X)) = 𝟙 (U.obj X)
    simp

noncomputable def pointCylinderIso
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) : pointCylinder U ≅ U :=
  (pointCylinder_iso U).some

/-- The endpoint inclusion at the vertex `ε` of `Δ[1]`. -/
noncomputable def intervalEndpoint
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) (ε : Fin 2) :
    U ⟶ intervalCylinder U where
  app X :=
    let _ : HasCoproduct (fun _ : (Δ[1] : SSet.{u}).obj X => U.obj X) :=
      Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U) X
    Sigma.ι (fun _ : (Δ[1] : SSet.{u}).obj X => U.obj X)
      (SSet.stdSimplex.const 1 ε X)
  naturality := by
    intro X Y f
    let _ : HasCoproduct (fun _ : (Δ[1] : SSet.{u}).obj X => U.obj X) :=
      Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U) X
    let _ : HasCoproduct (fun _ : (Δ[1] : SSet.{u}).obj Y => U.obj Y) :=
      Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U) Y
    change
      U.map f ≫ Sigma.ι (fun _ : (Δ[1] : SSet.{u}).obj Y => U.obj Y)
        (SSet.stdSimplex.const 1 ε Y) =
      Sigma.ι (fun _ : (Δ[1] : SSet.{u}).obj X => U.obj X)
          (SSet.stdSimplex.const 1 ε X) ≫
        Sigma.desc (fun z =>
            U.map f ≫ Sigma.ι (fun _ : (Δ[1] : SSet.{u}).obj Y => U.obj Y)
            ((Δ[1] : SSet.{u}).map f z))
    have hε :
        (Δ[1] : SSet.{u}).map f (SSet.stdSimplex.const 1 ε X) =
          SSet.stdSimplex.const 1 ε Y := by
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      rfl
    simp [hε]

/-- The two endpoint maps used in the source. -/
noncomputable def homotopyE₀
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) : U ⟶ intervalCylinder U :=
  intervalEndpoint U 0

noncomputable def homotopyE₁
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) : U ⟶ intervalCylinder U :=
  intervalEndpoint U 1

/-- The projection `U × Δ[1] → U`, which is the canonical map back to `U`. -/
noncomputable def intervalProjection
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) : intervalCylinder U ⟶ U :=
  Unit13.productWithSimplicialSetTo (intervalCoproducts U)

structure CylinderHomotopy
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SimplicialObject C} (a b : U ⟶ V) where
  /-- The map out of the cylinder. -/
  h : intervalCylinder U ⟶ V
  h₀ : homotopyE₀ U ≫ h = a
  h₁ : homotopyE₁ U ≫ h = b

/-- The component of a cylinder map on the simplex `αᵢⁿ`. -/
noncomputable def cylinderHomotopyComponent
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : CylinderHomotopy a b) (n : ℕ) (i : Fin (n + 2)) :
    U.obj (op (SimplexCategory.mk n)) ⟶
      V.obj (op (SimplexCategory.mk n)) :=
  let _ : HasCoproduct
      (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj (op (SimplexCategory.mk n))) :=
    Unit13.degreewiseCoproductInstance (Δ[1] : SSet.{u}) U
      (Unit13.standardSimplex_finite_nonempty 1) n
  Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
      U.obj (op (SimplexCategory.mk n))) (intervalSimplex n i) ≫
    H.h.app (op (SimplexCategory.mk n))

/-- The degree-preserving component convention used in the source. -/
/- This is the source's degree-preserving convention for a homotopy.  It is
category-independent, unlike the cylinder presentation above. -/
structure DegreewiseHomotopy
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} (a b : U ⟶ V) where
  h (n : ℕ) (i : Fin (n + 2)) :
    U.obj (op (SimplexCategory.mk n)) ⟶
      V.obj (op (SimplexCategory.mk n))
  h_zero (n : ℕ) : h n 0 = b.app (op (SimplexCategory.mk n))
  h_last (n : ℕ) : h n (Fin.last (n + 1)) = a.app (op (SimplexCategory.mk n))
  face_of_gt {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
      (hji : j.castSucc < i) :
    h (n + 1) i ≫ V.δ j =
      U.δ j ≫ h n (i.pred (Fin.ne_zero_of_lt hji))
  face_of_le {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
      (hij : i ≤ j.castSucc) :
    h (n + 1) i ≫ V.δ j =
      U.δ j ≫ h n
        (i.castPred (Fin.ne_last_of_lt
          (lt_of_le_of_lt hij j.castSucc_lt_succ)))
  degeneracy_of_gt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
      (hji : j.castSucc < i) :
    h n i ≫ V.σ j = U.σ j ≫ h (n + 1) i.succ
  degeneracy_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
      (hij : i ≤ j.castSucc) :
    h n i ≫ V.σ j = U.σ j ≫ h (n + 1) i.castSucc

def mapDegreewiseHomotopy
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) (F : C ⥤ D) :
    DegreewiseHomotopy
      (((SimplicialObject.whiskering C D).obj F).map a)
      (((SimplicialObject.whiskering C D).obj F).map b) where
  h n i := F.map (H.h n i)
  h_zero n := by
    change F.map (H.h n 0) = F.map (b.app (op (SimplexCategory.mk n)))
    exact congrArg F.map (H.h_zero n)
  h_last n := by
    change F.map (H.h n (Fin.last (n + 1))) =
      F.map (a.app (op (SimplexCategory.mk n)))
    exact congrArg F.map (H.h_last n)
  face_of_gt i j hji := by
    change F.map (H.h _ i) ≫ F.map (V.δ j) =
      F.map (U.δ j) ≫ F.map (H.h _ _)
    simpa only [Functor.map_comp] using
      congrArg F.map (H.face_of_gt i j hji)
  face_of_le i j hij := by
    change F.map (H.h _ i) ≫ F.map (V.δ j) =
      F.map (U.δ j) ≫ F.map (H.h _ _)
    simpa only [Functor.map_comp] using
      congrArg F.map (H.face_of_le i j hij)
  degeneracy_of_gt i j hji := by
    change F.map (H.h _ i) ≫ F.map (V.σ j) =
      F.map (U.σ j) ≫ F.map (H.h _ _)
    simpa only [Functor.map_comp] using
      congrArg F.map (H.degeneracy_of_gt i j hji)
  degeneracy_of_le i j hij := by
    change F.map (H.h _ i) ≫ F.map (V.σ j) =
      F.map (U.σ j) ≫ F.map (H.h _ _)
    simpa only [Functor.map_comp] using
      congrArg F.map (H.degeneracy_of_le i j hij)

theorem cylinderHomotopyComponent_zero
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : CylinderHomotopy a b) (n : ℕ) :
    cylinderHomotopyComponent H n 0 = b.app (op (SimplexCategory.mk n)) := by
  let _ : HasCoproduct
      (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj (op (SimplexCategory.mk n))) :=
    Unit13.degreewiseCoproductInstance (Δ[1] : SSet.{u}) U
      (Unit13.standardSimplex_finite_nonempty 1) n
  change Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
      U.obj (op (SimplexCategory.mk n))) (intervalSimplex n 0) ≫
    H.h.app (op (SimplexCategory.mk n)) = _
  have hindex :
      intervalSimplex n 0 =
        SSet.stdSimplex.const 1 1 (op (SimplexCategory.mk n)) := by
    apply SSet.stdSimplex.objEquiv.injective
    ext j
    simp [intervalSimplex, SSet.stdSimplex.objMk₁_apply,
      SSet.stdSimplex.objEquiv_toOrderHom_apply, SSet.stdSimplex.const]
  rw [hindex]
  have h := congrArg (fun k => k.app (op (SimplexCategory.mk n))) H.h₁
  change
      Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj (op (SimplexCategory.mk n)))
        (SSet.stdSimplex.const 1 1 (op (SimplexCategory.mk n))) ≫
        H.h.app (op (SimplexCategory.mk n)) = _ at h
  exact h

theorem cylinderHomotopyComponent_last
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : CylinderHomotopy a b) (n : ℕ) :
    cylinderHomotopyComponent H n (Fin.last (n + 1)) =
      a.app (op (SimplexCategory.mk n)) := by
  let _ : HasCoproduct
      (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj (op (SimplexCategory.mk n))) :=
    Unit13.degreewiseCoproductInstance (Δ[1] : SSet.{u}) U
      (Unit13.standardSimplex_finite_nonempty 1) n
  change Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
      U.obj (op (SimplexCategory.mk n))) (intervalSimplex n (Fin.last (n + 1))) ≫
    H.h.app (op (SimplexCategory.mk n)) = _
  have hindex :
      intervalSimplex n (Fin.last (n + 1)) =
        SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n)) := by
    apply SSet.stdSimplex.objEquiv.injective
    ext j
    simp [intervalSimplex, SSet.stdSimplex.objMk₁_apply,
      SSet.stdSimplex.objEquiv_toOrderHom_apply, SSet.stdSimplex.const]
  rw [hindex]
  have h := congrArg (fun k => k.app (op (SimplexCategory.mk n))) H.h₀
  change
      Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj (op (SimplexCategory.mk n)))
        (SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n))) ≫
        H.h.app (op (SimplexCategory.mk n)) = _ at h
  exact h

theorem exists_cylinderHomotopy_to_degreewise
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : CylinderHomotopy a b) :
    Nonempty (DegreewiseHomotopy a b) := by
  have component_naturality :
      ∀ {m n} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
        (i : Fin (n + 2)) (k : Fin (m + 2)),
        (Δ[1] : SSet.{u}).map f.op (intervalSimplex n i) =
          intervalSimplex m k →
        U.map f.op ≫ cylinderHomotopyComponent H m k =
          cylinderHomotopyComponent H n i ≫ V.map f.op := by
    intro m n f i k hk
    let _ : HasCoproduct
        (fun _ : (Δ[1] : SSet.{u}) _⦋m⦌ =>
          U.obj (op (SimplexCategory.mk m))) :=
      Unit13.degreewiseCoproductInstance (Δ[1] : SSet.{u}) U
        (Unit13.standardSimplex_finite_nonempty 1) m
    let _ : HasCoproduct
        (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
          U.obj (op (SimplexCategory.mk n))) :=
      Unit13.degreewiseCoproductInstance (Δ[1] : SSet.{u}) U
        (Unit13.standardSimplex_finite_nonempty 1) n
    have hn := congrArg
      (fun q =>
        Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
            U.obj (op (SimplexCategory.mk n))) (intervalSimplex n i) ≫ q)
      (H.h.naturality f.op)
    dsimp [intervalCylinder, Unit13.simplicialSetProductOf] at hn
    rw [← Category.assoc, Sigma.ι_desc, hk] at hn
    dsimp [cylinderHomotopyComponent]
    calc
      U.map f.op ≫ Sigma.ι
          (fun _ : (Δ[1] : SSet.{u}) _⦋m⦌ =>
            U.obj (op (SimplexCategory.mk m))) (intervalSimplex m k) ≫
          H.h.app (op (SimplexCategory.mk m)) =
        (U.map f.op ≫ Sigma.ι
          (fun _ : (Δ[1] : SSet.{u}) _⦋m⦌ =>
            U.obj (op (SimplexCategory.mk m))) (intervalSimplex m k)) ≫
          H.h.app (op (SimplexCategory.mk m)) := (Category.assoc _ _ _).symm
      _ = Sigma.ι
          (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
            U.obj (op (SimplexCategory.mk n))) (intervalSimplex n i) ≫
          H.h.app (op (SimplexCategory.mk n)) ≫ V.map f.op := hn
      _ = (Sigma.ι
          (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
            U.obj (op (SimplexCategory.mk n))) (intervalSimplex n i) ≫
          H.h.app (op (SimplexCategory.mk n))) ≫ V.map f.op :=
        (Category.assoc _ _ _).symm
  have face_gt_map :
      ∀ {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
        (hji : j.castSucc < i),
        (Δ[1] : SSet.{u}).map (SimplexCategory.δ j).op
            (intervalSimplex (n + 1) i) =
          intervalSimplex n (i.pred (Fin.ne_zero_of_lt hji)) := by
    intro n i j hji
    simpa only [intervalSimplex, SimplicialObject.δ] using
      SSet.stdSimplex.δ_objMk₁_of_lt i j hji
  have face_le_map :
      ∀ {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
        (hij : i ≤ j.castSucc),
        (Δ[1] : SSet.{u}).map (SimplexCategory.δ j).op
            (intervalSimplex (n + 1) i) =
          intervalSimplex n (i.castPred (Fin.ne_last_of_lt
            (lt_of_le_of_lt hij j.castSucc_lt_succ))) := by
    intro n i j hij
    simpa only [intervalSimplex, SimplicialObject.δ] using
      SSet.stdSimplex.δ_objMk₁_of_le i j hij
  have degeneracy_gt_map :
      ∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
        (hji : j.castSucc < i),
        (Δ[1] : SSet.{u}).map (SimplexCategory.σ j).op
            (intervalSimplex n i) =
          intervalSimplex (n + 1) i.succ := by
    intro n i j hji
    simpa only [intervalSimplex, SimplicialObject.σ] using
      SSet.stdSimplex.σ_objMk₁_of_lt i j hji
  have degeneracy_le_map :
      ∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
        (hij : i ≤ j.castSucc),
        (Δ[1] : SSet.{u}).map (SimplexCategory.σ j).op
            (intervalSimplex n i) =
          intervalSimplex (n + 1) i.castSucc := by
    intro n i j hij
    simpa only [intervalSimplex, SimplicialObject.σ] using
      SSet.stdSimplex.σ_objMk₁_of_le i j hij
  refine ⟨{
    h := fun n i => cylinderHomotopyComponent H n i
    h_zero := fun n => cylinderHomotopyComponent_zero H n
    h_last := fun n => cylinderHomotopyComponent_last H n
    face_of_gt := by
      intro n i j hji
      simpa only [SimplicialObject.δ] using
        (component_naturality (SimplexCategory.δ j) i
          (i.pred (Fin.ne_zero_of_lt hji)) (face_gt_map i j hji)).symm
    face_of_le := by
      intro n i j hij
      simpa only [SimplicialObject.δ] using
        (component_naturality (SimplexCategory.δ j) i
          (i.castPred (Fin.ne_last_of_lt
            (lt_of_le_of_lt hij j.castSucc_lt_succ)))
          (face_le_map i j hij)).symm
    degeneracy_of_gt := by
      intro n i j hji
      simpa only [SimplicialObject.σ] using
        (component_naturality (SimplexCategory.σ j) i i.succ
          (degeneracy_gt_map i j hji)).symm
    degeneracy_of_le := by
      intro n i j hij
      simpa only [SimplicialObject.σ] using
        (component_naturality (SimplexCategory.σ j) i i.castSucc
          (degeneracy_le_map i j hij)).symm
  }⟩

noncomputable def cylinderHomotopy_to_degreewise
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : CylinderHomotopy a b) : DegreewiseHomotopy a b :=
  (exists_cylinderHomotopy_to_degreewise H).some

theorem degreewiseHomotopy_to_cylinder
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) :
    Nonempty (CylinderHomotopy a b) := by
  sorry

theorem cylinderHomotopy_iff_degreewise
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SimplicialObject C} {a b : U ⟶ V} :
    Nonempty (CylinderHomotopy a b) ↔ Nonempty (DegreewiseHomotopy a b) := by
  constructor
  · rintro ⟨H⟩
    exact exists_cylinderHomotopy_to_degreewise H
  · rintro ⟨H⟩
    exact degreewiseHomotopy_to_cylinder H

/-! ## The canonical homotopy relation and its generated category -/

/-- Mathlib's canonical combinatorial homotopy, reused as the chapter's
category-independent notion. -/
abbrev Homotopy
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} (a b : U ⟶ V) :=
  SimplicialObject.Homotopy a b

/-- The one-step homotopy relation. -/
def OneStepHomotopy
    {C : Type u} [Category.{v} C] {U V : SimplicialObject C}
    (a b : U ⟶ V) : Prop :=
  Nonempty (Homotopy a b)

/-- The equivalence relation generated by one-step simplicial homotopies. -/
def Homotopic
    {C : Type u} [Category.{v} C] {U V : SimplicialObject C}
    (a b : U ⟶ V) : Prop :=
  Relation.EqvGen (fun a b : U ⟶ V => OneStepHomotopy a b) a b

theorem homotopicOfHomotopy
    {C : Type u} [Category.{v} C] {U V : SimplicialObject C}
    {a b : U ⟶ V} (H : Homotopy a b) : Homotopic a b :=
  Relation.EqvGen.rel a b ⟨H⟩

theorem homotopic_is_equivalence
    {C : Type u} [Category.{v} C] (U V : SimplicialObject C) :
    Equivalence (fun a b : U ⟶ V => Homotopic a b) := by
  exact Relation.EqvGen.is_equivalence _

theorem homotopic_refl
    {C : Type u} [Category.{v} C] {U V : SimplicialObject C}
  (a : U ⟶ V) : Homotopic a a := by
  exact Relation.EqvGen.refl a

theorem homotopic_symm
    {C : Type u} [Category.{v} C] {U V : SimplicialObject C}
    {a b : U ⟶ V} (h : Homotopic a b) : Homotopic b a := by
  exact (homotopic_is_equivalence U V).symm h

theorem homotopic_trans
    {C : Type u} [Category.{v} C] {U V : SimplicialObject C}
    {a b c : U ⟶ V} (hab : Homotopic a b) (hbc : Homotopic b c) :
    Homotopic a c := by
  exact (homotopic_is_equivalence U V).trans hab hbc

theorem homotopicOfEq
    {C : Type u} [Category.{v} C] {U V : SimplicialObject C}
    {a b : U ⟶ V} (h : a = b) : Homotopic a b := by
  subst b
  exact Relation.EqvGen.refl a

/-- The canonical homotopy from a map to itself. -/
def trivialHomotopy
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} (a : U ⟶ V) : Homotopy a a :=
  SimplicialObject.Homotopy.refl a

theorem trivialOneStepHomotopy
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} (a : U ⟶ V) :
    OneStepHomotopy a a := by
  exact ⟨trivialHomotopy a⟩

theorem homotopy_iff_degreewise
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SimplicialObject C} {a b : U ⟶ V} :
    Nonempty (CylinderHomotopy a b) ↔ OneStepHomotopy a b := by
  rw [cylinderHomotopy_iff_degreewise]
  sorry

theorem trivialCylinderHomotopy
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {U V : SimplicialObject C} (a : U ⟶ V) :
    Nonempty (CylinderHomotopy a a) := by
  exact (homotopy_iff_degreewise).2 (trivialOneStepHomotopy a)

noncomputable def trivialDegreewiseHomotopy
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} (a : U ⟶ V) :
    DegreewiseHomotopy a a where
  h := fun n _ => a.app (op (SimplexCategory.mk n))
  h_zero := by
    intro n
    rfl
  h_last := by
    intro n
    rfl
  face_of_gt := by
    intro n i j hji
    simp
  face_of_le := by
    intro n i j hij
    simp
  degeneracy_of_gt := by
    intro n i j hji
    simp
  degeneracy_of_le := by
    intro n i j hij
    simp

def homotopyHomRel (C : Type u) [Category.{v} C] :
    HomRel (SimplicialObject C) :=
  fun _ _ a b => Homotopic a b

abbrev HomotopyCategory (C : Type u) [Category.{v} C] :=
  CategoryTheory.Quotient (homotopyHomRel C)

def homotopyCategoryFunctor (C : Type u) [Category.{v} C] :
    SimplicialObject C ⥤ HomotopyCategory C :=
  CategoryTheory.Quotient.functor (homotopyHomRel C)

theorem homotopyHomRel_congruence
    (C : Type u) [Category.{v} C] :
    CategoryTheory.Congruence (homotopyHomRel C) := by
  sorry

theorem homotopyCategoryFunctor_full
    (C : Type u) [Category.{v} C] :
    (homotopyCategoryFunctor C).Full := by
  simpa [homotopyCategoryFunctor] using
    (inferInstance : (CategoryTheory.Quotient.functor (homotopyHomRel C)).Full)

theorem homotopyCategoryFunctor_essentially_surjective
    (C : Type u) [Category.{v} C] :
    (homotopyCategoryFunctor C).EssSurj := by
  simpa [homotopyCategoryFunctor] using
    (inferInstance :
      (CategoryTheory.Quotient.functor (homotopyHomRel C)).EssSurj)

/-! ## Functoriality and homotopy equivalences -/

def mapHomotopy
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopy a b) (F : C ⥤ D) :
    Homotopy
      (((SimplicialObject.whiskering C D).obj F).map a)
      (((SimplicialObject.whiskering C D).obj F).map b) :=
  H.whiskerRight F

theorem map_homotopic
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopic a b) (F : C ⥤ D) :
    Homotopic
      (((SimplicialObject.whiskering C D).obj F).map a)
      (((SimplicialObject.whiskering C D).obj F).map b) := by
  sorry

def postcomposeHomotopy
    {C : Type u} [Category.{v} C]
    {U V W : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopy a b) (q : V ⟶ W) :
    Homotopy (a ≫ q) (b ≫ q) :=
  H.postcomp q

def precomposeHomotopy
    {C : Type u} [Category.{v} C]
    {U V X : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopy a b) (p : X ⟶ U) :
    Homotopy (p ≫ a) (p ≫ b) :=
  H.precomp p

theorem postcompose_homotopic
    {C : Type u} [Category.{v} C]
    {U V W : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopic a b) (q : V ⟶ W) :
    Homotopic (a ≫ q) (b ≫ q) := by
  sorry

theorem precompose_homotopic
    {C : Type u} [Category.{v} C]
    {U V X : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopic a b) (p : X ⟶ U) :
    Homotopic (p ≫ a) (p ≫ b) := by
  sorry

def IsHomotopyEquivalence
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} (a : U ⟶ V) : Prop :=
  ∃ b : V ⟶ U,
    Homotopic (b ≫ a) (𝟙 V) ∧ Homotopic (a ≫ b) (𝟙 U)

def HomotopyEquivalent
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) : Prop :=
  ∃ a : U ⟶ V, IsHomotopyEquivalence a

/-! ## The standard simplex and the cylinder -/

noncomputable def simplexToPoint (m : ℕ) :
    (Δ[m] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.from _

noncomputable def pointToSimplexLast (m : ℕ) :
    (Δ[0] : SSet.{u}) ⟶ (Δ[m] : SSet.{u}) :=
  SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))

noncomputable def pointToSimplexFirst (m : ℕ) :
    (Δ[0] : SSet.{u}) ⟶ (Δ[m] : SSet.{u}) :=
  SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)

theorem pointToSimplexLast_comp_simplexToPoint (m : ℕ) :
    pointToSimplexLast m ≫ simplexToPoint m = 𝟙 (Δ[0] : SSet.{u}) := by
  apply SSet.stdSimplex.ext₀

theorem simplexMaxHomotopy_exists (m : ℕ) :
    ∃ H : SSet.Homotopy (𝟙 (Δ[m] : SSet.{u}))
        (simplexToPoint m ≫ pointToSimplexLast m),
      ∀ (n : ℕ) (φ : (Δ[m] : SSet.{u}) _⦋n⦌)
        (α : (Δ[1] : SSet.{u}) _⦋n⦌) (k : Fin (n + 1)),
        H.h.app (op (SimplexCategory.mk n)) (φ, α) k =
          if α k = 0 then φ k else Fin.last m := by
  sorry

theorem simplexFirstHomotopy_exists (m : ℕ) :
    Nonempty
      (SSet.Homotopy (simplexToPoint m ≫ pointToSimplexFirst m)
        (𝟙 (Δ[m] : SSet.{u}))) := by
  sorry

theorem simplex_homotopy_equivalent_point (m : ℕ) :
    HomotopyEquivalent (Δ[m] : SSet.{u}) (Δ[0] : SSet.{u}) := by
  sorry

/-! ## The cylinder is homotopy equivalent to its base -/

theorem intervalMaxMap_exists :
    ∃ μ : ((Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ⟶
        (Δ[1] : SSet.{u}),
      ∀ (n : ℕ) (β₁ β₂ : (Δ[1] : SSet.{u}) _⦋n⦌),
        μ.app (op (SimplexCategory.mk n)) (β₁, β₂) =
          fun k => max (β₁ k) (β₂ k) := by
  sorry

theorem intervalMinMap_exists :
    ∃ μ : ((Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ⟶
        (Δ[1] : SSet.{u}),
      ∀ (n : ℕ) (β₁ β₂ : (Δ[1] : SSet.{u}) _⦋n⦌),
        μ.app (op (SimplexCategory.mk n)) (β₁, β₂) =
          fun k => min (β₁ k) (β₂ k) := by
  sorry

theorem intervalProjection_comp_endpoint
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) :
    intervalEndpoint U 0 ≫ intervalProjection U = 𝟙 U ∧
      intervalEndpoint U 1 ≫ intervalProjection U = 𝟙 U := by
  sorry

theorem intervalCylinder_id_homotopic_endpoint_zero
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) :
    Homotopic (𝟙 (intervalCylinder U))
      (intervalProjection U ≫ intervalEndpoint U 0) := by
  sorry

theorem intervalCylinder_id_homotopic_endpoint_one
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) :
    Homotopic (𝟙 (intervalCylinder U))
      (intervalProjection U ≫ intervalEndpoint U 1) := by
  sorry

theorem intervalCylinder_homotopy_equivalent
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) :
    HomotopyEquivalent (intervalCylinder U) U := by
  refine ⟨intervalProjection U, ?_⟩
  refine ⟨intervalEndpoint U 0, ?_, ?_⟩
  · exact homotopicOfEq (intervalProjection_comp_endpoint U).1
  · exact Relation.EqvGen.symm _ _
      (intervalCylinder_id_homotopic_endpoint_zero U)

/-! ## Čech nerves of split epimorphisms -/

def splitEpiOfSection
    {C : Type u} [Category.{v} C] {Y X : C}
    (f : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ f = 𝟙 X) : SplitEpi f where
  section_ := s
  id := hs

def cechNerveSectionArrowHom
    {C : Type u} [Category.{v} C] (f : Arrow C)
    (s : f.right ⟶ f.left) (hs : s ≫ f.hom = 𝟙 f.right) : f ⟶ f :=
  Arrow.homMk (f.hom ≫ s) (𝟙 f.right) (by
    simp [Category.assoc, hs])

noncomputable def cechNerveSelfMap
    {C : Type u} [Category.{v} C]
    (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : s ≫ f.hom = 𝟙 f.right)
    [∀ n : ℕ, HasWidePullback f.right
      (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom)] :
    f.cechNerve ⟶ f.cechNerve :=
  Arrow.mapCechNerve (cechNerveSectionArrowHom f s hs)

theorem cechNerveSelfMap_app_projection
    {C : Type u} [Category.{v} C]
    (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : s ≫ f.hom = 𝟙 f.right)
    [∀ n : ℕ, HasWidePullback f.right
      (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom)]
    (n : ℕ) (i : Fin (n + 1)) :
    (cechNerveSelfMap f s hs).app (op (SimplexCategory.mk n)) ≫
        WidePullback.π (B := f.right)
          (objs := fun _ : Fin (n + 1) => f.left)
          (arrows := fun _ => f.hom) i =
      WidePullback.π (B := f.right)
          (objs := fun _ : Fin (n + 1) => f.left)
          (arrows := fun _ => f.hom) i ≫ f.hom ≫ s := by
  sorry

theorem cechNerveSelfMap_homotopic_identity
    {C : Type u} [Category.{v} C]
    (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : s ≫ f.hom = 𝟙 f.right)
    [∀ n : ℕ, HasWidePullback f.right
      (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom)] :
    Homotopic (cechNerveSelfMap f s hs) (𝟙 f.cechNerve) := by
  sorry

theorem cechNerveHomotopyEquivalence
    {C : Type u} [Category.{v} C]
    (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : s ≫ f.hom = 𝟙 f.right)
    [∀ n : ℕ, HasWidePullback f.right
      (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom)] :
    IsHomotopyEquivalence f.augmentedCechNerve.hom := by
  let ed := Arrow.AugmentedCechNerve.extraDegeneracy f
    (splitEpiOfSection f.hom s hs)
  refine ⟨ed.section_, ?_, ?_⟩
  · exact homotopicOfEq ed.section_comp_hom
  · exact homotopicOfHomotopy ed.homotopy

theorem cechNerve_homotopy_equivalent_constant
    {C : Type u} [Category.{v} C]
    (f : Arrow C) (s : f.right ⟶ f.left)
    (hs : s ≫ f.hom = 𝟙 f.right)
    [∀ n : ℕ, HasWidePullback f.right
      (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom)] :
    HomotopyEquivalent f.cechNerve
      ((SimplicialObject.const C).obj f.right) := by
  exact ⟨f.augmentedCechNerve.hom,
    cechNerveHomotopyEquivalence f s hs⟩

/-! ## Products -/

noncomputable def indexedProduct
    {C : Type u} [Category.{v} C] {T : Type w}
    (F : T → SimplicialObject C)
    (hF : HasLimit (Discrete.functor F)) : SimplicialObject C :=
  letI := hF
  limit (Discrete.functor F)

noncomputable def indexedProductMap
    {C : Type u} [Category.{v} C] {T : Type w}
    {F G : T → SimplicialObject C}
    (hF : HasLimit (Discrete.functor F))
    (hG : HasLimit (Discrete.functor G))
    (f : ∀ t, F t ⟶ G t) :
    indexedProduct F hF ⟶ indexedProduct G hG := by
  letI := hF
  letI := hG
  change limit (Discrete.functor F) ⟶ limit (Discrete.functor G)
  let c : Cone (Discrete.functor G) :=
    { pt := limit (Discrete.functor F)
      π :=
        { app := fun t =>
            limit.π (Discrete.functor F) t ≫ f t.as
          naturality := by
            rintro ⟨i⟩ ⟨j⟩ g
            obtain rfl : i = j := Discrete.eq_of_hom g
            simp } }
  exact limit.lift (Discrete.functor G) c

theorem indexedProductMap_comp_projection
    {C : Type u} [Category.{v} C] {T : Type w}
    {F G : T → SimplicialObject C}
    (hF : HasLimit (Discrete.functor F))
    (hG : HasLimit (Discrete.functor G))
    (f : ∀ t, F t ⟶ G t) (t : T) :
    indexedProductMap hF hG f ≫
        limit.π (Discrete.functor G) ⟨t⟩ =
      limit.π (Discrete.functor F) ⟨t⟩ ≫ f t := by
  sorry

theorem indexedProduct_homotopy_of_components
    {C : Type u} [Category.{v} C] {T : Type w}
    {F G : T → SimplicialObject C}
    (hF : HasLimit (Discrete.functor F))
    (hG : HasLimit (Discrete.functor G))
    (f g : ∀ t, F t ⟶ G t)
    (H : ∀ t, Nonempty (Homotopy (f t) (g t))) :
    Nonempty (Homotopy
      (indexedProductMap hF hG f) (indexedProductMap hF hG g)) := by
  sorry

theorem indexedProduct_homotopic_of_components
    {C : Type u} [Category.{v} C] {T : Type w}
    [Finite T] {F G : T → SimplicialObject C}
    (hF : HasLimit (Discrete.functor F))
    (hG : HasLimit (Discrete.functor G))
    (f g : ∀ t, F t ⟶ G t)
    (H : ∀ t, Homotopic (f t) (g t)) :
    Homotopic (indexedProductMap hF hG f) (indexedProductMap hF hG g) := by
  sorry

theorem indexedProduct_homotopy_equivalent
    {C : Type u} [Category.{v} C] {T : Type w}
    [Finite T] {F G : T → SimplicialObject C}
    (hF : HasLimit (Discrete.functor F))
    (hG : HasLimit (Discrete.functor G))
    (H : ∀ t, HomotopyEquivalent (F t) (G t)) :
    HomotopyEquivalent (indexedProduct F hF) (indexedProduct G hG) := by
  sorry

end Formalization.Books.Simplicial.Unit26
