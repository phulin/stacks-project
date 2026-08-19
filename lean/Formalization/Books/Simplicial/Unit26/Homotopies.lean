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
      Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U)
        (op (SimplexCategory.mk n))
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
  have hinv : ∀ (n : ℕ) (i : Fin (n + 2)),
      Function.invFun (intervalSimplex.{u} n) (intervalSimplex.{u} n i) = i := by
    intro n i
    let _ : Nonempty ((Δ[1] : SSet.{u}) _⦋n⦌) :=
      interval_degree_finite_nonempty n |>.2
    apply (intervalSimplex_bijective.{u} n).1
    rw [Function.leftInverse_invFun (intervalSimplex_bijective.{u} n).1]
  let hh : ∀ (n : ℕ), (Δ[1] : SSet.{u}) _⦋n⦌ →
      (U.obj (op (SimplexCategory.mk n)) ⟶
        V.obj (op (SimplexCategory.mk n))) :=
    fun n α => H.h n (Function.invFun (intervalSimplex n) α)
  have hδ : ∀ {n : ℕ} (j : Fin (n + 2))
      (α : (Δ[1] : SSet.{u}) _⦋n + 1⦌),
      U.map (SimplexCategory.δ j).op ≫ hh n
          ((Δ[1] : SSet.{u}).map (SimplexCategory.δ j).op α) =
        hh (n + 1) α ≫ V.map (SimplexCategory.δ j).op := by
    intro n j α
    let _ : Nonempty ((Δ[1] : SSet.{u}) _⦋n + 1⦌) :=
      interval_degree_finite_nonempty (n + 1) |>.2
    let i := Function.invFun (intervalSimplex (n + 1)) α
    have hi : intervalSimplex (n + 1) i = α := by
      exact Function.rightInverse_invFun (intervalSimplex_bijective (n + 1)).2 α
    by_cases hji : j.castSucc < i
    · have hindex :
          (Δ[1] : SSet.{u}).map (SimplexCategory.δ j).op
              (intervalSimplex (n + 1) i) =
            intervalSimplex n (i.pred (Fin.ne_zero_of_lt hji)) := by
        simpa only [intervalSimplex, SimplicialObject.δ] using
          SSet.stdSimplex.δ_objMk₁_of_lt i j hji
      rw [← hi, hindex]
      dsimp [hh]
      rw [hinv (n + 1) i, hinv n (i.pred (Fin.ne_zero_of_lt hji))]
      simpa only [SimplicialObject.δ] using (H.face_of_gt i j hji).symm
    · have hij : i ≤ j.castSucc := le_of_not_gt hji
      have hindex :
          (Δ[1] : SSet.{u}).map (SimplexCategory.δ j).op
              (intervalSimplex (n + 1) i) =
            intervalSimplex n
              (i.castPred (Fin.ne_last_of_lt
                (lt_of_le_of_lt hij j.castSucc_lt_succ))) := by
        simpa only [intervalSimplex, SimplicialObject.δ] using
          SSet.stdSimplex.δ_objMk₁_of_le i j hij
      rw [← hi, hindex]
      dsimp [hh]
      rw [hinv (n + 1) i,
        hinv n (i.castPred (Fin.ne_last_of_lt
          (lt_of_le_of_lt hij j.castSucc_lt_succ)))]
      simpa only [SimplicialObject.δ] using (H.face_of_le i j hij).symm
  have hσ : ∀ {n : ℕ} (j : Fin (n + 1))
      (α : (Δ[1] : SSet.{u}) _⦋n⦌),
      U.map (SimplexCategory.σ j).op ≫ hh (n + 1)
          ((Δ[1] : SSet.{u}).map (SimplexCategory.σ j).op α) =
        hh n α ≫ V.map (SimplexCategory.σ j).op := by
    intro n j α
    let _ : Nonempty ((Δ[1] : SSet.{u}) _⦋n⦌) :=
      interval_degree_finite_nonempty n |>.2
    let i := Function.invFun (intervalSimplex n) α
    have hi : intervalSimplex n i = α := by
      exact Function.rightInverse_invFun (intervalSimplex_bijective n).2 α
    by_cases hji : j.castSucc < i
    · have hindex :
          (Δ[1] : SSet.{u}).map (SimplexCategory.σ j).op
              (intervalSimplex n i) = intervalSimplex (n + 1) i.succ := by
        simpa only [intervalSimplex, SimplicialObject.σ] using
          SSet.stdSimplex.σ_objMk₁_of_lt i j hji
      rw [← hi, hindex]
      dsimp [hh]
      rw [hinv n i, hinv (n + 1) i.succ]
      simpa only [SimplicialObject.σ] using (H.degeneracy_of_gt i j hji).symm
    · have hij : i ≤ j.castSucc := le_of_not_gt hji
      have hindex :
          (Δ[1] : SSet.{u}).map (SimplexCategory.σ j).op
              (intervalSimplex n i) = intervalSimplex (n + 1) i.castSucc := by
        simpa only [intervalSimplex, SimplicialObject.σ] using
          SSet.stdSimplex.σ_objMk₁_of_le i j hij
      rw [← hi, hindex]
      dsimp [hh]
      rw [hinv n i, hinv (n + 1) i.castSucc]
      simpa only [SimplicialObject.σ] using (H.degeneracy_of_le i j hij).symm
  have hnat : ∀ {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
      (α : (Δ[1] : SSet.{u}) _⦋n⦌),
      U.map f.op ≫ hh m ((Δ[1] : SSet.{u}).map f.op α) =
        hh n α ≫ V.map f.op := by
    let P : ℕ → Prop := fun k =>
      ∀ m n, k = m + n →
        ∀ (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
          (α : (Δ[1] : SSet.{u}) _⦋n⦌),
          U.map f.op ≫ hh m ((Δ[1] : SSet.{u}).map f.op α) =
            hh n α ≫ V.map f.op
    have hP : ∀ k, P k := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro m n hmn f α
          by_cases hmi : Function.Injective f.toOrderHom
          · by_cases hns : Function.Surjective f.toOrderHom
            · have hcard : m + 1 = n + 1 := by
                simpa using Nat.card_congr
                  (Equiv.ofBijective f.toOrderHom ⟨hmi, hns⟩)
              have hmn' : m = n := by omega
              subst n
              have hmono : Mono f :=
                (SimplexCategory.mono_iff_injective).mpr hmi
              rw [SimplexCategory.eq_id_of_mono f]
              simp
            · cases n with
              | zero =>
                  exfalso
                  apply hns
                  intro y
                  exact ⟨0, (Fin.eq_zero _).trans (Fin.eq_zero y).symm⟩
              | succ n =>
                  obtain ⟨i, f', hf⟩ :=
                    SimplexCategory.eq_comp_δ_of_not_surjective f hns
                  have hi := ih (m + n) (by omega) m n rfl f'
                    ((Δ[1] : SSet.{u}).map (SimplexCategory.δ i).op α)
                  have hcomp :
                      (Δ[1] : SSet.{u}).map
                          (f' ≫ SimplexCategory.δ i).op α =
                        (Δ[1] : SSet.{u}).map f'.op
                          ((Δ[1] : SSet.{u}).map (SimplexCategory.δ i).op α) := by
                    rw [op_comp, Functor.map_comp]
                    rfl
                  rw [hf, hcomp, op_comp, U.map_comp, Category.assoc, hi]
                  rw [← Category.assoc, hδ i α]
                  rw [V.map_comp]
                  simp only [Category.assoc]
          · cases m with
            | zero =>
                exfalso
                apply hmi
                intro x y hxy
                exact (Fin.eq_zero x).trans (Fin.eq_zero y).symm
            | succ m =>
                obtain ⟨i, f', hf⟩ :=
                  SimplexCategory.eq_σ_comp_of_not_injective f hmi
                have hi := ih (m + n) (by omega) m n rfl f' α
                have hcomp :
                    (Δ[1] : SSet.{u}).map
                        (SimplexCategory.σ i ≫ f').op α =
                      (Δ[1] : SSet.{u}).map (SimplexCategory.σ i).op
                        ((Δ[1] : SSet.{u}).map f'.op α) := by
                  rw [op_comp, Functor.map_comp]
                  rfl
                rw [hf, hcomp, op_comp, U.map_comp, Category.assoc,
                  hσ i ((Δ[1] : SSet.{u}).map f'.op α)]
                rw [← Category.assoc, hi, V.map_comp]
                simp only [Category.assoc]
    intro m n f α
    exact hP (m + n) m n rfl f α
  refine ⟨{
    h := {
      app := fun X =>
        let _ : HasCoproduct
            (fun _ : (Δ[1] : SSet.{u}).obj X => U.obj X) :=
          Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U) X
        Sigma.desc (fun α => hh X.unop.len α)
      naturality := by
        intro X Y f
        induction X using Opposite.rec with
        | _ X =>
          induction Y using Opposite.rec with
          | _ Y =>
            induction X using SimplexCategory.rec with
            | _ m =>
              induction Y using SimplexCategory.rec with
              | _ n =>
                let X := SimplexCategory.mk m
                let Y := SimplexCategory.mk n
                let _ : HasCoproduct
                    (fun _ : (Δ[1] : SSet.{u}).obj (op X) => U.obj (op X)) :=
                  Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U) (op X)
                let _ : HasCoproduct
                    (fun _ : (Δ[1] : SSet.{u}).obj (op Y) => U.obj (op Y)) :=
                  Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U) (op Y)
                apply Sigma.hom_ext
                intro α
                dsimp [intervalCylinder, Unit13.simplicialSetProductOf]
                change
                  Sigma.ι
                      (fun _ : (Δ[1] : SSet.{u}).obj (op X) => U.obj (op X)) α ≫
                    Sigma.desc (fun β =>
                      U.map f ≫ Sigma.ι
                        (fun _ : (Δ[1] : SSet.{u}).obj (op Y) => U.obj (op Y))
                        ((Δ[1] : SSet.{u}).map f β)) ≫
                    Sigma.desc (fun β => hh n β) =
                  Sigma.ι
                      (fun _ : (Δ[1] : SSet.{u}).obj (op X) => U.obj (op X)) α ≫
                    Sigma.desc (fun β => hh m β) ≫ V.map f
                calc
                  Sigma.ι
                        (fun _ : (Δ[1] : SSet.{u}).obj (op X) => U.obj (op X)) α ≫
                      Sigma.desc (fun β =>
                        U.map f ≫ Sigma.ι
                          (fun _ : (Δ[1] : SSet.{u}).obj (op Y) => U.obj (op Y))
                          ((Δ[1] : SSet.{u}).map f β)) ≫
                      Sigma.desc (fun β => hh n β) =
                    U.map f ≫ hh n ((Δ[1] : SSet.{u}).map f α) := by
                      rw [← Category.assoc, Sigma.ι_desc, Category.assoc,
                        Sigma.ι_desc]
                  _ = hh m α ≫ V.map f := by
                    simpa only [Quiver.Hom.op_unop] using hnat f.unop α
                  _ = Sigma.ι
                        (fun _ : (Δ[1] : SSet.{u}).obj (op X) => U.obj (op X)) α ≫
                      Sigma.desc (fun β => hh m β) ≫ V.map f := by
                      rw [← Category.assoc, Sigma.ι_desc]
    }
    h₀ := by
      ext X
      induction X using Opposite.rec with
      | _ X =>
        induction X using SimplexCategory.rec with
        | _ n =>
          let X := SimplexCategory.mk n
          let _ : HasCoproduct
              (fun _ : (Δ[1] : SSet.{u}).obj (op X) => U.obj (op X)) :=
            Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U) (op X)
          have hz : intervalSimplex n (Fin.last (n + 1)) =
              SSet.stdSimplex.const 1 0 (op X) := by
            apply SSet.stdSimplex.objEquiv.injective
            ext j
            simp [intervalSimplex, SSet.stdSimplex.objMk₁_apply,
              SSet.stdSimplex.objEquiv_toOrderHom_apply, SSet.stdSimplex.const,
              OrderHom.const]
            change (0 : ℕ) = 0
            rfl
          have hi : Function.invFun (intervalSimplex n)
              (SSet.stdSimplex.const 1 0 (op X)) = Fin.last (n + 1) := by
            rw [← hz]
            exact hinv n (Fin.last (n + 1))
          change
            Sigma.ι (fun _ : (Δ[1] : SSet.{u}).obj (op X) => U.obj (op X))
                (SSet.stdSimplex.const 1 0 (op X)) ≫
              Sigma.desc (fun α => hh n α) = a.app (op X)
          rw [Sigma.ι_desc]
          change H.h n (Function.invFun (intervalSimplex n)
            (SSet.stdSimplex.const 1 0 (op X))) = a.app (op X)
          rw [hi]
          exact H.h_last n
    h₁ := by
      ext X
      induction X using Opposite.rec with
      | _ X =>
        induction X using SimplexCategory.rec with
        | _ n =>
          let X := SimplexCategory.mk n
          let _ : HasCoproduct
              (fun _ : (Δ[1] : SSet.{u}).obj (op X) => U.obj (op X)) :=
            Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U) (op X)
          have hz : intervalSimplex n 0 =
              SSet.stdSimplex.const 1 1 (op X) := by
            apply SSet.stdSimplex.objEquiv.injective
            ext j
            simp [intervalSimplex, SSet.stdSimplex.objMk₁_apply,
              SSet.stdSimplex.objEquiv_toOrderHom_apply, SSet.stdSimplex.const,
              OrderHom.const]
            change (1 : ℕ) = 1
            rfl
          have hi : Function.invFun (intervalSimplex n)
              (SSet.stdSimplex.const 1 1 (op X)) = 0 := by
            rw [← hz]
            exact hinv n 0
          change
            Sigma.ι (fun _ : (Δ[1] : SSet.{u}).obj (op X) => U.obj (op X))
                (SSet.stdSimplex.const 1 1 (op X)) ≫
              Sigma.desc (fun α => hh n α) = b.app (op X)
          rw [Sigma.ι_desc]
          change H.h n (Function.invFun (intervalSimplex n)
            (SSet.stdSimplex.const 1 1 (op X))) = b.app (op X)
          rw [hi]
          exact H.h_zero n
  }⟩

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

/-! The source's degree-preserving convention and Mathlib's degree-raising
convention contain the same data.  We keep both explicit because the former
is convenient for interval arguments, while the latter interfaces with
Mathlib's normalized-chain-complex API. -/

private noncomputable def homotopyDegreewiseComponent
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopy a b) (n : ℕ) (i : Fin (n + 2)) :
    U.obj (op (SimplexCategory.mk n)) ⟶ V.obj (op (SimplexCategory.mk n)) :=
  Fin.lastCases (a.app (op (SimplexCategory.mk n)))
    (fun i => H.h i ≫ V.δ i.castSucc) i

private lemma homotopyDegreewiseComponent_castSucc
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopy a b) (n : ℕ) (i : Fin (n + 1)) :
    homotopyDegreewiseComponent H n i.castSucc = H.h i ≫ V.δ i.castSucc := by
  simp [homotopyDegreewiseComponent]

private lemma homotopyDegreewiseComponent_succ
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopy a b) (n : ℕ) (i : Fin (n + 1)) :
    homotopyDegreewiseComponent H n i.succ = H.h i ≫ V.δ i.succ := by
  cases i using Fin.lastCases with
  | last =>
      simp [homotopyDegreewiseComponent]
  | cast i =>
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
          rw [show i.castSucc.succ = i.succ.castSucc by ext; rfl,
            homotopyDegreewiseComponent_castSucc]
          exact H.h_succ_comp_δ_castSucc_succ i

/-- Convert Mathlib's degree-raising simplicial homotopy to the source's
degree-preserving convention. -/
noncomputable def homotopyToDegreewiseHomotopy
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopy a b) : DegreewiseHomotopy a b where
  h n := homotopyDegreewiseComponent H n
  h_zero n := by
    rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl,
      homotopyDegreewiseComponent_castSucc]
    exact H.h_zero_comp_δ_zero n
  h_last n := by simp [homotopyDegreewiseComponent]
  face_of_gt := by
    intro n i j hji
    cases i using Fin.lastCases with
    | last =>
        simp only [homotopyDegreewiseComponent, Fin.lastCases_last, Fin.pred_last]
        exact (a.naturality _).symm
    | cast k =>
        simp only [homotopyDegreewiseComponent, Fin.lastCases_castSucc]
        cases k using Fin.cases with
        | zero => simp at hji
        | succ l =>
            have hk : l.succ.castSucc.pred (Fin.ne_zero_of_lt hji) = l.castSucc := by
              apply Fin.ext
              simp
            rw [hk, Fin.lastCases_castSucc]
            have hval : (j : ℕ) < (l : ℕ) + 1 := by exact hji
            have hle : j ≤ l.castSucc := Fin.le_iff_val_le_val.mpr
              (Nat.le_of_lt_succ hval)
            have hδ := V.δ_comp_δ (i := j) (j := l.castSucc) hle
            have hH := H.h_succ_comp_δ_castSucc_of_lt j l hle
            rw [show l.succ.castSucc = l.castSucc.succ by ext; rfl]
            simp only [Category.assoc]
            rw [hδ, ← Category.assoc, hH, Category.assoc]
  face_of_le := by
    intro n i j hij
    cases i using Fin.cases with
    | zero =>
        have hc₁ : homotopyDegreewiseComponent H (n + 1) 0 =
            H.h 0 ≫ V.δ 0 := by
          simpa using homotopyDegreewiseComponent_castSucc H (n + 1)
            (0 : Fin (n + 2))
        have hc₀ : homotopyDegreewiseComponent H n ((0 : Fin (n + 3)).castPred
            (Fin.ne_last_of_lt (lt_of_le_of_lt hij j.castSucc_lt_succ))) =
            H.h 0 ≫ V.δ 0 := by
          have hz : (0 : Fin (n + 3)).castPred
              (Fin.ne_last_of_lt (lt_of_le_of_lt hij j.castSucc_lt_succ)) = 0 := by
            apply Fin.ext
            rfl
          rw [hz]
          simpa using homotopyDegreewiseComponent_castSucc H n (0 : Fin (n + 1))
        rw [hc₁, hc₀, H.h_zero_comp_δ_zero (n + 1),
          H.h_zero_comp_δ_zero n]
        exact (b.naturality _).symm
    | succ k =>
        have hklt : k < Fin.last (n + 1) := by
          change (k : ℕ) < n + 1
          have hv : (k : ℕ) + 1 ≤ (j : ℕ) := Fin.le_iff_val_le_val.mp hij
          omega
        let l : Fin (n + 1) := k.castPred (ne_of_lt hklt)
        have hkl : k = l.castSucc := by apply Fin.ext; rfl
        have hi : k.succ.castPred (Fin.ne_last_of_lt
            (lt_of_le_of_lt hij j.castSucc_lt_succ)) = l.succ := by
          apply Fin.ext
          simp [l]
        rw [hi, homotopyDegreewiseComponent_succ,
          homotopyDegreewiseComponent_succ, hkl]
        have hlt : l.castSucc < j := by
          apply Fin.lt_def.mpr
          exact lt_of_lt_of_le (Nat.lt_succ_self _) (Fin.le_iff_val_le_val.mp hij)
        have hδ := V.δ_comp_δ (i := l.succ) (j := j) hij
        have hH := H.h_castSucc_comp_δ_succ_of_lt j l hlt
        rw [show l.castSucc.succ = l.succ.castSucc by ext; rfl]
        simp only [Category.assoc]
        rw [← hδ, ← Category.assoc, hH, Category.assoc]
  degeneracy_of_gt := by
    intro n i j hji
    cases i using Fin.cases with
    | zero => simp at hji
    | succ k =>
        rw [homotopyDegreewiseComponent_succ]
        rw [homotopyDegreewiseComponent_succ]
        have hle : j ≤ k := by
          apply Fin.le_iff_val_le_val.mpr
          exact Nat.le_of_lt_succ hji
        have hδσ := V.δ_comp_σ_of_gt (i := k.succ) (j := j) hji
        have hH := H.h_comp_σ_castSucc_of_le j k hle
        simp only [Category.assoc]
        rw [← hδσ, ← Category.assoc, hH, Category.assoc]
  degeneracy_of_le := by
    intro n i j hij
    cases i using Fin.cases with
    | zero =>
        have hc₀ : homotopyDegreewiseComponent H n 0 = H.h 0 ≫ V.δ 0 := by
          simpa using homotopyDegreewiseComponent_castSucc H n (0 : Fin (n + 1))
        have hc₁ : homotopyDegreewiseComponent H (n + 1)
            (0 : Fin (n + 2)).castSucc = H.h 0 ≫ V.δ 0 :=
          homotopyDegreewiseComponent_castSucc H (n + 1) 0
        rw [hc₀, hc₁, H.h_zero_comp_δ_zero n,
          H.h_zero_comp_δ_zero (n + 1)]
        exact (b.naturality _).symm
    | succ k =>
        rw [homotopyDegreewiseComponent_succ]
        rw [show k.succ.castSucc = k.castSucc.succ by ext; rfl,
          homotopyDegreewiseComponent_succ]
        have hle : k ≤ j := by
          apply Fin.le_iff_val_le_val.mpr
          exact le_trans (Nat.le_succ _) (Fin.le_iff_val_le_val.mp hij)
        have hδσ := V.δ_comp_σ_of_le (i := k.succ) (j := j) hij
        have hH := H.h_comp_σ_succ_of_lt j k hle
        simp only [Category.assoc]
        rw [← hδσ, ← Category.assoc, hH, Category.assoc]
        congr 2

/-- Convert the source's degree-preserving homotopy to Mathlib's
degree-raising convention. -/
noncomputable def degreewiseHomotopyToHomotopy
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) : Homotopy a b := {
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
      rw [hface, H.h_zero n]
      rw [U.δ_comp_σ_self'_assoc (i := 0) (j := 0) (by ext; rfl)]
    h_last_comp_δ_last := by
      intro n
      let i : Fin (n + 3) := (Fin.last n).castSucc.succ
      let j : Fin (n + 2) := Fin.last (n + 1)
      have hle : i ≤ j.castSucc := by simp [i, j]
      have hface := H.face_of_le (n := n) i j hle
      have hcast : i.castPred
          (Fin.ne_last_of_lt (lt_of_le_of_lt hle j.castSucc_lt_succ)) =
            Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      rw [hcast] at hface
      simp only [Category.assoc]
      rw [hface]
      rw [U.δ_comp_σ_succ'_assoc (i := Fin.last n)
        (j := Fin.last (n + 1)) (by ext; rfl)]
      simp [H.h_last]
    h_succ_comp_δ_castSucc_of_lt := by
      intro n i j hij
      have hgt : i.castSucc.castSucc < j.succ.castSucc.succ := by
        apply Fin.val_fin_lt.mpr
        have hij' : (i : ℕ) ≤ (j : ℕ) := Fin.le_iff_val_le_val.mp hij
        exact hij'.trans_lt (Nat.lt_succ_of_le (Nat.le_succ _))
      have hface := H.face_of_gt (n := n + 1)
        (i := j.succ.castSucc.succ) (j := i.castSucc) hgt
      have hpred : (j.succ.castSucc.succ).pred (Fin.ne_zero_of_lt hgt) =
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
      have hpred₁ : (j.succ.castSucc.succ).pred
          (Fin.ne_zero_of_lt (show (j.castSucc.succ).castSucc <
            j.succ.castSucc.succ by simp)) = j.castSucc.succ := by
        apply Fin.ext
        rfl
      rw [hpred₁] at hface₁
      have hface₂ := H.face_of_le (n := n + 1)
        (i := j.castSucc.castSucc.succ) (j := j.castSucc.succ) (by simp)
      have hpred₂ : (j.castSucc.castSucc.succ).castPred
          (Fin.ne_last_of_lt (lt_of_le_of_lt (by simp)
            (j.castSucc.succ).castSucc_lt_succ)) = j.castSucc.succ := by
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
      have hpred : (j.castSucc.castSucc.succ).castPred
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
      have hidx : (j.castSucc.succ).castSucc = j.castSucc.castSucc.succ := by
        apply Fin.ext
        simp
      rw [hidx] at hface
      simp only [Category.assoc]
      rw [hface, ← U.σ_comp_σ_assoc hji] }

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
  constructor
  · rintro ⟨H⟩
    exact ⟨degreewiseHomotopyToHomotopy H⟩
  · rintro ⟨H⟩
    exact ⟨homotopyToDegreewiseHomotopy H⟩

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

theorem homotopy_to_degreewise
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopy a b) : Nonempty (DegreewiseHomotopy a b) :=
  ⟨homotopyToDegreewiseHomotopy H⟩

/-- Compatibility alias for the proved camel-case conversion. -/
noncomputable def degreewiseHomotopy_to_homotopy
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) : Homotopy a b :=
  degreewiseHomotopyToHomotopy H

theorem degreewiseHomotopy_iff_oneStepHomotopy
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} {a b : U ⟶ V} :
    Nonempty (DegreewiseHomotopy a b) ↔ OneStepHomotopy a b := by
  constructor
  · rintro ⟨H⟩
    exact ⟨degreewiseHomotopy_to_homotopy H⟩
  · rintro ⟨H⟩
    exact homotopy_to_degreewise H

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
  refine {
    comp_left := ?_
    comp_right := ?_
    equivalence := ?_ }
  · intro X Y Z f g g' h
    change Homotopic (f ≫ g) (f ≫ g')
    change Homotopic g g' at h
    induction h with
    | rel g g' h =>
        rcases h with ⟨K⟩
        exact Relation.EqvGen.rel _ _ ⟨K.precomp f⟩
    | refl g => exact Relation.EqvGen.refl _
    | symm g g' h ih => exact Relation.EqvGen.symm _ _ ih
    | trans g g' g'' h₁ h₂ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro X Y Z f f' g h
    change Homotopic (f ≫ g) (f' ≫ g)
    change Homotopic f f' at h
    induction h with
    | rel f f' h =>
        rcases h with ⟨K⟩
        exact Relation.EqvGen.rel _ _ ⟨K.postcomp g⟩
    | refl f => exact Relation.EqvGen.refl _
    | symm f f' h ih => exact Relation.EqvGen.symm _ _ ih
    | trans f f' f'' h₁ h₂ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro X Y
    exact homotopic_is_equivalence X Y

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
  induction H with
  | rel a b h =>
      rcases h with ⟨K⟩
      exact Relation.EqvGen.rel _ _ ⟨degreewiseHomotopyToHomotopy
        (mapDegreewiseHomotopy (homotopyToDegreewiseHomotopy K) F)⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c h₁ h₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

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
  induction H with
  | rel a b h =>
      rcases h with ⟨K⟩
      exact Relation.EqvGen.rel _ _ ⟨K.postcomp q⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c h₁ h₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem precompose_homotopic
    {C : Type u} [Category.{v} C]
    {U V X : SimplicialObject C} {a b : U ⟶ V}
    (H : Homotopic a b) (p : X ⟶ U) :
    Homotopic (p ≫ a) (p ≫ b) := by
  induction H with
  | rel a b h =>
      rcases h with ⟨K⟩
      exact Relation.EqvGen.rel _ _ ⟨K.precomp p⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c h₁ h₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

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
  let g : ∀ {n : ℕ}, (Δ[m] : SSet.{u}) _⦋n⦌ →
      (Δ[1] : SSet.{u}) _⦋n⦌ →
        (SimplexCategory.mk n ⟶ SimplexCategory.mk m) :=
    fun {n} φ α => SimplexCategory.Hom.mk {
      toFun := fun k => if α k = 0 then φ k else Fin.last m
      monotone' := by
        intro i j hij
        by_cases hi : α i = 0
        · by_cases hj : α j = 0
          · simp only [if_pos hi, if_pos hj]
            exact (SSet.stdSimplex.monotone_apply φ) hij
          · have hj1 : α j = 1 := Fin.eq_one_of_ne_zero (α j) hj
            simp only [if_pos hi, if_neg hj]
            exact Fin.le_last _
        · have hi1 : α i = 1 := Fin.eq_one_of_ne_zero (α i) hi
          have hα := (SSet.stdSimplex.monotone_apply α) hij
          have hj1 : α j = 1 := by
            apply Fin.eq_one_of_ne_zero (α j)
            intro hj
            apply hi
            apply Fin.ext
            have hα' : (α i).val ≤ (α j).val :=
              Fin.le_iff_val_le_val.mp hα
            have hi' : (α i).val = 1 :=
              congrArg (fun z : Fin 2 => z.val) hi1
            have hj' : (α j).val = 0 :=
              congrArg (fun z : Fin 2 => z.val) hj
            omega
          simp [hi1, hj1]
    }
  let h : (Δ[m] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶
      (Δ[m] : SSet.{u}) := {
    app := fun X => TypeCat.ofHom (fun x =>
      SSet.stdSimplex.objEquiv.symm (g x.1 x.2))
    naturality := by
      intro X Y f
      ext x
      change SSet.stdSimplex.objEquiv.symm
          (g ((Δ[m] : SSet.{u}).map f x.1)
            ((Δ[1] : SSet.{u}).map f x.2)) =
        (Δ[m] : SSet.{u}).map f
          (SSet.stdSimplex.objEquiv.symm (g x.1 x.2))
      apply SSet.stdSimplex.objEquiv.injective
      ext k
      simp [g, SSet.stdSimplex.map_apply] <;> rfl
    }
  let H : SSet.Homotopy (𝟙 (Δ[m] : SSet.{u}))
      (simplexToPoint m ≫ pointToSimplexLast m) := by
    unfold SSet.Homotopy
    refine { h := h, h₀ := ?_, h₁ := ?_, rel := ?_ }
    · change SSet.ι₀ ≫ h = 𝟙 (Δ[m] : SSet.{u})
      apply SimplicialObject.hom_ext
      intro X
      induction X using Opposite.rec with
      | _ X =>
        induction X using SimplexCategory.rec with
        | _ n =>
          apply ConcreteCategory.hom_ext
          intro x
          change SSet.stdSimplex.objEquiv.symm
              (g ((SSet.ι₀.app (op (SimplexCategory.mk n))) x).1
                ((SSet.ι₀.app (op (SimplexCategory.mk n))) x).2) = x
          have hfst := SSet.ι₀_app_fst (X := (Δ[m] : SSet.{u})) x
          have hsnd := SSet.ι₀_app_snd_apply (X := (Δ[m] : SSet.{u})) x
          apply SSet.stdSimplex.objEquiv.injective
          ext k
          simp [g, hfst, hsnd, SSet.stdSimplex.const]
    · change SSet.ι₁ ≫ h = simplexToPoint m ≫ pointToSimplexLast m
      apply SimplicialObject.hom_ext
      intro X
      induction X using Opposite.rec with
      | _ X =>
        induction X using SimplexCategory.rec with
        | _ n =>
          apply ConcreteCategory.hom_ext
          intro x
          change SSet.stdSimplex.objEquiv.symm
              (g ((SSet.ι₁.app (op (SimplexCategory.mk n))) x).1
                ((SSet.ι₁.app (op (SimplexCategory.mk n))) x).2) =
            (simplexToPoint m ≫ pointToSimplexLast m).app
              (op (SimplexCategory.mk n)) x
          have hfst := SSet.ι₁_app_fst (X := (Δ[m] : SSet.{u})) x
          have hsnd := SSet.ι₁_app_snd_apply (X := (Δ[m] : SSet.{u})) x
          apply SSet.stdSimplex.objEquiv.injective
          ext k
          simp [g, hfst, hsnd, simplexToPoint, pointToSimplexLast,
            SSet.stdSimplex.const, SSet.stdSimplex.map_apply]
    · ext m x
      exact x.1.property.elim
  refine ⟨H, ?_⟩
  intro n φ α k
  dsimp [H, h]
  change ((SSet.stdSimplex.objEquiv.symm (g φ α) :
    (Δ[m] : SSet.{u}) _⦋n⦌) k) = _
  rfl

theorem simplexFirstHomotopy_exists (m : ℕ) :
    Nonempty
      (SSet.Homotopy (simplexToPoint m ≫ pointToSimplexFirst m)
        (𝟙 (Δ[m] : SSet.{u}))) := by
  let g : ∀ {n : ℕ}, (Δ[m] : SSet.{u}) _⦋n⦌ →
      (Δ[1] : SSet.{u}) _⦋n⦌ →
        (SimplexCategory.mk n ⟶ SimplexCategory.mk m) :=
    fun {n} φ α => SimplexCategory.Hom.mk {
      toFun := fun k => if α k = 0 then 0 else φ k
      monotone' := by
        intro i j hij
        by_cases hi : α i = 0
        · by_cases hj : α j = 0
          · simp only [if_pos hi, if_pos hj]
            exact le_rfl
          · simp only [if_pos hi, if_neg hj]
            exact Fin.zero_le _
        · have hj : ¬ α j = 0 := by
            intro hj
            apply hi
            apply Fin.ext
            have hα := (SSet.stdSimplex.monotone_apply α) hij
            have hα' : (α i).val ≤ (α j).val :=
              Fin.le_iff_val_le_val.mp hα
            have hi' : (α i).val = 1 :=
              congrArg (fun z : Fin 2 => z.val)
                (Fin.eq_one_of_ne_zero (α i) hi)
            have hj' : (α j).val = 0 :=
              congrArg (fun z : Fin 2 => z.val) hj
            omega
          simp only [if_neg hi, if_neg hj]
          exact (SSet.stdSimplex.monotone_apply φ) hij
    }
  let h : (Δ[m] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶
      (Δ[m] : SSet.{u}) := {
    app := fun X => TypeCat.ofHom (fun x =>
      SSet.stdSimplex.objEquiv.symm (g x.1 x.2))
    naturality := by
      intro X Y f
      ext x
      change SSet.stdSimplex.objEquiv.symm
          (g ((Δ[m] : SSet.{u}).map f x.1)
            ((Δ[1] : SSet.{u}).map f x.2)) =
        (Δ[m] : SSet.{u}).map f
          (SSet.stdSimplex.objEquiv.symm (g x.1 x.2))
      apply SSet.stdSimplex.objEquiv.injective
      ext k
      simp [g, SSet.stdSimplex.map_apply] <;> rfl
    }
  refine ⟨?_⟩
  unfold SSet.Homotopy
  refine { h := h, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · change SSet.ι₀ ≫ h = simplexToPoint m ≫ pointToSimplexFirst m
    apply SimplicialObject.hom_ext
    intro X
    induction X using Opposite.rec with
    | _ X =>
      induction X using SimplexCategory.rec with
      | _ n =>
        apply ConcreteCategory.hom_ext
        intro x
        change SSet.stdSimplex.objEquiv.symm
            (g ((SSet.ι₀.app (op (SimplexCategory.mk n))) x).1
              ((SSet.ι₀.app (op (SimplexCategory.mk n))) x).2) =
          (simplexToPoint m ≫ pointToSimplexFirst m).app
            (op (SimplexCategory.mk n)) x
        have hfst := SSet.ι₀_app_fst (X := (Δ[m] : SSet.{u})) x
        have hsnd := SSet.ι₀_app_snd_apply (X := (Δ[m] : SSet.{u})) x
        apply SSet.stdSimplex.objEquiv.injective
        ext k
        simp [g, hfst, hsnd, simplexToPoint, pointToSimplexFirst,
          SSet.stdSimplex.const, SSet.stdSimplex.map_apply]
  · change SSet.ι₁ ≫ h = 𝟙 (Δ[m] : SSet.{u})
    apply SimplicialObject.hom_ext
    intro X
    induction X using Opposite.rec with
    | _ X =>
      induction X using SimplexCategory.rec with
      | _ n =>
        apply ConcreteCategory.hom_ext
        intro x
        change SSet.stdSimplex.objEquiv.symm
            (g ((SSet.ι₁.app (op (SimplexCategory.mk n))) x).1
              ((SSet.ι₁.app (op (SimplexCategory.mk n))) x).2) = x
        have hfst := SSet.ι₁_app_fst (X := (Δ[m] : SSet.{u})) x
        have hsnd := SSet.ι₁_app_snd_apply (X := (Δ[m] : SSet.{u})) x
        apply SSet.stdSimplex.objEquiv.injective
        ext k
        simp [g, hfst, hsnd, SSet.stdSimplex.const]
  · ext m x
    exact x.1.property.elim

theorem simplex_homotopy_equivalent_point (m : ℕ) :
    HomotopyEquivalent (Δ[m] : SSet.{u}) (Δ[0] : SSet.{u}) := by
  refine ⟨simplexToPoint m, ?_⟩
  refine ⟨pointToSimplexLast m,
    homotopicOfEq (pointToSimplexLast_comp_simplexToPoint m), ?_⟩
  obtain ⟨H, hH⟩ := simplexMaxHomotopy_exists m
  let hh (n : ℕ) (i : Fin (n + 2)) :
      (Δ[m] : SSet.{u}) _⦋n⦌ ⟶ (Δ[m] : SSet.{u}) _⦋n⦌ :=
    TypeCat.ofHom (fun φ =>
      H.h.app (op (SimplexCategory.mk n)) (φ, intervalSimplex n i))
  have component_naturality :
      ∀ {r s : ℕ} (f : SimplexCategory.mk r ⟶ SimplexCategory.mk s)
        (i : Fin (s + 2)) (k : Fin (r + 2)),
        (Δ[1] : SSet.{u}).map f.op (intervalSimplex s i) =
          intervalSimplex r k →
        (Δ[m] : SSet.{u}).map f.op ≫ hh r k =
          hh s i ≫ (Δ[m] : SSet.{u}).map f.op := by
    intro r s f i k hk
    apply ConcreteCategory.hom_ext
    intro φ
    have hn := congrArg
      (fun q => q (φ, intervalSimplex s i)) (H.h.naturality f.op)
    change H.h.app (op (SimplexCategory.mk r))
          ((Δ[m] : SSet.{u}).map f.op φ,
            (Δ[1] : SSet.{u}).map f.op (intervalSimplex s i)) =
        (Δ[m] : SSet.{u}).map f.op
          (H.h.app (op (SimplexCategory.mk s))
            (φ, intervalSimplex s i)) at hn
    rw [hk] at hn
    simpa [hh] using hn
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
  let K : DegreewiseHomotopy (𝟙 (Δ[m] : SSet.{u}))
      (simplexToPoint m ≫ pointToSimplexLast m) := {
    h := hh
    h_zero := by
      intro n
      apply ConcreteCategory.hom_ext
      intro φ
      change H.h.app (op (SimplexCategory.mk n))
          (φ, intervalSimplex n 0) =
        (simplexToPoint m ≫ pointToSimplexLast m).app
          (op (SimplexCategory.mk n)) φ
      apply SSet.stdSimplex.objEquiv.injective
      ext k
      simp only [SSet.stdSimplex.objEquiv_toOrderHom_apply]
      rw [hH]
      simp [intervalSimplex, SSet.stdSimplex.objMk₁_apply,
        simplexToPoint, pointToSimplexLast, SSet.stdSimplex.const,
        SSet.stdSimplex.map_apply] <;> rfl
    h_last := by
      intro n
      apply ConcreteCategory.hom_ext
      intro φ
      change H.h.app (op (SimplexCategory.mk n))
          (φ, intervalSimplex n (Fin.last (n + 1))) = φ
      apply SSet.stdSimplex.objEquiv.injective
      ext k
      simp only [SSet.stdSimplex.objEquiv_toOrderHom_apply]
      rw [hH]
      simp [intervalSimplex, SSet.stdSimplex.objMk₁_apply]
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
          (degeneracy_le_map i j hij)).symm }
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _ ⟨degreewiseHomotopy_to_homotopy K⟩)

/-! ## The cylinder is homotopy equivalent to its base -/

theorem intervalMaxMap_exists :
    ∃ μ : ((Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ⟶
        (Δ[1] : SSet.{u}),
      ∀ (n : ℕ) (β₁ β₂ : (Δ[1] : SSet.{u}) _⦋n⦌),
        μ.app (op (SimplexCategory.mk n)) (β₁, β₂) =
          fun k => max (β₁ k) (β₂ k) := by
  let g : ∀ {n : ℕ}, (Δ[1] : SSet.{u}) _⦋n⦌ →
      (Δ[1] : SSet.{u}) _⦋n⦌ →
        (SimplexCategory.mk n ⟶ SimplexCategory.mk 1) :=
    fun {n} β₁ β₂ => SimplexCategory.Hom.mk {
      toFun := fun k => max (β₁ k) (β₂ k)
      monotone' := by
        intro i j hij
        exact max_le_max
          (SSet.stdSimplex.monotone_apply β₁ hij)
          (SSet.stdSimplex.monotone_apply β₂ hij) }
  let μ : ((Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ⟶
      (Δ[1] : SSet.{u}) := {
    app := fun X => TypeCat.ofHom (fun x =>
      SSet.stdSimplex.objEquiv.symm (g x.1 x.2))
    naturality := by
      intro X Y f
      ext x
      change SSet.stdSimplex.objEquiv.symm
          (g ((Δ[1] : SSet.{u}).map f x.1)
            ((Δ[1] : SSet.{u}).map f x.2)) =
        (Δ[1] : SSet.{u}).map f
          (SSet.stdSimplex.objEquiv.symm (g x.1 x.2))
      apply SSet.stdSimplex.objEquiv.injective
      ext k
      simp [g, SSet.stdSimplex.map_apply] <;> rfl
    }
  refine ⟨μ, ?_⟩
  intro n β₁ β₂
  dsimp [μ]
  rfl

theorem intervalMinMap_exists :
    ∃ μ : ((Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ⟶
        (Δ[1] : SSet.{u}),
      ∀ (n : ℕ) (β₁ β₂ : (Δ[1] : SSet.{u}) _⦋n⦌),
        μ.app (op (SimplexCategory.mk n)) (β₁, β₂) =
          fun k => min (β₁ k) (β₂ k) := by
  let g : ∀ {n : ℕ}, (Δ[1] : SSet.{u}) _⦋n⦌ →
      (Δ[1] : SSet.{u}) _⦋n⦌ →
        (SimplexCategory.mk n ⟶ SimplexCategory.mk 1) :=
    fun {n} β₁ β₂ => SimplexCategory.Hom.mk {
      toFun := fun k => min (β₁ k) (β₂ k)
      monotone' := by
        intro i j hij
        exact min_le_min
          (SSet.stdSimplex.monotone_apply β₁ hij)
          (SSet.stdSimplex.monotone_apply β₂ hij) }
  let μ : ((Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ⟶
      (Δ[1] : SSet.{u}) := {
    app := fun X => TypeCat.ofHom (fun x =>
      SSet.stdSimplex.objEquiv.symm (g x.1 x.2))
    naturality := by
      intro X Y f
      ext x
      change SSet.stdSimplex.objEquiv.symm
          (g ((Δ[1] : SSet.{u}).map f x.1)
            ((Δ[1] : SSet.{u}).map f x.2)) =
        (Δ[1] : SSet.{u}).map f
          (SSet.stdSimplex.objEquiv.symm (g x.1 x.2))
      apply SSet.stdSimplex.objEquiv.injective
      ext k
      simp [g, SSet.stdSimplex.map_apply] <;> rfl
    }
  refine ⟨μ, ?_⟩
  intro n β₁ β₂
  dsimp [μ]
  rfl

theorem intervalProjection_comp_endpoint
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) :
    intervalEndpoint U 0 ≫ intervalProjection U = 𝟙 U ∧
      intervalEndpoint U 1 ≫ intervalProjection U = 𝟙 U := by
  constructor
  · apply NatTrans.ext
    funext X
    let _ : HasCoproduct
        (fun _ : (Δ[1] : SSet.{u}).obj X => U.obj X) :=
      Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U) X
    change
      Sigma.ι (fun _ : (Δ[1] : SSet.{u}).obj X => U.obj X)
          (SSet.stdSimplex.const 1 0 X) ≫
        Sigma.desc (fun _ => 𝟙 (U.obj X)) = 𝟙 _
    simp
  · apply NatTrans.ext
    funext X
    let _ : HasCoproduct
        (fun _ : (Δ[1] : SSet.{u}).obj X => U.obj X) :=
      Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U) X
    change
      Sigma.ι (fun _ : (Δ[1] : SSet.{u}).obj X => U.obj X)
          (SSet.stdSimplex.const 1 1 X) ≫
        Sigma.desc (fun _ => 𝟙 (U.obj X)) = 𝟙 _
    simp

theorem intervalCylinder_id_homotopic_endpoint_zero
    {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    (U : SimplicialObject C) :
    Homotopic (𝟙 (intervalCylinder U))
      (intervalProjection U ≫ intervalEndpoint U 0) := by
  obtain ⟨μ, hμ⟩ := intervalMinMap_exists
  let hh (n : ℕ) (i : Fin (n + 2)) :
      (intervalCylinder U).obj (op (SimplexCategory.mk n)) ⟶
        (intervalCylinder U).obj (op (SimplexCategory.mk n)) :=
    let _ : HasCoproduct
        (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj (op (SimplexCategory.mk n))) :=
      Unit13.degreewiseCoproductInstance (Δ[1] : SSet.{u}) U
        (Unit13.standardSimplex_finite_nonempty 1) n
    Sigma.desc (fun β =>
      Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
          U.obj (op (SimplexCategory.mk n)))
        (μ.app (op (SimplexCategory.mk n))
          (β, intervalSimplex n i)))
  have component_naturality :
      ∀ {r s : ℕ} (f : SimplexCategory.mk r ⟶ SimplexCategory.mk s)
        (i : Fin (s + 2)) (k : Fin (r + 2)),
        (Δ[1] : SSet.{u}).map f.op (intervalSimplex s i) =
          intervalSimplex r k →
        (intervalCylinder U).map f.op ≫ hh r k =
          hh s i ≫ (intervalCylinder U).map f.op := by
    intro r s f i k hk
    let _ : HasCoproduct
        (fun _ : (Δ[1] : SSet.{u}) _⦋r⦌ => U.obj (op (SimplexCategory.mk r))) :=
      Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U)
        (op (SimplexCategory.mk r))
    let _ : HasCoproduct
        (fun _ : (Δ[1] : SSet.{u}) _⦋s⦌ => U.obj (op (SimplexCategory.mk s))) :=
      Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U)
        (op (SimplexCategory.mk s))
    apply Sigma.hom_ext
    intro β
    have hn := congrArg
      (fun q => q ((β : (Δ[1] : SSet.{u}) _⦋s⦌), intervalSimplex s i))
      (μ.naturality f.op)
    change
      μ.app (op (SimplexCategory.mk r))
          ((Δ[1] : SSet.{u}).map f.op β,
            (Δ[1] : SSet.{u}).map f.op (intervalSimplex s i)) =
        (Δ[1] : SSet.{u}).map f.op
          (μ.app (op (SimplexCategory.mk s))
            (β, intervalSimplex s i)) at hn
    dsimp [intervalCylinder, Unit13.simplicialSetProductOf, hh]
    rw [← Category.assoc, Sigma.ι_desc, Category.assoc, Sigma.ι_desc]
    rw [hk] at hn
    calc
      _ = U.map f.op ≫
          Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋r⦌ =>
            U.obj (op (SimplexCategory.mk r)))
            ((Δ[1] : SSet.{u}).map f.op
              (μ.app (op (SimplexCategory.mk s))
                (β, intervalSimplex s i))) := by
        convert congrArg
          (fun z => U.map f.op ≫
            Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋r⦌ =>
              U.obj (op (SimplexCategory.mk r))) z) hn using 1
        all_goals rfl
      _ = _ := by
        rw [← Category.assoc, Sigma.ι_desc]
        exact (Sigma.ι_desc
          (fun u : (Δ[1] : SSet.{u}) _⦋s⦌ =>
            U.map f.op ≫
              Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋r⦌ =>
                U.obj (op (SimplexCategory.mk r)))
                ((Δ[1] : SSet.{u}).map f.op u))
          (μ.app (op (SimplexCategory.mk s))
            (β, intervalSimplex s i))).symm
  let K : DegreewiseHomotopy
      (intervalProjection U ≫ intervalEndpoint U 0)
      (𝟙 (intervalCylinder U)) := {
    h := hh
    h_zero := by
      intro n
      let _ : HasCoproduct
          (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj (op (SimplexCategory.mk n))) :=
        Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U)
          (op (SimplexCategory.mk n))
      apply Sigma.hom_ext
      intro β
      have hβ :
          μ.app (op (SimplexCategory.mk n))
              (β, intervalSimplex n 0) = β := by
        apply SSet.stdSimplex.objEquiv.injective
        ext j
        simp only [SSet.stdSimplex.objEquiv_toOrderHom_apply]
        rw [hμ]
        simp [intervalSimplex, SSet.stdSimplex.objMk₁_apply]
        omega
      have hdesc :
          Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
              U.obj (op (SimplexCategory.mk n))) β ≫
            Sigma.desc (fun β =>
              Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
                U.obj (op (SimplexCategory.mk n)))
                (μ.app (op (SimplexCategory.mk n))
                  (β, intervalSimplex n 0))) =
          Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
              U.obj (op (SimplexCategory.mk n)))
            (μ.app (op (SimplexCategory.mk n))
              (β, intervalSimplex n 0)) := by
        simp
      dsimp [intervalCylinder, Unit13.simplicialSetProductOf, hh]
      calc
        _ = Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
              U.obj (op (SimplexCategory.mk n)))
            (μ.app (op (SimplexCategory.mk n))
              (β, intervalSimplex n 0)) := hdesc
        _ = Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
              U.obj (op (SimplexCategory.mk n))) β := by rw [hβ]
        _ = _ := by simp
    h_last := by
      intro n
      let _ : HasCoproduct
          (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj (op (SimplexCategory.mk n))) :=
        Unit13.degreewiseCoproductInstanceAt (intervalCoproducts U)
          (op (SimplexCategory.mk n))
      apply Sigma.hom_ext
      intro β
      have hβ :
          μ.app (op (SimplexCategory.mk n))
              (β, intervalSimplex n (Fin.last (n + 1))) =
            SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n)) := by
        apply SSet.stdSimplex.objEquiv.injective
        ext j
        simp only [SSet.stdSimplex.objEquiv_toOrderHom_apply]
        rw [hμ]
        simp [intervalSimplex, SSet.stdSimplex.objMk₁_apply,
          SSet.stdSimplex.const]
      rw [NatTrans.comp_app]
      dsimp [intervalCylinder, Unit13.simplicialSetProductOf, hh,
        intervalProjection, intervalEndpoint]
      rw [Unit13.productWithSimplicialSetTo_app]
      change
        Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj
            (op (SimplexCategory.mk n))) β ≫
          Sigma.desc (fun β =>
            Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj
              (op (SimplexCategory.mk n)))
              (μ.app (op (SimplexCategory.mk n))
                (β, intervalSimplex n (Fin.last (n + 1))))) =
        Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj
            (op (SimplexCategory.mk n))) β ≫
          Sigma.desc (fun _ => 𝟙 (U.obj (op (SimplexCategory.mk n)))) ≫
            Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ => U.obj
              (op (SimplexCategory.mk n)))
              (SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n)))
      have hdesc :
          Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
              U.obj (op (SimplexCategory.mk n))) β ≫
            Sigma.desc (fun β =>
              Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
                U.obj (op (SimplexCategory.mk n)))
                (μ.app (op (SimplexCategory.mk n))
                  (β, intervalSimplex n (Fin.last (n + 1))))) =
          Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
              U.obj (op (SimplexCategory.mk n)))
            (μ.app (op (SimplexCategory.mk n))
              (β, intervalSimplex n (Fin.last (n + 1)))) := by
        simp
      calc
        _ = Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
              U.obj (op (SimplexCategory.mk n)))
            (μ.app (op (SimplexCategory.mk n))
              (β, intervalSimplex n (Fin.last (n + 1)))) := hdesc
        _ = Sigma.ι (fun _ : (Δ[1] : SSet.{u}) _⦋n⦌ =>
              U.obj (op (SimplexCategory.mk n)))
            (SSet.stdSimplex.const 1 0 (op (SimplexCategory.mk n))) := by
          rw [hβ]
        _ = _ := by simp
    face_of_gt := by
      intro n i j hji
      simpa only [SimplicialObject.δ] using
        (component_naturality (SimplexCategory.δ j) i
          (i.pred (Fin.ne_zero_of_lt hji)) (by
            simpa only [intervalSimplex, SimplicialObject.δ] using
              SSet.stdSimplex.δ_objMk₁_of_lt i j hji)).symm
    face_of_le := by
      intro n i j hij
      simpa only [SimplicialObject.δ] using
        (component_naturality (SimplexCategory.δ j) i
          (i.castPred (Fin.ne_last_of_lt
            (lt_of_le_of_lt hij j.castSucc_lt_succ))) (by
            simpa only [intervalSimplex, SimplicialObject.δ] using
              SSet.stdSimplex.δ_objMk₁_of_le i j hij)).symm
    degeneracy_of_gt := by
      intro n i j hji
      simpa only [SimplicialObject.σ] using
        (component_naturality (SimplexCategory.σ j) i i.succ (by
          simpa only [intervalSimplex, SimplicialObject.σ] using
            SSet.stdSimplex.σ_objMk₁_of_lt i j hji)).symm
    degeneracy_of_le := by
      intro n i j hij
      simpa only [SimplicialObject.σ] using
        (component_naturality (SimplexCategory.σ j) i i.castSucc (by
          simpa only [intervalSimplex, SimplicialObject.σ] using
            SSet.stdSimplex.σ_objMk₁_of_le i j hij)).symm }
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _ ⟨degreewiseHomotopy_to_homotopy K⟩)

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
