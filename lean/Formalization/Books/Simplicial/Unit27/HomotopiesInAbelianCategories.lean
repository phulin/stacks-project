import Formalization.Books.Simplicial.Unit23.SimplicialObjectsAndChainComplexes
import Formalization.Books.Simplicial.Unit26.Homotopies
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Homology.Homotopy

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
  sorry

theorem additiveAssociatedHomotopyComponent_zero_equation
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) :
    additiveAssociatedHomotopyComponent H 0 ≫ additiveAssociatedBoundary V 0 =
      a.app (op ⦋0⦌) - b.app (op ⦋0⦌) := by
  sorry

theorem additiveAssociatedHomotopyComponent_succ_equation
    {C : Type u} [Category.{v} C] [Preadditive C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : DegreewiseHomotopy a b) (n : ℕ) :
    additiveAssociatedHomotopyComponent H (n + 1) ≫
          additiveAssociatedBoundary V (n + 1) +
        additiveAssociatedBoundary U n ≫
          additiveAssociatedHomotopyComponent H n =
      a.app (op ⦋n + 1⦌) - b.app (op ⦋n + 1⦌) := by
  sorry

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
  sorry

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
  sorry

theorem normalizedChainMap_homotopic
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : Formalization.Books.Simplicial.Unit26.Homotopic a b) :
    Nonempty (_root_.Homotopy
      (normalizedChainComplexMap a)
      (normalizedChainComplexMap b)) := by
  sorry

theorem additiveAssociatedChainMap_homotopyEquivalence
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {U V : SimplicialObject C} {a : U ⟶ V}
    (H : Formalization.Books.Simplicial.Unit26.IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences C (ComplexShape.down ℕ)
      (additiveAssociatedChainComplexMap a) := by
  sorry

theorem normalizedChainMap_homotopyEquivalence
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} {a : U ⟶ V}
    (H : Formalization.Books.Simplicial.Unit26.IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences C (ComplexShape.down ℕ)
      (normalizedChainComplexMap a) := by
  sorry

end Formalization.Books.Simplicial.Unit27
