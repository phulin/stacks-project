import Formalization.Books.Simplicial.Unit26.Homotopies
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Simplicial Methods, Chapter 30: Trivial Kan fibrations

The boundary of the standard simplex is Mathlib's canonical `∂Δ[n]`, with
inclusion `(SSet.boundary n).ι`.  The declarations below give the source's
lifting property and its closure properties in the category of simplicial
sets.  Products, limits, filtered colimits, and homotopy equivalences use the
canonical categorical and homotopical interfaces established earlier.

The preliminary recalls about standard simplices are already represented by
the earlier interfaces `standard_simplex_obj_equiv`,
`standard_simplex_unique_nonDegenerate_top`, `simplex_map_equiv`, and
`simplex_map_equiv_apply`, together with Mathlib's
`SSet.stdSimplex.mem_nonDegenerate_iff_mono` and
`SSet.stdSimplex.nonDegenerateEquiv'`.  Thus the source's descriptions of
nondegenerate simplices as injective maps (or subsets) and of maps out of a
standard simplex require no parallel declarations here.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit30

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe u v w

/-! ## The boundary and the lifting property -/

/-
The source's boundary construction
`∂Δ[n] = i_(n - 1)! sk_(n - 1) Δ[n]` is represented by Mathlib's canonical
`SSet.boundary` and its inclusion `(SSet.boundary n).ι`; the earlier
left-adjoint identification is not needed to state any result in this
chapter.  The source's assertion that all lower-dimensional simplices lie in
the boundary and that the top simplex does not is already the pair of
Mathlib facts `SSet.boundary_obj_eq_univ` and
`SSet.stdSimplex.notMem_boundary`.
-/

/-- A simplicial map is injective in every degree. -/
abbrev TermwiseInjective {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ n : ℕ, Function.Injective (f.app (op (SimplexCategory.mk n)))

/-- The source's definition of a trivial Kan fibration. -/
def TrivialKanFibration {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  Function.Surjective (f.app (op (SimplexCategory.mk 0))) ∧
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (a : (∂Δ[n] : SSet.{u}) ⟶ X)
        (b : (Δ[n] : SSet.{u}) ⟶ Y),
        a ≫ f = (SSet.boundary n).ι ≫ b →
          ∃ l : (Δ[n] : SSet.{u}) ⟶ X,
            (SSet.boundary n).ι ≫ l = a ∧ l ≫ f = b

/-! ## General lifting and base change -/

/-- A trivial Kan fibration has the lifting property against every
degreewise-injective simplicial map. -/
theorem trivialKanFibration_lift
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f)
    {Z W : SSet.{u}} (i : Z ⟶ W) (hi : TermwiseInjective i)
    (a : Z ⟶ X) (b : W ⟶ Y) (comm : a ≫ f = i ≫ b) :
    ∃ l : W ⟶ X, i ≫ l = a ∧ l ≫ f = b := by
  sorry

/-- Base change preserves trivial Kan fibrations. -/
theorem trivialKanFibration_baseChange
    {X Y Y' : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f)
    (g : Y' ⟶ Y) :
    TrivialKanFibration (pullback.fst f g) := by
  sorry

/-- The composite of trivial Kan fibrations is a trivial Kan fibration. -/
theorem trivialKanFibration_comp
    {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : TrivialKanFibration f) (hg : TrivialKanFibration g) :
    TrivialKanFibration (f ≫ g) := by
  sorry

/-! ## Limits and products -/

/-
The source's sequence `… → U² → U¹ → U⁰` is represented by a functor
`U : ℕᵒᵖ ⥤ SSet`; its categorical limit is computed degreewise by the
presheaf category.
-/

/-- The successive transition map in an inverse sequence of simplicial sets. -/
def inverseSequenceTransition
    (U : ℕᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    U.obj (op (n + 1)) ⟶ U.obj (op n) :=
  U.map (homOfLE (Nat.le_succ n)).op

/-- The limit of a sequence of trivial Kan fibrations maps by a trivial Kan
fibration to its zeroth term. -/
theorem trivialKanFibration_limit
    (U : ℕᵒᵖ ⥤ SSet.{u})
    (hU : ∀ n : ℕ,
      TrivialKanFibration (inverseSequenceTransition U n)) :
    TrivialKanFibration (limit.π U (op 0)) := by
  sorry

/-- The product map induced by a family of trivial Kan fibrations is a
trivial Kan fibration. -/
theorem trivialKanFibration_product
    {T : Type w} {X Y : T → SSet.{u}}
    (hX : HasLimit (Discrete.functor X))
    (hY : HasLimit (Discrete.functor Y))
    (f : ∀ t, X t ⟶ Y t)
    (hf : ∀ t, TrivialKanFibration (f t)) :
    TrivialKanFibration
      (Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f) := by
  sorry

/-! ## Filtered colimits -/

/-- The canonical map on colimits induced by a natural transformation, with
the colimit choices made explicit for use in the filtered-colimit theorem. -/
noncomputable def filteredColimitMap
    {J : Type v} [Category.{v} J]
    {X Y : J ⥤ SSet.{u}} (f : X ⟶ Y)
    (hX : HasColimit X) (hY : HasColimit Y) :
    colimit X ⟶ colimit Y := by
  letI := hX
  letI := hY
  let c : Cocone X :=
    { pt := colimit Y
      ι :=
        { app := fun j => f.app j ≫ colimit.ι Y j
          naturality := by
            intro i j α
            change X.map α ≫ (f.app j ≫ colimit.ι Y j) =
              f.app i ≫ colimit.ι Y i
            rw [← Category.assoc, f.naturality α, Category.assoc, colimit.w] } }
  exact colimit.desc X c

/-- Filtered colimits preserve trivial Kan fibrations. -/
theorem trivialKanFibration_filteredColimit
    {J : Type v} [Category.{v} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (f : X ⟶ Y)
    (hX : HasColimit X) (hY : HasColimit Y)
    (hf : ∀ j, TrivialKanFibration (f.app j)) :
    TrivialKanFibration (filteredColimitMap f hX hY) := by
  sorry

/-! ## Homotopy equivalence -/

/-- A trivial Kan fibration admits a simplicial section. -/
theorem trivialKanFibration_has_section
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f) :
    ∃ g : Y ⟶ X, g ≫ f = 𝟙 Y := by
  sorry

/-- Every trivial Kan fibration is a homotopy equivalence of simplicial sets. -/
theorem trivialKanFibration_isHomotopyEquivalence
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f) :
    Formalization.Books.Simplicial.Unit26.IsHomotopyEquivalence f := by
  sorry

/-! The displayed cylinder in the final proof is represented by Mathlib's
`SSet.Homotopy`, whose interval object is `Δ[1]`; the degreewise identity
`(∂Δ[1] × X)_n ≅ X_n ⊔ X_n` is consequently subsumed by that established
endpoint API.
-/

end Formalization.Books.Simplicial.Unit30
