import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.Prod
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

import Formalization.Books.Exercises.Unit04.Core

/-!
# Exercises, Chapter 4: Tensor product

This file contains the declarations for the four numbered parts of
`exercise-characterize-tensor-functor`.  Proposition proofs are intentionally
left for the prove stage; the functors and examples themselves are defined
explicitly.
-/

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace Formalization.Books.Exercises.Unit04

/-! ## (1) An additive functor which is not `R`-linear -/

/-- The product ring used for the non-`R`-linear additive example. -/
abbrev exampleRing : Type := ℤ × ℤ

/-- The ring automorphism which swaps the two components of `exampleRing`. -/
def exampleRingSwap : exampleRing ≃+* exampleRing :=
  RingEquiv.prodComm (R := ℤ) (S := ℤ)

/-- Restriction of scalars along the component swap. -/
def exampleAdditiveFunctor :
    ModuleCat exampleRing ⥤ ModuleCat exampleRing :=
  ModuleCat.restrictScalars exampleRingSwap.toRingHom

/-- The restriction-of-scalars example is additive but not linear over the
original product ring. -/
theorem additive_not_R_linear_example :
    exampleAdditiveFunctor.Additive ∧
      ¬ Functor.Linear exampleRing exampleAdditiveFunctor := by
  refine ⟨{ map_add := by intros; rfl }, ?_⟩
  intro h
  have h' := (Functor.linear_iff exampleRing exampleAdditiveFunctor).mp h
  let X := ModuleCat.of exampleRing (ULift exampleRing)
  have hx := h' X ((1, 0) : exampleRing)
  have hx' := congrArg (fun f => f (ULift.up ((1, 0) : exampleRing))) hx
  change ULift.up ((1, 0) : exampleRing) = ULift.up ((0, 0) : exampleRing) at hx'
  exact (by norm_num : ((1, 0) : exampleRing) ≠ (0, 0)) (ULift.up.inj hx')

/-! ## (2) Tensoring with a fixed module -/

/-- The canonical functor `M ↦ M ⊗_R N`, namely right tensoring in the
monoidal category of `R`-modules. -/
noncomputable def tensorProductFunctor
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  CategoryTheory.MonoidalCategory.tensorRight N

/-- Tensoring with `N` is `R`-linear in the source's bundled sense. -/
theorem tensorProductFunctor_is_R_linear
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    IsRLinearFunctor (tensorProductFunctor N) := by
  unfold IsRLinearFunctor tensorProductFunctor
  exact ⟨CategoryTheory.tensorRight_additive N, CategoryTheory.tensorRight_linear R N⟩

/-- Tensoring with `N` is right exact. -/
theorem tensorProductFunctor_is_right_exact
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    PreservesFiniteColimits (tensorProductFunctor N) := by
  unfold tensorProductFunctor
  refine ⟨fun J _ _ => ⟨fun {K} => ?_⟩⟩
  exact CategoryTheory.MonoidalCategory.Limits.preservesColimit_of_braided_and_preservesColimit_tensor_left K N

/-- Tensoring with `N` commutes with arbitrary direct sums. -/
theorem tensorProductFunctor_commutes_with_direct_sums
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    CommutesWithDirectSums (tensorProductFunctor N) := by
  unfold CommutesWithDirectSums tensorProductFunctor
  intro ι M
  infer_instance

/-! ## (3) The converse characterization -/

/-- A source-faithful formulation of the Eilenberg--Watts characterization.
The phrase “is of the form” is represented by a natural isomorphism of
functors, since categorical functors are determined only up to isomorphism. -/
theorem exists_tensorProductFunctor_iso
    {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    (hF : IsRLinearFunctor F)
    (hRight : PreservesFiniteColimits F)
    (hSums : CommutesWithDirectSums F) :
    ∃ N : ModuleCat.{u} R, Nonempty (F ≅ tensorProductFunctor N) := by
  sorry

/-! ## (4) Why direct sums cannot be omitted -/

/-- The countable product endofunctor on abelian groups, written directly on
objects and morphisms. -/
def infiniteProductFunctor :
    ModuleCat ℤ ⥤ ModuleCat ℤ where
  obj M := ModuleCat.of ℤ (ℕ → M)
  map {M N} f :=
    ModuleCat.ofHom (X := ModuleCat.of ℤ (ℕ → M))
      (Y := ModuleCat.of ℤ (ℕ → N))
      { toFun := fun x n => f.hom (x n)
        map_add' := by
          intro x y
          funext n
          exact f.hom.map_add (x n) (y n)
        map_smul' := by
          intro r x
          funext n
          simp }
  map_id := by
    intro M
    apply ModuleCat.hom_ext
    ext x n
    rfl
  map_comp := by
    intro M N P f g
    apply ModuleCat.hom_ext
    ext x n
    rfl

/-- The product functor supplies the requested counterexample after the
direct-sum hypothesis is removed. -/
theorem exists_right_exact_R_linear_not_tensorProductFunctor :
    ∃ F : ModuleCat ℤ ⥤ ModuleCat ℤ,
      IsRLinearFunctor F ∧
        PreservesFiniteColimits F ∧
          ¬ CommutesWithDirectSums F ∧
            ¬ ∃ N : ModuleCat ℤ, Nonempty (F ≅ tensorProductFunctor N) := by
  refine ⟨infiniteProductFunctor, ?_⟩
  sorry

end Formalization.Books.Exercises.Unit04
