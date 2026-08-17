import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 14: other papers
-/

noncomputable section

open CategoryTheory
open Formalization.Books.StacksMorphisms.Unit07

universe u v

namespace Formalization.Books.Guide.Unit05

structure RelativeSurfaceGerbeData {C : Type u} [Category.{v} C]
    [StackCategory C] where
  base : C
  surface : C
  surfaceToBase : surface ⟶ base
  projectiveRelativeSurface : Prop
  smoothConnectedGeometricFibers : Prop
  n : ℕ
  gerbe : C
  gerbeToSurface : gerbe ⟶ surface
  isMuNGerbe : Prop

structure TwistedSheafModuliData {C : Type u} [Category.{v} C]
    [StackCategory C] (D : RelativeSurfaceGerbeData (C := C)) where
  moduliStack : C
  moduliToBase : moduliStack ⟶ D.base

structure TwistedSheafModuliConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] (D : RelativeSurfaceGerbeData (C := C))
    (M : TwistedSheafModuliData D) where
  semistableTwistedSheafStack : Prop
  moduliStackIsArtin : IsArtinStack M.moduliStack
  locallyOfFinitePresentationOverBase :
    LocallyOfFinitePresentation M.moduliToBase

def HasSemistableTwistedSheafModuli {C : Type u} [Category.{v} C]
    [StackCategory C] (D : RelativeSurfaceGerbeData (C := C)) : Prop :=
  ∃ M : TwistedSheafModuliData D, Nonempty (TwistedSheafModuliConclusion D M)

theorem lieblich_semistable_twisted_sheaves_form_an_artin_stack
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : RelativeSurfaceGerbeData (C := C))
    (hprojective : D.projectiveRelativeSurface)
    (hsmoothConnected : D.smoothConnectedGeometricFibers)
    (hgerbe : D.isMuNGerbe) :
    HasSemistableTwistedSheafModuli D := by
  sorry

structure AssociatedPointsAndPurityConclusion where
  associatedPoints : Prop
  purityOfSheaves : Prop

def HasAssociatedPointsAndPurityTheory {C : Type u} [Category.{v} C]
    [StackCategory C] (_X : C) : Prop :=
  Nonempty (AssociatedPointsAndPurityConclusion)

theorem lieblich_associated_points_and_purity_on_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hArtin : IsArtinStack X) :
    HasAssociatedPointsAndPurityTheory X := by
  sorry

structure FunctorialReconstructionData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  associatedFunctor : C → Type u
  reconstructionHypotheses : Prop

structure FunctorialReconstructionConclusion where
  reconstructionConclusion : Prop

def IsReconstructedFromAssociatedFunctor {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} (D : FunctorialReconstructionData X) : Prop :=
  D.reconstructionHypotheses ∧ Nonempty FunctorialReconstructionConclusion

theorem lieblich_osserman_functorial_reconstruction
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : FunctorialReconstructionData X)
    (h : D.reconstructionHypotheses) :
    Nonempty FunctorialReconstructionConclusion := by
  sorry

structure NoetherianApproximationData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  approximation : C
  approximationMap : X ⟶ approximation

structure NoetherianApproximationConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} (D : NoetherianApproximationData X) where
  approximationIsNoetherian : Prop
  approximatesOriginalStack : Prop

def HasNoetherianApproximation {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ D : NoetherianApproximationData X,
    Nonempty (NoetherianApproximationConclusion D)

structure NoetherianApproximationApplications where
  chevalley : Prop
  serre : Prop
  zariski : Prop
  chow : Prop

def HasNoetherianApproximationApplications : Prop :=
  ∃ D : NoetherianApproximationApplications,
    D.chevalley ∧ D.serre ∧ D.zariski ∧ D.chow

theorem rydh_noetherian_approximation_of_quasi_finite_diagonal
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hqc : IsQuasiCompactStack X) (hdiagonal : HasQuasiFiniteDiagonal X)
    (hArtin : IsArtinStack X) :
    HasNoetherianApproximation X := by
  sorry

theorem rydh_applications_of_noetherian_approximation :
    HasNoetherianApproximationApplications := by
  sorry

end Formalization.Books.Guide.Unit05
