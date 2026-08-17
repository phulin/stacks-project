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
  semistableTwistedSheafStack : Prop
  moduliStackIsArtin : IsArtinStack moduliStack
  locallyOfFinitePresentationOverBase :
    LocallyOfFinitePresentation moduliToBase
  associatedPointsAndPurityTheory : Prop

def HasSemistableTwistedSheafModuli {C : Type u} [Category.{v} C]
    [StackCategory C] (D : RelativeSurfaceGerbeData (C := C)) : Prop :=
  ∃ M : TwistedSheafModuliData D,
    M.semistableTwistedSheafStack ∧ IsArtinStack M.moduliStack ∧
      LocallyOfFinitePresentation M.moduliToBase ∧
      M.associatedPointsAndPurityTheory

theorem lieblich_semistable_twisted_sheaves_form_an_artin_stack
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : RelativeSurfaceGerbeData (C := C))
    (hprojective : D.projectiveRelativeSurface)
    (hsmoothConnected : D.smoothConnectedGeometricFibers)
    (hgerbe : D.isMuNGerbe) :
    HasSemistableTwistedSheafModuli D := by
  sorry

structure AssociatedPointsAndPurityData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  associatedPoints : Prop
  purityOfSheaves : Prop

def HasAssociatedPointsAndPurityTheory {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ D : AssociatedPointsAndPurityData X,
    D.associatedPoints ∧ D.purityOfSheaves

theorem lieblich_associated_points_and_purity_on_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hArtin : IsArtinStack X) :
    HasAssociatedPointsAndPurityTheory X := by
  sorry

structure FunctorialReconstructionData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  associatedFunctor : C → Type u
  reconstructionHypotheses : Prop
  reconstructionConclusion : Prop

def IsReconstructedFromAssociatedFunctor {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} (D : FunctorialReconstructionData X) : Prop :=
  D.reconstructionHypotheses ∧ D.reconstructionConclusion

theorem lieblich_osserman_functorial_reconstruction
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : FunctorialReconstructionData X)
    (h : D.reconstructionHypotheses) :
    D.reconstructionConclusion := by
  sorry

structure QuasiFiniteDiagonalData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  diagonalIsQuasiFinite : Prop

def HasQuasiFiniteDiagonal {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ D : QuasiFiniteDiagonalData X, D.diagonalIsQuasiFinite

structure NoetherianApproximationData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  approximation : C
  approximationMap : X ⟶ approximation
  approximationIsNoetherian : Prop
  approximatesOriginalStack : Prop

def HasNoetherianApproximation {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ D : NoetherianApproximationData X,
    D.approximationIsNoetherian ∧ D.approximatesOriginalStack

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
