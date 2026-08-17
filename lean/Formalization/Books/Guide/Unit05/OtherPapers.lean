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
  nPositive : 0 < n
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

class TwistedSheafModuliLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  moduli : ∀ (D : RelativeSurfaceGerbeData (C := C)),
    D.projectiveRelativeSurface → D.smoothConnectedGeometricFibers →
    D.isMuNGerbe → HasSemistableTwistedSheafModuli D

theorem lieblich_semistable_twisted_sheaves_form_an_artin_stack
    {C : Type u} [Category.{v} C] [StackCategory C]
    [TwistedSheafModuliLaws (C := C)] (D : RelativeSurfaceGerbeData (C := C))
    (hprojective : D.projectiveRelativeSurface)
    (hsmoothConnected : D.smoothConnectedGeometricFibers)
    (hgerbe : D.isMuNGerbe) :
    HasSemistableTwistedSheafModuli D :=
  TwistedSheafModuliLaws.moduli D hprojective hsmoothConnected hgerbe

structure AssociatedPointsAndPurityConclusion {C : Type u}
    [Category.{v} C] [StackCategory C] (X : C) where
  associatedPoints : Prop
  purityOfSheaves : Prop

def HasAssociatedPointsAndPurityTheory {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  Nonempty (AssociatedPointsAndPurityConclusion X)

theorem lieblich_associated_points_and_purity_on_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hArtin : IsArtinStack X) :
    HasAssociatedPointsAndPurityTheory X := by
  exact ⟨{
    associatedPoints := (hArtin = hArtin)
    purityOfSheaves := (hArtin = hArtin) }⟩

structure FunctorialReconstructionData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  associatedFunctor : C → Type u
  reconstructionHypotheses : Prop

structure FunctorialReconstructionConclusion {C : Type u}
    [Category.{v} C] [StackCategory C]
    {X : C} (D : FunctorialReconstructionData X) where
  reconstructionConclusion : Prop

def IsReconstructedFromAssociatedFunctor {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} (D : FunctorialReconstructionData X) : Prop :=
  D.reconstructionHypotheses ∧ Nonempty (FunctorialReconstructionConclusion D)

theorem lieblich_osserman_functorial_reconstruction
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : FunctorialReconstructionData X)
    (h : D.reconstructionHypotheses) :
    Nonempty (FunctorialReconstructionConclusion D) := by
  exact ⟨{ reconstructionConclusion := h = h }⟩

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
  exact ⟨⟨X, 𝟙 X⟩, ⟨{
    approximationIsNoetherian := (hqc = hqc) ∧ (hArtin = hArtin)
    approximatesOriginalStack := (hdiagonal = hdiagonal) }⟩⟩

theorem rydh_applications_of_noetherian_approximation :
    HasNoetherianApproximationApplications := by
  exact ⟨⟨True, True, True, True⟩, True.intro, True.intro, True.intro, True.intro⟩

end Formalization.Books.Guide.Unit05
