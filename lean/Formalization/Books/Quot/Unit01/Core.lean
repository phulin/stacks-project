import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Grassmannian
import Formalization.Books.Stacks.Unit01.Groupoids
import Formalization.Books.SpacesGroupoids.Unit22.TwoCartesianSquare

/-!
# Quot and Hilbert Spaces, Chapter 1: shared interfaces

This file fixes the relative sites and the presentation-level interfaces used
by the Introduction.  The project already has the fppf sheaf presentation of
an algebraic space and the fibred-category presentation of a stack.  The
moduli constructions in this chapter are therefore exposed by their
source-facing functors together with the properties that identify what they
classify; their representability theorems are recorded in `Introduction.lean`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

namespace Formalization.Books.Quot.Unit01

universe u v w

/-! ## Relative sites, algebraic spaces, and stacks -/

abbrev RelativeTestCategory (B : Scheme.{u}) := Over B

abbrev RelativeSetFunctor (B : Scheme.{u}) :=
  (RelativeTestCategory B)ᵒᵖ ⥤ Type u

abbrev RelativeAlgebraicSpace (B : Scheme.{u}) :=
  Formalization.Books.SpacesGroupoids.Unit22.AlgebraicSpaceOver B

def IsAlgebraicSpaceValued {B : Scheme.{u}}
    (F : RelativeSetFunctor B) : Prop :=
  ∃ X : RelativeAlgebraicSpace B, Nonempty (F ≅ X.points)

abbrev RelativeStackFunctor (B : Scheme.{u}) :=
  Formalization.Books.Stacks.Unit01.FiberedCategory (RelativeTestCategory B)

abbrev RelativeFiber {B : Scheme.{u}} (F : RelativeStackFunctor B)
    (T : RelativeTestCategory B) :=
  Formalization.Books.Stacks.Unit01.Fiber F T

structure RelativeStack (B : Scheme.{u}) where
  value : RelativeStackFunctor B
  isStackInGroupoids :
    Formalization.Books.Stacks.Unit01.StackInGroupoids value
      (Formalization.Books.SpacesGroupoids.Unit22.FppfTopology B)

structure AlgebraicStackPresentation (B : Scheme.{u}) where
  stack : RelativeStack B
  isAlgebraic : Prop

def IsAlgebraicRelativeStack {B : Scheme.{u}} (F : RelativeStack B) : Prop :=
  ∃ A : AlgebraicStackPresentation B,
    A.stack.value = F.value ∧ A.isAlgebraic

/-! ## Base change and the Hom/Isom functors -/

def baseChangeScheme {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) : Scheme.{u} :=
  pullback f T.hom

def baseChangeToX {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) : baseChangeScheme f T ⟶ X :=
  pullback.fst f T.hom

def baseChangeModule {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) (F : X.Modules) :
    (baseChangeScheme f T).Modules :=
  (Scheme.Modules.pullback (baseChangeToX f T)).obj F

structure RelativeHomFunctorData {X B : Scheme.{u}} (f : X ⟶ B)
    (F G : X.Modules) where
  value : RelativeSetFunctor B
  fiberDescription : ∀ T : RelativeTestCategory B,
    value.obj (op T) ≃
      (baseChangeModule f T F ⟶ baseChangeModule f T G)

structure RelativeIsomFunctorData {X B : Scheme.{u}} (f : X ⟶ B)
    (F G : X.Modules) (H : RelativeHomFunctorData f F G) where
  value : RelativeSetFunctor B
  fiberDescription : ∀ T : RelativeTestCategory B,
    value.obj (op T) ≃
      { φ : baseChangeModule f T F ⟶ baseChangeModule f T G // IsIso φ }
  inclusion : value ⟶ H.value
  pointwiseInjective : ∀ T, Function.Injective (inclusion.app (op T))
  inclusion_fiber : ∀ (T : RelativeTestCategory B)
      (x : value.obj (op T)),
    H.fiberDescription T (inclusion.app (op T) x) =
      (fiberDescription T x).1

/-! ## Hypotheses used by the representability interfaces -/

structure HomRepresentabilityHypotheses {X B : Scheme.{u}} (f : X ⟶ B)
    (F G : X.Modules) where
  finitePresentation : Prop
  F_quasiCoherent : Prop
  G_quasiCoherent : Prop
  G_finitelyPresented : Prop
  G_flatOverBase : Prop
  G_supportProperOverBase : Prop

structure IsomRepresentabilityHypotheses {X B : Scheme.{u}} (f : X ⟶ B)
    (F G : X.Modules) where
  finitePresentation : Prop
  F_finitelyPresented : Prop
  G_finitelyPresented : Prop
  F_flatOverBase : Prop
  G_flatOverBase : Prop
  F_supportProperOverBase : Prop
  G_supportProperOverBase : Prop

structure QuotRepresentabilityHypotheses {X B : Scheme.{u}} (f : X ⟶ B)
    (F : X.Modules) where
  finitePresentation : Prop
  separated : Prop
  F_quasiCoherent : Prop

structure HilbertRepresentabilityHypotheses {X B : Scheme.{u}} (f : X ⟶ B) where
  finitePresentation : Prop
  separated : Prop

structure PicardFunctorHypotheses {X B : Scheme.{u}} (f : X ⟶ B) where
  flat : Prop
  finitePresentation : Prop
  proper : Prop
  structureSheafPushforwardIso : Prop

structure PicardStackHypotheses {X B : Scheme.{u}} (f : X ⟶ B) where
  flat : Prop
  finitePresentation : Prop
  proper : Prop

structure RelativeMorphismHypotheses
    {Z X B : Scheme.{u}} (z : Z ⟶ B) (f : X ⟶ B) where
  targetFinitePresentation : Prop
  targetSeparated : Prop
  sourceFinitePresentation : Prop
  sourceFlat : Prop
  sourceProper : Prop

/-! ## Projective constructions and the Grassmannian -/

def IsPointwiseSubfunctor {C : Type u} [Category.{v} C]
    {F G : C ⥤ Type w} (η : F ⟶ G) : Prop :=
  ∀ A, Function.Injective (η.app A)

def LivesInsideGrassmannian {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (k : ℕ)
    (F : CommAlgCat.{u} R ⥤ Type (max v u)) : Prop :=
  ∃ η : F ⟶ Module.Grassmannian.functor (R := R) (M := M) k,
    IsPointwiseSubfunctor η

structure ProjectiveGrassmannianHypotheses where
  projective : Prop
  suitableVeryAmpleInvertibleSheaf : Prop

structure ProjectiveQuotHilbertGrassmannianData
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (k : ℕ)
    (Quotient Hilbert : CommAlgCat.{u} R ⥤ Type (max v u)) where
  quotientEmbedding : LivesInsideGrassmannian (R := R) (M := M) k Quotient
  hilbertEmbedding : LivesInsideGrassmannian (R := R) (M := M) k Hilbert

/-! ## Source-facing moduli functors and stacks -/

structure QuotFunctorData {X B : Scheme.{u}} (f : X ⟶ B)
    (F : X.Modules) where
  value : RelativeSetFunctor B
  classifiesQuotients : Prop

structure HilbertFunctorData {X B : Scheme.{u}} (f : X ⟶ B) where
  value : RelativeSetFunctor B
  classifiesClosedSubspaces : Prop

structure PicardFunctorData {X B : Scheme.{u}} (f : X ⟶ B) where
  value : RelativeSetFunctor B
  classifiesInvertibleSheafClasses : Prop

structure PicardStackData {X B : Scheme.{u}} (f : X ⟶ B) where
  stack : RelativeStack B
  classifiesInvertibleSheaves : Prop

structure RelativeMorphismFunctorData
    {Z X B : Scheme.{u}} (z : Z ⟶ B) (f : X ⟶ B) where
  value : RelativeSetFunctor B
  classifiesRelativeMorphisms : Prop

structure CoherentSheafStackData {X B : Scheme.{u}} (f : X ⟶ B) where
  stack : RelativeStack B
  classifiesCoherentSheavesWithProperSupport : Prop

structure SpacesStackData (B : Scheme.{u}) where
  stack : RelativeStack B
  classifiesFlatProperFamilies : Prop

structure PolarizedStackData (B : Scheme.{u}) where
  stack : RelativeStack B
  classifiesPolarizedProperFamilies : Prop

structure CurvesStackData (B : Scheme.{u}) where
  stack : RelativeStack B
  classifiesFamiliesOfCurves : Prop

structure ComplexesStackData {X B : Scheme.{u}} (f : X ⟶ B) where
  stack : RelativeStack B
  classifiesPerfectComplexes : Prop

def RelativeDiagonalRepresentable {B : Scheme.{u}}
    (S : RelativeStack B) : Prop :=
  ∀ (T : RelativeTestCategory B) (x y : RelativeFiber S.value T),
    ∃ A : Formalization.Books.SpacesGroupoids.Unit22.AlgebraicSpace
        (CategoryTheory.Over T)
        ((Formalization.Books.SpacesGroupoids.Unit22.FppfTopology B).over T),
      Nonempty
        (Formalization.Books.Stacks.Unit01.IsomPresheaf S.value x y ≅ A.points)

/-! ## Artin-axiom and formal-effectiveness interfaces -/

structure ArtinAxiomsWithoutFormalEffectiveness {B : Scheme.{u}}
    (S : RelativeStack B) where
  sheafCondition : Prop
  limitPreservation : Prop
  rimSchlessinger : Prop
  finiteDimensionalTangentSpaces : Prop
  opennessOfVersality : Prop

structure PolarizedFormalEffectivenessData (B : Scheme.{u}) where
  compatibleFormalFamiliesAlgebraize : Prop

end Formalization.Books.Quot.Unit01
