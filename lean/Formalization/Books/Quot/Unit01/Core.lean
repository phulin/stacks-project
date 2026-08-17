import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
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

/-! ## Base change and the Hom/Isom functors -/

def baseChangeScheme {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) : Scheme.{u} :=
  pullback f T.hom

def baseChangeToX {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) : baseChangeScheme f T ⟶ X :=
  pullback.fst f T.hom

def baseChangeToTest {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) : baseChangeScheme f T ⟶ T.left :=
  pullback.snd f T.hom

def baseChangeModule {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) (F : X.Modules) :
    (baseChangeScheme f T).Modules :=
  (Scheme.Modules.pullback (baseChangeToX f T)).obj F

/-!
`RelativeSetClassification` records the data that makes a relative
set-valued functor classify a specified family of objects.  The restriction
maps and their laws are part of the interface: a collection of unrelated
fibrewise equivalences is not enough to describe a functor.
-/
structure RelativeSetClassification {B : Scheme.{u}}
    (value : RelativeSetFunctor B)
    (Objects : RelativeTestCategory B → Type u) where
  restrict : ∀ {T₁ T₂ : RelativeTestCategory B},
    (T₁ ⟶ T₂) → Objects T₂ → Objects T₁
  restrict_id : ∀ (T : RelativeTestCategory B) (x : Objects T),
    restrict (𝟙 T) x = x
  restrict_comp : ∀ {T₁ T₂ T₃ : RelativeTestCategory B}
    (q₁₂ : T₁ ⟶ T₂) (q₂₃ : T₂ ⟶ T₃) (x : Objects T₃),
    restrict q₁₂ (restrict q₂₃ x) = restrict (q₁₂ ≫ q₂₃) x
  fiberDescription : ∀ T : RelativeTestCategory B,
    value.obj (op T) ≃ Objects T
  fiberDescription_natural : ∀ {T₁ T₂ : RelativeTestCategory B}
    (q : T₁ ⟶ T₂) (x : value.obj (op T₂)),
    fiberDescription T₁ (value.map q.op x) =
      restrict q (fiberDescription T₂ x)

/-! The object-level interfaces used by the named moduli functors. -/

structure RelativeQuotientObject {X B : Scheme.{u}} (f : X ⟶ B)
    (F : X.Modules) (T : RelativeTestCategory B) where
  target : (baseChangeScheme f T).Modules
  quotient : baseChangeModule f T F ⟶ target
  targetQuasiCoherent : Prop
  targetFinitePresentation : Prop
  targetFlatOverTest : Prop
  supportProperOverTest : Prop

structure RelativeHilbertObject {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ baseChangeScheme f T
  structureMap : carrier ⟶ T.left
  overTest : inclusion ≫ baseChangeToTest f T = structureMap
  closed : Prop
  finitePresentationOverTest : Prop
  flatOverTest : Prop
  properOverTest : Prop

structure RelativeInvertibleSheafRepresentative {X B : Scheme.{u}}
    (f : X ⟶ B) (T : RelativeTestCategory B) where
  module : (baseChangeScheme f T).Modules
  invertible : Prop

def relativeInvertibleSheafSetoid {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) : Setoid (RelativeInvertibleSheafRepresentative f T) where
  r L M := Nonempty (L.module ≅ M.module)
  iseqv := {
    refl := fun L => ⟨Iso.refl _⟩
    symm := by
      intro L M h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    trans := by
      intro L M N hLM hMN
      rcases hLM with ⟨eLM⟩
      rcases hMN with ⟨eMN⟩
      exact ⟨eLM.trans eMN⟩
  }

abbrev RelativeInvertibleSheafClass {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) :=
  Quotient (relativeInvertibleSheafSetoid f T)

structure RelativeMorphismObject {Z X B : Scheme.{u}}
    (z : Z ⟶ B) (f : X ⟶ B) (T : RelativeTestCategory B) where
  map : baseChangeScheme z T ⟶ baseChangeScheme f T
  overTest : map ≫ baseChangeToTest f T = baseChangeToTest z T

structure RelativeCoherentSheafObject {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) where
  module : (baseChangeScheme f T).Modules
  quasiCoherent : Prop
  finitePresentation : Prop
  flatOverTest : Prop
  supportProperOverTest : Prop

structure RelativeFlatProperFamily (B : Scheme.{u})
    (T : RelativeTestCategory B) where
  totalSpace : Scheme.{u}
  structureMap : totalSpace ⟶ T.left
  finitePresentation : Prop
  flat : Prop
  proper : Prop

structure RelativePolarizedFamily (B : Scheme.{u})
    (T : RelativeTestCategory B) extends RelativeFlatProperFamily B T where
  polarization : Prop

structure RelativeCurveFamily (B : Scheme.{u})
    (T : RelativeTestCategory B) extends RelativeFlatProperFamily B T where
  isCurve : Prop

structure RelativePerfectComplexFamily {X B : Scheme.{u}} (f : X ⟶ B)
    (T : RelativeTestCategory B) where
  perfect : Prop
  negativeSelfExtVanishing : Prop

def RelativeFamilyIso {B : Scheme.{u}} {T : RelativeTestCategory B}
    (A C : RelativeFlatProperFamily B T) : Type u :=
  { φ : A.totalSpace ⟶ C.totalSpace //
      IsIso φ ∧ φ ≫ C.structureMap = A.structureMap }

structure RelativeHomFunctorData {X B : Scheme.{u}} (f : X ⟶ B)
    (F G : X.Modules) where
  value : RelativeSetFunctor B
  restrictHom : ∀ {T₁ T₂ : RelativeTestCategory B},
    (T₁ ⟶ T₂) →
      (baseChangeModule f T₂ F ⟶ baseChangeModule f T₂ G) →
        (baseChangeModule f T₁ F ⟶ baseChangeModule f T₁ G)
  restrictHom_id : ∀ (T : RelativeTestCategory B)
      (φ : baseChangeModule f T F ⟶ baseChangeModule f T G),
    restrictHom (𝟙 T) φ = φ
  restrictHom_comp : ∀ {T₁ T₂ T₃ : RelativeTestCategory B}
      (q₁₂ : T₁ ⟶ T₂) (q₂₃ : T₂ ⟶ T₃)
      (φ : baseChangeModule f T₃ F ⟶ baseChangeModule f T₃ G),
    restrictHom q₁₂ (restrictHom q₂₃ φ) =
      restrictHom (q₁₂ ≫ q₂₃) φ
  fiberDescription : ∀ T : RelativeTestCategory B,
    value.obj (op T) ≃
      (baseChangeModule f T F ⟶ baseChangeModule f T G)
  fiberDescription_natural : ∀ {T₁ T₂ : RelativeTestCategory B}
      (q : T₁ ⟶ T₂) (x : value.obj (op T₂)),
    fiberDescription T₁ (value.map q.op x) =
      restrictHom q (fiberDescription T₂ x)

structure RelativeIsomFunctorData {X B : Scheme.{u}} (f : X ⟶ B)
    (F G : X.Modules) (H : RelativeHomFunctorData f F G) where
  value : RelativeSetFunctor B
  restrictIsom : ∀ {T₁ T₂ : RelativeTestCategory B},
    (T₁ ⟶ T₂) →
      { φ : baseChangeModule f T₂ F ⟶ baseChangeModule f T₂ G // IsIso φ } →
        { φ : baseChangeModule f T₁ F ⟶ baseChangeModule f T₁ G // IsIso φ }
  restrictIsom_id : ∀ (T : RelativeTestCategory B)
      (φ : { φ : baseChangeModule f T F ⟶ baseChangeModule f T G // IsIso φ }),
    restrictIsom (𝟙 T) φ = φ
  restrictIsom_comp : ∀ {T₁ T₂ T₃ : RelativeTestCategory B}
      (q₁₂ : T₁ ⟶ T₂) (q₂₃ : T₂ ⟶ T₃)
      (φ : { φ : baseChangeModule f T₃ F ⟶ baseChangeModule f T₃ G // IsIso φ }),
    restrictIsom q₁₂ (restrictIsom q₂₃ φ) =
      restrictIsom (q₁₂ ≫ q₂₃) φ
  fiberDescription : ∀ T : RelativeTestCategory B,
    value.obj (op T) ≃
      { φ : baseChangeModule f T F ⟶ baseChangeModule f T G // IsIso φ }
  fiberDescription_natural : ∀ {T₁ T₂ : RelativeTestCategory B}
      (q : T₁ ⟶ T₂) (x : value.obj (op T₂)),
    fiberDescription T₁ (value.map q.op x) =
      restrictIsom q (fiberDescription T₂ x)
  inclusion : value ⟶ H.value
  pointwiseInjective : ∀ T, Function.Injective (inclusion.app (op T))
  inclusion_fiber : ∀ (T : RelativeTestCategory B)
      (x : value.obj (op T)),
    H.fiberDescription T (inclusion.app (op T) x) =
      (fiberDescription T x).1

/-! ## Hypotheses used by the representability interfaces -/

structure HomRepresentabilityHypotheses {X B : Scheme.{u}} (f : X ⟶ B)
    (F G : X.Modules) where
  finitePresentation :
    AlgebraicGeometry.LocallyOfFinitePresentation f ∧
      AlgebraicGeometry.QuasiCompact f
  F_quasiCoherent : F.IsQuasicoherent
  G_quasiCoherent : G.IsQuasicoherent
  G_finitelyPresented : G.IsFinitePresentation
  G_flatOverBase : Prop
  G_supportProperOverBase : Prop

structure IsomRepresentabilityHypotheses {X B : Scheme.{u}} (f : X ⟶ B)
    (F G : X.Modules) where
  finitePresentation :
    AlgebraicGeometry.LocallyOfFinitePresentation f ∧
      AlgebraicGeometry.QuasiCompact f
  F_finitelyPresented : F.IsFinitePresentation
  G_finitelyPresented : G.IsFinitePresentation
  F_flatOverBase : Prop
  G_flatOverBase : Prop
  F_supportProperOverBase : Prop
  G_supportProperOverBase : Prop

structure QuotRepresentabilityHypotheses {X B : Scheme.{u}} (f : X ⟶ B)
    (F : X.Modules) where
  finitePresentation :
    AlgebraicGeometry.LocallyOfFinitePresentation f ∧
      AlgebraicGeometry.QuasiCompact f
  separated : AlgebraicGeometry.IsSeparated f
  F_quasiCoherent : F.IsQuasicoherent

structure HilbertRepresentabilityHypotheses {X B : Scheme.{u}} (f : X ⟶ B) where
  finitePresentation :
    AlgebraicGeometry.LocallyOfFinitePresentation f ∧
      AlgebraicGeometry.QuasiCompact f
  separated : AlgebraicGeometry.IsSeparated f

structure PicardFunctorHypotheses {X B : Scheme.{u}} (f : X ⟶ B) where
  flat : AlgebraicGeometry.Flat f
  finitePresentation :
    AlgebraicGeometry.LocallyOfFinitePresentation f ∧
      AlgebraicGeometry.QuasiCompact f
  proper : AlgebraicGeometry.IsProper f
  structureSheafPushforwardIso : ∀ T : RelativeTestCategory B, Prop

structure PicardStackHypotheses {X B : Scheme.{u}} (f : X ⟶ B) where
  flat : AlgebraicGeometry.Flat f
  finitePresentation :
    AlgebraicGeometry.LocallyOfFinitePresentation f ∧
      AlgebraicGeometry.QuasiCompact f
  proper : AlgebraicGeometry.IsProper f

structure RelativeMorphismHypotheses
    {Z X B : Scheme.{u}} (z : Z ⟶ B) (f : X ⟶ B) where
  targetSeparated : AlgebraicGeometry.IsSeparated f
  sourceFinitePresentation :
    AlgebraicGeometry.LocallyOfFinitePresentation z ∧
      AlgebraicGeometry.QuasiCompact z
  sourceFlat : AlgebraicGeometry.Flat z
  sourceProper : AlgebraicGeometry.IsProper z

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
  classifiesQuotients :
    RelativeSetClassification value (fun T => RelativeQuotientObject f F T)

structure HilbertFunctorData {X B : Scheme.{u}} (f : X ⟶ B) where
  value : RelativeSetFunctor B
  classifiesClosedSubspaces :
    RelativeSetClassification value (fun T => RelativeHilbertObject f T)

structure PicardFunctorData {X B : Scheme.{u}} (f : X ⟶ B) where
  value : RelativeSetFunctor B
  classifiesInvertibleSheafClasses :
    RelativeSetClassification value
      (fun T => RelativeInvertibleSheafClass f T)

structure PicardStackData {X B : Scheme.{u}} (f : X ⟶ B) where
  stack : RelativeStack B
  objectDescription : ∀ T : RelativeTestCategory B,
    RelativeFiber stack.value T → RelativeInvertibleSheafRepresentative f T
  essentiallySurjective : ∀ (T : RelativeTestCategory B)
    (L : RelativeInvertibleSheafRepresentative f T),
    ∃ x : RelativeFiber stack.value T,
      Nonempty ((objectDescription T x).module ≅ L.module)
  homDescription : ∀ (T : RelativeTestCategory B)
    (x y : RelativeFiber stack.value T),
    Nonempty ((x ⟶ y) ≃
      { φ : (objectDescription T x).module ⟶ (objectDescription T y).module //
          IsIso φ })

structure RelativeMorphismFunctorData
    {Z X B : Scheme.{u}} (z : Z ⟶ B) (f : X ⟶ B) where
  value : RelativeSetFunctor B
  classifiesRelativeMorphisms :
    RelativeSetClassification value (fun T => RelativeMorphismObject z f T)

structure CoherentSheafStackData {X B : Scheme.{u}} (f : X ⟶ B) where
  stack : RelativeStack B
  objectDescription : ∀ T : RelativeTestCategory B,
    RelativeFiber stack.value T → RelativeCoherentSheafObject f T
  essentiallySurjective : ∀ (T : RelativeTestCategory B)
    (M : RelativeCoherentSheafObject f T),
    ∃ x : RelativeFiber stack.value T,
      Nonempty ((objectDescription T x).module ≅ M.module)
  homDescription : ∀ (T : RelativeTestCategory B)
    (x y : RelativeFiber stack.value T),
    Nonempty ((x ⟶ y) ≃
      { φ : (objectDescription T x).module ⟶ (objectDescription T y).module //
          IsIso φ })

structure SpacesStackData (B : Scheme.{u}) where
  stack : RelativeStack B
  objectDescription : ∀ T : RelativeTestCategory B,
    RelativeFiber stack.value T → RelativeFlatProperFamily B T
  essentiallySurjective : ∀ (T : RelativeTestCategory B)
    (X : RelativeFlatProperFamily B T),
    ∃ x : RelativeFiber stack.value T,
      Nonempty (RelativeFamilyIso (objectDescription T x) X)
  homDescription : ∀ (T : RelativeTestCategory B)
    (x y : RelativeFiber stack.value T),
    Nonempty ((x ⟶ y) ≃
      RelativeFamilyIso (objectDescription T x) (objectDescription T y))

structure PolarizedStackData (B : Scheme.{u}) where
  stack : RelativeStack B
  objectDescription : ∀ T : RelativeTestCategory B,
    RelativeFiber stack.value T → RelativePolarizedFamily B T
  essentiallySurjective : ∀ (T : RelativeTestCategory B)
    (X : RelativePolarizedFamily B T),
    ∃ x : RelativeFiber stack.value T,
      Nonempty (RelativeFamilyIso
        (objectDescription T x).toRelativeFlatProperFamily
        X.toRelativeFlatProperFamily)
  homDescription : ∀ (T : RelativeTestCategory B)
    (x y : RelativeFiber stack.value T),
    Nonempty ((x ⟶ y) ≃
      RelativeFamilyIso
        (objectDescription T x).toRelativeFlatProperFamily
        (objectDescription T y).toRelativeFlatProperFamily)

structure CurvesStackData (B : Scheme.{u}) where
  stack : RelativeStack B
  objectDescription : ∀ T : RelativeTestCategory B,
    RelativeFiber stack.value T → RelativeCurveFamily B T
  essentiallySurjective : ∀ (T : RelativeTestCategory B)
    (X : RelativeCurveFamily B T),
    ∃ x : RelativeFiber stack.value T,
      Nonempty (RelativeFamilyIso
        (objectDescription T x).toRelativeFlatProperFamily
        X.toRelativeFlatProperFamily)
  homDescription : ∀ (T : RelativeTestCategory B)
    (x y : RelativeFiber stack.value T),
    Nonempty ((x ⟶ y) ≃
      RelativeFamilyIso
        (objectDescription T x).toRelativeFlatProperFamily
        (objectDescription T y).toRelativeFlatProperFamily)

structure ComplexesStackData {X B : Scheme.{u}} (f : X ⟶ B) where
  stack : RelativeStack B
  objectDescription : ∀ T : RelativeTestCategory B,
    RelativeFiber stack.value T → RelativePerfectComplexFamily f T
  essentiallySurjective : ∀ (T : RelativeTestCategory B)
    (C : RelativePerfectComplexFamily f T),
    ∃ x : RelativeFiber stack.value T, objectDescription T x = C

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
  sheafCondition :
    Formalization.Books.Stacks.Unit01.Stack S.value
      (Formalization.Books.SpacesGroupoids.Unit22.FppfTopology B)
  limitPreservation : Prop
  rimSchlessinger : Prop
  finiteDimensionalTangentSpaces : Prop
  opennessOfVersality : Prop

structure PolarizedFormalEffectivenessData {B : Scheme.{u}}
    (P : PolarizedStackData B) where
  compatibleFormalFamiliesAlgebraize : Prop

/-! An algebraic-stack witness contains the representability and
deformation-theoretic interfaces that the introduction invokes. -/
structure AlgebraicStackPresentation (B : Scheme.{u}) where
  stack : RelativeStack B
  diagonalRepresentable : RelativeDiagonalRepresentable stack
  artinAxioms : ArtinAxiomsWithoutFormalEffectiveness stack
  formalEffectiveness : Prop

def IsAlgebraicRelativeStack {B : Scheme.{u}} (F : RelativeStack B) : Prop :=
  ∃ A : AlgebraicStackPresentation B,
    Nonempty (A.stack.value ≅ F.value)

end Formalization.Books.Quot.Unit01
