import Formalization.Books.Schemes.Unit06.AffineSchemes
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Data.Complex.Basic
import Mathlib.Order.KrullDimension
import Mathlib.Topology.Separation.Basic

/-!
# Exercises, Chapter 33: Schemes

This file contains the reusable definitions and concrete categorical
constructions occurring in the chapter.  Scheme-theoretic notions are taken
from Mathlib; the few predicates below are the source-facing formulations
which concern arbitrary locally ringed spaces or the textbook's examples.
-/

namespace Formalization.Books.Exercises.Unit33

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.StructureSheaf
open Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u v

noncomputable section

/-! ## Schemes, affine opens, and point-counting predicates -/

abbrev LocallyRingedSpace := AlgebraicGeometry.LocallyRingedSpace

abbrev affineLocallyRingedSpace :=
  Formalization.Books.Schemes.Unit06.IsAffineLocallyRingedSpace

abbrev affineLocallyRingedSpaceOpen :=
  Formalization.Books.Schemes.Unit06.IsAffineLocallyRingedSpaceOpen

/-- Global sections of a scheme, using the earlier chapter's canonical
contravariant global-sections functor. -/
abbrev schemeGlobalSections (X : Scheme.{u}) : CommRingCat.{u} :=
  Formalization.Books.Schemes.Unit06.locallyRingedSpaceGlobalSections
    X.toLocallyRingedSpace

/-- A locally ringed space satisfies the textbook's local definition of a
scheme when every point has an affine open neighbourhood. -/
def IsSchemeLocallyRingedSpace (X : LocallyRingedSpace.{u}) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ affineLocallyRingedSpaceOpen X U

/-- A finite discrete underlying space. -/
def IsFiniteDiscrete (X : Scheme.{u}) : Prop :=
  Finite X ∧ DiscreteTopology X

/-- The underlying space has exactly two points. -/
def IsTwoPoint (X : Scheme.{u}) : Prop :=
  ∃ x y : X, x ≠ y ∧ ∀ z : X, z = x ∨ z = y

/-- The underlying space has exactly three points. -/
def IsThreePoint (X : Scheme.{u}) : Prop :=
  ∃ x y z : X, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ∀ w : X, w = x ∨ w = y ∨ w = z

/-- A scheme has a closed point when some singleton is closed. -/
def HasClosedPoint (X : Scheme.{u}) : Prop :=
  ∃ x : X, IsClosed ({x} : Set X)

/-! ## Open subschemes and immersions -/

/-- The scheme obtained by restricting a scheme to an open subset. -/
abbrev openSubscheme (X : Scheme.{u}) (U : Opens X) : Scheme.{u} :=
  X.restrict U.isOpenEmbedding

/-- The canonical open immersion of an open subscheme. -/
abbrev openSubschemeInclusion (X : Scheme.{u}) (U : Opens X) :
    openSubscheme X U ⟶ X :=
  X.ofRestrict U.isOpenEmbedding

/-- A ringed-space morphism is induced by a locally ringed-space morphism. -/
def IsLocallyRingedSpaceMorphism
    {X Y : LocallyRingedSpace.{u}}
    (f : X.toRingedSpace ⟶ Y.toRingedSpace) : Prop :=
  ∃ g : X ⟶ Y, g.toShHom = f

/-! ## Closed subscheme extension data -/

/-- Data expressing that a closed subscheme of an open subscheme extends to a
closed subscheme of the ambient scheme.  The comparison is the canonical
pullback of the ambient closed immersion to the open subscheme. -/
structure ClosedSubschemeExtension
    (X : Scheme.{u}) (U : Opens X)
    (Z : Scheme.{u}) (i : Z ⟶ openSubscheme X U) where
  ambient : Scheme.{u}
  inclusion : ambient ⟶ X
  inclusion_closed : IsClosedImmersion inclusion
  comparison : Z ≅ pullback inclusion (openSubschemeInclusion X U)
  comparison_fac :
    comparison.hom ≫ pullback.snd inclusion (openSubschemeInclusion X U) = i

/-- A source-faithful package for the hard closed-subscheme example. -/
structure ClosedSubschemeNonExtensionExample where
  ambient : Scheme.{u}
  openSet : Opens ambient
  closed : Scheme.{u}
  inclusion : closed ⟶ openSubscheme ambient openSet
  inclusion_closed : @AlgebraicGeometry.IsClosedImmersion _ _ inclusion
  no_extension : ¬ Nonempty
    (ClosedSubschemeExtension ambient openSet closed inclusion)

/-! ## Finite type and integral schemes -/

/-- The standard finite-type condition: locally of finite type and
quasi-compact.  Mathlib exposes these two canonical properties separately. -/
def IsFiniteTypeMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.LocallyOfFiniteType f ∧ AlgebraicGeometry.QuasiCompact f

/-!
The textbook definition of an integral scheme is recorded directly.  The
affine-open hypothesis uses the earlier chapter's canonical locally ringed
space formulation, while sections are Mathlib's global sections of the
restricted scheme.
-/
def IsIntegralScheme (X : Scheme.{u}) : Prop :=
  Nonempty X ∧
    ∀ (U : Opens X), (U : Set X).Nonempty →
      affineLocallyRingedSpaceOpen X.toLocallyRingedSpace U →
        IsDomain (schemeGlobalSections (openSubscheme X U) : Type u)

/-! ## Dimension and the base-change objects in the final exercises -/

/-- Krull dimension of the specialization preorder on the points of a scheme. -/
def SchemeDimension (X : Scheme.{u}) :=
  letI := specializationPreorder X
  Order.krullDim X

/-- Krull dimension of the ideal lattice of a commutative ring. -/
def RingKrullDimension (R : Type u) [CommRing R] :=
  Order.krullDim (Ideal R)

/-- The rational affine scheme used in the geometric-integrality exercise. -/
abbrev rationalSpectrum : Scheme.{0} :=
  Scheme.Spec.obj (op (CommRingCat.of ℚ))

/-- The complex affine scheme used in the geometric-integrality exercise. -/
abbrev complexSpectrum : Scheme.{0} :=
  Scheme.Spec.obj (op (CommRingCat.of ℂ))

/-- The canonical morphism `Spec(ℂ) ⟶ Spec(ℚ)`. -/
def complexToRational : complexSpectrum ⟶ rationalSpectrum :=
  Scheme.Spec.map (op (CommRingCat.ofHom (algebraMap ℚ ℂ)))

/-- The base-change map `Spec(k') ⟶ Spec(k)` for a field extension. -/
def fieldSpectrumMap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Scheme.Spec.obj (op (CommRingCat.of k')) ⟶
  Scheme.Spec.obj (op (CommRingCat.of k)) :=
  Scheme.Spec.map (op (CommRingCat.ofHom (algebraMap k k')))

/-- The geometric base change of a scheme over `Spec(k)`. -/
abbrev fieldBaseChange (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (V : Scheme.{u})
    (v : V ⟶ Scheme.Spec.obj (op (CommRingCat.of k))) : Scheme.{u} :=
  pullback (fieldSpectrumMap k k') v

end

end Formalization.Books.Exercises.Unit33
