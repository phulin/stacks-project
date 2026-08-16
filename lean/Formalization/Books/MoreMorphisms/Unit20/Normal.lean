import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# More on Morphisms, Chapter 20: Normal morphisms

This file formalizes the definitions and theorem interfaces in the source
section “Normal morphisms”.  Proofs belong to a later stage.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-!
## Normal schemes and geometric normality
-/

/-- The local ring of a point of a scheme is a normal domain. -/
def IsNormalAt (X : Scheme.{u}) (x : X) : Prop :=
  IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- A scheme is normal when all of its local rings are normal domains. -/
def IsNormal (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsNormalAt X x

/--
`X` is geometrically normal at `x` over the field represented by `S` if every
field-valued base change and every point above `x` has a normal local ring.

The quantification over maps from spectra of fields is the scheme-theoretic
form of quantifying over field extensions of the ground field.
-/
def GeometricallyNormalAt {S : CommRingCat.{u}} [Field S]
    {X : Scheme.{u}} (f : X ⟶ Spec S) (x : X) : Prop :=
  ∀ (K : Type u) [Field K] (g : Spec (.of K) ⟶ Spec S),
    let X' : Scheme.{u} := Limits.pullback f g
    ∀ (x' : X'),
      Limits.pullback.fst f g x' = x → IsNormalAt X' x'

/-- A scheme over a field is geometrically normal at every point. -/
def GeometricallyNormal {S : CommRingCat.{u}} [Field S]
    {X : Scheme.{u}} (f : X ⟶ Spec S) : Prop :=
  ∀ x : X, GeometricallyNormalAt f x

/-!
## Pointwise morphism conditions
-/

/-- A morphism is flat at `x` when its map on stalks at `x` is flat. -/
def FlatAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat

/-- A morphism is normal at `x` when it is flat there and its fibre is
geometrically normal at the corresponding point. -/
def NormalAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  FlatAt f x ∧
    GeometricallyNormalAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)

/-- Every fibre of `f` is a locally Noetherian scheme. -/
def LocallyNoetherianFibers : MorphismProperty Scheme.{u} :=
  fun _ _ f => ∀ y, IsLocallyNoetherian (f.fiber y)

/-!
## Definition and characterization
-/

/-- A normal morphism has locally Noetherian fibres and is normal at every
point. -/
def Normal : MorphismProperty Scheme.{u} :=
  fun _ _ f => LocallyNoetherianFibers f ∧ ∀ x, NormalAt f x

/-- Under the locally Noetherian-fibre hypothesis, normality is equivalent to
flatness and geometrically normal fibres. -/
theorem normal_iff_flat_and_geometricallyNormal_fibers
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : LocallyNoetherianFibers f) :
    Normal f ↔ Flat f ∧ ∀ y : Y,
      GeometricallyNormal (f.fiberToSpecResidueField y) := by
  sorry

/-!
## Smooth morphisms
-/

/-- Smooth morphisms are normal. -/
theorem smooth_normal {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    Normal f := by
  sorry

/-!
## Locality
-/

/-- Having locally Noetherian fibres is local for the fppf topology on both
the source and the target. -/
theorem locallyNoetherianFibers_isLocal_fppf :
    LocallyNoetherianFibers.IsLocalAtTarget Scheme.fppfPrecoverage ∧
      LocallyNoetherianFibers.IsLocalAtSource Scheme.fppfPrecoverage := by
  sorry

/-- The property of having locally Noetherian fibres and being normal is local
for the fppf topology on the target and for the smooth topology on the source.
Here the smooth topology is represented by the precoverage of smooth maps.
-/
theorem normal_isLocal_fppf_target_smooth_source :
    Normal.IsLocalAtTarget Scheme.fppfPrecoverage ∧
      Normal.IsLocalAtSource (MorphismProperty.precoverage @Smooth) := by
  sorry

end AlgebraicGeometry
