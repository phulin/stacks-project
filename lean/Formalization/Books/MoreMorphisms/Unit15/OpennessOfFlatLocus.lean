import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# More on Morphisms, §15: Openness of the flat locus

This section records the openness of the flat locus for a locally finitely
presented morphism and module, together with its stalkwise base-change
criterion.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-
The local-ring formulation is the canonical stalkwise meaning of a morphism
being flat at a point.  `Flat.stalkMap` supplies the corresponding result for
a globally flat morphism.
-/
def FlatAt (f : X ⟶ Y) (x : X) : Prop :=
  letI := Module.compHom (X.presheaf.stalk x) (f.stalkMap x).hom
  Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

end Scheme.Hom

namespace Scheme.Modules

variable {X Y : Scheme.{u}}

/-
Mathlib's `IsFinitePresentation` for a sheaf of modules is the established
quasi-coherent, locally finite-presentation interface used below.  The
stalkwise module structure is provided by `ModuleCat.Stalk`, and the
`Module.compHom` makes it a module over the base stalk.
-/
def FlatAt (M : X.Modules) (f : X ⟶ Y) (x : X) : Prop :=
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
    let N : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := M.val
    change Module (X.presheaf.stalk x)
      (@TopCat.Presheaf.stalk (AddCommGrpCat.{u}) _ _ (X : TopCat.{u}) N.presheaf x)
    infer_instance
  letI := Module.compHom (M.presheaf.stalk x) (f.stalkMap x).hom
  Module.Flat (Y.presheaf.stalk (f x)) (M.presheaf.stalk x)

/-- The set of points where `M` is flat over the base of `f`. -/
def flatLocus (M : X.Modules) (f : X ⟶ Y) : Set X :=
  {x | M.FlatAt f x}

/-!
The affine reduction in the source proof is supplied by Mathlib's local
finite-presentation and stalk APIs; the substantive openness assertion is
left for the proof stage.
-/
theorem isOpen_flatLocus (M : X.Modules) (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [M.IsFinitePresentation] :
    IsOpen (M.flatLocus f) := by
  sorry

end Scheme.Modules

section BaseChange

variable {X X' Y Y' : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-!
The following two declarations are the two assertions in the source lemma,
with `IsPullback g' f' f g` expressing its cartesian square and
`Scheme.Modules.pullback g'` expressing `(g')^*`.
-/

lemma flatAt_pullback (h : IsPullback g' f' f g) (M : X.Modules) (x' : X')
    (hx : M.FlatAt f (g' x')) :
    ((Scheme.Modules.pullback g').obj M).FlatAt f' x' := by
  sorry

lemma flatAt_of_flatAt_pullback (h : IsPullback g' f' f g) (M : X.Modules) (x' : X')
    (hg : g.FlatAt (f' x'))
    (hx' : ((Scheme.Modules.pullback g').obj M).FlatAt f' x') :
    M.FlatAt f (g' x') := by
  sorry

/-!
When the base change is globally flat, the two stalkwise implications give
the source's statement that the flat-locus open subset commutes with base
change.
-/
theorem flatLocus_pullback_eq_preimage (h : IsPullback g' f' f g) (M : X.Modules)
    [Flat g] [LocallyOfFinitePresentation f] [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback g').obj M).flatLocus f' = g' ⁻¹' M.flatLocus f := by
  sorry

end BaseChange
