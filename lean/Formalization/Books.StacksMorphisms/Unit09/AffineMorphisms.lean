import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Morphisms of Algebraic Stacks, Chapter 9: affine morphisms

The project does not yet contain a native category of algebraic stacks.  The
source-facing interface in this chapter therefore uses `Scheme` as the
available category of representable objects.  In this proxy, representability
by algebraic spaces is built into the choice of morphisms, and
`AlgebraicGeometry.IsAffineHom` is Mathlib's canonical affine-morphism
property.  The categorical pullback statements below are consequently the
same statements used by the stack-level definitions.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace
noncomputable section

namespace Formalization.«Books.StacksMorphisms».Unit09

/-! ### The source-facing stack interface -/

/--
The available proxy for algebraic stacks in this chapter.

Every morphism in this category is representable by a scheme, hence by an
algebraic space; this is why the separate representability conjunct in the
textbook definition is implicit in the proxy.
-/
abbrev AlgebraicStack := Scheme

/-- Morphisms of the source-facing algebraic-stack proxy. -/
abbrev AlgebraicStackMorphism (X Y : AlgebraicStack) := X ⟶ Y

/-! ### Definition -/

/--
The affine morphisms of the chapter.

For the scheme proxy this is exactly Mathlib's affine morphism property; the
representability part of the stack definition is automatic in the proxy.
-/
def Affine {X Y : AlgebraicStack} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsAffineHom f

/-- The source's two descriptions of affine agree in the available proxy. -/
theorem affine_iff_isAffineHom {X Y : AlgebraicStack} (f : X ⟶ Y) :
    Affine f ↔ AlgebraicGeometry.IsAffineHom f :=
  Iff.rfl

/-! ### Base change and composition -/

/-- Affineness is preserved by base change. -/
theorem affine_base_change {X Y Z : AlgebraicStack} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hg : Affine g) : Affine (pullback.snd g f) := by
  change AlgebraicGeometry.IsAffineHom (pullback.snd g f)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.IsAffineHom)
    (self := AlgebraicGeometry.isAffineHom_isStableUnderBaseChange)
    (IsPullback.of_hasPullback g f) hg

/-- Compositions of affine morphisms are affine. -/
theorem affine_composition {X Y Z : AlgebraicStack} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Affine f) (hg : Affine g) : Affine (f ≫ g) := by
  change AlgebraicGeometry.IsAffineHom (f ≫ g)
  constructor
  intro U hU
  rw [Scheme.Hom.comp_base, Opens.map_comp_obj]
  apply AlgebraicGeometry.IsAffineHom.isAffine_preimage (self := hf)
  apply AlgebraicGeometry.IsAffineHom.isAffine_preimage (self := hg)
  exact hU

/-! ### The pullback square used in affine permanence -/

/-- The map `(1, f)` from the source into the pullback in the permanence proof. -/
def affinePermanenceSection {X Y Z : AlgebraicStack}
    (f : X ⟶ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (hcomm : f ≫ b = a) :
    X ⟶ pullback a b :=
  pullback.lift (𝟙 X) f (by simpa using hcomm.symm)

/-- The map from `X ×_Z Y` to `Y ×_Z Y` along which the diagonal is pulled back. -/
def affinePermanenceBaseMap {X Y Z : AlgebraicStack}
    (f : X ⟶ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (hcomm : f ≫ b = a) :
    pullback a b ⟶ pullback b b :=
  pullback.lift (pullback.fst a b ≫ f) (pullback.snd a b) (by
    rw [Category.assoc, hcomm, pullback.condition])

/-- The second projection recovers `f` from the section `(1, f)`. -/
theorem affinePermanenceSection_comp_snd {X Y Z : AlgebraicStack}
    (f : X ⟶ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (hcomm : f ≫ b = a) :
    affinePermanenceSection f a b hcomm ≫ pullback.snd a b = f := by
  exact pullback.lift_snd (𝟙 X) f _

/--
The square expressing that `(1, f)` is the base change of the diagonal of
`b`.  This is the categorical form of the square used in the source proof.
-/
theorem affinePermanenceSection_isPullback {X Y Z : AlgebraicStack}
    (f : X ⟶ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (hcomm : f ≫ b = a) :
    IsPullback (affinePermanenceSection f a b hcomm) f
      (affinePermanenceBaseMap f a b hcomm) (pullback.diagonal b) := by
  let i : pullback (f ≫ b) b ≅ pullback a b := pullback.congrHom hcomm rfl
  have h := pullback_lift_diagonal_isPullback f b
  apply h.flip.of_iso (Iso.refl _) i (Iso.refl _) (Iso.refl _)
  · apply pullback.hom_ext
    · simp [Category.assoc, i, affinePermanenceSection, pullback.map,
        pullback.lift_fst]
    · simp [Category.assoc, i, affinePermanenceSection, pullback.map,
        pullback.lift_snd]
  · simp
  · apply pullback.hom_ext
    · simp [Category.assoc, i, affinePermanenceBaseMap, pullback.map,
        pullback.lift_fst, pullback.lift_fst_assoc]
    · simp [Category.assoc, i, affinePermanenceBaseMap, pullback.map,
        pullback.lift_snd]
  · simp

/-! ### Affine permanence -/

/--
In a commutative triangle, if `a` is affine and the diagonal of `b` is
affine, then `f` is affine.
-/
theorem affine_permanence {X Y Z : AlgebraicStack}
    (f : X ⟶ Y) (a : X ⟶ Z) (b : Y ⟶ Z)
    (hcomm : f ≫ b = a) (ha : Affine a)
    (hdiagonal : Affine (pullback.diagonal b)) : Affine f := by
  have hbase : Affine (pullback.snd a b) := affine_base_change b a ha
  have hsection : Affine (affinePermanenceSection f a b hcomm) := by
    change AlgebraicGeometry.IsAffineHom (affinePermanenceSection f a b hcomm)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsAffineHom)
      (self := AlgebraicGeometry.isAffineHom_isStableUnderBaseChange)
      (affinePermanenceSection_isPullback f a b hcomm).flip hdiagonal
  have hcomp : Affine
      (affinePermanenceSection f a b hcomm ≫ pullback.snd a b) :=
    affine_composition _ _ hsection hbase
  rw [affinePermanenceSection_comp_snd f a b hcomm] at hcomp
  exact hcomp

end Formalization.«Books.StacksMorphisms».Unit09
