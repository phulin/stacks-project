import Formalization.«Books.SpacesGroupoids».Unit17.Core

/-!
# Groupoids in Algebraic Spaces, Chapter 17: restricting groupoids

This file formalizes the pullback construction in the source section.  The
three factors of the restricted arrow space are kept visible through the two
corner pullbacks and their pullback over the original arrow space; this makes
the source, target, and comparison maps usable in later chapters.
-/

namespace Formalization.«Books.SpacesGroupoids».Unit17

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace GroupoidInAlgebraicSpaces

variable {S : AlgebraicSpace} {B : AlgebraicSpaceOver S}

open AlgebraicSpaceRelation

/-- The upper-left corner `R ×_{s,U} U'` of the restriction diagram. -/
abbrev restrictionSourceCorner (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :=
  pullback G.source g

/-- The lower-left corner `U' ×_{U,t} R` of the restriction diagram. -/
abbrev restrictionTargetCorner (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :=
  pullback g G.target

/-- The restricted arrow space, as the pullback of the two corners over `R`.

Equivalently this is
`U' ×_{g,t} R ×_{s,g} U'`, with the middle factor `R` retained as the
comparison map to the original groupoid.
-/
abbrev restrictionArrowSpace (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :=
  pullback
    (pullback.fst G.source g)
    (pullback.snd g G.target)

/-- The source map `s' : R' → U'`. -/
noncomputable def restrictionSource (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionArrowSpace G U' g ⟶ U' :=
  pullback.fst (pullback.fst G.source g) (pullback.snd g G.target) ≫
    pullback.snd G.source g

/-- The target map `t' : R' → U'`. -/
noncomputable def restrictionTarget (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionArrowSpace G U' g ⟶ U' :=
  pullback.snd (pullback.fst G.source g) (pullback.snd g G.target) ≫
    pullback.fst g G.target

/-- The canonical comparison `R' → R`. -/
noncomputable def restrictionArrowMap (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionArrowSpace G U' g ⟶ G.arrowSpace :=
  pullback.fst (pullback.fst G.source g) (pullback.snd g G.target) ≫
    pullback.fst G.source g

/-- The same comparison map through the lower-left corner. -/
noncomputable def restrictionArrowMap' (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionArrowSpace G U' g ⟶ G.arrowSpace :=
  pullback.snd (pullback.fst G.source g) (pullback.snd g G.target) ≫
    pullback.snd g G.target

@[simp]
theorem restriction_arrow_map_eq (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionArrowMap G U' g = restrictionArrowMap' G U' g := by
  exact pullback.condition

@[reassoc]
theorem restriction_source_compatibility (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionArrowMap G U' g ≫ G.source =
      restrictionSource G U' g ≫ g := by
  simp only [restrictionArrowMap, restrictionSource, Category.assoc]
  rw [pullback.condition]

@[reassoc]
theorem restriction_target_compatibility (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionArrowMap G U' g ≫ G.target =
      restrictionTarget G U' g ≫ g := by
  simp only [restrictionArrowMap, restrictionTarget, Category.assoc]
  calc
    pullback.fst (pullback.fst G.source g) (pullback.snd g G.target) ≫
          pullback.fst G.source g ≫ G.target =
        pullback.snd (pullback.fst G.source g) (pullback.snd g G.target) ≫
          pullback.snd g G.target ≫ G.target := by
            simpa only [Category.assoc] using
              congrArg (fun q => q ≫ G.target)
                (pullback.condition :
                  pullback.fst (pullback.fst G.source g) (pullback.snd g G.target) ≫
                      pullback.fst G.source g =
                    pullback.snd (pullback.fst G.source g) (pullback.snd g G.target) ≫
                      pullback.snd g G.target)
    _ = pullback.snd (pullback.fst G.source g) (pullback.snd g G.target) ≫
          pullback.fst g G.target ≫ g := by
            simpa only [Category.assoc] using
              congrArg (fun q =>
                pullback.snd (pullback.fst G.source g) (pullback.snd g G.target) ≫ q)
                (pullback.condition :
                  pullback.fst g G.target ≫ g =
                    pullback.snd g G.target ≫ G.target).symm

/-- The restricted composable-pair space. -/
abbrev restrictionComposable (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :=
  pullback (restrictionSource G U' g) (restrictionTarget G U' g)

/-- The map of restricted composable pairs to the original composable pairs. -/
noncomputable def restrictionComposableMap (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionComposable G U' g ⟶ G.composable :=
  pullback.lift
    (pullback.fst (restrictionSource G U' g) (restrictionTarget G U' g) ≫
      restrictionArrowMap G U' g)
    (pullback.snd (restrictionSource G U' g) (restrictionTarget G U' g) ≫
      restrictionArrowMap G U' g)
    (by
      calc
        (pullback.fst (restrictionSource G U' g) (restrictionTarget G U' g) ≫
            restrictionArrowMap G U' g) ≫ G.source =
            pullback.fst (restrictionSource G U' g) (restrictionTarget G U' g) ≫
              (restrictionArrowMap G U' g ≫ G.source) := by
                simp only [Category.assoc]
        _ = pullback.fst (restrictionSource G U' g) (restrictionTarget G U' g) ≫
              (restrictionSource G U' g ≫ g) := by
                rw [restriction_source_compatibility]
        _ = pullback.snd (restrictionSource G U' g) (restrictionTarget G U' g) ≫
              (restrictionTarget G U' g ≫ g) := by
                simpa only [Category.assoc] using
                  congrArg (fun q => q ≫ g) pullback.condition
        _ = (pullback.snd (restrictionSource G U' g) (restrictionTarget G U' g) ≫
            restrictionArrowMap G U' g) ≫ G.target := by
                calc
                  pullback.snd (restrictionSource G U' g) (restrictionTarget G U' g) ≫
                        (restrictionTarget G U' g ≫ g) =
                      pullback.snd (restrictionSource G U' g)
                        (restrictionTarget G U' g) ≫
                        (restrictionArrowMap G U' g ≫ G.target) := by
                          exact congrArg (fun q =>
                            pullback.snd (restrictionSource G U' g)
                              (restrictionTarget G U' g) ≫ q)
                            (restriction_target_compatibility G U' g).symm
                  _ = (pullback.snd (restrictionSource G U' g)
                        (restrictionTarget G U' g) ≫
                        restrictionArrowMap G U' g) ≫ G.target := by
                          simp only [Category.assoc])

/-- The underlying original arrow of the restricted composite. -/
noncomputable def restrictionCompositionToArrow
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionComposable G U' g ⟶ G.arrowSpace :=
  restrictionComposableMap G U' g ≫ G.composition

@[simp, reassoc]
theorem restrictionComposableMap_fst (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionComposableMap G U' g ≫ G.composableFst =
      pullback.fst (restrictionSource G U' g) (restrictionTarget G U' g) ≫
        restrictionArrowMap G U' g := by
  dsimp [restrictionComposableMap, GroupoidInAlgebraicSpaces.composableFst,
    GroupoidInAlgebraicSpaces.composable]
  exact pullback.lift_fst _ _ _

@[simp, reassoc]
theorem restrictionComposableMap_snd (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionComposableMap G U' g ≫ G.composableSnd =
      pullback.snd (restrictionSource G U' g) (restrictionTarget G U' g) ≫
        restrictionArrowMap G U' g := by
  dsimp [restrictionComposableMap, GroupoidInAlgebraicSpaces.composableSnd,
    GroupoidInAlgebraicSpaces.composable]
  exact pullback.lift_snd _ _ _

/-- The source corner of the restricted composite. -/
noncomputable def restrictionCompositionSourceCorner
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionComposable G U' g ⟶ restrictionSourceCorner G U' g :=
  pullback.lift
    (restrictionCompositionToArrow G U' g)
    (pullback.snd (restrictionSource G U' g) (restrictionTarget G U' g) ≫
      restrictionSource G U' g)
    (by
      calc
        restrictionCompositionToArrow G U' g ≫ G.source =
            restrictionComposableMap G U' g ≫
              (G.composition ≫ G.source) := by
                simp only [restrictionCompositionToArrow, Category.assoc]
        _ = restrictionComposableMap G U' g ≫
              (G.composableSnd ≫ G.source) := by
                rw [G.axioms.source_comp]
        _ = pullback.snd (restrictionSource G U' g) (restrictionTarget G U' g) ≫
              (restrictionSource G U' g ≫ g) := by
                calc
                  restrictionComposableMap G U' g ≫ G.composableSnd ≫ G.source =
                      (pullback.snd (restrictionSource G U' g)
                        (restrictionTarget G U' g) ≫ restrictionArrowMap G U' g) ≫
                        G.source := by
                          rw [restrictionComposableMap_snd_assoc]
                          simp only [Category.assoc]
                  _ = pullback.snd (restrictionSource G U' g)
                        (restrictionTarget G U' g) ≫
                      (restrictionSource G U' g ≫ g) := by
                          simp only [Category.assoc]
                          rw [restriction_source_compatibility])

/-- The target corner of the restricted composite. -/
noncomputable def restrictionCompositionTargetCorner
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionComposable G U' g ⟶ restrictionTargetCorner G U' g :=
  pullback.lift
    (pullback.fst (restrictionSource G U' g) (restrictionTarget G U' g) ≫
      restrictionTarget G U' g)
    (restrictionCompositionToArrow G U' g)
    (by
      calc
        (pullback.fst (restrictionSource G U' g) (restrictionTarget G U' g) ≫
            restrictionTarget G U' g) ≫ g =
            pullback.fst (restrictionSource G U' g) (restrictionTarget G U' g) ≫
              (restrictionTarget G U' g ≫ g) := by simp only [Category.assoc]
        _ = pullback.fst (restrictionSource G U' g) (restrictionTarget G U' g) ≫
              (restrictionArrowMap G U' g ≫ G.target) := by
                rw [restriction_target_compatibility]
        _ = restrictionCompositionToArrow G U' g ≫ G.target := by
                calc
                  pullback.fst (restrictionSource G U' g)
                        (restrictionTarget G U' g) ≫
                      (restrictionArrowMap G U' g ≫ G.target) =
                      (pullback.fst (restrictionSource G U' g)
                        (restrictionTarget G U' g) ≫ restrictionArrowMap G U' g) ≫
                        G.target := by simp only [Category.assoc]
                  _ = restrictionComposableMap G U' g ≫ G.composableFst ≫
                        G.target := by
                          rw [restrictionComposableMap_fst_assoc]
                          simp only [Category.assoc]
                  _ = restrictionCompositionToArrow G U' g ≫ G.target := by
                          simp only [restrictionCompositionToArrow,
                            G.axioms.target_comp, Category.assoc])

/-- The canonical restricted composition law `c'`. -/
noncomputable def restrictionComposition (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionComposable G U' g ⟶ restrictionArrowSpace G U' g :=
  pullback.lift
    (restrictionCompositionSourceCorner G U' g)
    (restrictionCompositionTargetCorner G U' g)
    (by
      simp only [restrictionCompositionSourceCorner,
        restrictionCompositionTargetCorner,
        pullback.lift_fst, pullback.lift_snd])

/-- The identity section into the source corner. -/
noncomputable def restrictionIdentitySourceCorner
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    U' ⟶ restrictionSourceCorner G U' g :=
  pullback.lift (g ≫ G.identity) (𝟙 U') (by
    simp only [Category.assoc, G.axioms.source_identity, Category.id_comp,
      Category.comp_id])

/-- The identity section into the target corner. -/
noncomputable def restrictionIdentityTargetCorner
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    U' ⟶ restrictionTargetCorner G U' g :=
  pullback.lift (𝟙 U') (g ≫ G.identity) (by
    simp only [Category.assoc, G.axioms.target_identity, Category.id_comp,
      Category.comp_id])

/-- The identity section of the restricted groupoid. -/
noncomputable def restrictionIdentity (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    U' ⟶ restrictionArrowSpace G U' g :=
  pullback.lift
    (restrictionIdentitySourceCorner G U' g)
    (restrictionIdentityTargetCorner G U' g)
    (by
      calc
        restrictionIdentitySourceCorner G U' g ≫
            pullback.fst G.source g = g ≫ G.identity := by
              exact pullback.lift_fst _ _ _
        _ = restrictionIdentityTargetCorner G U' g ≫
            pullback.snd g G.target := by
              symm
              exact pullback.lift_snd _ _ _)

/-- The inverse arrow in the source corner. -/
noncomputable def restrictionInverseSourceCorner
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionArrowSpace G U' g ⟶ restrictionSourceCorner G U' g :=
  pullback.lift
    (restrictionArrowMap G U' g ≫ G.inverse)
    (pullback.snd (pullback.fst G.source g) (pullback.snd g G.target) ≫
      pullback.fst g G.target)
    (by
      calc
        (restrictionArrowMap G U' g ≫ G.inverse) ≫ G.source =
            restrictionArrowMap G U' g ≫ G.target := by
              simp only [Category.assoc]
              rw [G.axioms.source_inverse]
        _ = (pullback.snd (pullback.fst G.source g)
              (pullback.snd g G.target) ≫ pullback.fst g G.target) ≫ g := by
              exact restriction_target_compatibility G U' g)

/-- The inverse arrow in the target corner. -/
noncomputable def restrictionInverseTargetCorner
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionArrowSpace G U' g ⟶ restrictionTargetCorner G U' g :=
  pullback.lift
    (pullback.fst (pullback.fst G.source g) (pullback.snd g G.target) ≫
      pullback.snd G.source g)
    (restrictionArrowMap G U' g ≫ G.inverse)
    (by
      calc
        (pullback.fst (pullback.fst G.source g)
              (pullback.snd g G.target) ≫ pullback.snd G.source g) ≫ g =
            restrictionArrowMap G U' g ≫ G.source := by
              exact (restriction_source_compatibility G U' g).symm
        _ = (restrictionArrowMap G U' g ≫ G.inverse) ≫ G.target := by
              simp only [Category.assoc]
              rw [G.axioms.target_inverse])

/-- The inverse map of the restricted groupoid. -/
noncomputable def restrictionInverse (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    restrictionArrowSpace G U' g ⟶ restrictionArrowSpace G U' g :=
  pullback.lift
    (restrictionInverseSourceCorner G U' g)
    (restrictionInverseTargetCorner G U' g)
    (by
      simp only [restrictionInverseSourceCorner, restrictionInverseTargetCorner,
        pullback.lift_fst, pullback.lift_snd])

/-- The raw groupoid data produced by restricting along `g`. -/
noncomputable def restrictionData (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) : GroupoidData S B where
  U := U'
  R := restrictionArrowSpace G U' g
  s := restrictionSource G U' g
  t := restrictionTarget G U' g
  c := restrictionComposition G U' g
  e := restrictionIdentity G U' g
  i := restrictionInverse G U' g

/-- The restriction's groupoid axioms. -/
theorem restriction_axioms (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    GroupoidAxioms (restrictionData G U' g) := by
  sorry

/-- The restricted groupoid in algebraic spaces. -/
noncomputable def restriction (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    GroupoidInAlgebraicSpaces S B where
  toGroupoidData := restrictionData G U' g
  axioms := restriction_axioms G U' g

/-- A source-facing name for the canonical restricted groupoid. -/
noncomputable def restrictGroupoid (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :=
  restriction G U' g

/-- The object and arrow maps of the canonical restriction morphism. -/
noncomputable def restrictionMorphismCore
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    GroupoidMorphismCore (restriction G U' g) G where
  object := g
  arrow := restrictionArrowMap G U' g
  source_commutes := restriction_source_compatibility G U' g
  target_commutes := restriction_target_compatibility G U' g

/-- The composition square for the canonical restriction morphism. -/
theorem restriction_morphism_composition
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    (restrictionMorphismCore G U' g).mapComposable ≫ G.composition =
      (restriction G U' g).composition ≫ restrictionArrowMap G U' g := by
  sorry

/-- The canonical morphism from the restricted groupoid to the original. -/
noncomputable def restrictionMorphism
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    GroupoidMorphism (restriction G U' g) G where
  toGroupoidMorphismCore := restrictionMorphismCore G U' g
  composition_commutes := restriction_morphism_composition G U' g

/-- Lemma `lemma-restrict-groupoid`: the pullback construction gives a
groupoid and a morphism to the original groupoid. -/
noncomputable def restrict_groupoid (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    GroupoidMorphism (restriction G U' g) G :=
  restrictionMorphism G U' g

/-- Proposition form of Lemma `lemma-restrict-groupoid`. -/
theorem restrict_groupoid_exists (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    Nonempty (GroupoidMorphism (restriction G U' g) G) :=
  ⟨restrict_groupoid G U' g⟩

/-- Points of a space over `B` with values in a test object `T`. -/
abbrev point (T X : AlgebraicSpaceOverB B) := T ⟶ X

/-- A pair of pointwise arrows that is composable in a groupoid. -/
abbrev pointwiseComposable (G : GroupoidInAlgebraicSpaces S B)
    (T : AlgebraicSpaceOverB B) :=
  { p : (point T G.arrowSpace) × (point T G.arrowSpace) //
      p.1 ≫ G.source = p.2 ≫ G.target }

/-- Composition of pointwise arrows induced by the internal composition law. -/
noncomputable def pointwiseComposition (G : GroupoidInAlgebraicSpaces S B)
    (T : AlgebraicSpaceOverB B) (p : pointwiseComposable G T) :
    point T G.arrowSpace :=
  pullback.lift p.1.1 p.1.2 p.2 ≫ G.composition

/-- The data carried by a pointwise functor between the presentations of two
groupoids. -/
structure PointwiseFunctorData
    (G H : GroupoidInAlgebraicSpaces S B) (T : AlgebraicSpaceOverB B) where
  onObjects : point T G.objectSpace → point T H.objectSpace
  onArrows : point T G.arrowSpace → point T H.arrowSpace

/-- The source, target, and composition conditions for a pointwise functor. -/
def IsPointwiseFunctor
    {G H : GroupoidInAlgebraicSpaces S B} {T : AlgebraicSpaceOverB B}
    (F : PointwiseFunctorData G H T) : Prop :=
  (∀ r, F.onArrows r ≫ H.source = F.onObjects (r ≫ G.source)) ∧
  (∀ r, F.onArrows r ≫ H.target = F.onObjects (r ≫ G.target)) ∧
  (∀ (p : pointwiseComposable G T)
      (h : F.onArrows p.1.1 ≫ H.source = F.onArrows p.1.2 ≫ H.target),
    F.onArrows (pointwiseComposition G T p) =
      pointwiseComposition H T ⟨(F.onArrows p.1.1, F.onArrows p.1.2), h⟩)

/-- The pointwise object/arrow maps of the canonical restriction morphism. -/
def restrictionPointwiseFunctorData
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace)
    (T : AlgebraicSpaceOverB B) :
    PointwiseFunctorData (restriction G U' g) G T where
  onObjects := fun x => x ≫ g
  onArrows := fun r => r ≫ restrictionArrowMap G U' g

/-- Formula-level meaning of “the restriction” for pointwise functors. -/
def IsRestrictionPointwiseFunctor
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace)
    (T : AlgebraicSpaceOverB B)
    (F : PointwiseFunctorData (restriction G U' g) G T) : Prop :=
  F.onObjects = (fun x => x ≫ g) ∧
    F.onArrows = (fun r => r ≫ restrictionArrowMap G U' g)

/-- The pointwise functor is the restriction of the original pointwise
groupoid along `T ⟶ U' ⟶ U`. -/
theorem restriction_functor_of_points
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace)
    (T : AlgebraicSpaceOverB B) :
    IsPointwiseFunctor (restrictionPointwiseFunctorData G U' g T) ∧
      IsRestrictionPointwiseFunctor G U' g T
        (restrictionPointwiseFunctorData G U' g T) := by
  sorry

/-- The source corner for restricting a relation. -/
abbrev relationSourceCorner
    {U : AlgebraicSpaceOverB B} (Q : AlgebraicSpaceRelation S B U)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ U) :=
  pullback Q.source g

/-- The target corner for restricting a relation. -/
abbrev relationTargetCorner
    {U : AlgebraicSpaceOverB B} (Q : AlgebraicSpaceRelation S B U)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ U) :=
  pullback g Q.target

/-- The relation restriction/pullback `R|_{U'}`. -/
noncomputable def relationRestriction
    {U : AlgebraicSpaceOverB B} (Q : AlgebraicSpaceRelation S B U)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ U) :
    AlgebraicSpaceRelation S B U' where
  arrows := pullback (pullback.fst Q.source g) (pullback.snd g Q.target)
  source :=
    pullback.fst (pullback.fst Q.source g) (pullback.snd g Q.target) ≫
      pullback.snd Q.source g
  target :=
    pullback.snd (pullback.fst Q.source g) (pullback.snd g Q.target) ≫
      pullback.fst g Q.target

/-- The groupoid and relation restriction constructions have the same arrow
space, source, and target maps. -/
theorem restrict_groupoid_relation
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    relationRestriction G.toRelation U' g =
      (restriction G U' g).toRelation := by
  rfl

/-- In particular, the pre-equivalence-relation predicates agree under the
two presentations. -/
theorem restrict_pre_equivalence_relation_iff
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    IsPreEquivalenceRelation (relationRestriction G.toRelation U' g) ↔
      IsPreEquivalenceRelation (restriction G U' g).toRelation := by
  rw [restrict_groupoid_relation]
  rfl

/-- The same compatibility for the source's `(pre-)equivalence relation`
terminology. -/
theorem restrict_equivalence_relation_iff
    (G : GroupoidInAlgebraicSpaces S B)
    (U' : AlgebraicSpaceOverB B) (g : U' ⟶ G.objectSpace) :
    IsEquivalenceRelation (relationRestriction G.toRelation U' g) ↔
      IsEquivalenceRelation (restriction G U' g).toRelation := by
  rw [restrict_groupoid_relation]
  rfl

end GroupoidInAlgebraicSpaces

end

end Formalization.«Books.SpacesGroupoids».Unit17
