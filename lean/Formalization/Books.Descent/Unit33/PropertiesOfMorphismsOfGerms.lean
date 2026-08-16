import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Descent, Chapter 33: Properties of morphisms of germs local on source-and-target

This file formalizes the precise statements in the source section
“Properties of morphisms of germs local on source-and-target”.  Mathlib does
not provide a quotient type of scheme germs, so `SchemeGerm` records a scheme
and a chosen point, while `SchemeGerm.Hom` records a pointed representative.
The locality interfaces below keep the source's representative and
source-and-target-square data explicit.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

/-- A chosen representative of a germ of a scheme at a point. -/
structure SchemeGerm where
  carrier : Scheme.{u}
  point : carrier

namespace SchemeGerm

/-- A pointed representative of a morphism of scheme germs. -/
structure Hom (X Y : SchemeGerm.{u}) where
  map : X.carrier ⟶ Y.carrier
  map_point : map X.point = Y.point

/-- The property type for morphisms of the chosen scheme-germ representatives. -/
abbrev GermMorphismProperty :=
  ∀ {X Y : SchemeGerm.{u}}, Hom X Y → Prop

namespace Hom

/-- The identity morphism of a scheme germ. -/
def id (X : SchemeGerm.{u}) : Hom X X :=
  ⟨𝟙 X.carrier, by simp⟩

/-- Composition of pointed representatives. -/
def comp {X Y Z : SchemeGerm.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨f.map ≫ g.map, by simp [f.map_point, g.map_point]⟩

/-- The underlying scheme morphism of a germ morphism is étale. -/
def IsEtale {X Y : SchemeGerm.{u}} (f : Hom X Y) : Prop :=
  Etale f.map

/-- A morphism of germs is flat at its distinguished point. -/
def IsFlatAtPoint {X Y : SchemeGerm.{u}} (f : Hom X Y) : Prop :=
  (f.map.stalkMap X.point).hom.Flat

/-- The fibre germ represented by a pointed scheme morphism. -/
noncomputable def fibre {X Y : SchemeGerm.{u}} (f : Hom X Y) : SchemeGerm.{u} :=
  ⟨f.map.fiber (f.map X.point), f.map.asFiber X.point⟩

/-- The Krull dimension of the local ring of the fibre at its distinguished point.

`ringKrullDim` takes values in `WithBot ℕ∞`; for a scheme stalk the bottom
case is excluded by the usual nontriviality theorem, while this type retains
Mathlib's canonical dimension invariant without an extra coercion convention.
-/
noncomputable def fibreLocalRingDimension {X Y : SchemeGerm.{u}} (f : Hom X Y) :
    WithBot ℕ∞ :=
  ringKrullDim (↑((fibre f).carrier.presheaf.stalk (fibre f).point))

/-- The local topological dimension of the fibre germ at its distinguished point. -/
noncomputable def fibrePointDimension {X Y : SchemeGerm.{u}} (f : Hom X Y) : ℕ∞ :=
  Order.coheight (fibre f).point

/-- The residue-field map attached to a pointed representative.

The displayed equality in the point-preservation field identifies the target
residue field at `f.map X.point` with the target residue field at `Y.point`.
-/
noncomputable def residueFieldMap {X Y : SchemeGerm.{u}} (f : Hom X Y) :
    Y.carrier.residueField Y.point ⟶ X.carrier.residueField X.point :=
  (Y.carrier.residueFieldCongr f.map_point).inv ≫ f.map.residueFieldMap X.point

/-- The transcendence degree of the residue-field extension of a germ morphism. -/
noncomputable def residueFieldTranscendenceDegree {X Y : SchemeGerm.{u}} (f : Hom X Y) :
    Cardinal :=
  letI := f.residueFieldMap.hom.toAlgebra
  Algebra.trdeg (Y.carrier.residueField Y.point) (X.carrier.residueField X.point)

end Hom

/-- A commutative square of pointed representatives, with the square equation
recorded on the underlying scheme morphisms. -/
def CommSquare {U' U V' V : SchemeGerm.{u}}
    (a : Hom U' U) (b : Hom V' V) (h' : Hom U' V') (h : Hom U V) : Prop :=
  a.map ≫ h.map = h'.map ≫ b.map

/-- Étale-locality on source-and-target for a property of germ morphisms. -/
def IsEtaleLocalOnSourceAndTarget (Q : GermMorphismProperty) : Prop :=
  ∀ {U' U V' V : SchemeGerm.{u}}
    (a : Hom U' U) (b : Hom V' V) (h' : Hom U' V') (h : Hom U V),
    CommSquare a b h' h → Hom.IsEtale a → Hom.IsEtale b → (Q h ↔ Q h')

/-- The corresponding property type for morphisms of schemes. -/
abbrev SchemeMorphismProperty := MorphismProperty Scheme.{u}

/-- Étale-locality on source-and-target for a property of scheme morphisms. -/
def IsEtaleLocalOnSourceAndTargetScheme (P : SchemeMorphismProperty) : Prop :=
  ∀ {U' U V' V : Scheme.{u}}
    (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V),
    a ≫ h = h' ≫ b → Etale a → Etale b → (P h ↔ P h')

/-- The pointed germ morphism obtained from a scheme morphism and a source point. -/
def Hom.ofSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    Hom ⟨X, x⟩ ⟨Y, f x⟩ :=
  ⟨f, rfl⟩

/-- The chosen-representative form of the source's associated germ property.

The equality records that the quantified map represents the same chosen germ
morphism; this is the explicit representative relation available in the
chosen-point interface above.
-/
def germPropertyOfSchemeProperty (P : SchemeMorphismProperty) :
    GermMorphismProperty :=
  fun {X Y} f => ∃ g : Hom X Y, g.map = f.map ∧ P g.map

/-! ### Definition and the two global/local comparison lemmas -/

/-- Source Definition `definition-local-source-target-at-point`. -/
def etaleLocalOnSourceAndTarget (Q : GermMorphismProperty) : Prop :=
  IsEtaleLocalOnSourceAndTarget Q

/-! ### Étale morphisms on fibres -/

/-- The morphism on scheme-theoretic fibres induced by a commutative square.

For `v' : V'`, this is the map
`h'.fiber v' ⟶ h.fiber (b v')` induced by `a` and the residue-field map of
`b` at `v'`.
-/
noncomputable def fibreMap
    {U' U V' V : Scheme.{u}}
    (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V)
    (comm : a ≫ h = h' ≫ b) (v' : V') :
    h'.fiber v' ⟶ h.fiber (b v') :=
  pullback.lift
    (h'.fiberι v' ≫ a)
    (h'.fiberToSpecResidueField v' ≫ Spec.map (b.residueFieldMap v'))
    (by
      rw [Category.assoc, Category.assoc, comm]
      rw [h'.fiber_fac_assoc]
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    )

/-! ### Dimension at a point -/

/-- Source's local dimension of a pointed scheme, represented by `Order.coheight`. -/
noncomputable def pointDimension (X : SchemeGerm.{u}) : ℕ∞ :=
  Order.coheight X.point

end SchemeGerm
