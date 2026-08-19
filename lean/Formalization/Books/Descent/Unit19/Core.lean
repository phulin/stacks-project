import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Properties

/-!
# Descent, Chapter 19: Variants on descending properties

This file contains the presentation-level interface needed by the regularity
statement. Scheme predicates are Mathlib predicates; Mathlib has no native
algebraic-space object in this snapshot, so the regularity statement uses the
small explicit interface below.
-/

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Formalization.Books.Descent.Unit19

/-! ## Supporting algebraic-space interface -/

namespace AlgebraicSpaceInterface

/-- The minimal algebraic-space interface needed by the regularity lemma. -/
structure Space where
  carrier : Type u
  [topology : TopologicalSpace carrier]
  regular : Prop

attribute [instance] Space.topology

/-- A morphism of algebraic spaces, with the three predicates used in the source. -/
structure Hom (X Y : Space.{u}) where
  map : ContinuousMap X.carrier Y.carrier
  locallyOfFinitePresentation : Prop
  flat : Prop
  surjective : Prop

def IsRegular (X : Space.{u}) : Prop := X.regular
def IsLocallyOfFinitePresentation {X Y : Space.{u}} (f : Hom X Y) : Prop :=
  f.locallyOfFinitePresentation
def IsFlat {X Y : Space.{u}} (f : Hom X Y) : Prop := f.flat
def IsSurjective {X Y : Space.{u}} (f : Hom X Y) : Prop := f.surjective

end AlgebraicSpaceInterface

/-
PRIOR ATTEMPT: The declarations below were retained from a broader draft that
also covered later sections of Descent. They are kept verbatim for proof
history, but are not part of Chapter 19 and are intentionally commented out.

/-! ## Topologies, covers, and pullbacks -/

/-- The six topologies appearing in Chapter 19. -/
inductive Topology
  | fpqc | fppf | syntomic | smooth | etale | zariski
deriving DecidableEq, Repr

/-- A presentation witness for a local complete-intersection ring.

This is the local-ring interface used for the fibre condition below. -/
structure LocalCompleteIntersectionWitness (A : Type u) [CommRing A] where
  R : Type u
  [commRingR : CommRing R]
  [localR : IsLocalRing R]
  [regularR : IsRegularLocalRing R]
  generators : List R
  regular : RingTheory.Sequence.IsRegular R generators
  quotientIso : Nonempty (A ≃+* (R ⧸ Ideal.ofList generators))

def IsLocallyCompleteIntersectionFibre {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) : Prop :=
  ∀ x : f.fiber y,
    Nonempty (LocalCompleteIntersectionWitness
      ((f.fiber y).presheaf.stalk x : Type u))

class IsSyntomic {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  flat : Flat f
  fibresLocallyCompleteIntersection : ∀ y : Y, IsLocallyCompleteIntersectionFibre f y

noncomputable def fibreDimension {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) : ℕ∞ :=
  ⨆ x : f.fiber y, Order.coheight x

class HasFibreDimension {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (d : ℕ) : Prop where
  dimension_eq : fibreDimension f y = d

class IsLocallyOfFiniteTypeOfRelativeDimension (d : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType f
  fibreDimension_eq : ∀ y : Y, HasFibreDimension f y d

/-- The G-unramified predicate used by the source. -/
class IsGUnramified {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  diagonal_open : IsOpenImmersion (pullback.diagonal f)

/-- The ordinary unramified predicate used by the source. -/
class IsUnramified {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType f
  diagonal_open : IsOpenImmersion (pullback.diagonal f)

/- These three predicates are the named regular-immersion interfaces used by
the source.  The current Mathlib snapshot has no scheme-level regular
immersion API; each interface retains the underlying immersion datum so later
developments can add the sequence condition without changing theorem users. -/
class IsKoszulRegularImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  isImmersion : IsImmersion f

class IsH1RegularImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  isImmersion : IsImmersion f

class IsQuasiRegularImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  isImmersion : IsImmersion f

/-- A property of scheme morphisms. -/
abbrev SchemeMorphismProperty := MorphismProperty Scheme.{u}

/-- The Mathlib precoverage associated to each named topology. -/
def precoverage : Topology → Precoverage Scheme.{u}
  | .fpqc => Scheme.fpqcPrecoverage
  | .fppf => Scheme.fppfPrecoverage
  | .syntomic => MorphismProperty.precoverage @IsSyntomic
  | .smooth => MorphismProperty.precoverage @Smooth
  | .etale => Scheme.etalePrecoverage
  | .zariski => Scheme.zariskiPrecoverage

/-- A covering family in one of the six topologies. -/
abbrev Cover (τ : Topology) (Y : Scheme.{u}) :=
  Scheme.Cover.{u} (precoverage τ) Y

/-- The pullback of a morphism along one member of a covering family. -/
noncomputable def baseChange {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) : Scheme := pullback f g

noncomputable def baseChangeTo {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) : baseChange f g ⟶ Y' :=
  pullback.snd f g

noncomputable def baseChangeFrom {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) : baseChange f g ⟶ X :=
  pullback.fst f g

/-! ## Locality predicates -/

/-- A property is local on the target for a named covering topology. -/
def IsLocalOnTarget (τ : Topology) (P : SchemeMorphismProperty) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Cover τ Y),
    P f ↔ ∀ i, P (baseChangeTo f (𝒰.f i))

/-- A property is local on the source for a named covering topology. -/
def IsLocalOnSource (τ : Topology) (P : SchemeMorphismProperty) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Cover τ X),
    P f ↔ ∀ i, P (𝒰.f i ≫ f)

/-- Preservation under base change along a specified class of maps. -/
def PreservedByBaseChange (Q P : SchemeMorphismProperty) : Prop :=
  ∀ {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y),
    Q g → P f → P (baseChangeTo f g)

/-- Descent through a specified class of surjective base changes. -/
def DescendsThroughBaseChange (Q P : SchemeMorphismProperty) : Prop :=
  ∀ {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y),
    Q g → P (baseChangeTo f g) → P f

/-- The morphism class used by the affine descent criterion for each topology. -/
def coveringMorphismProperty : Topology → SchemeMorphismProperty
  | .fpqc => @Flat
  | .fppf => @Flat ⊓ @LocallyOfFinitePresentation
  | .syntomic => @IsSyntomic
  | .smooth => @Smooth
  | .etale => @Etale
  | .zariski => @IsOpenImmersion

/-- The affine base-change clause in the source's general descent criterion. -/
def AffineDescent (P : SchemeMorphismProperty) (τ : Topology) : Prop :=
  ∀ {S' S X : Scheme.{u}} (g : S' ⟶ S) (f : X ⟶ S),
    IsAffine S' → IsAffine S → Surjective g →
    coveringMorphismProperty τ g → P (baseChangeTo f g) → P f

/-- The abstract output of the source's affine criterion. -/
theorem isLocalOnTarget_of_affine_criterion
    (τ : Topology) (P : SchemeMorphismProperty)
    (hbase : PreservedByBaseChange (coveringMorphismProperty τ) P)
    (hzariski : IsLocalOnTarget .zariski P)
    (haffine : AffineDescent P τ) : IsLocalOnTarget τ P := by
  sorry

/-! ## Chosen representatives for scheme germs -/

/-- A scheme together with its distinguished point. -/
structure SchemeGerm where
  carrier : Scheme.{u}
  point : carrier

namespace SchemeGerm

/-- A pointed representative of a morphism of germs.

The source quotient-by-agreement is represented by this canonical chosen
representative interface; all later predicates are invariant under shrinking
the represented neighbourhood, exactly as in the source definition. -/
structure Hom (X Y : SchemeGerm.{u}) where
  map : X.carrier ⟶ Y.carrier
  map_point : map X.point = Y.point

abbrev GermMorphismProperty :=
  ∀ {X Y : SchemeGerm.{u}}, Hom X Y → Prop

def Hom.id (X : SchemeGerm.{u}) : Hom X X :=
  ⟨𝟙 X.carrier, by simp⟩

def Hom.comp {X Y Z : SchemeGerm.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨f.map ≫ g.map, by simp [f.map_point, g.map_point]⟩

def Hom.IsEtale {X Y : SchemeGerm.{u}} (f : Hom X Y) : Prop := Etale f.map
def Hom.IsSmooth {X Y : SchemeGerm.{u}} (f : Hom X Y) : Prop := Smooth f.map

/-- Étale-locality of a property of germs. -/
def IsEtaleLocal (Q : GermMorphismProperty) : Prop :=
  ∀ {X Y X' Y' : SchemeGerm.{u}} (a : Hom X' X) (b : Hom Y' Y)
    (f' : Hom X' Y') (f : Hom X Y),
    a.map ≫ f.map = f'.map ≫ b.map →
    Hom.IsEtale a → Hom.IsEtale b → (Q f ↔ Q f')

/-! The local-at-point predicates used in the next sections. -/

def IsEtaleLocalOnGerms (Q : GermMorphismProperty) : Prop := IsEtaleLocal Q
def IsSmoothLocalOnGerms (Q : GermMorphismProperty) : Prop :=
  ∀ {X Y X' Y' : SchemeGerm.{u}} (a : Hom X' X) (b : Hom Y' Y)
    (f' : Hom X' Y') (f : Hom X Y),
    a.map ≫ f.map = f'.map ≫ b.map →
    Hom.IsSmooth a → Hom.IsSmooth b → (Q f ↔ Q f')

/-- The local ring at the distinguished point. -/
noncomputable abbrev localRing (X : SchemeGerm.{u}) : CommRingCat :=
  X.carrier.presheaf.stalk X.point

/-- The Krull dimension of the local ring of a germ. -/
noncomputable def localRingDimension (X : SchemeGerm.{u}) : WithBot ℕ∞ :=
  ringKrullDim (↑X.localRing)

/-- The topological dimension at the distinguished point. -/
noncomputable def pointDimension (X : SchemeGerm.{u}) : ℕ∞ :=
  Order.coheight X.point

def IsRegularLocalRingAtGerm (X : SchemeGerm.{u}) : Prop :=
  _root_.IsRegularLocalRing (↑X.localRing)

/-- The fibre of a pointed morphism, using Mathlib's scheme-theoretic fibre. -/
noncomputable def Hom.fibre {X Y : SchemeGerm.{u}} (f : Hom X Y) : SchemeGerm :=
  ⟨f.map.fiber (f.map X.point), f.map.asFiber X.point⟩

def Hom.IsFlatAtPoint {X Y : SchemeGerm.{u}} (f : Hom X Y) : Prop :=
  (f.map.stalkMap X.point).hom.Flat

noncomputable def Hom.fibreLocalRingDimension {X Y : SchemeGerm.{u}}
    (f : Hom X Y) : WithBot ℕ∞ :=
  (f.fibre).localRingDimension

noncomputable def Hom.fibrePointDimension {X Y : SchemeGerm.{u}}
    (f : Hom X Y) : ℕ∞ := (f.fibre).pointDimension

noncomputable def Hom.residueFieldMap {X Y : SchemeGerm.{u}} (f : Hom X Y) :
    Y.carrier.residueField Y.point ⟶ X.carrier.residueField X.point :=
  (Y.carrier.residueFieldCongr f.map_point).inv ≫ f.map.residueFieldMap X.point

noncomputable def Hom.residueFieldTranscendenceDegree
    {X Y : SchemeGerm.{u}} (f : Hom X Y) : Cardinal :=
  letI := f.residueFieldMap.hom.toAlgebra
  Algebra.trdeg (Y.carrier.residueField Y.point) (X.carrier.residueField X.point)

end SchemeGerm

end Formalization.Books.Descent.Unit19
-/
