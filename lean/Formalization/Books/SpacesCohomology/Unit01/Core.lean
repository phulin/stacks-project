import Mathlib.Algebra.Group.Hom.End
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Topology.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-!
# Cohomology of Algebraic Spaces, Chapter 1: shared interfaces

The project snapshot does not yet contain the algebraic-space and étale-site
implementations used by the source chapter.  This file therefore records the
objects, operations, and properties which the chapter statements use.  The
topological stand-in for an algebraic space is the one already introduced by
the earlier Spaces Morphisms chapter; the sheaf and cohomology operations are
kept as explicit model data rather than being silently replaced by unrelated
scheme constructions.

TODO(proof agents): keep the data interfaces below lightweight and add
separate, reusable law classes as results need them. The useful boundaries
are: geometry laws (property implications and stability under composition or
base change), sheaf-operation laws (restriction, stalks, tensor,
extension-by-zero, and pushforward), cohomology laws (affine vanishing, base
change, projection formula, and filtered colimits), coherence laws (closure
and support), and valuative/existence laws. A theorem should depend only on
the narrow law class containing its actual input; the independent `Prop`
fields below cannot prove these relationships by themselves.
-/

namespace Formalization.Books.SpacesCohomology.Unit01

open CategoryTheory CategoryTheory.Limits

universe u

abbrev AlgebraicSpace := TopCat

abbrev SpaceHom (X Y : AlgebraicSpace.{u}) := X ⟶ Y

abbrev SchemeLike := AlgebraicSpace

/-! ## Algebraic-space properties -/

class AlgebraicSpaceTheory where
  isScheme : AlgebraicSpace.{u} → Prop
  isRepresentable : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isQuasiCompact : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isQuasiSeparated : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isSeparated : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isIntegral : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isFinite : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isAffine : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isProper : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isFlat : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isEtale : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isQuasiFinite : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isFiniteType : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isLocallyOfFiniteType : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isLocallyOfFinitePresentation : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isClosedImmersion : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isOpenImmersion : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isProjective : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isHQuasiProjective : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Prop
  isLocallyNoetherian : AlgebraicSpace.{u} → Prop
  isNoetherian : AlgebraicSpace.{u} → Prop
  isReduced : AlgebraicSpace.{u} → Prop
  dimension : AlgebraicSpace.{u} → ℕ

def IsScheme (S : AlgebraicSpace.{u}) [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isScheme S

def IsRepresentable {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isRepresentable f

def IsQuasiCompact {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isQuasiCompact f

def IsQuasiSeparated {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isQuasiSeparated f

def IsSeparated {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isSeparated f

def IsIntegral {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isIntegral f

def IsFinite {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isFinite f

def IsAffine {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isAffine f

def IsProper {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isProper f

def IsFlat {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isFlat f

def IsEtale {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isEtale f

def IsQuasiFinite {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isQuasiFinite f

def IsFiniteType {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isFiniteType f

def IsLocallyOfFiniteType {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isLocallyOfFiniteType f

def IsLocallyOfFinitePresentation {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isLocallyOfFinitePresentation f

def IsClosedImmersion {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isClosedImmersion f

def IsOpenImmersion {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isOpenImmersion f

def IsProjective {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isProjective f

def IsHQuasiProjective {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isHQuasiProjective f

def IsLocallyNoetherian (X : AlgebraicSpace.{u}) [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isLocallyNoetherian X

def IsNoetherian (X : AlgebraicSpace.{u}) [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isNoetherian X

def IsReduced (X : AlgebraicSpace.{u}) [AlgebraicSpaceTheory.{u}] : Prop :=
  AlgebraicSpaceTheory.isReduced X

def SpaceDimension (X : AlgebraicSpace.{u}) [AlgebraicSpaceTheory.{u}] : ℕ :=
  AlgebraicSpaceTheory.dimension X

def IsSurjective {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) : Prop :=
  Function.Surjective f

def IsInjective {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) : Prop :=
  Function.Injective f

def IsDiscrete (X : AlgebraicSpace.{u}) : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, y = x

def IsFinitePointSet {X : Type u} (s : Set X) : Prop := s.Finite

structure ClosedSubspace (X : AlgebraicSpace.{u}) where
  carrier : AlgebraicSpace.{u}
  inclusion : SpaceHom carrier X
  closed : Prop

structure OpenSubspace (X : AlgebraicSpace.{u}) where
  carrier : AlgebraicSpace.{u}
  inclusion : SpaceHom carrier X
  is_open : Prop

structure ClosedSubspaceComplement (X : AlgebraicSpace.{u})
    (Z : ClosedSubspace X) where
  open_subspace : OpenSubspace X
  disjoint : Disjoint (Set.range open_subspace.inclusion)
    (Set.range Z.inclusion)
  covers : Set.range open_subspace.inclusion ∪ Set.range Z.inclusion = Set.univ

noncomputable def pointMap (Y : AlgebraicSpace.{u}) (y : Y) : TopCat.of (PUnit.{u + 1}) ⟶ Y :=
  TopCat.ofHom (ContinuousMap.const (PUnit.{u + 1}) y)

noncomputable def FibreSpace {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) (y : Y) : AlgebraicSpace.{u} :=
  pullback f (pointMap Y y)

def FibrePoints {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) (y : Y) : Set X :=
  {x | f x = y}

noncomputable def baseChange {X Y Y' : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (g : SpaceHom Y' Y) : AlgebraicSpace.{u} :=
  pullback f g

noncomputable def baseChangeSource {X Y Y' : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (g : SpaceHom Y' Y) : SpaceHom (baseChange f g) X :=
  pullback.fst f g

noncomputable def baseChangeTarget {X Y Y' : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (g : SpaceHom Y' Y) : SpaceHom (baseChange f g) Y' :=
  pullback.snd f g

noncomputable def relativeProduct (X Y S : AlgebraicSpace.{u})
    (f : SpaceHom X S) (g : SpaceHom Y S) : AlgebraicSpace.{u} :=
  pullback f g

noncomputable def relativeProductFst {X Y S : AlgebraicSpace.{u}}
    (f : SpaceHom X S) (g : SpaceHom Y S) : SpaceHom (relativeProduct X Y S f g) X :=
  pullback.fst f g

noncomputable def relativeProductSnd {X Y S : AlgebraicSpace.{u}}
    (f : SpaceHom X S) (g : SpaceHom Y S) : SpaceHom (relativeProduct X Y S f g) Y :=
  pullback.snd f g

def IsUniversallyInjective {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) : Prop :=
  ∀ (Y' : AlgebraicSpace.{u}) (g : SpaceHom Y' Y),
    IsInjective (baseChangeTarget f g)

/-! ## A ringed étale-site/cohomology model -/

class AlgebraicSpaceCohomology where
  Sheaf : AlgebraicSpace.{u} → Type u
  Hom : ∀ (X : AlgebraicSpace.{u}), Sheaf X → Sheaf X → Type u
  id : ∀ (X : AlgebraicSpace.{u}) (F : Sheaf X), Hom X F F
  comp : ∀ {X : AlgebraicSpace.{u}} {F G H : Sheaf X}, Hom X F G → Hom X G H → Hom X F H
  comp_id : ∀ {X : AlgebraicSpace.{u}} {F G : Sheaf X} (f : Hom X F G), comp f (id X G) = f
  id_comp : ∀ {X : AlgebraicSpace.{u}} {F G : Sheaf X} (f : Hom X F G), comp (id X F) f = f
  assoc : ∀ {X : AlgebraicSpace.{u}} {F G H K : Sheaf X}
    (f : Hom X F G) (g : Hom X G H) (h : Hom X H K),
    comp (comp f g) h = comp f (comp g h)
  homGroup : ∀ (X : AlgebraicSpace.{u}) (F G : Sheaf X), AddCommGroup (Hom X F G)
  isQuasiCoherent : ∀ {X : AlgebraicSpace.{u}}, Sheaf X → Prop
  isCoherent : ∀ {X : AlgebraicSpace.{u}}, Sheaf X → Prop
  isFiniteType : ∀ {X : AlgebraicSpace.{u}}, Sheaf X → Prop
  isFinitePresentation : ∀ {X : AlgebraicSpace.{u}}, Sheaf X → Prop
  isInvertible : ∀ {X : AlgebraicSpace.{u}}, Sheaf X → Prop
  isFiniteLocallyFree : ∀ {X : AlgebraicSpace.{u}}, Sheaf X → Prop
  isAmple : ∀ {X : AlgebraicSpace.{u}}, Sheaf X → Prop
  constantSheaf : ∀ X : AlgebraicSpace.{u}, Sheaf X
  structureSheaf : ∀ X : AlgebraicSpace.{u}, Sheaf X
  zeroSheaf : ∀ X : AlgebraicSpace.{u}, Sheaf X
  sections : ∀ (X : AlgebraicSpace.{u}), Sheaf X → Type u
  sectionsGroup : ∀ (X : AlgebraicSpace.{u}) (F : Sheaf X), AddCommGroup (sections X F)
  stalk : ∀ (X : AlgebraicSpace.{u}) (_F : Sheaf X), X → Type u
  stalkGroup : ∀ (X : AlgebraicSpace.{u}) (F : Sheaf X) (x : X),
    AddCommGroup (stalk X F x)
  cohomology : ∀ (X : AlgebraicSpace.{u}) (_F : Sheaf X), ℤ → Type u
  cohomologyGroup : ∀ (X : AlgebraicSpace.{u}) (F : Sheaf X) (n : ℤ),
    AddCommGroup (cohomology X F n)
  extGroup : ∀ (X : AlgebraicSpace.{u}) (_F _G : Sheaf X), ℕ → Type u
  extGroupStructure : ∀ (X : AlgebraicSpace.{u}) (F G : Sheaf X) (n : ℕ),
    AddCommGroup (extGroup X F G n)
  Derived : AlgebraicSpace.{u} → Type u
  DerivedHom : ∀ (X : AlgebraicSpace.{u}), Derived X → Derived X → Type u
  derivedShift : ∀ (X : AlgebraicSpace.{u}), ℤ → Derived X → Derived X
  derivedTensor : ∀ (X : AlgebraicSpace.{u}), Derived X → Derived X → Derived X
  derivedPullback : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Derived Y → Derived X
  derivedGlobalSections : ∀ (X : AlgebraicSpace.{u}), Derived X → Type u
  derivedGlobalSectionsGroup : ∀ (X : AlgebraicSpace.{u}) (K : Derived X),
    AddCommGroup (derivedGlobalSections X K)
  pullbackSheaf : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Sheaf Y → Sheaf X
  pushforwardSheaf : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Sheaf X → Sheaf Y
  higherPushforwardSheaf : ∀ {X Y : AlgebraicSpace.{u}}, ℕ → SpaceHom X Y → Sheaf X → Sheaf Y
  derivedPushforward : ∀ {X Y : AlgebraicSpace.{u}}, SpaceHom X Y → Derived X → Derived Y
  extensionByZero : ∀ {U X : AlgebraicSpace.{u}}, SpaceHom U X → Sheaf U → Sheaf X
  traceMap : ∀ {U X : AlgebraicSpace.{u}} (f : SpaceHom U X),
    Hom X (extensionByZero f (constantSheaf U)) (constantSheaf X)
  tensorSheaf : ∀ (X : AlgebraicSpace.{u}), Sheaf X → Sheaf X → Sheaf X
  tensorPower : ∀ (X : AlgebraicSpace.{u}), Sheaf X → ℕ → Sheaf X
  internalHomSheaf : ∀ (X : AlgebraicSpace.{u}), Sheaf X → Sheaf X → Sheaf X
  exteriorPower : ∀ (X : AlgebraicSpace.{u}), ℕ → Sheaf X → Sheaf X
  exteriorPowerOne : ∀ (X : AlgebraicSpace.{u}) (F : Sheaf X),
    Hom X (exteriorPower X 1 F) F
  idealPower : ∀ (X : AlgebraicSpace.{u}), Sheaf X → ℕ → Sheaf X
  idealTimes : ∀ (X : AlgebraicSpace.{u}), Sheaf X → Sheaf X → Sheaf X
  quotientBy : ∀ (X : AlgebraicSpace.{u}), Sheaf X → Sheaf X → Sheaf X
  directSum : ∀ (X : AlgebraicSpace.{u}), ℕ → Sheaf X → Sheaf X
  restriction : ∀ {U X : AlgebraicSpace.{u}}, SpaceHom U X → Sheaf X → Sheaf U
  supportOfSection : ∀ {X : AlgebraicSpace.{u}} {F : Sheaf X}, sections X F → Set X
  supportOfSheaf : ∀ {X : AlgebraicSpace.{u}}, Sheaf X → Set X
  schemeTheoreticSupport : ∀ {X : AlgebraicSpace.{u}}, Sheaf X → ClosedSubspace X

abbrev SheafObj (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}] :=
  AlgebraicSpaceCohomology.Sheaf X

abbrev SheafHom {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (F G : SheafObj X) :=
  AlgebraicSpaceCohomology.Hom X F G

abbrev DerivedObj (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}] :=
  AlgebraicSpaceCohomology.Derived X

abbrev DerivedHom {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (K L : DerivedObj X) := AlgebraicSpaceCohomology.DerivedHom X K L

abbrev Sections (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) := AlgebraicSpaceCohomology.sections X F

abbrev Stalk (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) (x : X) := AlgebraicSpaceCohomology.stalk X F x

abbrev CohomologyGroup (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) (n : ℤ) := AlgebraicSpaceCohomology.cohomology X F n

abbrev ExtGroup (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F G : SheafObj X) (n : ℕ) := AlgebraicSpaceCohomology.extGroup X F G n

abbrev DerivedGlobalSections (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (K : DerivedObj X) := AlgebraicSpaceCohomology.derivedGlobalSections X K

instance sectionsGroup (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : AddCommGroup (Sections X F) :=
  AlgebraicSpaceCohomology.sectionsGroup X F

instance stalkGroup (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) (x : X) : AddCommGroup (Stalk X F x) :=
  AlgebraicSpaceCohomology.stalkGroup X F x

instance cohomologyGroup (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) (n : ℤ) : AddCommGroup (CohomologyGroup X F n) :=
  AlgebraicSpaceCohomology.cohomologyGroup X F n

instance extGroupStructure (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F G : SheafObj X) (n : ℕ) : AddCommGroup (ExtGroup X F G n) :=
  AlgebraicSpaceCohomology.extGroupStructure X F G n

instance derivedGlobalSectionsGroup (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (K : DerivedObj X) :
    AddCommGroup (DerivedGlobalSections X K) :=
  AlgebraicSpaceCohomology.derivedGlobalSectionsGroup X K

def sheafId (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : SheafHom F F :=
  AlgebraicSpaceCohomology.id X F

instance sheafHomGroup (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F G : SheafObj X) : AddCommGroup (SheafHom F G) :=
  AlgebraicSpaceCohomology.homGroup X F G

def sheafComp {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    {F G H : SheafObj X}
    (f : SheafHom F G) (g : SheafHom G H) : SheafHom F H :=
  AlgebraicSpaceCohomology.comp f g

noncomputable def zeroSheafHom {X : AlgebraicSpace.{u}}
    [AlgebraicSpaceCohomology.{u}] (F G : SheafObj X) : SheafHom F G := by
  letI := AlgebraicSpaceCohomology.homGroup X F G
  exact 0

structure SheafIso (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F G : SheafObj X) where
  hom : SheafHom F G
  inv : SheafHom G F
  hom_inv_id : sheafComp hom inv = sheafId X F
  inv_hom_id : sheafComp inv hom = sheafId X G

def IsQuasiCoherent {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  AlgebraicSpaceCohomology.isQuasiCoherent F

def IsCoherent {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  AlgebraicSpaceCohomology.isCoherent F

def IsFiniteTypeSheaf {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  AlgebraicSpaceCohomology.isFiniteType F

def IsFinitePresentation {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  AlgebraicSpaceCohomology.isFinitePresentation F

def IsInvertible {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  AlgebraicSpaceCohomology.isInvertible F

def IsFiniteLocallyFree {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  AlgebraicSpaceCohomology.isFiniteLocallyFree F

def IsAmple {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  AlgebraicSpaceCohomology.isAmple F

def constantSheaf (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}] : SheafObj X :=
  AlgebraicSpaceCohomology.constantSheaf X

def structureSheaf (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}] : SheafObj X :=
  AlgebraicSpaceCohomology.structureSheaf X

def zeroSheaf (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}] : SheafObj X :=
  AlgebraicSpaceCohomology.zeroSheaf X

def CohomologyVanishes (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) (n : ℤ) : Prop :=
  Subsingleton (CohomologyGroup X F n)

def CohomologyIso (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    {F G : SheafObj X} (n : ℤ) : Prop :=
  Nonempty (CohomologyGroup X F n ≃+ CohomologyGroup X G n)

def CohomologyComparison (X Y : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (F : SheafObj X) (G : SheafObj Y)
    (m n : ℤ) : Prop :=
  Nonempty (CohomologyGroup X F m ≃+ CohomologyGroup Y G n)

def pullbackSheaf {X Y : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (g : SpaceHom X Y) (F : SheafObj Y) : SheafObj X :=
  AlgebraicSpaceCohomology.pullbackSheaf g F

def pushforwardSheaf {X Y : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (f : SpaceHom X Y) (F : SheafObj X) : SheafObj Y :=
  AlgebraicSpaceCohomology.pushforwardSheaf f F

def higherDirectImage {X Y : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (p : ℕ) (f : SpaceHom X Y) (F : SheafObj X) : SheafObj Y :=
  AlgebraicSpaceCohomology.higherPushforwardSheaf p f F

def derivedDirectImage {X Y : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (f : SpaceHom X Y) (K : DerivedObj X) : DerivedObj Y :=
  AlgebraicSpaceCohomology.derivedPushforward f K

def derivedTensor (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (K L : DerivedObj X) : DerivedObj X :=
  AlgebraicSpaceCohomology.derivedTensor X K L

def derivedPullback {X Y : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (g : SpaceHom X Y) (K : DerivedObj Y) : DerivedObj X :=
  AlgebraicSpaceCohomology.derivedPullback g K

abbrev RΓ (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (K : DerivedObj X) : Type u :=
  AlgebraicSpaceCohomology.derivedGlobalSections X K

def extensionByZero {U X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (f : SpaceHom U X) (F : SheafObj U) : SheafObj X :=
  AlgebraicSpaceCohomology.extensionByZero f F

def traceMap {U X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (f : SpaceHom U X) :
    SheafHom (extensionByZero f (constantSheaf U)) (constantSheaf X) :=
  AlgebraicSpaceCohomology.traceMap f

def tensorSheaf (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F G : SheafObj X) : SheafObj X :=
  AlgebraicSpaceCohomology.tensorSheaf X F G

def tensorPowerSheaf (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) (n : ℕ) : SheafObj X :=
  AlgebraicSpaceCohomology.tensorPower X F n

def internalHomSheaf (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F G : SheafObj X) : SheafObj X :=
  AlgebraicSpaceCohomology.internalHomSheaf X F G

def exteriorPower (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (n : ℕ) (F : SheafObj X) : SheafObj X :=
  AlgebraicSpaceCohomology.exteriorPower X n F

def idealPower (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (I : SheafObj X) (n : ℕ) : SheafObj X :=
  AlgebraicSpaceCohomology.idealPower X I n

def idealTimes (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (I F : SheafObj X) : SheafObj X :=
  AlgebraicSpaceCohomology.idealTimes X I F

def quotientBy (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F I : SheafObj X) : SheafObj X :=
  AlgebraicSpaceCohomology.quotientBy X F I

def directSumSheaf (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (n : ℕ) (F : SheafObj X) : SheafObj X :=
  AlgebraicSpaceCohomology.directSum X n F

def restrictSheaf {U X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (j : SpaceHom U X) (F : SheafObj X) : SheafObj U :=
  AlgebraicSpaceCohomology.restriction j F

def sectionSupport {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    {F : SheafObj X} (s : Sections X F) : Set X :=
  AlgebraicSpaceCohomology.supportOfSection s

def sheafSupport (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Set X :=
  AlgebraicSpaceCohomology.supportOfSheaf F

def schemeTheoreticSupport {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : ClosedSubspace X :=
  AlgebraicSpaceCohomology.schemeTheoreticSupport F

structure ShortExactSheaves (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] where
  F₁ : SheafObj X
  F₂ : SheafObj X
  F₃ : SheafObj X
  left : SheafHom F₁ F₂
  right : SheafHom F₂ F₃
  complex : sheafComp left right = zeroSheafHom F₁ F₃
  exact : Prop

structure DerivedTriangle (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] where
  A : DerivedObj X
  B : DerivedObj X
  C : DerivedObj X
  first : DerivedHom A B
  second : DerivedHom B C
  third : DerivedHom C A
  distinguished : Prop

structure DerivedIso (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (K L : DerivedObj X) where
  hom : DerivedHom K L
  inv : DerivedHom L K
  left_inverse : Prop
  right_inverse : Prop

structure SpectralSequenceStatement (Page : ℤ → ℤ → Type u) (Target : ℤ → Type u) where
  e₁_page : Prop
  convergence : Prop

structure LongExactSequenceStatement (Term : ℤ → Type u) where
  differential : ∀ n, Term n → Term (n + 1)
  exactness : Prop

structure ShortExactGroups (A B C : Type u)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] where
  left : A →+ B
  right : B →+ C
  complex : right.comp left = 0
  exact : Prop

structure IdealSheaf (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] where
  object : SheafObj X
  ideal : Prop
  closedSubspace : ClosedSubspace X
  cuts_out : Prop

def IdealSheaf.power {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (I : IdealSheaf X) (n : ℕ) : IdealSheaf X where
  object := idealPower X I.object n
  ideal := I.ideal
  closedSubspace := I.closedSubspace
  cuts_out := I.cuts_out

def IdealSheaf.mul {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    (I F : IdealSheaf X) : IdealSheaf X where
  object := idealTimes X I.object F.object
  ideal := I.ideal
  closedSubspace := I.closedSubspace
  cuts_out := I.cuts_out

structure CohomologySituation [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] where
  base : AlgebraicSpace.{u}
  space : AlgebraicSpace.{u}
  structureMap : SpaceHom space base
  baseIsScheme : IsScheme base
  spaceQuasiCompact : IsQuasiCompact structureMap
  spaceQuasiSeparated : IsQuasiSeparated structureMap
  h1_vanishes : ∀ (F : SheafObj space), IsQuasiCoherent F → CohomologyVanishes space F 1

end Formalization.Books.SpacesCohomology.Unit01
