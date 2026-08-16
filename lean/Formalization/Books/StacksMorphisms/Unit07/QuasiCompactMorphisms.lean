import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Topology.Basic

/-!
# Morphisms of Algebraic Stacks, Chapter 7: quasi-compact morphisms

Mathlib has the scheme-theoretic notion of a quasi-compact morphism, but it
does not yet have a category of algebraic stacks.  The declarations below
therefore use a small category-level interface for algebraic stacks.  The
interface keeps the categorical constructions (morphisms and pullbacks)
concrete, while leaving the geometric predicates supplied by the eventual
algebraic-stack development.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Set TopologicalSpace

universe u v

namespace Formalization.Books.StacksMorphisms.Unit07

/-! ## The algebraic-stack interface used in this chapter -/

/-
The valuation-ring data used by the valuative point-reaching statement.
The fields are the standard Mathlib typeclasses, so a witness includes an
actual valuation ring and an actual field of fractions.
-/
structure ValuationRingData where
  A : Type u
  [commRingA : CommRing A]
  [domainA : IsDomain A]
  [valuationRingA : ValuationRing A]
  K : Type u
  [fieldK : Field K]
  [algebraAK : Algebra A K]
  [isFractionRingAK : IsFractionRing A K]

attribute [instance] ValuationRingData.commRingA ValuationRingData.domainA
  ValuationRingData.valuationRingA ValuationRingData.fieldK
  ValuationRingData.algebraAK ValuationRingData.isFractionRingAK

namespace ValuationRingData

/-- The canonical inclusion of a valuation ring into its fraction field. -/
def algebraMap (V : ValuationRingData.{u}) : V.A →+* V.K :=
  V.algebraAK.algebraMap

end ValuationRingData

/-
`AlgebraicStackCategory C` says that `C` is the ambient category of
algebraic stacks.  In particular, every object of `C` is an algebraic stack;
`isAlgebraicSpace` identifies the objects which are algebraic spaces.  The
field `quasiCompact` is the pre-existing notion for representable morphisms,
which is compared with the definition introduced below.
-/
class AlgebraicStackCategory (C : Type u) [Category.{v} C] where
  isAlgebraicSpace : C → Prop
  isQuasiCompactStack : C → Prop
  isQuasiSeparatedStack : C → Prop
  quasiCompact : ∀ {X Y : C}, (X ⟶ Y) → Prop
  quasiSeparated : ∀ {X Y : C}, (X ⟶ Y) → Prop
  representableByAlgebraicSpace : ∀ {X Y : C}, (X ⟶ Y) → Prop
  surjective : ∀ {X Y : C}, (X ⟶ Y) → Prop
  closedImmersion : ∀ {X Y : C}, (X ⟶ Y) → Prop
  flat : ∀ {X Y : C}, (X ⟶ Y) → Prop
  locallyOfFinitePresentation : ∀ {X Y : C}, (X ⟶ Y) → Prop
  point : C → Type u
  pointTopology : ∀ X, TopologicalSpace (point X)
  pointMap : ∀ {X Y : C}, (X ⟶ Y) → point X → point Y
  spec : ∀ (R : Type u) [CommRing R], C
  specMap : ∀ {R S : Type u} [CommRing R] [CommRing S],
    (R →+* S) → ((@spec S _) ⟶ (@spec R _))
  closedPoint : ∀ (V : ValuationRingData.{u}), point (@spec V.A _)

instance pointTopologicalSpace {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] (X : C) : TopologicalSpace
      (AlgebraicStackCategory.point X) :=
  AlgebraicStackCategory.pointTopology X

/-! ## Predicates and constructions -/

def IsAlgebraicSpace {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] (X : C) : Prop :=
  AlgebraicStackCategory.isAlgebraicSpace X

def IsQuasiCompactStack {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] (X : C) : Prop :=
  AlgebraicStackCategory.isQuasiCompactStack X

def IsQuasiSeparatedStack {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] (X : C) : Prop :=
  AlgebraicStackCategory.isQuasiSeparatedStack X

def ExistingQuasiCompact {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  AlgebraicStackCategory.quasiCompact f

def QuasiSeparated {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  AlgebraicStackCategory.quasiSeparated f

def RepresentableByAlgebraicSpace {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  AlgebraicStackCategory.representableByAlgebraicSpace f

def Surjective {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  AlgebraicStackCategory.surjective f

def ClosedImmersion {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  AlgebraicStackCategory.closedImmersion f

def Flat {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  AlgebraicStackCategory.flat f

def LocallyOfFinitePresentation {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  AlgebraicStackCategory.locallyOfFinitePresentation f

/-- The fibre product of a quasi-compact stack over the target of `f`. -/
def QuasiCompact {C : Type u} [Category.{v} C] [HasPullbacks C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ (Z : C), IsQuasiCompactStack Z →
    ∀ (g : Z ⟶ Y), IsQuasiCompactStack (pullback g f)

/-- The point space and the map on points supplied by the stack interface. -/
abbrev Point {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] (X : C) : Type u :=
  AlgebraicStackCategory.point X

def pointMap {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) :
    Point X → Point Y :=
  AlgebraicStackCategory.pointMap f

def PointImage {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) : Set (Point Y) :=
  Set.range (pointMap f)

def PointInClosureOfImage {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) (y : Point Y) : Prop :=
  y ∈ closure (PointImage f)

def Spec {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] (R : Type u) [CommRing R] : C :=
  AlgebraicStackCategory.spec R

def SpecMap {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : Spec (C := C) S ⟶ Spec (C := C) R :=
  AlgebraicStackCategory.specMap (C := C) φ

def closedPoint {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] (V : ValuationRingData.{u}) :
    Point (Spec (C := C) V.A) :=
  AlgebraicStackCategory.closedPoint (C := C) V

/-! ## Characterization and permanence of quasi-compactness -/

/-- The source's characterization of the pre-existing notion for
representable morphisms. -/
lemma quasiCompact_iff_of_representable {C : Type u} [Category.{v} C]
    [HasPullbacks C] [AlgebraicStackCategory C] {X Y : C}
    (f : X ⟶ Y) (h : RepresentableByAlgebraicSpace f) :
    ExistingQuasiCompact f ↔ QuasiCompact f := by
  sorry

/-
The displayed definition in the source is the definition of `QuasiCompact`
above.  The following theorem records the agreement with the old notion in
the representable case without introducing a duplicate predicate.
-/
theorem quasiCompact_agrees_with_existing {C : Type u} [Category.{v} C]
    [HasPullbacks C] [AlgebraicStackCategory C] {X Y : C}
    (f : X ⟶ Y) (h : RepresentableByAlgebraicSpace f) :
    QuasiCompact f ↔ ExistingQuasiCompact f :=
  (quasiCompact_iff_of_representable f h).symm

lemma quasiCompact_baseChange {C : Type u} [Category.{v} C]
    [HasPullbacks C] [AlgebraicStackCategory C] {X Y Z : C}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : QuasiCompact f) :
    QuasiCompact (pullback.fst g f) := by
  sorry

lemma quasiCompact_comp {C : Type u} [Category.{v} C]
    [HasPullbacks C] [AlgebraicStackCategory C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : QuasiCompact f)
    (hg : QuasiCompact g) : QuasiCompact (f ≫ g) := by
  sorry

lemma quasiCompact_closedImmersion {C : Type u} [Category.{v} C]
    [HasPullbacks C] [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y)
    (hf : ClosedImmersion f) : QuasiCompact f := by
  sorry

lemma quasiCompact_of_surjective {C : Type u} [Category.{v} C]
    [HasPullbacks C] [AlgebraicStackCategory C] {X Y Z : C}
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (commutes : f ≫ q = p)
    (hf : Surjective f) (hp : QuasiCompact p) : QuasiCompact q := by
  sorry

lemma quasiCompact_of_comp {C : Type u} [Category.{v} C]
    [HasPullbacks C] [AlgebraicStackCategory C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hcomp : QuasiCompact (f ≫ g))
    (hg : QuasiSeparated g) : QuasiCompact f := by
  sorry

lemma quasiCompact_of_quasiCompactStack_of_quasiSeparatedStack
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y)
    (hX : IsQuasiCompactStack X) (hY : IsQuasiSeparatedStack Y) :
    QuasiCompact f := by
  sorry

lemma quasiCompact_quasiSeparated_of_quasiCompactStack
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y)
    (hXqc : IsQuasiCompactStack X) (hXqs : IsQuasiSeparatedStack X)
    (hYqs : IsQuasiSeparatedStack Y) :
    QuasiCompact f ∧ QuasiSeparated f := by
  sorry

lemma quasiCompact_quasiSeparated_pullback
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    [AlgebraicStackCategory C] {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hXqc : IsQuasiCompactStack X) (hXqs : IsQuasiSeparatedStack X)
    (hYqc : IsQuasiCompactStack Y) (hYqs : IsQuasiSeparatedStack Y)
    (hZqc : IsQuasiCompactStack Z) (hZqs : IsQuasiSeparatedStack Z) :
    IsQuasiCompactStack (pullback f g) ∧
      IsQuasiSeparatedStack (pullback f g) := by
  sorry

/-! ## Valuation-ring point reaching -/

/-- A commutative square over `f` obtained from a valuation ring. -/
structure ValuationSquare {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y) (y : Point Y)
    (V : ValuationRingData.{u}) where
  generic : Spec (C := C) V.K ⟶ X
  special : Spec (C := C) V.A ⟶ Y
  commSq : SpecMap V.algebraMap ≫ special = generic ≫ f
  closedPoint_maps_to : pointMap special (closedPoint V) = y

lemma exists_valuation_square_reaching
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    [AlgebraicStackCategory C] {X Y : C} (f : X ⟶ Y)
    (hf : QuasiCompact f) (y : Point Y)
    (hy : PointInClosureOfImage f y) :
    ∃ V : ValuationRingData.{u}, Nonempty (ValuationSquare f y V) := by
  sorry

/-! ## Checking quasi-compactness on a covering -/

lemma quasiCompact_of_cover {C : Type u} [Category.{v} C]
    [HasPullbacks C] [AlgebraicStackCategory C] {X Y W : C}
    (f : X ⟶ Y) (w : W ⟶ Y) (hW : IsAlgebraicSpace W)
    (hw_surjective : Surjective w) (hw_flat : Flat w)
    (hw_lfp : LocallyOfFinitePresentation w)
    (hbase : QuasiCompact (pullback.fst w f)) : QuasiCompact f := by
  sorry

end Formalization.Books.StacksMorphisms.Unit07
