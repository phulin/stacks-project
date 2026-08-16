import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Chapter 40: Detecting Boundedness — core interfaces

Mathlib contains the categorical and scheme-theoretic infrastructure used below,
but it does not provide the derived category of quasi-coherent sheaves on a
scheme.  The definitions in this file record precisely the derived-category
operations which the statements in this chapter use.
-/

namespace Formalization.Books.Perfect.Unit40

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w z

/-- The graded object underlying the cohomology of a complex over `ℤ`.

The degree spaces are deliberately left abstract: in applications they are
the abelian groups `H^i` of an object of `D(ℤ)`.  `IsTrivial` below is the
underlying zero-object condition and does not require choosing a presentation
of those groups.
-/
structure IntegerGraded where
  degree : ℤ → Type u

/-- A type is trivial when it has at most one element.

For a cohomology group this is equivalent to being the zero group. -/
def IsTrivial (A : Type u) : Prop :=
  ∀ x y : A, x = y

/-- Vanishing of all cohomology in degrees strictly larger than a bound. -/
def CohomologyVanishesAbove (K : IntegerGraded.{u}) : Prop :=
  ∃ a : ℤ, ∀ i : ℤ, a < i → IsTrivial (K.degree i)

/-- Vanishing of all cohomology in degrees strictly smaller than a bound. -/
def CohomologyVanishesBelow (K : IntegerGraded.{u}) : Prop :=
  ∃ a : ℤ, ∀ i : ℤ, i < a → IsTrivial (K.degree i)

/-- The usual bounded-above and bounded-below predicates for an object of
`D(ℤ)`, expressed on its cohomology. -/
def InDMinus (K : IntegerGraded.{u}) : Prop :=
  CohomologyVanishesAbove K

def InDPlus (K : IntegerGraded.{u}) : Prop :=
  CohomologyVanishesBelow K

/-- The derived-category operations used by Chapter 40.

`C` is the ambient derived category associated with the scheme `X`.  The
fields `shiftHomEquiv` and `rHom` make the two standard presentations of Ext
and derived Hom available without committing to a particular construction of
the derived category.
-/
class DerivedCategoryData (X : Scheme) (C : Type v)
    [Category.{w} C] [HasZeroMorphisms C] where
  isQCoh : C → Prop
  isPerfect : C → Prop
  shift : ℤ → C → C
  truncGE : ℤ → C → C
  truncLE : ℤ → C → C
  dual : C → C
  tensor : C → C → C
  rHom : C → C → IntegerGraded.{v}
  globalSections : C → IntegerGraded.{v}
  shiftHomEquiv : ∀ (P E : C) (i : ℤ),
    (shift (-i) P ⟶ E) ≃ (P ⟶ shift i E)

variable {X : Scheme} {C : Type v} [Category.{w} C] [HasZeroMorphisms C]
  [DerivedCategoryData X C]

/-- Membership in the quasi-coherent and perfect parts of the derived category. -/
def IsQCoh (E : C) : Prop :=
  DerivedCategoryData.isQCoh (X := X) (C := C) E

def IsPerfect (P : C) : Prop :=
  DerivedCategoryData.isPerfect (X := X) (C := C) P

/-- The shift `P[n]`. -/
def Shift (P : C) (n : ℤ) : C :=
  DerivedCategoryData.shift (X := X) (C := C) n P

/-- The standard truncations of a derived object. -/
def TruncGE (E : C) (a : ℤ) : C :=
  DerivedCategoryData.truncGE (X := X) (C := C) a E

def TruncLE (E : C) (a : ℤ) : C :=
  DerivedCategoryData.truncLE (X := X) (C := C) a E

/-- Derived dual and derived tensor product. -/
def Dual (P : C) : C :=
  DerivedCategoryData.dual (X := X) (C := C) P

def Tensor (P E : C) : C :=
  DerivedCategoryData.tensor (X := X) (C := C) P E

/-- Derived Hom and derived global sections, viewed through their cohomology. -/
def RHom (P E : C) : IntegerGraded.{v} :=
  DerivedCategoryData.rHom (X := X) (C := C) P E

def RΓ (E : C) : IntegerGraded.{v} :=
  DerivedCategoryData.globalSections (X := X) (C := C) E

/-- A morphism space is zero. -/
def HomVanishes (P E : C) : Prop :=
  ∀ f : P ⟶ E, f = 0

/-- The derived Ext space `Ext^i(P, E)`, represented by the usual shifted Hom. -/
def ExtGroup (P E : C) (i : ℤ) : Type _ :=
  P ⟶ Shift (X := X) (C := C) E i

def ExtVanishes (P E : C) (i : ℤ) : Prop :=
  ∀ f : P ⟶ Shift (X := X) (C := C) E i, f = 0

/-- Vanishing of `Hom(P[-i], E)` for all sufficiently large `i`. -/
def HomVanishesAbove (P E : C) : Prop :=
  ∃ a : ℤ, ∀ i : ℤ, a < i →
    HomVanishes (Shift (X := X) (C := C) P (-i)) E

/-- Vanishing of `Hom(P[-i], E)` for all sufficiently small `i`. -/
def HomVanishesBelow (P E : C) : Prop :=
  ∃ a : ℤ, ∀ i : ℤ, i < a →
    HomVanishes (Shift (X := X) (C := C) P (-i)) E

def ExtVanishesAbove (P E : C) : Prop :=
  ∃ a : ℤ, ∀ i : ℤ, a < i → ExtVanishes (X := X) (C := C) P E i

def ExtVanishesBelow (P E : C) : Prop :=
  ∃ a : ℤ, ∀ i : ℤ, i < a → ExtVanishes (X := X) (C := C) P E i

/-- Isomorphism of derived objects, expressed using Mathlib's category API. -/
def Isomorphic (A B : C) : Prop :=
  Nonempty (A ≅ B)

/-- The intrinsic boundedness predicates in the derived category.

An object is bounded above (respectively below) when it is isomorphic to a
truncation which is bounded above (respectively below). -/
def ObjectBoundedAbove (E : C) : Prop :=
  ∃ a : ℤ, Isomorphic E (TruncLE (X := X) (C := C) E a)

def ObjectBoundedBelow (E : C) : Prop :=
  ∃ a : ℤ, Isomorphic E (TruncGE (X := X) (C := C) E a)

/-- A perfect object generates the quasi-coherent derived category. -/
def GeneratesQCoh (G : C) : Prop :=
  ∀ E : C, IsQCoh (X := X) (C := C) E →
    (∀ n : ℤ, HomVanishes (Shift (X := X) (C := C) G n) E) → IsZero E

/-- Data for restriction and derived direct image along an open immersion.

The two direct images are kept separately so the displayed `*_ = !_`
identity in the source has a faithful interface.  The Hom equivalence records
the adjunction used when the proof identifies Hom spaces after restriction.
-/
structure OpenImmersionData
    (X U : Scheme) (C D : Type*)
    [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    [DerivedCategoryData X C] [DerivedCategoryData U D] where
  j : U ⟶ X
  isOpenImmersion : IsOpenImmersion j
  restrict : C → D
  pushforwardStar : D → C
  pushforwardShriek : D → C
  starShriekIso : ∀ K : D, Nonempty (pushforwardStar K ≅ pushforwardShriek K)
  truncGEMap : ∀ (a : ℤ) (E : C),
    TruncGE (X := X) (C := C) E a ⟶
      TruncGE (X := X) (C := C) (pushforwardStar (restrict E)) a
  truncLEMap : ∀ (a : ℤ) (E : C),
    TruncLE (X := X) (C := C) E a ⟶
      TruncLE (X := X) (C := C) (pushforwardStar (restrict E)) a
  homEquiv : ∀ (K : D) (E : C) (i : ℤ),
    (Shift (X := U) (C := D) K (-i) ⟶ restrict E) ≃
      (Shift (X := X) (C := C) (pushforwardStar K) (-i) ⟶ E)

variable {X U : Scheme} {C D : Type*}
  [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  [DerivedCategoryData X C] [DerivedCategoryData U D]

/-- The canonical maps in the two orthogonality lemmas. -/
def TruncGEComparison (R : OpenImmersionData X U C D) (E : C) (a : ℤ) :
    TruncGE (X := X) (C := C) E a ⟶
      TruncGE (X := X) (C := C) (R.pushforwardStar (R.restrict E)) a :=
  R.truncGEMap a E

def TruncLEComparison (R : OpenImmersionData X U C D) (E : C) (a : ℤ) :
    TruncLE (X := X) (C := C) E a ⟶
      TruncLE (X := X) (C := C) (R.pushforwardStar (R.restrict E)) a :=
  R.truncLEMap a E

/-- The Koszul object used in the first two source lemmas.

The ambient derived category supplies the construction in concrete
applications; this witness records the two properties used by the arguments:
perfectness and vanishing after restriction to the open complement. -/
structure KoszulObject (R : OpenImmersionData X U C D)
    (A : Type*) [CommRing A] (r : ℕ) (f : Fin r → A) where
  object : C
  perfect : IsPerfect (X := X) (C := C) object
  restrict_isZero : IsZero (R.restrict object)

def KoszulExtension (R : OpenImmersionData X U C D) (K : D) : C :=
  R.pushforwardStar K

/-- The first equality in the source's displayed definition of `K'`. -/
theorem koszulExtension_eq_pushforwardStar
    (R : OpenImmersionData X U C D) (K : D) :
    KoszulExtension R K = R.pushforwardStar K :=
  rfl

/-- The second equality in the source's displayed definition of `K'`, with
the mathematically correct categorical formulation by isomorphism. -/
theorem koszulExtension_iso_pushforwardShriek
    (R : OpenImmersionData X U C D) (K : D) :
    Nonempty (KoszulExtension R K ≅ R.pushforwardShriek K) :=
  R.starShriekIso K

end Formalization.Books.Perfect.Unit40
