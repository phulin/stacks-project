import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Derived Categories of Varieties, Chapter 10: core interfaces

This file records the categorical interfaces used by the section on sibling
functors.  The ambient category called `Dᵇ(𝒜)` in the source is kept
abstract: the declarations only require its triangulated-category structure,
the inclusion of the abelian heart, and the cohomology functors used by the
two auxiliary lemmas.
-/

namespace Formalization.Books.Equiv.Unit10

open CategoryTheory
open CategoryTheory.Limits

universe u v w

/-! ## Exact functors and siblings -/

variable (C D : Type*) [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  [CategoryTheory.IsTriangulated C] [CategoryTheory.IsTriangulated D]

/-- A functor of triangulated categories, including Mathlib's shift and
distinguished-triangle compatibility data. -/
structure ExactTriangulatedFunctor where
  toFunctor : C ⥤ D
  commShift : toFunctor.CommShift ℤ
  isTriangulated : let _ := commShift; Functor.IsTriangulated toFunctor

attribute [instance] ExactTriangulatedFunctor.commShift
  ExactTriangulatedFunctor.isTriangulated

instance (F : ExactTriangulatedFunctor C D) : F.toFunctor.CommShift ℤ := F.commShift

instance (F : ExactTriangulatedFunctor C D) : F.toFunctor.IsTriangulated := by
  let _ := F.commShift
  exact F.isTriangulated

variable {A : Type*} [Category A] [Abelian A]

/-- The source's notion that two exact functors out of `Dᵇ(𝒜)` are siblings.

The first conjunct is the isomorphism after restriction to the abelian heart;
the second is the objectwise isomorphism on the whole derived category. -/
def Siblings (ι : A ⥤ C) (F F' : ExactTriangulatedFunctor C D) : Prop :=
  Nonempty (ι ⋙ F.toFunctor ≅ ι ⋙ F'.toFunctor) ∧
    ∀ K : C, Nonempty (F.toFunctor.obj K ≅ F'.toFunctor.obj K)

/-! ## Ext and cohomology notation -/

/-- The shifted Hom space used for `Ext^q` in a triangulated category. -/
abbrev TriangulatedExt (X Y : D) (q : ℤ) : Type _ :=
  X ⟶ (shiftFunctor D q).obj Y

/-- Vanishing of a shifted Hom space. -/
def ExtVanishes (X Y : D) (q : ℤ) : Prop :=
  ∀ f : TriangulatedExt (D := D) X Y q, f = 0

/-- Cohomology functors for an abstract model of `Dᵇ(𝒜)`, together with the
canonical identification `H^b(N[-b]) ≅ N` used to extract the top-degree map. -/
class CohomologyData (ι : A ⥤ C) where
  cohomology : ℤ → C ⥤ A
  singleShiftIso : ∀ (N : A) (b : ℤ),
    (cohomology b).obj ((shiftFunctor C (-b)).obj (ι.obj N)) ≅ N

/-- The object denoted `H^i(X)` in the source. -/
def Cohomology (ι : A ⥤ C) [CohomologyData (A := A) (C := C) ι]
    (X : C) (i : ℤ) : A :=
  (CohomologyData.cohomology (A := A) (C := C) ι i).obj X

/-- Vanishing of cohomology above a degree. -/
def CohomologyVanishesAbove (ι : A ⥤ C) [CohomologyData (A := A) (C := C) ι]
    (X : C) (b : ℤ) : Prop :=
  ∀ i : ℤ, b < i → IsZero (Cohomology (A := A) (C := C) ι X i)

/-- Vanishing of cohomology in degrees at least a degree. -/
def CohomologyVanishesAtLeast (ι : A ⥤ C) [CohomologyData (A := A) (C := C) ι]
    (X : C) (b : ℤ) : Prop :=
  ∀ i : ℤ, b ≤ i → IsZero (Cohomology (A := A) (C := C) ι X i)

/-- The map on top cohomology induced by a map from a shifted heart object. -/
def inducedCohomologyMap (ι : A ⥤ C)
    [CohomologyData (A := A) (C := C) ι]
    (N : A) (X : C) (b : ℤ)
    (f : (shiftFunctor C (-b)).obj (ι.obj N) ⟶ X) :
    N ⟶ Cohomology (A := A) (C := C) ι X b :=
  (CohomologyData.singleShiftIso (A := A) (C := C) (ι := ι) N b).inv ≫
    (CohomologyData.cohomology (A := A) (C := C) ι b).map f

/-! ## Enough negative objects and width -/

/-- An abelian category has enough negative objects in the sense of the
source: every object is covered by one receiving no nonzero map from it. -/
def HasEnoughNegativeObjects (A : Type*) [Category A] [Abelian A] : Prop :=
  ∀ X : A, ∃ (N : A) (p : N ⟶ X), Epi p ∧ ∀ f : X ⟶ N, f = 0

/-- The source's bounded-cohomology predicate for an object of `Dᵇ(𝒜)` and a
candidate width.  The interval is `[a, a + w - 1]`. -/
def HasWidth (ι : A ⥤ C)
    [CohomologyData (A := A) (C := C) ι] (X : C) (w : ℕ) : Prop :=
  ∃ a : ℤ, ∀ i : ℤ, (i < a ∨ a + (w : ℤ) ≤ i) →
    IsZero (Cohomology (A := A) (C := C) ι X i)

/-- The minimal width, supplied with the boundedness witness that every
object under consideration has some finite width. -/
noncomputable def Width (ι : A ⥤ C)
    [CohomologyData (A := A) (C := C) ι]
    (X : C) (hX : ∃ w : ℕ, HasWidth (A := A) (C := C) ι X w) : ℕ :=
  by
    classical
    exact Nat.find hX

end Formalization.Books.Equiv.Unit10
