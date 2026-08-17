import Mathlib.Order.WithBotTop
import Formalization.Books.Derived.Unit16.HigherDerivedFunctors

/-!
# Derived Categories, Chapter 32: bounded cohomological dimension

This file records the replacement argument and the unbounded derived-functor
statements in the chapter.  The derived categories, their cohomology functors,
and the bounded derived-functor interfaces are the canonical Mathlib and
earlier-chapter constructions.  The comparison and termination arguments are
the theorem interfaces whose proofs are deferred to the proving stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit16
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u w' v' u'

namespace Formalization.Books.Derived.Unit32

/-! ## 32.1. The replacement degree function -/

/- The source uses the values `0, 1, 2, ..., ∞`.  `WithTop ℕ` is Mathlib's
   existing implementation of exactly this ordered set. -/

/-- The three axioms imposed on the source's degree function. -/
def IsAdmissibleDegreeFunction
    {A : Type u} [Category.{v} A] [Abelian A]
    (d : A → WithTop ℕ) : Prop :=
  (∀ X : A, ∃ (Y : A) (i : X ⟶ Y), Mono i ∧ d Y = 0) ∧
    (∀ X Y : A, d (X ⊞ Y) ≤ max (d X) (d Y)) ∧
      (∀ (S : ShortComplex A), S.ShortExact →
        d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂))

/-- The source's condition that `n + d(Kⁿ)` tends to `-∞` on the left.

The existential natural number records that the degree is finite at all
sufficiently negative terms; the final inequality is the usual spelling of
the limit in the ordered set `WithTop ℕ`. -/
def DegreeFunctionNegativeTail
    {A : Type u} [Category.{v} A] [Abelian A]
    (d : A → WithTop ℕ) (K : BookComplex A) : Prop :=
  ∀ b : ℤ, ∃ N : ℤ, ∀ n : ℤ, n ≤ N →
    ∃ m : ℕ, d (K.X n) = (m : WithTop ℕ) ∧ n + (m : ℤ) ≤ b

/- The elementary replacement in the proof is the cokernel of the map
   `(u, d_K^n) : K^n → M ⊕ K^(n+1)`.  The object and map are exposed because
   they are the only noncanonical construction used by the termination
   argument. -/

/-- The map whose cokernel is the next term in an elementary replacement. -/
noncomputable def elementaryReplacementMap
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : BookComplex A) (n : ℤ) (M : A)
    (u : K.X n ⟶ M) : K.X n ⟶ M ⊞ K.X (n + 1) :=
  biprod.lift u (K.d n (n + 1))

/-- The cokernel object `M'` in the elementary replacement step. -/
noncomputable def elementaryReplacementObject
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : BookComplex A) (n : ℤ) (M : A)
    (u : K.X n ⟶ M) : A :=
  cokernel (elementaryReplacementMap K n M u)

/-- Data for one elementary replacement step in the proof of the resolution
  lemma.  The fields record the quasi-isomorphism, the changed degrees, and
  the cokernel description of the new term. -/
structure ElementaryDegreeZeroReplacement
    {A : Type u} [Category.{v} A] [Abelian A]
    (d : A → WithTop ℕ) (K : BookComplex A) (n : ℤ) (M : A)
    (u : K.X n ⟶ M) where
  replaced : BookComplex A
  comparison : K ⟶ replaced
  quasiIso : QuasiIsomorphism comparison
  mono : Mono u
  targetDegreeZero : d M = 0
  degreeZero : d (replaced.X n) = 0
  nextDegreeBound :
    d (replaced.X (n + 1)) ≤
      max (d (K.X n) - 1) (d (K.X (n + 1)))
  unchanged : ∀ m : ℤ, m ≠ n → m ≠ n + 1 →
    d (replaced.X m) = d (K.X m)
  nextIsCokernel :
    Nonempty (replaced.X (n + 1) ≅ elementaryReplacementObject K n M u)

/-- An elementary replacement can be made at every positive-degree term. -/
theorem exists_elementaryDegreeZeroReplacement
    {A : Type u} [Category.{v} A] [Abelian A]
    (d : A → WithTop ℕ) (hd : IsAdmissibleDegreeFunction d)
    (K : BookComplex A) (n : ℤ)
    (hn : 0 < d (K.X n)) :
    ∃ (M : A) (u : K.X n ⟶ M), Mono u ∧ d M = 0 ∧
      Nonempty (ElementaryDegreeZeroReplacement d K n M u) := by
  sorry

/-- A complex satisfying the negative-tail hypothesis has a
  quasi-isomorphic representative whose every term has degree zero. -/
theorem exists_quasiIso_degreeZero_complex
    {A : Type u} [Category.{v} A] [Abelian A]
    (d : A → WithTop ℕ) (hd : IsAdmissibleDegreeFunction d)
    (K : BookComplex A) (hK : DegreeFunctionNegativeTail d K) :
    ∃ (L : BookComplex A) (f : K ⟶ L),
      QuasiIsomorphism f ∧ ∀ n : ℤ, d (L.X n) = 0 := by
  sorry

/-! The source's `ξ(K)` and the finite set `I` are termination measures for
the preceding theorem.  Their finiteness and strict decrease are proof
infrastructure rather than additional book-level assertions; the theorem
above records their mathematical output. -/

/-! ## 32.2. Unbounded derived functors -/

/-- The canonical `≤ a` truncation of an unbounded derived object. -/
noncomputable def derivedTruncLEFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (a : ℤ) :
    DerivedCategory A ⥤ DerivedCategory A :=
  (DerivedCategory.TStructure.t (C := A)).truncLE a

/-- The canonical `≥ a` truncation of an unbounded derived object. -/
noncomputable def derivedTruncGEFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (a : ℤ) :
    DerivedCategory A ⥤ DerivedCategory A :=
  (DerivedCategory.TStructure.t (C := A)).truncGE a

/-- The canonical map from a `≤ a` truncation to the original object. -/
noncomputable def derivedTruncLEMap
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (E : DerivedCategory A) (a : ℤ) :
    (derivedTruncLEFunctor a).obj E ⟶ E :=
  ((DerivedCategory.TStructure.t (C := A)).truncLEι a).app E

/-- The canonical map from an object to its `≥ a` truncation. -/
noncomputable def derivedTruncGEMap
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (E : DerivedCategory A) (a : ℤ) :
    E ⟶ (derivedTruncGEFunctor a).obj E :=
  ((DerivedCategory.TStructure.t (C := A)).truncGEπ a).app E

/- The following endpoint operations keep the source's `-∞` and `∞` cases
   while applying the finite shift `n - 1` only to an integral endpoint. -/

/-- The upper endpoint shift `b ↦ b + n - 1` in the range theorem. -/
def shiftUpperBound (b : EInt) (n : ℕ) : EInt :=
  WithBotTop.rec (motive := fun _ => EInt) (⊥ : EInt)
    (fun z => ((z + (n : ℤ) - 1 : ℤ) : EInt)) (⊤ : EInt) b

/-- The lower endpoint shift `a ↦ a - n + 1` in the dual range theorem. -/
def shiftLowerBound (a : EInt) (n : ℕ) : EInt :=
  WithBotTop.rec (motive := fun _ => EInt) (⊥ : EInt)
    (fun z => ((z - (n : ℤ) + 1 : ℤ) : EInt)) (⊤ : EInt) a

/-- Cohomology vanishes outside the extended-integer interval `[a,b]`. -/
def cohomologyVanishesOutside
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (E : DerivedCategory C)
    (a b : EInt) : Prop :=
  ∀ i : ℤ, ¬ (a ≤ (i : EInt) ∧ (i : EInt) ≤ b) →
    IsZero ((derivedCohomologyFunctor C i).obj E)

/-- The degree of an object computed from the nonzero higher right-derived
  functors, with `0` included exactly as in the source. -/
noncomputable def rightDerivedDegree
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F) (X : A) :
    WithTop ℕ :=
  sSup (({0} : Set (WithTop ℕ)) ∪
    {d : WithTop ℕ | ∃ i : ℕ,
      d = (i : WithTop ℕ) ∧
        ¬ IsZero ((higherRightDerivedFunctor F R.functor (i : ℤ)).obj X)})

/-- The degree function used in the source proof satisfies the three
  admissibility axioms. -/
theorem rightDerivedDegree_isAdmissible
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] (hF : IsLeftExact F)
    (R : RightDerivedFunctorData F) (hR : InjectsIntoRightAcyclic R)
    (hn : ∃ n : ℕ, ∀ X : A,
      IsZero ((higherRightDerivedFunctor F R.functor (n : ℤ)).obj X)) :
    IsAdmissibleDegreeFunction (rightDerivedDegree R) := by
  sorry

/-- Higher right-derived functors vanish in every degree at least as large as
  a vanishing degree. -/
theorem rightDerived_vanishes_of_ge
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F)
    (n m : ℕ) (hnm : n ≤ m)
    (hn : ∀ X : A,
      IsZero ((higherRightDerivedFunctor F R.functor (n : ℤ)).obj X)) :
    ∀ X : A,
      IsZero ((higherRightDerivedFunctor F R.functor (m : ℤ)).obj X) := by
  sorry

/-- The unbounded right-derived conclusion, including the two truncation
  comparisons and the cohomological range bound from the source. -/
structure UnboundedRightDerivedConclusion
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive]
    (R : RightDerivedFunctorData F) (n : ℕ) where
  data : UnboundedRightDerivedFunctorData F
  computesRightAcyclic :
    ∀ K : BookComplex A,
      (∀ i : ℤ, RightAcyclic R (K.X i)) →
        ComputesUnboundedRightDerivedComplex data K
  rightAcyclicReplacement :
    ∀ K : BookComplex A, ∃ (L : BookComplex A) (f : K ⟶ L),
      QuasiIsomorphism f ∧ ∀ i : ℤ, RightAcyclic R (L.X i)
  truncLEIso :
    ∀ (E : DerivedCategory A) (a i : ℤ), i ≤ a →
      IsIso ((derivedCohomologyFunctor B i).map
        (data.functor.map (derivedTruncLEMap E a)))
  truncGEIso :
    ∀ (E : DerivedCategory A) (b i : ℤ), b ≤ i →
      IsIso ((derivedCohomologyFunctor B i).map
        (data.functor.map (derivedTruncGEMap E (b - (n : ℤ) + 1))))
  boundedRange :
    ∀ (E : DerivedCategory A) (a b : EInt), a ≤ b →
      cohomologyVanishesOutside E a b →
        cohomologyVanishesOutside (data.functor.obj E) a
          (shiftUpperBound b n)

/-- A left exact functor of bounded cohomological dimension has an unbounded
  right-derived functor with the source's computation, truncation, and range
  properties. -/
theorem exists_unboundedRightDerived
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] (hF : IsLeftExact F)
    (R : RightDerivedFunctorData F) (hR : InjectsIntoRightAcyclic R)
    (n : ℕ) (hn : ∀ X : A,
      IsZero ((higherRightDerivedFunctor F R.functor (n : ℤ)).obj X)) :
    Nonempty (UnboundedRightDerivedConclusion R n) := by
  sorry

/-! ## 32.3. The dual left-derived statement -/

/-- The higher left-derived functor, viewed in the unbounded derived category
  through the canonical inclusion of `D⁻`. -/
noncomputable def higherLeftDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] (LF : DMinus A ⥤ DMinus B) (i : ℤ) :
    A ⥤ B :=
  singleMinusFunctor (A := A) 0 ⋙ minusDerivedLocalizationFunctor A ⋙ LF ⋙
    DerivedCategory.Minus.ι (C := B) ⋙ derivedCohomologyFunctor B i

/-- The unbounded left-derived functor before choosing its computation data. -/
structure UnboundedLeftDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] where
  functor : DerivedCategory A ⥤ DerivedCategory B
  counit :
    DerivedCategory.Qh (C := A) ⋙ functor ⟶
      additiveHomotopyFunctor F ⋙ DerivedCategory.Qh (C := B)
  isLeftDerived :
    functor.IsLeftDerivedFunctor counit (quasiIsoHomotopyProperty A)
  exact : Nonempty (ExactTriangulatedFunctorData functor)

/-- A complex all of whose terms are left acyclic computes the unbounded
  left-derived functor. -/
def ComputesUnboundedLeftDerivedComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive]
    (L : UnboundedLeftDerivedFunctorData F) (K : BookComplex A) : Prop :=
  IsIso (L.counit.app
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))

/-- The degree function used in the dual proof. -/
noncomputable def leftDerivedDegree
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (L : LeftDerivedFunctorData F) (X : A) :
    WithTop ℕ :=
  sSup (({0} : Set (WithTop ℕ)) ∪
    {d : WithTop ℕ | ∃ i : ℕ,
      d = (i : WithTop ℕ) ∧
        ¬ IsZero ((higherLeftDerivedFunctor F L.functor (i : ℤ)).obj X)})

/-- The dual degree function satisfies the same replacement axioms. -/
theorem leftDerivedDegree_isAdmissible
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] (hF : IsRightExact F)
    (L : LeftDerivedFunctorData F) (hL : QuotientOfLeftAcyclic L)
    (hn : ∃ n : ℕ, ∀ X : A,
      IsZero ((higherLeftDerivedFunctor F L.functor (n : ℤ)).obj X)) :
    IsAdmissibleDegreeFunction (leftDerivedDegree L) := by
  sorry

/-- The dual unbounded conclusion, with all three source assertions. -/
structure UnboundedLeftDerivedConclusion
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive]
    (L : LeftDerivedFunctorData F) (n : ℕ) where
  data : UnboundedLeftDerivedFunctorData F
  computesLeftAcyclic :
    ∀ K : BookComplex A,
      (∀ i : ℤ, LeftAcyclic L (K.X i)) →
        ComputesUnboundedLeftDerivedComplex data K
  leftAcyclicReplacement :
    ∀ K : BookComplex A, ∃ (M : BookComplex A) (f : M ⟶ K),
      QuasiIsomorphism f ∧ ∀ i : ℤ, LeftAcyclic L (M.X i)
  truncLEIso :
    ∀ (E : DerivedCategory A) (a i : ℤ), i ≤ a →
      IsIso ((derivedCohomologyFunctor B i).map
        (data.functor.map (derivedTruncLEMap E (a + (n : ℤ) - 1))))
  truncGEIso :
    ∀ (E : DerivedCategory A) (b i : ℤ), b ≤ i →
      IsIso ((derivedCohomologyFunctor B i).map
        (data.functor.map (derivedTruncGEMap E b)))
  boundedRange :
    ∀ (E : DerivedCategory A) (a b : EInt), a ≤ b →
      cohomologyVanishesOutside E a b →
        cohomologyVanishesOutside (data.functor.obj E)
          (shiftLowerBound a n) b

/-- A right exact functor of bounded cohomological dimension has the dual
  unbounded left-derived functor. -/
theorem exists_unboundedLeftDerived
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] (hF : IsRightExact F)
    (L : LeftDerivedFunctorData F) (hL : QuotientOfLeftAcyclic L)
    (n : ℕ) (hn : ∀ X : A,
      IsZero ((higherLeftDerivedFunctor F L.functor (n : ℤ)).obj X)) :
    Nonempty (UnboundedLeftDerivedConclusion L n) := by
  sorry

end Formalization.Books.Derived.Unit32
