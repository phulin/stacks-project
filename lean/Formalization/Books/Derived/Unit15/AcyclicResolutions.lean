import Formalization.Books.Derived.Unit15.ClassicalDerivedFunctors
import Formalization.Books.Homology.Unit07.AdditiveFunctors

/-!
# Derived Categories, Chapter 15: resolutions and acyclic objects

The resolution criteria are stated for cochain complexes using Mathlib's
strict support predicates and degreewise mono/epi conditions.  The exactness
conditions in the acyclicity criteria use the existing four-term
`exactImageSequence` from Homology, Chapter 7; the longer exact sequences in
the source proof are proof scaffolding for these interfaces and introduce no
additional mathematical object.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit15
open Formalization.Books.Homology.Unit07
open scoped ZeroObject

universe w v u v' u'

namespace Formalization.Books.Derived.Unit15

/-! ## Covering families of objects -/

/- Every object is the target of an epimorphism from an object of `Pset`. -/
def QuotientCovering
    {A : Type u} [Category.{v} A] [Abelian A] (Pset : Set A) : Prop :=
  ∀ X : A, ∃ P : A, P ∈ Pset ∧ ∃ q : P ⟶ X, Epi q

/- Every object embeds as a subobject of an object of `Iset`. -/
def SubobjectCovering
    {A : Type u} [Category.{v} A] [Abelian A] (Iset : Set A) : Prop :=
  ∀ X : A, ∃ I : A, I ∈ Iset ∧ ∃ i : X ⟶ I, Mono i

/-! ## Left resolutions -/

section LeftResolutions

variable {A : Type u} [Category.{v} A] [Abelian A]

/- The source's condition `Kⁿ = 0 for n > a` is represented by the canonical
strict-support predicate `K.IsStrictlyLE a`, which is invariant under the
choice of a zero object. -/

/-- A quotient-covering family resolves a strictly bounded-above complex by a
termwise epimorphic quasi-isomorphism with terms in the family. -/
theorem subcategory_left_resolution_termwise
    (Pset : Set A) (hzero : (0 : A) ∈ Pset)
    (hcover : QuotientCovering Pset) (a : ℤ)
    (K : BookComplex A) (hK : K.IsStrictlyLE a) :
    ∃ (P : BookComplex A) (p : P ⟶ K),
      QuasiIso p ∧
        (∀ n : ℤ, P.X n ∈ Pset) ∧
          (∀ n : ℤ, Epi (p.f n)) ∧ P.IsStrictlyLE a := by
  sorry

/-- If the cohomology of a complex vanishes above `a`, a quotient-covering
family gives a quasi-isomorphic complex with the same strict upper bound. -/
theorem subcategory_left_resolution_cohomology
    (Pset : Set A) (hzero : (0 : A) ∈ Pset)
    (hcover : QuotientCovering Pset) (a : ℤ)
    (K : BookComplex A)
    (hK : ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    ∃ (P : BookComplex A) (p : P ⟶ K),
      QuasiIso p ∧ (∀ n : ℤ, P.X n ∈ Pset) ∧ P.IsStrictlyLE a := by
  sorry

end LeftResolutions

/-! ## Right resolutions -/

section RightResolutions

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A subobject-covering family resolves a strictly bounded-below complex by a
termwise monomorphic quasi-isomorphism with terms in the family. -/
theorem subcategory_right_resolution_termwise
    (Iset : Set A) (hzero : (0 : A) ∈ Iset)
    (hcover : SubobjectCovering Iset) (a : ℤ)
    (K : BookComplex A) (hK : K.IsStrictlyGE a) :
    ∃ (I : BookComplex A) (i : K ⟶ I),
      QuasiIso i ∧
        (∀ n : ℤ, I.X n ∈ Iset) ∧
          (∀ n : ℤ, Mono (i.f n)) ∧ I.IsStrictlyGE a := by
  sorry

/-- If the cohomology of a complex vanishes below `a`, a subobject-covering
family gives a quasi-isomorphic complex with the same strict lower bound. -/
theorem subcategory_right_resolution_cohomology
    (Iset : Set A) (hzero : (0 : A) ∈ Iset)
    (hcover : SubobjectCovering Iset) (a : ℤ)
    (K : BookComplex A)
    (hK : ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    ∃ (I : BookComplex A) (i : K ⟶ I),
      QuasiIso i ∧ (∀ n : ℤ, I.X n ∈ Iset) ∧ I.IsStrictlyGE a := by
  sorry

end RightResolutions

/-! ## Acyclic objects from closure properties -/

section AcyclicCriteria

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]

/-- Objects in a subobject-covering family are right acyclic when the family is
closed under the relevant quotients and `F` carries those short exact
sequences to exact sequences. -/
theorem subcategory_right_acyclics
    (Iset : Set A) (hcover : SubobjectCovering Iset)
    (hclosed : ∀ (S : ShortComplex A), S.ShortExact →
      S.X₁ ∈ Iset → S.X₂ ∈ Iset →
        S.X₃ ∈ Iset ∧ (exactImageSequence F S).Exact) :
    ∀ X : A, X ∈ Iset → classicalRightAcyclic F X := by
  sorry

/-- Objects in a quotient-covering family are left acyclic when the family is
closed under the relevant kernels and `F` carries those short exact
sequences to exact sequences. -/
theorem subcategory_left_acyclics
    (Pset : Set A) (hcover : QuotientCovering Pset)
    (hclosed : ∀ (S : ShortComplex A), S.ShortExact →
      S.X₂ ∈ Pset → S.X₃ ∈ Pset →
        S.X₁ ∈ Pset ∧ (exactImageSequence F S).Exact) :
    ∀ X : A, X ∈ Pset → classicalLeftAcyclic F X := by
  sorry

end AcyclicCriteria

end Formalization.Books.Derived.Unit15
