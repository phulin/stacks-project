import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit153
import Formalization.Books.Algebra.Unit154.FilteredColimitsEtale
import Formalization.Books.Algebra.Unit32.LocallyNilpotent
import Formalization.Books.MoreAlgebra.Unit13
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# More on Algebra, Chapter 14: Absolute integral closure

This file records the definitions and theorem interfaces in the section
“Absolute integral closure”.  Polynomial factorizations use Mathlib's
canonical `Polynomial` API.  Filtered colimits of finite free algebras are
expressed using the filtered-colimit data introduced in the commutative
algebra chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit14

open CategoryTheory
open Polynomial

noncomputable section

universe u

/-! ## Absolute integral closure -/

/-- A commutative ring in which every monic polynomial splits into linear
factors.  The list records one possible choice of factors; it is not meant
to impose uniqueness of a factorization. -/
def AbsolutelyIntegrallyClosed (A : Type u) [CommRing A] : Prop :=
  ∀ f : Polynomial A, f.Monic →
    ∃ xs : List A,
      f = (xs.map (fun a : A => Polynomial.X - Polynomial.C a)).prod

/- The factorization definition is equivalent to the root formulation used
   repeatedly in the source proof. -/
theorem absolutelyIntegrallyClosed_iff_monic_has_root
    {A : Type u} [CommRing A] :
    AbsolutelyIntegrallyClosed A ↔
      ∀ f : Polynomial A, f.Monic → ∃ x : A, f.IsRoot x := by
  sorry

/- The two permanence assertions in the source lemma are kept together,
   matching its enumerated conclusion. -/
theorem absolutelyIntegrallyClosed_quotient_localization
    {A : Type u} [CommRing A]
    (hA : AbsolutelyIntegrallyClosed A) (I : Ideal A) (S : Submonoid A) :
    AbsolutelyIntegrallyClosed (A ⧸ I) ∧
      AbsolutelyIntegrallyClosed (Localization S) := by
  sorry

theorem absolutelyIntegrallyClosed_of_integrallyClosed_localization
    {A : Type u} [CommRing A] (S : Submonoid A)
    (hS : S ≤ nonZeroDivisors A)
    (hlocal : AbsolutelyIntegrallyClosed (Localization S))
    (hclosed : IsIntegrallyClosedIn A (Localization S)) :
    AbsolutelyIntegrallyClosed A := by
  sorry

theorem absolutelyIntegrallyClosed_iff_fractionRing_isAlgClosed
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] :
    AbsolutelyIntegrallyClosed A ↔ IsAlgClosed (FractionRing A) := by
  sorry

/-! ## Construction by adjoining roots -/

/-- The finite-free condition on one algebra in a filtered system over `A`.
The ring map supplies the canonical `A`-algebra structure. -/
def IsFiniteFreeAlgebra {A C : Type u} [CommRing A] [CommRing C]
    (f : A →+* C) : Prop :=
  letI : Algebra A C := f.toAlgebra
  Module.Finite A C ∧ Module.Free A C

/-- A filtered colimit presentation whose stages are finite free algebras. -/
structure FilteredFiniteFreeColimit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    extends Formalization.Books.Algebra.Unit154.FilteredColimitData f where
  finiteFree : ∀ i,
    IsFiniteFreeAlgebra (A := A) (diagram.obj i).hom.hom

def IsFilteredColimitOfFiniteFree
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  Nonempty (FilteredFiniteFreeColimit f)

/-- Data for an extension satisfying all three conclusions of the
absolute-integral-closure construction lemma. -/
structure AbsoluteIntegralClosureData
    (A : Type u) [CommRing A] where
  B : CommRingCat.{u}
  algebra : CommRingCat.of A ⟶ B
  injective : Function.Injective algebra.hom
  filteredFiniteFree : IsFilteredColimitOfFiniteFree algebra.hom
  free :
    letI : Algebra A (B : Type u) := algebra.hom.toAlgebra
    Module.Free A (B : Type u)
  absolutelyIntegrallyClosed :
    letI : Algebra A (B : Type u) := algebra.hom.toAlgebra
    AbsolutelyIntegrallyClosed (B : Type u)

theorem construct_absolute_integral_closure
    (A : Type u) [CommRing A] :
    Nonempty (AbsoluteIntegralClosureData A) := by
  sorry

/-! ## Localizations and henselian pairs -/

theorem absolutelyIntegrallyClosed_localization_atPrime_strictlyHenselian
    {A : Type u} [CommRing A] (hA : AbsolutelyIntegrallyClosed A)
    (p : Ideal A) (hp : p.IsPrime) :
    Formalization.Books.Algebra.Unit153.StrictlyHenselianLocalRing
      (Localization.AtPrime p) := by
  sorry

theorem absolutelyIntegrallyClosed_henselianPair_iff
    {A : Type u} [CommRing A] (hA : AbsolutelyIntegrallyClosed A)
    (I : Ideal A) :
    Formalization.Books.MoreAlgebra.Unit13.HenselianPair A I ↔
      I ≤ Ring.jacobson A ∧
        Function.Bijective
          (Formalization.Books.Algebra.Unit32.quotientIdempotentMap I) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit14
