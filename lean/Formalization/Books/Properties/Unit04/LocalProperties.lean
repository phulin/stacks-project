import Formalization.Books.Properties.Unit03
import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Properties of Schemes, Chapter 4: Types of schemes defined by properties of rings

The source section is `books/properties.tex:294--411`.  A local ring
property reuses Mathlib's `LocalizationPreserves` for the localization clause;
the finite standard-cover clause is stated directly because Mathlib's
similarly named finite-span API is for properties of ring homomorphisms.
-/

namespace Formalization.Books.Properties.Unit04

open AlgebraicGeometry

universe u v

/-! ## Definition `definition-property-local` -/

/-- A property of commutative rings is local in the sense of the source.

`LocalizationPreserves` is the source's principal-localization condition.  The
finite-span condition is stated here for properties of rings; Mathlib's
similarly named finite-span API is for properties of ring homomorphisms.
-/
def OfLocalizationFiniteSpan
    (P : ∀ (R : Type u) [CommRing R], Prop) : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (f : Fin n → R),
    Ideal.span (Set.range f) = ⊤ →
      (∀ i, P (Localization.Away (f i))) → P R

def IsLocalRingProperty
    (P : ∀ (R : Type u) [CommRing R], Prop) : Prop :=
  LocalizationPreserves P ∧ OfLocalizationFiniteSpan P

/-! ## Definition `definition-locally-P` -/

/-- A scheme is locally `P` when every point has an affine open neighbourhood
whose ring of sections satisfies `P`.
-/
def IsLocally
    (P : ∀ (R : Type u) [CommRing R], Prop) (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ P Γ(X, U)

/-! ## Lemma `lemma-locally-P` -/

/-- The four equivalent formulations of being locally `P` from the source.

The third and fourth formulations use indexed families of open subsets; an
open subset is regarded as its canonical open subscheme in the fourth.
-/
theorem lemma_locally_P
    (P : ∀ (R : Type u) [CommRing R], Prop)
    (hP : IsLocalRingProperty P) (X : Scheme.{u}) :
    List.TFAE [
      IsLocally P X,
      ∀ U : X.Opens, IsAffineOpen U → P Γ(X, U),
      ∃ (I : Type v) (U : I → X.Opens),
        TopologicalSpace.IsOpenCover U ∧
          ∀ i, IsAffineOpen (U i) ∧ P Γ(X, U i),
      ∃ (I : Type v) (U : I → X.Opens),
        TopologicalSpace.IsOpenCover U ∧
          ∀ i, IsLocally P (U i : Scheme)] := by
  sorry

/-- Locality is inherited by every open subscheme. -/
theorem isLocally_of_isLocally
    (P : ∀ (R : Type u) [CommRing R], Prop)
    (hP : IsLocalRingProperty P) {X : Scheme.{u}}
    (hX : IsLocally P X) (U : X.Opens) :
    IsLocally P (U : Scheme) := by
  sorry

/-! ## Lemma `lemma-reduced-is-locally-reduced` -/

/-- Reducedness is equivalent to being locally reduced in the source's sense.
-/
theorem lemma_reduced_is_locally_reduced (X : Scheme.{u}) :
    AlgebraicGeometry.IsReduced X ↔
      IsLocally (fun (R : Type u) [CommRing R] => _root_.IsReduced R) X := by
  sorry

/-! ## Lemma `lemma-properties-local` -/

/-- The source's Noetherian Cohen--Macaulay ring property.

The earlier Algebra chapter defines Cohen--Macaulayness only under a
Noetherian instance, so the existential packages that required instance into
the ring property.
-/
def IsNoetherianCohenMacaulay
    (R : Type u) [CommRing R] : Prop :=
  ∃ hR : IsNoetherianRing R,
    @Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing R _ hR

/-- The source's Noetherian regular ring property, using Mathlib's canonical
regular-ring class, which extends `IsNoetherianRing`.
-/
def IsNoetherianRegular
    (R : Type u) [CommRing R] : Prop :=
  IsRegularRing R

/-- The source's “finite type over `ℤ`” property. -/
def IsFiniteTypeOverIntegers
    (R : Type u) [CommRing R] : Prop :=
  Algebra.FiniteType ℤ R

/-- Cohen--Macaulay, regular, and finite-type-over-`ℤ` are local ring
properties, as listed in the source.
-/
theorem lemma_properties_local :
    IsLocalRingProperty (fun (R : Type u) [CommRing R] =>
      IsNoetherianCohenMacaulay R) ∧
    IsLocalRingProperty (fun (R : Type u) [CommRing R] =>
      IsNoetherianRegular R) ∧
    IsLocalRingProperty (fun (R : Type u) [CommRing R] =>
      IsFiniteTypeOverIntegers R) := by
  sorry

end Formalization.Books.Properties.Unit04
