import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Morphisms of Schemes, Chapter 14: Types of morphisms defined by properties of ring maps

This file formalizes the generic property-of-ring-maps framework from the
chapter.  The existing Mathlib definitions are used for affine-local
morphisms and for stability under base change and composition; the
source-facing pointwise definition is recorded explicitly here.
-/

namespace Formalization.Books.Morphisms.Unit14

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry BigOperators

universe u

/-- A property of homomorphisms of commutative rings in universe `u`. -/
abbrev RingMapProperty : Type (u + 1) :=
  ∀ {R A : Type u} [CommRing R] [CommRing A], (R →+* A) → Prop

/-! ## Locality and permanence of ring-map properties -/

/-- The three locality clauses in the source definition of a ring-map property.

The second clause is kept in its source-facing form: a map out of a standard
localization of the source may be followed by localization of its target. -/
structure RingMapProperty.IsLocal (P : RingMapProperty.{u}) : Prop where
  localization :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      (f : R →+* A) (r : R),
      P f → P (Localization.awayMap f r)
  source_localization :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      (r : R) (a : A) (f : Localization.Away r →+* A),
      P f →
        P ((algebraMap A (Localization.Away a)).comp
          (f.comp (algebraMap R (Localization.Away r))))
  of_localization_span :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      (f : R →+* A) (n : ℕ) (a : Fin n → A),
      Ideal.span (Set.range a) = ⊤ →
        (∀ i, P ((algebraMap A (Localization.Away (a i))).comp f)) →
          P f

/- The source cautions that the local-neighborhood definition below is only
meaningful as a standard notion when this locality hypothesis is explicitly
assumed; it is therefore retained as a separate hypothesis throughout. -/

/-- Stability under base change, using Mathlib's pushout/tensor-product API. -/
abbrev RingMapProperty.StableUnderBaseChange (P : RingMapProperty.{u}) : Prop :=
  RingHom.IsStableUnderBaseChange @P

/-- Stability under composition, using Mathlib's canonical ring-map interface. -/
abbrev RingMapProperty.StableUnderComposition (P : RingMapProperty.{u}) : Prop :=
  RingHom.StableUnderComposition @P

/-- A morphism is locally of type `P` when every point has affine source and
target neighborhoods on which the induced map of sections has property `P`. -/
def LocallyOfType (P : RingMapProperty.{u}) {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (V : S.Opens)
    (_hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V),
    x ∈ U ∧ P (f.appLE V U hUV).hom

/-- If `P` is local, a locally `P` morphism has property `P` on every affine
source/target pair of opens to which the morphism restricts. -/
theorem locallyOfType_of_affine_pair
    (P : RingMapProperty.{u})
    (hP : RingMapProperty.IsLocal P)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : LocallyOfType P f)
    {U : X.Opens} {V : S.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    P (f.appLE V U hUV).hom := by
  sorry

/-- Characterization of locally `P` morphisms by affine opens and by open
coverings.  The two covering formulations use indexed families of opens;
their `iSup` equalities are the scheme-theoretic open-cover conditions. -/
theorem locallyOfType_characterization
    (P : RingMapProperty.{u})
    (hP : RingMapProperty.IsLocal P)
    {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfType P f ↔
      affineLocally P f ∧
      (∃ (ι : Type u) (V : ι → S.Opens),
        (⨆ j, V j) = ⊤ ∧
          ∀ j, ∃ (κ : Type u) (U : κ → X.Opens),
            (⨆ i, U i) = f ⁻¹ᵁ V j ∧
              (∀ i, U i ≤ f ⁻¹ᵁ V j) ∧
                ∀ i (hUV : U i ≤ f ⁻¹ᵁ V j),
                  LocallyOfType P (f.resLE (V j) (U i) hUV)) ∧
      (∃ (ι : Type u) (V : ι → S.Opens),
        (∀ j, IsAffineOpen (V j)) ∧
          (⨆ j, V j) = ⊤ ∧
            ∀ j, ∃ (κ : Type u) (U : κ → X.Opens),
              (∀ i, IsAffineOpen (U i)) ∧
                (⨆ i, U i) = f ⁻¹ᵁ V j ∧
                  (∀ i, U i ≤ f ⁻¹ᵁ V j) ∧
                    ∀ i (hUV : U i ≤ f ⁻¹ᵁ V j),
                      P (f.appLE (V j) (U i) hUV).hom) := by
  sorry

/-- Locality is inherited by restriction to arbitrary open subschemes. -/
theorem locallyOfType.restrict
    (P : RingMapProperty.{u})
    (hP : RingMapProperty.IsLocal P)
    {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : LocallyOfType P f)
    {U : X.Opens} {V : S.Opens}
    (hUV : U ≤ f ⁻¹ᵁ V) :
    LocallyOfType P (f.resLE V U hUV) := by
  sorry

/-- Composition of locally morphisms of a local property stable under
composition is locally of that property. -/
theorem locallyOfType.comp
    (P : RingMapProperty.{u})
    (hP : RingMapProperty.IsLocal P)
    (hcomp : RingMapProperty.StableUnderComposition P)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocallyOfType P f) (hg : LocallyOfType P g) :
    LocallyOfType P (f ≫ g) := by
  sorry

/-- Base change of a locally morphism for a local, base-change-stable
property remains locally of that property. -/
theorem locallyOfType.baseChange
    (P : RingMapProperty.{u})
    (hP : RingMapProperty.IsLocal P)
    (hbase : RingMapProperty.StableUnderBaseChange P)
    {X S S' : Scheme.{u}} {f : X ⟶ S} (hf : LocallyOfType P f)
    (g : S' ⟶ S) :
    LocallyOfType P (pullback.fst g f) := by
  sorry

/-! ## The properties listed in the source -/

/- The source's sixth list item is the literal placeholder “add more here”; it
does not assert an additional mathematical property. -/

/-- The map on localizations at corresponding primes is an isomorphism. -/
def IsomorphismOnLocalRings : RingMapProperty.{u} :=
  fun {R A} _ _ f =>
    ∀ (p : PrimeSpectrum R) (q : PrimeSpectrum A)
      (hpq : p.asIdeal = q.asIdeal.comap f),
      Function.Bijective (Localization.localRingHom p.asIdeal q.asIdeal f hpq)

/-- The standard-open criterion for a ring map to define an open immersion. -/
def OpenImmersionRingMap : RingMapProperty.{u} :=
  fun {R A} _ _ f =>
    ∀ (q : PrimeSpectrum A),
      ∃ r : R, f r ∉ q.asIdeal ∧ Function.Bijective (Localization.awayMap f r)

/-- Every fibre ring of the map is reduced. -/
def ReducedFibers : RingMapProperty.{u} :=
  fun {R A} _ _ f =>
    letI : Algebra R A := f.toAlgebra
    ∀ p : PrimeSpectrum R, IsReduced (p.asIdeal.Fiber A)

/-- Every fibre ring has Krull dimension at most `n`. -/
def FibersOfDimensionAtMost (n : ℕ) : RingMapProperty.{u} :=
  fun {R A} _ _ f =>
    letI : Algebra R A := f.toAlgebra
    ∀ p : PrimeSpectrum R, Ring.KrullDimLE n (p.asIdeal.Fiber A)

/-- The target ring is Noetherian. -/
def LocallyNoetherianOnTarget : RingMapProperty.{u} :=
  fun {_ A} _ _ _ => IsNoetherianRing A

/-- The five mathematically specified properties in the source are local. -/
theorem properties_local :
    RingMapProperty.IsLocal IsomorphismOnLocalRings ∧
      RingMapProperty.IsLocal OpenImmersionRingMap ∧
        RingMapProperty.IsLocal ReducedFibers ∧
          (∀ n : ℕ, RingMapProperty.IsLocal (FibersOfDimensionAtMost n)) ∧
            RingMapProperty.IsLocal LocallyNoetherianOnTarget := by
  sorry

/-- Isomorphisms on local rings and open-immersion ring maps are stable under
base change. -/
theorem properties_baseChange :
    RingMapProperty.StableUnderBaseChange IsomorphismOnLocalRings ∧
      RingMapProperty.StableUnderBaseChange OpenImmersionRingMap := by
  sorry

/-- Isomorphisms on local rings, open-immersion ring maps, and target
Noetherianity are stable under composition. -/
theorem properties_composition :
    RingMapProperty.StableUnderComposition IsomorphismOnLocalRings ∧
      RingMapProperty.StableUnderComposition OpenImmersionRingMap ∧
        RingMapProperty.StableUnderComposition LocallyNoetherianOnTarget := by
  sorry

end Formalization.Books.Morphisms.Unit14
