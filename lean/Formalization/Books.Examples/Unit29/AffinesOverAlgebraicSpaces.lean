import Formalization.«Books.SpacesCohomology».Unit01.Core
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Examples, Chapter 29: Affines over algebraic spaces

This file records the scheme-theoretic embedding theorem and the two
coordinate presentations of its failure for algebraic spaces.  Mathlib has
the relative affine-space and coordinate-function API for schemes, while the
project's earlier `AlgebraicSpaceTheory` interface supplies the properties of
algebraic-space morphisms.  The latter is deliberately reused here because
the current Mathlib snapshot has no intrinsic algebraic-space library.
-/

namespace Formalization.«Books.Examples».Unit29

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open Formalization.«Books.SpacesCohomology».Unit01
open scoped AlgebraicGeometry

universe u

/-! ## The scheme-theoretic statement -/

/-- The relative affine `n`-space used in the scheme statement.

`AffineSpace` indexes coordinates by a type, so `ULift (Fin n)` gives the
finite `n`-coordinate version at the scheme universe `u`.
-/
noncomputable abbrev affineNSpace (n : ℕ) (X : Scheme.{u}) : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace (ULift.{u} (Fin n)) X

/-- The canonical projection `𝔸ⁿ_X ⟶ X`. -/
noncomputable abbrev affineNSpaceProjection (n : ℕ) (X : Scheme.{u}) :
    affineNSpace n X ⟶ X :=
  affineNSpace n X ↘ X

/--
For an affine scheme locally of finite type over a scheme, some finite
relative affine space contains it by an immersion over the base.

The theorem is the chapter's first assertion.  The coordinate description of
maps into the target is already available through
`AlgebraicGeometry.AffineSpace.homOfVector` and `homOverEquiv`.
-/
theorem exists_scheme_affine_immersion
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType f] :
    ∃ n : ℕ, ∃ g : Y ⟶ affineNSpace n X,
      AlgebraicGeometry.IsImmersion g ∧
        g ≫ affineNSpaceProjection n X = f := by
  sorry

/-- Every relative affine-space map is determined by its coordinate sections.

This is a source-facing form of Mathlib's existing `AffineSpace` API; no
parallel coordinate-map construction is introduced in this chapter.
-/
theorem affine_space_map_is_coordinate_map
    {X Y : Scheme.{u}} {n : ℕ} (f : Y ⟶ X)
    (g : Y ⟶ affineNSpace n X)
    (hg : g ≫ affineNSpaceProjection n X = f) :
    ∃ v : ULift.{u} (Fin n) → Γ(Y, ⊤),
      g = AlgebraicGeometry.AffineSpace.homOfVector f v := by
  sorry

/-! ## The algebraic-space interface used below -/

/--
The property that a morphism of algebraic spaces is an immersion, expressed
by the standard open-after-closed factorization.  The two factors reuse the
earlier chapter's `IsClosedImmersion` and `IsOpenImmersion` interfaces.
-/
def SpaceImmersion {X Y : AlgebraicSpace.{u}}
    [AlgebraicSpaceTheory.{u}] (f : SpaceHom X Y) : Prop :=
  ∃ (Z : AlgebraicSpace.{u}) (i : SpaceHom X Z) (j : SpaceHom Z Y),
    IsClosedImmersion i ∧ IsOpenImmersion j ∧ i ≫ j = f

/-- An affine scheme represented in the algebraic-space interface. -/
def IsAffineSchemeSpace (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] : Prop :=
  IsScheme X ∧
    ∃ S : Scheme.{u}, AlgebraicGeometry.IsAffine S ∧
      Nonempty ((S : AlgebraicSpace.{u}) ≅ X)

/-- Quasi-separatedness of an algebraic space, using the identity morphism. -/
def IsQuasiSeparatedSpace (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] : Prop :=
  IsQuasiSeparated (𝟙 X)

/--
The missing canonical algebraic-space family `𝔸ⁿ_X`, retained as the minimal
interface needed by this chapter.  Its objects and projections are the
relative affine spaces and their structure maps in the source.
-/
structure RelativeAffineSpaceFamily (X : AlgebraicSpace.{u}) where
  object : ℕ → AlgebraicSpace.{u}
  projection : ∀ n : ℕ, SpaceHom (object n) X
  isRelativeAffineSpace : ∀ _n : ℕ, Prop

/-- A morphism admits an immersion into one member of a relative affine-space family. -/
def HasRelativeAffineSpaceImmersion
    {Y X : AlgebraicSpace.{u}} (family : RelativeAffineSpaceFamily X)
  (f : SpaceHom Y X) [AlgebraicSpaceTheory.{u}] : Prop :=
  ∃ n : ℕ, family.isRelativeAffineSpace n ∧
    ∃ g : SpaceHom Y (family.object n),
      SpaceImmersion g ∧ g ≫ family.projection n = f

/-! ## The translation quotient `[𝔸¹_k / ℤ]` -/

/-- The translation action of an integer on the affine-line coordinate. -/
def integerTranslation (k : Type u) [Field k] [CharZero k] (n : ℤ) (t : k) : k :=
  t + (n : k)

theorem integerTranslation_zero (k : Type u) [Field k] [CharZero k] (t : k) :
    integerTranslation k 0 t = t := by
  simp [integerTranslation]

theorem integerTranslation_add (k : Type u) [Field k] [CharZero k]
    (m n : ℤ) (t : k) :
    integerTranslation k (m + n) t =
      integerTranslation k m (integerTranslation k n t) := by
  simp [integerTranslation, add_comm, add_left_comm]

/-- The orbit relation underlying the translation quotient. -/
def translationOrbitRelation (k : Type u) [Field k] [CharZero k] (t t' : k) : Prop :=
  ∃ n : ℤ, integerTranslation k n t = t'

theorem translationOrbitRelation_equivalence (k : Type u) [Field k] [CharZero k] :
    Equivalence (translationOrbitRelation k) := by
  sorry

/-- The infinite disjoint union of copies of the affine line in the first pullback. -/
noncomputable def countableAffineLineCoproduct (k : Type u) [Field k] : Scheme.{u} :=
  ∐ fun _ : ℕ => Spec (.of (Polynomial k))

/-!
The source's first example is represented by the following data.  The
surjective cover and the two maps record the displayed presentation, while
the final theorem records the failure of an affine-space immersion.
-/
structure TranslationQuotientExample (k : Type u) [Field k] [CharZero k]
    [AlgebraicSpaceTheory.{u}] where
  quotient : AlgebraicSpace.{u}
  affineLineCover : (Spec (.of (Polynomial k)) : AlgebraicSpace.{u}) ⟶ quotient
  pointMap : (Spec (.of k) : AlgebraicSpace.{u}) ⟶ quotient
  affineLineCover_surjective : IsSurjective affineLineCover
  quotientRelation : k → k → Prop
  quotientRelation_eq : quotientRelation = translationOrbitRelation k
  family : RelativeAffineSpaceFamily quotient
  pointMap_source_is_affine_scheme :
    IsAffineSchemeSpace (Spec (.of k) : AlgebraicSpace.{u})
  pointMap_locallyOfFiniteType : IsLocallyOfFiniteType pointMap

/--
The source-facing interface for the pullback in the translation example.
`map_is_pullback_coordinate_map` is the missing algebraic-space base-change
predicate; the carrier, target, and non-immersion conclusion are concrete
scheme data.
-/
structure TranslationPullbackPresentation (k : Type u) [Field k] [CharZero k]
    [AlgebraicSpaceTheory.{u}] (E : TranslationQuotientExample k)
    (n : ℕ)
    (g : SpaceHom (Spec (.of k) : AlgebraicSpace.{u}) (E.family.object n))
    where
  over_base : g ≫ E.family.projection n = E.pointMap
  carrier : Scheme.{u}
  carrier_is_countable_affine_line_coproduct :
    Nonempty (carrier ≅ countableAffineLineCoproduct k)
  map : carrier ⟶ affineNSpace (n + 1) (Spec (.of k))
  map_is_pullback_coordinate_map : Prop

theorem translation_quotient_pullback_is_not_immersion
    (k : Type u) [Field k] [CharZero k]
    [AlgebraicSpaceTheory.{u}] (E : TranslationQuotientExample k) (n : ℕ)
    (g : SpaceHom (Spec (.of k) : AlgebraicSpace.{u}) (E.family.object n))
    (hg : g ≫ E.family.projection n = E.pointMap) :
    ∃ P : TranslationPullbackPresentation k E n g,
      P.map_is_pullback_coordinate_map ∧
        ¬ AlgebraicGeometry.IsImmersion P.map := by
  sorry

theorem translation_quotient_counterexample_exists
    (k : Type u) [Field k] [CharZero k]
    [AlgebraicSpaceTheory.{u}] :
    ∃ E : TranslationQuotientExample k,
      ¬ HasRelativeAffineSpaceImmersion E.family E.pointMap := by
  sorry

/-! ## The doubled affine line `𝔸¹_k / R` -/

/-- The relation `R = Δ ⊔ {(t,-t) | t ≠ 0}` from the second example. -/
def doubledAffineLineRelation (k : Type u) [Field k] (t t' : k) : Prop :=
  t = t' ∨ (t ≠ 0 ∧ t' = -t)

/-- The relation `R` as a subset of the product of two affine-line coordinates. -/
def doubledAffineLineRelationSet (k : Type u) [Field k] : Set (k × k) :=
  {p | doubledAffineLineRelation k p.1 p.2}

theorem doubledAffineLineRelation_equivalence (k : Type u) [Field k] [CharZero k] :
    Equivalence (doubledAffineLineRelation k) := by
  sorry

/-- The two components in the displayed pullback of the second quotient. -/
abbrev secondPullbackCoordinateCarrier (k : Type u) [Field k] :=
  k ⊕ {t : k // t ≠ 0}

/--
The coordinate map from the displayed disjoint union to the `(n+1)`-tuple
coordinates.  The codomain is written as `(Fin n → k) × k`, which is
canonically the same finite affine space and makes the two branches visible.
-/
def secondPullbackCoordinateMap (k : Type u) [Field k] {n : ℕ}
    (f : Fin n → Polynomial k) :
    secondPullbackCoordinateCarrier k → (Fin n → k) × k :=
  Sum.elim
    (fun t => ((fun i => (f i).eval t), t))
    (fun t => ((fun i => (f i).eval (t : k)), -(t : k)))

/-- The image of the displayed coordinate map. -/
def secondPullbackCoordinateImage (k : Type u) [Field k] {n : ℕ}
    (f : Fin n → Polynomial k) : Set ((Fin n → k) × k) :=
  Set.range (secondPullbackCoordinateMap k f)

/-!
The relation and coordinate map above are the source's explicit second
counterexample.  The following data records its algebraic-space quotient and
the source properties used in the final failure statement.
-/
structure DoubledAffineLineQuotientExample (k : Type u) [Field k] [CharZero k]
    [AlgebraicSpaceTheory.{u}] where
  quotient : AlgebraicSpace.{u}
  quotientMap : (Spec (.of (Polynomial k)) : AlgebraicSpace.{u}) ⟶ quotient
  relation : Set (k × k)
  relation_eq : relation = doubledAffineLineRelationSet k
  family : RelativeAffineSpaceFamily quotient
  quotientMap_source_is_affine_scheme :
    IsAffineSchemeSpace (Spec (.of (Polynomial k)) : AlgebraicSpace.{u})
  quotientMap_locallyOfFiniteType : IsLocallyOfFiniteType quotientMap
  quotient_is_quasiSeparated : IsQuasiSeparatedSpace quotient

theorem doubled_affine_line_counterexample_exists
    (k : Type u) [Field k] [CharZero k]
    [AlgebraicSpaceTheory.{u}] :
    ∃ E : DoubledAffineLineQuotientExample k,
      ¬ HasRelativeAffineSpaceImmersion E.family E.quotientMap := by
  sorry

/-! ## The final no-embedding lemma -/

/--
There is a finite-type morphism from an affine scheme to a quasi-separated
algebraic space which has no immersion into any relative finite affine space.
-/
theorem exists_finiteType_affine_algebraicSpace_no_immersion
    [AlgebraicSpaceTheory.{u}] :
    ∃ (Y X : AlgebraicSpace.{u}) (f : SpaceHom Y X)
      (family : RelativeAffineSpaceFamily X),
      IsAffineSchemeSpace Y ∧ IsFiniteType f ∧
        IsQuasiSeparatedSpace X ∧
          ¬ HasRelativeAffineSpaceImmersion family f := by
  sorry

end

end Formalization.«Books.Examples».Unit29
