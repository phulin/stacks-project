import Formalization.«Books.Examples».Unit20.BadLocalNoetherianRings
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Dimension in Noetherian Jacobson rings

This file formalizes the construction in the source section.  The affine
plane, finite unions of curves, and the localization are represented by
Mathlib's polynomial, quotient, zero-locus, and localization constructions.
The geometric existence and dimension calculations are theorem interfaces for
the proof stage.
-/

noncomputable section

namespace Formalization.«Books.Examples».Unit21

variable {p : ℕ} [Fact p.Prime]

/-!
## The affine plane over an algebraic closure of a finite field
-/

/-- A canonical algebraic closure of the prime finite field of characteristic `p`. -/
abbrev NoetherianJacobsonField (p : ℕ) [Fact p.Prime] := AlgebraicClosure (ZMod p)

/-- The polynomial ring `k[x, y]`, with variables indexed by `Fin 2`. -/
abbrev NoetherianJacobsonPolynomialRing (p : ℕ) [Fact p.Prime] :=
  MvPolynomial (Fin 2) (NoetherianJacobsonField p)

/-- The affine scheme `X = Spec(k[x, y])`. -/
abbrev NoetherianJacobsonAffinePlane (p : ℕ) [Fact p.Prime] : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (.of (NoetherianJacobsonPolynomialRing p))

/-- The ideal defining the `y`-axis `C = V(x)`. -/
def noetherianJacobsonXAxisIdeal (p : ℕ) [Fact p.Prime] :
    Ideal (NoetherianJacobsonPolynomialRing p) :=
  Ideal.span ({MvPolynomial.X (0 : Fin 2)} :
    Set (NoetherianJacobsonPolynomialRing p))

/-- The closed subset of the affine plane underlying the `y`-axis. -/
def noetherianJacobsonXAxisClosedSet (p : ℕ) [Fact p.Prime] :
    Set (PrimeSpectrum (NoetherianJacobsonPolynomialRing p)) :=
  PrimeSpectrum.zeroLocus
    (noetherianJacobsonXAxisIdeal p : Set (NoetherianJacobsonPolynomialRing p))

/-- A prime closed subscheme of the affine plane of dimension one. -/
def IsNoetherianJacobsonIntegralCurve (p : ℕ) [Fact p.Prime]
    (I : Ideal (NoetherianJacobsonPolynomialRing p)) : Prop :=
  I.IsPrime ∧
    ringKrullDim (NoetherianJacobsonPolynomialRing p ⧸ I) =
      (1 : WithBot ℕ∞)

/-- The chosen axis is an integral closed subscheme of dimension one. -/
theorem noetherianJacobsonXAxis_isIntegralCurve (p : ℕ) [Fact p.Prime] :
    IsNoetherianJacobsonIntegralCurve p (noetherianJacobsonXAxisIdeal p) := by
  sorry

/-- A closed point of the axis, represented by a maximal ideal of the plane
containing the axis ideal. -/
def IsNoetherianJacobsonXAxisClosedPoint (p : ℕ) [Fact p.Prime]
    (I : Ideal (NoetherianJacobsonPolynomialRing p)) : Prop :=
  I.IsMaximal ∧ noetherianJacobsonXAxisIdeal p ≤ I

/-!
## The two enumerations used by the construction
-/

/-- An enumeration of all one-dimensional integral curves other than the axis.

The Lean sequence is indexed by `ℕ`; this is the same countable enumeration as
the source's `C₁, C₂, …`, with a harmless zero-based reindexing. -/
structure NoetherianJacobsonCurveEnumeration (p : ℕ) [Fact p.Prime] where
  curve : ℕ → Ideal (NoetherianJacobsonPolynomialRing p)
  is_curve : ∀ n, IsNoetherianJacobsonIntegralCurve p (curve n)
  injective : Function.Injective curve
  ne_xAxis : ∀ n, curve n ≠ noetherianJacobsonXAxisIdeal p
  exhaustive : ∀ I, IsNoetherianJacobsonIntegralCurve p I →
    I ≠ noetherianJacobsonXAxisIdeal p → ∃ n, curve n = I

/-- An enumeration of the closed points of the axis. -/
structure NoetherianJacobsonPointEnumeration (p : ℕ) [Fact p.Prime] where
  point : ℕ → Ideal (NoetherianJacobsonPolynomialRing p)
  is_point : ∀ n, IsNoetherianJacobsonXAxisClosedPoint p (point n)
  injective : Function.Injective point
  exhaustive : ∀ I, IsNoetherianJacobsonXAxisClosedPoint p I → ∃ n, point n = I

/-- The complete choice of curve and point enumerations in the source. -/
structure NoetherianJacobsonSetup (p : ℕ) [Fact p.Prime] where
  curves : NoetherianJacobsonCurveEnumeration p
  points : NoetherianJacobsonPointEnumeration p

variable {s : NoetherianJacobsonSetup p}

/-- The countability assertions implicit in the source's two enumerations. -/
theorem noetherianJacobson_setup_exists (p : ℕ) [Fact p.Prime] :
    Nonempty (NoetherianJacobsonSetup p) := by
  sorry

/-- The `n`-th closed point of the axis as a point of `Spec(A)`. -/
def noetherianJacobsonPoint (s : NoetherianJacobsonSetup p) (n : ℕ) :
    PrimeSpectrum (NoetherianJacobsonPolynomialRing p) :=
  ⟨s.points.point n, (s.points.is_point n).1.isPrime⟩

/-!
## The finite union `Y` and the separating curves
-/

/-- The ideal defining `C ∪ C₀ ∪ ⋯ ∪ Cₙ`. -/
def noetherianJacobsonFiniteUnionIdeal
    (s : NoetherianJacobsonSetup p) (n : ℕ) :
    Ideal (NoetherianJacobsonPolynomialRing p) :=
  noetherianJacobsonXAxisIdeal p ⊓
    ⨅ i : Fin (n + 1), s.curves.curve i.1

/-- The displayed finite union as a closed subset of `Spec(A)`. -/
def noetherianJacobsonFiniteUnionClosedSet
    (s : NoetherianJacobsonSetup p) (n : ℕ) :
    Set (PrimeSpectrum (NoetherianJacobsonPolynomialRing p)) :=
  noetherianJacobsonXAxisClosedSet p ∪
    ⋃ i : Fin (n + 1),
      PrimeSpectrum.zeroLocus
        (s.curves.curve i.1 : Set (NoetherianJacobsonPolynomialRing p))

/-- The affine scheme `Y = C ∪ C₀ ∪ ⋯ ∪ Cₙ`. -/
abbrev NoetherianJacobsonFiniteUnionScheme
    (s : NoetherianJacobsonSetup p) (n : ℕ) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (.of (NoetherianJacobsonPolynomialRing p ⧸
    noetherianJacobsonFiniteUnionIdeal s n))

/-- The quotient ring used for the global sections of the affine union `Y`. -/
abbrev noetherianJacobsonFiniteUnionGlobalSections
    (s : NoetherianJacobsonSetup p) (n : ℕ) :=
  NoetherianJacobsonPolynomialRing p ⧸ noetherianJacobsonFiniteUnionIdeal s n

/-- The ideal/zero-locus translation of the finite union in the source. -/
theorem noetherianJacobsonFiniteUnionClosedSet_eq_zeroLocus
    (s : NoetherianJacobsonSetup p) (n : ℕ) :
    noetherianJacobsonFiniteUnionClosedSet s n =
      PrimeSpectrum.zeroLocus
        (noetherianJacobsonFiniteUnionIdeal s n :
          Set (NoetherianJacobsonPolynomialRing p)) := by
  sorry

/-- `Y` is reduced, affine of finite type over `k`, and one-dimensional. -/
theorem noetherianJacobsonFiniteUnion_properties
    (s : NoetherianJacobsonSetup p) (n : ℕ) :
    IsReduced (noetherianJacobsonFiniteUnionGlobalSections s n) ∧
      Algebra.FiniteType (NoetherianJacobsonField p)
        (noetherianJacobsonFiniteUnionGlobalSections s n) ∧
      ringKrullDim (noetherianJacobsonFiniteUnionGlobalSections s n) =
        (1 : WithBot ℕ∞) := by
  sorry

/-- The restriction map `A → Γ(Y, 𝒪_Y)`, represented by the quotient map. -/
def noetherianJacobsonRestrictionMap
    (s : NoetherianJacobsonSetup p) (n : ℕ) :
    NoetherianJacobsonPolynomialRing p →+*
      noetherianJacobsonFiniteUnionGlobalSections s n :=
  Ideal.Quotient.mk (noetherianJacobsonFiniteUnionIdeal s n)

/-- The restriction map to the affine union is surjective. -/
theorem noetherianJacobsonRestrictionMap_surjective
    (s : NoetherianJacobsonSetup p) (n : ℕ) :
    Function.Surjective (noetherianJacobsonRestrictionMap s n) := by
  sorry

/-- Mathlib's invertible-ideal interface for an effective Cartier divisor.  Its
support is recorded separately by the zero locus of the ideal. -/
structure NoetherianJacobsonEffectiveCartierDivisor
    (R : Type*) [CommRing R] where
  ideal : Ideal R
  invertible : Module.Invertible R ideal

/-- An effective Cartier divisor on `Y` supported at the enumerated point. -/
theorem noetherianJacobson_exists_effectiveCartierDivisor
    (s : NoetherianJacobsonSetup p) (n : ℕ) :
    ∃ D : NoetherianJacobsonEffectiveCartierDivisor
        (noetherianJacobsonFiniteUnionGlobalSections s n),
      ∃ q : PrimeSpectrum (noetherianJacobsonFiniteUnionGlobalSections s n),
        PrimeSpectrum.comap (noetherianJacobsonRestrictionMap s n) q =
            noetherianJacobsonPoint s n ∧
          PrimeSpectrum.zeroLocus (D.ideal : Set _) = {q} := by
  sorry

/-- Torsion of the Picard group of the affine one-dimensional union. -/
theorem noetherianJacobsonFiniteUnion_picard_is_torsion
    (s : NoetherianJacobsonSetup p) (n : ℕ) :
    IsMulTorsion
      (CommRing.Pic (noetherianJacobsonFiniteUnionGlobalSections s n)) := by
  sorry

/-- Torsion of the Picard group trivializes a positive power of an invertible
ideal, in the source's `𝒪_Y(ND) ≅ 𝒪_Y` form. -/
theorem noetherianJacobson_picard_torsion_trivializes_divisor_power
    {R : Type*} [CommRing R] (I : Ideal R)
    (hI : Module.Invertible R I)
    (hPic : IsMulTorsion (CommRing.Pic R)) :
    ∃ N : ℕ, 0 < N ∧ (CommRing.Pic.mk R I) ^ N = 1 := by
  sorry

/-- The source's separating-curve assertion, expressed by an irreducible
equation and its one-dimensional prime principal ideal. -/
def IsNoetherianJacobsonSeparatingCurveEquation
    (s : NoetherianJacobsonSetup p) (n : ℕ)
    (f : NoetherianJacobsonPolynomialRing p) : Prop :=
  Irreducible f ∧
    IsNoetherianJacobsonIntegralCurve p
      (Ideal.span ({f} : Set (NoetherianJacobsonPolynomialRing p))) ∧
    PrimeSpectrum.zeroLocus
        (Ideal.span ({f} : Set (NoetherianJacobsonPolynomialRing p))) ∩
        noetherianJacobsonFiniteUnionClosedSet s n =
      {noetherianJacobsonPoint s n}

/-- For each `n`, there is an irreducible one-dimensional closed curve meeting
`C ∪ C₀ ∪ ⋯ ∪ Cₙ` set-theoretically only at `pₙ`. -/
theorem noetherianJacobson_exists_separatingCurveEquation
    (s : NoetherianJacobsonSetup p) (n : ℕ) :
    ∃ f : NoetherianJacobsonPolynomialRing p,
      IsNoetherianJacobsonSeparatingCurveEquation s n f := by
  sorry

/-- A simultaneous choice of the equations `fₙ` for all separating curves. -/
structure NoetherianJacobsonSeparatingCurveFamily
    (s : NoetherianJacobsonSetup p) where
  equation : ℕ → NoetherianJacobsonPolynomialRing p
  separates : ∀ n, IsNoetherianJacobsonSeparatingCurveEquation s n (equation n)

/-- The simultaneous choice of all the `Zₙ` and their equations. -/
theorem noetherianJacobson_exists_separatingCurveFamily
    (s : NoetherianJacobsonSetup p) :
    Nonempty (NoetherianJacobsonSeparatingCurveFamily s) := by
  sorry

/-- A chosen family of separating curves, for use in the localization. -/
noncomputable def noetherianJacobsonChosenSeparatingCurveFamily
    (s : NoetherianJacobsonSetup p) :
    NoetherianJacobsonSeparatingCurveFamily s :=
  Classical.choice (noetherianJacobson_exists_separatingCurveFamily s)

/-- The ideal defining `Zₙ = V(fₙ)`. -/
def noetherianJacobsonSeparatingCurveIdeal
    (F : NoetherianJacobsonSeparatingCurveFamily s) (n : ℕ) :
    Ideal (NoetherianJacobsonPolynomialRing p) :=
  Ideal.span ({F.equation n} : Set (NoetherianJacobsonPolynomialRing p))

/-- The closed subset underlying `Zₙ`. -/
def noetherianJacobsonSeparatingCurveClosedSet
    (F : NoetherianJacobsonSeparatingCurveFamily s) (n : ℕ) :
  Set (PrimeSpectrum (NoetherianJacobsonPolynomialRing p)) :=
  PrimeSpectrum.zeroLocus
    (noetherianJacobsonSeparatingCurveIdeal F n :
      Set (NoetherianJacobsonPolynomialRing p))

/-- Every enumerated one-dimensional integral curve has an irreducible equation. -/
theorem noetherianJacobson_curve_equation_exists
    (s : NoetherianJacobsonSetup p) (i : ℕ) :
    ∃ g : NoetherianJacobsonPolynomialRing p,
      Irreducible g ∧
        PrimeSpectrum.zeroLocus
            (Ideal.span ({g} : Set (NoetherianJacobsonPolynomialRing p))) =
          PrimeSpectrum.zeroLocus
            (s.curves.curve i : Set (NoetherianJacobsonPolynomialRing p)) := by
  sorry

/-!
## The multiplicative set and its localization
-/

/-- The multiplicative subset generated by all equations `fₙ`. -/
noncomputable def noetherianJacobsonSeparatingSubmonoid
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    Submonoid (NoetherianJacobsonPolynomialRing p) :=
  Submonoid.closure (Set.range F.equation)

/-- The localized ring `B = S⁻¹A`. -/
noncomputable abbrev noetherianJacobsonLocalizedRing
    (F : NoetherianJacobsonSeparatingCurveFamily s) :=
  Localization (noetherianJacobsonSeparatingSubmonoid F)

/-- The extension to `B` of an ideal of `A`. -/
def noetherianJacobsonLocalizedIdeal
    (F : NoetherianJacobsonSeparatingCurveFamily s)
    (I : Ideal (NoetherianJacobsonPolynomialRing p)) :
    Ideal (noetherianJacobsonLocalizedRing F) :=
  Ideal.map (algebraMap (NoetherianJacobsonPolynomialRing p)
    (noetherianJacobsonLocalizedRing F)) I

/-- The ideal `xB`. -/
abbrev noetherianJacobsonLocalizedXAxisIdeal
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    Ideal (noetherianJacobsonLocalizedRing F) :=
  noetherianJacobsonLocalizedIdeal F (noetherianJacobsonXAxisIdeal p)

/-- The maximal ideals of `A` that survive in the localization. -/
def noetherianJacobsonSurvivingMaximalIdeals
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    Set (Ideal (NoetherianJacobsonPolynomialRing p)) :=
  {m | m.IsMaximal ∧
    Disjoint (noetherianJacobsonSeparatingSubmonoid F :
      Set (NoetherianJacobsonPolynomialRing p))
      (m : Set (NoetherianJacobsonPolynomialRing p))}

/-- The polynomial ring `A` is Noetherian. -/
instance noetherianJacobsonPolynomialRing_isNoetherian
    (p : ℕ) [Fact p.Prime] :
    IsNoetherianRing (NoetherianJacobsonPolynomialRing p) := by
  infer_instance

/-- The UFD fact used to choose an irreducible equation for each `Zₙ`. -/
instance noetherianJacobsonPolynomialRing_isUniqueFactorizationMonoid
    (p : ℕ) [Fact p.Prime] :
    UniqueFactorizationMonoid (NoetherianJacobsonPolynomialRing p) := by
  infer_instance

/-- Localization preserves Noetherianity in this construction. -/
instance noetherianJacobsonLocalizedRing_isNoetherian
    (s : NoetherianJacobsonSetup p)
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    IsNoetherianRing (noetherianJacobsonLocalizedRing F) := by
  infer_instance

/-- The localized ring is a domain. -/
theorem noetherianJacobsonLocalizedRing_isDomain
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    IsDomain (noetherianJacobsonLocalizedRing F) := by
  sorry

/-- The image of `Spec(B)` in `Spec(A)`. -/
def noetherianJacobsonLocalizationPrimeImage
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    Set (PrimeSpectrum (NoetherianJacobsonPolynomialRing p)) :=
  Set.range (PrimeSpectrum.comap
    (algebraMap (NoetherianJacobsonPolynomialRing p)
      (noetherianJacobsonLocalizedRing F)))

/-- The canonical localization map identifies local rings at corresponding
prime ideals. -/
theorem noetherianJacobson_localization_identifies_local_rings
    (F : NoetherianJacobsonSeparatingCurveFamily s)
    (q : PrimeSpectrum (noetherianJacobsonLocalizedRing F)) :
    Nonempty
      (Localization.AtPrime
          (q.asIdeal.comap (algebraMap (NoetherianJacobsonPolynomialRing p)
            (noetherianJacobsonLocalizedRing F))) ≃ₐ[
              NoetherianJacobsonPolynomialRing p]
        Localization.AtPrime q.asIdeal) := by
  sorry

/-- The induced map `Spec(B) → Spec(A)` is injective, using Mathlib's
localization correspondence. -/
theorem noetherianJacobson_localization_prime_comap_injective
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    Function.Injective (PrimeSpectrum.comap
      (algebraMap (NoetherianJacobsonPolynomialRing p)
        (noetherianJacobsonLocalizedRing F))) := by
  sorry

/-- A prime of `A` survives precisely when it is disjoint from `S`. -/
theorem noetherianJacobson_localization_prime_image_eq_disjoint
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    noetherianJacobsonLocalizationPrimeImage F =
      {q | Disjoint (noetherianJacobsonSeparatingSubmonoid F : Set _)
        (q.asIdeal : Set (NoetherianJacobsonPolynomialRing p))} := by
  sorry

/-- The points removed by the localization are the union of the zero loci of
the equations `fₙ`. -/
theorem noetherianJacobson_localization_removed_points
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    (noetherianJacobsonLocalizationPrimeImage F)ᶜ =
      ⋃ n : ℕ, PrimeSpectrum.zeroLocus
        ({F.equation n} : Set (NoetherianJacobsonPolynomialRing p)) := by
  sorry

/-!
## Which points survive
-/

/-- The union of the preceding separating curves. -/
def noetherianJacobsonPriorSeparatingCurveClosedSet
    (F : NoetherianJacobsonSeparatingCurveFamily s) (i : ℕ) :
    Set (PrimeSpectrum (NoetherianJacobsonPolynomialRing p)) :=
  ⋃ j : Fin i, noetherianJacobsonSeparatingCurveClosedSet F j.1

/-- The closed points of `Cᵢ` removed by the localization. -/
def noetherianJacobsonRemovedClosedPointsOnCurve
    (s : NoetherianJacobsonSetup p)
    (F : NoetherianJacobsonSeparatingCurveFamily s) (i : ℕ) :
    Set (PrimeSpectrum (NoetherianJacobsonPolynomialRing p)) :=
  {q | q.asIdeal.IsMaximal ∧
    q ∈ PrimeSpectrum.zeroLocus
      (s.curves.curve i : Set (NoetherianJacobsonPolynomialRing p)) ∧
    q ∉ noetherianJacobsonLocalizationPrimeImage F}

/-- For the first enumerated curve, only points of `C ∩ C₀` can be removed. -/
theorem noetherianJacobson_first_curve_removed_points
    (s : NoetherianJacobsonSetup p)
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    noetherianJacobsonRemovedClosedPointsOnCurve s F 0 ⊆
      PrimeSpectrum.zeroLocus
        (s.curves.curve 0 : Set (NoetherianJacobsonPolynomialRing p)) ∩
        noetherianJacobsonXAxisClosedSet p := by
  sorry

/-- If `Cᵢ` is not one of the `Zₙ`, the only removed closed points on it lie
in `((Z₀ ∪ ⋯ ∪ Zᵢ₋₁) ∪ C) ∩ Cᵢ`. -/
theorem noetherianJacobson_curve_removed_points_subset_prior_intersection
    (s : NoetherianJacobsonSetup p)
    (F : NoetherianJacobsonSeparatingCurveFamily s) (i : ℕ)
    (hne : ∀ n, s.curves.curve i ≠
      noetherianJacobsonSeparatingCurveIdeal F n) :
    noetherianJacobsonRemovedClosedPointsOnCurve s F i ⊆
      (noetherianJacobsonXAxisClosedSet p ∪
        noetherianJacobsonPriorSeparatingCurveClosedSet F i) ∩
        PrimeSpectrum.zeroLocus
          (s.curves.curve i : Set (NoetherianJacobsonPolynomialRing p)) := by
  sorry

/-- The removed closed points on a curve not equal to a separating curve are
finite, so all but finitely many of its closed points survive. -/
theorem noetherianJacobson_curve_removed_points_finite
    (s : NoetherianJacobsonSetup p)
    (F : NoetherianJacobsonSeparatingCurveFamily s) (i : ℕ)
    (hne : ∀ n, s.curves.curve i ≠
      noetherianJacobsonSeparatingCurveIdeal F n) :
    Set.Finite (noetherianJacobsonRemovedClosedPointsOnCurve s F i) := by
  sorry

/-- If `Cᵢ = Zₙ`, its defining equation becomes a unit in `B`. -/
theorem noetherianJacobson_curve_equation_isUnit_when_separating
    (s : NoetherianJacobsonSetup p)
    (F : NoetherianJacobsonSeparatingCurveFamily s) (i n : ℕ)
    (g : NoetherianJacobsonPolynomialRing p)
    (hg : Irreducible g)
    (hcurve : PrimeSpectrum.zeroLocus
        (Ideal.span ({g} : Set (NoetherianJacobsonPolynomialRing p))) =
      PrimeSpectrum.zeroLocus
        (s.curves.curve i : Set (NoetherianJacobsonPolynomialRing p)))
    (heq : s.curves.curve i =
      noetherianJacobsonSeparatingCurveIdeal F n) :
    IsUnit (algebraMap (NoetherianJacobsonPolynomialRing p)
      (noetherianJacobsonLocalizedRing F) g) := by
  sorry

/-- There are infinitely many surviving maximal ideals of `A`. -/
theorem noetherianJacobson_surviving_maximalIdeals_infinite
    (s : NoetherianJacobsonSetup p)
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    (noetherianJacobsonSurvivingMaximalIdeals F).Infinite := by
  sorry

/-- A surviving maximal ideal of `A` extends to a maximal ideal of `B`. -/
theorem noetherianJacobson_localized_surviving_ideal_isMaximal
    (F : NoetherianJacobsonSeparatingCurveFamily s)
    (m : Ideal (NoetherianJacobsonPolynomialRing p))
    (hm : m ∈ noetherianJacobsonSurvivingMaximalIdeals F) :
    (noetherianJacobsonLocalizedIdeal F m).IsMaximal := by
  sorry

/-- The localized axis ideal `xB` is maximal. -/
theorem noetherianJacobson_localizedXAxisIdeal_isMaximal
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    (noetherianJacobsonLocalizedXAxisIdeal F).IsMaximal := by
  sorry

/-- The quotient `B/xB` has exactly one prime ideal. -/
theorem noetherianJacobson_quotient_by_xAxis_has_unique_prime
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    Nonempty (PrimeSpectrum
      (noetherianJacobsonLocalizedRing F ⧸
        noetherianJacobsonLocalizedXAxisIdeal F)) ∧
      Subsingleton (PrimeSpectrum
        (noetherianJacobsonLocalizedRing F ⧸
          noetherianJacobsonLocalizedXAxisIdeal F)) := by
  sorry

/-! This is a proof-free localization at the complement of an ideal.  For a
maximal (hence prime) ideal, the displayed closure is the usual prime
complement, while this presentation lets the source's maximal-ideal
conjunctions remain ordinary propositions at theorem boundaries. -/
noncomputable abbrev noetherianJacobsonLocalRingAt
    {R : Type*} [CommSemiring R] (I : Ideal R) :=
  Localization (Submonoid.closure (I : Set R)ᶜ)

/-!
## Jacobsonness, dimensions, and the final lemma
-/

/-- The localized ring is Jacobson. -/
theorem noetherianJacobson_localizedRing_isJacobson
    (s : NoetherianJacobsonSetup p)
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    IsJacobsonRing (noetherianJacobsonLocalizedRing F) := by
  sorry

/-- The source's description of all maximal ideals of `B`. -/
theorem noetherianJacobson_localizedRing_isMaximal_iff
    (s : NoetherianJacobsonSetup p)
    (F : NoetherianJacobsonSeparatingCurveFamily s)
    (J : Ideal (noetherianJacobsonLocalizedRing F)) :
    J.IsMaximal ↔
      J = noetherianJacobsonLocalizedXAxisIdeal F ∨
        ∃ m ∈ noetherianJacobsonSurvivingMaximalIdeals F,
          J = noetherianJacobsonLocalizedIdeal F m := by
  sorry

/-- The local ring at `xB` has dimension one. -/
theorem noetherianJacobson_axis_local_dimension_one
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    ringKrullDim (noetherianJacobsonLocalRingAt
      (noetherianJacobsonLocalizedXAxisIdeal F)) =
        (1 : WithBot ℕ∞) := by
  sorry

/-- The local rings at surviving closed points have dimension two. -/
theorem noetherianJacobson_surviving_local_dimension_two
    (s : NoetherianJacobsonSetup p)
    (F : NoetherianJacobsonSeparatingCurveFamily s)
    (m : Ideal (NoetherianJacobsonPolynomialRing p))
    (hm : m ∈ noetherianJacobsonSurvivingMaximalIdeals F) :
    ringKrullDim (noetherianJacobsonLocalRingAt
      (noetherianJacobsonLocalizedIdeal F m)) =
        (2 : WithBot ℕ∞) := by
  sorry

/-- The localization is universally catenary, using the earlier chapter's
source-facing interface for universal catenarity. -/
theorem noetherianJacobson_localizedRing_isUniversallyCatenary
    (F : NoetherianJacobsonSeparatingCurveFamily s) :
    Formalization.«Books.Examples».Unit20.IsUniversallyCatenary
      (noetherianJacobsonLocalizedRing F) := by
  sorry

/-- Chapter 21's main existence lemma: a Jacobson, universally catenary,
Noetherian domain with maximal localizations of dimensions one and two. -/
theorem exists_noetherian_jacobson_universally_catenary_domain
    (p : ℕ) [Fact p.Prime] :
    ∃ (s : NoetherianJacobsonSetup p)
      (F : NoetherianJacobsonSeparatingCurveFamily s),
      IsJacobsonRing (noetherianJacobsonLocalizedRing F) ∧
        Formalization.«Books.Examples».Unit20.IsUniversallyCatenary
          (noetherianJacobsonLocalizedRing F) ∧
        IsNoetherianRing (noetherianJacobsonLocalizedRing F) ∧
        IsDomain (noetherianJacobsonLocalizedRing F) ∧
        ∃ m₁ m₂ : Ideal (noetherianJacobsonLocalizedRing F),
          m₁.IsMaximal ∧ m₂.IsMaximal ∧
            ringKrullDim (noetherianJacobsonLocalRingAt m₁) =
              (1 : WithBot ℕ∞) ∧
            ringKrullDim (noetherianJacobsonLocalRingAt m₂) =
              (2 : WithBot ℕ∞) := by
  sorry

end Formalization.«Books.Examples».Unit21
