import Formalization.Books.Exercises.Unit33.Core

/-!
# Exercises, Chapter 33: Schemes

The declarations below record the source's definition, remarks, and fourteen
numbered exercises in source order.  Proofs are deferred to the proving
stage; all example requests retain their mathematical data and exclusions.
-/

namespace Formalization.Books.Exercises.Unit33

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Opposite TopologicalSpace

universe u

noncomputable section

/-! ## Exercises `exercise-one-point` through `exercise-three-points` -/

/-- A one-point locally ringed space need not satisfy the local affine-cover
condition for schemes. -/
theorem exists_one_point_locallyRingedSpace_not_scheme :
    ∃ X : LocallyRingedSpace.{u},
      (∃ x : X, ∀ y : X, y = x) ∧ ¬ IsSchemeLocallyRingedSpace X := by
  sorry

/-- A two-point scheme is affine. -/
theorem two_point_scheme_is_affine (X : Scheme.{u})
    (hX : IsTwoPoint X) : IsAffine X := by
  sorry

/-- A scheme with finite discrete underlying space is affine. -/
theorem finite_discrete_scheme_is_affine (X : Scheme.{u})
    (hX : IsFiniteDiscrete X) : IsAffine X := by
  sorry

/-- There is a non-affine scheme with exactly three points. -/
theorem exists_three_point_non_affine_scheme :
    ∃ X : Scheme.{u}, IsThreePoint X ∧ ¬ IsAffine X := by
  sorry

/-! ## Exercise `exercise-quasi-compact-closed-point` -/

/-- A nonempty quasi-compact scheme has a closed point. -/
theorem quasiCompact_nonempty_scheme_has_closed_point (X : Scheme.{u})
    [AlgebraicGeometry.QuasiCompact (𝟙 X)] (hX : Nonempty X) :
    HasClosedPoint X := by
  sorry

/-! ## Remark `remark-open-immersion` -/

/-- Restriction to an open subset is a scheme and its canonical map is an
open immersion. -/
theorem openSubscheme_is_scheme_and_open_immersion
    (X : Scheme.{u}) (U : Opens X) :
    IsOpenImmersion (openSubschemeInclusion X U) := by
  infer_instance

/-- The source's general notion of open immersion is the canonical one up to
isomorphism, as represented by Mathlib's `IsOpenImmersion` predicate. -/
theorem open_immersion_predicate_is_canonical
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsOpenImmersion f ↔
      ∃ U : Opens Y, ∃ e : X ≅ openSubscheme Y U,
        e.hom ≫ openSubschemeInclusion Y U = f := by
  sorry

/-! ## Exercises `exercise-open-affine-not-affine` and
`exercise-morphism-does-not-extend` -/

/-- An affine scheme can have a non-affine open subscheme. -/
theorem exists_affine_scheme_nonaffine_open_subscheme :
    ∃ (X : Scheme.{u}) (U : Opens X),
      IsAffine X ∧ ¬ IsAffine (openSubscheme X U) := by
  sorry

/-- A morphism from an open subscheme of an affine scheme to an affine scheme
need not extend to the ambient affine scheme. -/
theorem exists_affine_morphism_not_extend :
    ∃ (X Y : Scheme.{u}) (U : Opens X),
      IsAffine X ∧ IsAffine Y ∧
        ∃ f : openSubscheme X U ⟶ Y,
          ∀ g : X ⟶ Y, openSubschemeInclusion X U ≫ g ≠ f := by
  sorry

/-! ## Exercise `exercise-closed-subscheme-does-not-extend` -/

/-- A closed subscheme of an open subscheme need not extend to the ambient
scheme. -/
theorem exists_closed_subscheme_not_extend :
    Nonempty ClosedSubschemeNonExtensionExample := by
  sorry

/-! ## Exercise `exercise-not-morphism-schemes` -/

/-- A morphism of ringed spaces from the spectrum of a field need not be a
morphism of locally ringed spaces. -/
theorem exists_ringedSpace_morphism_not_scheme_morphism :
    ∃ (X : Scheme.{u}) (K : Type u) (_ : Field K)
      (f : (Scheme.Spec.obj (op (CommRingCat.of K))).toRingedSpace ⟶ X.toRingedSpace),
      ¬ IsLocallyRingedSpaceMorphism f := by
  sorry

/-! ## Definition `definition-integral` and its exercise -/

/-- The textbook definition of an integral scheme is the source-facing
`IsIntegralScheme` predicate from the core file. -/
theorem integral_scheme_definition_unfolds (X : Scheme.{u}) :
    IsIntegralScheme X ↔
      (Nonempty X ∧
        ∀ (U : Opens X), (U : Set X).Nonempty →
          affineLocallyRingedSpaceOpen X.toLocallyRingedSpace U →
            IsDomain (schemeGlobalSections (openSubscheme X U) : Type u)) := by
  rfl

/-- Integral schemes admit morphisms with surjective maps on every stalk that
are nevertheless not closed immersions. -/
theorem exists_integral_stalk_surjective_not_closed_immersion :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsIntegralScheme X ∧ IsIntegralScheme Y ∧
        (∀ x : X, Function.Surjective (Scheme.Hom.stalkMap f x).hom) ∧
          ¬ IsClosedImmersion f := by
  sorry

/-! ## Exercise `exercise-fibre-product-affines-not-affine` and its remark -/

/-- Affine schemes can have a non-affine fibre product over a non-separated
base. -/
theorem exists_affine_fibre_product_not_affine :
    ∃ (S X Y : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S),
      IsAffine X ∧ IsAffine Y ∧ ¬ IsAffine (pullback f g) := by
  sorry

/-- Over a separated base, the fibre product of two affine schemes is affine.
This is the assertion behind the intervening remark. -/
theorem affine_fibre_product_of_separated_base
    (S X Y : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffine X] [IsAffine Y] [AlgebraicGeometry.Scheme.IsSeparated S] :
    IsAffine (pullback f g) := by
  sorry

/-! ## Exercise `exercise-not-geometrically-integral` -/

/-- There is an integral one-dimensional finite-type scheme over `ℚ` whose
complex base change is not integral. -/
theorem exists_integral_curve_over_Q_not_geometrically_integral :
    ∃ (V : Scheme.{0}) (v : V ⟶ rationalSpectrum),
      IsIntegralScheme V ∧ SchemeDimension V = 1 ∧
        IsFiniteTypeMorphism v ∧
        ¬ IsIntegralScheme (pullback complexToRational v) := by
  sorry

/-! ## Exercise `exercise-not-geometrically-reduced` -/

/-- An integral one-dimensional finite-type scheme over a field can acquire
nilpotents after a finite field extension. -/
theorem exists_integral_curve_not_geometrically_reduced :
    ∃ (k k' : Type u) (_ : Field k) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k')
      (V : Scheme.{u})
      (v : V ⟶ Scheme.Spec.obj (op (CommRingCat.of k))),
      IsIntegralScheme V ∧ SchemeDimension V = 1 ∧
        IsFiniteTypeMorphism v ∧
          ¬ AlgebraicGeometry.IsReduced (fieldBaseChange k k' V v) := by
  sorry

/-! ## Remark `remark-affine-dimension` -/

/-- For an affine scheme, the scheme dimension agrees with the Krull
dimension of its coordinate ring. -/
theorem affine_scheme_dimension_eq_ring_krull_dimension
    (X : Scheme.{u}) [IsAffine X] :
    SchemeDimension X = RingKrullDimension (schemeGlobalSections X : Type u) := by
  sorry

end

end Formalization.Books.Exercises.Unit33
