import Formalization.Books.Exercises.Unit34.Core

/-!
# Exercises, Chapter 34: Morphisms

The declarations below follow the source order.  The concrete constructions
are in `Core.lean`; proposition-valued exercise proofs are deferred.
-/

namespace Formalization.Books.Exercises.Unit34

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Opposite TopologicalSpace

universe u

noncomputable section

/-! ## Exercise `exercise-no-section` -/

/-- The displayed morphism has no section over all of `Spec(ℂ[t])`. -/
theorem noSection_has_no_section :
    ¬ HasSection noSectionMorphism := by
  sorry

/-- The same morphism acquires a section after restricting to a nonempty open
of the base. -/
theorem noSection_has_nonempty_open_section :
    HasOpenSection noSectionMorphism := by
  sorry

/-! ## Exercise `exercise-no-rational-section` -/

/-- The morphism cut out by `x² + t` has no section over any nonempty open of
the base. -/
theorem noRationalSection_has_no_open_section :
    ¬ HasOpenSection noRationalSectionMorphism := by
  sorry

/-! ## Exercise `exercise-has-rational-section` -/

/-- The conic with nonzero polynomial coefficients has a rational section. -/
theorem rationalSection_has_open_section
    (A B C : noSectionBaseRing)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    HasOpenSection (rationalSectionMorphism A B C) := by
  sorry

/-! ## Remark `remark-tsen` -/

/-- The preceding conic statement is the special case of Tsen's theorem
recorded by the source. -/
theorem tsen_conic_special_case :
    ∀ (A B C : noSectionBaseRing), A ≠ 0 → B ≠ 0 → C ≠ 0 →
      HasOpenSection (rationalSectionMorphism A B C) := by
  sorry

/-! ## Exercise `exercise-no-section-curve` -/

/-- The cubic curve example has no rational section. -/
theorem noSectionCurve_has_no_open_section :
    ¬ HasOpenSection noSectionCurveMorphism := by
  sorry

/-! ## Exercise `exercise-no-section-surface` -/

/-- The eight-variable cubic surface example has no rational section. -/
theorem noSectionSurface_has_no_open_section :
    ¬ HasOpenSection noSectionSurfaceMorphism := by
  sorry

/-! ## Exercise `exercise-for-number-theorists` -/

/-- A closed subscheme of the displayed localization has a finite
surjective map to `Spec(ℤ)`. -/
theorem exists_numberTheory_finite_surjective_closed_subscheme :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ numberTheoryScheme),
      IsClosedImmersion i ∧
        IsFiniteSurjective (i ≫ numberTheoryMorphism) := by
  sorry

/-! ## Exercise `exercise-quasi-section` -/

/-- The finite-field variant has a finite surjective closed subscheme over
the polynomial base. -/
theorem exists_finiteField_finite_surjective_closed_subscheme
    (p : ℕ) [Fact p.Prime] :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ finiteFieldScheme p),
      IsClosedImmersion i ∧
        IsFiniteSurjective (i ≫ finiteFieldMorphism p) := by
  sorry

/-! ## Remark `remark-interpretation-skolem-noether` -/

/-- The two preceding exercises have the source's common geometric
interpretation: a finite surjective base change admits a section after base
change. -/
theorem finite_surjective_base_change_interpretation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [Surjective f] [GeometricallyIrreducible f] :
    HasFiniteSurjectiveBaseChangeSection f := by
  sorry

/-! ## Exercise `exercise-no-quasi-section` -/

/-- Some polynomial localization over `ℂ[t]` admits no finite surjective
closed subscheme over the base, while its defining polynomial has no factor
`t - α`. -/
theorem exists_noQuasiSection_polynomial :
    ∃ f : noQuasiSectionPolynomialRing,
      (∀ α : ℂ, ¬ noQuasiSectionLinearFactor α ∣ f) ∧
        ¬ ∃ (Z : Scheme.{0}) (i : Z ⟶ noQuasiSectionSource f),
          IsClosedImmersion i ∧
            IsFiniteSurjective (i ≫ noQuasiSectionMorphism f) := by
  sorry

/-! The source proposes a particular candidate with the qualification “I
think”.  It is retained as a separate theorem interface rather than silently
upgrading that suggestion to an established fact. -/

/-- The candidate suggested parenthetically by the source has the claimed
non-quasi-section property. -/
theorem noQuasiSection_candidate_works :
    (∀ α : ℂ,
      ¬ noQuasiSectionLinearFactor α ∣ noQuasiSectionCandidate) ∧
      ¬ ∃ (Z : Scheme.{0})
          (i : Z ⟶ noQuasiSectionSource noQuasiSectionCandidate),
        IsClosedImmersion i ∧
          IsFiniteSurjective
            (i ≫ noQuasiSectionMorphism noQuasiSectionCandidate) := by
  sorry

/-! ## Exercise `exercise-finite` -/

/-- A finite-type algebra which factors through a closed subscheme of a
projective space is finite, under the Noetherian hypothesis used in the
source's hint. -/
theorem finite_of_projective_factorization
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (f : A →+* B) (hfiniteType : RingHom.FiniteType f)
    (hfactor :
      ∃ n : ℕ, ∃ i : affineScheme B ⟶ projectiveSpace A n,
        IsClosedImmersion i ∧
          i ≫ projectiveSpaceStructureMap A n = affineSchemeMap f) :
    RingHom.Finite f := by
  sorry

/-! ## Exercise `exercise-projective-finite` -/

/-- A morphism between projective varieties over an algebraically closed field
with finite closed-point fibres is finite. -/
theorem finite_morphism_of_projective_varieties
    (k : Type u) [Field k] [IsAlgClosed k]
    (X Y : Scheme.{u})
    (pX : X ⟶ affineScheme k) (pY : Y ⟶ affineScheme k)
    (f : X ⟶ Y)
    (hX : IsProjectiveVarietyOver k X pX)
    (hY : IsProjectiveVarietyOver k Y pY)
    (hbase : f ≫ pY = pX)
    (hfib : ∀ y : Y, IsClosed ({y} : Set Y) →
      Set.Finite {x : X | f.base x = y}) :
    IsFinite f := by
  sorry

end

end Formalization.Books.Exercises.Unit34
