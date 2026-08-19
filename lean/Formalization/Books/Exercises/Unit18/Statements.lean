import Formalization.Books.Exercises.Unit18.Core

import Formalization.Books.Topology.Unit20.DimensionFunctions
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# Exercises, Chapter 18: Catenary rings

The declarations below follow the source definition and its four exercises
in order.  Proofs are deferred to the proving stage; the definitions and
interfaces use the canonical quotient, localization, prime-spectrum,
topological catenarity, and dimension-function APIs.
-/

noncomputable section

universe u

namespace Formalization.Books.Exercises.Unit18

/-! ## Definition `catenary` -/

/-
The source's four displayed descriptions of `ht(p / q)` are recorded here.
The first term is the relative height, the second is the dimension of
`Aₚ / qAₚ`, and the last term is the dimension of `(A / q)ₚ₋q`; the middle
notation `(A / q)ₚ` is represented by the same canonical quotient-localized
ring.
-/
theorem relativeHeight_eq_displayed_dimensions
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p q : PrimeSpectrum A) (hpq : q ≤ p) :
    (relativeHeight p.asIdeal q.asIdeal
        ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hpq) : WithBot ℕ∞) =
      ringKrullDim
        (Localization.AtPrime p.asIdeal ⧸
          q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) ∧
      ringKrullDim
        (Localization.AtPrime p.asIdeal ⧸
          q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) =
        ringKrullDim (Localization.AtPrime (quotientPrime p q hpq).asIdeal) := by
  let P : Ideal (A ⧸ q.asIdeal) := p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)
  have hP : P.IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime
      ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hpq)
  letI : P.IsPrime := hP
  have hPover : P.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change p.asIdeal = (p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).comap
      (Ideal.Quotient.mk q.asIdeal)
    rw [Ideal.comap_map_quotientMk]
    exact (sup_eq_right.mpr ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hpq)).symm
  have hsub :
      Algebra.algebraMapSubmonoid (A ⧸ q.asIdeal) p.asIdeal.primeCompl = P.primeCompl := by
    exact Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective
      (p := p.asIdeal) (P := P) Ideal.Quotient.mk_surjective
  have hloc : IsLocalization P.primeCompl
      (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) := by
    rw [← hsub]
    infer_instance
  letI : IsLocalization.AtPrime
      (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) P := hloc
  have hdimC :
      ringKrullDim (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) =
        (P.height : WithBot ℕ∞) := by
    exact IsLocalization.AtPrime.ringKrullDim_eq_height P
      (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal)))
  constructor
  · change (P.height : WithBot ℕ∞) = _
    exact hdimC.symm
  · have hdim := ringKrullDim_eq_of_ringEquiv
      (IsLocalization.algEquiv P.primeCompl
        (Localization.AtPrime p.asIdeal ⧸
          q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (Localization.AtPrime P)).toRingEquiv
    change ringKrullDim (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) =
      ringKrullDim (Localization.AtPrime P)
    exact hdim

/-! ## Exercise `catenary-the-same` -/

/-- The height-additivity definition agrees with Algebra's chain definition
for Noetherian rings. -/
theorem catenary_iff_algebra_catenary
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    IsCatenaryRing A ↔ IsAlgebraCatenaryRing A := by
  sorry

/-! ## Exercise `Noetherian-local-domain-dim-2-catenary` -/

/-- A Noetherian local domain of Krull dimension two is catenary. -/
theorem noetherian_local_domain_dimension_two_isCatenary
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (hA : ringKrullDim A = (2 : WithBot ℕ∞)) :
    IsCatenaryRing A := by
  sorry

/-! ## Exercise `finite-type-over-field-catenary` -/

/-- Every finite-type algebra over a field is catenary. -/
theorem finite_type_algebra_over_field_isCatenary
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    IsCatenaryRing A := by
  sorry

/-! ## Exercise `example-no-dim-function` -/

/-
The source writes the second dimension-function condition using an
intermediate point whenever the integer-valued function drops by at least
two.  The established `Topology.Unit20.IsDimensionFunction` uses the
equivalent immediate-specialization/equality-by-one formulation, so the
existence statement below reuses that canonical predicate.
-/
/-- There is a finite sober catenary space with no dimension function. -/
theorem exists_finite_sober_catenary_space_without_dimension_function :
    ∃ (X : Type u) (inst : TopologicalSpace X),
      @IsFiniteSoberCatenarySpace X inst ∧
        ¬ ∃ δ : X → ℤ,
          @Formalization.Books.Topology.Unit20.IsDimensionFunction X inst δ := by
  sorry

end Formalization.Books.Exercises.Unit18
