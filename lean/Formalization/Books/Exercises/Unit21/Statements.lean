import Formalization.Books.Exercises.Unit21.Core

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Exercises, Chapter 21: Dimension of fibres

This file records the theorem interfaces for the two numbered exercises.
Proofs are deferred to the proving stage.
-/

namespace Formalization.Books.Exercises.Unit21

universe u v

noncomputable section

/-! ## Exercise `nr-components-fibre` -/

/- The source's phrase “finite type extension of domains” is represented by
   an injective finite-type ring homomorphism with a domain as target.  The
   polynomial source rings are domains under the field hypotheses. -/

/-- For every `n ≥ 0`, there is a finite-type domain extension of `k[x]`
whose zero fibre has exactly `n` irreducible components. -/
theorem exists_finiteType_domain_extension_with_fibre_component_cardinal
    (k : Type u) [Field k] [IsAlgClosed k] :
    ∀ n : ℕ,
      ∃ (A : Type v) (_ : CommRing A)
        (f : oneVariablePolynomialRing k →+* A),
        IsDomain A ∧ Function.Injective f ∧ RingHom.FiniteType f ∧
          fibreComponentCardinal f (oneVariableOriginIdeal k) = (n : ℕ∞) := by
  sorry

/-- There is a finite-type domain extension of `k[x]` whose fibre over every
closed point is nonempty and reducible. -/
theorem exists_finiteType_domain_extension_with_all_fibres_reducible
    (k : Type u) [Field k] [IsAlgClosed k] :
    ∃ (A : Type v) (_ : CommRing A)
      (f : oneVariablePolynomialRing k →+* A),
      IsDomain A ∧ Function.Injective f ∧ RingHom.FiniteType f ∧
        ∀ α : k,
          Nonempty (PrimeSpectrum (fibreRing f (oneVariablePointIdeal k α))) ∧
            fibreIsReducible f (oneVariablePointIdeal k α) := by
  sorry

/-- There is a finite-type domain extension of `k[x,y]` whose non-origin
fibres are irreducible and whose origin fibre is nonempty and reducible. -/
theorem exists_finiteType_domain_extension_with_irreducible_nonzero_fibres
    (k : Type u) [Field k] [IsAlgClosed k] :
    ∃ (A : Type v) (_ : CommRing A)
      (f : twoVariablePolynomialRing k →+* A),
      IsDomain A ∧ Function.Injective f ∧ RingHom.FiniteType f ∧
        (∀ α β : k, ((α, β) : k × k) ≠ (0, 0) →
          fibreIsIrreducible f (twoVariablePointIdeal k α β)) ∧
        Nonempty (PrimeSpectrum (fibreRing f (twoVariablePointIdeal k 0 0))) ∧
          fibreIsReducible f (twoVariablePointIdeal k 0 0) := by
  sorry

/-! ## Exercise `codim-1` -/

/-- The codimension-one exercise's dimension bounds for a nonzero origin
fibre.  Dimensions use Mathlib's canonical `ringKrullDim`, whose values are
in `WithBot ℕ∞`; the source's natural number `d` is inserted canonically. -/
theorem fibre_dimension_bounds_at_coordinate_origin
    (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (hn : 1 ≤ n)
    {A : Type v} [CommRing A] [IsDomain A]
    (f : nVariablePolynomialRing k n →+* A)
    (hinj : Function.Injective f) (hfinite : RingHom.FiniteType f)
    (d : ℕ)
    (hdim : ringKrullDim A = (((d : ℕ∞) : WithBot ℕ∞)))
    (hfibre : Nontrivial (fibreRing f (coordinateOriginIdeal k n))) :
    (((d - n : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
        ringKrullDim (fibreRing f (coordinateOriginIdeal k n)) ∧
      ringKrullDim (fibreRing f (coordinateOriginIdeal k n)) ≤
        (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  sorry

/-- Every natural value in the interval supplied by the preceding bounds is
realized by the origin fibre of a finite-type domain extension. -/
theorem exists_finiteType_domain_extension_for_every_admissible_fibre_dimension
    (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ d e : ℕ, n ≤ d → d - n ≤ e → e ≤ d - 1 →
      ∃ (A : Type v) (_ : CommRing A)
        (f : nVariablePolynomialRing k n →+* A),
        IsDomain A ∧ Function.Injective f ∧ RingHom.FiniteType f ∧
          ringKrullDim A = (((d : ℕ∞) : WithBot ℕ∞)) ∧
          Nontrivial (fibreRing f (coordinateOriginIdeal k n)) ∧
          ringKrullDim (fibreRing f (coordinateOriginIdeal k n)) =
            (((e : ℕ∞) : WithBot ℕ∞)) := by
  sorry

/-- Some origin fibres have irreducible components of different Krull
dimensions. -/
theorem exists_finiteType_domain_extension_with_mixed_fibre_component_dimensions
    (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (A : Type v) (_ : CommRing A)
      (f : nVariablePolynomialRing k n →+* A),
      IsDomain A ∧ Function.Injective f ∧ RingHom.FiniteType f ∧
        ∃ C D : Set
            (PrimeSpectrum (fibreRing f (coordinateOriginIdeal k n))),
          C ∈ irreducibleComponents
              (PrimeSpectrum (fibreRing f (coordinateOriginIdeal k n))) ∧
          D ∈ irreducibleComponents
              (PrimeSpectrum (fibreRing f (coordinateOriginIdeal k n))) ∧
          fibreComponentDimension f (coordinateOriginIdeal k n) C ≠
            fibreComponentDimension f (coordinateOriginIdeal k n) D := by
  sorry

end

end Formalization.Books.Exercises.Unit21
