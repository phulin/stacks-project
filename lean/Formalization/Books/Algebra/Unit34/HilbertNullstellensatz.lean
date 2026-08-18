import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Commutative Algebra, Chapter 34: Hilbert Nullstellensatz

The source's residue fields are Mathlib's canonical `Ideal.ResidueField`s.
Finite field extensions are expressed by `Module.Finite`, finite-type algebras
by `Algebra.FiniteType`, and the assertion about intersections of maximal
ideals by `IsJacobsonRing` and `Ideal.jacobson`.
-/

namespace Formalization.Books.Algebra.Unit34

universe u v

noncomputable section

/-! ## Hilbert Nullstellensatz -/

/- The source's `κ(m)` is `m.asIdeal.ResidueField` for the canonical maximal
   spectrum point `m`.  This general finite-type statement contains the
   polynomial-ring case as its specialization. -/
theorem hilbert_nullstellensatz_residueField_finite
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (m : MaximalSpectrum A) :
    Module.Finite k m.asIdeal.ResidueField := by
  sorry

/- The source's intersection assertion is exactly the canonical Jacobson-ring
   predicate. -/
theorem hilbert_nullstellensatz_isJacobsonRing
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    IsJacobsonRing A := by
  sorry

/- This is the source-facing form for an individual radical ideal.  The
   stronger bundled result above also records that all such ideals satisfy it. -/
theorem hilbert_nullstellensatz_radical_ideal_eq_jacobson
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (I : Ideal A) (hI : I.IsRadical) :
    I.jacobson = I := by
  exact IsJacobsonRing.out (hilbert_nullstellensatz_isJacobsonRing (k := k) (A := A)) hI

/- Explicit polynomial-ring specializations of the two source clauses. -/
theorem hilbert_nullstellensatz_polynomial_residueField_finite
    {k : Type*} [Field k] (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) k)) :
    Module.Finite k m.asIdeal.ResidueField := by
  exact hilbert_nullstellensatz_residueField_finite (k := k) (A := MvPolynomial (Fin n) k) m

theorem hilbert_nullstellensatz_polynomial_isJacobsonRing
    {k : Type*} [Field k] (n : ℕ) :
    IsJacobsonRing (MvPolynomial (Fin n) k) := by
  exact hilbert_nullstellensatz_isJacobsonRing (k := k) (A := MvPolynomial (Fin n) k)

/-! ## Finite type over a domain -/

/- The map from `R_f` to `K` used by the final lemma is the localization
   universal property applied to the injective map `R → K`. -/
noncomputable def localizationAwayToField
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (hRK : Function.Injective (algebraMap R K)) (f : R) (hf : f ≠ 0) :
    Localization.Away f →+* K :=
  Localization.awayLift (algebraMap R K) f
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff (algebraMap R K) hRK).2 hf))

/- The source's `R ⊂ K` is represented by an injective algebra map.  The
   final conjunction makes both the field structure on `R_f` and the finite
   module underlying the field extension explicit, together with its canonical
   localization map into `K`. -/
theorem field_finite_type_over_domain
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (hRK : Function.Injective (algebraMap R K)) [Algebra.FiniteType R K] :
    ∃ (f : R) (hf : f ≠ 0),
      IsField (Localization.Away f) ∧
        Function.Injective (localizationAwayToField hRK f hf) ∧
          (letI : Algebra (Localization.Away f) K :=
            (localizationAwayToField hRK f hf).toAlgebra
           Module.Finite (Localization.Away f) K) := by
  sorry

end

end Formalization.Books.Algebra.Unit34
