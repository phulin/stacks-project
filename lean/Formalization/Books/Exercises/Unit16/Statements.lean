import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Spectrum.Prime.Topology

import Formalization.Books.Exercises.Unit16.Core

/-!
# Exercises, Chapter 16: Hilbert Nullstellensatz

The declarations follow the numbered exercises and remarks in the source.
The proofs are intentionally left for the prove stage; the definitions use
Mathlib's canonical polynomial, power-series, spectrum, and spectrum-topology
objects directly.
-/

noncomputable section

universe u

open Set

namespace Formalization.Books.Exercises.Unit16

open scoped BigOperators

/-! ## Exercise `uncountable` -/

/-- The rational function field `ℂ(X)` has uncountable vector-space dimension
over `ℂ`. -/
theorem rational_function_field_uncountable_dimension :
    Cardinal.aleph0 < Module.rank ℂ (RatFunc ℂ) := by
  have hcard : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  exact hcard.trans_le
    ((RatFunc.transcendental_X (K := ℂ)).linearIndependent_sub_inv.cardinal_le_rank)

/-- Mathlib's spectrum agrees with the source's convention for a linear
operator: `λ` is spectral precisely when `T - λ • id` is not a unit. -/
theorem linear_operator_spectrum_mem_iff
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (z : ℂ) :
    z ∈ spectrum ℂ T ↔
      ¬ IsUnit (T - algebraMap ℂ (Module.End ℂ V) z) := by
  rw [spectrum.mem_iff, IsUnit.sub_iff]

/-- Every endomorphism of a nonzero finite- or countable-dimensional complex
vector space has nonempty spectrum. -/
theorem linear_operator_spectrum_nonempty
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (T : V →ₗ[ℂ] V)
    (hV : Module.rank ℂ V ≤ Cardinal.aleph0) :
    (spectrum ℂ T).Nonempty := by
  classical
  by_contra hs
  have hspec : ∀ z : ℂ, z ∉ spectrum ℂ T := by
    intro z hz
    exact hs ⟨z, hz⟩
  have hunit (z : ℂ) : IsUnit (T - algebraMap ℂ (Module.End ℂ V) z) :=
    IsUnit.sub_iff.mp (spectrum.notMem_iff.mp (hspec z))
  have hp (z : ℂ) : Polynomial.aeval T (Polynomial.X - Polynomial.C z) =
      T - algebraMap ℂ (Module.End ℂ V) z := by
    simp
  have hinv (z : ℂ) : (T - algebraMap ℂ (Module.End ℂ V) z) *
      (↑((hunit z).unit⁻¹) : Module.End ℂ V) = 1 := by
    calc
      (T - algebraMap ℂ (Module.End ℂ V) z) *
            (↑((hunit z).unit⁻¹) : Module.End ℂ V) =
          (↑(hunit z).unit : Module.End ℂ V) *
            (↑((hunit z).unit⁻¹) : Module.End ℂ V) := by
        congr 1
      _ = 1 := by simp
  have hv : ∃ v : V, v ≠ 0 := exists_ne 0
  let v : V := Classical.choose hv
  have hv' : v ≠ 0 := Classical.choose_spec hv
  let p : ℂ → Polynomial ℂ := fun z => Polynomial.X - Polynomial.C z
  have hpa (z : ℂ) : Polynomial.aeval T (p z) =
      T - algebraMap ℂ (Module.End ℂ V) z := hp z
  let f : ℂ → V := fun z => (↑((hunit z).unit⁻¹) : Module.End ℂ V) v
  have hli : LinearIndependent ℂ f := by
    rw [linearIndependent_iff']
    intro s m hm i hi
    let q : Polynomial ℂ :=
      ∑ j ∈ s, Polynomial.C (m j) * ∏ k ∈ s.erase j, p k
    have hprod (j : ℂ) (hj : j ∈ s) :
        (∏ k ∈ s, p k) = (∏ k ∈ s.erase j, p k) * p j := by
      symm
      exact Finset.prod_erase_mul s p hj
    have hfactor (j : ℂ) (hj : j ∈ s) :
        Polynomial.aeval T (∏ k ∈ s, p k) *
            (↑((hunit j).unit⁻¹) : Module.End ℂ V) =
          Polynomial.aeval T (∏ k ∈ s.erase j, p k) := by
      rw [hprod j hj, map_mul, mul_assoc, hpa j, hinv j, mul_one]
    have hmul : ∑ j ∈ s, m j •
            (Polynomial.aeval T (∏ k ∈ s.erase j, p k)) v = 0 := by
      calc
        ∑ j ∈ s, m j • (Polynomial.aeval T (∏ k ∈ s.erase j, p k)) v =
            ∑ j ∈ s, m j •
              (Polynomial.aeval T (∏ k ∈ s, p k) *
                (↑((hunit j).unit⁻¹) : Module.End ℂ V)) v := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hfactor j hj]
        _ = (Polynomial.aeval T (∏ k ∈ s, p k))
              (∑ j ∈ s, m j • f j) := by
          simp only [f, map_sum, map_smul, Module.End.mul_apply]
        _ = 0 := by rw [hm]; simp
    have hq : (Polynomial.aeval T q) v = 0 := by
      simpa [q, Algebra.smul_def] using hmul
    have hqunit (hq0 : q ≠ 0) : IsUnit (Polynomial.aeval T q) := by
      have hrootunit : IsUnit
          (Polynomial.aeval T (Multiset.map (fun x : ℂ =>
            Polynomial.X - Polynomial.C x) q.roots).prod) := by
        by_contra hn
        obtain ⟨r, hr, _⟩ :=
          spectrum.exists_mem_of_not_isUnit_aeval_prod hn
        exact hspec r hr
      rw [(IsAlgClosed.splits q).eq_prod_roots, map_mul]
      exact IsUnit.mul
        ((Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
          (Polynomial.leadingCoeff_ne_zero.mpr hq0))).map (Polynomial.aeval T))
        hrootunit
    have hqzero : q = 0 := by
      by_contra hq0
      have hqu := hqunit hq0
      apply hv'
      calc
        v = (1 : Module.End ℂ V) v := by simp
        _ = ((↑(hqu.unit⁻¹) : Module.End ℂ V) *
            (↑hqu.unit : Module.End ℂ V)) v := by simp
        _ = ((↑(hqu.unit⁻¹) : Module.End ℂ V) *
            Polynomial.aeval T q) v := by congr 1
        _ = 0 := by rw [Module.End.mul_apply, hq]; simp
    have h_eval : Polynomial.eval i q = 0 := by
      rw [hqzero, Polynomial.eval_zero]
    rw [Polynomial.eval_finsetSum] at h_eval
    simp only [p, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at h_eval
    have hrest : ∑ j ∈ s.erase i, m j *
        ∏ k ∈ s.erase j, (i - k) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hij : i ∈ s.erase j := by
        rw [Finset.mem_erase]
        exact ⟨(Finset.ne_of_mem_erase hj).symm, hi⟩
      rw [Finset.prod_eq_zero hij]
      · exact mul_zero _
      · exact sub_self i
    have hbase :
        m i * ∏ k ∈ s.erase i, (i - k) =
          ∑ j ∈ s, m j * ∏ k ∈ s.erase j, (i - k) := by
      rw [← Finset.sum_erase_add _ _ hi, hrest, zero_add]
    have hprod_eq : m i * ∏ k ∈ s.erase i, (i - k) = 0 := by
      rw [hbase, h_eval]
    have hprod_ne : ∏ k ∈ s.erase i, (i - k) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hk).symm
    exact (mul_eq_zero.mp hprod_eq).resolve_right hprod_ne
  have hcard : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  have hcard' : Cardinal.lift.{u} Cardinal.aleph0 <
      Cardinal.lift.{u} (Cardinal.mk ℂ) := Cardinal.lift_lt.mpr hcard
  have hrank : Cardinal.lift.{u} (Cardinal.mk ℂ) ≤
      Cardinal.lift.{0} (Module.rank ℂ V) := hli.cardinal_lift_le_rank
  exact (not_lt_of_ge hV) (by
    simpa only [Cardinal.lift_aleph0, Cardinal.lift_id'] using hcard'.trans_le hrank)

/-- A finite-type complex algebra which is a field has bijective structure
map from `ℂ`. -/
theorem complex_finite_type_field_algebraMap_bijective
    {R : Type u} [Field R] [Algebra ℂ R]
    [Algebra.FiniteType ℂ R] :
    Function.Bijective (algebraMap ℂ R) := by
  let _ : Module.Finite ℂ R := finite_of_finite_type_of_isJacobsonRing ℂ R
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Every maximal ideal of `ℂ[x₁, ..., xₙ]` is a coordinate maximal ideal. -/
theorem complex_polynomial_maximal_ideal_eq_coordinate
    (n : ℕ) (m : Ideal (polynomialRing ℂ n)) (hm : m.IsMaximal) :
    ∃ α : Fin n → ℂ,
      m = polynomialCoordinateIdeal ℂ n α := by
  obtain ⟨α, hα⟩ :=
    MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal (K := ℂ) hm
  have hcoord :
      MvPolynomial.vanishingIdeal ℂ ({α} : Set (Fin n → ℂ)) =
        polynomialCoordinateIdeal ℂ n α := by
    have hgenzero :
        polynomialCoordinateIdeal ℂ n α ≤
          MvPolynomial.vanishingIdeal ℂ ({α} : Set (Fin n → ℂ)) := by
      rw [polynomialCoordinateIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change MvPolynomial.X i - MvPolynomial.C (α i) ∈
        MvPolynomial.vanishingIdeal ℂ ({α} : Set (Fin n → ℂ))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    apply Ideal.ext
    intro p
    constructor
    · intro hp
      have hrep : ∀ q : polynomialRing ℂ n,
          q - MvPolynomial.C (MvPolynomial.aeval α q) ∈
            polynomialCoordinateIdeal ℂ n α := by
        intro q
        induction q using MvPolynomial.induction_on with
        | C a => simp
        | add p q hp hq =>
            rw [map_add, MvPolynomial.C_add]
            convert Ideal.add_mem (polynomialCoordinateIdeal ℂ n α) hp hq using 1;
              abel
        | mul_X p i hp =>
            have hgen :
                MvPolynomial.X i - MvPolynomial.C (α i) ∈
                  polynomialCoordinateIdeal ℂ n α := by
              exact Ideal.subset_span ⟨i, rfl⟩
            have h₁ := Ideal.mul_mem_left (polynomialCoordinateIdeal ℂ n α)
              (MvPolynomial.X i) hp
            have h₂ := Ideal.mul_mem_left (polynomialCoordinateIdeal ℂ n α)
              (MvPolynomial.C (MvPolynomial.aeval α p)) hgen
            convert Ideal.add_mem _ h₁ h₂ using 1;
              simp only [map_mul, MvPolynomial.aeval_X];
              ring
      have hzero : MvPolynomial.aeval α p = 0 :=
        (MvPolynomial.mem_vanishingIdeal_singleton_iff α p).mp hp
      simpa [hzero] using hrep p
    · intro hp
      exact hgenzero hp
  exact ⟨α, hα.trans hcoord⟩

/-! ## Remark `HNSS` -/

/-- A maximal ideal in a polynomial algebra over a field has a finite field
extension as quotient. -/
theorem polynomial_maximal_ideal_quotient_finite_field_extension
    (k : Type u) [Field k] (n : ℕ)
    (m : Ideal (polynomialRing k n)) (hm : m.IsMaximal) :
    IsField (polynomialRing k n ⧸ m) ∧
      Module.Finite k (polynomialRing k n ⧸ m) := by
  have hfield : IsField (polynomialRing k n ⧸ m) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hm
  constructor
  · exact hfield
  · let _ : m.IsMaximal := hm
    let _ : Field (polynomialRing k n ⧸ m) := Ideal.Quotient.field m
    exact finite_of_finite_type_of_isJacobsonRing k (polynomialRing k n ⧸ m)

/-- The same finite-field-extension conclusion for maximal ideals of any
finite-type algebra over a field. -/
theorem finite_type_maximal_ideal_quotient_finite_field_extension
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R]
    (m : Ideal R) (hm : m.IsMaximal) :
    IsField (R ⧸ m) ∧ Module.Finite k (R ⧸ m) := by
  have hfield : IsField (R ⧸ m) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hm
  constructor
  · exact hfield
  · let _ : m.IsMaximal := hm
    let _ : Field (R ⧸ m) := Ideal.Quotient.field m
    exact finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)

/-! ## Exercise `Hilbert-Nullstellensatz` -/

/-- A finite-dimensional domain algebra over a field is a field. -/
theorem finite_dimensional_domain_algebra_is_field
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    [Module.Finite k R] [IsDomain R] :
    IsField R := by
  exact IsField.of_isDomain_of_finite k R

/-- A nonnilpotent element of a finite-type algebra is avoided by a maximal
ideal. -/
theorem finite_type_exists_maximal_ideal_not_mem
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (f : R) (hf : ¬ IsNilpotent f) :
    ∃ m : Ideal R, m.IsMaximal ∧ f ∉ m := by
  let _ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k) (B := R)
  have hnotradical : f ∉ (⊥ : Ideal R).radical := by
    rw [Ideal.mem_radical_iff]
    simpa [IsNilpotent] using hf
  have hnotjacobson : f ∉ (⊥ : Ideal R).jacobson := by
    rw [← Ideal.radical_eq_jacobson (⊥ : Ideal R)]
    exact hnotradical
  rw [Ideal.jacobson, Ideal.mem_sInf] at hnotjacobson
  push Not at hnotjacobson
  obtain ⟨m, hm, hfm⟩ := hnotjacobson
  exact ⟨m, hm.2, hfm⟩

/-! ### The non-finite-type counterexample -/

/-- The ring used for the counterexample is the formal power-series ring. -/
abbrev powerSeriesCounterexampleRing (k : Type u) [Semiring k] := PowerSeries k

/-- The counterexample element is the formal variable `X`. -/
def powerSeriesCounterexampleElement (k : Type u) [Semiring k] :
    powerSeriesCounterexampleRing k :=
  PowerSeries.X

/-- Formal power series over a field are not finite type as algebras over that
field. -/
theorem power_series_counterexample_not_finite_type
    (k : Type u) [Field k] :
    ¬ Algebra.FiniteType k (powerSeriesCounterexampleRing k) := by
  intro hft
  let _ : Algebra.FiniteType k (powerSeriesCounterexampleRing k) := hft
  obtain ⟨m, hm, hXm⟩ :=
    finite_type_exists_maximal_ideal_not_mem
      (k := k) (R := powerSeriesCounterexampleRing k)
      (f := powerSeriesCounterexampleElement k) (by
        rintro ⟨n, hn⟩
        have hc := congr_arg (PowerSeries.coeff n) hn
        simp [powerSeriesCounterexampleElement] at hc)
  have hm_eq : m = Ideal.span {powerSeriesCounterexampleElement k} :=
    (IsLocalRing.eq_maximalIdeal hm).trans
      (PowerSeries.maximalIdeal_eq_span_X (k := k))
  apply hXm
  rw [hm_eq]
  exact Ideal.mem_span_singleton_self _

/-- The formal variable in the power-series counterexample is not nilpotent. -/
theorem power_series_counterexample_element_not_nilpotent
    (k : Type u) [Field k] :
    ¬ IsNilpotent (powerSeriesCounterexampleElement k) := by
  rintro ⟨n, hn⟩
  have hc := congr_arg (PowerSeries.coeff n) hn
  rw [powerSeriesCounterexampleElement, PowerSeries.coeff_X_pow_self] at hc
  exact one_ne_zero hc

/-- The unique maximal ideal description of formal power series over a field. -/
theorem power_series_counterexample_maximal_ideal
    (k : Type u) [Field k] :
    IsLocalRing.maximalIdeal (powerSeriesCounterexampleRing k) =
      Ideal.span {powerSeriesCounterexampleElement k} := by
  simpa [powerSeriesCounterexampleRing, powerSeriesCounterexampleElement] using
    (PowerSeries.maximalIdeal_eq_span_X (k := k))

/-- Every maximal ideal in the power-series counterexample contains `X`. -/
theorem power_series_counterexample_maximal_ideals_contain_element
    (k : Type u) [Field k] :
    ∀ m : Ideal (powerSeriesCounterexampleRing k),
      m.IsMaximal → powerSeriesCounterexampleElement k ∈ m := by
  intro m hm
  rw [IsLocalRing.eq_maximalIdeal hm, power_series_counterexample_maximal_ideal k]
  exact Ideal.mem_span_singleton_self _

/-- A radical ideal in `ℂ[x₁, ..., xₙ]` is the infimum of the maximal ideals
which contain it. -/
theorem complex_polynomial_radical_ideal_eq_intersection_maximal_ideals
    (n : ℕ) (I : Ideal (polynomialRing ℂ n)) (hI : I.IsRadical) :
    I = sInf {m : Ideal (polynomialRing ℂ n) | I ≤ m ∧ m.IsMaximal} := by
  let _ : IsJacobsonRing (polynomialRing ℂ n) := inferInstance
  calc
    I = I.radical := hI.radical.symm
    _ = I.jacobson := Ideal.radical_eq_jacobson I
    _ = sInf {m : Ideal (polynomialRing ℂ n) | I ≤ m ∧ m.IsMaximal} := by
      rfl

/-! ## Remark `Hilbert-Nullstellensatz` -/

/-- Closed subsets of an affine polynomial spectrum are exactly the zero loci
of radical ideals. -/
theorem polynomial_closed_sets_correspond_to_radical_ideals
    (k : Type u) [Field k] (n : ℕ)
    (Z : Set (PrimeSpectrum (polynomialRing k n))) :
    IsClosed Z ↔
      ∃ I : Ideal (polynomialRing k n), I.IsRadical ∧
        Z = PrimeSpectrum.zeroLocus (I : Set (polynomialRing k n)) := by
  sorry

/-- Closed subsets of the spectrum of a finite-variable polynomial ring are
determined by the maximal ideals, equivalently the closed points, they contain. -/
theorem polynomial_closed_subsets_determined_by_closed_points
    (k : Type u) [Field k] (n : ℕ)
    {Z W : Set (PrimeSpectrum (polynomialRing k n))}
    (hZ : IsClosed Z) (hW : IsClosed W)
    (hclosed : ∀ p : PrimeSpectrum (polynomialRing k n),
      p.asIdeal.IsMaximal → (p ∈ Z ↔ p ∈ W)) :
    Z = W := by
  sorry

/-! ## Exercise `product-matrices-ring` -/

/-- The polynomial ring in the matrix-product exercise.  Variables `0` through
`3` are the entries of `X`, and variables `4` through `7` those of `Y`, in
row-major order. -/
abbrev matrixProductRing := polynomialRing ℂ 8

/-- The four entries of the matrix product `XY`. -/
def matrixProductEquations : Set matrixProductRing :=
  {
    MvPolynomial.X (0 : Fin 8) * MvPolynomial.X (4 : Fin 8) +
        MvPolynomial.X (1 : Fin 8) * MvPolynomial.X (6 : Fin 8),
    MvPolynomial.X (0 : Fin 8) * MvPolynomial.X (5 : Fin 8) +
        MvPolynomial.X (1 : Fin 8) * MvPolynomial.X (7 : Fin 8),
    MvPolynomial.X (2 : Fin 8) * MvPolynomial.X (4 : Fin 8) +
        MvPolynomial.X (3 : Fin 8) * MvPolynomial.X (6 : Fin 8),
    MvPolynomial.X (2 : Fin 8) * MvPolynomial.X (5 : Fin 8) +
        MvPolynomial.X (3 : Fin 8) * MvPolynomial.X (7 : Fin 8)
  }

/-- The ideal generated by the entries of the displayed matrix product. -/
def matrixProductIdeal : Ideal matrixProductRing :=
  Ideal.span matrixProductEquations

/-- The determinant of the `X` matrix in the matrix-product exercise. -/
def matrixXDeterminant : matrixProductRing :=
  MvPolynomial.X (0 : Fin 8) * MvPolynomial.X (3 : Fin 8) -
    MvPolynomial.X (1 : Fin 8) * MvPolynomial.X (2 : Fin 8)

/-- The determinant of the `Y` matrix in the matrix-product exercise. -/
def matrixYDeterminant : matrixProductRing :=
  MvPolynomial.X (4 : Fin 8) * MvPolynomial.X (7 : Fin 8) -
    MvPolynomial.X (5 : Fin 8) * MvPolynomial.X (6 : Fin 8)

/-- The component on which the matrix `X` is zero. -/
def matrixXZeroIdeal : Ideal matrixProductRing :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 8), MvPolynomial.X (1 : Fin 8),
      MvPolynomial.X (2 : Fin 8), MvPolynomial.X (3 : Fin 8)} :
      Set matrixProductRing)

/-- The component on which the matrix `Y` is zero. -/
def matrixYZeroIdeal : Ideal matrixProductRing :=
  Ideal.span
    ({MvPolynomial.X (4 : Fin 8), MvPolynomial.X (5 : Fin 8),
      MvPolynomial.X (6 : Fin 8), MvPolynomial.X (7 : Fin 8)} :
      Set matrixProductRing)

/-- The third component, cut out by `XY = 0` together with the two rank-one
determinant equations. -/
def matrixProductMiddleIdeal : Ideal matrixProductRing :=
  Ideal.span (matrixProductEquations ∪
    {matrixXDeterminant, matrixYDeterminant})

/-- The closed subset `V(I)` in the matrix-product exercise. -/
def matrixProductClosedSet : Set (PrimeSpectrum matrixProductRing) :=
  PrimeSpectrum.zeroLocus (matrixProductIdeal : Set matrixProductRing)

/-- The canonical correspondence between minimal primes over the matrix
product ideal and irreducible components of `V(I)`. -/
noncomputable def matrixProductComponentCorrespondence :
    matrixProductIdeal.minimalPrimes ≃o
      (irreducibleComponents matrixProductClosedSet)ᵒᵈ := by
  exact Ideal.minimalPrimes.equivIrreducibleComponents matrixProductIdeal

/-- The three irreducible components of `V(XY)`, represented by their prime
ideals of equations. -/
theorem matrix_product_irreducible_components :
    matrixProductIdeal.minimalPrimes =
      {matrixXZeroIdeal, matrixYZeroIdeal, matrixProductMiddleIdeal} := by
  sorry

end Formalization.Books.Exercises.Unit16
