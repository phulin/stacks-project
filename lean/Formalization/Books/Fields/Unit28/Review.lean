import Formalization.Books.Fields.Unit14.PurelyInseparableExtensions
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Galois.Basic

/-!
# Fields, Chapter 28: Review

The source reviews the canonical notions of algebraic, separable, purely
inseparable, normal, and Galois extensions.  Those notions are already
provided by Mathlib and the earlier Fields chapters, so this file adds only
the source-facing interfaces that are not already available there.
-/

namespace Formalization.Books.Fields.Unit28

noncomputable section

open Polynomial

/-! ## Algebraic and separable elements -/

/- The algebraic/transcendental dichotomy is already the exact theorem
   `Unit08.simple_extension_algebraic_or_transcendental`.  Likewise,
   `minpoly` is the canonical minimal polynomial, and Unit09 already records
   its monicity, irreducibility, annihilation, and uniqueness properties.  In
   particular, the source's degree of an algebraic element is represented by
   `(minpoly k α).natDegree`; Unit09 also identifies this natural degree with
   the finite dimension of the simple extension. -/

/-- The minimal-polynomial data listed in the Review holds for every
    algebraic element. -/
theorem review_minimal_polynomial_data
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α) :
    (minpoly k α).Monic ∧
      Irreducible (minpoly k α) ∧
        Polynomial.aeval α (minpoly k α) = 0 := by
  exact ⟨minpoly.monic hα.isIntegral, minpoly.irreducible hα.isIntegral,
    minpoly.aeval k α⟩

/-- The monic irreducible polynomial annihilating an algebraic element is its
    minimal polynomial. -/
theorem review_minimal_polynomial_unique
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α) {P : k[X]}
    (hP_monic : P.Monic) (hP_irreducible : Irreducible P)
    (hP_root : Polynomial.aeval α P = 0) :
    P = minpoly k α := by
  exact minpoly.eq_of_irreducible_of_monic hP_irreducible hP_root hP_monic

/- The derivative criterion and the distinct-root formulation are already
   supplied by the separability API.  The following theorem places both
   formulations directly beside the Review's minimal-polynomial discussion.
-/
/-- An algebraic element is separable exactly when its minimal polynomial has
    nonzero derivative. -/
theorem review_separable_iff_minpoly_derivative_ne_zero
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α) :
    IsSeparable k α ↔ (minpoly k α).derivative ≠ 0 := by
  rw [Formalization.Books.Fields.Unit12.separable_element_iff_minpoly_separable,
    Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hα.isIntegral)]

/-- An algebraic element is separable exactly when its minimal polynomial has
    pairwise distinct roots in the algebraic closure. -/
theorem review_separable_iff_distinct_algebraic_closure_roots
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α) :
    IsSeparable k α ↔
      ((minpoly k α).aroots (AlgebraicClosure k)).Nodup := by
  rw [Formalization.Books.Fields.Unit12.separable_element_iff_minpoly_separable]
  exact Formalization.Books.Fields.Unit12.irreducible_polynomial_separable_iff_distinct_algebraic_closure_roots
    (minpoly.irreducible hα.isIntegral)

/-- The distinct-root condition can equivalently be written as the displayed
    product of the monic linear factors in the algebraic closure. -/
theorem review_separable_iff_minpoly_product_of_distinct_roots
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α) :
    IsSeparable k α ↔
      ∃ roots : Multiset (AlgebraicClosure k),
        roots.Nodup ∧ roots.card = (minpoly k α).natDegree ∧
          (minpoly k α).map (algebraMap k (AlgebraicClosure k)) =
            (roots.map (fun r => X - C r)).prod := by
  let P := minpoly k α
  let A := AlgebraicClosure k
  have hPmonic : P.Monic := minpoly.monic hα.isIntegral
  have hPirr : Irreducible P := minpoly.irreducible hα.isIntegral
  have hsplit : (P.map (algebraMap k A)).Splits := IsAlgClosed.splits _
  have hcard : (P.aroots A).card = P.natDegree :=
    IsAlgClosed.card_aroots_eq_natDegree
  have hprod : P.map (algebraMap k A) =
      ((P.aroots A).map (fun r => X - C r)).prod := by
    simpa [Polynomial.aroots_def] using
      hsplit.eq_prod_roots_of_monic (hPmonic.map (algebraMap k A))
  constructor
  · intro hsep
    refine ⟨P.aroots A, ?_, hcard, hprod⟩
    exact (Formalization.Books.Fields.Unit12.irreducible_polynomial_separable_iff_distinct_algebraic_closure_roots
      hPirr).1
      ((Formalization.Books.Fields.Unit12.separable_element_iff_minpoly_separable α).1 hsep)
  · rintro ⟨roots, hnodup, _, hroots⟩
    have hnodupP : (P.aroots A).Nodup := by
      rw [Polynomial.aroots_def, hroots, Polynomial.roots_multiset_prod_X_sub_C]
      exact hnodup
    apply (Formalization.Books.Fields.Unit12.separable_element_iff_minpoly_separable α).2
    exact (Formalization.Books.Fields.Unit12.irreducible_polynomial_separable_iff_distinct_algebraic_closure_roots
      hPirr).2 hnodupP

/- The earlier separability chapter's Frobenius-contraction theorem supplies
   the polynomial-in-a-power assertion in the inseparable case.  This
   source-facing statement also records the maximal exponent and the
   separability of the corresponding powered element.
-/
/-- If the minimal polynomial of an algebraic element has zero derivative,
    it is a polynomial in a largest Frobenius power, and the corresponding
    power of the element is separable. -/
theorem review_inseparable_frobenius_contraction
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α)
    (hderiv : (minpoly k α).derivative = 0) :
    ∃ (p e : ℕ) (Q : k[X]),
      p.Prime ∧ CharP k p ∧ Q.Separable ∧ Irreducible Q ∧
        Polynomial.expand k (p ^ e) Q = minpoly k α ∧
          (∀ m : ℕ,
            (∃ R : k[X], Polynomial.expand k (p ^ m) R = minpoly k α) →
              m ≤ e) ∧
          IsSeparable k (α ^ (p ^ e)) := by
  have hPirr : Irreducible (minpoly k α) := minpoly.irreducible hα.isIntegral
  obtain ⟨p, e, Q, hp_pos, hchar, hQsep, hQirr, hPQ⟩ :=
    Formalization.Books.Fields.Unit12.irreducible_polynomial_derivative_zero_factorization
      hPirr hderiv
  letI : CharP k p := hchar
  have hp : p.Prime :=
    (CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt hp_pos)
  refine ⟨p, e, Q, hp, hchar, hQsep, hQirr, hPQ, ?_, ?_⟩
  · intro m hm
    rcases hm with ⟨R, hR⟩
    by_contra hme
    have hem : e < m := Nat.lt_of_not_ge hme
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hem.le
    have hd_pos : 0 < d := by omega
    have hQeq : Q = Polynomial.expand k (p ^ d) R := by
      apply Polynomial.expand_injective (pow_pos hp_pos e)
      calc
        Polynomial.expand k (p ^ e) Q = minpoly k α := hPQ
        _ = Polynomial.expand k (p ^ (e + d)) R := hR.symm
        _ = Polynomial.expand k (p ^ e) (Polynomial.expand k (p ^ d) R) := by
          rw [pow_add, Polynomial.expand_mul]
    rcases Polynomial.isUnit_or_eq_zero_of_separable_expand p d hp_pos
        (hQeq ▸ hQsep) with hunit | hd
    · have hunitP : IsUnit (minpoly k α) := by
        rw [← hR]
        exact hunit.map (Polynomial.expand k (p ^ (e + d)))
      exact hPirr.not_isUnit hunitP
    · exact (Nat.ne_of_gt hd_pos hd).elim
  · have hrootQ : Polynomial.aeval (α ^ (p ^ e)) Q = 0 := by
      calc
        Polynomial.aeval (α ^ (p ^ e)) Q =
            Polynomial.aeval α (Polynomial.expand k (p ^ e) Q) :=
          (Polynomial.expand_aeval (p ^ e) Q α).symm
        _ = Polynomial.aeval α (minpoly k α) := by rw [hPQ]
        _ = 0 := minpoly.aeval k α
    apply (Formalization.Books.Fields.Unit12.separable_element_iff_minpoly_separable
      (α ^ (p ^ e))).2
    exact Polynomial.Separable.of_dvd hQsep (minpoly.dvd k _ hrootQ)

/-! ## Algebraic field extensions -/

/- The five extension definitions in the source are canonical declarations,
   not parallel local predicates:

   * `Algebra.IsAlgebraic k K` is algebraicness, with
     `Unit08.algebraic_extension_iff_all_elements_algebraic` as its
     pointwise characterization.
   * `Algebra.IsSeparable k K` is separability; Mathlib's definition already
     implies algebraicity, and Unit12 records its pointwise characterization.
   * `IsPurelyInseparable k K` is the canonical purely inseparable class.
     Unit14's `purely_inseparable_extension_iff_pow_mem` gives the source's
     p-power characterization when `CharP k p` holds for a prime `p`.
   * `Normal k K` packages algebraicity with splitting of every minimal
     polynomial, exposed pointwise by Mathlib's `normal_iff` and `Normal.splits`.
   * `IsGalois k K` is separable and normal, exactly as stated by
     `isGalois_iff`.

   No duplicate definitions are introduced for these established notions.
-/

/-! ## The p-th-root lemma -/

/- “Pairwise distinct roots in an algebraic closure” is represented by
   `Polynomial.Separable`, whose root formulation is the theorem used above.
   “All coefficients are p-th powers” is kept inline as a condition on
   `Polynomial.coeff`; this avoids introducing a second polynomial predicate.
-/

private theorem pth_root_of_separable_polynomial_aux
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] (p : ℕ) (hp : p.Prime) [CharP K p]
    (α : L) (P : K[X])
    (hroot : Polynomial.aeval α P = 0)
    (hseparable : P.Separable)
    (hcoeff : ∀ i : ℕ, ∃ b : K, P.coeff i = b ^ p) :
    ∃ β : L, β ^ p = α := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : ExpChar K p := ExpChar.prime hp
  let f : K →+* K := frobenius K p
  have hPlifts : P ∈ Polynomial.lifts f := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rcases hcoeff i with ⟨b, hb⟩
    exact ⟨b, by simpa [f, frobenius_def] using hb.symm⟩
  obtain ⟨Q, hQmap, _⟩ := Polynomial.exists_support_eq_of_mem_lifts hPlifts
  have hQsep : Q.Separable := by
    apply (Polynomial.separable_map f).1
    simpa [hQmap] using hseparable
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  letI : ExpChar L p := ExpChar.prime hp
  by_contra hno
  have hno_root : ∀ b : L, b ^ p ≠ α := by
    simpa only [not_exists] using hno
  let fL : L[X] := X ^ p - C α
  have hfL : Irreducible fL := by
    dsimp [fL]
    exact Formalization.Books.Fields.Unit14.take_pth_root_polynomial_irreducible
      p hp α hno_root
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap L (AlgebraicClosure L) α) hp.pos
  have hProot_closure :
      (P.map (algebraMap K (AlgebraicClosure L))).eval
          (algebraMap L (AlgebraicClosure L) α) = 0 := by
    have hcomp :
        (algebraMap (AlgebraicClosure L) (AlgebraicClosure L)).comp
            (algebraMap K (AlgebraicClosure L)) =
          (algebraMap L (AlgebraicClosure L)).comp (algebraMap K L) := by
      simpa using (IsScalarTower.algebraMap_eq K L (AlgebraicClosure L))
    have hmap := Polynomial.map_aeval_eq_aeval_map
      (φ := algebraMap K (AlgebraicClosure L))
      (ψ := algebraMap L (AlgebraicClosure L)) hcomp P α
    have hmap' :
        (algebraMap L (AlgebraicClosure L)) ((Polynomial.aeval α) P) =
          (P.map (algebraMap K (AlgebraicClosure L))).eval
            (algebraMap L (AlgebraicClosure L) α) := by
      simpa [Polynomial.aeval_def] using hmap
    rw [← hmap']
    simp [hroot]
  have hQroot_closure :
      Polynomial.aeval γ Q = 0 := by
    have hpow_eval :
        (Polynomial.aeval γ Q) ^ p =
          Polynomial.aeval (γ ^ p) (Q.map f) := by
      calc
        (Polynomial.aeval γ Q) ^ p = Polynomial.aeval γ (Q ^ p) := by
          rw [map_pow]
        _ = Polynomial.aeval γ ((Polynomial.expand K p Q).map (frobenius K p)) := by
          rw [Polynomial.map_frobenius_expand]
        _ = Polynomial.aeval γ (Polynomial.expand K p (Q.map f)) := by
          simpa [f] using congrArg (Polynomial.aeval γ)
            (Polynomial.map_expand (p := p) (f := frobenius K p) (q := Q))
        _ = Polynomial.aeval (γ ^ p) (Q.map f) := Polynomial.expand_aeval p _ _
    apply eq_zero_of_pow_eq_zero (n := p)
    rw [hpow_eval, hQmap, hγ, ← Polynomial.eval_map_algebraMap]
    exact hProot_closure
  have hQroot_L :
      Polynomial.aeval γ (Q.map (algebraMap K L)) = 0 := by
    calc
      Polynomial.aeval γ (Q.map (algebraMap K L)) =
          ((Q.map (algebraMap K L)).map (algebraMap L (AlgebraicClosure L))).eval γ :=
        (Polynomial.eval_map_algebraMap (Q.map (algebraMap K L)) γ).symm
      _ = (Q.map (algebraMap K (AlgebraicClosure L))).eval γ := by
        rw [Polynomial.map_map, IsScalarTower.algebraMap_eq K L (AlgebraicClosure L)]
      _ = Polynomial.aeval γ Q := Polynomial.eval_map_algebraMap Q γ
      _ = 0 := hQroot_closure
  have hfL_root : Polynomial.aeval γ fL = 0 := by
    simp [fL, hγ]
  have hnotcop : ¬ IsCoprime fL (Q.map (algebraMap K L)) := by
    rintro ⟨A, B, hAB⟩
    have hAB' := congrArg (Polynomial.aeval γ) hAB
    simp [map_add, map_mul, hfL_root, hQroot_L] at hAB'
  rcases EuclideanDomain.dvd_or_coprime fL (Q.map (algebraMap K L)) hfL with hdiv | hcop
  · have hfsep : fL.Separable := hQsep.map.of_dvd hdiv
    have hfderiv : fL.derivative = 0 := by
      simp [fL, Polynomial.derivative_sub, Polynomial.derivative_pow,
        CharP.cast_eq_zero]
    exact (Polynomial.separable_iff_derivative_ne_zero hfL).1 hfsep hfderiv
  · exact hnotcop hcop

/-- In a separable algebraic extension, an element whose minimal-polynomial
    coefficients are p-th powers already has a p-th root in the extension. -/
theorem pth_root_of_minpoly_coefficients
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] (p : ℕ) (hp : p.Prime) [CharP K p]
    (α : L)
    (hcoeff : ∀ i : ℕ, ∃ b : K, (minpoly K α).coeff i = b ^ p) :
    ∃ β : L, β ^ p = α := by
  apply pth_root_of_separable_polynomial_aux p hp α (minpoly K α)
    (minpoly.aeval K α) ?_ hcoeff
  exact (Formalization.Books.Fields.Unit12.separable_element_iff_minpoly_separable α).1
    (Algebra.IsSeparable.isSeparable K α)

/-- More generally, a root in a separable algebraic extension of a separable
    polynomial with p-th-power coefficients has a p-th root in the extension.
-/
theorem pth_root_of_separable_polynomial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] (p : ℕ) (hp : p.Prime) [CharP K p]
    (α : L) (P : K[X])
    (hroot : Polynomial.aeval α P = 0)
    (hseparable : P.Separable)
    (hcoeff : ∀ i : ℕ, ∃ b : K, P.coeff i = b ^ p) :
    ∃ β : L, β ^ p = α := by
  exact pth_root_of_separable_polynomial_aux p hp α P hroot hseparable hcoeff

end

end Formalization.Books.Fields.Unit28
