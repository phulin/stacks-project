import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Commutative Algebra, Chapter 115: Noether normalization

The canonical polynomial-ring, finite-map, residue-field, localization, and
Krull-dimension interfaces are used throughout.  The source-facing auxiliary
definitions below make the weighted multi-index and affine normalization
statements explicit without duplicating Mathlib's polynomial-ring API.
-/

namespace Formalization.Books.Algebra.Unit115

universe u v

noncomputable section

open Set
open scoped Polynomial

/-! ## The two helper lemmas -/

/-- The weighted degree of a multi-index for a chosen family of weights. -/
def weightedMultiIndex {σ : Type u} [Fintype σ]
    (e : σ → ℕ) (ν : σ →₀ ℕ) : ℕ :=
  ∑ i, e i * ν i

/-- The absolute difference of two natural numbers. -/
def natDifference (a b : ℕ) : ℕ :=
  if a ≤ b then b - a else a - b

/-- A concrete version of the source's notation `e₁ ≫ e₂ ≫ ⋯`: every
coordinate difference dominates all possible contributions from later
coordinates on the given finite set of multi-indices. -/
def multiIndexDominates {σ : Type u} [Fintype σ] [LinearOrder σ]
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) : Prop :=
  ∀ ⦃i : σ⦄ ⦃ν ν' : σ →₀ ℕ⦄,
    ν ∈ N → ν' ∈ N → ν i ≠ ν' i →
      e i * natDifference (ν i) (ν' i) >
        ∑ j, if i < j then e j * natDifference (ν j) (ν' j) else 0

/-- Distinct multi-indices in a finite nonempty set have distinct weighted
degrees for a dominating family of weights. -/
theorem helper_multiIndex_separation
    {n : ℕ} (N : Finset (Fin n →₀ ℕ)) (hN : N.Nonempty)
    (e : Fin n → ℕ) (he : multiIndexDominates N e) :
    ∀ ⦃ν ν' : Fin n →₀ ℕ⦄,
      ν ∈ N → ν' ∈ N →
        (weightedMultiIndex e ν = weightedMultiIndex e ν' ↔ ν = ν') := by
  classical
  have hsplit (i : Fin n) (f : Fin n → ℕ) :
      (∑ j, f j) =
        (∑ j ∈ Finset.univ.filter (fun j => j < i), f j) +
          (∑ j ∈ Finset.univ.filter (fun j => ¬ j < i), f j) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have hsplit2 (i : Fin n) (f : Fin n → ℕ) :
      (∑ j, f j) =
        (∑ j ∈ Finset.univ.filter (fun j => j < i), f j) + f i +
          (∑ j ∈ Finset.univ.filter (fun j => i < j), f j) := by
    rw [hsplit]
    have hi : i ∈ Finset.univ.filter (fun j : Fin n => ¬ j < i) := by simp
    have hs :
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j < i), f j) =
          f i +
            (∑ j ∈ (Finset.univ.filter (fun j : Fin n => ¬ j < i)).erase i, f j) := by
      rw [add_comm]
      exact (Finset.sum_erase_add _ _ hi).symm
    rw [hs]
    have heq :
        (∑ j ∈ (Finset.univ.filter (fun j : Fin n => ¬ j < i)).erase i, f j) =
          (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f j) := by
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · intro j hj
        rfl
    rw [heq]
    ac_rfl
  have hsumfilter (i : Fin n) (f : Fin n → ℕ) :
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f j) =
        ∑ j, if i < j then f j else 0 := by
    rw [Finset.sum_filter]
  have hdiff_comm (a b : ℕ) : natDifference a b = natDifference b a := by
    simp [natDifference]
    split_ifs <;> omega
  have hmul {a b c : ℕ} (h : a ≤ b) :
      c * b = c * (b - a) + c * a := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h]
  have htail_aux (i : Fin n) (u v : Fin n →₀ ℕ) :
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * u j) ≤
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * v j) +
          ∑ j, if i < j then e j * natDifference (u j) (v j) else 0 := by
    calc
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * u j) ≤
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            (e j * v j + e j * natDifference (u j) (v j)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hc : u j ≤ v j + natDifference (u j) (v j) := by
          simp [natDifference]
          split_ifs <;> omega
        have hm := Nat.mul_le_mul_left (e j) hc
        simpa [Nat.mul_add] using hm
      _ = (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * v j) +
          ∑ j, if i < j then e j * natDifference (u j) (v j) else 0 := by
        rw [Finset.sum_add_distrib]
        congr 1
        exact hsumfilter i (fun j => e j * natDifference (u j) (v j))
  intro ν ν' hν hν'
  constructor
  · intro hsum
    by_contra hne
    let D : Finset (Fin n) := Finset.univ.filter (fun i => ν i ≠ ν' i)
    have hD : D.Nonempty := by
      by_contra hD
      apply hne
      ext i
      by_contra hdiff
      have hiD : i ∈ D := by simp [D, hdiff]
      have heq : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
      rw [heq] at hiD
      simp at hiD
    let i : Fin n := D.min' hD
    have hiD : i ∈ D := by exact D.min'_mem hD
    have hi_ne : ν i ≠ ν' i := by simpa [D] using hiD
    have hbefore : ∀ j : Fin n, j < i → ν j = ν' j := by
      intro j hji
      by_contra hjne
      have hjD : j ∈ D := by simp [D, hjne]
      have hle : i ≤ j := D.min'_le j hjD
      omega
    let B : ℕ := ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), e j * ν j
    let B' : ℕ := ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), e j * ν' j
    let T : ℕ := ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * ν j
    let T' : ℕ := ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * ν' j
    have hB : B = B' := by
      apply Finset.sum_congr
      · rfl
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [hbefore j hj]
    have hmid : e i * ν i + T = e i * ν' i + T' := by
      dsimp [B, B', T, T'] at *
      have hp := hsplit2 i (fun j => e j * ν j)
      have hp' := hsplit2 i (fun j => e j * ν' j)
      simp only [weightedMultiIndex] at hsum
      omega
    have hdom := he hν hν' hi_ne
    by_cases hle : ν i ≤ ν' i
    · have hlt : ν i < ν' i := lt_of_le_of_ne hle hi_ne
      have hm := hmul (c := e i) hle
      have hrel : T = T' + e i * (ν' i - ν i) := by
        omega
      have htail := htail_aux i ν ν'
      have hndi : natDifference (ν i) (ν' i) = ν' i - ν i := by
        simp [natDifference, hle]
      rw [hndi] at hdom
      omega
    · have hle' : ν' i ≤ ν i := Nat.le_of_lt (lt_of_not_ge hle)
      have hm := hmul (c := e i) hle'
      have hrel : T' = T + e i * (ν i - ν' i) := by
        omega
      have htail := htail_aux i ν' ν
      have htail' :
          T' ≤ T + ∑ j, if i < j then e j * natDifference (ν j) (ν' j) else 0 := by
        simpa only [hdiff_comm] using htail
      have hndi : natDifference (ν i) (ν' i) = ν i - ν' i := by
        simp [natDifference, hle]
      rw [hndi] at hdom
      omega
  · intro h
    subst ν'
    rfl

/-- The substitution used in the polynomial helper lemma.  The last variable
is retained as the polynomial variable and each earlier variable is shifted
by a power of it. -/
def lastVariableSubstitution {R : Type u} [CommRing R]
    (n : ℕ) (e : Fin n → ℕ) :
    Fin (n + 1) → Polynomial (MvPolynomial (Fin n) R) :=
  Fin.lastCases Polynomial.X
    (fun i => Polynomial.C (MvPolynomial.X i) + Polynomial.X ^ e i)

/-- The polynomial obtained from a multivariable polynomial by the preceding
substitution. -/
def noetherPolynomialSubstitution {R : Type u} [CommRing R]
    {n : ℕ} (g : MvPolynomial (Fin (n + 1)) R) (e : Fin n → ℕ) :
    Polynomial (MvPolynomial (Fin n) R) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : MvPolynomial (Fin n) R →+* Polynomial (MvPolynomial (Fin n) R)).comp
      (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
    (lastVariableSubstitution n e) g

/-- The full family of weights in the polynomial helper lemma; the retained
last variable has weight one, as in the source. -/
def lastVariableWeight {n : ℕ} (e : Fin n → ℕ) : Fin (n + 1) → ℕ :=
  Fin.lastCases 1 e

/-- After a sufficiently separated substitution, the resulting polynomial has
positive degree and scalar leading coefficient equal to a nonzero coefficient
of the original polynomial. -/
theorem helper_polynomial_leading_term
    {R : Type u} [CommRing R] {n : ℕ}
    (g : MvPolynomial (Fin (n + 1)) R)
    (hg : g ∉ Set.range (fun a : R => MvPolynomial.C a))
    (e : Fin n → ℕ)
    (he : multiIndexDominates g.support (lastVariableWeight e)) :
    ∃ d : ℕ, ∃ a : R, 0 < d ∧ a ≠ 0 ∧
      ∃ ν ∈ g.support, a = g.coeff ν ∧
        (noetherPolynomialSubstitution g e).natDegree = d ∧
          (noetherPolynomialSubstitution g e).leadingCoeff =
            MvPolynomial.C a := by
  sorry

/-! ## Polynomial quotients and one relation -/

/-- The subalgebra generated by chosen polynomial representatives in a
polynomial quotient. -/
def quotientGeneratorSubalgebra
    {k : Type u} [CommRing k] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (y : Fin r → MvPolynomial (Fin n) k) :
    Subalgebra k ((MvPolynomial (Fin n) k) ⧸ I) :=
  Algebra.adjoin k (Set.range (fun i => Ideal.Quotient.mk I (y i)))

/-- The `ℤ`-subalgebra of a polynomial ring generated by its variables. -/
def integerPolynomialSubalgebra
    (k : Type u) [CommRing k] (n : ℕ) :
    Subalgebra ℤ (MvPolynomial (Fin n) k) :=
  Algebra.adjoin ℤ (Set.range (fun i : Fin n => MvPolynomial.X i))

/-- One nonzero relation in a polynomial quotient makes the quotient finite
over a polynomial subalgebra on one fewer variable. -/
theorem one_relation
    {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hIproper : I ≠ ⊤) (hInonzero : I ≠ ⊥) :
    ∃ y : Fin (n - 1) → MvPolynomial (Fin n) k,
      RingHom.Finite
          (quotientGeneratorSubalgebra I y).val.toRingHom ∧
        ∀ i, y i ∈ integerPolynomialSubalgebra k n := by
  sorry

/-! ## Noether normalization -/

/-- The integral, injective core of Noether normalization is Mathlib's
canonical quotient theorem. -/
theorem noether_normalization_integral_core
    {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    ∃ r : ℕ, r ≤ n ∧
      ∃ g : MvPolynomial (Fin r) k →ₐ[k]
          ((MvPolynomial (Fin n) k) ⧸ I),
        Function.Injective g ∧ g.IsIntegral := by
  exact exists_integral_inj_algHom_of_quotient I hI

/-- Noether normalization for a polynomial quotient, with the source-facing
representatives of the normalized variables recorded in the original
polynomial ring.  The finite and injective map uses Mathlib's canonical
`AlgHom` interface. -/
theorem noether_normalization
    {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    ∃ r : ℕ, r ≤ n ∧
      ∃ g : MvPolynomial (Fin r) k →ₐ[k]
          ((MvPolynomial (Fin n) k) ⧸ I),
        Function.Injective g ∧
          RingHom.Finite g.toRingHom ∧
            ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) = r ∧
              ∃ y : Fin r → MvPolynomial (Fin n) k,
                (∀ i, g (MvPolynomial.X i) = Ideal.Quotient.mk I (y i)) ∧
                  ∀ i, y i ∈ integerPolynomialSubalgebra k n := by
  sorry

/-! ## Normalization at a point -/

/-- The affine local dimension at a prime, written as the infimum of the
Krull dimensions of its principal neighborhoods. -/
def affineDimensionAtPrime {S : Type u} [CommRing S]
    (q : Ideal S) : WithBot ℕ∞ :=
  ⨅ (g : { g : S // g ∉ q }), ringKrullDim (Localization.Away (g : S))

/-- At a point of a finite-type affine algebra over a field, one principal
neighborhood realizes the local dimension and admits finite injective
normalization. -/
theorem noether_normalization_at_point
    {k : Type u} [Field k] {S : Type u} [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S]
    (q : Ideal S) (hq : q.IsPrime) :
    let x : PrimeSpectrum S := ⟨q, hq⟩
    ∃ g : S, g ∉ x.asIdeal ∧
      ∃ d : ℕ,
        affineDimensionAtPrime x.asIdeal = d ∧
          ringKrullDim (Localization.Away g) = d ∧
            ∃ φ : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g,
              Function.Injective φ ∧ RingHom.Finite φ.toRingHom := by
  sorry

/-! ## Refined normalization -/

/-- The ideal generated by the last `n - r` variables of an `n`-variable
polynomial ring. -/
def tailVariableIdeal
    (k : Type u) [CommRing k] (n r : ℕ) :
    Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span {p | ∃ i : Fin n, r ≤ i.1 ∧ p = MvPolynomial.X i}

/-- A prime ideal in a polynomial ring admits a finite coordinate change whose
contraction is generated by the variables beyond its transcendence degree. -/
theorem refined_noether_normalization
    {k : Type u} [Field k] {n : ℕ}
    (q : Ideal (MvPolynomial (Fin n) k)) (hq : q.IsPrime) :
    letI : q.IsPrime := hq
    ∃ r : ℕ, r ≤ n ∧
      Algebra.trdeg k q.ResidueField = r ∧
        ∃ φ : MvPolynomial (Fin n) k →+*
            MvPolynomial (Fin n) k,
          RingHom.Finite φ ∧ q.comap φ = tailVariableIdeal k n r := by
  sorry

/-! ## Normalization over a domain -/

/-- The domain version of Noether normalization: the finite polynomial
subalgebra is realized by an injective intermediate `R`-subalgebra, and it
becomes the original algebra after inverting one nonzero base element. -/
theorem noether_normalization_over_domain
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (hfiniteType : RingHom.FiniteType φ) :
    letI : Algebra R S := φ.toAlgebra
    ∃ d : ℕ, ∃ S' : Subalgebra R S,
      ∃ g : MvPolynomial (Fin d) R →ₐ[R] S',
        Function.Injective (MvPolynomial.C : R →+* MvPolynomial (Fin d) R) ∧
          Function.Injective g.toRingHom ∧
            RingHom.Finite g.toRingHom ∧
              Function.Injective S'.val ∧
                (S'.val.toRingHom.comp g.toRingHom).comp
                    (MvPolynomial.C : R →+* MvPolynomial (Fin d) R) = φ ∧
                  ∃ f : R, f ≠ 0 ∧
                    Nonempty
                      (Localization.Away (algebraMap R S' f) ≃+*
                        Localization.Away (φ f)) := by
  sorry

end

end Formalization.Books.Algebra.Unit115
