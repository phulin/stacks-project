import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.NormNum

/-!
# Exercises, Chapter 9: Length

Mathlib's `Module.length` is the canonical implementation of the source's
supremum of lengths of strict submodule chains.  The declarations below use
that API directly and record the four exercises in the order in which they
occur in the source.
-/

namespace Formalization.Books.Exercises.Unit09

noncomputable section

universe u

/-! ## Length one and simple modules -/

/-- A module has source-length one exactly when it is a simple residue-field
quotient by a maximal ideal. -/
theorem module_length_one_iff_quotient_by_maximal_ideal
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] :
    Module.length A M = 1 ↔
      ∃ m : Ideal A, m.IsMaximal ∧
        Nonempty (M ≃ₗ[A] A ⧸ m) := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_quot_maximal]

/-! ## The three elementary computations -/

/- The first example is the canonical quotient `ℤ / 120ℤ`. -/
abbrev integerLengthExample : Type := ZMod 120

/-- The length of `ℤ / 120ℤ` as a `ℤ`-module. -/
theorem integer_quotient_120_length :
    Module.length ℤ integerLengthExample = 5 := by
  let e : (ℤ ⧸ Ideal.span ({(120 : ℤ)} : Set ℤ)) ≃ₗ[ℤ] integerLengthExample :=
    (Int.quotientSpanNatEquivZMod 120).toAddEquiv.toIntLinearEquiv
  rw [← e.length_eq]
  change Ring.ord ℤ 120 = 5
  rw [show (120 : ℤ) = 2 ^ 3 * 3 * 5 by norm_num]
  rw [Ring.ord_mul ℤ (by simp : (5 : ℤ) ∈ nonZeroDivisors ℤ)]
  rw [Ring.ord_mul ℤ (by simp : (3 : ℤ) ∈ nonZeroDivisors ℤ)]
  rw [Ring.ord_pow (by simp : (2 : ℤ) ∈ nonZeroDivisors ℤ)]
  rw [Ring.ord_of_irreducible (by norm_num [irreducible_iff_prime]; decide : Irreducible (2 : ℤ)),
    Ring.ord_of_irreducible (by norm_num [irreducible_iff_prime]; decide : Irreducible (3 : ℤ)),
    Ring.ord_of_irreducible (by norm_num [irreducible_iff_prime]; decide : Irreducible (5 : ℤ))]
  norm_num

/- The polynomial relations in the two complex/real examples. -/
def complexLengthPolynomial : Polynomial ℂ :=
  Polynomial.X ^ 100 + Polynomial.X + 1

def realLengthPolynomial : Polynomial ℝ :=
  Polynomial.X ^ 4 + Polynomial.C (2 : ℝ) * Polynomial.X ^ 2 + 1

abbrev complexLengthIdeal : Ideal (Polynomial ℂ) :=
  Ideal.span {complexLengthPolynomial}

abbrev realLengthIdeal : Ideal (Polynomial ℝ) :=
  Ideal.span {realLengthPolynomial}

abbrev complexLengthExample : Type :=
  Polynomial ℂ ⧸ complexLengthIdeal

abbrev realLengthExample : Type :=
  Polynomial ℝ ⧸ realLengthIdeal

/-- The length of `ℂ[x]/(x^100 + x + 1)` over `ℂ[x]`. -/
theorem complex_polynomial_quotient_length :
    Module.length (Polynomial ℂ) complexLengthExample = 100 := by
  change Ring.ord (Polynomial ℂ) complexLengthPolynomial = 100
  unfold complexLengthPolynomial
  have hsplit : (Polynomial.X ^ 100 + Polynomial.X + 1 : Polynomial ℂ).Splits :=
    IsAlgClosed.splits _
  have hdegree : (Polynomial.X ^ 100 + Polynomial.X + 1 : Polynomial ℂ).degree ≤ 100 := by
    have hpow : (Polynomial.X ^ 100 : Polynomial ℂ).degree ≤ 100 := by
      rw [Polynomial.degree_X_pow]
      exact le_rfl
    have hX : (Polynomial.X : Polynomial ℂ).degree ≤ 100 := by
      rw [Polynomial.degree_X]
      exact_mod_cast (by norm_num : (1 : ℕ) ≤ 100)
    have hone : (1 : Polynomial ℂ).degree ≤ 100 := by
      rw [Polynomial.degree_one]
      exact_mod_cast (by norm_num : (0 : ℕ) ≤ 100)
    have hdeg1 : (Polynomial.X ^ 100 + Polynomial.X : Polynomial ℂ).degree ≤ 100 := by
      exact Polynomial.degree_add_le_of_degree_le hpow hX
    exact Polynomial.degree_add_le_of_degree_le hdeg1 hone
  have hcoeff : (Polynomial.X ^ 100 + Polynomial.X + 1 : Polynomial ℂ).coeff 100 = 1 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      if_pos rfl, Polynomial.coeff_X_of_ne_one (by norm_num), Polynomial.coeff_one]
    norm_num
  have hcoeff_ne : (Polynomial.X ^ 100 + Polynomial.X + 1 : Polynomial ℂ).coeff 100 ≠ 0 := by
    rw [hcoeff]
    exact one_ne_zero
  have hmonic : (Polynomial.X ^ 100 + Polynomial.X + 1 : Polynomial ℂ).Monic :=
    Polynomial.monic_of_degree_le 100 hdegree hcoeff
  have hprod : ∀ s : Multiset ℂ,
      Ring.ord (Polynomial ℂ) (s.map (fun x => Polynomial.X - Polynomial.C x)).prod =
        s.card := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
        have hne : (s.map (fun x => Polynomial.X - Polynomial.C x)).prod ≠ 0 := by
          apply Multiset.prod_ne_zero
          simp [Polynomial.X_sub_C_ne_zero]
        rw [Multiset.map_cons, Multiset.prod_cons,
          Ring.ord_mul (Polynomial ℂ) (by simp [hne] :
            (s.map (fun x => Polynomial.X - Polynomial.C x)).prod ∈
              nonZeroDivisors (Polynomial ℂ)),
          Ring.ord_of_irreducible (Polynomial.irreducible_X_sub_C a), ih]
        simp [add_comm]
  have hnd : (Polynomial.X ^ 100 + Polynomial.X + 1 : Polynomial ℂ).natDegree = 100 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_eq_of_le_of_coeff_ne_zero hdegree hcoeff_ne)
  calc
    Ring.ord (Polynomial ℂ)
          (Polynomial.X ^ 100 + Polynomial.X + 1 : Polynomial ℂ) =
        Ring.ord (Polynomial ℂ)
          ((Polynomial.X ^ 100 + Polynomial.X + 1 : Polynomial ℂ).roots.map
            (Polynomial.X - Polynomial.C ·)).prod :=
      congrArg (Ring.ord (Polynomial ℂ)) (hsplit.eq_prod_roots_of_monic hmonic)
    _ = (Polynomial.X ^ 100 + Polynomial.X + 1 : Polynomial ℂ).roots.card := hprod _
    _ = 100 := by
      rw [← hsplit.natDegree_eq_card_roots]
      exact_mod_cast hnd

/-- The length of `ℝ[x]/(x^4 + 2x^2 + 1)` over `ℝ[x]`. -/
theorem real_polynomial_quotient_length :
    Module.length (Polynomial ℝ) realLengthExample = 4 := by
  sorry

/-! ## The local plane calculation -/

/-- The polynomial ring `k[x,y]`, represented by `MvPolynomial` on `Fin 2`. -/
abbrev planePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

/-- The origin ideal `(x,y)` in `k[x,y]`, using Mathlib's canonical ideal of
variables. -/
abbrev planeOriginIdeal (k : Type u) [Field k] : Ideal (planePolynomialRing k) :=
  MvPolynomial.idealOfVars (Fin 2) k

/- The origin ideal is the kernel of evaluation at the origin, hence prime.
   This is the only extra interface needed to instantiate the canonical
   localization-at-a-prime construction below. -/
instance planeOriginIdeal_isPrime (k : Type u) [Field k] :
    (planeOriginIdeal k).IsPrime := by
  have hker :
      RingHom.ker (MvPolynomial.constantCoeff : planePolynomialRing k →+* k) =
        planeOriginIdeal k := by
    ext p
    rw [RingHom.mem_ker]
    constructor
    · intro hp
      change p ∈ Ideal.span (Set.range (MvPolynomial.X : Fin 2 → planePolynomialRing k))
      rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra h
      have hm0 : m = 0 := by
        apply Finsupp.ext
        intro i
        exact not_ne_iff.mp (fun hmi => h ⟨i, by simp, hmi⟩)
      exact (MvPolynomial.mem_support_iff.mp hm)
        (by simpa [hm0, MvPolynomial.constantCoeff_eq] using hp)
    · intro hp
      change p ∈ Ideal.span (Set.range (MvPolynomial.X : Fin 2 → planePolynomialRing k)) at hp
      rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image] at hp
      by_contra h
      have hmem : (0 : Fin 2 →₀ ℕ) ∈ p.support :=
        MvPolynomial.mem_support_iff.mpr
          (by simpa [MvPolynomial.constantCoeff_eq] using h)
      obtain ⟨i, hi, hmi⟩ := hp 0 hmem
      exact hmi (by simp)
  rw [← hker]
  exact RingHom.ker_isPrime _

/-- The local ring `k[x,y]_(x,y)` from the source. -/
abbrev planeLocalRing (k : Type u) [Field k] :=
  Localization.AtPrime (planeOriginIdeal k)

/-- The images of the two coordinate variables in the local ring. -/
def planeX (k : Type u) [Field k] : planeLocalRing k :=
  algebraMap (planePolynomialRing k) (planeLocalRing k)
    (MvPolynomial.X (0 : Fin 2))

def planeY (k : Type u) [Field k] : planeLocalRing k :=
  algebraMap (planePolynomialRing k) (planeLocalRing k)
    (MvPolynomial.X (1 : Fin 2))

/-- The two equations from the local-plane exercise. -/
def planeEquationF (k : Type u) [Field k] : planeLocalRing k :=
  planeX k ^ 3 + planeX k ^ 2 * planeY k ^ 2 + planeY k ^ 100

def planeEquationG (k : Type u) [Field k] : planeLocalRing k :=
  planeY k ^ 3 - planeX k ^ 999

/-- The ideal `(f,g)` in the local plane ring. -/
def planeEquationIdeal (k : Type u) [Field k] : Ideal (planeLocalRing k) :=
  Ideal.span {planeEquationF k, planeEquationG k}

/-- The quotient module `A/(f,g)` in the local-plane exercise. -/
abbrev planeEquationQuotient (k : Type u) [Field k] : Type u :=
  planeLocalRing k ⧸ planeEquationIdeal k

/-- The local intersection quotient has length nine. -/
theorem local_plane_equation_quotient_length (k : Type u) [Field k] :
    Module.length (planeLocalRing k) (planeEquationQuotient k) = 9 := by
  sorry

end

end Formalization.Books.Exercises.Unit09
