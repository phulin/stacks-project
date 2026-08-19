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
import Mathlib.Tactic.Ring
import Mathlib.FieldTheory.KummerPolynomial

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
abbrev integerLengthExample : Type := ZMod 120

/-- The length of `ℤ / 120ℤ` as a `ℤ`-module. -/
theorem integer_quotient_120_length :
    Module.length ℤ integerLengthExample = 5 := by
  rw [← (Int.quotientSpanNatEquivZMod 120).toIntAlgEquiv.toLinearEquiv.length_eq]
  change Ring.ord ℤ 120 = 5
  have h2 : Irreducible (2 : ℤ) :=
    irreducible_iff_prime.mpr (Int.prime_iff_natAbs_prime.mpr (by decide))
  have h3 : Irreducible (3 : ℤ) :=
    irreducible_iff_prime.mpr (Int.prime_iff_natAbs_prime.mpr (by decide))
  have h5 : Irreducible (5 : ℤ) :=
    irreducible_iff_prime.mpr (Int.prime_iff_natAbs_prime.mpr (by decide))
  have h2' : (2 : ℤ) ∈ nonZeroDivisors ℤ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (by norm_num)
  have h3' : (3 : ℤ) ∈ nonZeroDivisors ℤ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (by norm_num)
  have h5' : (5 : ℤ) ∈ nonZeroDivisors ℤ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (by norm_num)
  rw [show (120 : ℤ) = 2 ^ 3 * 3 * 5 by norm_num,
    Ring.ord_mul (R := ℤ) h5', Ring.ord_mul (R := ℤ) h3',
    Ring.ord_pow (R := ℤ) h2', Ring.ord_of_irreducible h2,
    Ring.ord_of_irreducible h3, Ring.ord_of_irreducible h5]
  norm_num
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
  let hs := IsAlgClosed.splits complexLengthPolynomial
  have hdeg : (Polynomial.X + (1 : Polynomial ℂ)).degree < 100 := by
    rw [show (1 : Polynomial ℂ) = Polynomial.C (1 : ℂ) by simp]
    rw [Polynomial.degree_X_add_C]
    norm_num
  have hm0 : (Polynomial.X ^ 100 + (Polynomial.X + (1 : Polynomial ℂ))).Monic :=
    Polynomial.monic_X_pow_add (p := Polynomial.X + (1 : Polynomial ℂ))
      (n := 100) hdeg
  have hpoly : complexLengthPolynomial =
      Polynomial.X ^ 100 + (Polynomial.X + (1 : Polynomial ℂ)) := by
    unfold complexLengthPolynomial
    rw [add_assoc]
  have hm : complexLengthPolynomial.Monic := by
    rw [hpoly]
    exact hm0
  have hfactor : complexLengthPolynomial =
      (complexLengthPolynomial.roots.map
        (fun a => Polynomial.X - Polynomial.C a)).prod :=
    hs.eq_prod_roots_of_monic hm
  rw [hfactor]
  have hord : ∀ m : Multiset ℂ,
      Ring.ord (Polynomial ℂ)
          (m.map (fun a => Polynomial.X - Polynomial.C a)).prod = m.card := by
    intro m
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons a m ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, Ring.ord_mul' _]
        · rw [ih, Ring.ord_of_irreducible (Polynomial.irreducible_X_sub_C a)]
          simp [add_comm]
        · exact mem_nonZeroDivisors_iff_ne_zero.mpr
            (Polynomial.X_sub_C_ne_zero a)
  rw [hord, ← hs.natDegree_eq_card_roots]
  rw [hpoly, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · rw [show (1 : Polynomial ℂ) = Polynomial.C (1 : ℂ) by simp,
      Polynomial.natDegree_X_add_C]
    norm_num
theorem real_polynomial_quotient_length :
    Module.length (Polynomial ℝ) realLengthExample = 2 := by
  change Ring.ord (Polynomial ℝ) realLengthPolynomial = 2
  have hq : Irreducible (Polynomial.X ^ 2 + 1 : Polynomial ℝ) := by
    have h := X_pow_sub_C_irreducible_of_prime (K := ℝ) (p := 2) (by decide)
        (a := (-1 : ℝ)) (by
          intro b hb
          have hnonneg : 0 ≤ b ^ 2 := sq_nonneg b
          rw [hb] at hnonneg
          norm_num at hnonneg)
    simpa [sub_eq_add_neg] using h
  have hfactor : realLengthPolynomial =
      (Polynomial.X ^ 2 + 1) * (Polynomial.X ^ 2 + 1) := by
    unfold realLengthPolynomial
    rw [show Polynomial.C (2 : ℝ) = (2 : Polynomial ℝ) by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, map_add, map_one]
      norm_num]
    ring
  have hnd : (Polynomial.X ^ 2 + 1 : Polynomial ℝ) ∈
      nonZeroDivisors (Polynomial ℝ) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr <| by
      simpa using (Polynomial.X_pow_add_C_ne_zero (R := ℝ) (by decide) (1 : ℝ))
  rw [hfactor, Ring.ord_mul' (R := Polynomial ℝ) hnd,
    Ring.ord_of_irreducible hq]
  norm_num
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
    (planeOriginIdeal k).IsPrime := by sorry
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

/-- The finite normal-form calculation for the local-plane quotient.  The
source computation gives nine successive simple factors; recording it as a
composition series keeps the localization visible in the module being
filtered and gives the proving stage a checked interface for the missing
normal-form calculation.
-/
theorem planeEquationQuotient_composition_series (k : Type u) [Field k] :
    ∃ s : CompositionSeries (Submodule (planeLocalRing k) (planeEquationQuotient k)),
      s.head = ⊥ ∧ s.last = ⊤ ∧ s.length = 9 := by sorry
theorem local_plane_equation_quotient_length (k : Type u) [Field k] :
    Module.length (planeLocalRing k) (planeEquationQuotient k) = 9 := by sorry
