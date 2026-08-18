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
    Module.length (Polynomial ℝ) realLengthExample = 2 := by
  change Ring.ord (Polynomial ℝ) realLengthPolynomial = 2
  unfold realLengthPolynomial
  rw [show (Polynomial.X ^ 4 + Polynomial.C (2 : ℝ) * Polynomial.X ^ 2 + 1 : Polynomial ℝ) =
      (Polynomial.X ^ 2 + 1) ^ 2 by rw [Polynomial.C_ofNat]; ring]
  have hirr : Irreducible (Polynomial.X ^ 2 + 1 : Polynomial ℝ) := by
    simpa [sub_eq_add_neg] using
      (X_pow_sub_C_irreducible_of_prime (K := ℝ) (p := 2) Nat.prime_two
        (a := (-1 : ℝ)) (by
          intro b hb
          have hnonneg : (0 : ℝ) ≤ b ^ 2 := sq_nonneg b
          rw [hb] at hnonneg
          exact (not_lt_of_ge hnonneg) neg_one_lt_zero))
  rw [Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hirr.ne_zero),
    Ring.ord_of_irreducible hirr]
  norm_num

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

/-- The finite normal-form calculation for the local-plane quotient.  The
source computation gives nine successive simple factors; recording it as a
composition series keeps the localization visible in the module being
filtered and gives the proving stage a checked interface for the missing
normal-form calculation.
-/
theorem planeEquationQuotient_composition_series (k : Type u) [Field k] :
    ∃ s : CompositionSeries (Submodule (planeLocalRing k) (planeEquationQuotient k)),
      s.head = ⊥ ∧ s.last = ⊤ ∧ s.length = 9 := by
  let A := planeLocalRing k
  let I := planeEquationIdeal k
  have hx : planeX k ∈ IsLocalRing.maximalIdeal A := by
    change algebraMap (planePolynomialRing k) A
      (MvPolynomial.X (0 : Fin 2)) ∈ IsLocalRing.maximalIdeal A
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff
      (S := A) (I := planeOriginIdeal k)]
    exact Ideal.subset_span (by simp [planeOriginIdeal])
  have hy : planeY k ∈ IsLocalRing.maximalIdeal A := by
    change algebraMap (planePolynomialRing k) A
      (MvPolynomial.X (1 : Fin 2)) ∈ IsLocalRing.maximalIdeal A
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff
      (S := A) (I := planeOriginIdeal k)]
    exact Ideal.subset_span (by simp [planeOriginIdeal])
  have hunit : IsUnit (1 - (-planeX k ^ 32964 * planeY k)) := by
    have hpow : planeX k ^ 32964 ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.maximalIdeal A).pow_mem_of_mem hx 32964 (by norm_num)
    have hprod : planeY k * planeX k ^ 32964 ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.maximalIdeal A).mul_mem_left _ hpow
    have hneg : -planeX k ^ 32964 * planeY k ∈ IsLocalRing.maximalIdeal A := by
      convert (IsLocalRing.maximalIdeal A).neg_mem hprod using 1 <;> ring
    have hneg' : -planeX k ^ 32964 * planeY k ∈
        IsLocalRing.maximalIdeal (planeLocalRing k) := hneg
    have hnon : -planeX k ^ 32964 * planeY k ∈
        (nonunits (planeLocalRing k) : Set (planeLocalRing k)) :=
      (IsLocalRing.mem_maximalIdeal (R := planeLocalRing k) _).mp hneg'
    have hu : IsUnit (1 - (-planeX k ^ 32964 * planeY k)) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      (R := planeLocalRing k) (-planeX k ^ 32964 * planeY k)
      hnon
    exact hu
  have hx3 : planeX k ^ 3 ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).pow_mem_of_mem hx 3 (by norm_num)
  have hy3 : planeY k ^ 3 ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).pow_mem_of_mem hy 3 (by norm_num)
  have hx999 : planeX k ^ 999 ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).pow_mem_of_mem hx 999 (by norm_num)
  have hxy : planeX k ^ 2 * planeY k ^ 2 ∈ IsLocalRing.maximalIdeal A := by
    exact (IsLocalRing.maximalIdeal A).mul_mem_left _
      ((IsLocalRing.maximalIdeal A).pow_mem_of_mem hy 2 (by norm_num))
  have hy100 : planeY k ^ 100 ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).pow_mem_of_mem hy 100 (by norm_num)
  have hfmax : planeEquationF k ∈ IsLocalRing.maximalIdeal A := by
    exact (IsLocalRing.maximalIdeal A).add_mem
      ((IsLocalRing.maximalIdeal A).add_mem hx3 hxy) hy100
  have hgmax : planeEquationG k ∈ IsLocalRing.maximalIdeal A := by
    exact (IsLocalRing.maximalIdeal A).sub_mem hy3 hx999
  have hIle : I ≤ IsLocalRing.maximalIdeal A := by
    apply Ideal.span_le.2
    intro z hz
    rcases hz with (rfl | rfl) <;> assumption
  have hIne : I ≠ ⊤ := ne_top_of_le_ne_top
    (Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal A)) hIle
  let Q := A ⧸ I
  let q : A →+* Q := Ideal.Quotient.mk I
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hIne
  letI : IsLocalRing Q := IsLocalRing.of_surjective' q q.surjective
  have hqF : q (planeEquationF k) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp [planeEquationIdeal])
  have hqG : q (planeEquationG k) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp [planeEquationIdeal])
  let qX : Q := q (planeX k)
  let qY : Q := q (planeY k)
  have hG : qY ^ 3 = qX ^ 999 := by
    have h := hqG
    simp only [planeEquationG, map_sub, qX, qY] at h
    exact sub_eq_zero.mp h
  have hF : qX ^ 3 + qX ^ 2 * qY ^ 2 + qY ^ 100 = 0 := by
    have h := hqF
    simp only [planeEquationF, map_add, map_mul, qX, qY] at h
    exact h
  have hY100 : qY ^ 100 = qX ^ 32967 * qY := by
    calc
      qY ^ 100 = qY * (qY ^ 3) ^ 33 := by ring
      _ = qY * (qX ^ 999) ^ 33 := by rw [hG]
      _ = qY * qX ^ (999 * 33) := by rw [pow_mul]
      _ = qX ^ 32967 * qY := by ring
  have hrel : qX ^ 3 * (1 - (-qX ^ 32964 * qY)) + qX ^ 2 * qY ^ 2 = 0 := by
    calc
      qX ^ 3 * (1 - (-qX ^ 32964 * qY)) + qX ^ 2 * qY ^ 2 =
          qX ^ 3 + qX ^ 2 * qY ^ 2 + qX ^ 3 * qX ^ 32964 * qY := by ring
      _ = qX ^ 3 + qX ^ 2 * qY ^ 2 + qX ^ 32967 * qY := by
        rw [← pow_add]
      _ = qX ^ 3 + qX ^ 2 * qY ^ 2 + qY ^ 100 := by rw [hY100]
      _ = 0 := hF
  have huQ : IsUnit (q (1 - (-planeX k ^ 32964 * planeY k))) := hunit.map q
  let U : Qˣ := huQ.unit
  have hU : (U : Q) = 1 - (-qX ^ 32964 * qY) := by
    change (huQ.unit : Q) = q (1 - (-planeX k ^ 32964 * planeY k))
    exact huQ.unit_spec.symm
  let v : Q := (↑(U⁻¹) : Q)
  have hUv : (1 - (-qX ^ 32964 * qY)) * v = 1 := by
    rw [← hU]
    exact U.mul_inv
  let a : Q := (-qY ^ 2) * v
  have hXa : qX ^ 3 = qX ^ 2 * a := by
    have hfirst : qX ^ 3 * (1 - (-qX ^ 32964 * qY)) = -(qX ^ 2 * qY ^ 2) :=
      eq_neg_of_add_eq_zero_left hrel
    calc
      qX ^ 3 = qX ^ 3 * 1 := by ring
      _ = qX ^ 3 * ((1 - (-qX ^ 32964 * qY)) * v) := by rw [hUv]
      _ = (qX ^ 3 * (1 - (-qX ^ 32964 * qY))) * v := by ring
      _ = (-(qX ^ 2 * qY ^ 2)) * v := by rw [hfirst]
      _ = qX ^ 2 * a := by dsimp [a]; ring
  have ha333 : a ^ 333 = qY ^ 666 * ((-v) ^ 333) := by
    change ((-(qY ^ 2)) * v) ^ 333 = qY ^ 666 * ((-v) ^ 333)
    calc
      ((-(qY ^ 2)) * v) ^ 333 = (-(qY ^ 2)) ^ 333 * v ^ 333 :=
        mul_pow _ _ _
      _ = qY ^ 666 * ((-v) ^ 333) := by
        have hodd : Odd (333 : ℕ) := by
          exact ⟨166, by norm_num⟩
        have hnegY : (-(qY ^ 2)) ^ 333 = -(qY ^ 666) := by
          calc
            (-(qY ^ 2)) ^ 333 = -(qY ^ 2) ^ 333 := hodd.neg_pow _
            _ = -(qY ^ 666) := by rw [(pow_mul qY 2 333).symm]
        have hnegv : (-v) ^ 333 = -(v ^ 333) := by
          exact hodd.neg_pow v
        rw [hnegY, hnegv]
        ring
  have hY3zero : qY ^ 3 = 0 := by
    have h999 : qX ^ 999 = (qX ^ 2 * a) ^ 333 := by
      rw [← hXa]
      rw [← pow_mul]
    have hcycle : qY ^ 3 = qY ^ 3 * (qX ^ 666 * qY ^ 663 * ((-v) ^ 333)) := by
      calc
        qY ^ 3 = qX ^ 999 := hG
        _ = (qX ^ 2 * a) ^ 333 := h999
        _ = qX ^ 666 * a ^ 333 := by
          calc
            (qX ^ 2 * a) ^ 333 = (qX ^ 2) ^ 333 * a ^ 333 :=
              mul_pow _ _ _
            _ = qX ^ 666 * a ^ 333 := by
              rw [(pow_mul qX 2 333).symm]
        _ = qY ^ 3 * (qX ^ 666 * qY ^ 663 * ((-v) ^ 333)) := by
          rw [ha333]
          have hYexp : qY ^ 666 = qY ^ 3 * qY ^ 663 := by
            rw [← pow_add]
          rw [hYexp]
          ring
    have hCmem : qX ^ 666 * qY ^ 663 * ((-v) ^ 333) ∈ IsLocalRing.maximalIdeal Q := by
      have hyQ : qY ∈ IsLocalRing.maximalIdeal Q := by
        apply (IsLocalRing.mem_maximalIdeal (R := Q) qY).mpr
        intro hqunit
        obtain ⟨b, hb⟩ := q.surjective (↑(hqunit.unit⁻¹) : Q)
        have hybq : q (planeY k * b) = 1 := by
          calc
            q (planeY k * b) = q (planeY k) * q b := map_mul q _ _
            _ = qY * q b := by rfl
            _ = (↑hqunit.unit : Q) * ↑(hqunit.unit⁻¹) := by
              rw [hqunit.unit_spec, hb]
            _ = 1 := by simp
        have hybI : planeY k * b - 1 ∈ I := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          rw [map_sub, hybq, map_one]
          simp
        have hybmax : planeY k * b - 1 ∈ IsLocalRing.maximalIdeal A :=
          hIle hybI
        have hnegmax : 1 - planeY k * b ∈ IsLocalRing.maximalIdeal A := by
          have := (IsLocalRing.maximalIdeal A).neg_mem hybmax
          convert this using 1 <;> ring
        have hprod : IsUnit (planeY k * b) := by
          have hnon :=
            (IsLocalRing.mem_maximalIdeal (R := A) (1 - planeY k * b)).mp hnegmax
          simpa only [sub_sub_cancel] using
            IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
              (R := A) (1 - planeY k * b) hnon
        have hyunit : IsUnit (planeY k) :=
          (Commute.all (planeY k) b).isUnit_mul_iff.mp hprod |>.1
        exact (IsLocalRing.mem_maximalIdeal (R := A) (planeY k)).mp hy hyunit
      have hxyQ : qX ^ 666 * qY ^ 663 ∈ IsLocalRing.maximalIdeal Q := by
        exact (IsLocalRing.maximalIdeal Q).mul_mem_left _
          ((IsLocalRing.maximalIdeal Q).pow_mem_of_mem hyQ 663 (by norm_num))
      exact (IsLocalRing.maximalIdeal Q).mul_mem_right _ hxyQ
    have hCunit : IsUnit (1 - (qX ^ 666 * qY ^ 663 * ((-v) ^ 333))) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
        (R := Q) (qX ^ 666 * qY ^ 663 * ((-v) ^ 333))
        ((IsLocalRing.mem_maximalIdeal (R := Q)
          (qX ^ 666 * qY ^ 663 * ((-v) ^ 333))).mp hCmem)
    have hzero :
        (1 - (qX ^ 666 * qY ^ 663 * ((-v) ^ 333))) * qY ^ 3 = 0 := by
      have hdiff :
          qY ^ 3 - (qX ^ 666 * qY ^ 663 * ((-v) ^ 333)) * qY ^ 3 =
            qY ^ 3 * (qX ^ 666 * qY ^ 663 * ((-v) ^ 333)) -
              (qX ^ 666 * qY ^ 663 * ((-v) ^ 333)) * qY ^ 3 :=
        congrArg
          (fun z : Q => z - (qX ^ 666 * qY ^ 663 * ((-v) ^ 333)) * qY ^ 3)
          hcycle
      calc
        (1 - (qX ^ 666 * qY ^ 663 * ((-v) ^ 333))) * qY ^ 3 =
            qY ^ 3 - (qX ^ 666 * qY ^ 663 * ((-v) ^ 333)) * qY ^ 3 := by
              rw [sub_mul, one_mul]
        _ = qY ^ 3 * (qX ^ 666 * qY ^ 663 * ((-v) ^ 333)) -
              (qX ^ 666 * qY ^ 663 * ((-v) ^ 333)) * qY ^ 3 := hdiff
        _ = 0 := by ring
    apply hCunit.mul_left_cancel
    simpa only [mul_zero] using hzero
  sorry

/-- The local intersection quotient has length nine. -/
theorem local_plane_equation_quotient_length (k : Type u) [Field k] :
    Module.length (planeLocalRing k) (planeEquationQuotient k) = 9 := by
  obtain ⟨s, hs_head, hs_last, hs_length⟩ :=
    planeEquationQuotient_composition_series k
  rw [← Module.length_compositionSeries s hs_head hs_last, hs_length]
  norm_num

end

end Formalization.Books.Exercises.Unit09
