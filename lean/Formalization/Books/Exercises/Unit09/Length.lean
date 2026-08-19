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
  let R := planePolynomialRing k
  let x₀ : R := MvPolynomial.X (0 : Fin 2)
  let y₀ : R := MvPolynomial.X (1 : Fin 2)
  let K : Ideal R := Ideal.span {x₀ ^ 3 + x₀ ^ 2 * y₀ ^ 2, y₀ ^ 3}
  let b : Fin 9 → R :=
    ![1, x₀, x₀ ^ 2, y₀, x₀ * y₀, x₀ ^ 2 * y₀, y₀ ^ 2,
      x₀ * y₀ ^ 2, x₀ ^ 2 * y₀ ^ 2]
  have hxrel : x₀ ^ 3 + x₀ ^ 2 * y₀ ^ 2 ∈ K := by
    exact Ideal.subset_span (by simp [K])
  have hyrel : y₀ ^ 3 ∈ K := by
    exact Ideal.subset_span (by simp [K])
  have hKpow : (planeOriginIdeal k) ^ 5 ≤ K := by
    rw [MvPolynomial.pow_idealOfVars_eq_span]
    apply Ideal.span_le.2
    rintro _ ⟨m, hm, rfl⟩
    change MvPolynomial.monomial m 1 ∈ K
    change Finsupp.degree m = 5 at hm
    have hmdeg : m 0 + m 1 = 5 := by
      simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hm
    have hmform : m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
      ext i
      fin_cases i <;> simp
    by_cases hmy : 3 ≤ m 1
    · have hle : Finsupp.single 1 3 ≤ m := by
        intro i
        fin_cases i <;> simp [hmy]
      have hadd : m - Finsupp.single 1 3 + Finsupp.single 1 3 = m :=
        tsub_add_cancel_of_le hle
      rw [← hadd, MvPolynomial.monomial_add_single]
      simpa only [map_one, mul_one, ← MvPolynomial.X_pow_eq_monomial] using
        K.mul_mem_left _ hyrel
    · have hmy' : m 1 ≤ 2 := by omega
      have hmx : 3 ≤ m 0 := by omega
      have hle : Finsupp.single 0 3 ≤ m := by
        intro i
        fin_cases i <;> simp [hmx]
      have hm0 : m 0 = 5 - m 1 := by omega
      have hbase : x₀ ^ (m 0) * y₀ ^ (m 1) = MvPolynomial.monomial m 1 := by
        have hmon : MvPolynomial.monomial m 1 =
            x₀ ^ (m 0) * y₀ ^ (m 1) := by
          calc
            MvPolynomial.monomial m 1 =
                MvPolynomial.monomial (Finsupp.single 0 (m 0)) 1 *
                  MvPolynomial.X 1 ^ (m 1) := by
              conv_lhs => rw [hmform, MvPolynomial.monomial_add_single]
            _ = x₀ ^ (m 0) * y₀ ^ (m 1) := by
              rw [← MvPolynomial.X_pow_eq_monomial]
        exact hmon.symm
      rw [← hbase]
      change x₀ ^ m 0 * y₀ ^ m 1 ∈ K
      interval_cases hmy'' : m 1
      · have hm0' : m 0 = 5 := by omega
        have h₁ : x₀ ^ 5 + x₀ ^ 4 * y₀ ^ 2 ∈ K := by
          convert K.mul_mem_left (x₀ ^ 2) hxrel using 1 <;> ring
        have h₂ : x₀ ^ 4 * y₀ ^ 2 + x₀ ^ 3 * y₀ ^ 4 ∈ K := by
          convert K.mul_mem_left (x₀ * y₀ ^ 2) hxrel using 1 <;> ring
        have h₃ : x₀ ^ 3 * y₀ ^ 4 ∈ K := by
          convert K.mul_mem_left (x₀ ^ 3 * y₀) hyrel using 1 <;> ring
        have := K.sub_mem h₁ h₂
        have hgoal := K.add_mem (by convert this using 1 <;> ring) h₃
        have hfinal : x₀ ^ 5 ∈ K := by
          convert hgoal using 1 <;> ring
        simpa [hm0', hmy''] using hfinal
      · have hm0' : m 0 = 4 := by omega
        have h₁ : x₀ ^ 4 * y₀ + x₀ ^ 3 * y₀ ^ 3 ∈ K := by
          convert K.mul_mem_left (x₀ * y₀) hxrel using 1 <;> ring
        have h₂ : x₀ ^ 3 * y₀ ^ 3 ∈ K := by
          convert K.mul_mem_left (x₀ ^ 3) hyrel using 1 <;> ring
        have hgoal := K.sub_mem (by convert h₁ using 1 <;> ring) h₂
        have hfinal : x₀ ^ 4 * y₀ ∈ K := by
          convert hgoal using 1 <;> ring
        simpa [hm0', hmy''] using hfinal
      · have hm0' : m 0 = 3 := by omega
        have h₁ : x₀ ^ 3 * y₀ ^ 2 + x₀ ^ 2 * y₀ ^ 4 ∈ K := by
          convert K.mul_mem_left (y₀ ^ 2) hxrel using 1 <;> ring
        have h₂ : x₀ ^ 2 * y₀ ^ 4 ∈ K := by
          convert K.mul_mem_left (x₀ ^ 2 * y₀) hyrel using 1 <;> ring
        have hgoal := K.sub_mem (by convert h₁ using 1 <;> ring) h₂
        have hfinal : x₀ ^ 3 * y₀ ^ 2 ∈ K := by
          convert hgoal using 1 <;> ring
        simpa [hm0', hmy''] using hfinal
  have hnormal : ∀ p : R, ∃ c : Fin 9 → k,
      p - ∑ i, c i • b i ∈ K := by
    let W : Submodule k R := Submodule.span k (Set.range b) ⊔ K.restrictScalars k
    have hB (i : Fin 9) : b i ∈ W :=
      Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
    have hK (z : R) (hz : z ∈ K) : z ∈ W := Submodule.mem_sup_right hz
    have hkx3 : x₀ ^ 3 ∈ W := by
      have h := hK (x₀ ^ 3 + x₀ ^ 2 * y₀ ^ 2) hxrel
      have hh := W.sub_mem h (hB 8)
      convert hh using 1 <;> simp [b] <;> ring
    have hkx3y : x₀ ^ 3 * y₀ ∈ W := by
      have h₁ : x₀ ^ 3 * y₀ + x₀ ^ 2 * y₀ ^ 3 ∈ K := by
        convert K.mul_mem_left y₀ hxrel using 1 <;> ring
      have h₂ : x₀ ^ 2 * y₀ ^ 3 ∈ K := K.mul_mem_left (x₀ ^ 2) hyrel
      have hh := W.sub_mem (hK _ h₁) (hK _ h₂)
      convert hh using 1 <;> ring
    have hkx3y2 : x₀ ^ 3 * y₀ ^ 2 ∈ W := by
      have h₁ : x₀ ^ 3 * y₀ ^ 2 + x₀ ^ 2 * y₀ ^ 4 ∈ K := by
        convert K.mul_mem_left (y₀ ^ 2) hxrel using 1 <;> ring
      have h₂ : x₀ ^ 2 * y₀ ^ 4 ∈ K := by
        have hh := K.mul_mem_left (x₀ ^ 2 * y₀) hyrel
        convert hh using 1 <;> ring
      have hh := W.sub_mem (hK _ h₁) (hK _ h₂)
      convert hh using 1 <;> ring
    have hkx2y3 : x₀ ^ 2 * y₀ ^ 3 ∈ W := by
      have hh := K.mul_mem_left (x₀ ^ 2) hyrel
      exact hK _ hh
    have hky3 : y₀ ^ 3 ∈ W := hK _ hyrel
    have hkxy3 : x₀ * y₀ ^ 3 ∈ W := by
      have hh := K.mul_mem_left x₀ hyrel
      exact hK _ hh
    have hBmul : ∀ i j, b i * MvPolynomial.X j ∈ W := by
      intro i j
      fin_cases i
      · fin_cases j
        · convert hB 1 using 1 <;> simp [b, x₀] <;> ring
        · convert hB 3 using 1 <;> simp [b, y₀] <;> ring
      · fin_cases j
        · convert hB 2 using 1 <;> simp [b, x₀] <;> ring
        · convert hB 4 using 1 <;> simp [b, x₀, y₀] <;> ring
      · fin_cases j
        · convert hkx3 using 1 <;> simp [b, x₀] <;> ring
        · convert hB 5 using 1 <;> simp [b, x₀, y₀] <;> ring
      · fin_cases j
        · convert hB 4 using 1 <;> simp [b, x₀, y₀] <;> ring
        · convert hB 6 using 1 <;> simp [b, y₀] <;> ring
      · fin_cases j
        · convert hB 5 using 1 <;> simp [b, x₀, y₀] <;> ring
        · convert hB 7 using 1 <;> simp [b, x₀, y₀] <;> ring
      · fin_cases j
        · convert hkx3y using 1 <;> simp [b, x₀, y₀] <;> ring
        · convert hB 8 using 1 <;> simp [b, x₀, y₀] <;> ring
      · fin_cases j
        · convert hB 7 using 1 <;> simp [b, x₀, y₀] <;> ring
        · convert hky3 using 1 <;> simp [b, x₀, y₀] <;> ring
      · fin_cases j
        · convert hB 8 using 1 <;> simp [b, x₀, y₀] <;> ring
        · convert hkxy3 using 1 <;> simp [b, x₀, y₀] <;> ring
      · fin_cases j
        · convert hkx3y2 using 1 <;> simp [b, x₀, y₀] <;> ring
        · convert hkx2y3 using 1 <;> simp [b, x₀, y₀] <;> ring
    have hmul : ∀ {p : R} (j : Fin 2), p ∈ W →
        p * MvPolynomial.X j ∈ W := by
      intro p j hp
      rcases Submodule.mem_sup.mp hp with ⟨u, hu, v, hv, rfl⟩
      have hu' : u * MvPolynomial.X j ∈ W := by
        refine Submodule.span_induction (p := fun z _ => z * MvPolynomial.X j ∈ W)
          ?_ ?_ ?_ ?_ hu
        · intro z hz
          rcases hz with ⟨i, rfl⟩
          exact hBmul i j
        · simp [W]
        · intro z z' hz hz' hzz hzz'
          simpa [add_mul] using W.add_mem hzz hzz'
        · intro a z hz hzz
          simpa [smul_eq_mul, mul_assoc] using W.smul_mem a hzz
      have hv' : v * MvPolynomial.X j ∈ W := by
        have hvK : v ∈ K := hv
        have hmulK : v * MvPolynomial.X j ∈ K := by
          have hh := Ideal.mul_mem_left K (MvPolynomial.X j) hvK
          convert hh using 1 <;> ring
        exact hK _ hmulK
      simpa [add_mul] using W.add_mem hu' hv'
    have hWmem : ∀ p : R, p ∈ W := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
          have h := W.smul_mem a (hB 0)
          have hac : (MvPolynomial.C a : R) = algebraMap k R a :=
            (congrArg (fun f : k →+* R => f a)
              (MvPolynomial.algebraMap_eq k (Fin 2))).symm
          rw [hac]
          simpa [b, Algebra.smul_def] using h
      | add p q hp hq => exact W.add_mem hp hq
      | mul_X p j hp => exact hmul j hp
    have hW : W = ⊤ := by
      apply top_unique
      intro p _
      exact hWmem p
    intro p
    have hp : p ∈ W := by rw [hW]; trivial
    rcases Submodule.mem_sup.mp hp with ⟨u, hu, v, hv, rfl⟩
    rcases (Submodule.mem_span_range_iff_exists_fun k).mp hu with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hv' : v ∈ K := hv
    rw [hc]
    convert hv' using 1 <;> ring
  let Q₀ := R ⧸ K
  let r₀ : R →+* Q₀ := Ideal.Quotient.mk K
  have hzero : ∀ c : Fin 9 → k,
      (∑ i, c i • b i) ∈ K → ∀ i, c i = 0 := by
    intro c hc i
    rcases (Ideal.mem_span_pair.mp hc) with ⟨p, q, hpq⟩
    let e : Fin 9 → Fin 2 →₀ ℕ :=
      ![0, Finsupp.single 0 1, Finsupp.single 0 2, Finsupp.single 1 1,
        Finsupp.single 0 1 + Finsupp.single 1 1,
        Finsupp.single 0 2 + Finsupp.single 1 1, Finsupp.single 1 2,
        Finsupp.single 0 1 + Finsupp.single 1 2,
        Finsupp.single 0 2 + Finsupp.single 1 2]
    have hAlg : algebraMap k R = MvPolynomial.C :=
      MvPolynomial.algebraMap_eq k (Fin 2)
    have hCmul (m : Fin 2 →₀ ℕ) (a : k) (p : R) :
        MvPolynomial.coeff m (MvPolynomial.C a * p) =
          a * MvPolynomial.coeff m p :=
      MvPolynomial.coeff_C_mul m a p
    have hmon (m n : Fin 2 →₀ ℕ) (a : k) :
        MvPolynomial.coeff m (MvPolynomial.monomial n a) =
          if n = m then a else 0 :=
      MvPolynomial.coeff_monomial m n a
    have hX (j : Fin 2) :
        (MvPolynomial.X j : R) = MvPolynomial.monomial (Finsupp.single j 1) 1 := by
      rw [← MvPolynomial.X_pow_eq_monomial]
      simp
    have hxmon : x₀ = MvPolynomial.monomial (Finsupp.single 0 1) 1 := by
      simpa [x₀] using hX 0
    have hymon : y₀ = MvPolynomial.monomial (Finsupp.single 1 1) 1 := by
      simpa [y₀] using hX 1
    have hpow0 : x₀ ^ 2 = MvPolynomial.monomial (Finsupp.single 0 2) 1 := by
      rw [hxmon, MvPolynomial.monomial_pow]
      have hsum : (2 : ℕ) • Finsupp.single (0 : Fin 2) 1 =
          Finsupp.single 0 2 := by
        ext j
        fin_cases j <;> simp
      rw [hsum]
      simp
    have hpow1 : y₀ ^ 2 = MvPolynomial.monomial (Finsupp.single 1 2) 1 := by
      rw [hymon, MvPolynomial.monomial_pow]
      have hsum : (2 : ℕ) • Finsupp.single (1 : Fin 2) 1 =
          Finsupp.single 1 2 := by
        ext j
        fin_cases j <;> simp
      rw [hsum]
      simp
    have hmul01 : x₀ * y₀ =
        MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
      rw [hxmon, hymon, MvPolynomial.monomial_mul]
      simp
    have hmul21 : x₀ ^ 2 * y₀ =
        MvPolynomial.monomial (Finsupp.single 0 2 + Finsupp.single 1 1) 1 := by
      rw [hpow0, hymon, MvPolynomial.monomial_mul]
      simp
    have hmul12 : x₀ * y₀ ^ 2 =
        MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 2) 1 := by
      rw [hxmon, hpow1, MvPolynomial.monomial_mul]
      simp
    have hmul22 : x₀ ^ 2 * y₀ ^ 2 =
        MvPolynomial.monomial (Finsupp.single 0 2 + Finsupp.single 1 2) 1 := by
      rw [hpow0, hpow1, MvPolynomial.monomial_mul]
      simp
    have hbmon : ∀ j : Fin 9, b j = MvPolynomial.monomial (e j) 1 := by
      intro j
      fin_cases j
      · simp [b, e]
      · simpa [b, e] using hxmon
      · simpa [b, e] using hpow0
      · simpa [b, e] using hymon
      · simpa [b, e] using hmul01
      · simpa [b, e] using hmul21
      · simpa [b, e] using hpow1
      · simpa [b, e] using hmul12
      · simpa [b, e] using hmul22
    have hR : ∀ j : Fin 9,
        MvPolynomial.coeff (e j) (∑ i, c i • b i) = c j := by
      intro j
      have hsum (m : Fin 2 →₀ ℕ) :
          MvPolynomial.coeff m (∑ i, c i • b i) =
            ∑ i, c i * MvPolynomial.coeff m (b i) := by
        simp only [Algebra.smul_def, hAlg]
        let L : R →+ k :=
          { toFun := MvPolynomial.coeff m
            map_zero' := MvPolynomial.coeff_zero m
            map_add' := by
              intro z w
              exact MvPolynomial.coeff_add m z w }
        change L (∑ i, MvPolynomial.C (c i) * b i) = _
        rw [map_sum]
        change (∑ i, MvPolynomial.coeff m (MvPolynomial.C (c i) * b i)) = _
        simp_rw [hCmul]
      rw [hsum]
      simp_rw [hbmon, hmon]
      fin_cases j <;>
        simp [e, Fin.sum_univ_succ, Finsupp.ext_iff]
    have hR0 : MvPolynomial.coeff (0 : Fin 2 →₀ ℕ) (∑ i, c i • b i) = c 0 := by
      simpa [e] using hR 0
    have hR1 : MvPolynomial.coeff (Finsupp.single 0 1) (∑ i, c i • b i) = c 1 := by
      simpa [e] using hR 1
    have hR2 : MvPolynomial.coeff (Finsupp.single 0 2) (∑ i, c i • b i) = c 2 := by
      simpa [e] using hR 2
    have hR3 : MvPolynomial.coeff (Finsupp.single 1 1) (∑ i, c i • b i) = c 3 := by
      simpa [e] using hR 3
    have hR4 : MvPolynomial.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)
        (∑ i, c i • b i) = c 4 := by
      simpa [e] using hR 4
    have hR5 : MvPolynomial.coeff (Finsupp.single 0 2 + Finsupp.single 1 1)
        (∑ i, c i • b i) = c 5 := by
      simpa [e] using hR 5
    have hR6 : MvPolynomial.coeff (Finsupp.single 1 2) (∑ i, c i • b i) = c 6 := by
      simpa [e] using hR 6
    have hR7 : MvPolynomial.coeff (Finsupp.single 0 1 + Finsupp.single 1 2)
        (∑ i, c i • b i) = c 7 := by
      simpa [e] using hR 7
    have hR8 : MvPolynomial.coeff (Finsupp.single 0 2 + Finsupp.single 1 2)
        (∑ i, c i • b i) = c 8 := by
      simpa [e] using hR 8
    fin_cases i
    · have h := congrArg (MvPolynomial.coeff (0 : Fin 2 →₀ ℕ)) hpq
      rw [MvPolynomial.coeff_add] at h
      rw [mul_add] at h
      repeat rw [MvPolynomial.coeff_add] at h
      rw [hR0] at h
      simp_rw [MvPolynomial.X_pow_eq_monomial] at h
      simp [MvPolynomial.coeff_mul_monomial'] at h
      simp [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] at h
      simpa using h
    · have h := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) hpq
      rw [MvPolynomial.coeff_add] at h
      rw [mul_add] at h
      simp_rw [MvPolynomial.coeff_add] at h
      rw [hR1] at h
      simp [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] at h
      simpa [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] using h
    · have h := congrArg (MvPolynomial.coeff (Finsupp.single 0 2)) hpq
      rw [MvPolynomial.coeff_add] at h
      rw [mul_add] at h
      simp_rw [MvPolynomial.coeff_add] at h
      rw [hR2] at h
      simp [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] at h
      simpa [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] using h
    · have h := congrArg (MvPolynomial.coeff (Finsupp.single 1 1)) hpq
      rw [MvPolynomial.coeff_add] at h
      rw [mul_add] at h
      simp_rw [MvPolynomial.coeff_add] at h
      rw [hR3] at h
      simp [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] at h
      simpa [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] using h
    · have h := congrArg (MvPolynomial.coeff
          (Finsupp.single 0 1 + Finsupp.single 1 1)) hpq
      rw [MvPolynomial.coeff_add] at h
      rw [mul_add] at h
      simp_rw [MvPolynomial.coeff_add] at h
      rw [hR4] at h
      simp [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] at h
      simpa [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] using h
    · have h := congrArg (MvPolynomial.coeff
          (Finsupp.single 0 2 + Finsupp.single 1 1)) hpq
      rw [MvPolynomial.coeff_add] at h
      rw [mul_add] at h
      simp_rw [MvPolynomial.coeff_add] at h
      rw [hR5] at h
      simp [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] at h
      simpa [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] using h
    · have h := congrArg (MvPolynomial.coeff (Finsupp.single 1 2)) hpq
      rw [MvPolynomial.coeff_add] at h
      rw [mul_add] at h
      simp_rw [MvPolynomial.coeff_add] at h
      rw [hR6] at h
      simp [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] at h
      simpa [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] using h
    · have h := congrArg (MvPolynomial.coeff
          (Finsupp.single 0 1 + Finsupp.single 1 2)) hpq
      rw [MvPolynomial.coeff_add] at h
      rw [mul_add] at h
      simp_rw [MvPolynomial.coeff_add] at h
      rw [hR7] at h
      simp [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] at h
      simpa [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] using h
    · have h := congrArg (fun z : R =>
          MvPolynomial.coeff (Finsupp.single 0 2 + Finsupp.single 1 2) z -
            MvPolynomial.coeff (Finsupp.single 0 3) z) hpq
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add] at h
      rw [mul_add] at h
      simp_rw [MvPolynomial.coeff_add] at h
      simp [b, x₀, y₀, MvPolynomial.coeff_add, MvPolynomial.coeff_mul_monomial',
        MvPolynomial.X_pow_eq_monomial, Fin.sum_univ_succ] at h
      simpa using h
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
