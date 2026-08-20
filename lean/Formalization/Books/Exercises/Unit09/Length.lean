import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Nilpotent.Basic
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
    (planeOriginIdeal k).IsPrime := by
  change (MvPolynomial.idealOfVars (Fin 2) k).IsPrime
  apply Ideal.isPrime_iff.mpr
  constructor
  · intro h
    have hmem : (1 : MvPolynomial (Fin 2) k) ∈ MvPolynomial.idealOfVars (Fin 2) k := by
      simp [h]
    have hmem' : (1 : MvPolynomial (Fin 2) k) ∈
        MvPolynomial.idealOfVars (Fin 2) k ^ 1 := by simpa using hmem
    rw [MvPolynomial.mem_pow_idealOfVars_iff' 1] at hmem'
    have hz := hmem' 0 (by simp)
    simp at hz
  · intro p q hpq
    have hmem_iff (r : MvPolynomial (Fin 2) k) :
        r ∈ MvPolynomial.idealOfVars (Fin 2) k ↔
          ∀ x, Finsupp.degree x < 1 → MvPolynomial.coeff x r = 0 := by
      simpa only [pow_one] using (MvPolynomial.mem_pow_idealOfVars_iff' 1 r)
    have hpq' := (hmem_iff (p * q)).mp hpq
    by_cases hp : MvPolynomial.coeff 0 p = 0
    · left
      apply (hmem_iff p).mpr
      intro x hx
      have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (by omega)
      simpa [hx0] using hp
    · right
      apply (hmem_iff q).mpr
      intro x hx
      have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (by omega)
      subst x
      have hprod := hpq' 0 (by simp)
      have hprod' : MvPolynomial.coeff 0 p * MvPolynomial.coeff 0 q = 0 := by
        simpa [MvPolynomial.coeff_mul] using hprod
      simpa using (mul_eq_zero.mp hprod').resolve_left hp
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

/-! The finite normal algebra used to read off the nine normal forms. -/

def planeNormalYPolynomial (k : Type u) [Field k] : Polynomial k :=
  Polynomial.X ^ 3

abbrev planeNormalYAlgebra (k : Type u) [Field k] : Type u :=
  AdjoinRoot (planeNormalYPolynomial k)

def planeNormalY (k : Type u) [Field k] : planeNormalYAlgebra k :=
  AdjoinRoot.root (planeNormalYPolynomial k)

def planeNormalXPolynomial (k : Type u) [Field k] :
    Polynomial (planeNormalYAlgebra k) :=
  Polynomial.X ^ 3 + Polynomial.C (planeNormalY k ^ 2) * Polynomial.X ^ 2

abbrev planeNormalAlgebra (k : Type u) [Field k] : Type u :=
  AdjoinRoot (planeNormalXPolynomial k)

def planeNormalX (k : Type u) [Field k] : planeNormalAlgebra k :=
  AdjoinRoot.root (planeNormalXPolynomial k)

def planeNormalYInAlgebra (k : Type u) [Field k] : planeNormalAlgebra k :=
  algebraMap (planeNormalYAlgebra k) (planeNormalAlgebra k) (planeNormalY k)

instance planeNormalYAlgebra_nontrivial (k : Type u) [Field k] :
    Nontrivial (planeNormalYAlgebra k) := by
  apply AdjoinRoot.nontrivial (planeNormalYPolynomial k)
  simp [planeNormalYPolynomial]

theorem planeNormalY_cube (k : Type u) [Field k] : planeNormalY k ^ 3 = 0 := by
  have hroot := AdjoinRoot.eval₂_root (planeNormalYPolynomial k)
  change AdjoinRoot.root (planeNormalYPolynomial k) ^ 3 = 0
  calc
    AdjoinRoot.root (planeNormalYPolynomial k) ^ 3 =
        Polynomial.eval₂ (AdjoinRoot.of (planeNormalYPolynomial k))
          (AdjoinRoot.root (planeNormalYPolynomial k)) (Polynomial.X ^ 3) := by
      simp
    _ = Polynomial.eval₂ (AdjoinRoot.of (planeNormalYPolynomial k))
          (AdjoinRoot.root (planeNormalYPolynomial k)) (planeNormalYPolynomial k) := by
      rw [planeNormalYPolynomial]
    _ = 0 := hroot

theorem planeNormalYPolynomial_monic (k : Type u) [Field k] :
    (planeNormalYPolynomial k).Monic := by
  simp [planeNormalYPolynomial]

theorem planeNormalYPolynomial_natDegree (k : Type u) [Field k] :
    (planeNormalYPolynomial k).natDegree = 3 := by
  simp [planeNormalYPolynomial]

theorem planeNormalXPolynomial_monic (k : Type u) [Field k] :
    (planeNormalXPolynomial k).Monic := by
  apply Polynomial.monic_X_pow_add
  exact (Polynomial.degree_C_mul_X_pow_le 2 (planeNormalY k ^ 2)).trans_lt (by norm_num)

theorem planeNormalXPolynomial_natDegree (k : Type u) [Field k] :
    (planeNormalXPolynomial k).natDegree = 3 := by
  unfold planeNormalXPolynomial
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · exact (Polynomial.natDegree_C_mul_X_pow_le (planeNormalY k ^ 2) 2).trans_lt
      (by norm_num)

instance planeNormalAlgebra_nontrivial (k : Type u) [Field k] :
    Nontrivial (planeNormalAlgebra k) := Ideal.Quotient.nontrivial_iff.mpr <| by
  intro htop
  have hpunit : IsUnit (planeNormalXPolynomial k) :=
    Ideal.span_singleton_eq_top.mp htop
  have hpone : planeNormalXPolynomial k = 1 :=
    (planeNormalXPolynomial_monic k).eq_one_of_isUnit hpunit
  have hdegree := congrArg Polynomial.natDegree hpone
  rw [planeNormalXPolynomial_natDegree, Polynomial.natDegree_one] at hdegree
  omega

theorem planeNormalYInAlgebra_cube (k : Type u) [Field k] :
    planeNormalYInAlgebra k ^ 3 = 0 := by
  unfold planeNormalYInAlgebra
  rw [← map_pow, planeNormalY_cube, map_zero]

theorem planeNormalX_relation (k : Type u) [Field k] :
    planeNormalX k ^ 3 +
      planeNormalX k ^ 2 * planeNormalYInAlgebra k ^ 2 = 0 := by
  have hroot := AdjoinRoot.eval₂_root (planeNormalXPolynomial k)
  have heval : Polynomial.eval₂
      (AdjoinRoot.of (planeNormalXPolynomial k)) (planeNormalX k)
        (planeNormalXPolynomial k) =
      planeNormalX k ^ 3 +
        algebraMap (planeNormalYAlgebra k) (planeNormalAlgebra k)
          (planeNormalY k ^ 2) * planeNormalX k ^ 2 := by
    calc
      Polynomial.eval₂ (AdjoinRoot.of (planeNormalXPolynomial k)) (planeNormalX k)
          (planeNormalXPolynomial k) =
          Polynomial.eval₂ (AdjoinRoot.of (planeNormalXPolynomial k)) (planeNormalX k)
            (Polynomial.X ^ 3 +
              Polynomial.C (planeNormalY k ^ 2) * Polynomial.X ^ 2) := rfl
      _ = planeNormalX k ^ 3 +
          algebraMap (planeNormalYAlgebra k) (planeNormalAlgebra k)
            (planeNormalY k ^ 2) * planeNormalX k ^ 2 := by
        rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
          Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, AdjoinRoot.algebraMap_eq]
  have hy2 : planeNormalYInAlgebra k ^ 2 =
      algebraMap (planeNormalYAlgebra k) (planeNormalAlgebra k) (planeNormalY k ^ 2) := by
    unfold planeNormalYInAlgebra
    exact (map_pow _ _ 2).symm
  calc
    planeNormalX k ^ 3 + planeNormalX k ^ 2 * planeNormalYInAlgebra k ^ 2 =
        planeNormalX k ^ 3 + planeNormalX k ^ 2 *
          algebraMap (planeNormalYAlgebra k) (planeNormalAlgebra k)
            (planeNormalY k ^ 2) :=
      congrArg (fun z : planeNormalAlgebra k =>
        planeNormalX k ^ 3 + planeNormalX k ^ 2 * z) hy2
    _ = planeNormalX k ^ 3 +
        algebraMap (planeNormalYAlgebra k) (planeNormalAlgebra k)
          (planeNormalY k ^ 2) * planeNormalX k ^ 2 := by ring
    _ = Polynomial.eval₂ (AdjoinRoot.of (planeNormalXPolynomial k))
        (planeNormalX k) (planeNormalXPolynomial k) := heval.symm
    _ = 0 := hroot

theorem planeNormalX_fourth (k : Type u) [Field k] : planeNormalX k ^ 4 = 0 := by
  have hx3 : planeNormalX k ^ 3 =
      -(planeNormalX k ^ 2 * planeNormalYInAlgebra k ^ 2) :=
    eq_neg_of_add_eq_zero_left (planeNormalX_relation k)
  calc
    planeNormalX k ^ 4 = planeNormalX k * planeNormalX k ^ 3 := by ring
    _ = planeNormalX k * (-(planeNormalX k ^ 2 * planeNormalYInAlgebra k ^ 2)) :=
      congrArg (fun z : planeNormalAlgebra k => planeNormalX k * z) hx3
    _ = -(planeNormalX k ^ 3 * planeNormalYInAlgebra k ^ 2) := by ring
    _ = -(-(planeNormalX k ^ 2 * planeNormalYInAlgebra k ^ 2) *
        planeNormalYInAlgebra k ^ 2) :=
      congrArg (fun z : planeNormalAlgebra k =>
        -(z * planeNormalYInAlgebra k ^ 2)) hx3
    _ = planeNormalX k ^ 2 * planeNormalYInAlgebra k ^ 4 := by ring
    _ = 0 := by
      rw [show planeNormalYInAlgebra k ^ 4 =
        planeNormalYInAlgebra k ^ 3 * planeNormalYInAlgebra k by ring,
        planeNormalYInAlgebra_cube, zero_mul, mul_zero]

def planeNormalCoordinates (k : Type u) [Field k] : Fin 2 → planeNormalAlgebra k :=
  fun i => if i = 0 then planeNormalX k else planeNormalYInAlgebra k

def planeNormalEval (k : Type u) [Field k] :
    planePolynomialRing k →+* planeNormalAlgebra k :=
  MvPolynomial.eval₂Hom (algebraMap k (planeNormalAlgebra k)) (planeNormalCoordinates k)

@[simp] theorem planeNormalEval_X_zero (k : Type u) [Field k] :
    planeNormalEval k (MvPolynomial.X (0 : Fin 2)) = planeNormalX k := by
  simp [planeNormalEval, planeNormalCoordinates]

@[simp] theorem planeNormalEval_X_one (k : Type u) [Field k] :
    planeNormalEval k (MvPolynomial.X (1 : Fin 2)) = planeNormalYInAlgebra k := by
  simp [planeNormalEval, planeNormalCoordinates]

theorem planeNormalEval_isUnit (k : Type u) [Field k]
    (s : (planeOriginIdeal k).primeCompl) : IsUnit (planeNormalEval k s) := by
  let c : k := MvPolynomial.coeff 0 (s : planePolynomialRing k)
  let p0 : planePolynomialRing k := (s : planePolynomialRing k) - MvPolynomial.C c
  have hc : c ≠ 0 := by
    intro hc
    have hs_mem_pow : (s : planePolynomialRing k) ∈ planeOriginIdeal k ^ 1 := by
      apply (MvPolynomial.mem_pow_idealOfVars_iff' 1 _).2
      intro d hd
      have hd0 : d = 0 := Finsupp.degree_eq_zero_iff d |>.mp (by omega)
      subst d
      simpa [c, hc]
    have hs_mem : (s : planePolynomialRing k) ∈ planeOriginIdeal k := by
      simpa only [pow_one] using hs_mem_pow
    exact (Ideal.mem_primeCompl_iff.mp s.property) hs_mem
  have hp0 : p0 ∈ planeOriginIdeal k := by
    have hp0pow : p0 ∈ planeOriginIdeal k ^ 1 := by
      apply (MvPolynomial.mem_pow_idealOfVars_iff' 1 _).2
      intro d hd
      have hd0 : d = 0 := Finsupp.degree_eq_zero_iff d |>.mp (by omega)
      subst d
      simp [p0, c]
    simpa only [pow_one] using hp0pow
  have hmap : (planeOriginIdeal k).map (planeNormalEval k) ≤
      Ideal.span {planeNormalX k, planeNormalYInAlgebra k} := by
    rw [Ideal.map_le_iff_le_comap]
    rw [show planeOriginIdeal k = Ideal.span (Set.range MvPolynomial.X) by rfl,
      Ideal.span_le]
    rintro z ⟨i, rfl⟩
    change planeNormalEval k (MvPolynomial.X i) ∈
      Ideal.span {planeNormalX k, planeNormalYInAlgebra k}
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · rw [planeNormalEval_X_zero]
      exact Ideal.subset_span (by simp)
    · rw [planeNormalEval_X_one]
      exact Ideal.subset_span (by simp)
  have hp0map : planeNormalEval k p0 ∈
      Ideal.span {planeNormalX k, planeNormalYInAlgebra k} :=
    hmap (Ideal.mem_map_of_mem (planeNormalEval k) hp0)
  obtain ⟨r, t, hrt⟩ := Ideal.mem_span_pair.mp hp0map
  have hnil : IsNilpotent (planeNormalEval k p0) := by
    rw [← hrt]
    exact Commute.isNilpotent_add (Commute.all _ _)
      ((Commute.all _ _).isNilpotent_mul_left ⟨4, planeNormalX_fourth k⟩)
      ((Commute.all _ _).isNilpotent_mul_left ⟨3, planeNormalYInAlgebra_cube k⟩)
  have hcunit : IsUnit (algebraMap k (planeNormalAlgebra k) c) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap k (planeNormalAlgebra k))
  have hsplit : planeNormalEval k s =
      algebraMap k (planeNormalAlgebra k) c + planeNormalEval k p0 := by
    dsimp [p0]
    rw [map_sub]
    have hC : planeNormalEval k (MvPolynomial.C c) =
        algebraMap k (planeNormalAlgebra k) c := by
      simp [planeNormalEval]
    rw [hC]
    ring
  rw [hsplit]
  exact hnil.isUnit_add_left_of_commute hcunit (Commute.all _ _)

def planeNormalFromLocal (k : Type u) [Field k] :
    planeLocalRing k →+* planeNormalAlgebra k :=
  IsLocalization.lift (planeNormalEval_isUnit k)

@[simp] theorem planeNormalFromLocal_X (k : Type u) [Field k] :
    planeNormalFromLocal k (planeX k) = planeNormalX k := by
  change IsLocalization.lift (planeNormalEval_isUnit k)
    (algebraMap (planePolynomialRing k) (planeLocalRing k)
      (MvPolynomial.X (0 : Fin 2))) = planeNormalX k
  exact (IsLocalization.lift_eq (planeNormalEval_isUnit k) _).trans
    (planeNormalEval_X_zero k)

@[simp] theorem planeNormalFromLocal_Y (k : Type u) [Field k] :
    planeNormalFromLocal k (planeY k) = planeNormalYInAlgebra k := by
  change IsLocalization.lift (planeNormalEval_isUnit k)
    (algebraMap (planePolynomialRing k) (planeLocalRing k)
      (MvPolynomial.X (1 : Fin 2))) = planeNormalYInAlgebra k
  exact (IsLocalization.lift_eq (planeNormalEval_isUnit k) _).trans
    (planeNormalEval_X_one k)

theorem planeEquationIdeal_le_normal_ker (k : Type u) [Field k] :
    planeEquationIdeal k ≤ RingHom.ker (planeNormalFromLocal k) := by
  rw [planeEquationIdeal, Ideal.span_le]
  rintro z (rfl | rfl)
  · change planeNormalFromLocal k (planeEquationF k) = 0
    unfold planeEquationF
    rw [map_add, map_add, map_pow, map_mul, map_pow, map_pow, map_pow,
      planeNormalFromLocal_X, planeNormalFromLocal_Y]
    have hy100 : planeNormalYInAlgebra k ^ 100 = 0 := by
      calc
        planeNormalYInAlgebra k ^ 100 =
            (planeNormalYInAlgebra k ^ 3) ^ 33 * planeNormalYInAlgebra k := by ring
        _ = 0 := by rw [planeNormalYInAlgebra_cube]; simp
    rw [hy100, add_zero]
    exact planeNormalX_relation k
  · change planeNormalFromLocal k (planeEquationG k) = 0
    unfold planeEquationG
    rw [map_sub, map_pow, map_pow, planeNormalFromLocal_X, planeNormalFromLocal_Y,
      planeNormalYInAlgebra_cube]
    rw [show planeNormalX k ^ 999 = planeNormalX k ^ 4 * planeNormalX k ^ 995 by ring,
      planeNormalX_fourth, zero_mul, sub_zero]

def planeNormalFromQuotient (k : Type u) [Field k] :
    planeEquationQuotient k →+* planeNormalAlgebra k :=
  Ideal.Quotient.lift (planeEquationIdeal k) (planeNormalFromLocal k)
    (planeEquationIdeal_le_normal_ker k)

def planeNormalFromQuotientAlgHom (k : Type u) [Field k] :
    planeEquationQuotient k →ₐ[k] planeNormalAlgebra k :=
  { planeNormalFromQuotient k with
    commutes' := by
      intro c
      change planeNormalFromLocal k (algebraMap k (planeLocalRing k) c) =
        algebraMap k (planeNormalAlgebra k) c
      change IsLocalization.lift (planeNormalEval_isUnit k)
        (algebraMap (planePolynomialRing k) (planeLocalRing k) (MvPolynomial.C c)) =
          algebraMap k (planeNormalAlgebra k) c
      calc
        IsLocalization.lift (planeNormalEval_isUnit k)
            (algebraMap (planePolynomialRing k) (planeLocalRing k) (MvPolynomial.C c)) =
            planeNormalEval k (MvPolynomial.C c) :=
          IsLocalization.lift_eq (planeNormalEval_isUnit k) _
        _ = algebraMap k (planeNormalAlgebra k) c := by simp [planeNormalEval] }

noncomputable def planeNormalYBasis (k : Type u) [Field k] :
    Module.Basis (Fin 3) k (planeNormalYAlgebra k) :=
  (AdjoinRoot.powerBasis' (planeNormalYPolynomial_monic k)).basis.reindex
    (finCongr (planeNormalYPolynomial_natDegree k))

noncomputable def planeNormalXBasis (k : Type u) [Field k] :
    Module.Basis (Fin 3) (planeNormalYAlgebra k) (planeNormalAlgebra k) :=
  (AdjoinRoot.powerBasis' (planeNormalXPolynomial_monic k)).basis.reindex
    (finCongr (planeNormalXPolynomial_natDegree k))

/-- The nine independent normal forms, in the order
`1,x,x²,y,xy,x²y,y²,xy²,x²y²`. -/
noncomputable def planeNormalBasis (k : Type u) [Field k] :
    Module.Basis (Fin 9) k (planeNormalAlgebra k) :=
  ((planeNormalYBasis k).smulTower (planeNormalXBasis k)).reindex
    finProdFinEquiv

set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem planeNormalYBasis_apply (k : Type u) [Field k] (i : Fin 3) :
    planeNormalYBasis k i = planeNormalY k ^ (i : ℕ) := by
  rw [planeNormalYBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast]
  change planeNormalY k ^ (i : ℕ) = planeNormalY k ^ (i : ℕ)
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem planeNormalXBasis_apply (k : Type u) [Field k] (i : Fin 3) :
    planeNormalXBasis k i = planeNormalX k ^ (i : ℕ) := by
  rw [planeNormalXBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast]
  change planeNormalX k ^ (i : ℕ) = planeNormalX k ^ (i : ℕ)
  rfl

@[simp] theorem planeNormalBasis_apply (k : Type u) [Field k] (i : Fin 9) :
    planeNormalBasis k i =
      planeNormalX k ^ (i.val % 3) * planeNormalYInAlgebra k ^ (i.val / 3) := by
  fin_cases i <;>
    simp [planeNormalBasis, Module.Basis.reindex_apply, Module.Basis.smulTower_apply,
      finProdFinEquiv, planeNormalYInAlgebra, Algebra.smul_def] <;> ring

noncomputable def planeNormalSocleBasis (k : Type u) [Field k] :
    Module.Basis (Fin 9) k (planeNormalAlgebra k) :=
  (planeNormalBasis k).reindex Fin.revPerm

@[simp] theorem planeNormalSocleBasis_apply (k : Type u) [Field k] (i : Fin 9) :
    planeNormalSocleBasis k i = planeNormalBasis k (Fin.rev i) := by
  simp [planeNormalSocleBasis, Module.Basis.reindex_apply, Fin.revPerm_symm]

def planeNormalSocleXDegree (i : Fin 9) : ℕ := (8 - i.val) % 3

def planeNormalSocleYDegree (i : Fin 9) : ℕ := (8 - i.val) / 3

def planeNormalSocleMulVanishes (i j : Fin 9) : Bool :=
  let a := planeNormalSocleXDegree i + planeNormalSocleXDegree j
  let b := planeNormalSocleYDegree i + planeNormalSocleYDegree j
  decide (4 ≤ a ∨ 3 ≤ b ∨ (a = 3 ∧ 1 ≤ b))

def planeNormalSocleMulCoeff (k : Type u) [Field k] (i j : Fin 9) : k :=
  if planeNormalSocleMulVanishes i j then 0
  else if planeNormalSocleXDegree i + planeNormalSocleXDegree j = 3 then -1 else 1

def planeNormalSocleMulIndex (i j : Fin 9) : Fin 9 :=
  if planeNormalSocleMulVanishes i j then 0
  else if planeNormalSocleXDegree i + planeNormalSocleXDegree j = 3 then 0
  else ⟨(8 - ((planeNormalSocleXDegree i + planeNormalSocleXDegree j) +
      3 * (planeNormalSocleYDegree i + planeNormalSocleYDegree j))) % 9,
      Nat.mod_lt _ (by norm_num)⟩

private theorem planeNormalX_cube_eq (k : Type u) [Field k] :
    planeNormalX k ^ 3 = -(planeNormalX k ^ 2 * planeNormalYInAlgebra k ^ 2) :=
  eq_neg_of_add_eq_zero_left (planeNormalX_relation k)

private theorem planeNormalYInAlgebra_fourth (k : Type u) [Field k] :
    planeNormalYInAlgebra k ^ 4 = 0 := by
  calc
    planeNormalYInAlgebra k ^ 4 =
        planeNormalYInAlgebra k ^ 3 * planeNormalYInAlgebra k := by ring
    _ = 0 := by rw [planeNormalYInAlgebra_cube, zero_mul]

private theorem planeNormalSocleBasis_mul_zero (k : Type u) [Field k] (j : Fin 9) :
    planeNormalSocleBasis k 0 * planeNormalSocleBasis k j =
      planeNormalSocleMulCoeff k 0 j • planeNormalSocleBasis k
        (planeNormalSocleMulIndex 0 j) := by
  fin_cases j <;> simp [planeNormalSocleMulIndex, planeNormalSocleMulCoeff,
    planeNormalSocleMulVanishes, planeNormalSocleXDegree, planeNormalSocleYDegree,
    planeNormalSocleBasis_apply, planeNormalBasis_apply, Algebra.smul_def] <;>
    ring_nf <;> simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth] <;> ring_nf <;>
    simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth]

private theorem planeNormalSocleBasis_mul_one (k : Type u) [Field k] (j : Fin 9) :
    planeNormalSocleBasis k 1 * planeNormalSocleBasis k j =
      planeNormalSocleMulCoeff k 1 j • planeNormalSocleBasis k
        (planeNormalSocleMulIndex 1 j) := by
  fin_cases j <;> simp [planeNormalSocleMulIndex, planeNormalSocleMulCoeff,
    planeNormalSocleMulVanishes, planeNormalSocleXDegree, planeNormalSocleYDegree,
    planeNormalSocleBasis_apply, planeNormalBasis_apply, Algebra.smul_def] <;>
    ring_nf <;> simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth] <;> ring_nf <;>
    simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth]

private theorem planeNormalSocleBasis_mul_two (k : Type u) [Field k] (j : Fin 9) :
    planeNormalSocleBasis k 2 * planeNormalSocleBasis k j =
      planeNormalSocleMulCoeff k 2 j • planeNormalSocleBasis k
        (planeNormalSocleMulIndex 2 j) := by
  fin_cases j <;> simp [planeNormalSocleMulIndex, planeNormalSocleMulCoeff,
    planeNormalSocleMulVanishes, planeNormalSocleXDegree, planeNormalSocleYDegree,
    planeNormalSocleBasis_apply, planeNormalBasis_apply, Algebra.smul_def] <;>
    ring_nf <;> simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth] <;> ring_nf <;>
    simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth]

private theorem planeNormalSocleBasis_mul_three (k : Type u) [Field k] (j : Fin 9) :
    planeNormalSocleBasis k 3 * planeNormalSocleBasis k j =
      planeNormalSocleMulCoeff k 3 j • planeNormalSocleBasis k
        (planeNormalSocleMulIndex 3 j) := by
  fin_cases j <;> simp [planeNormalSocleMulIndex, planeNormalSocleMulCoeff,
    planeNormalSocleMulVanishes, planeNormalSocleXDegree, planeNormalSocleYDegree,
    planeNormalSocleBasis_apply, planeNormalBasis_apply, Algebra.smul_def] <;>
    ring_nf <;> simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth] <;> ring_nf <;>
    simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth]

private theorem planeNormalSocleBasis_mul_four (k : Type u) [Field k] (j : Fin 9) :
    planeNormalSocleBasis k 4 * planeNormalSocleBasis k j =
      planeNormalSocleMulCoeff k 4 j • planeNormalSocleBasis k
        (planeNormalSocleMulIndex 4 j) := by
  fin_cases j <;> simp [planeNormalSocleMulIndex, planeNormalSocleMulCoeff,
    planeNormalSocleMulVanishes, planeNormalSocleXDegree, planeNormalSocleYDegree,
    planeNormalSocleBasis_apply, planeNormalBasis_apply, Algebra.smul_def] <;>
    ring_nf <;> simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth] <;> ring_nf <;>
    simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth]

private theorem planeNormalSocleBasis_mul_five (k : Type u) [Field k] (j : Fin 9) :
    planeNormalSocleBasis k 5 * planeNormalSocleBasis k j =
      planeNormalSocleMulCoeff k 5 j • planeNormalSocleBasis k
        (planeNormalSocleMulIndex 5 j) := by
  fin_cases j <;> simp [planeNormalSocleMulIndex, planeNormalSocleMulCoeff,
    planeNormalSocleMulVanishes, planeNormalSocleXDegree, planeNormalSocleYDegree,
    planeNormalSocleBasis_apply, planeNormalBasis_apply, Algebra.smul_def] <;>
    ring_nf <;> simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth] <;> ring_nf <;>
    simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth]

private theorem planeNormalSocleBasis_mul_six (k : Type u) [Field k] (j : Fin 9) :
    planeNormalSocleBasis k 6 * planeNormalSocleBasis k j =
      planeNormalSocleMulCoeff k 6 j • planeNormalSocleBasis k
        (planeNormalSocleMulIndex 6 j) := by
  fin_cases j <;> simp [planeNormalSocleMulIndex, planeNormalSocleMulCoeff,
    planeNormalSocleMulVanishes, planeNormalSocleXDegree, planeNormalSocleYDegree,
    planeNormalSocleBasis_apply, planeNormalBasis_apply, Algebra.smul_def] <;>
    ring_nf <;> simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth] <;> ring_nf <;>
    simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth]

private theorem planeNormalSocleBasis_mul_seven (k : Type u) [Field k] (j : Fin 9) :
    planeNormalSocleBasis k 7 * planeNormalSocleBasis k j =
      planeNormalSocleMulCoeff k 7 j • planeNormalSocleBasis k
        (planeNormalSocleMulIndex 7 j) := by
  fin_cases j <;> simp [planeNormalSocleMulIndex, planeNormalSocleMulCoeff,
    planeNormalSocleMulVanishes, planeNormalSocleXDegree, planeNormalSocleYDegree,
    planeNormalSocleBasis_apply, planeNormalBasis_apply, Algebra.smul_def] <;>
    ring_nf <;> simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth] <;> ring_nf <;>
    simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth]

private theorem planeNormalSocleBasis_mul_eight (k : Type u) [Field k] (j : Fin 9) :
    planeNormalSocleBasis k 8 * planeNormalSocleBasis k j =
      planeNormalSocleMulCoeff k 8 j • planeNormalSocleBasis k
        (planeNormalSocleMulIndex 8 j) := by
  fin_cases j <;> simp [planeNormalSocleMulIndex, planeNormalSocleMulCoeff,
    planeNormalSocleMulVanishes, planeNormalSocleXDegree, planeNormalSocleYDegree,
    planeNormalSocleBasis_apply, planeNormalBasis_apply, Algebra.smul_def] <;>
    ring_nf <;> simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth] <;> ring_nf <;>
    simp [planeNormalX_cube_eq, planeNormalX_fourth,
      planeNormalYInAlgebra_cube, planeNormalYInAlgebra_fourth]

theorem planeNormalSocleBasis_mul (k : Type u) [Field k] (i j : Fin 9) :
    planeNormalSocleMulIndex i j ≤ j ∧
      planeNormalSocleBasis k i * planeNormalSocleBasis k j =
        planeNormalSocleMulCoeff k i j •
          planeNormalSocleBasis k (planeNormalSocleMulIndex i j) := by
  constructor
  · native_decide +revert
  · fin_cases i
    · exact planeNormalSocleBasis_mul_zero k j
    · exact planeNormalSocleBasis_mul_one k j
    · exact planeNormalSocleBasis_mul_two k j
    · exact planeNormalSocleBasis_mul_three k j
    · exact planeNormalSocleBasis_mul_four k j
    · exact planeNormalSocleBasis_mul_five k j
    · exact planeNormalSocleBasis_mul_six k j
    · exact planeNormalSocleBasis_mul_seven k j
    · exact planeNormalSocleBasis_mul_eight k j

theorem planeNormalSocleFlag_mul_mem (k : Type u) [Field k]
    (i : Fin 10) (a z : planeNormalAlgebra k)
    (hz : z ∈ (planeNormalSocleBasis k).flag i) :
    a * z ∈ (planeNormalSocleBasis k).flag i := by
  let b := planeNormalSocleBasis k
  change z ∈ b.flag i at hz
  change a * z ∈ b.flag i
  rw [Module.Basis.flag] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨j, hj, rfl⟩ := hz
      have ha : a ∈ Submodule.span k (Set.range b) := by
        rw [b.span_eq]
        exact Submodule.mem_top
      induction ha using Submodule.span_induction with
      | mem w hw =>
          obtain ⟨l, rfl⟩ := hw
          obtain ⟨hlt, hmul⟩ := planeNormalSocleBasis_mul k l j
          rw [hmul]
          exact (b.flag i).smul_mem _ <| b.self_mem_flag <|
            lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hlt) hj
      | zero => simpa using (b.flag i).zero_mem
      | add u v _ _ hu hv =>
          simpa [add_mul] using (b.flag i).add_mem hu hv
      | smul c u _ hu =>
          simpa [Algebra.smul_def, mul_assoc] using (b.flag i).smul_mem c hu
  | zero => simpa using (b.flag i).zero_mem
  | add u v _ _ hu hv =>
      simpa [mul_add] using (b.flag i).add_mem hu hv
  | smul c u _ hu =>
      have hc := (b.flag i).smul_mem c hu
      rw [Algebra.smul_def] at hc ⊢
      convert hc using 1 <;> ring

/-- The reverse normal-form flag, regarded as a flag of ideals of the normal algebra. -/
noncomputable def planeNormalFlagSubmodule (k : Type u) [Field k] (i : Fin 10) :
    Submodule (planeNormalAlgebra k) (planeNormalAlgebra k) where
  carrier := (planeNormalSocleBasis k).flag i
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' a z hz := by
    simpa [Algebra.smul_def] using planeNormalSocleFlag_mul_mem k i a z hz

theorem planeNormalFlagSubmodule_restrictScalars (k : Type u) [Field k] (i : Fin 10) :
    (planeNormalFlagSubmodule k i).restrictScalars k =
      (planeNormalSocleBasis k).flag i := by
  ext z
  rfl

theorem planeNormalFlagSubmodule_covBy (k : Type u) [Field k] (i : Fin 9) :
    planeNormalFlagSubmodule k i.castSucc ⋖ planeNormalFlagSubmodule k i.succ := by
  apply CovBy.of_image
    (Submodule.restrictScalarsEmbedding k (planeNormalAlgebra k) (planeNormalAlgebra k))
  change (planeNormalFlagSubmodule k i.castSucc).restrictScalars k ⋖
    (planeNormalFlagSubmodule k i.succ).restrictScalars k
  rw [planeNormalFlagSubmodule_restrictScalars,
    planeNormalFlagSubmodule_restrictScalars]
  exact (planeNormalSocleBasis k).flag_covBy i

theorem basisMap_flag {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (e : V ≃ₗ[K] W) (i : Fin (n + 1)) :
    (b.map e).flag i = (b.flag i).map e.toLinearMap := by
  simp only [Module.Basis.flag, Submodule.map_span, Set.image_image]
  rw [Module.Basis.coe_map]
  rfl

def planeEquationQuotientMap (k : Type u) [Field k] :
    planeLocalRing k →+* planeEquationQuotient k :=
  Ideal.Quotient.mk (planeEquationIdeal k)

def planeEquationQuotientX (k : Type u) [Field k] : planeEquationQuotient k :=
  planeEquationQuotientMap k (planeX k)

def planeEquationQuotientY (k : Type u) [Field k] : planeEquationQuotient k :=
  planeEquationQuotientMap k (planeY k)

set_option maxHeartbeats 1200000 in
/-- The localization calculation that reduces the two original equations to
the finite normal-form relations. -/
theorem planeEquationQuotient_normal_relations (k : Type u) [Field k] :
    planeEquationQuotientX k ^ 4 = 0 ∧
      planeEquationQuotientY k ^ 3 = 0 ∧
      planeEquationQuotientX k ^ 3 +
        planeEquationQuotientX k ^ 2 * planeEquationQuotientY k ^ 2 = 0 := by
  classical
  let R := planeLocalRing k
  let I := planeEquationIdeal k
  let Q := planeEquationQuotient k
  let q : R →+* Q := planeEquationQuotientMap k
  let x : Q := planeEquationQuotientX k
  let y : Q := planeEquationQuotientY k
  have hxR : planeX k ∈ IsLocalRing.maximalIdeal R := by
    change algebraMap (planePolynomialRing k) R (MvPolynomial.X (0 : Fin 2)) ∈ _
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      R (planeOriginIdeal k) _).2 (Ideal.subset_span (Set.mem_range_self _))
  have hyR : planeY k ∈ IsLocalRing.maximalIdeal R := by
    change algebraMap (planePolynomialRing k) R (MvPolynomial.X (1 : Fin 2)) ∈ _
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      R (planeOriginIdeal k) _).2 (Ideal.subset_span (Set.mem_range_self _))
  have hpowR (z : R) (hz : z ∈ IsLocalRing.maximalIdeal R)
      (n : ℕ) (hn : 0 < n) : z ^ n ∈ IsLocalRing.maximalIdeal R := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [pow_succ]
    exact (IsLocalRing.maximalIdeal R).mul_mem_left _ hz
  have hImax : I ≤ IsLocalRing.maximalIdeal R := by
    rw [show I = Ideal.span {planeEquationF k, planeEquationG k} by rfl,
      Ideal.span_le]
    rintro z (rfl | rfl)
    · unfold planeEquationF
      exact (IsLocalRing.maximalIdeal R).add_mem
        ((IsLocalRing.maximalIdeal R).add_mem
          (hpowR _ hxR 3 (by norm_num))
          (by
            have hm := (IsLocalRing.maximalIdeal R).mul_mem_left (planeY k ^ 2)
              (hpowR _ hxR 2 (by norm_num))
            convert hm using 1 <;> ring))
        (hpowR _ hyR 100 (by norm_num))
    · unfold planeEquationG
      exact (IsLocalRing.maximalIdeal R).sub_mem
        (hpowR _ hyR 3 (by norm_num)) (hpowR _ hxR 999 (by norm_num))
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top
    (inferInstance : (IsLocalRing.maximalIdeal R).IsMaximal).ne_top hImax
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI
  letI : IsLocalRing Q :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  letI : IsLocalHom q :=
    IsLocalHom.of_surjective (R := R) (S := Q) q
      (Ideal.Quotient.mk_surjective (I := I))
  have hx : x ∈ IsLocalRing.maximalIdeal Q := by
    rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
    intro hxu
    change IsUnit (q (planeX k)) at hxu
    have hxRu : IsUnit (planeX k) :=
      IsLocalHom.map_nonunit (f := q) (planeX k) hxu
    have hxRn : ¬IsUnit (planeX k) := _root_.mem_nonunits_iff.mp
      ((IsLocalRing.mem_maximalIdeal (R := R) (planeX k)).mp hxR)
    exact hxRn hxRu
  have hy : y ∈ IsLocalRing.maximalIdeal Q := by
    rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
    intro hyu
    change IsUnit (q (planeY k)) at hyu
    have hyRu : IsUnit (planeY k) :=
      IsLocalHom.map_nonunit (f := q) (planeY k) hyu
    have hyRn : ¬IsUnit (planeY k) := _root_.mem_nonunits_iff.mp
      ((IsLocalRing.mem_maximalIdeal (R := R) (planeY k)).mp hyR)
    exact hyRn hyRu
  have hf : x ^ 3 + x ^ 2 * y ^ 2 + y ^ 100 = 0 := by
    change planeEquationQuotientMap k (planeEquationF k) = 0
    unfold planeEquationQuotientMap
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hg : y ^ 3 = x ^ 999 := by
    apply sub_eq_zero.mp
    change planeEquationQuotientMap k (planeEquationG k) = 0
    unfold planeEquationQuotientMap
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hy100 : y ^ 100 = x ^ 32967 * y := by
    calc
      y ^ 100 = (y ^ 3) ^ 33 * y := by ring
      _ = (x ^ 999) ^ 33 * y := by rw [hg]
      _ = x ^ 32967 * y := by ring
  have hshort : x ^ 3 + x ^ 2 * y ^ 2 + x ^ 32967 * y = 0 := by
    simpa only [hy100] using hf
  have hcomb :
      x ^ 4 + x ^ 32968 * y - x ^ 2 * y ^ 4 - x ^ 32967 * y ^ 3 = 0 := by
    calc
      x ^ 4 + x ^ 32968 * y - x ^ 2 * y ^ 4 - x ^ 32967 * y ^ 3 =
          x * (x ^ 3 + x ^ 2 * y ^ 2 + x ^ 32967 * y) -
            y ^ 2 * (x ^ 3 + x ^ 2 * y ^ 2 + x ^ 32967 * y) := by ring
      _ = 0 := by rw [hshort]; ring
  have hy4 : y ^ 4 = x ^ 999 * y := by
    calc
      y ^ 4 = y ^ 3 * y := by ring
      _ = x ^ 999 * y := by rw [hg]
  let a : Q := x ^ 997 * y - x ^ 32964 * y + x ^ 33962
  let unitFactor : Q := 1 - a
  have hfactor : x ^ 4 * unitFactor = 0 := by
    calc
      x ^ 4 * unitFactor =
          x ^ 4 + x ^ 32968 * y - x ^ 1001 * y - x ^ 33966 := by
            dsimp [unitFactor, a]
            ring
      _ = x ^ 4 + x ^ 32968 * y - x ^ 2 * y ^ 4 - x ^ 32967 * y ^ 3 := by
            rw [hy4, hg]
            ring
      _ = 0 := hcomb
  have hxpow (n : ℕ) (hn : 0 < n) : x ^ n ∈ IsLocalRing.maximalIdeal Q := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [pow_succ]
    exact (IsLocalRing.maximalIdeal Q).mul_mem_left _ hx
  have ha : a ∈ IsLocalRing.maximalIdeal Q := by
    dsimp [a]
    exact (IsLocalRing.maximalIdeal Q).add_mem
      ((IsLocalRing.maximalIdeal Q).sub_mem
        ((IsLocalRing.maximalIdeal Q).mul_mem_left _ hy)
        ((IsLocalRing.maximalIdeal Q).mul_mem_left _ hy))
      (hxpow 33962 (by norm_num))
  have ha' : a ∈ nonunits Q := by
    rw [_root_.mem_nonunits_iff]
    simpa only [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff] using ha
  have hunit : IsUnit unitFactor :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a ha'
  have hx4 : x ^ 4 = 0 := by
    calc
      x ^ 4 = x ^ 4 * unitFactor * (↑(hunit.unit⁻¹) : Q) := by
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
      _ = 0 := by rw [hfactor, zero_mul]
  have hy3 : y ^ 3 = 0 := by
    rw [hg, show x ^ 999 = x ^ 4 * x ^ 995 by ring, hx4, zero_mul]
  have hxrel : x ^ 3 + x ^ 2 * y ^ 2 = 0 := by
    have hy100zero : y ^ 100 = 0 := by
      calc
        y ^ 100 = (y ^ 3) ^ 33 * y := by ring
        _ = 0 := by rw [hy3]; simp
    simpa only [hy100zero, add_zero] using hf
  exact ⟨hx4, hy3, hxrel⟩

noncomputable def planeNormalYToQuotient (k : Type u) [Field k] :
    planeNormalYAlgebra k →ₐ[k] planeEquationQuotient k :=
  AdjoinRoot.liftAlgHom (planeNormalYPolynomial k)
    (Algebra.ofId k (planeEquationQuotient k)) (planeEquationQuotientY k) (by
      rw [planeNormalYPolynomial, Polynomial.eval₂_X_pow]
      exact (planeEquationQuotient_normal_relations k).2.1)

@[simp] theorem planeNormalYToQuotient_root (k : Type u) [Field k] :
    planeNormalYToQuotient k (planeNormalY k) = planeEquationQuotientY k := by
  apply AdjoinRoot.liftAlgHom_root

noncomputable def planeNormalToQuotient (k : Type u) [Field k] :
    planeNormalAlgebra k →ₐ[k] planeEquationQuotient k :=
  AdjoinRoot.liftAlgHom (planeNormalXPolynomial k) (planeNormalYToQuotient k)
    (planeEquationQuotientX k) (by
      rw [planeNormalXPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_pow]
      change planeEquationQuotientX k ^ 3 +
        planeNormalYToQuotient k (planeNormalY k) ^ 2 *
          planeEquationQuotientX k ^ 2 = 0
      rw [planeNormalYToQuotient_root]
      calc
        _ = planeEquationQuotientX k ^ 3 + planeEquationQuotientX k ^ 2 *
            planeEquationQuotientY k ^ 2 := congrArg _ (mul_comm _ _)
        _ = 0 := (planeEquationQuotient_normal_relations k).2.2)

@[simp] theorem planeNormalToQuotient_X (k : Type u) [Field k] :
    planeNormalToQuotient k (planeNormalX k) = planeEquationQuotientX k := by
  apply AdjoinRoot.liftAlgHom_root

@[simp] theorem planeNormalToQuotient_Y (k : Type u) [Field k] :
    planeNormalToQuotient k (planeNormalYInAlgebra k) = planeEquationQuotientY k := by
  change planeNormalToQuotient k
    (algebraMap (planeNormalYAlgebra k) (planeNormalAlgebra k) (planeNormalY k)) = _
  change AdjoinRoot.liftAlgHom (planeNormalXPolynomial k) (planeNormalYToQuotient k)
    (planeEquationQuotientX k) _
      (AdjoinRoot.of (planeNormalXPolynomial k) (planeNormalY k)) = _
  rw [AdjoinRoot.liftAlgHom_of, planeNormalYToQuotient_root]

@[simp] theorem planeNormalFromQuotient_X (k : Type u) [Field k] :
    planeNormalFromQuotientAlgHom k (planeEquationQuotientX k) = planeNormalX k := by
  change planeNormalFromLocal k (planeX k) = planeNormalX k
  exact planeNormalFromLocal_X k

@[simp] theorem planeNormalFromQuotient_Y (k : Type u) [Field k] :
    planeNormalFromQuotientAlgHom k (planeEquationQuotientY k) =
      planeNormalYInAlgebra k := by
  change planeNormalFromLocal k (planeY k) = planeNormalYInAlgebra k
  exact planeNormalFromLocal_Y k

private theorem planeNormalQuotient_leftInverse (k : Type u) [Field k] :
    (planeNormalToQuotient k).comp (planeNormalFromQuotientAlgHom k) =
      AlgHom.id k (planeEquationQuotient k) := by
  apply Ideal.Quotient.algHom_ext k
  apply IsLocalization.algHom_ext (planeOriginIdeal k).primeCompl
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change planeNormalToQuotient k
      (planeNormalFromQuotientAlgHom k (planeEquationQuotientX k)) =
        planeEquationQuotientX k
    rw [planeNormalFromQuotient_X, planeNormalToQuotient_X]
  · change planeNormalToQuotient k
      (planeNormalFromQuotientAlgHom k (planeEquationQuotientY k)) =
        planeEquationQuotientY k
    rw [planeNormalFromQuotient_Y, planeNormalToQuotient_Y]

private theorem planeNormalQuotient_rightInverse (k : Type u) [Field k] :
    (planeNormalFromQuotientAlgHom k).comp (planeNormalToQuotient k) =
      AlgHom.id k (planeNormalAlgebra k) := by
  apply Ideal.Quotient.algHom_ext k
  apply Polynomial.algHom_ext'
  · apply AdjoinRoot.algHom_ext
    change planeNormalFromQuotientAlgHom k
      (planeNormalToQuotient k (planeNormalYInAlgebra k)) = planeNormalYInAlgebra k
    rw [planeNormalToQuotient_Y, planeNormalFromQuotient_Y]
  · change planeNormalFromQuotientAlgHom k
      (planeNormalToQuotient k (planeNormalX k)) = planeNormalX k
    rw [planeNormalToQuotient_X, planeNormalFromQuotient_X]

/-- The checked localization calculation identifies the quotient with its
nine-dimensional normal algebra. -/
noncomputable def planeEquationQuotientEquivNormal (k : Type u) [Field k] :
    planeEquationQuotient k ≃ₐ[k] planeNormalAlgebra k :=
  AlgEquiv.ofAlgHom (planeNormalFromQuotientAlgHom k) (planeNormalToQuotient k)
    (planeNormalQuotient_rightInverse k) (planeNormalQuotient_leftInverse k)

/-- The nine independent normal forms give a strict composition series of the
localized quotient. -/
theorem planeEquationQuotient_composition_series (k : Type u) [Field k] :
    ∃ s : CompositionSeries (Submodule (planeLocalRing k) (planeEquationQuotient k)),
      s.head = ⊥ ∧ s.last = ⊤ ∧ s.length = 9 := by
  classical
  let R := planeLocalRing k
  let Q := planeEquationQuotient k
  let q : R →+* Q := Ideal.Quotient.mk (planeEquationIdeal k)
  let equivB : Q ≃ₐ[k] planeNormalAlgebra k := planeEquationQuotientEquivNormal k
  let b := planeNormalSocleBasis k
  let bQ : Module.Basis (Fin 9) k Q := b.map equivB.symm.toLinearEquiv
  have hbQflag (i : Fin 10) :
      bQ.flag i = (b.flag i).map equivB.symm.toLinearEquiv.toLinearMap := by
    exact basisMap_flag b equivB.symm.toLinearEquiv i
  let n : Fin 10 → Submodule R Q := fun i =>
    { carrier := {z | equivB z ∈ b.flag i}
      zero_mem' := by simp
      add_mem' := by
        intro z w hz hw
        simpa using (b.flag i).add_mem hz hw
      smul_mem' := by
        intro r z hz
        change equivB (q r * z) ∈ b.flag i
        rw [map_mul]
        exact planeNormalSocleFlag_mul_mem k i
          (equivB (algebraMap R Q r)) (equivB z) hz }
  have hn (i : Fin 10) : (n i).restrictScalars k = bQ.flag i := by
    rw [hbQflag]
    ext z
    change (equivB z ∈ b.flag i) ↔
      z ∈ (b.flag i).map equivB.symm.toLinearEquiv.toLinearMap
    constructor
    · intro hz
      exact ⟨equivB z, hz, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  have hn_covBy (i : Fin 9) : n i.castSucc ⋖ n i.succ := by
    apply CovBy.of_image (Submodule.restrictScalarsEmbedding k R Q)
    change (n i.castSucc).restrictScalars k ⋖ (n i.succ).restrictScalars k
    rw [hn, hn]
    exact bQ.flag_covBy i
  let s : CompositionSeries (Submodule R Q) :=
    { length := 9
      toFun := n
      step := hn_covBy }
  refine ⟨s, ?_, ?_, rfl⟩
  · change n 0 = ⊥
    ext z
    change (equivB z ∈ b.flag 0) ↔ z ∈ (⊥ : Submodule R Q)
    simp
  · change n (Fin.last 9) = ⊤
    ext z
    change (equivB z ∈ b.flag (Fin.last 9)) ↔ z ∈ (⊤ : Submodule R Q)
    rw [Module.Basis.flag_last]
    simp

theorem local_plane_equation_quotient_length (k : Type u) [Field k] :
    Module.length (planeLocalRing k) (planeEquationQuotient k) = 9 := by
  obtain ⟨s, hs, ht, hlen⟩ := planeEquationQuotient_composition_series k
  rw [← Module.length_compositionSeries s hs ht, hlen]
  norm_num
