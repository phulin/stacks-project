import Formalization.Books.Exercises.Unit17.Core

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Field.ULift

/-!
# Exercises, Chapter 17: Dimension

The declarations below follow the three exercises in source order.  Proofs are
deferred to the proving stage; the constructions use Mathlib's canonical
polynomial, ideal, prime-spectrum, Krull-dimension, and localization objects.
-/

noncomputable section

universe u

namespace Formalization.Books.Exercises.Unit17

/-! ## Exercise `dimension-bigger-one-finite-nr-primes` -/

/-- There is a commutative ring with finitely many prime ideals and Krull
dimension strictly greater than one. -/
theorem exists_ring_with_finitely_many_prime_ideals_and_dimension_gt_one :
    ∃ (R : Type u) (inst : CommRing R),
      @HasFinitePrimeSpectrumAndDimensionAboveOne R inst := by
  let Γ := ℤ ×ₗ ℤ
  letI : LE Γ := Prod.Lex.instLE ℤ ℤ
  letI : LT Γ := Prod.Lex.instLT ℤ ℤ
  letI : LinearOrder Γ := inferInstanceAs (LinearOrder (ℤ ×ₗ ℤ))
  let k := ULift.{u} ℚ
  let K := HahnSeries Γ k
  let V : ValuationSubring K :=
    (HahnSeries.addVal Γ k).toValuation.valuationSubring
  have hfin : Finite (PrimeSpectrum V) := by
    classical
    let e := ValuationSubring.primeSpectrumOrderEquiv V
    let a : K := HahnSeries.single (Γ := Γ) (R := k) ((0, -1) : Γ) (1 : k)
    let b : K := HahnSeries.single (Γ := Γ) (R := k) ((-1, 0) : Γ) (1 : k)
    have hV : ∀ x : K, x ∈ V ↔ 0 ≤ HahnSeries.addVal Γ k x := by
      intro x
      change (HahnSeries.addVal Γ k).toValuation x ≤ 1 ↔ _
      simp only [AddValuation.toValuation_apply]
      change Multiplicative.ofAdd (OrderDual.toDual (HahnSeries.addVal Γ k x)) ≤
          Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop Γ)) ↔ _
      rfl
    have hval_single : ∀ g : Γ,
        HahnSeries.addVal Γ k
            (HahnSeries.single (Γ := Γ) (R := k) g (1 : k)) = g := by
      intro g
      rw [HahnSeries.addVal_apply, HahnSeries.orderTop_single]
      simp
    have hquot_single : ∀ g h : Γ,
        0 ≤ HahnSeries.addVal Γ k
            (HahnSeries.single (Γ := Γ) (R := k) g (1 : k) /
              HahnSeries.single (Γ := Γ) (R := k) h (1 : k)) ↔
          @LE.le Γ (Prod.Lex.instLE ℤ ℤ) h g := by
      intro g h
      rw [AddValuation.map_div, hval_single, hval_single]
      change 0 ≤ (↑(g - h) : WithTop Γ) ↔ h ≤ g
      exact_mod_cast sub_nonneg
    have hquot_single_pow : ∀ g h : Γ, ∀ n : ℕ,
        0 ≤ HahnSeries.addVal Γ k
            (HahnSeries.single (Γ := Γ) (R := k) g (1 : k) /
              (HahnSeries.single (Γ := Γ) (R := k) h (1 : k)) ^ n) ↔
          @LE.le Γ (Prod.Lex.instLE ℤ ℤ) (n • h) g := by
      intro g h n
      rw [AddValuation.map_div, hval_single, AddValuation.map_pow, hval_single]
      change 0 ≤ (↑(g - n • h) : WithTop Γ) ↔ n • h ≤ g
      exact_mod_cast sub_nonneg
    have hfactor {S : ValuationSubring K} (hVS : V ≤ S)
        {x y : K} (hx0 : x ≠ 0) (hxS : x ∈ S)
        (hq : 0 ≤ HahnSeries.addVal Γ k (y / x)) : y ∈ S := by
      have hqV : y / x ∈ V := hV _ |>.2 hq
      have heq : y = x * (y / x) := by
        rw [div_eq_mul_inv, ← mul_assoc, mul_comm x y, mul_assoc,
          mul_inv_cancel₀ hx0, mul_one]
      rw [heq]
      exact S.mul_mem x _ hxS (hVS hqV)
    have hsingle_of_mem {S : ValuationSubring K} (hVS : V ≤ S) {x : K}
        (hxS : x ∈ S) : x = 0 ∨
          HahnSeries.single (Γ := Γ) (R := k) x.order (1 : k) ∈ S := by
      obtain rfl | hx := eq_or_ne x 0
      · exact Or.inl rfl
      right
      let m : K := HahnSeries.single (Γ := Γ) (R := k) x.order x.leadingCoeff
      let r : K := x / m
      have hlead : x.leadingCoeff ≠ 0 :=
        HahnSeries.leadingCoeff_ne_zero.mpr hx
      have hm : m ≠ 0 := by
        dsimp [m]
        exact HahnSeries.single_ne_zero hlead
      have hvalx : HahnSeries.addVal Γ k x = x.order := by
        rw [HahnSeries.addVal_apply_of_ne hx]
      have hvalm : HahnSeries.addVal Γ k m = x.order := by
        simp [m, hval_single, hlead]
      have hvalr : HahnSeries.addVal Γ k r = 0 := by
        dsimp [r]
        rw [AddValuation.map_div, hvalx, hvalm]
        change (↑(x.order - x.order) : WithTop Γ) = 0
        simp
      have hvalrinv : HahnSeries.addVal Γ k r⁻¹ = 0 := by
        rw [AddValuation.map_inv, hvalr, neg_zero]
      have hrinvV : r⁻¹ ∈ V := hV _ |>.2 (by simpa [hvalrinv])
      have hmS : m ∈ S := by
        have hxm : x = m * r := by
          dsimp [r]
          rw [div_eq_mul_inv, ← mul_assoc, mul_comm m x, mul_assoc,
            mul_inv_cancel₀ hm, mul_one]
        have hr : r ≠ 0 := div_ne_zero hx hm
        have hm_eq : m = x * r⁻¹ := by
          calc
            m = m * (r * r⁻¹) := by rw [mul_inv_cancel₀ hr, mul_one]
            _ = (m * r) * r⁻¹ := by ring
            _ = x * r⁻¹ := by rw [hxm]
        rw [hm_eq]
        exact S.mul_mem x r⁻¹ hxS (hVS hrinvV)
      have hcV :
          HahnSeries.single (Γ := Γ) (R := k) (0 : Γ) x.leadingCoeff⁻¹ ∈ V := by
        apply hV _ |>.2
        rw [HahnSeries.addVal_apply,
          HahnSeries.orderTop_single (inv_ne_zero hlead)]
        exact le_rfl
      have hmc : m * HahnSeries.single (Γ := Γ) (R := k) (0 : Γ)
          x.leadingCoeff⁻¹ =
          HahnSeries.single (Γ := Γ) (R := k) x.order (1 : k) := by
        dsimp [m]
        rw [HahnSeries.single_mul_single]
        rw [mul_inv_cancel₀ hlead]
        simp
      rw [← hmc]
      exact S.mul_mem m _ hmS (hVS hcV)
    have hmem_of_single {S : ValuationSubring K} (hVS : V ≤ S) (x : K) :
        x ∈ S ↔ x = 0 ∨
          HahnSeries.single (Γ := Γ) (R := k) x.order (1 : k) ∈ S := by
      constructor
      · intro hxS
        exact hsingle_of_mem hVS hxS
      · rintro (rfl | hxS)
        · exact S.zero_mem
        · by_cases hx : x = 0
          · exact hx ▸ S.zero_mem
          · have hvalx : HahnSeries.addVal Γ k x = x.order := by
              rw [HahnSeries.addVal_apply_of_ne hx]
            apply hfactor hVS (HahnSeries.single_ne_zero one_ne_zero) hxS
            rw [AddValuation.map_div, hvalx, hval_single]
            change 0 ≤ (↑(x.order - x.order) : WithTop Γ)
            simp
    have hclass : ∀ {S T : ValuationSubring K}, V ≤ S → V ≤ T →
        (a ∈ S ↔ a ∈ T) → (b ∈ S ↔ b ∈ T) → S = T := by
      intro S T hVS hVT ha hb
      apply ValuationSubring.ext
      intro x
      by_cases hx0 : x = 0
      · simp [hx0]
      have hvalx : HahnSeries.addVal Γ k x = x.order := by
        rw [HahnSeries.addVal_apply_of_ne hx0]
      by_cases hnonneg : @LE.le Γ (Prod.Lex.instLE ℤ ℤ) 0 x.order
      · have hxV : x ∈ V := hV _ |>.2 (by rw [hvalx]; exact_mod_cast hnonneg)
        exact iff_of_true (hVS hxV) (hVT hxV)
      generalize hg : x.order = g at hnonneg
      have hneg : @LT.lt Γ (Prod.Lex.instLT ℤ ℤ) g 0 := lt_of_not_ge hnonneg
      rcases g with ⟨i, j⟩
      rcases (Prod.Lex.toLex_lt_toLex.mp hneg) with hi | ⟨hi0, hj⟩
      · have hmonom : ∀ U : ValuationSubring K, V ≤ U →
            (HahnSeries.single (Γ := Γ) (R := k) ((i, j) : Γ) (1 : k) ∈ U ↔ b ∈ U) := by
          intro U
          intro hVU
          constructor
          · intro hz
            let z : K := HahnSeries.single (Γ := Γ) (R := k) (i, j) (1 : k)
            have hz' : z ∈ U := by simpa [z] using hz
            have hz2 : z ^ 2 ∈ U := pow_mem hz' 2
            have hq : 0 ≤ HahnSeries.addVal Γ k (b / z ^ 2) := by
              apply (hquot_single_pow ((-1, 0) : Γ) ((i, j) : Γ) 2).2
              change @LE.le Γ (Prod.Lex.instLE ℤ ℤ)
                (2 • toLex (i, j)) (toLex (-1, 0))
              apply (Prod.Lex.toLex_le_toLex).2
              left
              change 2 • i < (-1 : ℤ)
              simp only [nsmul_eq_mul]
              omega
            apply hfactor hVU (pow_ne_zero 2 (HahnSeries.single_ne_zero one_ne_zero)) hz2
            simpa [b, z] using hq
          · intro hbU
            let n : ℕ := i.natAbs + 1
            have hn : @LE.le Γ (Prod.Lex.instLE ℤ ℤ)
                (n • toLex (-1, 0)) (toLex (i, j)) := by
              apply (Prod.Lex.toLex_le_toLex).2
              left
              change n • (-1 : ℤ) < i
              dsimp [n]
              rw [Int.ofNat_natAbs_of_nonpos hi.le]
              omega
            have hq : 0 ≤ HahnSeries.addVal Γ k
                ((HahnSeries.single (Γ := Γ) (R := k) (i, j) (1 : k)) / b ^ n) := by
              apply (hquot_single_pow ((i, j) : Γ) ((-1, 0) : Γ) n).2
              change @LE.le Γ (Prod.Lex.instLE ℤ ℤ)
                (n • toLex (-1, 0)) (toLex (i, j))
              exact hn
            have hbpow : b ^ n ∈ U := pow_mem hbU n
            exact hfactor hVU (pow_ne_zero n (HahnSeries.single_ne_zero one_ne_zero))
              hbpow hq
        have hmonoS :
            HahnSeries.single (Γ := Γ) (R := k) x.order (1 : k) ∈ S ↔ b ∈ S := by
          rw [hg]
          exact hmonom S hVS
        have hmonoT :
            HahnSeries.single (Γ := Γ) (R := k) x.order (1 : k) ∈ T ↔ b ∈ T := by
          rw [hg]
          exact hmonom T hVT
        rw [hmem_of_single hVS x, hmem_of_single hVT x]
        simp [hx0, hmonoS, hmonoT, hb]
      · have hi0' : i = 0 := by simpa using hi0
        subst i
        have hmonom : ∀ U : ValuationSubring K, V ≤ U →
            (HahnSeries.single (Γ := Γ) (R := k) ((0, j) : Γ) (1 : k) ∈ U ↔ a ∈ U) := by
          intro U
          intro hVU
          constructor
          · intro hz
            let z : K := HahnSeries.single (Γ := Γ) (R := k) (0, j) (1 : k)
            have hz' : z ∈ U := by simpa [z] using hz
            have hq : 0 ≤ HahnSeries.addVal Γ k (a / z) := by
              apply (hquot_single ((0, -1) : Γ) ((0, j) : Γ)).2
              change @LE.le (Lex (ℤ × ℤ)) (Prod.Lex.instLE ℤ ℤ)
                (toLex ((0 : ℤ), j)) (toLex ((0 : ℤ), -1))
              exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, by omega⟩)
            apply hfactor hVU (HahnSeries.single_ne_zero one_ne_zero) hz'
            simpa [a, z] using hq
          · intro haU
            let n : ℕ := j.natAbs + 1
            have hn : @LE.le Γ (Prod.Lex.instLE ℤ ℤ)
                (n • toLex (0, -1)) (toLex (0, j)) := by
              change @LE.le Γ (Prod.Lex.instLE ℤ ℤ)
                (n • toLex (0, -1)) (toLex (0, j))
              apply (Prod.Lex.toLex_le_toLex).2
              right
              constructor
              · rfl
              · change n • (-1 : ℤ) ≤ j
                dsimp [n]
                rw [Int.ofNat_natAbs_of_nonpos hj.le]
                omega
            have hq : 0 ≤ HahnSeries.addVal Γ k
                ((HahnSeries.single (Γ := Γ) (R := k) (0, j) (1 : k)) / a ^ n) := by
              apply (hquot_single_pow ((0, j) : Γ) ((0, -1) : Γ) n).2
              change @LE.le Γ (Prod.Lex.instLE ℤ ℤ)
                (n • toLex (0, -1)) (toLex (0, j))
              exact hn
            have hapow : a ^ n ∈ U := pow_mem haU n
            exact hfactor hVU (pow_ne_zero n (HahnSeries.single_ne_zero one_ne_zero))
              hapow hq
        have hmonoS :
            HahnSeries.single (Γ := Γ) (R := k) x.order (1 : k) ∈ S ↔ a ∈ S := by
          rw [hg]
          exact hmonom S hVS
        have hmonoT :
            HahnSeries.single (Γ := Γ) (R := k) x.order (1 : k) ∈ T ↔ a ∈ T := by
          rw [hg]
          exact hmonom T hVT
        rw [hmem_of_single hVS x, hmem_of_single hVT x]
        simp [hx0, hmonoS, hmonoT, ha]
    let f : PrimeSpectrum V → Bool × Bool := fun p =>
      (decide (a ∈ (e (OrderDual.toDual p) : ValuationSubring K)),
        decide (b ∈ (e (OrderDual.toDual p) : ValuationSubring K)))
    apply Finite.of_injective f
    intro p q hpq
    let S : ValuationSubring K := e (OrderDual.toDual p)
    let T : ValuationSubring K := e (OrderDual.toDual q)
    have hVS : V ≤ S := (e (OrderDual.toDual p)).property
    have hVT : V ≤ T := (e (OrderDual.toDual q)).property
    have ha : a ∈ S ↔ a ∈ T := by
      apply decide_eq_decide.mp
      exact congrArg Prod.fst hpq
    have hb : b ∈ S ↔ b ∈ T := by
      apply decide_eq_decide.mp
      exact congrArg Prod.snd hpq
    have hST : S = T := hclass hVS hVT ha hb
    have heq : e (OrderDual.toDual p) = e (OrderDual.toDual q) := by
      exact Subtype.ext hST
    have hdual : OrderDual.toDual p = OrderDual.toDual q := e.injective heq
    simpa using hdual
  refine ⟨V, inferInstance, hfin, ?_⟩
  let proj : Γ →+ ℤ :=
    { toFun := fun g => g.1
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  have hproj : Monotone proj := by
    intro x y hxy
    change x.1 ≤ y.1
    change toLex (x.1, x.2) ≤ toLex (y.1, y.2) at hxy
    rcases (Prod.Lex.toLex_le_toLex.mp hxy) with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  have htop : (AddMonoidHom.withTopMap proj) (⊤ : WithTop Γ) = ⊤ := by
    simp
  let wval : AddValuation K (WithTop ℤ) :=
    (HahnSeries.addVal Γ k).map (AddMonoidHom.withTopMap proj) htop
      hproj.withTop_map
  let W : ValuationSubring K := wval.toValuation.valuationSubring
  have hW : ∀ x : K, x ∈ W ↔ 0 ≤ wval x := by
    intro x
    change wval.toValuation x ≤ 1 ↔ _
    simp only [AddValuation.toValuation_apply]
    change Multiplicative.ofAdd (OrderDual.toDual (wval x)) ≤
        Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) ↔ _
    rfl
  have hval_single' : ∀ g : Γ,
      HahnSeries.addVal Γ k
          (HahnSeries.single (Γ := Γ) (R := k) g (1 : k)) = g := by
    intro g
    rw [HahnSeries.addVal_apply, HahnSeries.orderTop_single]
    simp
  have hwval_single : ∀ g : Γ,
      wval (HahnSeries.single (Γ := Γ) (R := k) g (1 : k)) = (proj g : WithTop ℤ) := by
    intro g
    change WithTop.map proj (HahnSeries.addVal Γ k
      (HahnSeries.single (Γ := Γ) (R := k) g (1 : k))) = (proj g : WithTop ℤ)
    rw [hval_single']
    simp
  have hV' : ∀ x : K, x ∈ V ↔ 0 ≤ HahnSeries.addVal Γ k x := by
    intro x
    change (HahnSeries.addVal Γ k).toValuation x ≤ 1 ↔ _
    simp only [AddValuation.toValuation_apply]
    change Multiplicative.ofAdd (OrderDual.toDual (HahnSeries.addVal Γ k x)) ≤
        Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop Γ)) ↔ _
    rfl
  have hVW : V ≤ W := by
    intro x hx
    have hx' : 0 ≤ HahnSeries.addVal Γ k x := (hV' x).1 hx
    change 0 ≤ WithTop.map proj (HahnSeries.addVal Γ k x)
    simpa using hproj.withTop_map hx'
  let gA : Γ := toLex ((0 : ℤ), -1)
  let gB : Γ := toLex ((-1 : ℤ), 0)
  let a : K := HahnSeries.single (Γ := Γ) (R := k) gA (1 : k)
  let b : K := HahnSeries.single (Γ := Γ) (R := k) gB (1 : k)
  have hprojA : proj gA = 0 := by
    rfl
  have hprojB : proj gB = -1 := by
    rfl
  have haW : a ∈ W := by
    rw [hW]
    change 0 ≤ wval (HahnSeries.single (Γ := Γ) (R := k) gA (1 : k))
    rw [hwval_single]
    rw [hprojA]
    exact le_rfl
  have haV : a ∉ V := by
    intro ha
    have h := (hV' a).1 ha
    dsimp [a] at h
    rw [hval_single'] at h
    have hneg : gA < 0 := by
      dsimp [gA]
      apply (Prod.Lex.toLex_lt_toLex).2
      right
      omega
    have hneg' : (↑gA : WithTop Γ) < 0 := by
      simpa using (WithTop.coe_lt_coe.mpr hneg)
    exact (not_le_of_gt hneg') h
  have hbW : b ∉ W := by
    intro hb
    have h := (hW b).1 hb
    dsimp [b] at h
    change 0 ≤ wval (HahnSeries.single (Γ := Γ) (R := k) gB (1 : k)) at h
    rw [hwval_single] at h
    rw [hprojB] at h
    have hneg : (-1 : WithTop ℤ) < 0 := by
      simpa using (WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by omega))
    exact (not_le_of_gt hneg) h
  have hVWlt : V < W := by
    apply lt_of_le_of_ne hVW
    intro h
    apply haV
    rw [h]
    exact haW
  have hWtop : W < (⊤ : ValuationSubring K) := by
    apply lt_of_le_of_ne (ValuationSubring.le_top W)
    intro h
    apply hbW
    rw [h]
    exact ValuationSubring.mem_top b
  let e := ValuationSubring.primeSpectrumOrderEquiv V
  let qV : { S : ValuationSubring K // V ≤ S } := ⟨V, le_rfl⟩
  let qW : { S : ValuationSubring K // V ≤ S } := ⟨W, hVW⟩
  let qTop : { S : ValuationSubring K // V ≤ S } := ⟨⊤, V.le_top⟩
  have hqVW : qV < qW := hVWlt
  have hqWTop : qW < qTop := hWtop
  let p0 : PrimeSpectrum V := OrderDual.ofDual (e.symm qTop)
  let p1 : PrimeSpectrum V := OrderDual.ofDual (e.symm qW)
  let p2 : PrimeSpectrum V := OrderDual.ofDual (e.symm qV)
  have hp01 : p0 < p1 := by
    exact e.symm.strictMono hqWTop
  have hp12 : p1 < p2 := by
    exact e.symm.strictMono hqVW
  have hp02 : p0 < p2 := hp01.trans hp12
  have hchain : ∃ l : LTSeries (PrimeSpectrum V), l.length = 2 := by
    refine ⟨LTSeries.mk 2 ![p0, p1, p2] ?_, rfl⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hp01, hp12, hp02]
  have hdim : (2 : ℕ) ≤ ringKrullDim V := by
    change (2 : ℕ) ≤ Order.krullDim (PrimeSpectrum V)
    exact Order.le_krullDim_iff.mpr hchain
  exact lt_of_lt_of_le (by norm_num : (1 : WithBot ℕ∞) < 2) hdim

/-! ## Exercise `hypersurface-in-A2-dimension-one` -/

/-- The quotient of `ℂ[x,y]` by a nonconstant polynomial has dimension one. -/
theorem complex_bivariate_hypersurface_has_dimension_one
    (f : complexBivariatePolynomialRing)
    (hf : IsNonconstantComplexBivariatePolynomial f) :
    ringKrullDim (complexBivariateHypersurfaceRing f) = 1 := by
  have hf0 : f ≠ 0 := by
    intro h
    apply hf 0
    simpa [h]
  have hzero : (MvPolynomial.zeroLocus ℂ (Ideal.span {f})).Nonempty := by
    by_contra h
    have hempty : MvPolynomial.zeroLocus ℂ (Ideal.span {f}) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    have hrad : (Ideal.span {f}).radical = ⊤ := by
      rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ), hempty,
        MvPolynomial.vanishingIdeal_empty]
    have htop : Ideal.span {f} = ⊤ := Ideal.radical_eq_top.mp hrad
    have hunit : IsUnit f := Ideal.span_singleton_eq_top.mp htop
    obtain ⟨c, _, hc⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := f)).mp hunit
    exact hf c hc
  obtain ⟨x, hx⟩ := hzero
  have hpoint : ∀ (k : ℕ) (y : Fin k → ℂ),
      (MvPolynomial.vanishingIdeal ℂ {y}).height = k := by
    intro k
    induction k with
    | zero =>
        intro y
        have hbase : MvPolynomial.vanishingIdeal ℂ {y} = ⊥ := by
          ext p
          rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
          have he : MvPolynomial.aeval y =
              (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).toAlgHom := by
            apply MvPolynomial.algHom_ext
            intro i
            exact Fin.elim0 i
          rw [he]
          constructor
          · intro hp
            apply Ideal.mem_bot.mpr
            apply (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).injective
            simpa using hp
          · intro hp
            simpa [Ideal.mem_bot.mp hp]
        rw [hbase, Ideal.height_bot]
        simp
    | succ k ih =>
        intro y
        let yt : Fin k → ℂ := fun i => y i.succ
        let q : Ideal (MvPolynomial (Fin (k + 1)) ℂ) :=
          MvPolynomial.vanishingIdeal ℂ {y}
        let p : Ideal (MvPolynomial (Fin k) ℂ) :=
          MvPolynomial.vanishingIdeal ℂ {yt}
        let e := MvPolynomial.finSuccEquiv ℂ k
        let er := e.toRingEquiv
        let P : Ideal (Polynomial (MvPolynomial (Fin k) ℂ)) := q.map er
        letI : q.IsMaximal := by
          dsimp [q]
          infer_instance
        letI : P.IsMaximal := by
          dsimp [P]
          infer_instance
        have heval :
            ((MvPolynomial.aeval (R := ℂ) y : MvPolynomial (Fin (k + 1)) ℂ →+* ℂ).comp
              (er.symm : Polynomial (MvPolynomial (Fin k) ℂ) →+*
                MvPolynomial (Fin (k + 1)) ℂ)).comp
              (Polynomial.C : MvPolynomial (Fin k) ℂ →+*
                Polynomial (MvPolynomial (Fin k) ℂ)) =
              (MvPolynomial.aeval (R := ℂ) yt : MvPolynomial (Fin k) ℂ →+* ℂ) := by
          apply MvPolynomial.ringHom_ext'
          · ext c
            change MvPolynomial.aeval (R := ℂ) y
                (er.symm (Polynomial.C (MvPolynomial.C c))) =
              MvPolynomial.aeval (R := ℂ) yt (MvPolynomial.C c)
            have he := congrArg (fun f => f c)
              (MvPolynomial.finSuccEquiv_comp_C_eq_C (R := ℂ) k)
            have he' : er.symm (Polynomial.C (MvPolynomial.C c)) =
                (MvPolynomial.C c : MvPolynomial (Fin (k + 1)) ℂ) := by
              simpa [er, e, RingHom.comp_apply] using he
            rw [he']
            simp
          · intro i
            simp only [RingHom.comp_apply]
            have he : er.symm (Polynomial.C (MvPolynomial.X i)) =
                MvPolynomial.X i.succ := by
              rw [er.symm_apply_eq]
              simpa [er, e] using
                (MvPolynomial.finSuccEquiv_X_succ (R := ℂ) (n := k) (j := i)).symm
            have he' : (er.symm : Polynomial (MvPolynomial (Fin k) ℂ) →+*
                MvPolynomial (Fin (k + 1)) ℂ) (Polynomial.C (MvPolynomial.X i)) =
                MvPolynomial.X i.succ := he
            rw [he']
            simp [yt]
        have hunder : P.under (MvPolynomial (Fin k) ℂ) = p := by
          ext a
          change Polynomial.C a ∈ q.map er ↔ a ∈ p
          rw [← Ideal.symm_apply_mem_of_equiv_iff]
          rw [MvPolynomial.mem_vanishingIdeal_singleton_iff,
            MvPolynomial.mem_vanishingIdeal_singleton_iff]
          change MvPolynomial.aeval (R := ℂ) y (er.symm (Polynomial.C a)) = 0 ↔ _
          have haeval : MvPolynomial.aeval (R := ℂ) y (er.symm (Polynomial.C a)) =
              MvPolynomial.aeval (R := ℂ) yt a := by
            simpa [RingHom.comp_apply] using congrArg (fun f => f a) heval
          rw [haeval]
        letI : P.LiesOver p := ⟨hunder.symm⟩
        have hstep : q.height = p.height + 1 := by
          rw [← er.height_map q]
          exact Polynomial.height_eq_height_add_one p P
        have ih' : p.height = k := by
          simpa [p, yt] using ih yt
        rw [hstep, ih']
        simp
  let Q : Ideal complexBivariatePolynomialRing := MvPolynomial.vanishingIdeal ℂ {x}
  have hQ : Q.IsMaximal := by
    dsimp [Q]
    infer_instance
  letI : Q.IsMaximal := hQ
  have hQmem : f ∈ Q := by
    dsimp [Q]
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hx f (Ideal.subset_span (Set.mem_singleton f))
  have hQheight : Q.height = 2 := by
    simpa [Q] using hpoint 2 x
  have hlow : (2 : WithBot ℕ∞) ≤ ringKrullDim (complexBivariateHypersurfaceRing f) + 1 := by
    have hQheight' : (Q.height : WithBot ℕ∞) = 2 := by
      simpa using congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) hQheight
    rw [← hQheight']
    exact Ideal.height_le_ringKrullDim_quotient_add_one hQmem
  have hupper : ringKrullDim (complexBivariateHypersurfaceRing f) + 1 ≤ 2 := by
    have hnd : f ∈ nonZeroDivisors complexBivariatePolynomialRing :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hf0
    simpa [complexBivariatePolynomialRing, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field] using
      ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnd
  generalize hd : ringKrullDim (complexBivariateHypersurfaceRing f) = d at hlow hupper ⊢
  induction d using WithBot.recBotCoe with
  | bot =>
      simp at hlow
  | coe d =>
      have hlow'' : (↑(2 : ℕ∞) : WithBot ℕ∞) ≤ ↑(d + 1) := by
        convert hlow using 1 <;> norm_num [WithBot.coe_add, WithBot.coe_one]
      have hupper'' : (↑(d + 1) : WithBot ℕ∞) ≤ ↑(2 : ℕ∞) := by
        convert hupper using 1 <;> norm_num [WithBot.coe_add, WithBot.coe_one]
      have hlow' : (2 : ℕ∞) ≤ d + 1 := WithBot.coe_le_coe.mp hlow''
      have hupper' : d + 1 ≤ (2 : ℕ∞) := WithBot.coe_le_coe.mp hupper''
      norm_cast at ⊢
      apply le_antisymm
      · have hc : d + 1 ≤ (1 : ℕ∞) + 1 := by
          convert hupper' using 1 <;> norm_num
        exact (ENat.add_le_add_iff_right (k := (1 : ℕ∞))
          (by simp : (1 : ℕ∞) ≠ ⊤)).mp hc
      · have hc : (1 : ℕ∞) + 1 ≤ d + 1 := by
          convert hlow' using 1 <;> norm_num
        exact (ENat.add_le_add_iff_right (k := (1 : ℕ∞))
          (by simp : (1 : ℕ∞) ≠ ⊤)).mp hc

/-! ## Exercise `dimension-polynomial-ring` -/

/-- The ideal `(𝔪, x₁, ..., xₙ)` in a polynomial ring over a local ring is
maximal. -/
theorem polynomialMaximalIdeal_isMaximal
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    (polynomialMaximalIdeal R n).IsMaximal := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  letI : m.IsMaximal := by
    exact IsLocalRing.maximalIdeal.isMaximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  let φ : polynomialRing R n →+* R ⧸ m :=
    MvPolynomial.eval₂Hom (Ideal.Quotient.mk m) (fun _ => 0)
  have hsurj : Function.Surjective φ := by
    intro r
    rcases Ideal.Quotient.mk_surjective r with ⟨s, rfl⟩
    exact ⟨MvPolynomial.C s, by simp [φ]⟩
  have hdiff : ∀ p : polynomialRing R n,
      p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
        MvPolynomial.idealOfVars (Fin n) R := by
    intro p
    induction p using MvPolynomial.induction_on' with
    | monomial d a =>
        by_cases hd : d = 0
        · subst d
          simp
        · by_cases ha : a = 0
          · simp [ha]
          · simp only [MvPolynomial.constantCoeff_monomial, if_neg hd, sub_zero]
            have hdeg : 1 ≤ Finsupp.degree d :=
              Nat.one_le_iff_ne_zero.mpr fun h =>
                hd ((Finsupp.degree_eq_zero_iff d).mp h)
            rw [← pow_one (MvPolynomial.idealOfVars (Fin n) R)]
            simpa using (MvPolynomial.monomial_mem_pow_idealOfVars_iff 1 d ha).2 hdeg
    | add p q hp hq =>
        convert Ideal.add_mem _ hp hq using 1 <;>
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hker : RingHom.ker φ = polynomialMaximalIdeal R n := by
    apply le_antisymm
    · intro p hp
      have hp0 : Ideal.Quotient.mk m (MvPolynomial.constantCoeff p) = 0 := by
        simpa [φ] using hp
      have hcm : MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
          Ideal.map (algebraMap R (polynomialRing R n)) m := by
        simpa using (Ideal.mem_map_of_mem (algebraMap R (polynomialRing R n))
          (Ideal.Quotient.eq_zero_iff_mem.mp hp0))
      have hd := hdiff p
      have heq : p = (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) +
          MvPolynomial.C (MvPolynomial.constantCoeff p) := by ring
      rw [heq]
      rw [polynomialMaximalIdeal]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hd) (Ideal.mem_sup_left hcm)
    · apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        change φ (algebraMap R (polynomialRing R n) r) = 0
        have hrm : r ∈ m := by simpa [m] using hr
        simpa [φ] using (Ideal.Quotient.eq_zero_iff_mem.mpr hrm)
      · rw [MvPolynomial.idealOfVars, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        simp [φ]
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective φ hsurj

instance polynomialMaximalIdeal_isPrime
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    (polynomialMaximalIdeal R n).IsPrime :=
  (polynomialMaximalIdeal_isMaximal R n).isPrime

private theorem polynomialMaximalIdeal_eq_ker_eval₂Hom
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    RingHom.ker
        (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
          (fun _ : Fin n => 0)) = polynomialMaximalIdeal R n := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  letI : m.IsMaximal := by
    exact IsLocalRing.maximalIdeal.isMaximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  let φ : polynomialRing R n →+* R ⧸ m :=
    MvPolynomial.eval₂Hom (Ideal.Quotient.mk m) (fun _ => 0)
  have hdiff : ∀ p : polynomialRing R n,
      p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
        MvPolynomial.idealOfVars (Fin n) R := by
    intro p
    induction p using MvPolynomial.induction_on' with
    | monomial d a =>
        by_cases hd : d = 0
        · subst d
          simp
        · by_cases ha : a = 0
          · simp [ha]
          · simp only [MvPolynomial.constantCoeff_monomial, if_neg hd, sub_zero]
            have hdeg : 1 ≤ Finsupp.degree d :=
              Nat.one_le_iff_ne_zero.mpr fun h =>
                hd ((Finsupp.degree_eq_zero_iff d).mp h)
            rw [← pow_one (MvPolynomial.idealOfVars (Fin n) R)]
            simpa using (MvPolynomial.monomial_mem_pow_idealOfVars_iff 1 d ha).2 hdeg
    | add p q hp hq =>
        convert Ideal.add_mem _ hp hq using 1 <;>
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hker : RingHom.ker φ = polynomialMaximalIdeal R n := by
    apply le_antisymm
    · intro p hp
      have hp0 : Ideal.Quotient.mk m (MvPolynomial.constantCoeff p) = 0 := by
        simpa [φ] using hp
      have hcm : MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
          Ideal.map (algebraMap R (polynomialRing R n)) m := by
        simpa using (Ideal.mem_map_of_mem (algebraMap R (polynomialRing R n))
          (Ideal.Quotient.eq_zero_iff_mem.mp hp0))
      have hd := hdiff p
      have heq : p = (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) +
          MvPolynomial.C (MvPolynomial.constantCoeff p) := by ring
      rw [heq, polynomialMaximalIdeal]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hd) (Ideal.mem_sup_left hcm)
    · apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        change φ (algebraMap R (polynomialRing R n) r) = 0
        have hrm : r ∈ m := by simpa [m] using hr
        simpa [φ] using (Ideal.Quotient.eq_zero_iff_mem.mpr hrm)
      · rw [MvPolynomial.idealOfVars, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        simp [φ]
  simpa [φ, m] using hker

/- The localization at the displayed maximal ideal. -/
abbrev polynomialLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :=
  Localization.AtPrime (polynomialMaximalIdeal R n)

/-- For a Noetherian local ring, localizing its `n`-variable polynomial ring
at `(𝔪, x₁, ..., xₙ)` raises the dimension by `n` (for `n ≥ 1`). -/
theorem polynomial_localization_dimension_formula
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) (hn : 1 ≤ n) :
    ringKrullDim (polynomialLocalRing R n) = ringKrullDim R + n := by
  letI : (polynomialMaximalIdeal R n).IsPrime := polynomialMaximalIdeal_isPrime R n
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (polynomialMaximalIdeal R n)
    (polynomialLocalRing R n)]
  have hdim : ∀ k : ℕ,
      (polynomialMaximalIdeal R k).height = ringKrullDim R + k := by
    intro k
    induction k with
    | zero =>
        let e := MvPolynomial.isEmptyRingEquiv R (Fin 0)
        have hψ :
            MvPolynomial.eval₂Hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
                (fun _ : Fin 0 => 0) =
              (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp e := by
          rw [MvPolynomial.eval₂Hom_zero']
          apply MvPolynomial.ringHom_ext'
          · ext r
            change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
                (MvPolynomial.constantCoeff (MvPolynomial.C r)) =
              (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
                ((MvPolynomial.C r).coeff 0)
            simp
          · intro i
            exact Fin.elim0 i
        have he : polynomialMaximalIdeal R 0 =
            (IsLocalRing.maximalIdeal R).comap e := by
          rw [← polynomialMaximalIdeal_eq_ker_eval₂Hom R 0, hψ]
          ext p
          simp [Ideal.Quotient.eq_zero_iff_mem]
        rw [he, e.height_comap,
          IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
        simp
    | succ k ih =>
        let e := MvPolynomial.finSuccEquiv R k
        let er := e.toRingEquiv
        let p := polynomialMaximalIdeal R k
        let q := polynomialMaximalIdeal R (k + 1)
        let P : Ideal (Polynomial (polynomialRing R k)) := q.map er
        letI : q.IsMaximal := by
          dsimp [q]
          exact polynomialMaximalIdeal_isMaximal R (k + 1)
        letI : P.IsMaximal := by
          dsimp [P]
          infer_instance
        have hkerₖ :
            RingHom.ker
                (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
                  (fun _ : Fin k => 0)) = p := by
          simpa [p] using polynomialMaximalIdeal_eq_ker_eval₂Hom R k
        have hkerₛ :
            RingHom.ker
                (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
                  (fun _ : Fin (k + 1) => 0)) = q := by
          simpa [q] using polynomialMaximalIdeal_eq_ker_eval₂Hom R (k + 1)
        have heval :
            ((MvPolynomial.eval₂Hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
              (fun _ : Fin (k + 1) => 0)).comp
                (er.symm : Polynomial (polynomialRing R k) →+*
                  polynomialRing R (k + 1))).comp
              (Polynomial.C : polynomialRing R k →+* Polynomial (polynomialRing R k)) =
              MvPolynomial.eval₂Hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
                (fun _ : Fin k => 0) := by
          apply MvPolynomial.ringHom_ext'
          · ext r
            change
              (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
                (fun _ : Fin (k + 1) => 0))
                  (e.symm (Polynomial.C (MvPolynomial.C r))) =
                (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
                  (fun _ : Fin k => 0)) (MvPolynomial.C r)
            have he := congrArg (fun f => f r)
              (MvPolynomial.finSuccEquiv_comp_C_eq_C (R := R) k)
            have he' : e.symm (Polynomial.C (MvPolynomial.C r)) =
                (MvPolynomial.C r : polynomialRing R (k + 1)) := by
              simpa [e, RingHom.comp_apply] using he
            rw [he']
            simp
          · intro i
            simp only [RingHom.comp_apply]
            have he : er.symm (Polynomial.C (MvPolynomial.X i)) =
                MvPolynomial.X i.succ := by
              rw [er.symm_apply_eq]
              simpa [er, e] using
                (MvPolynomial.finSuccEquiv_X_succ (R := R) (n := k) (j := i)).symm
            have he' : (er.symm : Polynomial (polynomialRing R k) →+*
                polynomialRing R (k + 1)) (Polynomial.C (MvPolynomial.X i)) =
                MvPolynomial.X i.succ := he
            rw [he']
            simp
        have hunder : P.under (polynomialRing R k) = p := by
          ext a
          change Polynomial.C a ∈ q.map er ↔ a ∈ p
          rw [← Ideal.symm_apply_mem_of_equiv_iff, ← hkerₛ, ← hkerₖ]
          change (MvPolynomial.eval₂Hom
              (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
              (fun _ : Fin (k + 1) => 0)) (er.symm (Polynomial.C a)) = 0 ↔ _
          have haeval :
              (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
                (fun _ : Fin (k + 1) => 0)) (er.symm (Polynomial.C a)) =
                (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
                  (fun _ : Fin k => 0)) a := by
            simpa [RingHom.comp_apply] using congrArg (fun f => f a) heval
          simp only [RingHom.mem_ker]
          rw [haeval]
        letI : P.LiesOver p := ⟨hunder.symm⟩
        have hstep : q.height = p.height + 1 := by
          rw [← er.height_map q]
          exact Polynomial.height_eq_height_add_one p P
        have hstep' : q.height = ringKrullDim R + (k + 1) := by
          have ih' : (p.height : WithBot ℕ∞) = ringKrullDim R + k := by
            simpa [p] using ih
          calc
            (q.height : WithBot ℕ∞) = (p.height : WithBot ℕ∞) + 1 := by
              simpa using congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hstep
            _ = (ringKrullDim R + k) + 1 := by rw [ih']
            _ = ringKrullDim R + (k + 1) := by
              simp only [Nat.cast_add, add_assoc]
        simpa [q] using hstep'
  exact hdim n

end Formalization.Books.Exercises.Unit17
