import Formalization.Books.Fields.Unit26.Transcendence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Fields, Chapter 27: Linearly disjoint extensions

The source's compositum is Mathlib's supremum of two intermediate fields.
Linear disjointness is Mathlib's canonical `IntermediateField.LinearDisjoint`,
whose underlying multiplication map is the tensor-product map in the source.
The normal-extension decomposition uses the relative separable closure and the
fixed field of the full automorphism group.  The source's tensor-product
equality is represented by the canonical multiplication map and its induced
algebra equivalence.
-/

namespace Formalization.Books.Fields.Unit27

noncomputable section

open scoped TensorProduct

/-! ## The compositum and linear disjointness -/

/- `K ⊔ L` is the canonical compositum of two subextensions in an ambient
   field.  The following definitional identity exposes its source-facing
   generated-field description. -/
theorem compositum_eq_adjoin_union
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) :
    K ⊔ L = IntermediateField.adjoin k ((K : Set Ω) ∪ (L : Set Ω)) := by
  rfl

/- The lattice universal property is exactly the source's "smallest
   subfield" clause. -/
theorem compositum_is_smallest
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L M : IntermediateField k Ω) :
    K ⊔ L ≤ M ↔ K ≤ M ∧ L ≤ M := by
  exact sup_le_iff

/- The other two generated-field descriptions in the source use the field
   generated over one intermediate field by the other.  The fields are
   compared through their underlying subsets of the common ambient field. -/
theorem compositum_eq_adjoin_over_left
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) :
    ∀ x : Ω,
      x ∈ K ⊔ L ↔ x ∈ IntermediateField.adjoin L (K : Set Ω) := by
  intro x
  have h := IntermediateField.restrictScalars_adjoin_eq_sup (F := k) (E := Ω) L
    (K : Set Ω)
  rw [← show L ⊔ IntermediateField.adjoin k (K : Set Ω) = K ⊔ L by
    simp [IntermediateField.adjoin_self, sup_comm]]
  rw [← h]
  rfl

theorem compositum_eq_adjoin_over_right
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) :
    ∀ x : Ω,
      x ∈ K ⊔ L ↔ x ∈ IntermediateField.adjoin K (L : Set Ω) := by
  intro x
  have h := IntermediateField.restrictScalars_adjoin_eq_sup (F := k) (E := Ω) K
    (L : Set Ω)
  rw [← show K ⊔ IntermediateField.adjoin k (L : Set Ω) = K ⊔ L by
    simp [IntermediateField.adjoin_self]]
  rw [← h]
  rfl

/- Mathlib's definition is source-faithful: for intermediate fields in the
   same ambient field, `K.LinearDisjoint L` is the injectivity of the natural
   multiplication map from the tensor product. -/
theorem linear_disjoint_iff_tensor_product_multiplication_injective
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) :
    K.LinearDisjoint L ↔
      Function.Injective (K.toSubalgebra.mulMap L.toSubalgebra) := by
  rw [IntermediateField.linearDisjoint_iff',
    Subalgebra.linearDisjoint_iff_injective]

@[simp]
theorem tensor_product_multiplication_map_tmul
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) (x : K) (y : L) :
    K.toSubalgebra.mulMap L.toSubalgebra (x ⊗ₜ[k] y) = (x : Ω) * (y : Ω) := by
  rfl

/-! ## The embedding-dependence example -/

def realEighthRoot : ℝ := (2 : ℝ) ^ (1 / 8 : ℝ)

def realTwelfthRoot : ℝ := (2 : ℝ) ^ (1 / 12 : ℝ)

def realTwentyFourthRoot : ℝ := (2 : ℝ) ^ (1 / 24 : ℝ)

def rotatedEighthRoot : ℂ :=
  (realEighthRoot : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8)

abbrev realEighthRootField : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({realEighthRoot} : Set ℝ)

abbrev realTwelfthRootField : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({realTwelfthRoot} : Set ℝ)

abbrev realTwentyFourthRootField : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({realTwentyFourthRoot} : Set ℝ)

abbrev realRadicalCompositum : IntermediateField ℚ ℝ :=
  realEighthRootField ⊔ realTwelfthRootField

abbrev complexEighthRootField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({rotatedEighthRoot} : Set ℂ)

abbrev complexTwelfthRootField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({(realTwelfthRoot : ℂ)} : Set ℂ)

abbrev complexRadicalCompositum : IntermediateField ℚ ℂ :=
  complexEighthRootField ⊔ complexTwelfthRootField

/- The first embedding choice in the source gives the real compositum and its
   degree. -/
theorem real_radical_compositum_description :
    realRadicalCompositum = realTwentyFourthRootField := by
  have ha : realEighthRoot = realTwentyFourthRoot ^ 3 := by
    rw [realEighthRoot, realTwentyFourthRoot, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hb : realTwelfthRoot = realTwentyFourthRoot ^ 2 := by
    rw [realTwelfthRoot, realTwentyFourthRoot, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have htpos : 0 < realTwentyFourthRoot := by
    dsimp [realTwentyFourthRoot]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have ht : realTwentyFourthRoot ≠ 0 := ne_of_gt htpos
  have haC : realEighthRoot ∈ realRadicalCompositum :=
    (show realEighthRootField ≤ realRadicalCompositum from le_sup_left)
      (IntermediateField.subset_adjoin ℚ ({realEighthRoot} : Set ℝ) (by simp))
  have hbC : realTwelfthRoot ∈ realRadicalCompositum :=
    (show realTwelfthRootField ≤ realRadicalCompositum from le_sup_right)
      (IntermediateField.subset_adjoin ℚ ({realTwelfthRoot} : Set ℝ) (by simp))
  have htC : realTwentyFourthRoot ∈ realRadicalCompositum := by
    have hratio : realEighthRoot / realTwelfthRoot = realTwentyFourthRoot := by
      rw [ha, hb]
      field_simp [ht]
    rw [← hratio]
    exact div_mem haC hbC
  have hleft : realRadicalCompositum ≤ realTwentyFourthRootField := by
    apply sup_le
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      rw [ha]
      exact pow_mem (IntermediateField.subset_adjoin ℚ
        ({realTwentyFourthRoot} : Set ℝ) (by simp)) 3
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      rw [hb]
      exact pow_mem (IntermediateField.subset_adjoin ℚ
        ({realTwentyFourthRoot} : Set ℝ) (by simp)) 2
  have hright : realTwentyFourthRootField ≤ realRadicalCompositum := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact htC
  exact le_antisymm hleft hright

theorem real_radical_compositum_degree :
    Module.finrank ℚ realRadicalCompositum = 24 := by
  let f : Polynomial ℤ := Polynomial.X ^ 24 - Polynomial.C 2
  have hdeg : f.natDegree = 24 := by
    simpa [f] using
      (Polynomial.natDegree_X_pow_sub_C (R := ℤ) (n := 24) (r := (2 : ℤ)))
  have hm : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_sub_C (2 : ℤ) (by norm_num))
  have hP : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime := by
    simpa using
      (Ideal.isPrime_span_singleton_of_prime (α := ℤ)
        (Nat.prime_iff_prime_int.mp Nat.prime_two))
  have hfl : f.leadingCoeff ∉ Ideal.span ({(2 : ℤ)} : Set ℤ) := by
    rw [hm.leadingCoeff]
    intro h
    rw [Ideal.mem_span_singleton] at h
    obtain ⟨z, hz⟩ := h
    omega
  have hfP0 : ∀ n : ℕ, n < f.natDegree →
      f.coeff n ∈ Ideal.span ({(2 : ℤ)} : Set ℤ) := by
    intro n hn
    rw [hdeg] at hn
    by_cases h : n = 0
    · subst h
      rw [show f = Polynomial.X ^ 24 - Polynomial.C 2 by rfl,
        Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      norm_num [Ideal.mem_span_singleton]
    · have h24 : n ≠ 24 := by omega
      rw [show f = Polynomial.X ^ 24 - Polynomial.C 2 by rfl,
        Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      simp [h, h24]
  have hfP : ∀ n : ℕ, (↑n : WithBot ℕ) < f.degree →
      f.coeff n ∈ Ideal.span ({(2 : ℤ)} : Set ℤ) := by
    intro n hn
    exact hfP0 n (Polynomial.coe_lt_degree.1 hn)
  have hfd0 : 0 < f.degree := by
    rw [show f.degree = (24 : WithBot ℕ) by
      simpa [f] using
        (Polynomial.degree_X_pow_sub_C (R := ℤ) (n := 24) (by norm_num) (2 : ℤ))]
    norm_num
  have h0 : f.coeff 0 ∉ (Ideal.span ({(2 : ℤ)} : Set ℤ)) ^ 2 := by
    rw [Ideal.span_singleton_pow]
    simp [f]
    intro h
    rw [Ideal.mem_span_singleton] at h
    obtain ⟨z, hz⟩ := h
    omega
  have hi : Irreducible f :=
    Polynomial.irreducible_of_eisenstein_criterion hP hfl hfP hfd0 h0 hm.isPrimitive
  have hiQ : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).1 hi
  have hip : Irreducible (Polynomial.X ^ 24 - Polynomial.C (2 : ℚ)) := by
    convert hiQ using 1; norm_num [f]
    rw [Polynomial.C_ofNat]
  have hpmonic : (Polynomial.X ^ 24 - Polynomial.C (2 : ℚ)).Monic :=
    Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num)
  have hpow : realTwentyFourthRoot ^ 24 = 2 := by
    rw [realTwentyFourthRoot, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hroot :
      Polynomial.aeval (realTwentyFourthRoot : ℝ)
        (Polynomial.X ^ 24 - Polynomial.C (2 : ℚ)) = 0 := by
    simp [Polynomial.aeval_def, hpow]
  have htint : IsIntegral ℚ (realTwentyFourthRoot : ℝ) :=
    ⟨Polynomial.X ^ 24 - Polynomial.C (2 : ℚ), hpmonic, hroot⟩
  have hmin :
      minpoly ℚ (realTwentyFourthRoot : ℝ) =
        Polynomial.X ^ 24 - Polynomial.C (2 : ℚ) := by
    exact (minpoly.eq_of_irreducible_of_monic hip hroot hpmonic).symm
  calc
    Module.finrank ℚ realRadicalCompositum =
        Module.finrank ℚ realTwentyFourthRootField := by
          rw [real_radical_compositum_description]
    _ = (minpoly ℚ (realTwentyFourthRoot : ℝ)).natDegree :=
      IntermediateField.adjoin.finrank htint
    _ = 24 := by
      rw [hmin]
      simp

/- The second embedding choice maps the eighth-root generator to the rotated
   root.  These declarations record the source's two precise conclusions. -/
theorem complex_radical_compositum_contains_imaginary_unit :
    Complex.I ∈ complexRadicalCompositum := by
  have hreal : realEighthRoot ^ 6 = realTwelfthRoot ^ 9 := by
    rw [realEighthRoot, realTwelfthRoot, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hζ : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) ^ 6 = -Complex.I := by
    rw [← Complex.exp_nat_mul]
    convert congrArg Complex.exp
      (show (↑(6 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 8) =
        -(Real.pi / 2 * Complex.I) + 2 * Real.pi * Complex.I by ring) using 1
    rw [Complex.exp_add]
    rw [show -(Real.pi / 2 * Complex.I) = (-Real.pi / 2) * Complex.I by ring,
      Complex.exp_neg_pi_div_two_mul_I, Complex.exp_two_pi_mul_I, mul_one]
  have ha : rotatedEighthRoot ∈ complexRadicalCompositum :=
    (show complexEighthRootField ≤ complexRadicalCompositum from le_sup_left)
      (IntermediateField.subset_adjoin ℚ ({rotatedEighthRoot} : Set ℂ) (by simp))
  have hb : (realTwelfthRoot : ℂ) ∈ complexRadicalCompositum :=
    (show complexTwelfthRootField ≤ complexRadicalCompositum from le_sup_right)
      (IntermediateField.subset_adjoin ℚ ({(realTwelfthRoot : ℂ)} : Set ℂ) (by simp))
  have hp : rotatedEighthRoot ^ 6 / (realTwelfthRoot : ℂ) ^ 9 ∈ complexRadicalCompositum :=
    div_mem (pow_mem ha 6) (pow_mem hb 9)
  have hpow : rotatedEighthRoot ^ 6 / (realTwelfthRoot : ℂ) ^ 9 = -Complex.I := by
    rw [rotatedEighthRoot, mul_pow, hζ]
    have hc : (realEighthRoot : ℂ) ^ 6 = (realTwelfthRoot : ℂ) ^ 9 := by
      exact_mod_cast hreal
    rw [hc]
    have htr : 0 < realTwelfthRoot := by
      dsimp [realTwelfthRoot]
      exact Real.rpow_pos_of_pos (by norm_num) _
    have ht : (realTwelfthRoot : ℂ) ≠ 0 := by
      exact_mod_cast htr.ne'
    field_simp [ht]
  have hneg : Complex.I = -(rotatedEighthRoot ^ 6 / (realTwelfthRoot : ℂ) ^ 9) := by
    rw [hpow]
    simp
  rw [hneg]
  exact neg_mem hp

private theorem irreducible_X_pow_sub_C_two {n : ℕ} (hn : 0 < n) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (2 : ℚ)) := by
  let f : Polynomial ℤ := Polynomial.X ^ n - Polynomial.C 2
  have hdeg : f.natDegree = n := by
    simpa [f] using
      (Polynomial.natDegree_X_pow_sub_C (R := ℤ) (n := n) (r := (2 : ℤ)))
  have hm : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_sub_C (2 : ℤ) hn.ne')
  have hP : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime := by
    simpa using
      (Ideal.isPrime_span_singleton_of_prime (α := ℤ)
        (Nat.prime_iff_prime_int.mp Nat.prime_two))
  have hfl : f.leadingCoeff ∉ Ideal.span ({(2 : ℤ)} : Set ℤ) := by
    rw [hm.leadingCoeff]
    intro h
    rw [Ideal.mem_span_singleton] at h
    obtain ⟨z, hz⟩ := h
    omega
  have hfP0 : ∀ k : ℕ, k < f.natDegree →
      f.coeff k ∈ Ideal.span ({(2 : ℤ)} : Set ℤ) := by
    intro k hk
    rw [hdeg] at hk
    by_cases h : k = 0
    · subst h
      rw [show f = Polynomial.X ^ n - Polynomial.C 2 by rfl,
        Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      by_cases hn0 : 0 = n
      · exact (hn.ne' hn0.symm).elim
      · simp [hn0, Ideal.mem_span_singleton]
    · have hN : k ≠ n := by omega
      rw [show f = Polynomial.X ^ n - Polynomial.C 2 by rfl,
        Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      simp [h, hN]
  have hfP : ∀ k : ℕ, (↑k : WithBot ℕ) < f.degree →
      f.coeff k ∈ Ideal.span ({(2 : ℤ)} : Set ℤ) := by
    intro k hk
    exact hfP0 k (Polynomial.coe_lt_degree.1 hk)
  have hfd0 : 0 < f.degree := by
    rw [show f.degree = (n : WithBot ℕ) by
      simpa [f] using
        (Polynomial.degree_X_pow_sub_C (R := ℤ) (n := n) hn (2 : ℤ))]
    exact_mod_cast hn
  have h0 : f.coeff 0 ∉ (Ideal.span ({(2 : ℤ)} : Set ℤ)) ^ 2 := by
    rw [Ideal.span_singleton_pow]
    simp [f, hn.ne']
    intro h
    rw [Ideal.mem_span_singleton] at h
    obtain ⟨z, hz⟩ := h
    omega
  have hi : Irreducible f :=
    Polynomial.irreducible_of_eisenstein_criterion hP hfl hfP hfd0 h0 hm.isPrimitive
  have hiQ : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).1 hi
  convert hiQ using 1
  norm_num [f]
  rw [Polynomial.C_ofNat]

theorem complex_radical_compositum_degree :
    Module.finrank ℚ complexRadicalCompositum = 48 := by
  have hKreal : ∀ z : complexTwelfthRootField, Complex.im (z : ℂ) = 0 := by
    intro z
    refine IntermediateField.adjoin_induction (F := ℚ) (E := ℂ)
      (s := ({(realTwelfthRoot : ℂ)} : Set ℂ))
      (p := fun x _ => Complex.im x = 0) ?_ ?_ ?_ ?_ ?_ z.2 <;>
      simp_all [realTwelfthRoot]
  have hβint : IsIntegral ℚ (realTwelfthRoot : ℝ) := by
    have hpow : realTwelfthRoot ^ 12 = 2 := by
      rw [realTwelfthRoot, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hp : (Polynomial.X ^ 12 - Polynomial.C (2 : ℚ)).Monic :=
      Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num)
    have hroot :
        Polynomial.aeval (realTwelfthRoot : ℝ)
          (Polynomial.X ^ 12 - Polynomial.C (2 : ℚ)) = 0 := by
      simp [Polynomial.aeval_def, hpow]
    exact ⟨_, hp, hroot⟩
  have hβmin :
      minpoly ℚ (realTwelfthRoot : ℝ) =
        Polynomial.X ^ 12 - Polynomial.C (2 : ℚ) := by
    have hroot :
        Polynomial.aeval (realTwelfthRoot : ℝ)
          (Polynomial.X ^ 12 - Polynomial.C (2 : ℚ)) = 0 := by
      have hpow : realTwelfthRoot ^ 12 = 2 := by
        rw [realTwelfthRoot, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      simp [Polynomial.aeval_def, hpow]
    exact (minpoly.eq_of_irreducible_of_monic
      (irreducible_X_pow_sub_C_two (n := 12) (by norm_num)) hroot
      (Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num))).symm
  have hβintC : IsIntegral ℚ (realTwelfthRoot : ℂ) := by
    have hpow : realTwelfthRoot ^ 12 = 2 := by
      rw [realTwelfthRoot, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hroot :
        Polynomial.aeval (realTwelfthRoot : ℂ)
          (Polynomial.X ^ 12 - Polynomial.C (2 : ℚ)) = 0 := by
      have hpowC : (realTwelfthRoot : ℂ) ^ 12 = (2 : ℂ) := by
        exact_mod_cast hpow
      simp [Polynomial.aeval_def, hpowC]
    exact ⟨_, Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num), hroot⟩
  have hβminC :
      minpoly ℚ (realTwelfthRoot : ℂ) =
        Polynomial.X ^ 12 - Polynomial.C (2 : ℚ) := by
    have hpow : realTwelfthRoot ^ 12 = 2 := by
      rw [realTwelfthRoot, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hpowC : (realTwelfthRoot : ℂ) ^ 12 = (2 : ℂ) := by
      exact_mod_cast hpow
    have hroot :
        Polynomial.aeval (realTwelfthRoot : ℂ)
          (Polynomial.X ^ 12 - Polynomial.C (2 : ℚ)) = 0 := by
      simp [Polynomial.aeval_def, hpowC]
    exact (minpoly.eq_of_irreducible_of_monic
      (irreducible_X_pow_sub_C_two (n := 12) (by norm_num)) hroot
      (Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num))).symm
  have hKdim : Module.finrank ℚ complexTwelfthRootField = 12 := by
    change Module.finrank ℚ
      (IntermediateField.adjoin ℚ ({(realTwelfthRoot : ℂ)} : Set ℂ)) = 12
    rw [IntermediateField.adjoin.finrank hβintC, hβminC]
    simp
  have hr8int : IsIntegral ℚ (realEighthRoot : ℝ) := by
    have hpow : realEighthRoot ^ 8 = 2 := by
      rw [realEighthRoot, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hp : (Polynomial.X ^ 8 - Polynomial.C (2 : ℚ)).Monic :=
      Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num)
    have hroot :
        Polynomial.aeval (realEighthRoot : ℝ)
          (Polynomial.X ^ 8 - Polynomial.C (2 : ℚ)) = 0 := by
      simp [Polynomial.aeval_def, hpow]
    exact ⟨_, hp, hroot⟩
  have hr8min :
      minpoly ℚ (realEighthRoot : ℝ) =
        Polynomial.X ^ 8 - Polynomial.C (2 : ℚ) := by
    have hroot :
        Polynomial.aeval (realEighthRoot : ℝ)
          (Polynomial.X ^ 8 - Polynomial.C (2 : ℚ)) = 0 := by
      have hpow : realEighthRoot ^ 8 = 2 := by
        rw [realEighthRoot, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      simp [Polynomial.aeval_def, hpow]
    exact (minpoly.eq_of_irreducible_of_monic
      (irreducible_X_pow_sub_C_two (n := 8) (by norm_num)) hroot
      (Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num))).symm
  have hr8notK : (realEighthRoot : ℂ) ∉ (complexTwelfthRootField : Set ℂ) := by
    intro hr8K
    let x : complexTwelfthRootField := ⟨realEighthRoot, hr8K⟩
    have hxint : IsIntegral ℚ (x : complexTwelfthRootField) := by
      have hroot :
          Polynomial.aeval (x : complexTwelfthRootField)
            (Polynomial.X ^ 8 - Polynomial.C (2 : ℚ)) = 0 := by
        have hpow : realEighthRoot ^ 8 = 2 := by
          rw [realEighthRoot, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        have hxpow : (x : complexTwelfthRootField) ^ 8 = (2 : complexTwelfthRootField) := by
          have hxpowC : (realEighthRoot : ℂ) ^ 8 = (2 : ℂ) := by
            exact_mod_cast hpow
          apply Subtype.ext
          exact hxpowC
        simp [Polynomial.aeval_def, hxpow]
      exact ⟨_, Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num), hroot⟩
    have hdvd := minpoly.degree_dvd hxint
    have hminx :
        minpoly ℚ (x : complexTwelfthRootField) =
          Polynomial.X ^ 8 - Polynomial.C (2 : ℚ) := by
      have hroot :
          Polynomial.aeval (x : complexTwelfthRootField)
            (Polynomial.X ^ 8 - Polynomial.C (2 : ℚ)) = 0 := by
        have hpow : realEighthRoot ^ 8 = 2 := by
          rw [realEighthRoot, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        have hxpow : (x : complexTwelfthRootField) ^ 8 = (2 : complexTwelfthRootField) := by
          have hxpowC : (realEighthRoot : ℂ) ^ 8 = (2 : ℂ) := by
            exact_mod_cast hpow
          apply Subtype.ext
          exact hxpowC
        simp [Polynomial.aeval_def, hxpow]
      exact (minpoly.eq_of_irreducible_of_monic
        (irreducible_X_pow_sub_C_two (n := 8) (by norm_num)) hroot
        (Polynomial.monic_X_pow_sub_C (2 : ℚ) (by norm_num))).symm
    rw [hminx, hKdim] at hdvd
    norm_num at hdvd
  have hroot6 : realTwelfthRoot ^ 6 = Real.sqrt 2 := by
    rw [realTwelfthRoot, ← Real.rpow_natCast,
      Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hzeta :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) =
        (1 + Complex.I) / (realTwelfthRoot : ℂ) ^ 6 := by
    have hexp :
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) =
          (Real.sqrt 2 : ℂ)⁻¹ * (1 + Complex.I) := by
      have he : 2 * (Real.pi : ℂ) * Complex.I / 8 =
          (Real.pi / 4 : ℝ) * Complex.I := by
        norm_num [div_eq_mul_inv]
        ring
      rw [he, Complex.exp_ofReal_mul_I, Real.cos_pi_div_four,
        Real.sin_pi_div_four]
      simp [div_eq_mul_inv]
      have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
      field_simp [hsqrt]
      have hsqrtC : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by
        exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
      rw [hsqrtC]
    have hroot6C : (realTwelfthRoot : ℂ) ^ 6 = (Real.sqrt 2 : ℂ) := by
      exact_mod_cast hroot6
    rw [hexp, hroot6C]
    ring
  let K := complexTwelfthRootField
  let L : IntermediateField K ℂ :=
    IntermediateField.adjoin K ({Complex.I} : Set ℂ)
  have hLrepr : ∀ z : L, ∃ a b : K, (z : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := by
    intro z
    refine IntermediateField.adjoin_induction (F := K) (E := ℂ)
      (s := ({Complex.I} : Set ℂ))
      (p := fun x _ => ∃ a b : K, x = (a : ℂ) + (b : ℂ) * Complex.I)
      ?_ ?_ ?_ ?_ ?_ z.2
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨0, 1, by simp⟩
    · intro x
      exact ⟨x, 0, by simp⟩
    · intro x y hx hy hxp hyp
      obtain ⟨a, b, rfl⟩ := hxp
      obtain ⟨c, d, rfl⟩ := hyp
      refine ⟨a + c, b + d, ?_⟩
      push_cast
      ring
    · intro x hx hxp
      obtain ⟨a, b, rfl⟩ := hxp
      by_cases hzero : (a : ℂ) + (b : ℂ) * Complex.I = 0
      · exact ⟨0, 0, by simp [hzero]⟩
      · have hden : a ^ 2 + b ^ 2 ≠ 0 := by
          intro hden
          apply hzero
          have hdenC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 0 := by
            exact_mod_cast hden
          have hdenR := congrArg Complex.re hdenC
          simp [pow_two, Complex.mul_re, hKreal a, hKreal b] at hdenR
          apply Complex.normSq_eq_zero.mp
          simp [Complex.normSq, hKreal a, hKreal b]
          nlinarith [hdenR, sq_nonneg (a : ℂ).re, sq_nonneg (b : ℂ).re]
        have hdenC : (a ^ 2 + b ^ 2 : K) ≠ 0 := hden
        have hdenC' : ((a ^ 2 + b ^ 2 : K) : ℂ) ≠ 0 := by
          exact_mod_cast hdenC
        have hprod :
            ((a : ℂ) + (b : ℂ) * Complex.I) *
                ((a : ℂ) - (b : ℂ) * Complex.I) =
              ((a ^ 2 + b ^ 2 : K) : ℂ) := by
          push_cast
          ring_nf
          rw [Complex.I_sq]
          ring
        have hmul :
            ((a : ℂ) + (b : ℂ) * Complex.I) *
                (((a ^ 2 + b ^ 2 : K) : ℂ)⁻¹ *
                  ((a : ℂ) - (b : ℂ) * Complex.I)) = 1 := by
          calc
            _ = (((a : ℂ) + (b : ℂ) * Complex.I) *
                ((a : ℂ) - (b : ℂ) * Complex.I)) *
                  ((a ^ 2 + b ^ 2 : K) : ℂ)⁻¹ := by ring
            _ = 1 := by rw [hprod, mul_inv_cancel₀ hdenC']
        have hy :
            ((a ^ 2 + b ^ 2 : K) : ℂ)⁻¹ *
                  ((a : ℂ) - (b : ℂ) * Complex.I) =
              ((a / (a ^ 2 + b ^ 2) : K) : ℂ) +
                ((-(b / (a ^ 2 + b ^ 2) : K) : K) : ℂ) * Complex.I := by
          push_cast
          field_simp [hdenC]
          ring
        rw [hy] at hmul
        exact ⟨a / (a ^ 2 + b ^ 2), -(b / (a ^ 2 + b ^ 2)),
          (mul_eq_one_iff_inv_eq₀ hzero).mp hmul⟩
    · intro x y hx hy hxp hyp
      obtain ⟨a, b, rfl⟩ := hxp
      obtain ⟨c, d, rfl⟩ := hyp
      refine ⟨a * c - b * d, a * d + b * c, ?_⟩
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
  have hαnotL : rotatedEighthRoot ∉ (L : Set ℂ) := by
    intro hα
    have hζL : (1 + Complex.I) / (realTwelfthRoot : ℂ) ^ 6 ∈ L := by
      apply div_mem
      · exact add_mem (algebraMap_mem L (1 : K))
          (IntermediateField.subset_adjoin K _ (by simp))
      · exact pow_mem (algebraMap_mem L (⟨realTwelfthRoot, by
          exact IntermediateField.subset_adjoin ℚ _ (by simp)⟩ : K)) 6
    have hαfactor :
        rotatedEighthRoot = (realEighthRoot : ℂ) *
          ((1 + Complex.I) / (realTwelfthRoot : ℂ) ^ 6) := by
      rw [rotatedEighthRoot, hzeta]
    have hratio :
        rotatedEighthRoot / ((1 + Complex.I) / (realTwelfthRoot : ℂ) ^ 6) =
          (realEighthRoot : ℂ) := by
      rw [hαfactor]
      have hβne : (realTwelfthRoot : ℂ) ≠ 0 := by
        exact_mod_cast (Real.rpow_pos_of_pos (by norm_num) _).ne'
      have hplus : (1 + Complex.I : ℂ) ≠ 0 := by
        intro h
        have := congrArg Complex.im h
        norm_num at this
      field_simp [hβne, hplus]
    have hr8L : (realEighthRoot : ℂ) ∈ L := by
      rw [← hratio]
      exact div_mem hα hζL
    obtain ⟨a, b, hab⟩ := hLrepr ⟨realEighthRoot, hr8L⟩
    have him := congrArg Complex.im hab
    have hb_re : (b : ℂ).re = 0 := by
      simpa [hKreal a, hKreal b] using him.symm
    have hb0 : b = 0 := by
      apply Subtype.ext
      apply Complex.ext
      · simpa [hKreal b] using hb_re
      · exact hKreal b
    have hr8K : (realEighthRoot : ℂ) ∈ (K : Set ℂ) := by
      rw [show (realEighthRoot : ℂ) = (a : ℂ) by simpa [hb0] using hab]
      exact a.2
    exact hr8notK hr8K
  have hInotK : (Complex.I : ℂ) ∉ (K : Set ℂ) := by
    intro h
    have := hKreal ⟨Complex.I, h⟩
    norm_num at this
  have hIroot :
      Polynomial.aeval (Complex.I : ℂ)
        (Polynomial.X ^ 2 - Polynomial.C (-1 : K)) = 0 := by
    simp [Polynomial.aeval_def, Complex.I_sq]
  have hIint : IsIntegral K (Complex.I : ℂ) := by
    exact ⟨_, Polynomial.monic_X_pow_sub_C (-1 : K) (by norm_num), hIroot⟩
  have hIdeg_le : (minpoly K (Complex.I : ℂ)).natDegree ≤ 2 := by
    have hdeg := Polynomial.natDegree_le_of_dvd (minpoly.dvd K _ hIroot)
      (Polynomial.X_pow_sub_C_ne_zero (by norm_num) (-1 : K))
    simpa only [Polynomial.natDegree_X_pow_sub_C] using hdeg
  have hIdeg_ne_one : (minpoly K (Complex.I : ℂ)).natDegree ≠ 1 := by
    intro hdeg
    have hmem := (minpoly.natDegree_eq_one_iff.mp hdeg)
    obtain ⟨a, ha⟩ := hmem
    apply hInotK
    rw [← ha]
    exact a.2
  have hLdim : Module.finrank K L = 2 := by
    calc
      Module.finrank K L = (minpoly K (Complex.I : ℂ)).natDegree :=
        IntermediateField.adjoin.finrank hIint
      _ = 2 := by
        have hpos := minpoly.natDegree_pos hIint
        omega
  have hαfactor :
      rotatedEighthRoot = (realEighthRoot : ℂ) *
        ((1 + Complex.I) / (realTwelfthRoot : ℂ) ^ 6) := by
    rw [rotatedEighthRoot, hzeta]
  have hr8sq : realEighthRoot ^ 2 = realTwelfthRoot ^ 3 := by
    rw [realEighthRoot, realTwelfthRoot, ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hβ12 : (realTwelfthRoot : ℂ) ^ 12 = (2 : ℂ) := by
    have hβ12' : realTwelfthRoot ^ 12 = (2 : ℝ) := by
      rw [realTwelfthRoot, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    exact_mod_cast hβ12'
  have hα2 :
      rotatedEighthRoot ^ 2 = Complex.I * (realTwelfthRoot : ℂ) ^ 3 := by
    rw [hαfactor]
    have hβne : (realTwelfthRoot : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (by norm_num) _).ne'
    have hreal : (realEighthRoot : ℂ) ^ 2 =
        (realTwelfthRoot : ℂ) ^ 3 := by exact_mod_cast hr8sq
    field_simp [hβne]
    rw [hreal]
    ring_nf
    rw [Complex.I_sq]
    rw [show (realTwelfthRoot : ℂ) ^ 15 =
      (realTwelfthRoot : ℂ) ^ 3 * (realTwelfthRoot : ℂ) ^ 12 by ring, hβ12]
    ring
  let M : IntermediateField L ℂ :=
    IntermediateField.adjoin L ({rotatedEighthRoot} : Set ℂ)
  have hβL : (realTwelfthRoot : ℂ) ∈ L := by
    exact algebraMap_mem L (⟨realTwelfthRoot,
      IntermediateField.subset_adjoin ℚ _ (by simp)⟩ : K)
  have hIL : (Complex.I : ℂ) ∈ L := IntermediateField.subset_adjoin K _ (by simp)
  let cα : L := ⟨Complex.I * (realTwelfthRoot : ℂ) ^ 3,
    mul_mem hIL (pow_mem hβL 3)⟩
  have hαroot :
      Polynomial.aeval (rotatedEighthRoot : ℂ)
        (Polynomial.X ^ 2 -
          Polynomial.C cα) = 0 := by
    simp [Polynomial.aeval_def, cα, hα2]
  have hαintL : IsIntegral L (rotatedEighthRoot : ℂ) := by
    exact ⟨_, Polynomial.monic_X_pow_sub_C _ (by norm_num), hαroot⟩
  have hαdeg_le :
      (minpoly L (rotatedEighthRoot : ℂ)).natDegree ≤ 2 := by
    have hdeg := Polynomial.natDegree_le_of_dvd (minpoly.dvd L _ hαroot)
      (Polynomial.X_pow_sub_C_ne_zero (by norm_num) cα)
    simpa only [Polynomial.natDegree_X_pow_sub_C] using hdeg
  have hαdeg_ne_one :
      (minpoly L (rotatedEighthRoot : ℂ)).natDegree ≠ 1 := by
    intro hdeg
    have hmem := (minpoly.natDegree_eq_one_iff.mp hdeg)
    obtain ⟨a, ha⟩ := hmem
    apply hαnotL
    rw [← ha]
    exact a.2
  have hMdim : Module.finrank L M = 2 := by
    calc
      Module.finrank L M =
          (minpoly L (rotatedEighthRoot : ℂ)).natDegree :=
        IntermediateField.adjoin.finrank hαintL
      _ = 2 := by
        have hpos := minpoly.natDegree_pos hαintL
        omega
  have hM_eq : M.restrictScalars ℚ = complexRadicalCompositum := by
    have hLcomp : L.restrictScalars ℚ ≤ complexRadicalCompositum := by
      rintro x hx
      change x ∈ L at hx
      dsimp [L] at hx
      refine IntermediateField.adjoin_induction (F := K) (E := ℂ)
        (s := ({Complex.I} : Set ℂ))
        (p := fun x _ => x ∈ complexRadicalCompositum)
        ?_ ?_ ?_ ?_ ?_ hx
      · intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        exact complex_radical_compositum_contains_imaginary_unit
      · intro x
        exact (show complexTwelfthRootField ≤ complexRadicalCompositum from le_sup_right) x.2
      · intro x y hx hy hxp hyp
        exact add_mem hxp hyp
      · intro x hx hxp
        exact inv_mem hxp
      · intro x y hx hy hxp hyp
        exact mul_mem hxp hyp
    have hαcomp : rotatedEighthRoot ∈ complexRadicalCompositum := by
      exact (show complexEighthRootField ≤ complexRadicalCompositum from le_sup_left)
        (IntermediateField.subset_adjoin ℚ _ (by simp))
    apply le_antisymm
    · rintro x hx
      change x ∈ M at hx
      dsimp [M] at hx
      refine IntermediateField.adjoin_induction (F := L) (E := ℂ)
        (s := ({rotatedEighthRoot} : Set ℂ))
        (p := fun x _ => x ∈ complexRadicalCompositum)
        ?_ ?_ ?_ ?_ ?_ hx
      · intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        exact hαcomp
      · intro x
        exact hLcomp x.2
      · intro x y hx hy hxp hyp
        exact add_mem hxp hyp
      · intro x hx hxp
        exact inv_mem hxp
      · intro x y hx hy hxp hyp
        exact mul_mem hxp hyp
    · rw [complexRadicalCompositum]
      apply sup_le
      · rw [IntermediateField.adjoin_le_iff]
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        exact IntermediateField.subset_adjoin L _ (by simp)
      · rw [IntermediateField.adjoin_le_iff]
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        exact algebraMap_mem M (⟨(realTwelfthRoot : ℂ), hβL⟩ : L)
  have htower₀ := Module.finrank_mul_finrank ℚ K M
  have htower₁ := Module.finrank_mul_finrank K L M
  calc
    Module.finrank ℚ complexRadicalCompositum =
        Module.finrank ℚ (M.restrictScalars ℚ) := by rw [hM_eq]
    _ = Module.finrank ℚ M := by rfl
    _ = Module.finrank ℚ K * Module.finrank K M := htower₀.symm
    _ = 48 := by
      rw [← htower₁, hKdim, hLdim, hMdim]

theorem real_and_complex_radical_composita_not_isomorphic :
    ¬ Nonempty (realRadicalCompositum ≃+* complexRadicalCompositum) := by
  rintro ⟨e⟩
  let z : complexRadicalCompositum :=
    ⟨Complex.I, complex_radical_compositum_contains_imaginary_unit⟩
  let x : realRadicalCompositum := e.symm z
  have hx : x ^ 2 = -1 := by
    apply e.injective
    rw [map_pow, map_neg, map_one]
    have hxe : e x = z := by
      simp [x]
    rw [hxe]
    ext
    simp [z]
  have hxval : (x : ℝ) ^ 2 = -1 := congrArg Subtype.val hx
  nlinarith [sq_nonneg (x : ℝ)]

/-! ## Normal extensions and their separable/inseparable parts -/

/- These are source-facing names for Mathlib's canonical constructions, not
   parallel definitions: the separable part is `separableClosure`, and the
   inseparable part is the fixed field of all `F`-automorphisms of `E`. -/
noncomputable abbrev normalSeparablePart
    (F E : Type*) [Field F] [Field E] [Algebra F E] : IntermediateField F E :=
  separableClosure F E

noncomputable abbrev normalInseparablePart
    (F E : Type*) [Field F] [Field E] [Algebra F E] : IntermediateField F E :=
  IntermediateField.fixedField (⊤ : Subgroup Gal(E / F))

/- The map is the canonical tensor-product multiplication map into the
   ambient field. -/
noncomputable def normalExtensionTensorProductMap
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    (normalSeparablePart F E ⊗[F] normalInseparablePart F E) →ₐ[F] E :=
  Algebra.TensorProduct.productMap
    (normalSeparablePart F E).val (normalInseparablePart F E).val

@[simp]
theorem normalExtensionTensorProductMap_tmul
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : normalSeparablePart F E) (y : normalInseparablePart F E) :
    normalExtensionTensorProductMap (F := F) (E := E) (x ⊗ₜ[F] y) =
      (x : E) * (y : E) := by
  rfl

private theorem normal_fixedField_top_isPurelyInseparable
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    IsPurelyInseparable F
      (IntermediateField.fixedField (⊤ : Subgroup Gal(E / F))) := by
  rw [isPurelyInseparable_iff]
  intro x
  refine ⟨IntermediateField.coe_isIntegral_iff.mp
    ((inferInstance : Normal F E).isIntegral (x : E)), ?_⟩
  intro hsep
  have hroot :
      Polynomial.aeval (x : E) (minpoly F (x : E)) = 0 := minpoly.aeval F (x : E)
  have hroots :
      ∀ y ∈ (minpoly F (x : E)).map (algebraMap F E) |>.roots, y = (x : E) := by
    intro y hy
    have hy' : Polynomial.aeval y (minpoly F (x : E)) = 0 := by
      rw [Polynomial.aeval_def]
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero
        (minpoly.ne_zero ((inferInstance : Normal F E).isIntegral (x : E))))] at hy
      rw [Polynomial.IsRoot.def] at hy
      simpa only [Polynomial.eval₂_at_apply, Polynomial.eval_map] using hy
    obtain ⟨σ, hσ⟩ :=
      IntermediateField.exists_algHom_of_adjoin_splits_of_aeval
        (F := F) (E := E) (K := E) (S := (Set.univ : Set E))
        (fun s _ => ⟨(inferInstance : Normal F E).isIntegral s,
          (inferInstance : Normal F E).splits s⟩)
        (IntermediateField.adjoin_univ F E)
        hy'
    have hfix : σ (x : E) = (x : E) := by
      have hxfix' :=
        (IntermediateField.mem_fixedField_iff (H := (⊤ : Subgroup Gal(E / F)))
          (x : E)).mp x.2
      let σ' : Gal(E / F) :=
        AlgEquiv.ofBijective σ (AlgHom.normal_bijective F E E σ)
      have hfix' : σ' (x : E) = (x : E) := hxfix' σ' (Subgroup.mem_top σ')
      simpa [σ'] using hfix'
    exact hσ.symm.trans hfix
  have hsep_poly : (minpoly F (x : E)).Separable := by
    change (minpoly F x).Separable at hsep
    rw [IntermediateField.minpoly_eq] at hsep
    exact hsep
  have hrootE :
      ((minpoly F (x : E)).map (algebraMap F E)).eval (x : E) = 0 := by
    simpa only [Polynomial.eval_map, Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hroot
  have hsplitE :
      (((minpoly F (x : E)).map (algebraMap F E)).map (RingHom.id E)).Splits := by
    simpa only [Polynomial.map_id] using
      ((inferInstance : Normal F E).splits (x : E))
  have hpoly :=
    Polynomial.eq_X_sub_C_of_separable_of_root_eq
      (hsep_poly.map) hrootE hsplitE
        (by simpa only [Polynomial.map_id, RingHom.id_apply] using hroots)
  have hmonic :
      (minpoly F (x : E)).map (algebraMap F E) |>.Monic :=
    (minpoly.monic ((inferInstance : Normal F E).isIntegral (x : E))).map _
  rw [hmonic.leadingCoeff] at hpoly
  have hcoef := congrArg (fun q : Polynomial E => q.coeff 0) hpoly
  refine ⟨-(minpoly F (x : E)).coeff 0, ?_⟩
  apply Subtype.ext
  have hneg := congrArg (fun z : E => -z) hcoef.symm
  simpa using hneg.symm

private theorem normal_fixedField_top_sup_separableClosure_eq_top_of_finite
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E]
    [FiniteDimensional F E] :
    separableClosure F E ⊔
        IntermediateField.fixedField (⊤ : Subgroup Gal(E / F)) = ⊤ := by
  let S : IntermediateField F E := separableClosure F E
  let I : IntermediateField F E :=
    IntermediateField.fixedField (⊤ : Subgroup Gal(E / F))
  let L : IntermediateField F E := S ⊔ I
  letI : IsPurelyInseparable F I :=
    normal_fixedField_top_isPurelyInseparable (F := F) (E := E)
  have hld : S.LinearDisjoint I :=
    S.linearDisjoint_of_isPurelyInseparable_of_isSeparable I
  letI : FiniteDimensional F I := by infer_instance
  letI : FiniteDimensional F S := by infer_instance
  have hcard : Nat.card (Gal(E / F)) = Field.finSepDegree F E :=
    by
      have hcard' : Nat.card (E →ₐ[F] AlgebraicClosure E) =
          Nat.card (Gal(E / F)) :=
        Nat.card_congr (Normal.algHomEquivAut F (AlgebraicClosure E) E)
      simpa [Field.finSepDegree] using hcard'.symm
  have hSI : Module.finrank F S = Module.finrank I E := by
    calc
      Module.finrank F S = Field.finSepDegree F E := by
        rw [Field.finSepDegree_eq]
        change Module.finrank F S =
          Cardinal.toNat (Module.rank F (separableClosure F E))
        rw [show separableClosure F E = S by rfl]
        rw [← Cardinal.toNat_natCast (Module.finrank F S)]
        congr 1
        exact Module.finrank_eq_rank F S
      _ = Nat.card (Gal(E / F)) := hcard.symm
      _ = Module.finrank I E := by
        simpa [I] using
          (IntermediateField.finrank_fixedField_eq_card
            (F := F) (E := E) (H := (⊤ : Subgroup Gal(E / F)))).symm
  have hsup : Module.finrank F L =
      Module.finrank F S * Module.finrank F I := by
    exact hld.finrank_sup
  have hLfin : Module.finrank F L = Module.finrank F E := by
    calc
      Module.finrank F L =
          Module.finrank F S * Module.finrank F I := hsup
      _ = Module.finrank F I * Module.finrank I E := by
        rw [hSI]
        ac_rfl
      _ = Module.finrank F E :=
        Module.finrank_mul_finrank F I E
  have hmul := Module.finrank_mul_finrank F L E
  rw [hLfin] at hmul
  have hLE : Module.finrank L E = 1 := by
    nlinarith [Module.finrank_pos (R := F) (M := E)]
  rw [IntermediateField.finrank_eq_one_iff_eq_top] at hLE
  exact hLE

private theorem finite_adjoin_isFiniteDimensional
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (s : Set E) (hs : s.Finite)
    (hints : ∀ x ∈ s, IsIntegral F x) :
    FiniteDimensional F (IntermediateField.adjoin F s) := by
  classical
  revert hints
  refine Set.Finite.induction_on s hs ?_ ?_
  · intro hints
    rw [IntermediateField.adjoin_empty]
    infer_instance
  · intro a t ha ht ih hints
    let K : IntermediateField F E := IntermediateField.adjoin F t
    let L : IntermediateField K E :=
      IntermediateField.adjoin K ({a} : Set E)
    letI : FiniteDimensional F K := ih (fun z hz => hints z (Or.inr hz))
    have hxK : IsIntegral K a := IsIntegral.tower_top (hints a (Or.inl rfl))
    letI : FiniteDimensional K L :=
      IntermediateField.adjoin.finiteDimensional hxK
    have hsup : K ⊔ IntermediateField.adjoin F ({a} : Set E) =
        IntermediateField.adjoin F (insert a t) := by
      apply le_antisymm
      · apply sup_le
        · rw [IntermediateField.adjoin_le_iff]
          intro z hz
          exact IntermediateField.subset_adjoin F (insert a t) (Or.inr hz)
        · rw [IntermediateField.adjoin_le_iff]
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst z
          exact IntermediateField.subset_adjoin F (insert a t) (Or.inl rfl)
      · rw [IntermediateField.adjoin_le_iff]
        intro z hz
        rcases hz with hza | hz
        · rw [hza]
          exact (show IntermediateField.adjoin F ({a} : Set E) ≤
              K ⊔ IntermediateField.adjoin F ({a} : Set E) from le_sup_right)
            (IntermediateField.subset_adjoin F _ (by simp))
        · change z ∈ K ⊔ IntermediateField.adjoin F ({a} : Set E)
          exact (show K ≤ K ⊔ IntermediateField.adjoin F ({a} : Set E) from le_sup_left)
            (IntermediateField.subset_adjoin F t hz)
    have hrest : L.restrictScalars F =
        K ⊔ IntermediateField.adjoin F ({a} : Set E) := by
      simpa [L] using
        (IntermediateField.restrictScalars_adjoin_eq_sup (F := F) (E := E)
          K ({a} : Set E))
    have hfin : FiniteDimensional F (L.restrictScalars F) := by
      change Module.Finite F L
      exact Module.Finite.trans K L
    rw [← hsup, ← hrest]
    exact hfin

private theorem normal_fixedField_top_sup_separableClosure_eq_top
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    separableClosure F E ⊔
        IntermediateField.fixedField (⊤ : Subgroup Gal(E / F)) = ⊤ := by
  apply top_unique
  intro x hx
  let p := minpoly F x
  let N : IntermediateField F E :=
    IntermediateField.adjoin F (p.rootSet E)
  have hpmap : (p.map (algebraMap F E)).Splits :=
    (inferInstance : Normal F E).splits x
  have hNsplit : p.IsSplittingField F N := by
    exact IntermediateField.adjoin_rootSet_isSplittingField hpmap
  letI : FiniteDimensional F N := by
    apply finite_adjoin_isFiniteDimensional (p.rootSet E)
      (Polynomial.rootSet_finite p E)
    intro y hy
    exact (inferInstance : Normal F E).isIntegral y
  letI : Polynomial.IsSplittingField F N p := hNsplit
  letI : Normal F N := Normal.of_isSplittingField p
  have hNtop :=
    normal_fixedField_top_sup_separableClosure_eq_top_of_finite
      (F := F) (E := N)
  have hxroot : x ∈ p.rootSet E := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero ((inferInstance : Normal F E).isIntegral x),
      minpoly.aeval F x⟩
  have hxN : x ∈ N := IntermediateField.subset_adjoin F _ hxroot
  have hxNtop :
      (⟨x, hxN⟩ : N) ∈
        separableClosure F N ⊔
          IntermediateField.fixedField (⊤ : Subgroup Gal(N / F)) := by
    rw [hNtop]
    exact IntermediateField.mem_top
  let i : N →ₐ[F] E := N.val
  have hsep_le :
      (separableClosure F N).map i ≤ separableClosure F E := by
    rintro z ⟨zN, hzN, rfl⟩
    change zN ∈ separableClosure F N at hzN
    rw [mem_separableClosure_iff] at hzN ⊢
    change (minpoly F zN).Separable at hzN
    change (minpoly F (zN : E)).Separable
    simpa only [IntermediateField.minpoly_eq] using hzN
  have hfix_le :
      (IntermediateField.fixedField (⊤ : Subgroup Gal(N / F))).map i ≤
        IntermediateField.fixedField (⊤ : Subgroup Gal(E / F)) := by
    rintro z ⟨zN, hzN, rfl⟩
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hzfix :=
      (IntermediateField.mem_fixedField_iff
        (H := (⊤ : Subgroup Gal(N / F))) zN).mp hzN
        (σ.restrictNormal N) (Subgroup.mem_top _)
    have hcomm := AlgEquiv.restrictNormal_commutes σ N zN
    rw [hzfix] at hcomm
    simpa [i] using hcomm.symm
  have hsup_le :
      (separableClosure F N).map i ⊔
          (IntermediateField.fixedField (⊤ : Subgroup Gal(N / F))).map i ≤
        separableClosure F E ⊔
          IntermediateField.fixedField (⊤ : Subgroup Gal(E / F)) :=
    sup_le (hsep_le.trans le_sup_left) (hfix_le.trans le_sup_right)
  have hxmap : x ∈
      (separableClosure F N).map i ⊔
          (IntermediateField.fixedField (⊤ : Subgroup Gal(N / F))).map i := by
    rw [← IntermediateField.map_sup]
    exact ⟨⟨x, hxN⟩, hxNtop, rfl⟩
  exact hsup_le hxmap

/- The source's tensor-product equality is corrected to the natural
   `F`-algebra equivalence induced by this map. -/
theorem normal_extension_tensor_product_map_bijective
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    Function.Bijective (normalExtensionTensorProductMap (F := F) (E := E)) := by
  let S : IntermediateField F E := normalSeparablePart F E
  let I : IntermediateField F E := normalInseparablePart F E
  change Function.Bijective (S.toSubalgebra.mulMap I.toSubalgebra)
  let hI : IsPurelyInseparable F I :=
    normal_fixedField_top_isPurelyInseparable (F := F) (E := E)
  have hld : S.LinearDisjoint I :=
    S.linearDisjoint_of_isPurelyInseparable_of_isSeparable I
  have htop : S ⊔ I = ⊤ := by
    exact normal_fixedField_top_sup_separableClosure_eq_top
      (F := F) (E := E)
  let A : Subalgebra F E := S.toSubalgebra ⊔ I.toSubalgebra
  have hAinv : ∀ z : E, z ∈ A → z⁻¹ ∈ A := by
    intro z hz
    exact Subalgebra.inv_mem_of_algebraic A (x := (⟨z, hz⟩ : A))
      ((inferInstance : Normal F E).isIntegral z).isAlgebraic
  let J : IntermediateField F E := A.toIntermediateField hAinv
  have hSJ : S ≤ J := by
    intro z hz
    change z ∈ A
    change z ∈ S.toSubalgebra ⊔ I.toSubalgebra
    exact (show S.toSubalgebra ≤ S.toSubalgebra ⊔ I.toSubalgebra from le_sup_left) hz
  have hIJ : I ≤ J := by
    intro z hz
    change z ∈ A
    change z ∈ S.toSubalgebra ⊔ I.toSubalgebra
    exact (show I.toSubalgebra ≤ S.toSubalgebra ⊔ I.toSubalgebra from le_sup_right) hz
  have hJtop : J = ⊤ := by
    apply le_antisymm le_top
    rw [← htop]
    exact sup_le hSJ hIJ
  have hAtop : A = ⊤ := by
    have h := congrArg (fun K : IntermediateField F E => K.toSubalgebra) hJtop
    simpa [J] using h
  have htop'' : S.toSubalgebra ⊔ I.toSubalgebra = ⊤ := by
    simpa [A] using hAtop
  constructor
  · exact (linear_disjoint_iff_tensor_product_multiplication_injective S I).mp hld
  · rw [← AlgHom.range_eq_top]
    rw [Subalgebra.mulMap_range]
    exact htop''

noncomputable def normalExtensionTensorProductAlgEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    (normalSeparablePart F E ⊗[F] normalInseparablePart F E) ≃ₐ[F] E :=
  AlgEquiv.ofBijective
    (normalExtensionTensorProductMap (F := F) (E := E))
    (normal_extension_tensor_product_map_bijective (F := F) (E := E))

/- This packages the source lemma with the canonical choices of the two
   subextensions. -/
theorem normal_extension_separable_inseparable_decomposition
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    ∃ E_sep E_insep : IntermediateField F E,
      E_sep = normalSeparablePart F E ∧
        E_insep = normalInseparablePart F E ∧
        IsGalois F E_sep ∧
        IsPurelyInseparable E_sep E ∧
        IsPurelyInseparable F E_insep ∧
        IsGalois E_insep E ∧
        Nonempty (E_sep ⊗[F] E_insep ≃ₐ[F] E) := by
  refine ⟨normalSeparablePart F E, normalInseparablePart F E,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · exact normal_fixedField_top_isPurelyInseparable (F := F) (E := E)
  · let hN : Normal (normalInseparablePart F E) E :=
      Normal.tower_top_of_normal F (normalInseparablePart F E) E
    have hsup : normalSeparablePart F E ⊔ normalInseparablePart F E = ⊤ :=
      normal_fixedField_top_sup_separableClosure_eq_top (F := F) (E := E)
    let T : IntermediateField F E :=
      (separableClosure (normalInseparablePart F E) E).restrictScalars F
    have hSle : normalSeparablePart F E ≤ T := by
      exact separableClosure.le_restrictScalars F (normalInseparablePart F E) E
    have hIle : normalInseparablePart F E ≤ T := by
      exact le_restrictScalars_separableClosure (normalInseparablePart F E)
    have hTtop : T = ⊤ := by
      apply top_unique
      rw [← hsup]
      exact sup_le hSle hIle
    have htop_sep : (⊤ : IntermediateField (normalInseparablePart F E) E) ≤
        separableClosure (normalInseparablePart F E) E := by
      intro x hx
      have hxT : x ∈ T := by
        rw [hTtop]
        simp
      exact hxT
    have hsep_top : Algebra.IsSeparable (normalInseparablePart F E)
        (⊤ : IntermediateField (normalInseparablePart F E) E) :=
      (le_separableClosure_iff _ _ _).mp htop_sep
    have hsep : Algebra.IsSeparable (normalInseparablePart F E) E :=
      (IntermediateField.isSeparable_top _ _).mp hsep_top
    let hsep' : Algebra.IsSeparable (normalInseparablePart F E) E := hsep
    exact ⟨⟩
  · exact ⟨normalExtensionTensorProductAlgEquiv (F := F) (E := E)⟩

end

end Formalization.Books.Fields.Unit27
