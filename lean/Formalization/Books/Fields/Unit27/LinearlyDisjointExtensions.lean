import Formalization.Books.Fields.Unit26.Transcendence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PurelyInseparable.Basic
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
    convert hiQ using 1 <;> norm_num [f]
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

theorem complex_radical_compositum_degree :
    Module.finrank ℚ complexRadicalCompositum = 48 := by
  sorry

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

/- The source's tensor-product equality is corrected to the natural
   `F`-algebra equivalence induced by this map. -/
theorem normal_extension_tensor_product_map_bijective
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    Function.Bijective (normalExtensionTensorProductMap (F := F) (E := E)) := by
  sorry

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
  sorry

end

end Formalization.Books.Fields.Unit27
