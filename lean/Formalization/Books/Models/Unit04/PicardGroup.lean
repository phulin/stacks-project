import Formalization.Books.Models.Unit03.NumericalTypes

/-!
# The Picard group of a numerical type

Formal statements from Chapter 4 of *Semistable Reduction*.  The source uses
indices `1, ..., n`; this file keeps the preceding chapters' `Fin n`
convention and realizes the Picard group as the module cokernel of the
row-scaled intersection matrix.
-/

noncomputable section

namespace Formalization.Books.Models.Unit04

open Formalization.Books.Models.Unit02
open Formalization.Books.Models.Unit03

/-! The integral matrix `(aᵢⱼ / wᵢ)` defining the Picard group. -/
def picardMatrix (T : NumericalType) : Matrix (Fin T.n) (Fin T.n) ℤ :=
  fun i j => T.a i j / T.w i

/-! The Picard group is the cokernel of the row-scaled intersection matrix. -/
abbrev picardGroup (T : NumericalType) : Type _ :=
  moduleCokernel (Matrix.toLin' (picardMatrix T))

/-! The diagonal weight map in the comparison with the unscaled matrix. -/
def picardWeightMap (T : NumericalType) :
    (Fin T.n → ℤ) →ₗ[ℤ] (Fin T.n → ℤ) :=
  Matrix.toLin' (Matrix.diagonal T.w)

/-! The matrix identity underlying the comparison of the two cokernels. -/
theorem picard_weight_square (T : NumericalType) :
    (picardWeightMap T).comp (Matrix.toLin' (picardMatrix T)) =
      Matrix.toLin' T.a := by
  dsimp [picardWeightMap]
  rw [← Matrix.toLin'_mul]
  congr 1
  ext i j
  simp [picardMatrix, Matrix.mul_apply, Matrix.diagonal]
  rw [← mul_comm, Int.ediv_mul_cancel (T.w_dvd i j)]

/-! The weight map sends the Picard relations into the intersection relations. -/
theorem picard_weight_map_range (T : NumericalType) :
    LinearMap.range (Matrix.toLin' (picardMatrix T)) ≤
      LinearMap.ker
        ((Submodule.mkQ (LinearMap.range (Matrix.toLin' T.a))).comp
          (picardWeightMap T)) := by
  rintro x ⟨y, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.comp_apply, ← picard_weight_square T]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩

/-! The canonical map from the Picard group to the unscaled matrix cokernel. -/
def picardGroupToMatrixCokernel (T : NumericalType) :
    picardGroup T →ₗ[ℤ] matrixCokernel T.a :=
  (LinearMap.range (Matrix.toLin' (picardMatrix T))).liftQ
    ((Submodule.mkQ (LinearMap.range (Matrix.toLin' T.a))).comp
      (picardWeightMap T))
    (picard_weight_map_range T)

/-! The comparison map is injective. -/
theorem picardGroupToMatrixCokernel_injective (T : NumericalType) :
    Function.Injective (picardGroupToMatrixCokernel T) := by
  unfold picardGroupToMatrixCokernel
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.ker_liftQ_eq_bot
  rintro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx
  rcases (Submodule.Quotient.mk_eq_zero _).mp hx with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have hmap :
      picardWeightMap T ((Matrix.toLin' (picardMatrix T)) y) = picardWeightMap T x := by
    rw [← LinearMap.comp_apply, picard_weight_square T, hy]
  apply funext
  intro i
  apply mul_left_cancel₀ (ne_of_gt (T.w_pos i))
  have hi := congrFun hmap i
  simp only [picardWeightMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal] at hi
  exact hi

/-! The Picard group is a finitely generated abelian group of rank one. -/
theorem picard_group_finite_rank_one (T : NumericalType) :
    Module.Finite ℤ (picardGroup T) ∧
      Module.finrank ℤ (picardGroup T) = 1 := by
  sorry

/-! An additive abelian group killed by `2`, i.e. an elementary abelian 2-group. -/
def IsElementaryAbelianTwo (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, (2 : ℤ) • x = 0

/-!
The data saying that `T'` is the numerical type obtained by contracting the
`(-1)`-index `i`.  The preceding chapter proves existence of this data; the
explicit equivalence is retained so the contraction maps below have usable
coordinates.
-/
def IsContraction (T T' : NumericalType) (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i) : Prop :=
  T'.n = T.n - 1 ∧
    (∀ j, T'.m j = T.m (e j).1) ∧
      (∀ j k, T'.a j k = contractedIntersection T i (e j) (e k)) ∧
        (∀ j, T'.w j = contractedWeight T i (e j)) ∧
          (∀ j, T'.g j = contractedComponentGenus T i (e j)) ∧
            genus T' = genus T

/-! The contraction data supplied by the preceding numerical-type chapter. -/
theorem exists_contraction (T : NumericalType) (i : Fin T.n)
    (hi : IsMinusOneIndex T i) :
    ∃ T' : NumericalType, ∃ e : Fin T'.n ≃ RemainingIndex T i,
      IsContraction T T' i e := by
  rcases contract_minus_one_index T i hi with
    ⟨T', hT'n, e, hm, ha, hw, hg, hgenus⟩
  exact ⟨T', e, ⟨hT'n, hm, ha, hw, hg, hgenus⟩⟩

/-! The quotient map `q` in the contraction diagram. -/
def contractionQ (T T' : NumericalType) (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i) :
    (Fin T.n → ℤ) →ₗ[ℤ] (Fin T'.n → ℤ) :=
  { toFun := fun x j => x (e j).1
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro r x
      rfl }

/-! The quotient map `p` in the contraction diagram. -/
def contractionP (T T' : NumericalType) (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i) :
    (Fin T.n → ℤ) →ₗ[ℤ] (Fin T'.n → ℤ) :=
  { toFun := fun x j =>
      x i * (T.a i (e j).1 / T'.w j) +
        x (e j).1 * (T.w (e j).1 / T'.w j)
    map_add' := by
      intro x y
      ext j
      dsimp
      ring
    map_smul' := by
      intro r x
      ext j
      dsimp
      ring }

/-! The contraction maps form the commutative square in the source proof. -/
theorem contraction_square (T T' : NumericalType) (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i)
    (hcontraction : IsContraction T T' i e)
    (hi : IsMinusOneIndex T i := by assumption) :
    (contractionP T T' i e).comp (Matrix.toLin' (picardMatrix T)) =
      (Matrix.toLin' (picardMatrix T')).comp (contractionQ T T' i e) := by
  sorry

/-! The weight ratios used to control the contraction cokernel. -/
theorem contracted_weight_ratio_one_or_two (T T' : NumericalType)
    (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i)
    (hcontraction : IsContraction T T' i e) :
    ∀ j, T.w (e j).1 / T'.w j = 1 ∨ T.w (e j).1 / T'.w j = 2 := by
  intro j
  rw [hcontraction.2.2.2.1 j]
  unfold contractedWeight
  split_ifs with hcond
  · right
    have hwi : T.w i ∣ T.a (e j).1 i := by
      simpa [T.a_symmetric] using T.w_dvd i (e j).1
    have ha_even : Even (T.a (e j).1 i) := by
      have he := Even.mul_right hcond.1 (T.w i)
      rw [Int.ediv_mul_cancel hwi] at he
      exact he
    have hwj_even : Even (T.w (e j).1) := by
      by_contra hneven
      have hprod : Odd ((T.a (e j).1 i / T.w (e j).1) * T.w (e j).1) :=
        hcond.2.mul (Int.not_even_iff_odd.mp hneven)
      rw [Int.ediv_mul_cancel (T.w_dvd (e j).1 i)] at hprod
      exact (Int.not_odd_iff_even.mpr ha_even) hprod
    obtain ⟨k, hk⟩ := hwj_even.two_dvd
    have hk_formula : T.w (e j).1 / 2 = k := by
      apply Int.ediv_eq_of_eq_mul_left
      · norm_num
      · simpa [mul_comm] using hk
    have hk_ne : k ≠ 0 := by
      intro hk0
      rw [hk0] at hk
      have hwpos := T.w_pos (e j).1
      omega
    rw [hk_formula]
    exact Int.ediv_eq_of_eq_mul_left hk_ne hk
  · left
    apply Int.ediv_self
    exact ne_of_gt (T.w_pos (e j).1)

/-! Twice every target basis vector lies in the image of `p`. -/
theorem contractionP_two_smul_basis_mem_range (T T' : NumericalType)
    (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i)
    (hcontraction : IsContraction T T' i e) :
    ∀ j : Fin T'.n,
      (2 : ℤ) • (Pi.single j 1) ∈ LinearMap.range (contractionP T T' i e) := by
  intro j
  rcases contracted_weight_ratio_one_or_two T T' i e hcontraction j with hratio | hratio
  · refine ⟨2 • Pi.single (e j).1 1, ?_⟩
    ext k
    have hne : (e j).1 ≠ i := (e j).2
    by_cases hkj : k = j
    · subst k
      simp [contractionP, hratio, hne]
    · have hek : (e k).1 ≠ (e j).1 := by
        intro h
        apply hkj
        exact e.injective (Subtype.ext h)
      simp [contractionP, hkj, hek, hne]
  · refine ⟨Pi.single (e j).1 1, ?_⟩
    ext k
    have hne : (e j).1 ≠ i := (e j).2
    by_cases hkj : k = j
    · subst k
      simp [contractionP, hratio, hne]
    · have hek : (e k).1 ≠ (e j).1 := by
        intro h
        apply hkj
        exact e.injective (Subtype.ext h)
      simp [contractionP, hkj, hek, hne]

/-! The target quotient map used to descend `p` to the Picard cokernel. -/
def contractionTargetMap (T T' : NumericalType) (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i) :
    (Fin T.n → ℤ) →ₗ[ℤ] picardGroup T' :=
  (Submodule.mkQ (LinearMap.range (Matrix.toLin' (picardMatrix T')))).comp
    (contractionP T T' i e)

/-! The commutative square gives the relation needed to descend `p` to cokernels. -/
theorem contraction_square_range (T T' : NumericalType) (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i)
    (hcontraction : IsContraction T T' i e)
    (hi : IsMinusOneIndex T i := by assumption) :
    LinearMap.range (Matrix.toLin' (picardMatrix T)) ≤
      LinearMap.ker (contractionTargetMap T T' i e) := by
  rintro x ⟨y, rfl⟩
  change (Submodule.mkQ (LinearMap.range (Matrix.toLin' (picardMatrix T'))))
      ((contractionP T T' i e) ((Matrix.toLin' (picardMatrix T)) y)) = 0
  have hs : (contractionP T T' i e) ((Matrix.toLin' (picardMatrix T)) y) =
      (Matrix.toLin' (picardMatrix T')) ((contractionQ T T' i e) y) := by
    simpa only [LinearMap.comp_apply] using
      LinearMap.congr_fun (contraction_square T T' i e hcontraction hi) y
  rw [hs]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  show (Matrix.toLin' (picardMatrix T')) ((contractionQ T T' i e) y) ∈
    LinearMap.range (Matrix.toLin' (picardMatrix T'))
  exact ⟨contractionQ T T' i e y, rfl⟩

/-! The homomorphism of Picard groups induced by contraction. -/
def contractionPicardMap (T T' : NumericalType) (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i)
    (hcontraction : IsContraction T T' i e)
    (hi : IsMinusOneIndex T i := by assumption) :
    picardGroup T →ₗ[ℤ] picardGroup T' :=
  (LinearMap.range (Matrix.toLin' (picardMatrix T))).liftQ
    (contractionTargetMap T T' i e)
    (contraction_square_range T T' i e hcontraction hi)

/-!
Contracting a `(-1)`-index gives an injection of Picard groups whose cokernel
is an elementary abelian 2-group.
-/
theorem contract_picard_group (T T' : NumericalType) (i : Fin T.n)
    (hi : IsMinusOneIndex T i)
    (e : Fin T'.n ≃ RemainingIndex T i)
    (hcontraction : IsContraction T T' i e) :
    Function.Injective (contractionPicardMap T T' i e hcontraction) ∧
      IsElementaryAbelianTwo
        (moduleCokernel (contractionPicardMap T T' i e hcontraction)) := by
  sorry

/-! In nonpositive genus the Picard group is isomorphic to the integers. -/
theorem picard_group_genus_nonpositive (T : NumericalType)
    (hgenus : genus T ≤ 0) :
    Nonempty (picardGroup T ≃+ ℤ) := by
  sorry

end Formalization.Books.Models.Unit04
