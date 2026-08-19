import Formalization.Books.Models.Unit03.NumericalTypes
import Mathlib.LinearAlgebra.Span.TensorProduct
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.Flat.Localization

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
  sorry
/-
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

private theorem rational_span_finrank_eq_real_span {n m : ℕ}
    (v : Fin n → Fin m → ℚ) :
    Module.finrank ℝ
        (Submodule.span ℝ (Set.range (fun i j => (v i j : ℝ)))) =
      Module.finrank ℚ
        (Submodule.span ℚ (Set.range (fun i j => (v i j : ℝ)))) := by
  let pQ : Submodule ℚ (Fin m → ℚ) := Submodule.span ℚ (Set.range v)
  let b := Module.Free.chooseBasis ℚ pQ
  let : Fintype (Module.Free.ChooseBasisIndex ℚ pQ) := Fintype.ofFinite _
  let u : Module.Free.ChooseBasisIndex ℚ pQ → Fin m → ℚ :=
    fun i => b i
  have hu : LinearIndependent ℚ u := by
    simp [u, Function.comp_def] using b.linearIndependent.map' pQ.subtype pQ.ker_subtype
  have huR : LinearIndependent ℝ
      (fun i => algebraMap ℚ ℝ ∘ u i) := by
    have h := (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ)).mpr hu
    exact h
  have hu_span : Submodule.span ℚ (Set.range u) = pQ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact (b i).property
    · intro x hx
      let y : pQ := ⟨x, hx⟩
      have hy : ∑ i, (b.repr y) i • (b i : Fin m → ℚ) = x := by
        have hy' : pQ.subtype (∑ i, (b.repr y) i • b i) = x := by
          exact (congrArg Subtype.val (b.sum_repr y)).trans rfl
        calc
          ∑ i, (b.repr y) i • (b i : Fin m → ℚ) =
              pQ.subtype (∑ i, (b.repr y) i • b i) := by
                rw [map_sum]
                simp only [map_smul]
                apply Finset.sum_congr rfl
                intro i hi
                rfl
          _ = x := hy'
      rw [← hy]
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcast_v (x : Fin m → ℚ) (hx : x ∈ pQ) :
      (fun j => (x j : ℝ)) ∈
        Submodule.span ℝ (Set.range (fun i j => (v i j : ℝ))) := by
    apply Submodule.span_induction (R := ℚ) (s := Set.range v) (x := x)
      (p := fun (x : Fin m → ℚ) _ =>
        (fun j => (x j : ℝ)) ∈
          Submodule.span ℝ (Set.range (fun i j => (v i j : ℝ))))
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · have hz : (fun j : Fin m => ((0 : Fin m → ℚ) j : ℝ)) = 0 := by
        ext j
        simp
      rw [hz]
      exact Submodule.zero_mem _
    · intro x y hx hy hcx hcy
      convert Submodule.add_mem _ hcx hcy using 1
      · ext j
        simp
    · intro a x hx hcx
      convert Submodule.smul_mem _ (a : ℝ) hcx using 1
      · ext j
        simp
    · simp [pQ] using hx
  have hcast_u (x : Fin m → ℚ) (hx : x ∈ pQ) :
      (fun j => (x j : ℝ)) ∈
        Submodule.span ℝ
          (Set.range (fun i => algebraMap ℚ ℝ ∘ u i)) := by
    have hx' : x ∈ Submodule.span ℚ (Set.range u) := by
      rw [hu_span]
      exact hx
    apply Submodule.span_induction (R := ℚ) (s := Set.range u) (x := x)
      (p := fun (x : Fin m → ℚ) _ =>
        (fun j => (x j : ℝ)) ∈ Submodule.span ℝ
          (Set.range (fun i => algebraMap ℚ ℝ ∘ u i)))
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · have hz : (fun j : Fin m => ((0 : Fin m → ℚ) j : ℝ)) = 0 := by
        ext j
        simp
      rw [hz]
      exact Submodule.zero_mem _
    · intro x y hx hy hcx hcy
      convert Submodule.add_mem _ hcx hcy using 1
      · ext j
        simp
    · intro a x hx hcx
      convert Submodule.smul_mem _ (a : ℝ) hcx using 1
      · ext j
        simp
    · exact hx'
  have hspan :
      Submodule.span ℝ (Set.range (fun i j => (v i j : ℝ))) =
        Submodule.span ℝ
          (Set.range (fun i => algebraMap ℚ ℝ ∘ u i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact hcast_u (v i) (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact hcast_v (b i) (b i).property
  let cQ : (Fin m → ℚ) →ₗ[ℚ] (Fin m → ℝ) :=
    { toFun := fun x j => (x j : ℝ)
      map_add' := by
        intro x y
        ext j
        simp
      map_smul' := by
        intro r x
        ext j
        simp [Algebra.smul_def] }
  have hcQ_ker : LinearMap.ker cQ = ⊥ := by
    apply LinearMap.ker_eq_bot_of_injective
    intro x y hxy
    apply funext
    intro j
    have hj := congrFun hxy j
    have hj' : (x j : ℝ) = (y j : ℝ) := by
      simpa [cQ] using hj
    exact_mod_cast hj'
  have huQ : LinearIndependent ℚ (fun i => cQ (u i)) := by
    have h := hu.map' cQ hcQ_ker
    simpa [cQ, Function.comp_def] using h
  have hcastQ_v (x : Fin m → ℚ) (hx : x ∈ pQ) :
      cQ x ∈
        Submodule.span ℚ (Set.range (fun i j => (v i j : ℝ))) := by
    apply Submodule.span_induction (R := ℚ) (s := Set.range v) (x := x)
      (p := fun (x : Fin m → ℚ) _ =>
        cQ x ∈ Submodule.span ℚ (Set.range (fun i j => (v i j : ℝ))))
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      change (fun j => ((v i) j : ℝ)) ∈
        Submodule.span ℚ (Set.range (fun i j => (v i j : ℝ)))
      exact Submodule.subset_span ⟨i, rfl⟩
    · have hz : cQ (0 : Fin m → ℚ) = 0 := by
        ext j
        simp [cQ]
      rw [hz]
      exact Submodule.zero_mem _
    · intro x y hx hy hcx hcy
      rw [cQ.map_add]
      exact Submodule.add_mem _ hcx hcy
    · intro a x hx hcx
      rw [cQ.map_smul]
      exact Submodule.smul_mem _ a hcx
    · simpa [pQ, cQ] using hx
  have hcastQ_u (x : Fin m → ℚ) (hx : x ∈ pQ) :
      cQ x ∈ Submodule.span ℚ (Set.range (fun i => cQ (u i))) := by
    have hx' : x ∈ Submodule.span ℚ (Set.range u) := by
      rw [hu_span]
      exact hx
    apply Submodule.span_induction (R := ℚ) (s := Set.range u) (x := x)
      (p := fun (x : Fin m → ℚ) _ =>
        cQ x ∈ Submodule.span ℚ (Set.range (fun i => cQ (u i))))
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · have hz : cQ (0 : Fin m → ℚ) = 0 := by
        ext j
        simp [cQ]
      rw [hz]
      exact Submodule.zero_mem _
    · intro x y hx hy hcx hcy
      rw [cQ.map_add]
      exact Submodule.add_mem _ hcx hcy
    · intro a x hx hcx
      rw [cQ.map_smul]
      exact Submodule.smul_mem _ a hcx
    · exact hx'
  have hqspan :
      Submodule.span ℚ (Set.range (fun i j => (v i j : ℝ))) =
        Submodule.span ℚ (Set.range (fun i => cQ (u i))) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact hcastQ_u (v i) (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact hcastQ_v (b i) (b i).property
  rw [hspan, finrank_span_eq_card huR, hqspan,
    finrank_span_eq_card huQ, ← Module.finrank_eq_card_basis b]

private theorem int_matrix_range_finrank_eq_real_range {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) :
    Module.finrank ℤ (LinearMap.range (Matrix.toLin' A)) =
      Module.finrank ℝ
        (LinearMap.range (Matrix.toLin' (A.map (Int.castRingHom ℝ)))) := by
  let fZ := Matrix.toLin' A
  let fR := Matrix.toLin' (A.map (Int.castRingHom ℝ))
  let c : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℝ) :=
    { toFun := fun x i => (x i : ℝ)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro r x
        ext i
        simp }
  let S : Set (Fin n → ℝ) :=
    Set.range (fun j : Fin n => c (fZ (Pi.single j 1)))
  let pZ : Submodule ℤ (Fin n → ℝ) := Submodule.span ℤ S
  have hspan : Submodule.span ℝ S = LinearMap.range fR := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro y ⟨j, rfl⟩
      refine ⟨Pi.single j 1, ?_⟩
      ext k
      simp [fR, fZ, c, Matrix.toLin'_apply, Matrix.mulVec]
    · rintro y ⟨x, rfl⟩
      have hdecomp (x : Fin n → ℝ) :
          x = ∑ j, x j • Pi.single j 1 := by
        ext k
        rw [Finset.sum_apply, Finset.sum_eq_single k]
        · simp
        · intro j hj hjk
          have hkj : k ≠ j := Ne.symm hjk
          simp [hkj]
        · simp
      rw [hdecomp x, map_sum]
      apply Submodule.sum_mem
      intro j hj
      rw [map_smul]
      have hmem : c (fZ (Pi.single j 1)) ∈ Submodule.span ℝ S :=
        Submodule.subset_span ⟨j, rfl⟩
      convert Submodule.smul_mem _ (x j) hmem using 1
      ext k
      simp [fR, fZ, c, Matrix.toLin'_apply]
  have hc_injective : Function.Injective c := by
    intro x y hxy
    apply funext
    intro i
    have hi : (x i : ℝ) = (y i : ℝ) := by
      simpa [c] using congrFun hxy i
    exact_mod_cast hi
  have hmap : Submodule.map c (LinearMap.range fZ) = pZ := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      rcases hx with ⟨z, rfl⟩
      have hzdecomp (z : Fin n → ℤ) :
          z = ∑ j, z j • Pi.single j 1 := by
        ext k
        rw [Finset.sum_apply, Finset.sum_eq_single k]
        · simp
        · intro j hj hjk
          have hkj : k ≠ j := Ne.symm hjk
          simp [hkj]
        · simp
      rw [hzdecomp z]
      simp only [map_sum]
      apply Submodule.sum_mem
      intro j hj
      have hgen : c (fZ (Pi.single j 1)) ∈ pZ := by
        exact Submodule.subset_span (show c (fZ (Pi.single j 1)) ∈ S from ⟨j, rfl⟩)
      simpa only [map_smul] using Submodule.smul_mem pZ (z j) hgen
    · rw [Submodule.span_le]
      rintro y ⟨j, rfl⟩
      refine ⟨fZ (Pi.single j 1), ⟨Pi.single j 1, rfl⟩, rfl⟩
  let cR : LinearMap.range fZ →ₗ[ℤ] pZ :=
    ((c.domRestrict (LinearMap.range fZ)).codRestrict pZ (by
      intro x
      exact hmap ▸ ⟨(x : Fin n → ℤ), x.property, rfl⟩))
  have hcR_bijective : Function.Bijective cR := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hc_injective
      exact congrArg Subtype.val hxy
    · intro y
      have hy : (y : Fin n → ℝ) ∈ Submodule.map c (LinearMap.range fZ) := by
        rw [hmap]
        exact y.property
      rcases hy with ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let eZ : LinearMap.range fZ ≃ₗ[ℤ] pZ :=
    LinearEquiv.ofBijective cR hcR_bijective
  let : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  let : Module.Finite ℤ pZ :=
    Module.Finite.span_of_finite ℤ
      (Set.finite_range (fun j : Fin n => c (fZ (Pi.single j 1))))
  have hZQ : Module.finrank ℚ (Submodule.span ℚ (pZ : Set (Fin n → ℝ))) =
      Module.finrank ℤ pZ := by
    unfold pZ
    exact Submodule.finrank_span_eq_finrank_span ℤ ℚ S
  have hS : S = Set.range (fun j : Fin n => fun i => (A i j : ℝ)) := by
    apply Set.ext
    intro x
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      funext i
      simp [c, fZ, Matrix.toLin'_apply]
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      funext i
      simp [c, fZ, Matrix.toLin'_apply]
  have hpZQ :
      Submodule.span ℚ (pZ : Set (Fin n → ℝ)) =
        Submodule.span ℚ S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      change x ∈ Submodule.span ℤ S at hx
      apply Submodule.span_induction (R := ℤ) (s := S) (x := x)
        (p := fun y _ => y ∈ Submodule.span ℚ S)
      · intro y hy
        exact Submodule.subset_span hy
      · exact Submodule.zero_mem _
      · intro y z hy hz hpy hpz
        exact Submodule.add_mem _ hpy hpz
      · intro a y hy hpy
        simp [Algebra.smul_def] using
          Submodule.smul_mem (Submodule.span ℚ S) (a : ℚ) hpy
      · exact hx
    · rw [Submodule.span_le]
      intro x hx
      exact Submodule.subset_span (Submodule.subset_span hx)
  rw [hS] at hspan hpZQ
  have hgeneric := rational_span_finrank_eq_real_span
    (v := fun i j : Fin n => (A j i : ℚ))
  have hcast_fun :
      (fun i j : Fin n => (((A j i : ℚ) : ℝ))) =
        (fun i j : Fin n => (A j i : ℝ)) := by
    funext i j
    exact Rat.cast_intCast _
  rw [hcast_fun] at hgeneric
  calc
    Module.finrank ℤ (LinearMap.range fZ) = Module.finrank ℤ pZ :=
      eZ.finrank_eq
    _ = Module.finrank ℚ (Submodule.span ℚ (pZ : Set (Fin n → ℝ))) :=
      hZQ.symm
    _ = Module.finrank ℚ
        (Submodule.span ℚ (Set.range (fun i j : Fin n => (A j i : ℝ)))) := by
      rw [hpZQ]
    _ = Module.finrank ℝ
        (Submodule.span ℝ (Set.range (fun i j : Fin n => (A j i : ℝ)))) := by
      exact hgeneric.symm
    _ = Module.finrank ℝ (LinearMap.range fR) := by
      rw [hspan] -/

/-! The Picard group is a finitely generated abelian group of rank one. -/
theorem picard_group_finite_rank_one (T : NumericalType) :
    Module.Finite ℤ (picardGroup T) ∧
      Module.finrank ℤ (picardGroup T) = 1 := by
  sorry
/-
  constructor
  · infer_instance
  · let fP := Matrix.toLin' (picardMatrix T)
    let fA := Matrix.toLin' T.a
    have hweight_inj : Function.Injective (picardWeightMap T) := by
      intro x y hxy
      apply funext
      intro i
      apply mul_left_cancel₀ (ne_of_gt (T.w_pos i))
      have hi := congrFun hxy i
      simp only [picardWeightMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal] at hi
      exact hi
    have hmaprange :
        Submodule.map (picardWeightMap T) (LinearMap.range fP) =
          LinearMap.range fA := by
      apply le_antisymm
      · rintro y ⟨x, ⟨z, rfl⟩, rfl⟩
        refine ⟨z, ?_⟩
        simpa [fP, fA, LinearMap.comp_apply] using
          (LinearMap.congr_fun (picard_weight_square T) z).symm
      · rintro y ⟨z, rfl⟩
        refine ⟨fP z, ⟨z, rfl⟩, ?_⟩
        simpa [fP, fA, LinearMap.comp_apply] using
          LinearMap.congr_fun (picard_weight_square T) z
    let eWmap : LinearMap.range fP →ₗ[ℤ] LinearMap.range fA :=
      ((picardWeightMap T).domRestrict (LinearMap.range fP)).codRestrict
        (LinearMap.range fA) (by
          intro x
          exact hmaprange ▸ ⟨(x : Fin T.n → ℤ), x.property, rfl⟩)
    have heWmap_bijective : Function.Bijective eWmap := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        apply hweight_inj
        exact congrArg Subtype.val hxy
      · intro y
        have hy : (y : Fin T.n → ℤ) ∈
            Submodule.map (picardWeightMap T) (LinearMap.range fP) := by
          rw [hmaprange]
          exact y.property
        rcases hy with ⟨x, hx, hxy⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    let eW : LinearMap.range fP ≃ₗ[ℤ] LinearMap.range fA :=
      LinearEquiv.ofBijective eWmap heWmap_bijective
    have hP : Module.finrank ℤ (LinearMap.range fP) =
        Module.finrank ℤ (LinearMap.range fA) := eW.finrank_eq
    have hAm :
        Matrix.mulVec (fun i j => (T.a i j : ℝ))
            (fun i => (T.m i : ℝ)) = 0 := by
      funext i
      change (∑ j, (T.a i j : ℝ) * (T.m j : ℝ)) = 0
      exact_mod_cast T.row_sum i
    have hreal := recurring_symmetric_real_range_finrank
      (fun i j => (T.a i j : ℝ)) (fun i => (T.m i : ℝ))
      (by intro i j; exact_mod_cast T.a_symmetric i j)
      (by intro i j h; exact_mod_cast T.a_offdiag_nonneg h)
      (by intro i; exact_mod_cast T.m_pos i) hAm
      (by
        intro h
        apply T.connected
        rcases h with ⟨I, hI, hne, hcross⟩
        refine ⟨I, hI, hne, ?_⟩
        intro i j hi hj
        exact_mod_cast hcross hi hj)
    have hA : Module.finrank ℤ (LinearMap.range fA) = T.n - 1 := by
      dsimp [fA]
      rw [int_matrix_range_finrank_eq_real_range]
      change Module.finrank ℝ
          (LinearMap.range (Matrix.toLin'
            (fun i j => (T.a i j : ℝ)))) = T.n - 1
      exact hreal
    have hdim := Submodule.finrank_quotient_add_finrank
      (R := ℤ) (M := (Fin T.n → ℤ)) (LinearMap.range fP)
    rw [hP, hA] at hdim
    change Module.finrank ℤ ((Fin T.n → ℤ) ⧸ LinearMap.range fP) = 1
    have hdim' :
        Module.finrank ℤ ((Fin T.n → ℤ) ⧸ LinearMap.range fP) + (T.n - 1) = T.n := by
      simpa [Module.finrank_pi_fintype] using hdim
    have hn := T.hn
    omega -/

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

private theorem contraction_weight_dvd (T T' : NumericalType) (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i)
    (hcontraction : IsContraction T T' i e) (j : Fin T'.n) :
    T'.w j ∣ T.w (e j).1 := by
  rw [hcontraction.2.2.2.1 j]
  unfold contractedWeight
  split_ifs with hcond
  · have hwi : T.w i ∣ T.a (e j).1 i := by
      simpa [T.a_symmetric] using T.w_dvd i (e j).1
    have hwr : T.w (e j).1 ∣ T.a (e j).1 i := T.w_dvd _ _
    have hw_even : Even (T.w (e j).1) := by
      by_contra hneven
      have ha_even : Even (T.a (e j).1 i) := by
        obtain ⟨r, hr⟩ := hcond.1
        refine ⟨r * T.w i, ?_⟩
        rw [← Int.ediv_mul_cancel hwi, hr]
        ring
      have ha_odd : Odd (T.a (e j).1 i) := by
        have hcancel := Int.ediv_mul_cancel hwr
        rw [← hcancel]
        exact hcond.2.mul (Int.not_even_iff_odd.mp hneven)
      exact (Int.not_odd_iff_even.mpr ha_even) ha_odd
    obtain ⟨k, hk⟩ := hw_even
    refine ⟨2, ?_⟩
    rw [hk]
    omega
  · exact dvd_refl _

private theorem contraction_entry_dvd (T T' : NumericalType) (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i)
    (hcontraction : IsContraction T T' i e) (j : Fin T'.n) (l : Fin T.n) :
    T'.w j ∣ T.a (e j).1 l := by
  exact dvd_trans (contraction_weight_dvd T T' i e hcontraction j) (T.w_dvd _ _)

/-! The contraction maps form the commutative square in the source proof. -/
theorem contraction_square (T T' : NumericalType) (i : Fin T.n)
    (e : Fin T'.n ≃ RemainingIndex T i)
    (hcontraction : IsContraction T T' i e)
    (_hi : IsMinusOneIndex T i := by assumption) :
    (contractionP T T' i e).comp (Matrix.toLin' (picardMatrix T)) =
      (Matrix.toLin' (picardMatrix T')).comp (contractionQ T T' i e) := by
  classical
  have hweight_dvd (j : Fin T'.n) :
      T'.w j ∣ T.w (e j).1 := by
    rw [hcontraction.2.2.2.1 j]
    unfold contractedWeight
    split_ifs with hcond
    · have hwi : T.w i ∣ T.a (e j).1 i := by
        simpa [T.a_symmetric] using T.w_dvd i (e j).1
      have hwr : T.w (e j).1 ∣ T.a (e j).1 i := T.w_dvd _ _
      have hw_even : Even (T.w (e j).1) := by
        by_contra hneven
        have ha_even : Even (T.a (e j).1 i) := by
          obtain ⟨r, hr⟩ := hcond.1
          refine ⟨r * T.w i, ?_⟩
          rw [← Int.ediv_mul_cancel hwi, hr]
          ring
        have ha_odd : Odd (T.a (e j).1 i) := by
          have hcancel := Int.ediv_mul_cancel hwr
          rw [← hcancel]
          exact hcond.2.mul (Int.not_even_iff_odd.mp hneven)
        exact (Int.not_odd_iff_even.mpr ha_even) ha_odd
      obtain ⟨k, hk⟩ := hw_even
      refine ⟨2, ?_⟩
      rw [hk]
      omega
    · exact dvd_refl _
  have hdiv_target (j : Fin T'.n) (l : Fin T.n) :
      T'.w j ∣ T.a (e j).1 l := by
    have hwr : T.w (e j).1 ∣ T.a (e j).1 l := T.w_dvd _ _
    exact dvd_trans (hweight_dvd j) hwr
  have hquot_mul (j : Fin T'.n) (l : Fin T.n) :
      T.a (e j).1 l / T.w (e j).1 *
          (T.w (e j).1 / T'.w j) = T.a (e j).1 l / T'.w j := by
    obtain ⟨q, hq⟩ := hweight_dvd j
    obtain ⟨r, hr⟩ := T.w_dvd (e j).1 l
    calc
      T.a (e j).1 l / T.w (e j).1 * (T.w (e j).1 / T'.w j) =
          r * (T.w (e j).1 / T'.w j) := by
            rw [hr, Int.mul_ediv_cancel_left _ (ne_of_gt (T.w_pos (e j).1))]
      _ = r * q := by
        rw [hq, Int.mul_ediv_cancel_left _ (ne_of_gt (T'.w_pos j))]
      _ = (T.w (e j).1 * r) / T'.w j := by
        rw [hq]
        rw [show T'.w j * q * r = T'.w j * (q * r) by ring,
          Int.mul_ediv_cancel_left _ (ne_of_gt (T'.w_pos j))]
        ring
      _ = T.a (e j).1 l / T'.w j := by rw [hr]
  have hadd_div (a b d : ℤ) (hd : 0 < d) (ha : d ∣ a) (hb : d ∣ b) :
      (a + b) / d = a / d + b / d := by
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    have hdu := Int.mul_ediv_cancel_left u (ne_of_gt hd)
    have hdv := Int.mul_ediv_cancel_left v (ne_of_gt hd)
    have hduv := Int.mul_ediv_cancel_left (u + v) (ne_of_gt hd)
    rw [hu, hv, show d * u + d * v = d * (u + v) by ring,
      hdu, hdv, hduv]
  apply LinearMap.ext
  intro x
  funext j
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
  change (picardMatrix T).mulVec x i * (T.a i (e j).1 / T'.w j) +
      (picardMatrix T).mulVec x (e j).1 * (T.w (e j).1 / T'.w j) =
    (picardMatrix T').mulVec (fun k => x (e k).1) j
  simp only [Matrix.mulVec_apply_eq_sum, picardMatrix]
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  let c : Fin T.n → ℤ := fun l =>
    (T.a i l / T.w i * x l * (T.a i (e j).1 / T'.w j) +
      T.a (e j).1 l / T.w (e j).1 * x l * (T.w (e j).1 / T'.w j))
  change (∑ l, c l) = _
  have hci : c i = 0 := by
    dsimp [c]
    have hai : T.a i i / T.w i = -1 := by
      rw [_hi.2]
      simp [Int.neg_ediv, Int.ediv_self (ne_of_gt (T.w_pos i))]
    rw [hai]
    rw [show T.a (e j).1 i / T.w (e j).1 * x i *
        (T.w (e j).1 / T'.w j) =
        (T.a (e j).1 i / T.w (e j).1 *
          (T.w (e j).1 / T'.w j)) * x i by ring, hquot_mul j i]
    rw [T.a_symmetric (e j).1 i]
    ring
  rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin T.n)))
    (f := c) (Finset.mem_univ i), hci, add_zero]
  symm
  apply Finset.sum_bij (s := (Finset.univ : Finset (Fin T'.n)))
    (t := (Finset.univ : Finset (Fin T.n)).erase i)
    (f := fun k => T'.a j k / T'.w j * x (e k).1)
    (g := c) (fun k _ => (e k).1)
  · intro k hk
    exact Finset.mem_erase.mpr ⟨(e k).2, Finset.mem_univ _⟩
  · intro k₁ hk₁ k₂ hk₂ h
    exact e.injective (Subtype.ext h)
  · intro l hl
    let l' : RemainingIndex T i := ⟨l, (Finset.mem_erase.mp hl).1⟩
    refine ⟨e.symm l', Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply l')
  · intro k hk
    dsimp [c]
    have hdivi : T.w i ∣ T.a i (e k).1 := T.w_dvd i (e k).1
    have hdivj : T'.w j ∣ T.a i (e j).1 := by
      simpa [T.a_symmetric] using hdiv_target j i
    have hcontract := hcontraction.2.2.1 j k
    rw [hcontract]
    obtain ⟨u, hu⟩ := hdivi
    obtain ⟨v, hv⟩ := hdivj
    have hleft :
        T.a i (e k).1 / T.w i * (T.a i (e j).1 / T'.w j) =
          (T.a i (e k).1 * T.a i (e j).1 / T.w i) / T'.w j := by
      rw [hu, hv]
      have hwi := Int.mul_ediv_cancel_left (u * (T'.w j * v))
        (ne_of_gt (T.w_pos i))
      have hwv := Int.mul_ediv_cancel_left v
        (ne_of_gt (T'.w_pos j))
      have hwuv := Int.mul_ediv_cancel_left (u * v)
        (ne_of_gt (T'.w_pos j))
      rw [Int.mul_ediv_cancel_left u (ne_of_gt (T.w_pos i)),
        show T.w i * u * (T'.w j * v) =
          T.w i * (u * (T'.w j * v)) by ring,
        hwi,
        show u * (T'.w j * v) = T'.w j * (u * v) by ring,
        hwv, hwuv]
    have hfirstx :
        T.a i (e k).1 / T.w i * x (e k).1 *
            (T.a i (e j).1 / T'.w j) =
          (T.a i (e k).1 * T.a i (e j).1 / T.w i) /
            T'.w j * x (e k).1 := by
      rw [show T.a i (e k).1 / T.w i * x (e k).1 *
          (T.a i (e j).1 / T'.w j) =
            (T.a i (e k).1 / T.w i *
              (T.a i (e j).1 / T'.w j)) * x (e k).1 by ring,
        hleft]
    have hsecondx :
        T.a (e j).1 (e k).1 / T.w (e j).1 * x (e k).1 *
            (T.w (e j).1 / T'.w j) =
          T.a (e j).1 (e k).1 / T'.w j * x (e k).1 := by
      rw [show T.a (e j).1 (e k).1 / T.w (e j).1 * x (e k).1 *
          (T.w (e j).1 / T'.w j) =
            (T.a (e j).1 (e k).1 / T.w (e j).1 *
              (T.w (e j).1 / T'.w j)) * x (e k).1 by ring,
        hquot_mul j (e k).1]
    have hcontract' : contractedIntersection T i (e j) (e k) =
        T.a (e j).1 (e k).1 +
          T.a (e j).1 i * T.a (e k).1 i / T.w i := by
      unfold contractedIntersection
      rw [_hi.2]
      simp only [Int.ediv_neg]
      ring_nf
    have hnum :
        T.a (e j).1 i * T.a (e k).1 i / T.w i =
          T.a i (e k).1 * T.a i (e j).1 / T.w i := by
      exact congrArg (fun z : ℤ => z / T.w i) (by
        rw [T.a_symmetric (e j).1 i, T.a_symmetric (e k).1 i,
          T.a_symmetric i (e k).1, T.a_symmetric i (e j).1]
        ring)
    have hprod : T'.w j ∣ T.a i (e k).1 * T.a i (e j).1 / T.w i := by
      refine ⟨u * v, ?_⟩
      rw [hu, hv]
      have hwi := Int.mul_ediv_cancel_left (T'.w j * (u * v))
        (ne_of_gt (T.w_pos i))
      have hwj := Int.mul_ediv_cancel_left (u * v)
        (ne_of_gt (T'.w_pos j))
      rw [show T.w i * u * (T'.w j * v) =
        T.w i * (T'.w j * (u * v)) by ring,
        hwi]
    rw [hfirstx, hsecondx, hcontract', hnum,
      hadd_div _ _ _ (T'.w_pos j) (hdiv_target j (e k).1) hprod]
    ring

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
    Function.Injective (contractionPicardMap T T' i e hcontraction hi) ∧
      IsElementaryAbelianTwo
        (moduleCokernel (contractionPicardMap T T' i e hcontraction hi)) := by
  have hq_surjective : Function.Surjective (contractionQ T T' i e) := by
    intro z
    let y : Fin T.n → ℤ := fun l =>
      if hl : l = i then 0 else z (e.symm ⟨l, hl⟩)
    refine ⟨y, ?_⟩
    ext j
    simp [contractionQ, y, (e j).2]
  have hkerP (z : Fin T.n → ℤ)
      (hz : contractionP T T' i e z = 0) :
      z ∈ LinearMap.range (Matrix.toLin' (picardMatrix T)) := by
    let b : Fin T.n → ℤ := -(z i) • Pi.single i 1
    refine ⟨b, ?_⟩
    ext l
    by_cases hl : l = i
    · subst l
      change (picardMatrix T).mulVec b i = z i
      change (picardMatrix T).mulVec ((-(z i)) • Pi.single i 1) i = z i
      rw [Matrix.mulVec_smul, Matrix.mulVec_single]
      simp [picardMatrix, hi.2]
      have hai : -T.w i / T.w i = -1 := by
        simp [Int.neg_ediv, Int.ediv_self (ne_of_gt (T.w_pos i))]
      rw [hai]
      ring
    · let k : Fin T'.n := e.symm ⟨l, hl⟩
      have hk : (e k).1 = l := by
        exact congrArg Subtype.val (e.apply_symm_apply ⟨l, hl⟩)
      have hcoord := congrFun hz k
      dsimp [contractionP] at hcoord
      rw [hk] at hcoord
      have hdivA : T'.w k ∣ T.a i l := by
        have h := contraction_entry_dvd T T' i e hcontraction k i
        rw [hk] at h
        simpa [T.a_symmetric] using h
      have hdivW : T'.w k ∣ T.w l := by
        simpa [hk] using contraction_weight_dvd T T' i e hcontraction k
      have hmul := congrArg (fun q : ℤ => q * T'.w k) hcoord
      have hzero : z i * T.a i l + z l * T.w l = 0 := by
        obtain ⟨u, hu⟩ := hdivA
        obtain ⟨v, hv⟩ := hdivW
        rw [hu, hv] at hmul
        rw [show (z i * (T'.w k * u / T'.w k) +
            z l * (T'.w k * v / T'.w k)) * T'.w k =
            z i * ((T'.w k * u / T'.w k) * T'.w k) +
              z l * ((T'.w k * v / T'.w k) * T'.w k) by ring] at hmul
        rw [Int.mul_ediv_cancel_left _ (ne_of_gt (T'.w_pos k)),
          Int.mul_ediv_cancel_left _ (ne_of_gt (T'.w_pos k))] at hmul
        rw [show u * T'.w k = T'.w k * u by ring, ← hu,
          show v * T'.w k = T'.w k * v by ring, ← hv] at hmul
        simpa only [zero_mul] using hmul
      obtain ⟨u, hu⟩ := T.w_dvd l i
      have hzero' : T.w l * (z i * u + z l) = 0 := by
        calc
          T.w l * (z i * u + z l) = z i * T.a i l + z l * T.w l := by
            rw [T.a_symmetric i l, hu]
            ring
          _ = 0 := hzero
      have hsum : z i * u + z l = 0 := by
        exact (mul_eq_zero.mp hzero').resolve_left (ne_of_gt (T.w_pos l))
      have huquot : T.a l i / T.w l = u := by
        rw [hu]
        exact Int.mul_ediv_cancel_left _ (ne_of_gt (T.w_pos l))
      change (picardMatrix T).mulVec ((-(z i)) • Pi.single i 1) l = z l
      rw [Matrix.mulVec_smul, Matrix.mulVec_single]
      simp [picardMatrix, huquot]
      linarith [hsum]
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := ((LinearMap.range (Matrix.toLin' (picardMatrix T))).mkQ_surjective x)
    obtain ⟨y, rfl⟩ := ((LinearMap.range (Matrix.toLin' (picardMatrix T))).mkQ_surjective y)
    have htarget :
        (contractionTargetMap T T' i e) x =
          (contractionTargetMap T T' i e) y := by
      simpa [contractionPicardMap] using hxy
    have hdiff :
        contractionP T T' i e (x - y) ∈
          LinearMap.range (Matrix.toLin' (picardMatrix T')) := by
      have hzero :
          (contractionTargetMap T T' i e) x -
            (contractionTargetMap T T' i e) y = 0 :=
        sub_eq_zero.mpr htarget
      have hmk :
          (Submodule.mkQ (LinearMap.range (Matrix.toLin' (picardMatrix T'))))
              (contractionP T T' i e (x - y)) = 0 := by
        simpa [contractionTargetMap] using hzero
      exact (Submodule.Quotient.mk_eq_zero _).mp hmk
    rcases hdiff with ⟨q, hq⟩
    obtain ⟨v, hv⟩ := hq_surjective q
    have hpzero : contractionP T T' i e (x - y -
        (Matrix.toLin' (picardMatrix T)) v) = 0 := by
      have hsquare : contractionP T T' i e
          ((Matrix.toLin' (picardMatrix T)) v) =
          (Matrix.toLin' (picardMatrix T')) (contractionQ T T' i e v) := by
        simpa only [LinearMap.comp_apply] using
          LinearMap.congr_fun (contraction_square T T' i e hcontraction hi) v
      rw [map_sub, ← hq, hsquare, hv]
      simp
    have hmem := hkerP (x - y - (Matrix.toLin' (picardMatrix T)) v) hpzero
    apply (Submodule.Quotient.eq _).mpr
    have hfmem : (Matrix.toLin' (picardMatrix T)) v ∈
        LinearMap.range (Matrix.toLin' (picardMatrix T)) := ⟨v, rfl⟩
    have hadd := (LinearMap.range (Matrix.toLin' (picardMatrix T))).add_mem
      hmem hfmem
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
  · intro x
    refine Submodule.Quotient.induction_on
      (LinearMap.range (contractionPicardMap T T' i e hcontraction hi)) x ?_
    intro z
    change (2 : ℤ) • (Submodule.Quotient.mk z) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine Submodule.Quotient.induction_on
      (LinearMap.range (Matrix.toLin' (picardMatrix T'))) z ?_
    intro w
    have htwo_range : (2 : ℤ) • w ∈
        LinearMap.range (contractionP T T' i e) := by
      classical
      choose u hu using
        contractionP_two_smul_basis_mem_range T T' i e hcontraction
      refine ⟨∑ j, w j • u j, ?_⟩
      ext k
      simp only [map_sum, map_smul, hu, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Pi.single_apply]
      rw [Finset.sum_eq_single k]
      · simp
        ring
      · intro j hj hjk
        have hkj : k ≠ j := Ne.symm hjk
        simp [hkj]
      · simp
    rcases htwo_range with ⟨v, hv⟩
    refine ⟨Submodule.mkQ (LinearMap.range (Matrix.toLin' (picardMatrix T))) v, ?_⟩
    change (Submodule.mkQ (LinearMap.range (Matrix.toLin' (picardMatrix T'))))
        (contractionP T T' i e v) =
      (2 : ℤ) • (Submodule.mkQ (LinearMap.range (Matrix.toLin' (picardMatrix T'))) w)
    rw [hv]
    rfl

private theorem picard_group_genus_nonpositive_linear :
    ∀ n : ℕ, ∀ T : NumericalType, T.n = n → genus T ≤ 0 →
      Nonempty (picardGroup T ≃ₗ[ℤ] ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T hn hgenus
    by_cases hn1 : T.n = 1
    · let fP := Matrix.toLin' (picardMatrix T)
      have hai : ∀ i, T.a i i = 0 := by
        intro i
        have hprod : T.a i i * T.m i = 0 := by
          calc
            T.a i i * T.m i =
                (∑ j, T.a i j * T.m j) := by
              symm
              rw [Finset.sum_eq_single i]
              · intro b hb hbi
                exfalso
                apply hbi
                apply Fin.ext
                omega
              · simp
            _ = 0 := T.row_sum i
        exact (mul_eq_zero.mp hprod).resolve_right
          (ne_of_gt (T.m_pos i))
      have haij : ∀ i j, T.a i j = 0 := by
        intro i j
        have hij : j = i := by
          apply Fin.ext
          omega
        simpa [hij] using hai i
      have hfPzero : fP = 0 := by
        apply LinearMap.ext
        intro x
        funext i
        change (picardMatrix T).mulVec x i = 0
        simp [Matrix.mulVec_apply_eq_sum, picardMatrix, haij]
      have hPbot : LinearMap.range fP = ⊥ := by
        rw [hfPzero]
        simp
      let qequiv : picardGroup T ≃ₗ[ℤ] (Fin T.n → ℤ) :=
        (LinearMap.range fP).quotEquivOfEqBot hPbot
      let eval : (Fin T.n → ℤ) →ₗ[ℤ] ℤ :=
        { toFun := fun x => x (firstIndex T)
          map_add' := by intro x y; rfl
          map_smul' := by intro r x; rfl }
      have heval_bijective : Function.Bijective eval := by
        constructor
        · intro x y hxy
          funext i
          have hi : i = firstIndex T := by
            apply Fin.ext
            omega
          rw [hi]
          simpa [eval] using hxy
        · intro z
          refine ⟨fun _ => z, ?_⟩
          rfl
      let eeval : (Fin T.n → ℤ) ≃ₗ[ℤ] ℤ :=
        LinearEquiv.ofBijective eval heval_bijective
      exact ⟨qequiv.trans eeval⟩
    · have hTpos := T.hn
      have hn2 : 2 ≤ T.n := by omega
      have hex : ∃ i, IsMinusOneIndex T i := by
        by_contra hno
        have hminimal : IsMinimal T := by
          intro h
          exact hno h
        have hpos := minimal_genus_at_least_one T (genus T) rfl hminimal hn2
        omega
      rcases hex with ⟨i, hi⟩
      rcases exists_contraction T i hi with ⟨T', e, hcontraction⟩
      have hT'n : T'.n < n := by
        calc
          T'.n = T.n - 1 := hcontraction.1
          _ < T.n := by omega
          _ = n := hn
      have hgenus' : genus T' ≤ 0 := by
        rw [hcontraction.2.2.2.2.2]
        exact hgenus
      rcases ih T'.n hT'n T' rfl hgenus' with ⟨eT'⟩
      let F : picardGroup T →ₗ[ℤ] ℤ :=
        eT'.toLinearMap.comp (contractionPicardMap T T' i e hcontraction hi)
      have hFinj : Function.Injective F := by
        exact eT'.injective.comp
          (contract_picard_group T T' i hi e hcontraction).1
      let : Module.IsTorsionFree ℤ (picardGroup T) :=
        Function.Injective.moduleIsTorsionFree F hFinj (by
          intro r x
          exact F.map_smul r x)
      have hfinite := (picard_group_finite_rank_one T).1
      let : Module.Finite ℤ (picardGroup T) := hfinite
      exact ⟨LinearEquiv.ofFinrankEq (picardGroup T) ℤ (by
        rw [(picard_group_finite_rank_one T).2]
        simp)⟩

/-! In nonpositive genus the Picard group is isomorphic to the integers. -/
theorem picard_group_genus_nonpositive (T : NumericalType)
    (hgenus : genus T ≤ 0) :
    Nonempty (picardGroup T ≃+ ℤ) := by
  rcases picard_group_genus_nonpositive_linear T.n T rfl hgenus with ⟨e⟩
  exact ⟨e.toAddEquiv⟩

end Formalization.Books.Models.Unit04
