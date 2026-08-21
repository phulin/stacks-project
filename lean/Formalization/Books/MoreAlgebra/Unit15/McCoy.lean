import Formalization.Books.Algebra.Unit15.Miscellany
import Formalization.Books.Algebra.Unit24.GlueingFunctions
import Formalization.Books.Algebra.Unit66.WeaklyAssociatedPrimes
import Formalization.Books.Algebra.Unit82.UniversallyInjective
import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Formalization.Books.Algebra.Unit88.MittagLefflerModules
import Formalization.Books.Algebra.Unit91.ExamplesAndNonExamples
import Formalization.Books.Algebra.Unit102.WhatMakesAComplexExact
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology

namespace Formalization.Books.MoreAlgebra.Unit15

open Formalization.Books.Algebra.Unit66
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Algebra.Unit88
open scoped TensorProduct

universe u v w

noncomputable section
theorem annihilator_maximalMinorIdeal_eq_bot_of_injective
    {R : Type u} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) R)
    (hA : Function.Injective (Matrix.mulVecLin A)) :
    let minorIdeal (k : ℕ) : Ideal R :=
      Ideal.span (Set.range fun p :
        (Fin k ↪ Fin n) × (Fin k ↪ Fin m) =>
        (A.submatrix p.1 p.2).det)
    Module.annihilator R (minorIdeal m) = ⊥ := by
  classical
  let minorIdeal (k : ℕ) : Ideal R :=
    Ideal.span (Set.range fun p :
      (Fin k ↪ Fin n) × (Fin k ↪ Fin m) =>
      (A.submatrix p.1 p.2).det)
  apply le_bot_iff.mp
  intro a ha
  change (a : R) = 0
  by_contra ha0
  let D : ℕ → Ideal R := minorIdeal
  have hex : ∃ k : ℕ, a ∈ Module.annihilator R (D k) := ⟨m, ha⟩
  let k : ℕ := Nat.find hex
  have hk : a ∈ Module.annihilator R (D k) := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hkzero
    rw [hkzero] at hk
    have hone : (1 : R) ∈ D 0 := by
      apply Ideal.subset_span
      refine ⟨⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩,
        ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩, ?_⟩
      simp [D, minorIdeal, Matrix.det_fin_zero]
    have ha1 := Module.mem_annihilator.mp hk ⟨1, hone⟩
    exact ha0 (by simpa [smul_eq_mul] using congrArg Subtype.val ha1)
  obtain ⟨r, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  rw [hk_eq] at hk
  have hk' : a ∈ Module.annihilator R (D (r + 1)) := by
    simpa [Nat.succ_eq_add_one] using hk
  have hrnot : a ∉ Module.annihilator R (D r) := by
    intro hDr
    have hle0 := Nat.find_min' hex hDr
    have hle : r + 1 ≤ r := by omega
    omega
  have hminor : ∃ p : (Fin r ↪ Fin n) × (Fin r ↪ Fin m),
      a * (A.submatrix p.1 p.2).det ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hrnot
    rw [Module.mem_annihilator]
    intro z
    apply Subtype.ext
    change (a : R) * (z : R) = 0
    let K : Ideal R :=
      { carrier := {y : R | (a : R) * y = 0}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [mul_add, hx, hy, zero_add]
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_setOf_eq] at hx ⊢
          calc
            (a : R) * (c • x) = c * ((a : R) * x) := by
              simp [smul_eq_mul, mul_assoc, mul_left_comm]
            _ = 0 := by rw [hx, mul_zero] }
    have hDK : D r ≤ K := by
      dsimp [D, minorIdeal]
      rw [Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      exact hnone p
    exact hDK z.property
  obtain ⟨p, hminor⟩ := hminor
  have hrm : r < m := by
    have hle0 := Nat.find_min' hex ha
    have hle : r + 1 ≤ m := by omega
    omega
  obtain ⟨c, hc⟩ : ∃ c : Fin m, c ∉ Set.range p.2 := by
    by_contra hall
    push_neg at hall
    have hsurj : Function.Surjective p.2 := fun y => hall y
    have hcard0 := Fintype.card_le_of_surjective p.2 hsurj
    have hcard : m ≤ r := by simpa using hcard0
    omega
  let er : Fin r ↪ Fin n := p.1
  let optionFun : Option (Fin r) → Fin m := fun o => o.elim c p.2
  have hoption : Function.Injective optionFun := by
    intro s t hst
    cases s with
    | none =>
        cases t with
        | none => rfl
        | some t =>
            exfalso
            apply hc
            exact ⟨t, by simpa [optionFun] using hst.symm⟩
    | some s =>
        cases t with
        | none =>
            exfalso
            apply hc
            exact ⟨s, by simpa [optionFun] using hst⟩
        | some t =>
            exact congrArg some (p.2.injective (by simpa [optionFun] using hst))
  let ec : Fin (r + 1) ↪ Fin m :=
    ⟨fun i => optionFun (finSuccEquivLast i),
      hoption.comp finSuccEquivLast.injective⟩
  let j₀ : Fin (r + 1) := Fin.last r
  let coeff : Fin (r + 1) → R := fun j =>
    (a : R) * (-1 : R) ^ ((Fin.last r : ℕ) + (j : ℕ)) *
      (A.submatrix er (fun t => ec (j.succAbove t))).det
  let x : Fin m → R := ∑ j : Fin (r + 1), Pi.single (ec j) (coeff j)
  have hx_apply (j : Fin (r + 1)) : x (ec j) = coeff j := by
    simp only [x, Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp only [ite_eq_right_iff]
      intro hjb
      exact (hb (ec.injective hjb).symm).elim
    · simp
  have hcoeff_ne : coeff j₀ ≠ 0 := by
    dsimp [coeff]
    intro hzero
    apply hminor
    let s : R := (-1 : R) ^ ((Fin.last r : ℕ) + (j₀ : ℕ))
    have hs : s * s = 1 := by
      dsimp [s]
      rw [← pow_add]
      simp
    have hzero' : (a : R) * s * (A.submatrix er p.2).det = 0 := by
      simpa [s, ec, optionFun, j₀, Fin.succAbove_last] using hzero
    calc
      (a : R) * (A.submatrix p.1 p.2).det =
          (s * s) * ((a : R) * (A.submatrix er p.2).det) := by rw [hs, one_mul]
      _ = s * ((a : R) * s * (A.submatrix er p.2).det) := by
        simp [er, mul_assoc, mul_left_comm, mul_comm]
      _ = 0 := by rw [hzero', mul_zero]
  have hxne : x ≠ 0 := by
    intro hxzero
    apply hcoeff_ne
    rw [← hx_apply j₀, hxzero]
    rfl
  apply hxne
  apply hA
  funext i
  let rowFun : Fin (r + 1) → Fin n := Fin.lastCases i er
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
    A.submatrix rowFun ec
  have hdet : (a : R) * B.det = 0 := by
    by_cases hrow : Function.Injective rowFun
    · let rowEmb : Fin (r + 1) ↪ Fin n := ⟨rowFun, hrow⟩
      have hmem : B.det ∈ D (r + 1) := by
        apply Ideal.subset_span
        exact ⟨(rowEmb, ec), rfl⟩
      have hz := Module.mem_annihilator.mp hk' ⟨B.det, hmem⟩
      simpa [smul_eq_mul] using congrArg Subtype.val hz
    · obtain ⟨s, t, heq, hst⟩ := Function.not_injective_iff.mp hrow
      have hrowsame : B s = B t := by
        funext j
        exact congrArg (fun z => A z (ec j)) heq
      rw [Matrix.det_zero_of_row_eq hst hrowsame, mul_zero]
  have hlap := Matrix.det_succ_row B (Fin.last r)
  have hsub (j : Fin (r + 1)) :
      B.submatrix (Fin.last r).succAbove j.succAbove =
        A.submatrix er (fun t => ec (j.succAbove t)) := by
    ext s t
    simp [B, rowFun, er, Fin.succAbove_last]
  calc
    Matrix.mulVec A x i =
        ∑ j : Fin (r + 1), A i (ec j) * coeff j := by
          change (Matrix.mulVecLin A x) i = _
          rw [show x = ∑ j : Fin (r + 1), Pi.single (ec j) (coeff j) by rfl,
            map_sum]
          rw [Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro j _
          simp [Matrix.mulVecLin_apply, Matrix.mulVec, ec.injective.eq_iff]
    _ = (a : R) * B.det := by
      rw [hlap]
      simp_rw [hsub]
      dsimp [coeff, B, rowFun]
      simp only [Fin.lastCases_last, Matrix.submatrix_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := hdet
    _ = Matrix.mulVecLin A 0 i := by simp

theorem exteriorPower_map_ne_zero_of_full_minor_ne_zero
    {R : Type u} [CommRing R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (p : (Fin m ↪ Fin n) × (Fin m ↪ Fin m))
    (hp : ((LinearMap.toMatrix' φ).submatrix p.1 p.2).det ≠ 0) :
    exteriorPower.map m φ ≠ 0 := by
  classical
  let A : Matrix (Fin n) (Fin m) R := LinearMap.toMatrix' φ
  let rows : Finset (Fin n) := Finset.univ.image p.1
  have hrows : rows.card = m := by
    dsimp [rows]
    rw [Finset.card_image_of_injective _ p.1.injective]
    simp
  let e : Fin m ≃ {x // x ∈ rows} := rows.orderIsoOfFin hrows
  let pe : Fin m ≃ {x // x ∈ rows} := Equiv.ofBijective
    (fun i => (⟨p.1 i, Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩⟩ : {x // x ∈ rows}))
    ⟨fun i j hij => p.1.injective (congrArg Subtype.val hij), fun z => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp z.property
      exact ⟨i, Subtype.ext hi⟩⟩
  let σ : Equiv.Perm (Fin m) := pe.trans e.symm
  let τ : Equiv.Perm (Fin m) :=
    Equiv.ofBijective p.2 (Finite.injective_iff_bijective.mp p.2.injective)
  let M : Matrix (Fin m) (Fin m) R :=
    A.submatrix (fun i => (e i).1) id
  have hrow (i : Fin m) : (e (σ i)).1 = p.1 i := by
    exact congrArg Subtype.val (e.apply_symm_apply (pe i))
  have hmatrix : A.submatrix p.1 p.2 = M.submatrix σ τ := by
    ext i j
    simp only [Matrix.submatrix_apply, M]
    rw [hrow]
    rfl
  have hM : M.det ≠ 0 := by
    intro hzero
    apply hp
    change (A.submatrix p.1 p.2).det = 0
    rw [hmatrix]
    have hsub : M.submatrix σ τ =
        (M.submatrix σ id).submatrix id τ := by
      ext i j
      rfl
    rw [hsub, Matrix.det_permute', Matrix.det_permute, hzero, mul_zero,
      mul_zero]
  intro hmap
  let b : Module.Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n)
  let erows : Fin m ↪o Fin n := rows.orderEmbOfFin hrows
  let S : Set.powersetCard (Fin n) m :=
    Set.powersetCard.ofFinEmbEquiv erows
  let v : Fin m → (Fin m → R) := fun j => Pi.single j 1
  have hzero : exteriorPower.map m φ (exteriorPower.ιMulti R m v) = 0 := by
    rw [hmap]
    rfl
  have hdual := congrArg (exteriorPower.ιMultiDual R m b S) hzero
  apply hM
  rw [exteriorPower.map_apply_ιMulti,
    exteriorPower.ιMultiDual_apply_ιMulti] at hdual
  have hdualMatrix :
      Matrix.of (fun i j =>
        b.coord (Set.powersetCard.ofFinEmbEquiv.symm S j) (φ (v i))) =
        M.transpose := by
    ext i j
    simp [M, A, b, S, erows, v, LinearMap.toMatrix'_apply,
      Matrix.of_apply]
    have heq : (rows.orderEmbOfFin hrows j : Fin n) = (e j).1 := by rfl
    rw [heq]
  have hdual' :
      (Matrix.of fun i j =>
        b.coord (Set.powersetCard.ofFinEmbEquiv.symm S j) (φ (v i))).det = 0 := by
    simpa [Function.comp_apply] using hdual
  rw [hdualMatrix, Matrix.det_transpose] at hdual'
  exact hdual'

end

end Formalization.Books.MoreAlgebra.Unit15
