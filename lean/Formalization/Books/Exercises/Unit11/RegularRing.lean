import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Tactic.IntervalCases

/-!
# Exercises, Chapter 11: Ext over a regular ring

The source uses `k[x,y]` and identifies `k` with the residue ring at the
origin.  The latter is represented by the canonical ideal quotient; the
evaluation map and the quotient-to-`k` identification are recorded
separately so that the exact sequence uses Mathlib's standard module object.
-/

namespace Formalization.Books.Exercises.Unit11

open CategoryTheory
open Formalization.Books.Algebra.Unit71
open scoped ZeroObject

universe u

noncomputable section

/-! ## The polynomial ring and its residue field at the origin -/

abbrev twoVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

def originIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
      Set (twoVariablePolynomialRing k))

/-- Evaluation at `(0, 0)`, the last nonzero map in the displayed complex. -/
def originEvaluationAtZero (k : Type u) [Field k] :
    twoVariablePolynomialRing k →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : Fin 2 => 0)

/-- The canonical residue ring `k[x,y]/(x,y)`, used as an `R`-module. -/
abbrev originResidueRing (k : Type u) [Field k] :=
  twoVariablePolynomialRing k ⧸ originIdeal k

abbrev originResidueModule (k : Type u) [Field k] :
    ModuleCat (twoVariablePolynomialRing k) :=
  ModuleCat.of (twoVariablePolynomialRing k) (originResidueRing k)

/-- The quotient model of the source's coefficient field, together with the
identification under which the quotient map is evaluation at the origin. -/
theorem origin_residue_ring_isomorphic_to_field (k : Type u) [Field k] :
    ∃ e : originResidueRing k ≃+* k,
      e.toRingHom.comp
          (Ideal.Quotient.mkₐ (twoVariablePolynomialRing k) (originIdeal k)).toRingHom =
        originEvaluationAtZero k := by
  let R := twoVariablePolynomialRing k
  let f : R →+* k := originEvaluationAtZero k
  have hmem : ∀ p : R, p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ originIdeal k := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        rw [MvPolynomial.constantCoeff_C]
        simpa only [sub_self] using (originIdeal k).zero_mem
    | add p q hp hq =>
        simpa [map_add, sub_add_sub_comm] using (Ideal.add_mem (originIdeal k) hp hq)
    | mul_X p i hp =>
        have hi : MvPolynomial.X i ∈ originIdeal k := by
          apply Ideal.subset_span
          fin_cases i <;> simp
        have h := (originIdeal k).mul_mem_left p hi
        have hc : MvPolynomial.constantCoeff (p * MvPolynomial.X i) = 0 := by
          change MvPolynomial.coeff 0 (p * MvPolynomial.X i) = 0
          rw [MvPolynomial.coeff_mul]
          simp
        rw [hc, map_zero, sub_zero]
        exact h
  have hker : RingHom.ker f = originIdeal k := by
    apply le_antisymm
    · intro p hp
      have hp' := hmem p
      have hc : MvPolynomial.constantCoeff p = 0 := by
        simpa [f, originEvaluationAtZero, MvPolynomial.eval₂Hom_zero_apply] using hp
      simpa [hc] using hp'
    · refine Ideal.span_le.2 ?_
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · change MvPolynomial.eval₂ (RingHom.id k) (fun _ : Fin 2 => 0)
          (MvPolynomial.X 0) = 0
        rw [MvPolynomial.eval₂_X]
      · change MvPolynomial.eval₂ (RingHom.id k) (fun _ : Fin 2 => 0)
          (MvPolynomial.X 1) = 0
        rw [MvPolynomial.eval₂_X]
  have hf : Function.Surjective f := by
    intro a
    refine ⟨MvPolynomial.C a, ?_⟩
    change MvPolynomial.eval₂ (RingHom.id k) (fun _ : Fin 2 => 0) (MvPolynomial.C a) = a
    rw [MvPolynomial.eval₂_C]
    rfl
  let e₀ : R ⧸ RingHom.ker f ≃+* k :=
    RingHom.quotientKerEquivOfSurjective hf
  let q : R ⧸ RingHom.ker f ≃+* R ⧸ originIdeal k :=
    Ideal.quotientEquiv (RingHom.ker f) (originIdeal k) (RingEquiv.refl R) (by
      simpa using hker.symm)
  refine ⟨q.symm.trans e₀, ?_⟩
  apply RingHom.ext
  intro p
  change e₀ (q.symm (Ideal.Quotient.mk (originIdeal k) p)) = f p
  have hq : q.symm (Ideal.Quotient.mk (originIdeal k) p) =
      Ideal.Quotient.mk (RingHom.ker f) p := by
    dsimp [q]
    rw [Ideal.quotientEquiv_symm_mk]
    rfl
  rw [hq]
  simpa [e₀] using (RingHom.quotientKerEquivOfSurjective_apply_mk hf p)

/-! ## The displayed Koszul complex -/

/-- The column map `f ↦ (y f, -x f)`. -/
def koszulFirstDifferential (k : Type u) [Field k] :
    twoVariablePolynomialRing k →ₗ[twoVariablePolynomialRing k]
      twoVariablePolynomialRing k × twoVariablePolynomialRing k :=
  (LinearMap.mulLeft (twoVariablePolynomialRing k)
      (MvPolynomial.X (1 : Fin 2))).prod
    (LinearMap.mulLeft (twoVariablePolynomialRing k)
      (-MvPolynomial.X (0 : Fin 2)))

/-- The row map `(x, y)`. -/
def koszulSecondDifferential (k : Type u) [Field k] :
    (twoVariablePolynomialRing k × twoVariablePolynomialRing k) →ₗ[
      twoVariablePolynomialRing k] twoVariablePolynomialRing k :=
  (LinearMap.mulLeft (twoVariablePolynomialRing k)
      (MvPolynomial.X (0 : Fin 2))).comp
      (LinearMap.fst (twoVariablePolynomialRing k)
        (twoVariablePolynomialRing k) (twoVariablePolynomialRing k)) +
    (LinearMap.mulLeft (twoVariablePolynomialRing k)
      (MvPolynomial.X (1 : Fin 2))).comp
      (LinearMap.snd (twoVariablePolynomialRing k)
        (twoVariablePolynomialRing k) (twoVariablePolynomialRing k))

/-- The quotient map `R → R/(x,y)`, corresponding to evaluation at the origin. -/
def koszulAugmentation (k : Type u) [Field k] :
    twoVariablePolynomialRing k →ₗ[twoVariablePolynomialRing k]
      originResidueRing k :=
  (Ideal.Quotient.mkₐ (twoVariablePolynomialRing k) (originIdeal k)).toLinearMap

/-- The six objects and five arrows in the source's Koszul complex. -/
def koszulComplex (k : Type u) [Field k] :
    ComposableArrows (ModuleCat (twoVariablePolynomialRing k)) 5 :=
  ComposableArrows.mk₅
    (0 : (0 : ModuleCat (twoVariablePolynomialRing k)) ⟶
      ModuleCat.of (twoVariablePolynomialRing k) (twoVariablePolynomialRing k))
    (ModuleCat.ofHom (koszulFirstDifferential k))
    (ModuleCat.ofHom (koszulSecondDifferential k))
    (ModuleCat.ofHom (koszulAugmentation k))
    (0 : originResidueModule k ⟶ (0 : ModuleCat (twoVariablePolynomialRing k)))

private theorem koszul_first_injective (k : Type u) [Field k] :
    Function.Injective (koszulFirstDifferential k) := by
  intro a b hab
  have hab' : MvPolynomial.X (1 : Fin 2) * a =
      MvPolynomial.X (1 : Fin 2) * b := by
    exact congrArg Prod.fst hab
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := k) (1 : Fin 2)) hab'

private theorem koszul_middle_exact (k : Type u) [Field k] :
    Function.Exact (koszulFirstDifferential k) (koszulSecondDifferential k) := by
  let R := twoVariablePolynomialRing k
  let x : R := MvPolynomial.X (0 : Fin 2)
  let y : R := MvPolynomial.X (1 : Fin 2)
  have hx : x ≠ 0 := by
    change MvPolynomial.X (0 : Fin 2) ≠ 0
    exact MvPolynomial.X_ne_zero (R := k) (0 : Fin 2)
  intro z
  constructor
  · intro hz
    rcases z with ⟨a, b⟩
    change x * a + y * b = 0 at hz
    have hdiv : x ∣ y * b := by
      refine ⟨-a, ?_⟩
      calc
        y * b = -(x * a) := eq_neg_of_add_eq_zero_right hz
        _ = x * (-a) := by ring
    rcases (MvPolynomial.X_dvd_mul_iff.mp hdiv) with hxy | hb
    · have h01 : (0 : Fin 2) = 1 := MvPolynomial.X_dvd_X.mp hxy
      exact ((by decide : (0 : Fin 2) ≠ 1) h01).elim
    · rcases hb with ⟨c, hc⟩
      have hfactor : x * (a + y * c) = 0 := by
        calc
          x * (a + y * c) = x * a + y * (x * c) := by ring
          _ = x * a + y * b := by rw [hc]
          _ = 0 := hz
      have hsum : a + y * c = 0 := (mul_eq_zero.mp hfactor).resolve_left hx
      have ha : a = -(y * c) := eq_neg_of_add_eq_zero_left hsum
      refine ⟨-c, ?_⟩
      apply Prod.ext
      · change y * (-c) = a
        rw [mul_neg]
        exact ha.symm
      · change -x * (-c) = b
        rw [neg_mul, mul_neg, neg_neg]
        simpa [x] using hc.symm
  · rintro ⟨c, hc⟩
    rcases z with ⟨a, b⟩
    have hca : y * c = a := congrArg Prod.fst hc
    have hcb : -x * c = b := congrArg Prod.snd hc
    change x * a + y * b = 0
    rw [← hca, ← hcb]
    ring

private theorem koszul_range (k : Type u) [Field k] :
    ∀ p : twoVariablePolynomialRing k, p ∈ originIdeal k →
      ∃ z : twoVariablePolynomialRing k × twoVariablePolynomialRing k,
        koszulSecondDifferential k z = p := by
  let R := twoVariablePolynomialRing k
  let x : R := MvPolynomial.X (0 : Fin 2)
  let y : R := MvPolynomial.X (1 : Fin 2)
  intro p hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · refine ⟨(1, 0), ?_⟩
        change x * 1 + y * 0 = x
        simp
      · refine ⟨(0, 1), ?_⟩
        change x * 0 + y * 1 = y
        simp
  | zero =>
      exact ⟨0, by simp [koszulSecondDifferential]⟩
  | add p q hp hq ihp ihq =>
      rcases ihp with ⟨a, ha⟩
      rcases ihq with ⟨b, hb⟩
      change x * a.1 + y * a.2 = p at ha
      change x * b.1 + y * b.2 = q at hb
      refine ⟨(a.1 + b.1, a.2 + b.2), ?_⟩
      change x * (a.1 + b.1) + y * (a.2 + b.2) = p + q
      calc
        x * (a.1 + b.1) + y * (a.2 + b.2) =
            (x * a.1 + y * a.2) + (x * b.1 + y * b.2) := by ring
        _ = p + q := by rw [ha, hb]
  | smul r p hp ih =>
      rcases ih with ⟨a, ha⟩
      change x * a.1 + y * a.2 = p at ha
      refine ⟨(r * a.1, r * a.2), ?_⟩
      change x * (r * a.1) + y * (r * a.2) = r * p
      calc
        x * (r * a.1) + y * (r * a.2) = r * (x * a.1 + y * a.2) := by ring
        _ = r * p := by rw [ha]

private theorem koszul_second_comp_first (k : Type u) [Field k] :
    (koszulSecondDifferential k).comp (koszulFirstDifferential k) = 0 := by
  apply LinearMap.ext
  intro z
  change MvPolynomial.X (0 : Fin 2) * (MvPolynomial.X (1 : Fin 2) * z) +
      MvPolynomial.X (1 : Fin 2) * (-MvPolynomial.X (0 : Fin 2) * z) = 0
  ring

private theorem koszul_x_mem (k : Type u) [Field k] :
    MvPolynomial.X (0 : Fin 2) ∈ originIdeal k := by
  apply Ideal.subset_span
  simp [originIdeal]

private theorem koszul_y_mem (k : Type u) [Field k] :
    MvPolynomial.X (1 : Fin 2) ∈ originIdeal k := by
  apply Ideal.subset_span
  simp [originIdeal]

private theorem koszul_second_mem_origin (k : Type u) [Field k]
    (a b : twoVariablePolynomialRing k) :
    MvPolynomial.X (0 : Fin 2) * a + MvPolynomial.X (1 : Fin 2) * b ∈
      originIdeal k := by
  have hxa : a * MvPolynomial.X (0 : Fin 2) ∈ originIdeal k :=
    (originIdeal k).mul_mem_left a (koszul_x_mem k)
  have hyb : b * MvPolynomial.X (1 : Fin 2) ∈ originIdeal k :=
    (originIdeal k).mul_mem_left b (koszul_y_mem k)
  have hadd := (originIdeal k).add_mem hxa hyb
  simpa [mul_comm] using hadd

/-- The displayed Koszul complex is exact, with the injectivity of the map
`R → R × R` and the surjectivity of the map `R → R/(x,y)` exposed
explicitly. -/
theorem koszulComplex_exact (k : Type u) [Field k] :
    (koszulComplex k).Exact ∧
      Mono ((koszulComplex k).map' 1 2) ∧
      Epi ((koszulComplex k).map' 3 4) := by
  have hfirst := koszul_first_injective k
  have hmiddle := koszul_middle_exact k
  have hrange := koszul_range k
  let S₀ : ShortComplex (ModuleCat (twoVariablePolynomialRing k)) :=
    ShortComplex.mk
      (0 : (0 : ModuleCat (twoVariablePolynomialRing k)) ⟶
        ModuleCat.of (twoVariablePolynomialRing k) (twoVariablePolynomialRing k))
      (ModuleCat.ofHom (koszulFirstDifferential k)) (by simp)
  let S₁ : ShortComplex (ModuleCat (twoVariablePolynomialRing k)) :=
    ShortComplex.moduleCatMk (koszulFirstDifferential k)
      (koszulSecondDifferential k) (koszul_second_comp_first k)
  let S₂ : ShortComplex (ModuleCat (twoVariablePolynomialRing k)) :=
    ShortComplex.moduleCatMkOfKerLERange
      (ModuleCat.ofHom (koszulSecondDifferential k))
      (ModuleCat.ofHom (koszulAugmentation k))
      (by
        change LinearMap.range (koszulSecondDifferential k) ≤
          LinearMap.ker (koszulAugmentation k)
        intro p hp
        rcases hp with ⟨z, rfl⟩
        rcases z with ⟨a, b⟩
        change koszulAugmentation k (koszulSecondDifferential k (a, b)) = 0
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact koszul_second_mem_origin k a b)
  let S₃ : ShortComplex (ModuleCat (twoVariablePolynomialRing k)) :=
    ShortComplex.mk
      (ModuleCat.ofHom (koszulAugmentation k))
      (0 : originResidueModule k ⟶
        (0 : ModuleCat (twoVariablePolynomialRing k))) (by simp)
  have hS₀ : S₀.Exact := by
    rw [S₀.moduleCat_exact_iff]
    intro a ha
    refine ⟨0, ?_⟩
    change koszulFirstDifferential k a = 0 at ha
    have ha0 : a = 0 := hfirst (by simpa using ha)
    change 0 = a
    simp [ha0]
  have hS₁ : S₁.Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₁]
    exact hmiddle
  have hS₂ : S₂.Exact := by
    rw [S₂.moduleCat_exact_iff]
    intro p hp
    have hp' : p ∈ originIdeal k := Ideal.Quotient.eq_zero_iff_mem.mp hp
    exact hrange p hp'
  have hS₃ : S₃.Exact := by
    rw [S₃.moduleCat_exact_iff]
    intro q _
    rcases Ideal.Quotient.mk_surjective q with ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  have hcomplex : (koszulComplex k).IsComplex := by
    refine ⟨?_⟩
    intro i hi
    have hi' : i ≤ 3 := by omega
    interval_cases i
    · change (0 : (0 : ModuleCat (twoVariablePolynomialRing k)) ⟶
        ModuleCat.of (twoVariablePolynomialRing k) (twoVariablePolynomialRing k)) ≫
        ModuleCat.ofHom (koszulFirstDifferential k) = 0
      simp
    · change ModuleCat.ofHom (koszulFirstDifferential k) ≫
        ModuleCat.ofHom (koszulSecondDifferential k) = 0
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change MvPolynomial.X (0 : Fin 2) * (MvPolynomial.X (1 : Fin 2) * z) +
          MvPolynomial.X (1 : Fin 2) * (-MvPolynomial.X (0 : Fin 2) * z) = 0
      ring
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rcases z with ⟨a, b⟩
      change Ideal.Quotient.mk (originIdeal k)
          (MvPolynomial.X (0 : Fin 2) * a + MvPolynomial.X (1 : Fin 2) * b) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact koszul_second_mem_origin k a b
    · change ModuleCat.ofHom (koszulAugmentation k) ≫
        (0 : originResidueModule k ⟶
          (0 : ModuleCat (twoVariablePolynomialRing k))) = 0
      simp
  have hexact : (koszulComplex k).Exact := by
    refine ⟨hcomplex, ?_⟩
    intro i hi
    have hi' : i ≤ 3 := by omega
    interval_cases i
    · convert hS₀ using 1 <;> rfl
    · convert hS₁ using 1 <;> rfl
    · convert hS₂ using 1 <;> rfl
    · convert hS₃ using 1 <;> rfl
  refine ⟨hexact, ?_, ?_⟩
  · apply CategoryTheory.ConcreteCategory.mono_of_injective
    exact hfirst
  · apply CategoryTheory.ConcreteCategory.epi_of_surjective
    intro q
    rcases Ideal.Quotient.mk_surjective q with ⟨p, rfl⟩
    exact ⟨p, rfl⟩

/-! ## The Ext computation -/

/-- For `R = k[x,y]` and `k = R/(x,y)`, the Ext groups are `k`, `k²`,
`k`, and zero in degrees `0`, `1`, `2`, and at least `3`, respectively. -/
theorem regular_ring_ext_computation (k : Type u) [Field k] :
    Nonempty (ExtGroup (originResidueModule k) (originResidueModule k) 0 ≃+ k) ∧
      Nonempty (ExtGroup (originResidueModule k) (originResidueModule k) 1 ≃+
        (k × k)) ∧
      Nonempty (ExtGroup (originResidueModule k) (originResidueModule k) 2 ≃+ k) ∧
      ∀ i : ℕ, 3 ≤ i →
        Nonempty (ExtGroup (originResidueModule k) (originResidueModule k) i ≃+
          (Fin 0 → k)) := by
  let R := twoVariablePolynomialRing k
  let M : ModuleCat R := originResidueModule k
  let P₀ : ModuleCat R := ModuleCat.of R R
  let P₁ : ModuleCat R := ModuleCat.of R (R × R)
  let P₂ : ModuleCat R := ModuleCat.of R R
  let f : P₀ ⟶ P₁ := ModuleCat.ofHom (koszulFirstDifferential k)
  let g : P₁ ⟶ P₂ := ModuleCat.ofHom (koszulSecondDifferential k)
  let a : P₂ ⟶ M := ModuleCat.ofHom (koszulAugmentation k)
  letI : Projective P₀ :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R R)
  letI : Projective P₁ :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (R × R))
  letI : Projective P₂ :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R R)
  obtain ⟨eQ, _⟩ := origin_residue_ring_isomorphic_to_field k
  let evalOne : ((M : Type u) →ₗ[R] (M : Type u)) →+ originResidueRing k :=
    { toFun := fun h => h (Ideal.Quotient.mk (originIdeal k) 1)
      map_zero' := by simp
      map_add' := by intro h h'; simp }
  have evalOne_bijective : Function.Bijective evalOne := by
    constructor
    · intro h h' hh
      apply LinearMap.ext
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hone : h (Ideal.Quotient.mk (originIdeal k) 1) =
          h' (Ideal.Quotient.mk (originIdeal k) 1) := hh
      have hmk : Ideal.Quotient.mk (originIdeal k) p =
          p • Ideal.Quotient.mk (originIdeal k) 1 := by
        change Ideal.Quotient.mk (originIdeal k) p =
          Ideal.Quotient.mk (originIdeal k) (p * 1)
        simp
      rw [hmk, map_smul, hone, map_smul]
    · intro z
      let hlin : (M : Type u) →ₗ[R] (M : Type u) :=
        { toFun := fun x => x * z
          map_add' := by intro x y; rw [add_mul]
          map_smul' := by
            intro r x
            obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
            change Ideal.Quotient.mk (originIdeal k) (r * p) * z =
              Ideal.Quotient.mk (originIdeal k) r *
                (Ideal.Quotient.mk (originIdeal k) p * z)
            simp [mul_assoc, mul_comm, mul_left_comm] }
      refine ⟨hlin, ?_⟩
      dsimp [evalOne, hlin]
      simp
  let eHom₀ : (ExtGroup M M 0) ≃+ k :=
    CategoryTheory.Abelian.Ext.addEquiv₀.trans
      (ModuleCat.homAddEquiv.trans
        ((AddEquiv.ofBijective evalOne evalOne_bijective).trans eQ.toAddEquiv))

  let evalPair : ((P₁ : Type u) →ₗ[R] (M : Type u)) →+ (originResidueRing k ×
      originResidueRing k) :=
    { toFun := fun h =>
        (h (1, 0), h (0, 1))
      map_zero' := by simp
      map_add' := by intro h h'; simp }
  have evalPair_bijective : Function.Bijective evalPair := by
    constructor
    · intro h h' hh
      apply LinearMap.ext
      intro x
      have hx : x = x.1 • (1, 0) + x.2 • (0, 1) := by
        apply Prod.ext
        · change x.1 = x.1 * 1 + x.2 * 0
          ring
        · change x.2 = x.1 * 0 + x.2 * 1
          ring
      have hh₁ : h (1, 0) = h' (1, 0) := by
        simpa [evalPair] using congrArg Prod.fst hh
      have hh₂ : h (0, 1) = h' (0, 1) := by
        simpa [evalPair] using congrArg Prod.snd hh
      calc
        h x = h (x.1 • (1, 0) + x.2 • (0, 1)) := congrArg h hx
        _ = x.1 • h (1, 0) + x.2 • h (0, 1) := by
          rw [map_add, map_smul, map_smul]
        _ = x.1 • h' (1, 0) + x.2 • h' (0, 1) := by rw [hh₁, hh₂]
        _ = h' (x.1 • (1, 0) + x.2 • (0, 1)) := by
          rw [map_add, map_smul, map_smul]
        _ = h' x := congrArg h' hx.symm
    · intro z
      let hlin : (P₁ : Type u) →ₗ[R] (M : Type u) :=
        { toFun := fun x => x.1 • z.1 + x.2 • z.2
          map_add' := by
            intro x y
            change (x.1 + y.1) • z.1 + (x.2 + y.2) • z.2 =
              (x.1 • z.1 + x.2 • z.2) + (y.1 • z.1 + y.2 • z.2)
            simp [add_smul, add_assoc, add_left_comm, add_comm]
          map_smul' := by
            intro r x
            change (r * x.1) • z.1 + (r * x.2) • z.2 =
              r • (x.1 • z.1 + x.2 • z.2)
            rw [smul_add, mul_smul, mul_smul] }
      refine ⟨hlin, ?_⟩
      dsimp [evalPair, hlin]
      simp
  let ePair : (originResidueRing k × originResidueRing k) ≃+ (k × k) :=
    { toFun := fun z => (eQ z.1, eQ z.2)
      invFun := fun z => (eQ.symm z.1, eQ.symm z.2)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp
      map_add' := by intro z z'; ext <;> simp }
  let eHom₁ : (P₁ ⟶ M) ≃+ (k × k) :=
    ModuleCat.homAddEquiv.trans
      ((AddEquiv.ofBijective evalPair evalPair_bijective).trans ePair)

  let C : ModuleCat R :=
    ModuleCat.of R (LinearMap.range (koszulSecondDifferential k))
  let q : P₁ ⟶ C :=
    ModuleCat.ofHom
      ((koszulSecondDifferential k).codRestrict
        (LinearMap.range (koszulSecondDifferential k)) (fun z => ⟨z, rfl⟩))
  let c : C ⟶ P₂ :=
    ModuleCat.ofHom (LinearMap.range (koszulSecondDifferential k)).subtype
  have hfg : f ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    dsimp [f, q]
    apply Subtype.ext
    change (koszulSecondDifferential k) (koszulFirstDifferential k z) = 0
    simpa using congrArg (fun h => h z) (koszul_second_comp_first k)
  let S₁ : ShortComplex (ModuleCat R) := ShortComplex.mk f q hfg
  have hq_surj : Function.Surjective q := by
    intro z
    rcases z with ⟨z, ⟨w, rfl⟩⟩
    exact ⟨w, rfl⟩
  have hS₁ : S₁.ShortExact := by
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [S₁.moduleCat_exact_iff]
      intro z hz
      change q z = 0 at hz
      have hz' : koszulSecondDifferential k z = 0 := by
        have hz'' := congrArg Subtype.val hz
        dsimp [q] at hz''
        exact hz''
      rcases (koszul_middle_exact k z).mp hz' with ⟨w, hw⟩
      exact ⟨w, hw⟩
    · exact (ModuleCat.mono_iff_injective _).mpr (koszul_first_injective k)
    · exact (ModuleCat.epi_iff_surjective _).mpr hq_surj
  letI : Epi q := hS₁.epi_g
  have hga : g ≫ a = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rcases z with ⟨u, v⟩
    change Ideal.Quotient.mk (originIdeal k)
        (MvPolynomial.X (0 : Fin 2) * u + MvPolynomial.X (1 : Fin 2) * v) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact koszul_second_mem_origin k u v
  have hqc : q ≫ c = g := by
    apply ModuleCat.hom_ext
    rfl
  have hca : c ≫ a = 0 := by
    apply (cancel_epi q).1
    rw [← Category.assoc, hqc, hga]
    simp
  let S₂ : ShortComplex (ModuleCat R) := ShortComplex.mk c a hca
  have hS₂ : S₂.ShortExact := by
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [S₂.moduleCat_exact_iff]
      intro z hz
      change Ideal.Quotient.mk (originIdeal k) z = 0 at hz
      have hz' : z ∈ originIdeal k := Ideal.Quotient.eq_zero_iff_mem.mp hz
      rcases koszul_range k z hz' with ⟨w, hw⟩
      refine ⟨q w, ?_⟩
      change (q ≫ c) w = z
      rw [hqc]
      exact hw
    · exact (ModuleCat.mono_iff_injective _).mpr
        (LinearMap.range (koszulSecondDifferential k)).injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).mpr (by
        intro z
        rcases Ideal.Quotient.mk_surjective z with ⟨w, rfl⟩
        exact ⟨w, rfl⟩)

  have hzero_scalar : ∀ (v : (M : Type u)) (z : R), z ∈ originIdeal k → z • v = 0 := by
    intro v z hz
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective v
    change Ideal.Quotient.mk (originIdeal k) z *
      Ideal.Quotient.mk (originIdeal k) p = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa [mul_comm] using (originIdeal k).mul_mem_left p hz

  have hzero_ideal : ∀ (w : P₂ ⟶ M) (z : R), z ∈ originIdeal k → w z = 0 := by
    intro w z hz
    rw [show z = z • (1 : R) by simp, map_smul]
    exact hzero_scalar _ z hz

  have hzero_P₀ : ∀ (w : P₀ ⟶ M), c ≫ w = 0 := by
    intro w
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change w (x : R) = 0
    apply hzero_ideal w (x : R)
    rcases x.property with ⟨z, hz⟩
    rcases z with ⟨u, v⟩
    rw [← hz]
    exact koszul_second_mem_origin k u v

  have hzero_P₁ : ∀ (w : P₁ ⟶ M), f ≫ w = 0 := by
    intro w
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change w
      (MvPolynomial.X (1 : Fin 2) * z,
        -MvPolynomial.X (0 : Fin 2) * z) = 0
    rw [show
        (MvPolynomial.X (1 : Fin 2) * z,
          -MvPolynomial.X (0 : Fin 2) * z) =
        (MvPolynomial.X (1 : Fin 2) * z) • (1, 0) +
          (-MvPolynomial.X (0 : Fin 2) * z) • (0, 1) by
      ext <;> simp]
    rw [map_add, map_smul, map_smul]
    have hz₁ : MvPolynomial.X (1 : Fin 2) * z ∈ originIdeal k := by
      simpa [mul_comm] using (originIdeal k).mul_mem_left z (koszul_y_mem k)
    have hz₂ : -MvPolynomial.X (0 : Fin 2) * z ∈ originIdeal k := by
      simpa [mul_comm] using
        (originIdeal k).neg_mem
          ((originIdeal k).mul_mem_left z (koszul_x_mem k))
    rw [hzero_scalar _ _ hz₁, hzero_scalar _ _ hz₂, zero_add]

  have hker_factor : ∀ (w : P₁ ⟶ M),
      LinearMap.range f.hom ≤ LinearMap.ker w.hom := by
    intro w x hx
    rcases hx with ⟨z, rfl⟩
    have hw := congrArg (fun h => h z) (hzero_P₁ w)
    change w (f.hom z) = 0
    simpa using hw

  let qEquiv :
      ((P₁ : Type u) ⧸ LinearMap.range f.hom) ≃ₗ[R] (C : Type u) :=
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₁).mp
      (hS₁.exact) |>.linearEquivOfSurjective hq_surj

  let precompQ : (C ⟶ M) →+ (P₁ ⟶ M) :=
    { toFun := fun h => q ≫ h
      map_zero' := by simp
      map_add' := by intro h h'; simp }
  have precompQ_bijective : Function.Bijective precompQ := by
    constructor
    · intro h h' hh
      apply (cancel_epi q).1
      simpa [precompQ] using hh
    · intro w
      let liftW : C ⟶ M :=
        ModuleCat.ofHom
          (((LinearMap.range f.hom).liftQ w.hom (hker_factor w)).comp
            qEquiv.symm.toLinearMap)
      refine ⟨liftW, ?_⟩
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change ((LinearMap.range f.hom).liftQ w.hom (hker_factor w))
          (qEquiv.symm (q.hom z)) = w.hom z
      rw [Function.Exact.linearEquivOfSurjective_symm_apply
        ((CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₁).mp
          hS₁.exact) hq_surj z]
      simp

  let eHomC : (C ⟶ M) ≃+ (P₁ ⟶ M) :=
    AddEquiv.ofBijective precompQ precompQ_bijective

  let evalP₀ : ((P₀ : Type u) →ₗ[R] (M : Type u)) →+
      originResidueRing k :=
    { toFun := fun h => h 1
      map_zero' := by simp
      map_add' := by intro h h'; simp }
  have evalP₀_bijective : Function.Bijective evalP₀ := by
    constructor
    · intro h h' hh
      apply LinearMap.ext
      intro x
      rw [show x = x • (1 : R) by simp, map_smul, map_smul]
      change x • h 1 = x • h' 1
      rw [show h 1 = h' 1 by exact hh]
    · intro z
      let hlin : (P₀ : Type u) →ₗ[R] (M : Type u) :=
        { toFun := fun x => x • z
          map_add' := by intro x y; simp [add_smul]
          map_smul' := by
            intro r x
            change (r * x) • z = r • (x • z)
            rw [mul_smul] }
      refine ⟨hlin, ?_⟩
      dsimp [evalP₀, hlin]
      simp

  let eP₀ : (P₀ ⟶ M) ≃+ k :=
    ModuleCat.homAddEquiv.trans
      ((AddEquiv.ofBijective evalP₀ evalP₀_bijective).trans eQ.toAddEquiv)

  let δ₀ : (P₀ ⟶ M) →+ ExtGroup C M 1 :=
    AddMonoidHom.mk'
      (fun w => hS₁.extClass.comp
        (CategoryTheory.Abelian.Ext.mk₀ w) (by simp))
      (by
        intro w w'
        simp [CategoryTheory.Abelian.Ext.mk₀_add])
  have δ₀_bijective : Function.Bijective δ₀ := by
    constructor
    · intro w w' hww'
      have hdiff : δ₀ (w - w') = 0 := by
        rw [map_sub, hww', sub_self]
      have hdiff' : hS₁.extClass.comp
          (CategoryTheory.Abelian.Ext.mk₀ (w - w')) (add_zero 1) = 0 := by
        simpa [δ₀] using hdiff
      obtain ⟨v, hv⟩ :=
        CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁ hS₁ M
          (CategoryTheory.Abelian.Ext.mk₀ (w - w')) (n₁ := 1) (by simp) hdiff'
      have hvzero :
          (CategoryTheory.Abelian.Ext.mk₀ S₁.f).comp v (zero_add 0) = 0 := by
        rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply v,
          CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
          CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff]
        exact hzero_P₁ (CategoryTheory.Abelian.Ext.addEquiv₀ v)
      have hdiffzero : CategoryTheory.Abelian.Ext.mk₀ (w - w') = 0 := by
        rw [← hv, hvzero]
      exact sub_eq_zero.mp
        ((CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff _).mp hdiffzero)
    · intro x
      have hxzero :
          (CategoryTheory.Abelian.Ext.mk₀ S₁.g).comp x (zero_add 1) = 0 := by
        exact CategoryTheory.Abelian.Ext.eq_zero_of_projective
          (P := P₁) (Y := M) (n := 0)
          ((CategoryTheory.Abelian.Ext.mk₀ S₁.g).comp x (zero_add 1))
      obtain ⟨w, hw⟩ :=
        CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS₁ M x hxzero
          (n₀ := 0)
          (by simp)
      refine ⟨CategoryTheory.Abelian.Ext.addEquiv₀ w, ?_⟩
      simpa [δ₀] using hw
  let eC₁ : (ExtGroup C M 1) ≃+ k :=
    (AddEquiv.ofBijective δ₀ δ₀_bijective).symm.trans eP₀

  let δ₁ : (C ⟶ M) →+ ExtGroup M M 1 :=
    AddMonoidHom.mk'
      (fun w => hS₂.extClass.comp
        (CategoryTheory.Abelian.Ext.mk₀ w) (by simp))
      (by
        intro w w'
        simp [CategoryTheory.Abelian.Ext.mk₀_add])
  have δ₁_bijective : Function.Bijective δ₁ := by
    constructor
    · intro w w' hww'
      have hdiff : δ₁ (w - w') = 0 := by
        rw [map_sub, hww', sub_self]
      have hdiff' : hS₂.extClass.comp
          (CategoryTheory.Abelian.Ext.mk₀ (w - w')) (add_zero 1) = 0 := by
        simpa [δ₁] using hdiff
      obtain ⟨v, hv⟩ :=
        CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁ hS₂ M
          (CategoryTheory.Abelian.Ext.mk₀ (w - w')) (n₁ := 1) (by simp) hdiff'
      have hvzero :
          (CategoryTheory.Abelian.Ext.mk₀ S₂.f).comp v (zero_add 0) = 0 := by
        rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply v,
          CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
          CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff]
        exact hzero_P₀ (CategoryTheory.Abelian.Ext.addEquiv₀ v)
      have hdiffzero : CategoryTheory.Abelian.Ext.mk₀ (w - w') = 0 := by
        rw [← hv, hvzero]
      exact sub_eq_zero.mp
        ((CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff _).mp hdiffzero)
    · intro x
      have hxzero :
          (CategoryTheory.Abelian.Ext.mk₀ S₂.g).comp x (zero_add 1) = 0 := by
        exact CategoryTheory.Abelian.Ext.eq_zero_of_projective
          (P := P₂) (Y := M) (n := 0)
          ((CategoryTheory.Abelian.Ext.mk₀ S₂.g).comp x (zero_add 1))
      obtain ⟨w, hw⟩ :=
        CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS₂ M x hxzero
          (n₀ := 0)
          (by simp)
      refine ⟨CategoryTheory.Abelian.Ext.addEquiv₀ w, ?_⟩
      simpa [δ₁] using hw
  let eM₁ : (ExtGroup M M 1) ≃+ (k × k) :=
    (AddEquiv.ofBijective δ₁ δ₁_bijective).symm.trans (eHomC.trans eHom₁)

  let δ₂ : (ExtGroup C M 1) →+ ExtGroup M M 2 :=
    AddMonoidHom.mk'
      (fun x => hS₂.extClass.comp x (by simp))
      (by
        intro x y
        simp)
  have δ₂_bijective : Function.Bijective δ₂ := by
    constructor
    · intro x y hxy
      have hdiff : δ₂ (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      obtain ⟨z, hz⟩ :=
        CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁ hS₂ M
          (x - y) (n₁ := 2) (by simp) hdiff
      have hzzero : z = 0 :=
        CategoryTheory.Abelian.Ext.eq_zero_of_projective
          (P := P₂) (Y := M) (n := 0) z
      have hdiffzero : x - y = 0 := by
        rw [← hz, hzzero]
        simp
      exact sub_eq_zero.mp hdiffzero
    · intro x
      have hxzero :
          (CategoryTheory.Abelian.Ext.mk₀ S₂.g).comp x (zero_add 2) = 0 := by
        exact CategoryTheory.Abelian.Ext.eq_zero_of_projective
          (P := P₂) (Y := M) (n := 1)
          ((CategoryTheory.Abelian.Ext.mk₀ S₂.g).comp x (zero_add 2))
      obtain ⟨y, hy⟩ :=
        CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS₂ M x hxzero
          (n₀ := 1)
          (by simp)
      exact ⟨y, by simpa [δ₂] using hy⟩
  let eM₂ : (ExtGroup M M 2) ≃+ k :=
    (AddEquiv.ofBijective δ₂ δ₂_bijective).symm.trans eC₁

  have hC_vanishes : ∀ n : ℕ, 2 ≤ n →
      Subsingleton (ExtGroup C M n) := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hm : 0 < m := by omega
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    refine ⟨?_⟩
    intro x y
    have hzero : ∀ z : ExtGroup C M (l + 1 + 1), z = 0 := by
      intro z
      have hz :
          (CategoryTheory.Abelian.Ext.mk₀ S₁.g).comp z
              (zero_add (l + 1 + 1)) = 0 := by
        exact CategoryTheory.Abelian.Ext.eq_zero_of_projective
          (P := P₁) (Y := M) (n := l + 1)
          ((CategoryTheory.Abelian.Ext.mk₀ S₁.g).comp z
            (zero_add (l + 1 + 1)))
      obtain ⟨w, hw⟩ :=
        CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS₁ M z hz
          (n₀ := l + 1) (by omega)
      have hwzero : w = 0 :=
        CategoryTheory.Abelian.Ext.eq_zero_of_projective
          (P := P₀) (Y := M) (n := l) w
      rw [← hw, hwzero]
      simp
    exact (hzero x).trans (hzero y).symm

  have hM_vanishes : ∀ i : ℕ, 3 ≤ i →
      Subsingleton (ExtGroup M M i) := by
    intro i hi
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have hm : 2 ≤ m := by omega
    refine ⟨?_⟩
    intro x y
    have hzero : ∀ z : ExtGroup M M (m + 1), z = 0 := by
      intro z
      have hz :
          (CategoryTheory.Abelian.Ext.mk₀ S₂.g).comp z
              (zero_add (m + 1)) = 0 := by
        exact CategoryTheory.Abelian.Ext.eq_zero_of_projective
          (P := P₂) (Y := M) (n := m)
          ((CategoryTheory.Abelian.Ext.mk₀ S₂.g).comp z
            (zero_add (m + 1)))
      obtain ⟨w, hw⟩ :=
        CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS₂ M z hz
          (n₀ := m) (by omega)
      have hwzero : w = 0 := (hC_vanishes m hm).elim w 0
      rw [← hw, hwzero]
      simp
    exact (hzero x).trans (hzero y).symm

  change Nonempty (ExtGroup M M 0 ≃+ k) ∧
      Nonempty (ExtGroup M M 1 ≃+ (k × k)) ∧
      Nonempty (ExtGroup M M 2 ≃+ k) ∧
      ∀ i : ℕ, 3 ≤ i → Nonempty (ExtGroup M M i ≃+ (Fin 0 → k))
  refine ⟨⟨eHom₀⟩, ⟨eM₁⟩, ⟨eM₂⟩, ?_⟩
  intro i hi
  let huniq : Unique (ExtGroup M M i) :=
    { default := 0
      uniq := fun x => (hM_vanishes i hi).elim x 0 }
  exact ⟨@AddEquiv.ofUnique _ _ huniq inferInstance inferInstance inferInstance⟩

end

end Formalization.Books.Exercises.Unit11
