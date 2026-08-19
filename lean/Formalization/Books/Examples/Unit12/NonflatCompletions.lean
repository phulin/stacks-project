import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Examples, Chapter 12: Nonflat completions

This file records the definitions and theorem interfaces in the source
section.  The mathematical proofs belong to the proof stage.
-/

noncomputable section

open scoped TensorProduct
open scoped BigOperators

namespace Formalization.Books.Examples.Unit12

universe u v

/-! ## The tensor-product criterion -/

/-
The source's canonical map is Mathlib's `TensorProduct.piScalarRightHom` with
the coefficient ring used as both scalar rings.  Its codomain is the product
`ℕ → M`, and on a pure tensor it sends `m ⊗ a` to `n ↦ a n • m`.
-/

@[simp]
theorem countableTensorToPi_tmul (R : Type u) (M : Type v)
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    (m : M) (a : ℕ → R) :
    TensorProduct.piScalarRightHom R R M ℕ (m ⊗ₜ[R] a) = fun n => a n • m := by
  exact TensorProduct.piScalarRightHom_tmul R R M ℕ m a

theorem countable_finite_iff_tensor_surjective
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Countable M] :
      Module.Finite R M ↔
      Function.Surjective (TensorProduct.piScalarRightHom R R M ℕ) := by
  constructor
  · intro h
    obtain ⟨n, s, hs⟩ := @Module.Finite.exists_fin R M _ _ _ h
    let l : (Fin n → R) →ₗ[R] M := Fintype.linearCombination R s
    have hl : Function.Surjective l := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
      exact hs
    intro f
    choose c hc using fun i : ℕ => hl (f i)
    refine ⟨∑ j : Fin n, s j ⊗ₜ[R] fun i => c i j, ?_⟩
    ext i
    simp only [map_sum, countableTensorToPi_tmul, Finset.sum_apply]
    rw [← hc i]
    simp [l, Fintype.linearCombination_apply]
  · intro h
    obtain ⟨e, he⟩ := exists_surjective_nat M
    obtain ⟨x, hx⟩ := h e
    obtain ⟨M', hM', hMx⟩ :=
      TensorProduct.exists_finite_submodule_left_of_setFinite ({x} : Set _) (by simp)
    obtain ⟨y, hy⟩ :=
      hMx (show x ∈ ({x} : Set (M ⊗[R] (ℕ → R))) by simp)
    have hcoord (y : M' ⊗[R] (ℕ → R)) (n : ℕ) :
        (TensorProduct.piScalarRightHom R R M ℕ
          (M'.subtype.rTensor (ℕ → R) y)) n ∈ M' := by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul y f =>
          simpa using M'.smul_mem (f n) y.property
      | add y z ihy ihz =>
          simpa [map_add] using M'.add_mem ihy ihz
    have htop : (⊤ : Submodule R M) ≤ M' := by
      intro m hm
      obtain ⟨n, rfl⟩ := he m
      rw [← hx, ← hy]
      exact hcoord y n
    apply Module.Finite.of_fg_top
    rw [← top_unique htop]
    exact (Submodule.fg_top M').mp hM'.fg_top

private lemma finite_piScalarRightHom_injective
    (R : Type u) (n : ℕ) [CommRing R] :
    Function.Injective (TensorProduct.piScalarRightHom R R (Fin n → R) ℕ) := by
  classical
  let inv : (ℕ → (Fin n → R)) → (Fin n → R) ⊗[R] (ℕ → R) :=
    fun f => ∑ i : Fin n, Pi.single i 1 ⊗ₜ[R] fun j => f j i
  have hinv : Function.LeftInverse inv
      (TensorProduct.piScalarRightHom R R (Fin n → R) ℕ) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
        have hzero :
            TensorProduct.piScalarRightHom R R (Fin n → R) ℕ (0) =
              (0 : ℕ → Fin n → R) := map_zero _
        simp only [hzero]
        change (∑ i : Fin n, Pi.single i 1 ⊗ₜ[R]
          (0 : ℕ → R)) = 0
        apply Finset.sum_eq_zero
        intro i hi
        exact TensorProduct.tmul_zero _ _
    | tmul x y =>
        change (∑ i : Fin n, Pi.single i 1 ⊗ₜ[R] fun j => y j • x i) = x ⊗ₜ[R] y
        have hsmul (i : Fin n) : (fun j => y j • x i) = x i • y := by
          funext j
          simpa only [Pi.smul_apply, smul_eq_mul] using mul_comm (y j) (x i)
        calc
          _ = ∑ i : Fin n, Pi.single i 1 ⊗ₜ[R] (x i • y) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hsmul i]
          _ = ∑ i : Fin n, (x i • Pi.single i 1) ⊗ₜ[R] y := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
          _ = (∑ i : Fin n, x i • Pi.single i 1) ⊗ₜ[R] y := by
            rw [TensorProduct.sum_tmul]
          _ = x ⊗ₜ[R] y := by
            apply congrArg (fun q : Fin n → R => q ⊗ₜ[R] y)
            funext i
            change (∑ j : Fin n, x j • Pi.single j 1) i = x i
            simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
              mul_ite, mul_one, mul_zero]
            rw [Finset.sum_eq_single i]
            · simp
            · intro j hj hji
              simp [Ne.symm hji]
            · simp
    | add x y hx hy =>
        have hmap :
            TensorProduct.piScalarRightHom R R (Fin n → R) ℕ (x + y) =
              TensorProduct.piScalarRightHom R R (Fin n → R) ℕ x +
                TensorProduct.piScalarRightHom R R (Fin n → R) ℕ y :=
          map_add _ x y
        rw [hmap]
        simp only [inv]
        let p := TensorProduct.piScalarRightHom R R (Fin n → R) ℕ x
        let q := TensorProduct.piScalarRightHom R R (Fin n → R) ℕ y
        change (∑ i : Fin n, (Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R]
          (fun j : ℕ => p j i + q j i)) = x + y
        have hfun (i : Fin n) :
            (fun j => p j i + q j i) = (fun j => p j i) + (fun j => q j i) := by
          funext j
          simp
        have hadd :
            (∑ i : Fin n, (Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R]
                (fun j : ℕ => p j i + q j i)) =
              (∑ i : Fin n, ((Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R]
                (fun j : ℕ => p j i))) +
                (∑ i : Fin n, ((Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R]
                (fun j : ℕ => q j i))) := by
          calc
            _ = (∑ i : Fin n, (
                ((Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R]
                  (fun j : ℕ => p j i)) +
                  ((Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R]
                    (fun j : ℕ => q j i)))) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hfun i, TensorProduct.tmul_add]
            _ = _ := by rw [Finset.sum_add_distrib]
        rw [hadd]
        simpa [p, q, inv] using congrArg₂ (· + ·) hx hy
  exact hinv.injective

private lemma piScalarRightHom_rTensor_naturality
    (R : Type u) (M : Type v) (P : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup P] [Module R P] (f : M →ₗ[R] P)
    (x : M ⊗[R] (ℕ → R)) (n : ℕ) :
    (TensorProduct.piScalarRightHom R R P ℕ (f.rTensor (ℕ → R) x)) n =
      f (TensorProduct.piScalarRightHom R R M ℕ x n) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

private lemma piScalarRightHom_R_eq_lid
    (R : Type u) [CommRing R] (x : R ⊗[R] (ℕ → R)) :
    TensorProduct.piScalarRightHom R R R ℕ x = TensorProduct.lid R (ℕ → R) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
      funext n
      simp [TensorProduct.piScalarRightHom_tmul, TensorProduct.lid_tmul,
        smul_eq_mul, mul_comm]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]

private lemma piScalarRightHom_R_injective
    (R : Type u) [CommRing R] :
    Function.Injective (TensorProduct.piScalarRightHom R R R ℕ) := by
  intro x y hxy
  apply (TensorProduct.lid R (ℕ → R)).injective
  rw [← piScalarRightHom_R_eq_lid R x, ← piScalarRightHom_R_eq_lid R y]
  exact hxy

theorem countable_finitePresentation_iff_tensor_bijective
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Countable R] [Countable M] :
    Module.FinitePresentation R M ↔
    Function.Bijective (TensorProduct.piScalarRightHom R R M ℕ) := by
  constructor
  · intro h
    have hfin : Module.Finite R M := by
      obtain ⟨s, hs, _⟩ := h.out
      exact ⟨s, hs⟩
    have hsurj : Function.Surjective (TensorProduct.piScalarRightHom R R M ℕ) :=
      (countable_finite_iff_tensor_surjective R M).mp hfin
    refine ⟨?_, hsurj⟩
    intro x y hxy
    obtain ⟨n, m, f, g, hf, hgf⟩ :=
      @Module.FinitePresentation.exists_fin' R M _ _ _ h
    let K := LinearMap.ker f
    have hKfin : Module.Finite R K := by
      apply Module.Finite.of_fg
      change (LinearMap.ker f).FG
      rw [LinearMap.exact_iff.mp hgf]
      exact Submodule.fg_range g
    have hKsurj :
        Function.Surjective (TensorProduct.piScalarRightHom R R K ℕ) :=
      (countable_finite_iff_tensor_surjective R K).mp hKfin
    have hz : TensorProduct.piScalarRightHom R R M ℕ (x - y) = 0 := by
      simpa [map_sub] using sub_eq_zero.mpr hxy
    obtain ⟨w, hw⟩ := LinearMap.rTensor_surjective (ℕ → R) hf (x - y)
    have hmem (i : ℕ) :
        TensorProduct.piScalarRightHom R R (Fin n → R) ℕ w i ∈ K := by
      change f (TensorProduct.piScalarRightHom R R (Fin n → R) ℕ w i) = 0
      rw [← piScalarRightHom_rTensor_naturality R (Fin n → R) M f w i]
      rw [hw]
      exact congrFun hz i
    let a : ℕ → K := fun i ↦
      ⟨TensorProduct.piScalarRightHom R R (Fin n → R) ℕ w i, hmem i⟩
    obtain ⟨z, hz⟩ := hKsurj a
    have hwz : w = K.subtype.rTensor (ℕ → R) z := by
      apply finite_piScalarRightHom_injective R n
      funext i
      rw [piScalarRightHom_rTensor_naturality R K (Fin n → R) K.subtype z i, hz]
      rfl
    apply sub_eq_zero.mp
    rw [← hw, hwz]
    rw [← LinearMap.rTensor_comp_apply]
    have : f.comp K.subtype = 0 := by
      ext z
      exact z.property
    rw [this]
    simp
  · intro h
    have hfin : Module.Finite R M :=
      (countable_finite_iff_tensor_surjective R M).mpr h.2
    obtain ⟨n, s, hs⟩ := @Module.Finite.exists_fin R M _ _ _ hfin
    let l : (Fin n → R) →ₗ[R] M := Fintype.linearCombination R s
    have hl : Function.Surjective l := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
      exact hs
    have hKsurj : Function.Surjective (TensorProduct.piScalarRightHom R R
        (LinearMap.ker l) ℕ) := by
      have hFsurj : Function.Surjective
          (TensorProduct.piScalarRightHom R R (Fin n → R) ℕ) :=
        (countable_finite_iff_tensor_surjective R (Fin n → R)).mp inferInstance
      intro a
      let b : ℕ → (Fin n → R) := fun i ↦ a i
      obtain ⟨w, hw⟩ := hFsurj b
      have hwzero : l.rTensor (ℕ → R) w = 0 := by
        apply h.1
        funext i
        rw [piScalarRightHom_rTensor_naturality R (Fin n → R) M l w i, hw]
        rw [map_zero]
        change l (a i) = 0
        exact (a i).property
      have hker : LinearMap.ker (l.rTensor (ℕ → R)) =
          LinearMap.range ((LinearMap.ker l).subtype.rTensor (ℕ → R)) :=
        (rTensor_exact (ℕ → R) (LinearMap.exact_subtype_ker_map l) hl).linearMap_ker_eq
      have hwker : w ∈ LinearMap.ker (l.rTensor (ℕ → R)) := hwzero
      rw [hker] at hwker
      obtain ⟨z, hz⟩ := hwker
      refine ⟨z, ?_⟩
      funext i
      apply Subtype.ext
      change (LinearMap.ker l).subtype
          (TensorProduct.piScalarRightHom R R (LinearMap.ker l) ℕ z i) =
        (a i : Fin n → R)
      rw [← piScalarRightHom_rTensor_naturality R (LinearMap.ker l)
        (Fin n → R) (LinearMap.ker l).subtype z i]
      have hzw := congrArg
        (TensorProduct.piScalarRightHom R R (Fin n → R) ℕ) hz
      calc
        (TensorProduct.piScalarRightHom R R (Fin n → R) ℕ
            ((LinearMap.ker l).subtype.rTensor (ℕ → R) z)) i =
            (TensorProduct.piScalarRightHom R R (Fin n → R) ℕ w) i :=
          congrFun hzw i
        _ = b i := congrFun hw i
        _ = (a i : Fin n → R) := rfl
    have hK : (LinearMap.ker l).FG :=
      Module.Finite.iff_fg.mp
        ((countable_finite_iff_tensor_surjective R (LinearMap.ker l)).mpr hKsurj)
    exact Module.finitePresentation_of_free_of_surjective l hl hK

/-! ## Coherence and power series -/

/-
Mathlib has the module-level notion of finite presentation but no separate
`Coherent` ring predicate.  The following is the standard commutative-ring
definition used by the source: every finitely generated ideal is finitely
presented as a module.
-/
def IsCoherent (R : Type u) [CommRing R] : Prop :=
  ∀ I : Ideal R, I.FG → Module.FinitePresentation R I

theorem coherent_iff_pi_flat (R : Type u) [CommRing R] [Countable R] :
    IsCoherent R ↔ Module.Flat R (ℕ → R) := by
  constructor
  · intro h
    rw [Module.Flat.iff_rTensor_injective]
    intro I hI
    have hbij :=
      (countable_finitePresentation_iff_tensor_bijective R I).mp (h I hI)
    intro x y hxy
    apply hbij.1
    funext n
    apply Subtype.ext
    have hpi :=
      congrArg (TensorProduct.piScalarRightHom R R R ℕ) hxy
    change I.subtype ((TensorProduct.piScalarRightHom R R I ℕ) x n) =
      I.subtype ((TensorProduct.piScalarRightHom R R I ℕ) y n)
    rw [← piScalarRightHom_rTensor_naturality R I R I.subtype x n,
      ← piScalarRightHom_rTensor_naturality R I R I.subtype y n]
    exact congrFun hpi n
  · intro h I hI
    have hfin : Module.Finite R I := Module.Finite.iff_fg.mpr hI
    have hsurj :
        Function.Surjective (TensorProduct.piScalarRightHom R R I ℕ) :=
      (countable_finite_iff_tensor_surjective R I).mp hfin
    have hinj :
        Function.Injective (TensorProduct.piScalarRightHom R R I ℕ) := by
      have ht : Function.Injective (I.subtype.rTensor (ℕ → R)) :=
        (Module.Flat.iff_rTensor_injective.mp h) hI
      intro x y hxy
      apply ht
      apply piScalarRightHom_R_injective R
      funext n
      rw [piScalarRightHom_rTensor_naturality R I R I.subtype x n,
        piScalarRightHom_rTensor_naturality R I R I.subtype y n]
      exact congrArg (fun z : I => (z : R)) (congrFun hxy n)
    exact (countable_finitePresentation_iff_tensor_bijective R I).mpr
      ⟨hinj, hsurj⟩

/-
The coefficient map is the module isomorphism used in the observation that
`R[[x]]` is `R^ℕ` as an `R`-module.
-/
def powerSeriesCoeffEquiv (R : Type u) [Semiring R] :
    PowerSeries R ≃ₗ[R] (ℕ → R) where
  toFun p n := PowerSeries.coeff n p
  invFun := PowerSeries.mk
  left_inv p := by
    apply PowerSeries.ext
    intro n
    simp
  right_inv f := by
    funext n
    simp
  map_add' p q := by
    funext n
    simp
  map_smul' r p := by
    funext n
    simp

theorem powerSeriesCoeffEquiv_apply (R : Type u) [Semiring R]
    (p : PowerSeries R) (n : ℕ) :
    powerSeriesCoeffEquiv R p n = PowerSeries.coeff n p :=
  rfl

theorem powerSeries_flat_iff_isCoherent
    (R : Type u) [CommRing R] [Countable R] :
    Module.Flat R (PowerSeries R) ↔ IsCoherent R := by
  exact (Module.Flat.equiv_iff (powerSeriesCoeffEquiv R)).trans
    (coherent_iff_pi_flat R).symm

theorem powerSeries_algebraMap_flat_iff_isCoherent
    (R : Type u) [CommRing R] [Countable R] :
    RingHom.Flat (algebraMap R (PowerSeries R)) ↔ IsCoherent R := by
  rw [RingHom.flat_algebraMap_iff]
  exact powerSeries_flat_iff_isCoherent R

/-! ## The explicitly displayed noncoherent ring -/

abbrev NoncoherentExampleVariables := Fin 2 ⊕ (ℕ × Bool)

def noncoherentExampleYVar : NoncoherentExampleVariables := Sum.inl 0

def noncoherentExampleZVar : NoncoherentExampleVariables := Sum.inl 1

def noncoherentExampleAVar (n : ℕ) : NoncoherentExampleVariables :=
  Sum.inr (n, false)

def noncoherentExampleBVar (n : ℕ) : NoncoherentExampleVariables :=
  Sum.inr (n, true)

def noncoherentExampleRelation (k : Type u) [CommSemiring k] (n : ℕ) :
    MvPolynomial NoncoherentExampleVariables k :=
  MvPolynomial.X (noncoherentExampleAVar n) * MvPolynomial.X noncoherentExampleYVar +
    MvPolynomial.X (noncoherentExampleBVar n) * MvPolynomial.X noncoherentExampleZVar

def noncoherentExampleRelationsIdeal (k : Type u) [CommSemiring k] :
    Ideal (MvPolynomial NoncoherentExampleVariables k) :=
  Ideal.span (Set.range (noncoherentExampleRelation k))

abbrev noncoherentExampleRing (k : Type u) [CommRing k] :=
  MvPolynomial NoncoherentExampleVariables k ⧸ noncoherentExampleRelationsIdeal k

def noncoherentExampleY (k : Type u) [CommRing k] : noncoherentExampleRing k :=
  Ideal.Quotient.mk (noncoherentExampleRelationsIdeal k)
    (MvPolynomial.X noncoherentExampleYVar)

def noncoherentExampleZ (k : Type u) [CommRing k] : noncoherentExampleRing k :=
  Ideal.Quotient.mk (noncoherentExampleRelationsIdeal k)
    (MvPolynomial.X noncoherentExampleZVar)

def noncoherentExampleIdeal (k : Type u) [CommRing k] :
    Ideal (noncoherentExampleRing k) :=
  Ideal.span {noncoherentExampleY k, noncoherentExampleZ k}

private def noncoherentExampleEval (k : Type u) [CommRing k] :
    MvPolynomial NoncoherentExampleVariables k →+*
      MvPolynomial (ℕ × Bool) k :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (ℕ × Bool) k) (fun i =>
    match i with
    | Sum.inl _ => 0
    | Sum.inr j => MvPolynomial.X j)

private def noncoherentExampleRelVec (k : Type u) [CommRing k] (n : ℕ) :
    Fin 2 → MvPolynomial (ℕ × Bool) k :=
  ![MvPolynomial.X (n, false), MvPolynomial.X (n, true)]

private def noncoherentExamplePDerivEval (k : Type u) [CommRing k]
    (p : MvPolynomial NoncoherentExampleVariables k) :
    Fin 2 → MvPolynomial (ℕ × Bool) k :=
  fun i => noncoherentExampleEval k (MvPolynomial.pderiv (Sum.inl i) p)

private def noncoherentExampleQuotientEval (k : Type u) [CommRing k] :
    noncoherentExampleRing k →+* MvPolynomial (ℕ × Bool) k :=
  Ideal.Quotient.lift (noncoherentExampleRelationsIdeal k)
    (noncoherentExampleEval k) (by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem p hp =>
          obtain ⟨n, rfl⟩ := hp
          simp [noncoherentExampleEval, noncoherentExampleRelation,
            noncoherentExampleAVar, noncoherentExampleBVar,
            noncoherentExampleYVar, noncoherentExampleZVar]
      | zero => simp
      | add p q _ _ hp hq => simpa [map_add] using congrArg₂ (· + ·) hp hq
      | smul p q _ hq => simpa [map_mul] using congrArg (fun x =>
          (noncoherentExampleEval k p) * x) hq)

private lemma noncoherentExample_relationSpan_not_fg
    (k : Type u) [Field k] :
    ¬ (Submodule.span (MvPolynomial (ℕ × Bool) k)
      (Set.range (noncoherentExampleRelVec k))).FG := by
  classical
  intro hfg
  obtain ⟨s, hs⟩ := hfg
  let t : Finset ℕ := s.biUnion (fun v =>
    (Finset.univ : Finset (Fin 2)).biUnion (fun i =>
      (v i).vars.image Prod.fst))
  let n := t.sum id + 1
  have hn : n ∉ t := by
    intro hnt
    have hle : n ≤ t.sum id := by
      simpa using (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hnt :
        id n ≤ ∑ x ∈ t, id x)
    have : t.sum id + 1 ≤ t.sum id := by simpa [n] using hle
    exact (Nat.not_succ_le_self (t.sum id)) this
  let ev : MvPolynomial (ℕ × Bool) k →+* MvPolynomial (Fin 2) k :=
    MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k)
      (fun w => if w.1 = n then MvPolynomial.X (if w.2 then 1 else 0) else 0)
  have hcc : ∀ v ∈ Submodule.span (MvPolynomial (ℕ × Bool) k)
      (Set.range (noncoherentExampleRelVec k)), ∀ i,
      MvPolynomial.constantCoeff (v i) = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨m, rfl⟩ := hv
        intro i
        fin_cases i <;> simp [noncoherentExampleRelVec]
    | zero => intro i; simp
    | add v w hv hw ihv ihw =>
        intro i
        simpa using congrArg₂ (· + ·) (ihv i) (ihw i)
    | smul a v hv ih =>
        intro i
        simpa [smul_eq_mul] using congrArg (fun x =>
          MvPolynomial.constantCoeff a * x) (ih i)
  have hspan : ∀ v ∈ Submodule.span (MvPolynomial (ℕ × Bool) k)
      (s : Set (Fin 2 → MvPolynomial (ℕ × Bool) k)), ∀ i,
      ev (v i) = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        intro i
        have hvi : v ∈ Submodule.span (MvPolynomial (ℕ × Bool) k)
            (Set.range (noncoherentExampleRelVec k)) := by
          rw [← hs]
          exact Submodule.subset_span hv
        have hvars : ∀ w ∈ (v i).vars, w.1 ≠ n := by
          intro w hw hwn
          apply hn
          apply Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
          apply Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
          exact Finset.mem_image.mpr ⟨w, hw, hwn⟩
        rw [show ev (v i) = MvPolynomial.eval₂Hom
          (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k)
          (fun w => if w.1 = n then MvPolynomial.X (if w.2 then 1 else 0) else 0) (v i) by rfl]
        rw [MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars]
        · simpa [hcc v hvi i]
        · intro w hw
          simp [hvars w hw]
    | zero => intro i; simp [ev]
    | add v w hv hw ihv ihw =>
        intro i
        simpa [ev] using congrArg₂ (· + ·) (ihv i) (ihw i)
    | smul a v hv ih =>
        intro i
        simpa [ev, smul_eq_mul] using congrArg (fun x => ev a * x) (ih i)
  have htarget : noncoherentExampleRelVec k n ∈
      Submodule.span (MvPolynomial (ℕ × Bool) k)
        (Set.range (noncoherentExampleRelVec k)) := Submodule.subset_span
    (show noncoherentExampleRelVec k n ∈ Set.range
      (noncoherentExampleRelVec k) from ⟨n, rfl⟩)
  rw [← hs] at htarget
  have hz := hspan _ htarget 0
  have hnz : ev (noncoherentExampleRelVec k n 0) ≠ 0 := by
    simp [ev, noncoherentExampleRelVec]
  exact hnz hz

private lemma noncoherentExample_pderiv_eval_relations
    (k : Type u) [Field k] :
    ∀ p ∈ noncoherentExampleRelationsIdeal k,
      noncoherentExamplePDerivEval k p ∈
          Submodule.span (MvPolynomial (ℕ × Bool) k)
            (Set.range (noncoherentExampleRelVec k)) ∧
        noncoherentExampleEval k p = 0 := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨n, rfl⟩ := hp
      constructor
      · apply Submodule.subset_span
        exact ⟨n, by
          funext i
          fin_cases i <;>
            simp [noncoherentExamplePDerivEval, noncoherentExampleRelation,
              noncoherentExampleEval, noncoherentExampleRelVec,
              noncoherentExampleAVar, noncoherentExampleBVar,
              noncoherentExampleYVar, noncoherentExampleZVar]⟩
      · simp [noncoherentExampleEval, noncoherentExampleRelation,
          noncoherentExampleAVar, noncoherentExampleBVar,
          noncoherentExampleYVar, noncoherentExampleZVar]
  | zero =>
      constructor
      · have hz : noncoherentExamplePDerivEval k (0 :
            MvPolynomial NoncoherentExampleVariables k) = 0 := by
          funext i
          simp [noncoherentExamplePDerivEval]
        rw [hz]
        exact Submodule.zero_mem _
      · simp [noncoherentExampleEval]
  | add p q _ _ hp hq =>
      have hadd : noncoherentExamplePDerivEval k (p + q) =
          noncoherentExamplePDerivEval k p + noncoherentExamplePDerivEval k q := by
        funext i
        simp [noncoherentExamplePDerivEval]
      exact ⟨by rw [hadd]; exact add_mem hp.1 hq.1,
        by simpa using congrArg₂ (· + ·) hp.2 hq.2⟩
  | smul p q _ hq =>
      have hprod : noncoherentExamplePDerivEval k (p * q) =
          (noncoherentExampleEval k p) • noncoherentExamplePDerivEval k q := by
        funext i
        simp only [noncoherentExamplePDerivEval, MvPolynomial.pderiv_mul,
          map_add, map_mul, Pi.smul_apply, smul_eq_mul]
        rw [hq.2]
        simp
      refine ⟨?_, by simpa [map_mul, hq.2]⟩
      change noncoherentExamplePDerivEval k (p * q) ∈ _
      rw [hprod]
      exact Submodule.smul_mem _ _ hq.1

theorem noncoherentExample_countable
    (k : Type u) [Field k] [Countable k] :
    Countable (noncoherentExampleRing k) := by
  letI : Countable (MvPolynomial NoncoherentExampleVariables k) :=
    Countable.of_equiv _ AddMonoidAlgebra.coeffEquiv.symm
  exact Ideal.Quotient.mk_surjective.countable

instance noncoherentExample_countable_inst
    (k : Type u) [Field k] [Countable k] :
    Countable (noncoherentExampleRing k) :=
  noncoherentExample_countable k

theorem noncoherentExample_ideal_not_finitePresented
    (k : Type u) [Field k] [Countable k] :
    ¬ Module.FinitePresentation (noncoherentExampleRing k)
        (noncoherentExampleIdeal k) := by
  classical
  let A := noncoherentExampleRing k
  let S := MvPolynomial (ℕ × Bool) k
  let I := noncoherentExampleIdeal k
  let L : Submodule S (Fin 2 → S) :=
    Submodule.span S (Set.range (noncoherentExampleRelVec k))
  have hL : ¬ L.FG := by
    simpa [L] using noncoherentExample_relationSpan_not_fg k
  let y : A := noncoherentExampleY k
  let z : A := noncoherentExampleZ k
  let l : (Fin 2 → A) →ₗ[A] (I : Type u) :=
    { toFun := fun v =>
        ⟨v 0 * y + v 1 * z, by
          apply I.add_mem
          · exact I.mul_mem_left _ (by
              exact Ideal.subset_span (by simp [I, y]))
          · exact I.mul_mem_left _ (by
              exact Ideal.subset_span (by simp [I, z]))⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        change (v 0 + w 0) * y + (v 1 + w 1) * z =
          (v 0 * y + v 1 * z) + (w 0 * y + w 1 * z)
        rw [add_mul, add_mul]
        ac_rfl
      map_smul' := by
        intro a v
        apply Subtype.ext
        simp [smul_eq_mul, mul_add, mul_assoc] }
  have hl : Function.Surjective l := by
    have hmem : ∀ (q : A) (hq : q ∈ I), ∃ v, l v = ⟨q, hq⟩ := by
      intro q hq
      induction hq using Submodule.span_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · refine ⟨fun i => if i = 0 then 1 else 0, ?_⟩
          apply Subtype.ext
          simp [l, y]
        · refine ⟨fun i => if i = 1 then 1 else 0, ?_⟩
          apply Subtype.ext
          simp [l, z]
    | zero => exact ⟨0, by simp [l]⟩
    | add x x' hx hx' ih ih' =>
        obtain ⟨v, hv⟩ := ih
        obtain ⟨w, hw⟩ := ih'
        refine ⟨v + w, ?_⟩
        calc
          l (v + w) = l v + l w := l.map_add _ _
          _ = ⟨x, hx⟩ + ⟨x', hx'⟩ := congrArg₂ (· + ·) hv hw
          _ = ⟨x + x', _⟩ := by rfl
    | smul a x hx ih =>
        obtain ⟨v, hv⟩ := ih
        refine ⟨a • v, ?_⟩
        calc
          l (a • v) = a • l v := l.map_smul _ _
          _ = a • ⟨x, hx⟩ := congrArg (fun q => a • q) hv
          _ = ⟨a • x, _⟩ := by rfl
    intro x
    exact hmem (x : A) x.property
  intro hfp
  have hK : (LinearMap.ker l).FG :=
    Module.FinitePresentation.fg_ker l hl
  obtain ⟨t, ht⟩ := hK
  letI : Module A S := Module.compHom S (noncoherentExampleQuotientEval k)
  let ρ := noncoherentExampleQuotientEval k
  let θ : (Fin 2 → A) →ₗ[A] (Fin 2 → S) :=
    { toFun := fun v i => ρ (v i)
      map_add' := by
        intro v w
        funext i
        simp
      map_smul' := by
        intro a v
        funext i
        simp only [Pi.smul_apply]
        change ρ (a * v i) = ρ a * ρ (v i)
        exact map_mul ρ a (v i) }
  let avec (n : ℕ) : Fin 2 → A :=
    ![Ideal.Quotient.mk (noncoherentExampleRelationsIdeal k)
        (MvPolynomial.X (noncoherentExampleAVar n)),
      Ideal.Quotient.mk (noncoherentExampleRelationsIdeal k)
        (MvPolynomial.X (noncoherentExampleBVar n))]
  have havecKer (n : ℕ) : avec n ∈ LinearMap.ker l := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change (Ideal.Quotient.mk (noncoherentExampleRelationsIdeal k)
          (MvPolynomial.X (noncoherentExampleAVar n))) * y +
        (Ideal.Quotient.mk (noncoherentExampleRelationsIdeal k)
          (MvPolynomial.X (noncoherentExampleBVar n))) * z = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span ⟨n, rfl⟩
  have hθavec (n : ℕ) : θ (avec n) = noncoherentExampleRelVec k n := by
    funext i
    fin_cases i <;>
      simp [θ, avec, ρ, noncoherentExampleQuotientEval,
        noncoherentExampleEval, noncoherentExampleAVar,
        noncoherentExampleBVar, noncoherentExampleRelVec]
  have himage : ∀ v ∈ LinearMap.ker l, θ v ∈ L := by
    intro v hv
    obtain ⟨C, hC⟩ := Ideal.Quotient.mk_surjective (v 0)
    obtain ⟨D, hD⟩ := Ideal.Quotient.mk_surjective (v 1)
    let q := C * MvPolynomial.X noncoherentExampleYVar +
      D * MvPolynomial.X noncoherentExampleZVar
    have hq0 : Ideal.Quotient.mk (noncoherentExampleRelationsIdeal k) q = 0 := by
      have hv0 : l v = 0 := hv
      have hv1 : v 0 * y + v 1 * z = 0 := by
        simpa [l] using congrArg Subtype.val hv0
      rw [← hC, ← hD] at hv1
      simpa [q, y, z, noncoherentExampleY, noncoherentExampleZ] using hv1
    have hq : q ∈ noncoherentExampleRelationsIdeal k :=
      Ideal.Quotient.eq_zero_iff_mem.mp hq0
    have hd := (noncoherentExample_pderiv_eval_relations k q hq).1
    have heq : θ v = noncoherentExamplePDerivEval k q := by
      funext i
      fin_cases i
      · change ρ (v 0) =
          noncoherentExampleEval k (MvPolynomial.pderiv
            (Sum.inl 0) q)
        rw [← hC]
        simp [ρ, q, noncoherentExamplePDerivEval,
          noncoherentExampleQuotientEval, noncoherentExampleEval,
          noncoherentExampleYVar, noncoherentExampleZVar]
      · change ρ (v 1) =
          noncoherentExampleEval k (MvPolynomial.pderiv
            (Sum.inl 1) q)
        rw [← hD]
        simp [ρ, q, noncoherentExamplePDerivEval,
          noncoherentExampleQuotientEval, noncoherentExampleEval,
          noncoherentExampleYVar, noncoherentExampleZVar]
    rw [heq]
    exact hd
  have hmap : ∀ v ∈ Submodule.span A (t : Set (Fin 2 → A)),
      θ v ∈ Submodule.span S (t.image θ : Set (Fin 2 → S)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        exact Submodule.subset_span (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add v w hv hw ihv ihw =>
        rw [θ.map_add]
        exact Submodule.add_mem _ ihv ihw
    | smul a v hv ih =>
        rw [θ.map_smul]
        change ρ a • θ v ∈ _
        exact Submodule.smul_mem _ _ ih
  have hLfg : L.FG := by
    refine ⟨t.image θ, ?_⟩
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      apply himage v
      rw [← ht]
      exact Submodule.subset_span hv
    · apply Submodule.span_le.mpr
      rintro w ⟨n, rfl⟩
      rw [← hθavec n]
      apply hmap
      rw [ht]
      exact havecKer n
  exact hL hLfg

theorem noncoherentExample_not_coherent
    (k : Type u) [Field k] [Countable k] :
    ¬ IsCoherent (noncoherentExampleRing k) := by
  intro h
  exact noncoherentExample_ideal_not_finitePresented k
    (h (noncoherentExampleIdeal k) (by
      exact Submodule.fg_span (by simp [noncoherentExampleIdeal])))

theorem noncoherentExample_powerSeries_not_flat
    (k : Type u) [Field k] [Countable k] :
    ¬ Module.Flat (noncoherentExampleRing k)
        (PowerSeries (noncoherentExampleRing k)) := by
  rw [powerSeries_flat_iff_isCoherent]
  exact noncoherentExample_not_coherent k

/-! ## Completion of a polynomial ring -/

def polynomialXIdeal (R : Type u) [CommRing R] : Ideal (Polynomial R) :=
  Ideal.span {(Polynomial.X : Polynomial R)}

abbrev polynomialRingCompletion (R : Type u) [CommRing R] :=
  AdicCompletion (polynomialXIdeal R) (Polynomial R)

def IsPowerSeriesCompletion (R : Type u) [CommRing R] : Prop :=
  Nonempty
    (PowerSeries R ≃ₐ[Polynomial R]
      polynomialRingCompletion R)

theorem powerSeries_is_completion (R : Type u) [CommRing R] :
    IsPowerSeriesCompletion R := by
  let e := MvPolynomial.uniqueAlgEquiv R Unit
  have hI : (MvPolynomial.idealOfVars Unit R).map e.toRingEquiv =
      polynomialXIdeal R := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      simp [polynomialXIdeal, e]
    · intro hp
      simp only [Set.mem_singleton_iff] at hp
      subst p
      exact ⟨MvPolynomial.X default, ⟨default, rfl⟩, by simp [e]⟩
  let q (n : ℕ) :
      (MvPolynomial Unit R ⧸ (MvPolynomial.idealOfVars Unit R) ^ n) ≃ₐ[R]
        (Polynomial R ⧸ (polynomialXIdeal R) ^ n) :=
    Ideal.quotientEquivAlg _ _ e (by
      rw [← hI, ← Ideal.map_pow]
      rfl)
  let f (n : ℕ) :
      AdicCompletion (MvPolynomial.idealOfVars Unit R) (MvPolynomial Unit R) →ₐ[R]
        Polynomial R ⧸ (polynomialXIdeal R) ^ n :=
    (q n).toAlgHom.comp
      ((AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) n).restrictScalars R)
  have hq : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (q n).toAlgHom =
        (q m).toAlgHom.comp
          (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)) := by
    intro m n hle
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [q]
  have heval : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp
          ((AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) n).restrictScalars R) =
        (AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) m).restrictScalars R := by
    intro m n hle
    ext x
    let hn :
        (MvPolynomial.idealOfVars Unit R) ^ n • (⊤ : Ideal (MvPolynomial Unit R)) =
          (MvPolynomial.idealOfVars Unit R) ^ n := by
      ext y
      simp
    let hm :
        (MvPolynomial.idealOfVars Unit R) ^ m • (⊤ : Ideal (MvPolynomial Unit R)) =
          (MvPolynomial.idealOfVars Unit R) ^ m := by
      ext y
      simp
    have hpow :
        (MvPolynomial.idealOfVars Unit R) ^ n • (⊤ : Ideal (MvPolynomial Unit R)) ≤
          (MvPolynomial.idealOfVars Unit R) ^ m • (⊤ : Ideal (MvPolynomial Unit R)) := by
      simpa only [smul_eq_mul, Ideal.mul_top] using
        (Ideal.pow_le_pow_right hle :
          (MvPolynomial.idealOfVars Unit R) ^ n ≤
            (MvPolynomial.idealOfVars Unit R) ^ m)
    have hmap :
        ((Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hm).symm.toAlgHom).comp
            ((Ideal.Quotient.factorₐ (MvPolynomial Unit R)
              (Ideal.pow_le_pow_right hle)).comp
              (Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hn).toAlgHom) =
          Ideal.Quotient.factorₐ (MvPolynomial Unit R) hpow := by
      ext y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp [hn, hm]
    have htrans :
        Ideal.Quotient.factorₐ (MvPolynomial Unit R) hpow
            (AdicCompletion.eval (MvPolynomial.idealOfVars Unit R)
              (MvPolynomial Unit R) n x) =
            AdicCompletion.eval (MvPolynomial.idealOfVars Unit R)
              (MvPolynomial Unit R) m x := by
      change Ideal.Quotient.factorₐ (MvPolynomial Unit R) hpow (x.val n) = x.val m
      exact AdicCompletion.transitionMap_comp_eval_apply
        (I := MvPolynomial.idealOfVars Unit R) (M := MvPolynomial Unit R) hle x
    have hraw := congrArg (fun g ↦
      g (AdicCompletion.eval (MvPolynomial.idealOfVars Unit R)
        (MvPolynomial Unit R) n x)) hmap
    rw [htrans] at hraw
    have hstd := congrArg (fun y ↦
      Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hm y) hraw
    change (Ideal.Quotient.factorₐ (MvPolynomial Unit R)
      (Ideal.pow_le_pow_right hle))
          (Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hn
            (AdicCompletion.eval (MvPolynomial.idealOfVars Unit R)
              (MvPolynomial Unit R) n x)) =
      Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hm
        (AdicCompletion.eval (MvPolynomial.idealOfVars Unit R)
          (MvPolynomial Unit R) m x)
    convert hstd using 1
    let z : MvPolynomial Unit R ⧸ (MvPolynomial.idealOfVars Unit R) ^ m :=
      (Ideal.Quotient.factorₐ (MvPolynomial Unit R)
        (Ideal.pow_le_pow_right hle))
        ((Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hn)
          (AdicCompletion.eval (MvPolynomial.idealOfVars Unit R)
            (MvPolynomial Unit R) n x))
    have hcancel :
        (Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hm)
            ((((Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hm).symm.toAlgHom).comp
              ((Ideal.Quotient.factorₐ (MvPolynomial Unit R)
                (Ideal.pow_le_pow_right hle)).comp
                (Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hn).toAlgHom))
              (AdicCompletion.eval (MvPolynomial.idealOfVars Unit R)
                (MvPolynomial Unit R) n x)) = z := by
      change (Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hm)
          ((Ideal.quotientEquivAlgOfEq (MvPolynomial Unit R) hm).symm z) = z
      exact AlgEquiv.apply_symm_apply _ _
    simpa only [z, AlgHom.comp_apply] using hcancel.symm
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    intro m n hle
    change (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp
          ((q n).toAlgHom.comp
            ((AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) n).restrictScalars R)) =
      (q m).toAlgHom.comp
        ((AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) m).restrictScalars R)
    rw [← AlgHom.comp_assoc, hq hle, AlgHom.comp_assoc, heval hle]
  have evalCompat (A : Type u) [CommRing A] (I : Ideal A) :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
            (AdicCompletion.evalₐ I n) = AdicCompletion.evalₐ I m := by
    intro m n hle
    ext x
    let hn : I ^ n • (⊤ : Ideal A) = I ^ n := by
      ext y
      simp
    let hm : I ^ m • (⊤ : Ideal A) = I ^ m := by
      ext y
      simp
    have hpow : I ^ n • (⊤ : Ideal A) ≤ I ^ m • (⊤ : Ideal A) := by
      simpa only [smul_eq_mul, Ideal.mul_top] using
        (Ideal.pow_le_pow_right hle : I ^ n ≤ I ^ m)
    have hmap :
        ((Ideal.quotientEquivAlgOfEq A hm).symm.toAlgHom).comp
            ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
              (Ideal.quotientEquivAlgOfEq A hn).toAlgHom) =
          Ideal.Quotient.factorₐ A hpow := by
      ext y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp [hn, hm]
    have htrans :
        Ideal.Quotient.factorₐ A hpow (AdicCompletion.eval I A n x) =
          AdicCompletion.eval I A m x := by
      change Ideal.Quotient.factorₐ A hpow (x.val n) = x.val m
      exact AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := A) hle x
    have hraw := congrArg (fun g ↦ g (AdicCompletion.eval I A n x)) hmap
    rw [htrans] at hraw
    have hstd := congrArg (fun y ↦ Ideal.quotientEquivAlgOfEq A hm y) hraw
    let z : A ⧸ I ^ m :=
      Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)
        (Ideal.quotientEquivAlgOfEq A hn (AdicCompletion.eval I A n x))
    have hcancel :
        Ideal.quotientEquivAlgOfEq A hm
            ((((Ideal.quotientEquivAlgOfEq A hm).symm.toAlgHom).comp
              ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
                (Ideal.quotientEquivAlgOfEq A hn).toAlgHom))
              (AdicCompletion.eval I A n x)) = z := by
      change Ideal.quotientEquivAlgOfEq A hm
          ((Ideal.quotientEquivAlgOfEq A hm).symm z) = z
      exact AlgEquiv.apply_symm_apply _ _
    change Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)
          (Ideal.quotientEquivAlgOfEq A hn (AdicCompletion.eval I A n x)) =
      Ideal.quotientEquivAlgOfEq A hm (AdicCompletion.eval I A m x)
    calc
      _ = Ideal.quotientEquivAlgOfEq A hm
          ((((Ideal.quotientEquivAlgOfEq A hm).symm.toAlgHom).comp
            ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
              (Ideal.quotientEquivAlgOfEq A hn).toAlgHom))
            (AdicCompletion.eval I A n x)) := by
            simpa only [z, AlgHom.comp_apply] using hcancel.symm
      _ = _ := hstd
  let qinv (n : ℕ) := (q n).symm
  let g (n : ℕ) :
      AdicCompletion (polynomialXIdeal R) (Polynomial R) →ₐ[R]
        MvPolynomial Unit R ⧸ (MvPolynomial.idealOfVars Unit R) ^ n :=
    (qinv n).toAlgHom.comp
      ((AdicCompletion.evalₐ (polynomialXIdeal R) n).restrictScalars R)
  have hqinv : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp
          (qinv n).toAlgHom =
        (qinv m).toAlgHom.comp
          (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)) := by
    intro m n hle
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [f, qinv, q]
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (g n) = g m := by
    intro m n hle
    change (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp
          ((qinv n).toAlgHom.comp
            ((AdicCompletion.evalₐ (polynomialXIdeal R) n).restrictScalars R)) =
      (qinv m).toAlgHom.comp
        ((AdicCompletion.evalₐ (polynomialXIdeal R) m).restrictScalars R)
    rw [← AlgHom.comp_assoc, hqinv hle, AlgHom.comp_assoc]
    have hpoly := evalCompat (Polynomial R) (polynomialXIdeal R) hle
    have hpolyR :
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp
            ((AdicCompletion.evalₐ (polynomialXIdeal R) n).restrictScalars R) =
          (AdicCompletion.evalₐ (polynomialXIdeal R) m).restrictScalars R := by
      ext x
      change (Ideal.Quotient.factorₐ (Polynomial R)
        (Ideal.pow_le_pow_right hle))
          (AdicCompletion.evalₐ (polynomialXIdeal R) n x) =
        AdicCompletion.evalₐ (polynomialXIdeal R) m x
      exact congrArg (fun h => h x) hpoly
    rw [hpolyR]
  let F := AdicCompletion.liftAlgHom (polynomialXIdeal R) f hf
  let G := AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars Unit R) g hg
  have hGF : G.comp F = AlgHom.id R _ := by
    apply AlgHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change (AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) n)
        (AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars Unit R) g hg
          (AdicCompletion.liftAlgHom (polynomialXIdeal R) f hf x)) =
      AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) n x
    rw [AdicCompletion.evalₐ_liftAlgHom]
    change (qinv n)
        (AdicCompletion.evalₐ (polynomialXIdeal R) n
          (AdicCompletion.liftAlgHom (polynomialXIdeal R) f hf x)) =
      AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) n x
    rw [AdicCompletion.evalₐ_liftAlgHom]
    change (q n).symm ((q n)
        (AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) n x)) = _
    exact (q n).symm_apply_apply _
  have hFG : F.comp G = AlgHom.id R _ := by
    apply AlgHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change (AdicCompletion.evalₐ (polynomialXIdeal R) n)
        (AdicCompletion.liftAlgHom (polynomialXIdeal R) f hf
          (AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars Unit R) g hg x)) =
      AdicCompletion.evalₐ (polynomialXIdeal R) n x
    rw [AdicCompletion.evalₐ_liftAlgHom]
    change (q n)
        (AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) n
          (AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars Unit R) g hg x)) =
      AdicCompletion.evalₐ (polynomialXIdeal R) n x
    rw [AdicCompletion.evalₐ_liftAlgHom]
    change (q n) ((q n).symm
        (AdicCompletion.evalₐ (polynomialXIdeal R) n x)) = _
    exact (q n).apply_symm_apply _
  let E :
      AdicCompletion (MvPolynomial.idealOfVars Unit R) (MvPolynomial Unit R) ≃ₐ[R]
        AdicCompletion (polynomialXIdeal R) (Polynomial R) :=
    AlgEquiv.ofAlgHom F G hFG hGF
  have hE (a : MvPolynomial Unit R) :
      E (algebraMap (MvPolynomial Unit R)
          (AdicCompletion (MvPolynomial.idealOfVars Unit R) (MvPolynomial Unit R)) a) =
        algebraMap (Polynomial R)
          (AdicCompletion (polynomialXIdeal R) (Polynomial R)) (e a) := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change (q n)
        (AdicCompletion.evalₐ (MvPolynomial.idealOfVars Unit R) n
          (algebraMap (MvPolynomial Unit R)
            (AdicCompletion (MvPolynomial.idealOfVars Unit R) (MvPolynomial Unit R)) a)) =
      AdicCompletion.evalₐ (polynomialXIdeal R) n
        (algebraMap (Polynomial R)
          (AdicCompletion (polynomialXIdeal R) (Polynomial R)) (e a))
    simp [E, F, q, AdicCompletion.algebraMap_apply]
  have hcoe (p : Polynomial R) :
      algebraMap (Polynomial R) (PowerSeries R) p =
        algebraMap (MvPolynomial Unit R) (PowerSeries R) (e.symm p) := by
    let lhs : Polynomial R →ₐ[R] PowerSeries R :=
      Polynomial.coeToPowerSeries.algHom R
    let rhs : Polynomial R →ₐ[R] PowerSeries R :=
      (MvPolynomial.coeToMvPowerSeries.algHom R).comp e.symm.toAlgHom
    have heq : lhs = rhs := by
      apply Polynomial.algHom_ext
      simp [lhs, rhs, e, Polynomial.coeToPowerSeries.algHom,
        MvPolynomial.coeToMvPowerSeries.algHom, PowerSeries.X_apply]
    exact congrArg (fun h => h p) heq
  have hG (p : Polynomial R) :
      G (algebraMap (Polynomial R)
          (AdicCompletion (polynomialXIdeal R) (Polynomial R)) p) =
        algebraMap (MvPolynomial Unit R)
          (AdicCompletion (MvPolynomial.idealOfVars Unit R) (MvPolynomial Unit R))
          (e.symm p) := by
    have hp : E (algebraMap (MvPolynomial Unit R)
          (AdicCompletion (MvPolynomial.idealOfVars Unit R) (MvPolynomial Unit R))
          (e.symm p)) =
        algebraMap (Polynomial R)
          (AdicCompletion (polynomialXIdeal R) (Polynomial R)) p := by
      simpa using hE (e.symm p)
    rw [← hp]
    have hx := congrArg (fun h => h
      (algebraMap (MvPolynomial Unit R)
        (AdicCompletion (MvPolynomial.idealOfVars Unit R) (MvPolynomial Unit R))
        (e.symm p))) hGF
    simpa [E, AlgHom.comp_apply] using hx
  let P := MvPowerSeries.toAdicCompletionAlgEquiv Unit R
  let H : PowerSeries R →ₐ[Polynomial R] polynomialRingCompletion R :=
    { toFun := fun x => E (P x)
      map_one' := by simp [E, P]
      map_mul' := by intro x y; simp [E, P]
      map_zero' := by simp [E, P]
      map_add' := by intro x y; simp [E, P]
      commutes' := by
        intro p
        rw [hcoe, P.commutes, hE]
        simp }
  let Hinv : polynomialRingCompletion R →ₐ[Polynomial R] PowerSeries R :=
    { toFun := fun x => P.symm (G x)
      map_one' := by
        change P.symm (G 1) = 1
        rw [map_one]
        exact P.symm.map_one
      map_mul' := by
        intro x y
        change P.symm (G (x * y)) = P.symm (G x) * P.symm (G y)
        rw [map_mul]
        exact P.symm.map_mul _ _
      map_zero' := by
        change P.symm (G 0) = 0
        rw [map_zero]
        exact P.symm.map_zero
      map_add' := by
        intro x y
        change P.symm (G (x + y)) = P.symm (G x) + P.symm (G y)
        rw [map_add]
        exact P.symm.map_add _ _
      commutes' := by
        intro p
        change P.symm (G (algebraMap (Polynomial R)
          (AdicCompletion (polynomialXIdeal R) (Polynomial R)) p)) =
          algebraMap (Polynomial R) (PowerSeries R) p
        rw [hG, ← P.commutes, hcoe]
        exact P.symm_apply_apply _ }
  have hGF_apply (x :
      AdicCompletion (MvPolynomial.idealOfVars Unit R) (MvPolynomial Unit R)) :
      G (F x) = x := by
    have hx := congrArg (fun h => h x) hGF
    simpa [AlgHom.comp_apply] using hx
  have hFG_apply (x :
      AdicCompletion (polynomialXIdeal R) (Polynomial R)) :
      F (G x) = x := by
    have hx := congrArg (fun h => h x) hFG
    simpa [AlgHom.comp_apply] using hx
  exact ⟨AlgEquiv.ofAlgHom H Hinv (by
    apply AlgHom.ext
    intro x
    change E (P (P.symm (G x))) = x
    change F (P (P.symm (G x))) = x
    rw [P.apply_symm_apply, hFG_apply]) (by
    apply AlgHom.ext
    intro x
    change P.symm (G (E (P x))) = x
    change P.symm (G (F (P x))) = x
    rw [hGF_apply, P.symm_apply_apply])⟩

theorem completion_polynomial_ring_not_flat :
    ∃ (R : Type u) (_ : CommRing R),
      IsPowerSeriesCompletion R ∧
        ¬ Module.Flat R (PowerSeries R) ∧
        ¬ Module.Flat (Polynomial R) (PowerSeries R) := by
  sorry

/-! ## Valuation rings and almost integral elements -/

theorem valuationRing_is_coherent (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] :
    IsCoherent R := by
  sorry

theorem valuationRing_is_normal (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] :
    IsIntegrallyClosed R := by
  sorry

theorem valuationRing_powerSeries_flat (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] :
    Module.Flat R (PowerSeries R) := by
  sorry

theorem exists_valuationRing_dimension_gt_one_not_flat_over_polynomial :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : ValuationRing R),
      ¬ Ring.KrullDimLE 1 R ∧
        Module.Flat R (PowerSeries R) ∧
          ¬ Module.Flat (Polynomial R) (PowerSeries R) := by
  sorry

def IsCompletelyNormal (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] : Prop :=
  ∀ {x : K}, IsAlmostIntegral R x → ∃ r : R, algebraMap R K r = x

/-
The series used in the almost-integral argument is represented by its
coefficient data.  The source writes the coefficient of `x ^ n` as
`r * α ^ (n - 1)` but displays the identity `(a x - b) f = -r b`.
That identity uses the shifted coefficients `r * α ^ n`, including the
constant term `r`, so that is the convention used here.
-/
structure AlmostIntegralSeriesData (R : Type u) (K : Type v)
    [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (α : K) (r : R) where
  coefficient : ℕ → R
  coefficient_spec :
    ∀ n, algebraMap R K (coefficient n) = algebraMap R K r * α ^ n

def almostIntegralSeries {R : Type u} {K : Type v}
    [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {α : K} {r : R} (d : AlmostIntegralSeriesData R K α r) : PowerSeries R :=
  PowerSeries.mk d.coefficient

theorem exists_almostIntegralSeriesData
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (α : K) (r : R) (hr : r ≠ 0)
    (hpow : ∀ n : ℕ, 1 ≤ n →
      ∃ c : R, algebraMap R K c = algebraMap R K r * α ^ n) :
    Nonempty (AlmostIntegralSeriesData R K α r) := by
  sorry

theorem almostIntegralSeries_factorization
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (α : K) (r a b : R)
    (d : AlmostIntegralSeriesData R K α r) (hb : b ≠ 0)
    (hα : algebraMap R K a = α * algebraMap R K b) :
    (PowerSeries.C a * PowerSeries.X - PowerSeries.C b) *
        almostIntegralSeries d = PowerSeries.C (-r * b) := by
  sorry

/-
The multiplicative subset used in the proof consists of polynomials whose
constant coefficient is one.  It is represented by the canonical preimage
construction for submonoids.
-/
def almostIntegralDenominatorSubmonoid (R : Type u) [CommRing R] :
    Submonoid (Polynomial R) :=
  Submonoid.comap Polynomial.constantCoeff (Submonoid.powers (1 : R))

abbrev almostIntegralPolynomialLocalization (R : Type u) [CommRing R] :=
  Localization (almostIntegralDenominatorSubmonoid R)

noncomputable def almostIntegralPolynomialLocalizationMap
    (R : Type u) [CommRing R] :
    almostIntegralPolynomialLocalization R →+* PowerSeries R :=
  IsLocalization.lift (M := almostIntegralDenominatorSubmonoid R)
    (S := almostIntegralPolynomialLocalization R)
    (g := Polynomial.coeToPowerSeries.ringHom) (by
      intro h
      rw [PowerSeries.isUnit_iff_constantCoeff]
      change IsUnit (Polynomial.constantCoeff (h : Polynomial R))
      rcases (Submonoid.mem_powers_iff _ _).mp h.property with ⟨n, hn⟩
      rw [← hn]
      simp)

noncomputable instance almostIntegralPolynomialLocalizationPowerSeriesAlgebra
    (R : Type u) [CommRing R] :
    Algebra (almostIntegralPolynomialLocalization R) (PowerSeries R) :=
  RingHom.toAlgebra (almostIntegralPolynomialLocalizationMap R)

theorem almostIntegralPolynomialLocalization_faithfullyFlat
    (R : Type u) [CommRing R] [IsDomain R]
    (hflat : Module.Flat (Polynomial R) (PowerSeries R)) :
    RingHom.FaithfullyFlat (almostIntegralPolynomialLocalizationMap R) := by
  sorry

def almostIntegralPrincipalPolynomial (R : Type u) [CommRing R]
    (a b : R) : Ideal (Polynomial R) :=
  Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b}

abbrev almostIntegralLocalizedPrincipalIdeal
    (R : Type u) [CommRing R] (a b : R) :
    Ideal (almostIntegralPolynomialLocalization R) :=
  Ideal.map (algebraMap (Polynomial R)
    (almostIntegralPolynomialLocalization R))
    (almostIntegralPrincipalPolynomial R a b)

abbrev almostIntegralPowerSeriesPrincipalIdeal
    (R : Type u) [CommRing R] (a b : R) : Ideal (PowerSeries R) :=
  Ideal.map (almostIntegralPolynomialLocalizationMap R)
    (almostIntegralLocalizedPrincipalIdeal R a b)

noncomputable def almostIntegralPrincipalQuotientMap
    (R : Type u) [CommRing R] (a b : R) :
    (almostIntegralPolynomialLocalization R ⧸
        almostIntegralLocalizedPrincipalIdeal R a b) →+*
      (PowerSeries R ⧸ almostIntegralPowerSeriesPrincipalIdeal R a b) :=
  Ideal.Quotient.lift (almostIntegralLocalizedPrincipalIdeal R a b)
    ((Ideal.Quotient.mk (almostIntegralPowerSeriesPrincipalIdeal R a b)).comp
      (almostIntegralPolynomialLocalizationMap R))
    (fun _ hh => Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (almostIntegralPolynomialLocalizationMap R) hh))

theorem almostIntegralPrincipalQuotientMap_injective
    (R : Type u) [CommRing R] [IsDomain R]
    (hflat : Module.Flat (Polynomial R) (PowerSeries R)) (a b : R) :
    Function.Injective (almostIntegralPrincipalQuotientMap R a b) := by
  sorry

theorem flat_powerSeries_normal_iff_completelyNormal
    (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (hflat : Module.Flat (Polynomial R) (PowerSeries R)) :
    IsIntegrallyClosed R ↔ IsCompletelyNormal R K := by
  sorry

theorem valuationRing_dimension_gt_one_not_completelyNormal
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (hdim : ¬ Ring.KrullDimLE 1 R) :
    ¬ IsCompletelyNormal R (FractionRing R) := by
  sorry

theorem valuationRing_dimension_gt_one_not_flat_over_polynomial
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (hdim : ¬ Ring.KrullDimLE 1 R) :
    Module.Flat R (PowerSeries R) ∧
      ¬ Module.Flat (Polynomial R) (PowerSeries R) := by
  sorry

/-! ## The nonflat localized completion

The source leaves the coefficient ring `k` implicit.  The Noetherian step in
the argument uses that `k[z][[x]]` is Noetherian, so the field hypothesis is
attached to the kernel characterization and the nonflatness conclusions below.
-/

abbrev NonflatLocalizationVariables := Fin 2 ⊕ ℕ

def nonflatLocalizationYVar : NonflatLocalizationVariables := Sum.inl 0

def nonflatLocalizationZVar : NonflatLocalizationVariables := Sum.inl 1

def nonflatLocalizationAVar (n : ℕ) : NonflatLocalizationVariables := Sum.inr n

def nonflatLocalizationYRelation (n : ℕ) (k : Type u) [CommSemiring k] :
    MvPolynomial NonflatLocalizationVariables k :=
  MvPolynomial.X nonflatLocalizationYVar * MvPolynomial.X (nonflatLocalizationAVar n)

def nonflatLocalizationARelation (p : ℕ × ℕ) (k : Type u) [CommSemiring k] :
    MvPolynomial NonflatLocalizationVariables k :=
  MvPolynomial.X (nonflatLocalizationAVar p.1) *
    MvPolynomial.X (nonflatLocalizationAVar p.2)

def nonflatLocalizationRelationsIdeal (k : Type u) [CommSemiring k] :
    Ideal (MvPolynomial NonflatLocalizationVariables k) :=
  Ideal.span
    (Set.range (fun n => nonflatLocalizationYRelation n k) ∪
      Set.range (fun p => nonflatLocalizationARelation p k))

abbrev nonflatLocalizationRing (k : Type u) [CommRing k] :=
  MvPolynomial NonflatLocalizationVariables k ⧸ nonflatLocalizationRelationsIdeal k

def nonflatLocalizationF (k : Type u) [CommRing k] : nonflatLocalizationRing k :=
  Ideal.Quotient.mk (nonflatLocalizationRelationsIdeal k)
    (MvPolynomial.X nonflatLocalizationZVar)

def nonflatLocalizationA (k : Type u) [CommRing k] (n : ℕ) : nonflatLocalizationRing k :=
  Ideal.Quotient.mk (nonflatLocalizationRelationsIdeal k)
    (MvPolynomial.X (nonflatLocalizationAVar n))

def nonflatLocalizationY (k : Type u) [CommRing k] : nonflatLocalizationRing k :=
  Ideal.Quotient.mk (nonflatLocalizationRelationsIdeal k)
    (MvPolynomial.X nonflatLocalizationYVar)

abbrev nonflatLocalizationPowerSeries (k : Type u) [CommRing k] :=
  PowerSeries (Localization.Away (nonflatLocalizationF k))

noncomputable def nonflatLocalizationCompletionMap
    (k : Type u) [CommRing k] :
    PowerSeries (nonflatLocalizationRing k) →+*
      nonflatLocalizationPowerSeries k :=
  PowerSeries.map (algebraMap (nonflatLocalizationRing k)
    (Localization.Away (nonflatLocalizationF k)))

def powerSeriesMultiplication (R : Type u) [CommRing R] (r : R) :
    PowerSeries R →ₗ[PowerSeries R] PowerSeries R :=
  LinearMap.mulLeft (PowerSeries R) (PowerSeries.C r)

def powerSeriesMulKernel (R : Type u) [CommRing R] (r : R) : Ideal (PowerSeries R) :=
  (LinearMap.ker (powerSeriesMultiplication R r) : Ideal (PowerSeries R))

theorem powerSeriesMulKernel_exact (R : Type u) [CommRing R] (r : R) :
    Function.Exact (powerSeriesMulKernel R r).subtype
      (powerSeriesMultiplication R r) :=
  by
  sorry

def nonflatLocalizationKernel (k : Type u) [CommRing k] :
    Ideal (nonflatLocalizationPowerSeries k) :=
  powerSeriesMulKernel (Localization.Away (nonflatLocalizationF k))
    (algebraMap (nonflatLocalizationRing k)
      (Localization.Away (nonflatLocalizationF k))
      (nonflatLocalizationY k))

def nonflatLocalizationSourceKernel (k : Type u) [CommRing k] :
    Ideal (PowerSeries (nonflatLocalizationRing k)) :=
  powerSeriesMulKernel (nonflatLocalizationRing k)
    (nonflatLocalizationY k)

/-!
The source describes elements of the kernel coefficientwise as finite sums
of the `a_m` with coefficients in `k[z]`.  `Polynomial k` is the canonical
Lean model for `k[z]`, and a finitely supported family records the finite
support required separately at each power of `x`.
-/

def nonflatLocalizationZPolynomialMap (k : Type u) [CommRing k] :
    Polynomial k →+* nonflatLocalizationRing k :=
  Polynomial.eval₂RingHom (algebraMap k (nonflatLocalizationRing k))
    (nonflatLocalizationF k)

def NonflatLocalizationKernelExpansion (k : Type u) [CommRing k]
    (g : PowerSeries (nonflatLocalizationRing k)) : Prop :=
  ∃ c : ℕ → (ℕ →₀ Polynomial k),
    ∀ n, PowerSeries.coeff n g =
      ∑ m ∈ (c n).support,
        nonflatLocalizationZPolynomialMap k (c n m) * nonflatLocalizationA k m

theorem nonflatLocalizationSourceKernel_iff_expansion
    (k : Type u) [Field k] (g : PowerSeries (nonflatLocalizationRing k)) :
    g ∈ nonflatLocalizationSourceKernel k ↔
      NonflatLocalizationKernelExpansion k g := by
  sorry

def nonflatLocalizationTargetMultiplication (k : Type u) [CommRing k] :
    nonflatLocalizationPowerSeries k →ₗ[nonflatLocalizationPowerSeries k]
      nonflatLocalizationPowerSeries k :=
  powerSeriesMultiplication (Localization.Away (nonflatLocalizationF k))
    (algebraMap (nonflatLocalizationRing k)
      (Localization.Away (nonflatLocalizationF k)) (nonflatLocalizationY k))

def nonflatLocalizationSourceMultiplication (k : Type u) [CommRing k] :
    PowerSeries (nonflatLocalizationRing k) →ₗ[PowerSeries (nonflatLocalizationRing k)]
      PowerSeries (nonflatLocalizationRing k) :=
  powerSeriesMultiplication (nonflatLocalizationRing k) (nonflatLocalizationY k)

theorem nonflatLocalizationSource_exact (k : Type u) [CommRing k] :
    Function.Exact (nonflatLocalizationSourceKernel k).subtype
      (nonflatLocalizationSourceMultiplication k) :=
  by
  sorry

theorem nonflatLocalizationTarget_exact (k : Type u) [CommRing k] :
    Function.Exact (nonflatLocalizationKernel k).subtype
      (nonflatLocalizationTargetMultiplication k) :=
  by
  sorry

def nonflatLocalizationWitness (k : Type u) [CommRing k] :
    nonflatLocalizationPowerSeries k :=
  PowerSeries.mk fun n =>
    (Localization.Away.invSelf (nonflatLocalizationF k)) ^ n *
      algebraMap (nonflatLocalizationRing k)
        (Localization.Away (nonflatLocalizationF k))
        (nonflatLocalizationA k n)

@[simp]
theorem nonflatLocalizationWitness_coeff
    (k : Type u) [CommRing k] (n : ℕ) :
    PowerSeries.coeff n (nonflatLocalizationWitness k) =
      (Localization.Away.invSelf (nonflatLocalizationF k)) ^ n *
        algebraMap (nonflatLocalizationRing k)
          (Localization.Away (nonflatLocalizationF k))
          (nonflatLocalizationA k n) := by
  simp [nonflatLocalizationWitness]

theorem nonflatLocalizationWitness_mem_kernel
    (k : Type u) [Field k] :
    nonflatLocalizationWitness k ∈ nonflatLocalizationKernel k := by
  sorry

theorem nonflatLocalizationWitness_not_mem_mapped_kernel
    (k : Type u) [Field k] :
    nonflatLocalizationWitness k ∉
      Ideal.map (algebraMap (PowerSeries (nonflatLocalizationRing k))
        (nonflatLocalizationPowerSeries k))
        (nonflatLocalizationSourceKernel k) := by
  sorry

theorem nonflatLocalizationKernel_ne_mapped_kernel
    (k : Type u) [Field k] :
    nonflatLocalizationKernel k ≠
      Ideal.map (algebraMap (PowerSeries (nonflatLocalizationRing k))
        (nonflatLocalizationPowerSeries k))
        (nonflatLocalizationSourceKernel k) := by
  intro h
  exact nonflatLocalizationWitness_not_mem_mapped_kernel k
    (h ▸ nonflatLocalizationWitness_mem_kernel k)

theorem nonflatLocalizationCompletionMap_flat_implies_kernel_eq
    (k : Type u) [CommRing k]
    (hflat : RingHom.Flat (nonflatLocalizationCompletionMap k)) :
    nonflatLocalizationKernel k =
      Ideal.map (algebraMap (PowerSeries (nonflatLocalizationRing k))
        (nonflatLocalizationPowerSeries k))
        (nonflatLocalizationSourceKernel k) := by
  sorry

theorem nonflatLocalizationCompletionMap_not_flat
    (k : Type u) [Field k] :
    ¬ RingHom.Flat (nonflatLocalizationCompletionMap k) := by
  intro hflat
  exact nonflatLocalizationKernel_ne_mapped_kernel k
    (nonflatLocalizationCompletionMap_flat_implies_kernel_eq k hflat)

/-! ## Completion after localization -/

abbrev localizedAdicCompletion
    (A : Type u) [CommRing A] (I : Ideal A) (f : A) : Type u :=
  AdicCompletion (Ideal.map (algebraMap A (Localization.Away f)) I)
    (Localization.Away f)

def nonflatLocalizationAdicIdeal (k : Type u) [CommRing k] :
    Ideal (PowerSeries (nonflatLocalizationRing k)) :=
  Ideal.span {(PowerSeries.X : PowerSeries (nonflatLocalizationRing k))}

abbrev nonflatLocalizationAdicCompletion (k : Type u) [CommRing k] :=
  localizedAdicCompletion (PowerSeries (nonflatLocalizationRing k))
    (nonflatLocalizationAdicIdeal k)
    (algebraMap (nonflatLocalizationRing k)
      (PowerSeries (nonflatLocalizationRing k)) (nonflatLocalizationF k))

theorem nonflatLocalizationAdicIdeal_isPrincipal
    (k : Type u) [CommRing k] :
    (nonflatLocalizationAdicIdeal k).IsPrincipal := by
  sorry

theorem nonflatLocalizationPowerSeries_completion_equiv
    (k : Type u) [CommRing k] :
    Nonempty
      (nonflatLocalizationPowerSeries k ≃+*
        nonflatLocalizationAdicCompletion k) := by
  sorry

theorem nonflatLocalizationAdicCompletion_not_flat
    (k : Type u) [Field k] :
    ¬ Module.Flat (PowerSeries (nonflatLocalizationRing k))
      (nonflatLocalizationAdicCompletion k) := by
  sorry

theorem exists_nonflat_localized_adic_completion :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A) (f : A),
      I.IsPrincipal ∧ IsAdicComplete I A ∧
        ¬ Module.Flat A (localizedAdicCompletion A I f) := by
  sorry

end Formalization.Books.Examples.Unit12
