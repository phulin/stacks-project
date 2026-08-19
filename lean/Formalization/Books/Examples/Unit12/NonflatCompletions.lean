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
import Mathlib.RingTheory.PowerSeries.Basic
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

theorem noncoherentExample_countable
    (k : Type u) [Field k] [Countable k] :
    Countable (noncoherentExampleRing k) := by
  sorry

instance noncoherentExample_countable_inst
    (k : Type u) [Field k] [Countable k] :
    Countable (noncoherentExampleRing k) :=
  noncoherentExample_countable k

theorem noncoherentExample_ideal_not_finitePresented
    (k : Type u) [Field k] [Countable k] :
    ¬ Module.FinitePresentation (noncoherentExampleRing k)
        (noncoherentExampleIdeal k) := by
  sorry

theorem noncoherentExample_not_coherent
    (k : Type u) [Field k] [Countable k] :
    ¬ IsCoherent (noncoherentExampleRing k) := by
  sorry

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
  sorry

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
