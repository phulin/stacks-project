import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Field.ZMod

/-!
# Commutative Algebra, Chapter 64: symbolic powers

The symbolic power is expressed using Mathlib's canonical localization at a
prime, ideal extension, quotient map, and ring-homomorphism kernel.  The
associated-prime statement uses Mathlib's canonical set of associated prime
ideals; under the chapter's Noetherian hypothesis this agrees with the exact
annihilator formulation recorded in Chapter 63.
-/

namespace Formalization.Books.Algebra.Unit64

universe u v

noncomputable section

open scoped Pointwise TensorProduct

/-! ## Symbolic powers -/

/-- The `n`th symbolic power of a prime ideal, defined as the kernel of
the map to the quotient of the localization by the extended ordinary power. -/
def symbolicPower {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (n : ℕ) : Ideal R :=
  RingHom.ker
    ((Ideal.Quotient.mk
        ((p ^ n).map (algebraMap R (Localization.AtPrime p)))).comp
      (algebraMap R (Localization.AtPrime p)))

/-- Ordinary powers are contained in the corresponding symbolic powers. -/
theorem pow_le_symbolicPower
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ) :
    p ^ n ≤ symbolicPower p n := by
  intro x hx
  change x ∈ RingHom.ker _
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hx

private theorem mem_symbolicPower_iff
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (n : ℕ) (x : R) :
    x ∈ symbolicPower p n ↔ ∃ s ∉ p, s * x ∈ p ^ n := by
  change (Ideal.Quotient.mk
      ((p ^ n).map (algebraMap R (Localization.AtPrime p))))
      (algebraMap R (Localization.AtPrime p) x) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,
    IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl]
  rfl

/-- Equality of ordinary and symbolic powers is not valid for all prime ideals. -/
theorem symbolicPower_eq_pow_not_general :
    ¬ ∀ (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ),
      p ^ n = symbolicPower p n := by
  intro h
  let A := ULift.{u} (Polynomial (ZMod 4))
  let c0 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) _
  let F0 : Polynomial (ZMod 4) →+* Polynomial (ZMod 2) :=
    Polynomial.mapRingHom c0
  let F : A →+* ULift.{u} (Polynomial (ZMod 2)) := F0.ulift
  let instDomain : IsDomain (ULift.{u} (Polynomial (ZMod 2))) :=
    (ULift.ringEquiv : ULift.{u} (Polynomial (ZMod 2)) ≃+*
      Polynomial (ZMod 2)).isDomain
  let K : Ideal A := RingHom.ker F
  have hK : K.IsPrime := by
    dsimp [K]
    exact RingHom.ker_isPrime F
  let I : Ideal A := Ideal.span {(ULift.up (2 : Polynomial (ZMod 4))) *
    ULift.up Polynomial.X}
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hIK : I ≤ K := by
    rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change F ((ULift.up (2 : Polynomial (ZMod 4))) * ULift.up Polynomial.X) = 0
    rw [map_mul, RingHom.ulift_apply, RingHom.ulift_apply]
    change ULift.up (F0 (2 : Polynomial (ZMod 4)) * F0 Polynomial.X) = 0
    have hc : c0 (2 : ZMod 4) = 0 := by
      change ZMod.cast (2 : ZMod 4) = 0
      decide
    have hF02 : F0 (2 : Polynomial (ZMod 4)) = 0 := by
      change Polynomial.map c0 (2 : Polynomial (ZMod 4)) = 0
      rw [show (2 : Polynomial (ZMod 4)) = Polynomial.C (2 : ZMod 4) by rfl,
        Polynomial.map_C, hc, Polynomial.C_0]
    rw [hF02, zero_mul]
    rfl
  have hXK : ULift.up Polynomial.X ∉ K := by
    change F (ULift.up Polynomial.X) ≠ 0
    rw [RingHom.ulift_apply]
    change ULift.up (F0 Polynomial.X) ≠ 0
    rw [show F0 Polynomial.X = Polynomial.X by simp [F0]]
    exact fun hz => Polynomial.X_ne_zero (ULift.up_injective hz)
  have hp : (K.map q).IsPrime := by
    apply Ideal.isPrime_map_quotientMk_of_isPrime hIK
  have hqX : q (ULift.up Polynomial.X) ∉ K.map q := by
    intro hx
    rcases (Ideal.mem_map_iff_of_surjective (I := K) (f := q)
        (Ideal.Quotient.mk_surjective (I := I))).mp hx with ⟨a, ha, hqa⟩
    have hai : a - ULift.up Polynomial.X ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (a - ULift.up Polynomial.X) = 0
      rw [map_sub, hqa, sub_self]
    have hax : ULift.up Polynomial.X ∈ K := by
      have hh := K.sub_mem ha (hIK hai)
      simpa [sub_sub] using hh
    exact hXK hax
  let p : Ideal (A ⧸ I) := K.map q
  have instp : p.IsPrime := hp
  have hx : q (ULift.up (2 : Polynomial (ZMod 4))) ∈ symbolicPower p 2 := by
    change q (ULift.up (2 : Polynomial (ZMod 4))) ∈ RingHom.ker _
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl]
    refine ⟨q (ULift.up Polynomial.X), hqX, ?_⟩
    have hz : q (ULift.up Polynomial.X) *
        q (ULift.up (2 : Polynomial (ZMod 4))) = 0 := by
      rw [← map_mul]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply Ideal.subset_span
      simp [mul_comm]
    rw [hz]
    exact (p ^ 2).zero_mem
  let e0 : Polynomial (ZMod 4) →+* ZMod 4 := Polynomial.evalRingHom 0
  let e : A →+* ULift.{u} (ZMod 4) := e0.ulift
  have hIe : I ≤ RingHom.ker e := by
    rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change e ((ULift.up (2 : Polynomial (ZMod 4))) * ULift.up Polynomial.X) = 0
    rw [map_mul, RingHom.ulift_apply, RingHom.ulift_apply]
    change ULift.up (e0 (2 : Polynomial (ZMod 4)) * e0 Polynomial.X) = 0
    rw [show e0 Polynomial.X = 0 by
      change Polynomial.eval 0 Polynomial.X = 0
      rw [Polynomial.eval_X]]
    simp
    rfl
  let g : (A ⧸ I) →+* ULift.{u} (ZMod 4) := Ideal.Quotient.lift I e hIe
  have hg (a : A) : g (q a) = e a := by
    simpa [g, q] using (Ideal.Quotient.lift_mk I e hIe (a := a))
  have hcast (a : ZMod 4) (ha : a ∈ RingHom.ker c0) :
      ULift.up a ∈ Ideal.span {ULift.up (2 : ZMod 4)} := by
    have ha' : c0 a = 0 := RingHom.mem_ker.mp ha
    fin_cases a
    · exact (Ideal.span {ULift.up (2 : ZMod 4)}).zero_mem
    · have hne : c0 (1 : ZMod 4) ≠ 0 := by decide
      exact False.elim (hne ha')
    · change ULift.up (2 : ZMod 4) ∈ Ideal.span {ULift.up (2 : ZMod 4)}
      exact Ideal.subset_span (by simp)
    · have hne : c0 (3 : ZMod 4) ≠ 0 := by decide
      exact False.elim (hne ha')
  have hcoeff (a : A) (ha : a ∈ K) :
      a.down.coeff 0 ∈ RingHom.ker c0 := by
    have ha0 : a.down ∈ RingHom.ker F0 := by
      have ha' : F a = 0 := RingHom.mem_ker.mp ha
      have ha'' := congrArg ULift.down ha'
      cases a with
      | up a =>
        change F0 a = 0 at ha''
        exact ha''
    have hkeq : RingHom.ker F0 = (RingHom.ker c0).map
        (Polynomial.C : ZMod 4 →+* Polynomial (ZMod 4)) :=
      Polynomial.ker_mapRingHom c0
    rw [hkeq] at ha0
    have hc' : ∀ n : ℕ, a.down.coeff n ∈ RingHom.ker c0 :=
      Ideal.mem_map_C_iff.mp ha0
    specialize hc' 0
    assumption
  have heval (a : A) : e a = ULift.up (a.down.coeff 0) := by
    cases a with
    | up a =>
      change ULift.up (e0 a) = ULift.up (a.coeff 0)
      change ULift.up (Polynomial.eval 0 a) = ULift.up (a.coeff 0)
      rw [Polynomial.coeff_zero_eq_eval_zero]
  have hpg : p.map g ≤ Ideal.span {ULift.up (2 : ZMod 4)} := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    change g y ∈ Ideal.span {ULift.up (2 : ZMod 4)}
    rcases (Ideal.mem_map_iff_of_surjective (I := K) (f := q)
        (Ideal.Quotient.mk_surjective (I := I))).mp hy with ⟨a, ha, hqa⟩
    rw [← hqa, hg, heval]
    exact hcast _ (hcoeff a ha)
  have hspan2 : (Ideal.span {ULift.up (2 : ZMod 4)}) ^ 2 =
      (⊥ : Ideal (ULift.{u} (ZMod 4))) := by
    rw [Ideal.span_singleton_pow]
    have htwo : (ULift.up (2 : ZMod 4)) ^ 2 = 0 := by
      change ULift.up ((2 : ZMod 4) ^ 2) = 0
      have : (2 : ZMod 4) ^ 2 = 0 := by decide
      rw [this]
      rfl
    rw [htwo]
    simp
  have hmap : (p ^ 2).map g ≤
      (⊥ : Ideal (ULift.{u} (ZMod 4))) := by
    rw [Ideal.map_pow]
    calc
      p.map g ^ 2 ≤ (Ideal.span {ULift.up (2 : ZMod 4)}) ^ 2 := by
        rw [pow_two, pow_two]
        exact Ideal.mul_mono hpg hpg
      _ = ⊥ := hspan2
  have hnot : q (ULift.up (2 : Polynomial (ZMod 4))) ∉ p ^ 2 := by
    intro hpow
    have hzmem : g (q (ULift.up (2 : Polynomial (ZMod 4)))) ∈
        (⊥ : Ideal (ULift.{u} (ZMod 4))) := by
      apply hmap
      exact Ideal.mem_map_of_mem g hpow
    change g (q (ULift.up (2 : Polynomial (ZMod 4)))) = 0 at hzmem
    have he2 : e (ULift.up (2 : Polynomial (ZMod 4))) =
        ULift.up (2 : ZMod 4) := by
      change ULift.up (e0 (2 : Polynomial (ZMod 4))) = ULift.up (2 : ZMod 4)
      congr 1
      dsimp [e0]
      norm_num
    have htwo : ULift.up (2 : ZMod 4) = 0 := by
      calc
        ULift.up (2 : ZMod 4) = e (ULift.up (2 : Polynomial (ZMod 4))) := he2.symm
        _ = g (q (ULift.up (2 : Polynomial (ZMod 4)))) :=
          (hg (ULift.up (2 : Polynomial (ZMod 4)))).symm
        _ = 0 := hzmem
    exact (fun hz => by
      have : (2 : ZMod 4) = 0 := ULift.up_injective hz
      exact (by decide : (2 : ZMod 4) ≠ 0) this) htwo
  apply hnot
  rw [h (A ⧸ I) p 2]
  exact hx

/-! ## Associated primes -/

/-- For positive exponent, the symbolic-power quotient has exactly the given
prime ideal as its associated prime. -/
theorem associatedPrimes_symbolicPower
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] {n : ℕ} (hn : 0 < n) :
    _root_.associatedPrimes R (R ⧸ symbolicPower p n) = {p} := by
  have hprimary : (symbolicPower p n).IsPrimary := by
    rw [show symbolicPower p n =
        Ideal.comap (algebraMap R (Localization.AtPrime p))
          ((p ^ n).map (algebraMap R (Localization.AtPrime p))) by
      ext x
      change (Ideal.Quotient.mk ((p ^ n).map (algebraMap R (Localization.AtPrime p))))
          (algebraMap R (Localization.AtPrime p) x) = 0 ↔
        algebraMap R (Localization.AtPrime p) x ∈
          (p ^ n).map (algebraMap R (Localization.AtPrime p))
      rw [Ideal.Quotient.eq_zero_iff_mem]]
    apply Ideal.IsPrimary.comap
    apply Ideal.isPrimary_of_isMaximal_radical
    rw [Ideal.map_pow, Ideal.radical_pow _ (Nat.ne_of_gt hn),
      IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
    rw [(inferInstance : (IsLocalRing.maximalIdeal
      (Localization.AtPrime p)).IsPrime).radical]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hle : symbolicPower p n ≤ p := by
    intro x hx
    rw [← IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p,
      Ideal.mem_under]
    change x ∈ RingHom.ker _ at hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hx
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
    exact (Ideal.map_mono (Ideal.pow_le_self (Nat.ne_of_gt hn))) hx
  have hradical : (symbolicPower p n).radical = p := by
    apply le_antisymm
    · simpa only [(inferInstance : p.IsPrime).radical] using
        (Ideal.radical_mono hle)
    · calc
        p = (p ^ n).radical := by
          rw [Ideal.radical_pow p (Nat.ne_of_gt hn),
            (inferInstance : p.IsPrime).radical]
        _ ≤ (symbolicPower p n).radical :=
          Ideal.radical_mono (pow_le_symbolicPower p n)
  rw [associatedPrimes.eq_singleton_of_isPrimary hprimary, hradical]

/-! ## Flat extension -/

private lemma map_baseChange_rid
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) :
    (I.baseChange B).map (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap =
      (I.map (algebraMap A B) : Ideal B) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  change Submodule.span B _ = Submodule.span B _
  congr 1
  ext x
  simp [Algebra.smul_def]

private noncomputable def idealMapTensorEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) :
    B ⊗[A] I ≃ₗ[B] I.map (algebraMap A B) :=
  (Submodule.toBaseChange.toLinearEquiv B I).trans
    ((TensorProduct.AlgebraTensorModule.rid A B B).ofSubmodules _ _ (map_baseChange_rid I))

private noncomputable def powerLayerBaseChangeEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) (i : ℕ) :
    B ⊗[A] ((I ^ i : Ideal A) ⧸
        (I • (⊤ : Submodule A (I ^ i : Ideal A)))) ≃ₗ[B]
      ((I ^ i).map (algebraMap A B) ⧸
        (I.map (algebraMap A B) •
          (⊤ : Submodule B ((I ^ i).map (algebraMap A B))))) :=
  (TensorProduct.tensorQuotMapSMulEquivTensorQuot
      (I ^ i : Ideal A) B I).symm.trans
    (Submodule.Quotient.equiv _ _ (idealMapTensorEquiv (I ^ i)) (by
      simp [Submodule.map_smul'']))

private noncomputable def powerLayerResidueEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) (i : ℕ) :
    (B ⧸ I.map (algebraMap A B)) ⊗[A ⧸ I]
        ((I ^ i : Ideal A) ⧸
          (I • (⊤ : Submodule A (I ^ i : Ideal A)))) ≃ₗ[B ⧸ I.map (algebraMap A B)]
      ((I ^ i).map (algebraMap A B) ⧸
        (I.map (algebraMap A B) •
          (⊤ : Submodule B ((I ^ i).map (algebraMap A B))))) := by
  let hV := Module.isTorsionBySet_quotient_ideal_smul (I ^ i : Ideal A) I
  letI : Module (A ⧸ I)
      ((I ^ i : Ideal A) ⧸ (I • (⊤ : Submodule A (I ^ i : Ideal A)))) := hV.module
  letI : IsScalarTower A (A ⧸ I)
      ((I ^ i : Ideal A) ⧸ (I • (⊤ : Submodule A (I ^ i : Ideal A)))) :=
    hV.isScalarTower
  let hW := Module.isTorsionBySet_quotient_ideal_smul
    ((I ^ i).map (algebraMap A B)) (I.map (algebraMap A B))
  letI : Module (B ⧸ I.map (algebraMap A B))
      ((I ^ i).map (algebraMap A B) ⧸
        (I.map (algebraMap A B) •
          (⊤ : Submodule B ((I ^ i).map (algebraMap A B))))) := hW.module
  letI : IsScalarTower B (B ⧸ I.map (algebraMap A B))
      ((I ^ i).map (algebraMap A B) ⧸
        (I.map (algebraMap A B) •
          (⊤ : Submodule B ((I ^ i).map (algebraMap A B))))) :=
    hW.isScalarTower
  letI : TensorProduct.CompatibleSMul A (A ⧸ I)
      (B ⧸ I.map (algebraMap A B))
      ((I ^ i : Ideal A) ⧸ (I • (⊤ : Submodule A (I ^ i : Ideal A)))) :=
    ⟨fun k c v => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective k
      change (a • c) ⊗ₜ[A] v = c ⊗ₜ[A] (a • v)
      exact TensorProduct.smul_tmul _ _ _⟩
  letI : TensorProduct.CompatibleSMul B (B ⧸ I.map (algebraMap A B))
      (B ⧸ I.map (algebraMap A B))
      ((I ^ i).map (algebraMap A B) ⧸
        (I.map (algebraMap A B) •
          (⊤ : Submodule B ((I ^ i).map (algebraMap A B))))) :=
    ⟨fun c x w => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
      change (b • x) ⊗ₜ[B] w = x ⊗ₜ[B] (b • w)
      exact TensorProduct.smul_tmul _ _ _⟩
  let e₁ := TensorProduct.equivOfCompatibleSMul A (A ⧸ I)
      (B ⧸ I.map (algebraMap A B)) (B ⧸ I.map (algebraMap A B))
      ((I ^ i : Ideal A) ⧸ (I • (⊤ : Submodule A (I ^ i : Ideal A))))
  let e₂ := (TensorProduct.AlgebraTensorModule.cancelBaseChange A B
      (B ⧸ I.map (algebraMap A B)) (B ⧸ I.map (algebraMap A B))
      ((I ^ i : Ideal A) ⧸
        (I • (⊤ : Submodule A (I ^ i : Ideal A))))).symm
  let e₃ := (powerLayerBaseChangeEquiv I i).baseChange B
    (B ⧸ I.map (algebraMap A B)) _ _
  let e₄ := (TensorProduct.equivOfCompatibleSMul B
    (B ⧸ I.map (algebraMap A B)) (B ⧸ I.map (algebraMap A B))
    (B ⧸ I.map (algebraMap A B))
    ((I ^ i).map (algebraMap A B) ⧸
      (I.map (algebraMap A B) •
        (⊤ : Submodule B ((I ^ i).map (algebraMap A B)))))).symm
  let e₅ := TensorProduct.lid (B ⧸ I.map (algebraMap A B))
    ((I ^ i).map (algebraMap A B) ⧸
      (I.map (algebraMap A B) •
        (⊤ : Submodule B ((I ^ i).map (algebraMap A B)))))
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

private theorem isSMulRegular_powerLayer_map_of_flat
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) [I.IsMaximal]
    [(I.map (algebraMap A B)).IsPrime] (i : ℕ) {r : B}
    (hr : r ∉ I.map (algebraMap A B)) :
    IsSMulRegular
      ((I ^ i).map (algebraMap A B) ⧸
        (I.map (algebraMap A B) •
          (⊤ : Submodule B ((I ^ i).map (algebraMap A B))))) r := by
  let := Ideal.Quotient.field I
  let hV := Module.isTorsionBySet_quotient_ideal_smul (I ^ i : Ideal A) I
  let : Module (A ⧸ I)
      ((I ^ i : Ideal A) ⧸ (I • (⊤ : Submodule A (I ^ i : Ideal A)))) := hV.module
  let : IsScalarTower A (A ⧸ I)
      ((I ^ i : Ideal A) ⧸ (I • (⊤ : Submodule A (I ^ i : Ideal A)))) :=
    hV.isScalarTower
  let hW := Module.isTorsionBySet_quotient_ideal_smul
    ((I ^ i).map (algebraMap A B)) (I.map (algebraMap A B))
  let : Module (B ⧸ I.map (algebraMap A B))
      ((I ^ i).map (algebraMap A B) ⧸
        (I.map (algebraMap A B) •
          (⊤ : Submodule B ((I ^ i).map (algebraMap A B))))) := hW.module
  let : IsScalarTower B (B ⧸ I.map (algebraMap A B))
      ((I ^ i).map (algebraMap A B) ⧸
        (I.map (algebraMap A B) •
          (⊤ : Submodule B ((I ^ i).map (algebraMap A B))))) :=
    hW.isScalarTower
  have hr' : Ideal.Quotient.mk (I.map (algebraMap A B)) r ≠ 0 := by
    intro hzero
    exact hr (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hsource : IsSMulRegular
      ((B ⧸ I.map (algebraMap A B)) ⊗[A ⧸ I]
        ((I ^ i : Ideal A) ⧸
          (I • (⊤ : Submodule A (I ^ i : Ideal A)))))
      (Ideal.Quotient.mk (I.map (algebraMap A B)) r) :=
    Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero hr')
  have htarget : IsSMulRegular
      ((I ^ i).map (algebraMap A B) ⧸
        (I.map (algebraMap A B) •
          (⊤ : Submodule B ((I ^ i).map (algebraMap A B)))))
      (Ideal.Quotient.mk (I.map (algebraMap A B)) r) :=
    ((powerLayerResidueEquiv I i).isSMulRegular_congr _).mp hsource
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  apply htarget.right_eq_zero_of_smul
  simpa only [Module.IsTorsionBySet.mk_smul hW] using hx

private theorem isSMulRegular_quotient_pow_of_isSMulRegular_layers
    {A : Type*} [CommRing A] (I : Ideal A) (r : A) (n : ℕ)
    (h : ∀ i < n,
      IsSMulRegular
        ((I ^ i : Ideal A) ⧸ (I • (⊤ : Submodule A (I ^ i : Ideal A)))) r) :
    IsSMulRegular (A ⧸ I ^ n) r := by
  induction n with
  | zero =>
      rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
      intro x _
      simp
  | succ n ih =>
      rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
      intro x hx
      have hxn : x ∈ I ^ n := by
        apply mem_of_isSMulRegular_quotient_of_smul_mem (ih fun i hi => h i (hi.trans n.lt_succ_self))
        exact (Ideal.pow_le_pow_right n.le_succ) hx
      let y : (I ^ n : Ideal A) := ⟨x, hxn⟩
      have hy : r • y ∈ I • (⊤ : Submodule A (I ^ n : Ideal A)) := by
        rw [Submodule.mem_smul_top_iff]
        simpa [y, Ideal.smul_eq_mul, pow_succ'] using hx
      have := mem_of_isSMulRegular_quotient_of_smul_mem (h n n.lt_succ_self) hy
      rw [Submodule.mem_smul_top_iff] at this
      simpa [y, Ideal.smul_eq_mul, pow_succ'] using this

private theorem isSMulRegular_quotient_pow_map_of_flat
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) [I.IsMaximal]
    [(I.map (algebraMap A B)).IsPrime] (n : ℕ) {r : B}
    (hr : r ∉ I.map (algebraMap A B)) :
    IsSMulRegular (B ⧸ (I.map (algebraMap A B)) ^ n) r := by
  apply isSMulRegular_quotient_pow_of_isSMulRegular_layers
  intro i _
  rw [← I.map_pow (algebraMap A B) i]
  exact isSMulRegular_powerLayer_map_of_flat I i hr

private theorem isSMulRegular_symbolicPower_quotient
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsPrime]
    (n : ℕ) {r : A} (hr : r ∉ I) :
    IsSMulRegular (A ⧸ symbolicPower I n) r := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro x hx
  change r * x ∈ RingHom.ker _ at hx
  rw [RingHom.mem_ker, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem] at hx
  change x ∈ RingHom.ker _
  rw [RingHom.mem_ker, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem]
  rw [map_mul] at hx
  have hrM : r ∈ I.primeCompl := hr
  exact (Ideal.unit_mul_mem_iff_mem _
    (IsLocalization.map_units (Localization.AtPrime I) ⟨r, hrM⟩)).mp hx

private theorem isSMulRegular_quotient_map_of_flat
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) {r : A}
    (hr : IsSMulRegular (A ⧸ I) r) :
    IsSMulRegular (B ⧸ I.map (algebraMap A B)) (algebraMap A B r) := by
  have hTensorR : IsSMulRegular (B ⊗[A] (A ⧸ I)) r := hr.lTensor B
  have hTensorB : IsSMulRegular (B ⊗[A] (A ⧸ I)) (algebraMap A B r) := by
    exact (isSMulRegular_map (M := B ⊗[A] (A ⧸ I)) (a := r)
      (algebraMap A B) (fun x => IsScalarTower.algebraMap_smul B r x)).mpr hTensorR
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv
  exact (e.isSMulRegular_congr (algebraMap A B r)).mpr hTensorB

private theorem comap_map_eq_self_of_flat_of_isPrime_map
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) [I.IsPrime]
    [(I.map (algebraMap A B)).IsPrime] :
    (I.map (algebraMap A B)).comap (algebraMap A B) = I := by
  apply le_antisymm
  · intro r hr
    by_contra hrI
    have hregA : IsSMulRegular (A ⧸ I) r := by
      rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
      intro x hx
      exact ((inferInstance : I.IsPrime).mem_or_mem hx).resolve_left hrI
    have hregB := isSMulRegular_quotient_map_of_flat (B := B) I hregA
    have hzero : algebraMap A B r •
        (1 : B ⧸ I.map (algebraMap A B)) = 0 := by
      rw [Algebra.smul_def, mul_one]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
    exact one_ne_zero (hregB.right_eq_zero_of_smul hzero)
  · exact Ideal.le_comap_map

/-- Symbolic powers commute with a flat extension when the extended prime is
prime.  The displayed equality is the source's `q = pS` case, with `q`
retained as an explicit ideal to make the primality hypothesis available. -/
theorem symbolicPower_map_of_flat
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hflat : RingHom.Flat f)
    (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] (hq : q = p.map f) (n : ℕ) :
    (symbolicPower p n).map f = symbolicPower q n := by
  subst q
  algebraize [f]
  have hpcomap : (p.map (algebraMap R S)).comap (algebraMap R S) = p :=
    comap_map_eq_self_of_flat_of_isPrime_map p
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rcases (mem_symbolicPower_iff p n x).mp hx with ⟨r, hr, hrx⟩
    apply (mem_symbolicPower_iff (p.map (algebraMap R S)) n _).mpr
    refine ⟨algebraMap R S r, ?_, ?_⟩
    · intro hfr
      apply hr
      rw [← hpcomap]
      exact hfr
    · simpa only [RingHom.algebraMap_toAlgebra, map_mul, p.map_pow] using
        (Ideal.mem_map_of_mem f hrx)
  · intro x hx
    rcases (mem_symbolicPower_iff (p.map (algebraMap R S)) n x).mp hx with
      ⟨s, hs, hsx⟩
    let Rp := Localization.AtPrime p
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    let P : Ideal S := p.map (algebraMap R S)
    let m : Ideal Rp := p.map (algebraMap R Rp)
    let Q : Ideal Sp := P.map (algebraMap S Sp)
    let : P.LiesOver p := ⟨hpcomap.symm⟩
    have hQprime : Q.IsPrime := by
      dsimp only [Q]
      exact IsLocalization.AtPrime.isPrime_map_of_liesOver S p Sp P
    have hQeq : m.map (algebraMap Rp Sp) = Q := by
      dsimp only [m, Q, P]
      rw [Ideal.map_map, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq R Rp Sp,
        ← IsScalarTower.algebraMap_eq R S Sp]
    let : m.IsMaximal := by
      dsimp only [m]
      infer_instance
    let : (m.map (algebraMap Rp Sp)).IsPrime := hQeq ▸ hQprime
    have hsSp : algebraMap S Sp s ∉ m.map (algebraMap Rp Sp) := by
      rw [hQeq]
      intro hsQ
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Algebra.algebraMapSubmonoid S p.primeCompl)] at hsQ
      rcases hsQ with ⟨t, ht, hts⟩
      have htP : t ∉ P := by
        rcases ht with ⟨r, hr, rfl⟩
        intro hfr
        exact hr (hpcomap ▸ hfr)
      exact hs ((inferInstance : P.IsPrime).mem_or_mem hts |>.resolve_left htP)
    have hsreg : IsSMulRegular
        (Sp ⧸ (m.map (algebraMap Rp Sp)) ^ n) (algebraMap S Sp s) :=
      isSMulRegular_quotient_pow_map_of_flat m n hsSp
    have hsxSp : algebraMap S Sp (s * x) ∈
        (m.map (algebraMap Rp Sp)) ^ n := by
      rw [hQeq, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (algebraMap S Sp) hsx
    have hxSp : algebraMap S Sp x ∈ (m.map (algebraMap Rp Sp)) ^ n := by
      apply mem_of_isSMulRegular_quotient_of_smul_mem hsreg
      change algebraMap S Sp s * algebraMap S Sp x ∈
        (m.map (algebraMap Rp Sp)) ^ n
      simpa only [map_mul] using hsxSp
    have hxSp' : algebraMap S Sp x ∈ (P ^ n).map (algebraMap S Sp) := by
      rw [Ideal.map_pow]
      change algebraMap S Sp x ∈ Q ^ n
      rw [← hQeq]
      exact hxSp
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl)] at hxSp'
    rcases hxSp' with ⟨t, ht, htx⟩
    rcases ht with ⟨r, hr, rfl⟩
    have hregS : IsSMulRegular
        (S ⧸ (symbolicPower p n).map (algebraMap R S)) (algebraMap R S r) :=
      isSMulRegular_quotient_map_of_flat (symbolicPower p n)
        (isSMulRegular_symbolicPower_quotient p n hr)
    apply mem_of_isSMulRegular_quotient_of_smul_mem hregS
    rw [Algebra.smul_def]
    apply Ideal.map_mono (pow_le_symbolicPower p n)
    rw [p.map_pow (algebraMap R S) n]
    exact htx

/- Unfolding `RingHom.ker` and `Ideal.Quotient.mk` gives the source's
`R ∩ p ^ n Rₚ` kernel description, so it needs no parallel intersection
definition.  The associated-prime proof also uses the fact that elements
outside `p` act regularly on the quotient.  The flat-extension proof reduces
to injectivity of the map between the two localized quotients, observes that
the target is a further localization, and uses the finite filtration by
powers of `p` with the displayed tensor-product/vector-space subquotients;
these are proof-level reductions and introduce no additional chapter-facing
construction. -/

end

end Formalization.Books.Algebra.Unit64
