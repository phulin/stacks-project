import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Exercises, Chapter 5: Flat ring maps

This file records the three flat-deformation exercises.  The dual-number
construction uses Mathlib's canonical `DualNumber`; the polynomial quotients
and special fibres use the canonical ideal-quotient and `ZMod` APIs.
-/

noncomputable section

universe u v

namespace Formalization.Books.Exercises.Unit05

open scoped TensorProduct

/-! ## Dual-number deformations -/

/-- Mathlib's canonical implementation of the ring `k[ε] = k[x]/(x²)`. -/
abbrev dualNumberRing (k : Type u) [Field k] := DualNumber k

/-- The dual-number element `ε`. -/
def dualNumberEpsilon (k : Type u) [Field k] : dualNumberRing k :=
  DualNumber.eps

/-- The ideal `εB` in a `k[ε]`-algebra `B`. -/
def dualNumberIdeal
    (k B : Type u) [Field k] [CommRing B]
    [Algebra (dualNumberRing k) B] : Ideal B :=
  Ideal.span {algebraMap (dualNumberRing k) B (dualNumberEpsilon k)}

/-- The special fibre `B/εB`. -/
abbrev dualNumberSpecialFiber
    (k B : Type u) [Field k] [CommRing B]
    [Algebra (dualNumberRing k) B] [Algebra k B] :=
  B ⧸ dualNumberIdeal k B

/-- A flat `k[ε]`-deformation of a `k`-algebra `A`. -/
def IsFlatDualNumberDeformation
    (k A B : Type u) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra (dualNumberRing k) B] [Algebra k B]
    [IsScalarTower k (dualNumberRing k) B] : Prop :=
  Module.Flat (dualNumberRing k) B ∧
    Nonempty (A ≃ₐ[k] dualNumberSpecialFiber k B)

/-- The canonical base-change deformation `A ⊗[k] k[ε]`. -/
abbrev dualNumberBaseChange
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] :=
  A ⊗[k] dualNumberRing k

/-- The `k[ε]`-algebra structure on the canonical base-change deformation. -/
@[instance_reducible] noncomputable def dualNumberBaseChangeAlgebra
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    Algebra (dualNumberRing k) (dualNumberBaseChange k A) :=
  Algebra.TensorProduct.rightAlgebra

/-- The base-change construction is a flat deformation with special fibre `A`.
-/
theorem dualNumber_baseChange_is_deformation
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    letI : Algebra (dualNumberRing k) (dualNumberBaseChange k A) :=
      dualNumberBaseChangeAlgebra k A
    IsFlatDualNumberDeformation k A (dualNumberBaseChange k A) := by
  refine (letI : Algebra (dualNumberRing k) (dualNumberBaseChange k A) :=
    dualNumberBaseChangeAlgebra k A; ?_)
  dsimp only [IsFlatDualNumberDeformation]
  constructor
  · refine (letI : Module.Free k A := Module.Free.of_divisionRing k A; ?_)
    refine (letI : Module.Flat k A := Module.Flat.of_free; ?_)
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight k (dualNumberRing k) A).symm.toLinearEquiv
  · let Iε : Ideal (dualNumberRing k) := Ideal.span {dualNumberEpsilon k}
    let f : dualNumberRing k →ₐ[k] k := TrivSqZeroExt.fstHom k k k
    have hf : Function.Surjective f := by
      intro a
      exact ⟨TrivSqZeroExt.inl a, by simp [f]⟩
    have hker : Iε = RingHom.ker f := by
      ext x
      constructor
      · intro hx
        rcases Ideal.mem_span_singleton'.mp hx with ⟨a, ha⟩
        rw [← ha]
        change TrivSqZeroExt.fst (a * TrivSqZeroExt.inr (1 : k)) = 0
        rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inr, mul_zero]
      · intro hx
        change x.1 = 0 at hx
        refine Ideal.mem_span_singleton'.mpr
          ⟨TrivSqZeroExt.inl (TrivSqZeroExt.snd x), ?_⟩
        apply TrivSqZeroExt.ext
        · change TrivSqZeroExt.fst
            (TrivSqZeroExt.inl (TrivSqZeroExt.snd x) * TrivSqZeroExt.inr (1 : k)) =
              TrivSqZeroExt.fst x
          rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inr, mul_zero]
          exact hx.symm
        · simp [dualNumberEpsilon]
    have hmap :
        (RingHom.ker f).map
            (Algebra.TensorProduct.includeRight :
              dualNumberRing k →ₐ[k] dualNumberBaseChange k A) =
          dualNumberIdeal k (dualNumberBaseChange k A) := by
      rw [← hker]
      change (Ideal.map
          (Algebra.TensorProduct.includeRight :
            dualNumberRing k →ₐ[k] dualNumberBaseChange k A)
          (Ideal.span {dualNumberEpsilon k})) =
        Ideal.span {(algebraMap (dualNumberRing k) (dualNumberBaseChange k A))
          (dualNumberEpsilon k)}
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    let q : (dualNumberRing k ⧸ RingHom.ker f) ≃ₐ[k] k :=
      Ideal.quotientKerAlgEquivOfSurjective hf
    let e₀ : A ≃ₐ[k] A ⊗[k] k :=
      (Algebra.TensorProduct.rid k k A).symm
    let e₁ : A ⊗[k] k ≃ₐ[k]
        A ⊗[k] (dualNumberRing k ⧸ RingHom.ker f) :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k] A) q.symm
    refine (letI : CommRing (dualNumberBaseChange k A) := inferInstance; ?_)
    let e₂ : A ⊗[k] (dualNumberRing k ⧸ RingHom.ker f) ≃ₐ[k]
        (dualNumberBaseChange k A) ⧸
          (RingHom.ker f).map
            (Algebra.TensorProduct.includeRight :
              dualNumberRing k →ₐ[k] dualNumberBaseChange k A) :=
      Algebra.TensorProduct.tensorQuotientEquiv k (dualNumberRing k) A (RingHom.ker f)
    exact ⟨e₀.trans (e₁.trans (e₂.trans (Ideal.quotientEquivAlgOfEq k hmap)))⟩

/-! ## Polynomial lifts from `ℤ/p²ℤ` -/

/-- The quotient by the ideal generated by a scalar `r`; this is the source's
notation `B/rB`. -/
abbrev principalSpecialFiber
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B] (r : R) : Type v :=
  B ⧸ Ideal.span {algebraMap R B r}

/-- The ideal `(x₁^p, …, x₆^p)` in a six-variable polynomial ring. -/
def sixVariablePowerIdeal
    (p : ℕ) (R : Type u) [CommRing R] :
    Ideal (MvPolynomial (Fin 6) R) :=
  Ideal.span (Set.range (fun i : Fin 6 => (MvPolynomial.X i : MvPolynomial (Fin 6) R) ^ p))

/-- The characteristic-`p` algebra in the second deformation exercise. -/
abbrev sixVariablePowerAlgebra (p : ℕ) :=
  MvPolynomial (Fin 6) (ZMod p) ⧸ sixVariablePowerIdeal p (ZMod p)

/-- The evident lift of the characteristic-`p` algebra to `ℤ/p²ℤ`. -/
abbrev sixVariablePowerLift (p : ℕ) :=
  MvPolynomial (Fin 6) (ZMod (p ^ 2)) ⧸
    sixVariablePowerIdeal p (ZMod (p ^ 2))

/-- The special fibre of the evident lift. -/
abbrev sixVariablePowerLiftSpecialFiber (p : ℕ) :=
  principalSpecialFiber (R := ZMod (p ^ 2)) (B := sixVariablePowerLift p)
    (p : ZMod (p ^ 2))

/-- The displayed polynomial lift is flat over `ℤ/p²ℤ`. -/
theorem sixVariablePowerLift_flat (p : ℕ) (_hp : Nat.Prime p) :
    Module.Flat (ZMod (p ^ 2)) (sixVariablePowerLift p) := by
  let R := ZMod (p ^ 2)
  change Module.Flat R
    (MvPolynomial (Fin 6) R ⧸ sixVariablePowerIdeal p R)
  let red : MvPolynomial (Fin 6) R →ₗ[R] MvPolynomial (Fin 6) R :=
    { toFun := fun q =>
        ⟨Finsupp.filter (fun m : Fin 6 →₀ ℕ => ∀ i : Fin 6, m i < p)
            (AddMonoidAlgebra.coeff q)⟩
      map_add' := by
        intro q r
        ext m
        by_cases hm : ∀ i : Fin 6, m i < p <;>
          simp
      map_smul' := by
        intro a q
        ext m
        by_cases hm : ∀ i : Fin 6, m i < p <;>
          simp }
  have hgen :
      Ideal.span
          ((fun m : Fin 6 →₀ ℕ => MvPolynomial.monomial m (1 : R)) ''
            Set.range (fun i : Fin 6 => Finsupp.single i p)) =
        sixVariablePowerIdeal p R := by
    unfold sixVariablePowerIdeal
    apply congrArg Ideal.span
    ext z
    constructor
    · rintro ⟨m, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp [MvPolynomial.X, MvPolynomial.monomial]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Finsupp.single i p, ⟨i, rfl⟩, by
        simp [MvPolynomial.X, MvPolynomial.monomial]⟩
  have hker : LinearMap.ker red = (sixVariablePowerIdeal p R).restrictScalars R := by
    ext q
    change red q = 0 ↔ q ∈ sixVariablePowerIdeal p R
    rw [← hgen, MvPolynomial.mem_ideal_span_monomial_image]
    constructor
    · intro hq xi hxi
      by_contra hno
      push Not at hno
      have hgood : ∀ i : Fin 6, xi i < p := by
        intro i
        exact Nat.lt_of_not_ge (fun hpi =>
          hno (Finsupp.single i p) ⟨i, rfl⟩ (Finsupp.single_le_iff.mpr hpi))
      have hcoeff : (AddMonoidAlgebra.coeff q) xi = 0 := by
        have hcoeff' := congrArg (fun z => MvPolynomial.coeff xi z) hq
        change (Finsupp.filter
          (fun m : Fin 6 →₀ ℕ => ∀ i : Fin 6, m i < p)
          (AddMonoidAlgebra.coeff q)) xi = 0 at hcoeff'
        simpa [Finsupp.filter_apply, hgood] using hcoeff'
      exact (MvPolynomial.mem_support_iff.mp hxi) hcoeff
    · intro hq
      ext xi
      by_cases hgood : ∀ i : Fin 6, xi i < p
      · have hcoeff : (AddMonoidAlgebra.coeff q) xi = 0 := by
          by_contra hcoeff
          have hxi : xi ∈ q.support := MvPolynomial.mem_support_iff.mpr hcoeff
          rcases hq xi hxi with ⟨s, ⟨i, rfl⟩, hle⟩
          exact Nat.not_le_of_lt (hgood i) (Finsupp.single_le_iff.mp hle)
        change (Finsupp.filter
          (fun m : Fin 6 →₀ ℕ => ∀ i : Fin 6, m i < p)
          (AddMonoidAlgebra.coeff q)) xi = 0
        simp [hgood, hcoeff]
      · change (Finsupp.filter
          (fun m : Fin 6 →₀ ℕ => ∀ i : Fin 6, m i < p)
          (AddMonoidAlgebra.coeff q)) xi = 0
        simp [hgood]
  let red' : MvPolynomial (Fin 6) R →ₗ[R] LinearMap.range red :=
    red.codRestrict (LinearMap.range red) (fun q => ⟨q, rfl⟩)
  have hred_surj : Function.Surjective red' := by
    rintro ⟨x, ⟨q, rfl⟩⟩
    exact ⟨q, rfl⟩
  have hker' : LinearMap.ker red' = (sixVariablePowerIdeal p R).restrictScalars R := by
    ext q
    constructor
    · intro hq
      have hredq : red q = 0 := by
        have hq' := congrArg Subtype.val hq
        change red q = 0 at hq'
        exact hq'
      have hqker : q ∈ LinearMap.ker red := hredq
      rw [hker] at hqker
      exact hqker
    · intro hq
      have hredq : red q = 0 := by
        have hqker : q ∈ LinearMap.ker red := by
          rw [hker]
          exact hq
        exact hqker
      apply Subtype.ext
      exact hredq
  have hred_idem : red.comp red = red := by
    apply LinearMap.ext
    intro q
    apply AddMonoidAlgebra.ext
    ext m
    change (Finsupp.filter
      (fun m : Fin 6 →₀ ℕ => ∀ i : Fin 6, m i < p)
      (Finsupp.filter
        (fun m : Fin 6 →₀ ℕ => ∀ i : Fin 6, m i < p)
        (AddMonoidAlgebra.coeff q))) m =
      (Finsupp.filter
        (fun m : Fin 6 →₀ ℕ => ∀ i : Fin 6, m i < p)
        (AddMonoidAlgebra.coeff q)) m
    by_cases hm : ∀ i : Fin 6, m i < p <;>
      simp [hm]
  let r : MvPolynomial (Fin 6) R →ₗ[R] LinearMap.range red := red'
  have hri : r.comp (LinearMap.range red).subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, ⟨q, hq⟩⟩
    apply Subtype.ext
    change red x = x
    rw [← hq]
    simpa [LinearMap.comp_apply] using congrArg (fun f => f q) hred_idem
  refine (letI : Module.Flat R (LinearMap.range red) :=
    Module.Flat.of_retract (LinearMap.range red).subtype r hri; ?_)
  let equot :
      (MvPolynomial (Fin 6) R ⧸ (sixVariablePowerIdeal p R).restrictScalars R) ≃ₗ[R]
        LinearMap.range red :=
    (Submodule.quotEquivOfEq _ _ hker'.symm).trans
      (r.quotKerEquivOfSurjective hred_surj)
  exact Module.Flat.of_linearEquiv equot

/-- Its reduction modulo `p` is the characteristic-`p` algebra in the source.
-/
theorem sixVariablePowerLift_specialFiber (p : ℕ) :
    Nonempty (sixVariablePowerLiftSpecialFiber p ≃+* sixVariablePowerAlgebra p) := by
  let R₂ := ZMod (p ^ 2)
  let R₁ := ZMod p
  let P₂ := MvPolynomial (Fin 6) R₂
  let P₁ := MvPolynomial (Fin 6) R₁
  let I₂ : Ideal P₂ := sixVariablePowerIdeal p R₂
  let I₁ : Ideal P₁ := sixVariablePowerIdeal p R₁
  let J : Ideal P₂ := Ideal.span {algebraMap R₂ P₂ (p : R₂)}
  have hp2 : p ∣ p ^ 2 := by
    exact ⟨p, by ring⟩
  let c : R₂ →+* R₁ := ZMod.castHom hp2 R₁
  let f : P₂ →+* P₁ := MvPolynomial.map c
  have hc : ∀ a : R₂, c a = 0 ↔ (p : R₂) ∣ a := by
    intro a
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
    constructor
    · intro hz
      have hz0 : (z : R₁) = 0 := by
        rw [← ZMod.cast_intCast hp2 z]
        exact hz
      have hz' : (p : ℤ) ∣ z := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hz0
      obtain ⟨k, hk⟩ := hz'
      refine ⟨(k : R₂), ?_⟩
      simp [hk]
    · rintro ⟨a, ha⟩
      rw [ha, map_mul]
      have cp : c (p : R₂) = 0 := by
        change ZMod.cast (p : ZMod (p ^ 2)) = 0
        rw [ZMod.cast_natCast hp2]
        exact (ZMod.natCast_eq_zero_iff p p).2 dvd_rfl
      rw [cp, zero_mul]
  have hker : RingHom.ker f = J := by
    ext q
    rw [RingHom.mem_ker]
    rw [← MvPolynomial.C_dvd_iff_map_hom_eq_zero c (p : R₂) hc q]
    change MvPolynomial.C (p : R₂) ∣ q ↔
      q ∈ Ideal.span {MvPolynomial.C (p : R₂)}
    rw [Ideal.mem_span_singleton]
  have hf : Function.Surjective f := by
    exact MvPolynomial.map_surjective c (ZMod.castHom_surjective hp2)
  have hI_map : Ideal.map f I₂ = I₁ := by
    unfold I₂ I₁ sixVariablePowerIdeal
    rw [Ideal.map_span]
    apply congrArg Ideal.span
    ext q
    constructor
    · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      dsimp [f]
      rw [map_pow, MvPolynomial.map_X]
    · rintro ⟨i, rfl⟩
      refine ⟨(MvPolynomial.X i : P₂) ^ p, ⟨i, rfl⟩, ?_⟩
      dsimp [f]
      rw [map_pow, MvPolynomial.map_X]
  let e₀ : (P₂ ⧸ RingHom.ker f) ≃+* P₁ :=
    f.quotientKerEquivOfSurjective hf
  let e : (P₂ ⧸ J) ≃+* P₁ :=
    (Ideal.quotEquivOfEq hker.symm).trans e₀
  have hecomp : (e : (P₂ ⧸ J) →+* P₁).comp (Ideal.Quotient.mk J) = f := by
    apply RingHom.ext
    intro x
    simp [e, e₀]
  have hmap : I₁ = Ideal.map (e : (P₂ ⧸ J) →+* P₁)
      (Ideal.map (Ideal.Quotient.mk J) I₂) := by
    calc
      I₁ = Ideal.map f I₂ := hI_map.symm
      _ = Ideal.map ((e : (P₂ ⧸ J) →+* P₁).comp
          (Ideal.Quotient.mk J)) I₂ := by rw [hecomp]
      _ = Ideal.map (e : (P₂ ⧸ J) →+* P₁)
          (Ideal.map (Ideal.Quotient.mk J) I₂) :=
        (Ideal.map_map _ _).symm
  have hJmap : Ideal.map (Ideal.Quotient.mk I₂) J =
      Ideal.span {algebraMap R₂ (P₂ ⧸ I₂) (p : R₂)} := by
    change Ideal.map (Ideal.Quotient.mk I₂)
        (Ideal.span {algebraMap R₂ P₂ (p : R₂)}) = _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let e' : (P₂ ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) I₂ ≃+* P₁ ⧸ I₁ :=
    Ideal.quotientEquiv (Ideal.map (Ideal.Quotient.mk J) I₂) I₁ e hmap
  exact ⟨(Ideal.quotEquivOfEq hJmap.symm).trans
      ((DoubleQuot.quotQuotEquivComm I₂ J).trans e')⟩

/-- The second exercise supplies a flat `ℤ/p²ℤ`-algebra lifting the displayed
characteristic-`p` algebra. -/
theorem exists_flat_zmodSquare_lift (p : ℕ) (_hp : Nat.Prime p) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra (ZMod (p ^ 2)) B),
      Module.Flat (ZMod (p ^ 2)) B ∧
        Nonempty
          (principalSpecialFiber (R := ZMod (p ^ 2)) (B := B) (p : ZMod (p ^ 2))
            ≃+* sixVariablePowerAlgebra p) := by
  refine ⟨sixVariablePowerLift p, inferInstance, inferInstance, ?_⟩
  exact ⟨sixVariablePowerLift_flat p _hp, sixVariablePowerLift_specialFiber p⟩

/-! ## The quadratic obstruction -/

/-- The six-variable quadratic relation from the third deformation exercise.
-/
def sixVariableQuadratic (R : Type u) [CommRing R] : MvPolynomial (Fin 6) R :=
  MvPolynomial.X (0 : Fin 6) * MvPolynomial.X (1 : Fin 6) +
    MvPolynomial.X (2 : Fin 6) * MvPolynomial.X (3 : Fin 6) +
      MvPolynomial.X (4 : Fin 6) * MvPolynomial.X (5 : Fin 6)

/-- The ideal `(x₁^p,…,x₆^p,x₁x₂+x₃x₄+x₅x₆)`. -/
def sixVariableQuadraticIdeal
    (p : ℕ) (R : Type u) [CommRing R] :
    Ideal (MvPolynomial (Fin 6) R) :=
  Ideal.span
    (Set.range (fun i : Fin 6 => (MvPolynomial.X i : MvPolynomial (Fin 6) R) ^ p) ∪
      {sixVariableQuadratic R})

/-- The characteristic-`p` algebra with the quadratic relation. -/
abbrev sixVariableQuadraticAlgebra (p : ℕ) :=
  MvPolynomial (Fin 6) (ZMod p) ⧸ sixVariableQuadraticIdeal p (ZMod p)

/-- No flat `ℤ/p²ℤ`-algebra has the quadratic algebra above as its special
fibre. -/
theorem no_flat_sixVariableQuadratic_lift
    (p : ℕ) (hp : Nat.Prime p) :
    ¬ ∃ (B : Type) (_ : CommRing B) (_ : Algebra (ZMod (p ^ 2)) B),
      Module.Flat (ZMod (p ^ 2)) B ∧
        Nonempty
          (principalSpecialFiber (R := ZMod (p ^ 2)) (B := B) (p : ZMod (p ^ 2))
            ≃+* sixVariableQuadraticAlgebra p) := by
  rintro ⟨B, _, _, hflat, ⟨e⟩⟩
  let R := ZMod (p ^ 2)
  let K : Ideal B := Ideal.span {algebraMap R B (p : R)}
  let π : B →+* (B ⧸ K) := Ideal.Quotient.mk K
  let : Module.Flat R B := hflat
  have hscalar : ∀ a : R, (p : R) * a = 0 →
      ∃ c : R, a = (p : R) * c := by
    intro a ha
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
    have hzdiv : (p ^ 2 : ℤ) ∣ (p : ℤ) * z := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      rw [Int.cast_mul]
      simpa using ha
    obtain ⟨k, hk⟩ := hzdiv
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hz : z = (p : ℤ) * k := by
      apply (mul_left_cancel₀ hpz)
      calc
        (p : ℤ) * z = (p ^ 2 : ℤ) * k := hk
        _ = (p : ℤ) * ((p : ℤ) * k) := by ring
    refine ⟨(k : R), ?_⟩
    simp [hz, Int.cast_mul]
  have hdivide : ∀ y : B, (p : R) • y = 0 →
      ∃ z : B, y = (p : R) • z := by
    intro y hy
    have htr : Module.IsTrivialRelation
        (fun _ : Fin 1 => (p : R)) (fun _ : Fin 1 => y) := by
      apply Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      simpa [Fin.sum_univ_succ] using hy
    rcases htr with ⟨k, a, z, ha, haz⟩
    have hfactor : ∀ j : Fin k, ∃ c : R, a 0 j = (p : R) * c := by
      intro j
      apply hscalar
      simpa using haz j
    choose c hc using hfactor
    refine ⟨∑ j, c j • z j, ?_⟩
    calc
      y = ∑ j, a 0 j • z j := ha 0
      _ = ∑ j, ((p : R) * c j) • z j := by simp_rw [hc]
      _ = (p : R) • ∑ j, c j • z j := by
        rw [Finset.smul_sum]
        congr 1
        funext j
        rw [mul_smul]
  let D : B → B → B := fun u v =>
    ∑ k ∈ Finset.range (p + 1) with 0 < k ∧ k < p,
      algebraMap R B ((p.choose k / p : ℕ) : R) * u ^ k * v ^ (p - k)
  have hbinom (u v : B) :
      (u + v) ^ p = u ^ p + v ^ p + (p : R) • D u v := by
    classical
    rw [add_pow]
    simp only [D, Algebra.smul_def]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p + 1))
      (fun k => 0 < k ∧ k < p)]
    have hcomp : (Finset.range (p + 1)).filter (fun k => ¬ (0 < k ∧ k < p)) =
        {0, p} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    rw [hcomp]
    rw [Finset.sum_insert]
    · simp only [Finset.sum_singleton, Nat.choose_zero_right, Nat.choose_self,
        pow_zero, mul_one, Nat.sub_self, Nat.sub_zero, Nat.cast_one]
      have hsum :
          (∑ k ∈ Finset.range (p + 1) with 0 < k ∧ k < p,
            u ^ k * v ^ (p - k) * (p.choose k : B)) =
            ∑ k ∈ Finset.range (p + 1) with 0 < k ∧ k < p,
              (algebraMap R B) (p : R) *
                (u ^ k * v ^ (p - k) *
                  (algebraMap R B) ((p.choose k / p : ℕ) : R)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < p + 1 ∧ 0 < k ∧ k < p := by
          simpa only [Finset.mem_filter, Finset.mem_range] using hk
        have hk0 : k ≠ 0 := by
          exact Nat.ne_of_gt hk'.2.1
        have hklt : k < p := by
          exact hk'.2.2
        have hdiv : p ∣ p.choose k := hp.dvd_choose_self hk0 hklt
        have hcast : (p.choose k : B) =
            (algebraMap R B) (p : R) *
              (algebraMap R B) ((p.choose k / p : ℕ) : R) := by
          have hn : p * (p.choose k / p) = p.choose k :=
            Nat.mul_div_cancel' hdiv
          calc
            (p.choose k : B) = ((p * (p.choose k / p) : ℕ) : B) := by
              exact congrArg (fun n : ℕ => (n : B)) hn.symm
            _ = (algebraMap R B) (p : R) *
                (algebraMap R B) ((p.choose k / p : ℕ) : R) := by
              have hpmap : (algebraMap R B) (p : R) = (p : B) := by
                simp [R]
              have hqmap : (algebraMap R B)
                  ((p.choose k / p : ℕ) : R) =
                    (p.choose k / p : B) := by
                simp [R]
              rw [hpmap, hqmap]
              simp only [Nat.cast_mul]
        rw [hcast]
        ring
      calc
        (∑ x ∈ Finset.range (p + 1) with 0 < x ∧ x < p,
              u ^ x * v ^ (p - x) * (p.choose x : B)) +
            ((1 : B) * v ^ p + u ^ p) =
            u ^ p + v ^ p +
              ∑ x ∈ Finset.range (p + 1) with 0 < x ∧ x < p,
                u ^ x * v ^ (p - x) * (p.choose x : B) := by
          ring
        _ = u ^ p + v ^ p +
              ∑ x ∈ Finset.range (p + 1) with 0 < x ∧ x < p,
                (algebraMap R B) (p : R) *
                  (u ^ x * v ^ (p - x) *
                    (algebraMap R B) ((p.choose x / p : ℕ) : R)) := by
          rw [hsum]
        _ = u ^ p + v ^ p +
              (algebraMap R B) (p : R) * D u v := by
          simp only [D]
          rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          ring
    · intro h
      apply hp.ne_zero
      have h' : 0 = p := by simpa only [Finset.mem_singleton] using h
      exact h'.symm
  let A := sixVariableQuadraticAlgebra p
  let φ : B →+* A := e.toRingHom.comp π
  let y : Fin 6 → A := fun i =>
    Ideal.Quotient.mk (sixVariableQuadraticIdeal p (ZMod p))
      (MvPolynomial.X i)
  have hφsurj : Function.Surjective φ := by
    exact e.surjective.comp π.surjective
  choose x hx using fun i => hφsurj (y i)
  have hy_pow (i : Fin 6) : y i ^ p = 0 := by
    change (Ideal.Quotient.mk (sixVariableQuadraticIdeal p (ZMod p))
      (MvPolynomial.X i)) ^ p = 0
    rw [← map_pow]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (MvPolynomial.X i) ^ p ∈ sixVariableQuadraticIdeal p (ZMod p)
    exact Ideal.subset_span (Or.inl ⟨i, rfl⟩)
  have hpow_mem (i : Fin 6) : x i ^ p ∈ K := by
    have hφpow : φ (x i ^ p) = 0 := by
      rw [map_pow, hx i, hy_pow]
    have hπpow : π (x i ^ p) = 0 := by
      apply e.injective
      simpa [φ] using hφpow
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hπpow
  choose z hz using fun i => (Ideal.mem_span_singleton'.mp (hpow_mem i))
  let a := x 0 * x 1
  let b := x 2 * x 3
  let c := x 4 * x 5
  let q := a + b + c
  have hq_mem : q ∈ K := by
    have hφq : φ q = 0 := by
      dsimp [q, a, b, c]
      rw [map_add, map_add, map_mul, map_mul, map_mul,
        hx 0, hx 1, hx 2, hx 3, hx 4, hx 5]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr <| by
        exact Ideal.subset_span (Or.inr rfl)
    have hπq : π q = 0 := by
      apply e.injective
      simpa [φ] using hφq
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hπq
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hq_mem
  let P : B := algebraMap R B (p : R)
  have hp2 : 2 ≤ p := hp.two_le
  have hR2 : (p : R) ^ 2 = 0 := by
    change (p : ZMod (p ^ 2)) ^ 2 = 0
    rw [← Nat.cast_pow]
    exact (ZMod.natCast_eq_zero_iff (p ^ 2) (p ^ 2)).2 dvd_rfl
  have hP2 : P ^ 2 = 0 := by
    change (algebraMap R B (p : R)) ^ 2 = 0
    rw [← map_pow]
    simpa using congrArg (algebraMap R B) hR2
  have hPpow : P ^ p = 0 := by
    rw [show p = 2 + (p - 2) by omega, pow_add, hP2, zero_mul]
  have hxp (i : Fin 6) : x i ^ p = P * z i := by
    rw [← hz i]
    dsimp [P]
    ring
  have ha_pow : a ^ p = 0 := by
    dsimp [a]
    rw [mul_pow, hxp, hxp]
    calc
      (P * z 0) * (P * z 1) = P ^ 2 * (z 0 * z 1) := by ring
      _ = 0 := by rw [hP2, zero_mul]
  have hb_pow : b ^ p = 0 := by
    dsimp [b]
    rw [mul_pow, hxp, hxp]
    calc
      (P * z 2) * (P * z 3) = P ^ 2 * (z 2 * z 3) := by ring
      _ = 0 := by rw [hP2, zero_mul]
  have hc_pow : c ^ p = 0 := by
    dsimp [c]
    rw [mul_pow, hxp, hxp]
    calc
      (P * z 4) * (P * z 5) = P ^ 2 * (z 4 * z 5) := by ring
      _ = 0 := by rw [hP2, zero_mul]
  have hq_pow : q ^ p = 0 := by
    rw [← hw, mul_pow, hPpow, mul_zero]
  have hsum_pow :
      q ^ p = a ^ p + b ^ p + c ^ p +
        (p : R) • (D a b + D (a + b) c) := by
    calc
      q ^ p = (a + b + c) ^ p := by rfl
      _ = (a + b) ^ p + c ^ p + (p : R) • D (a + b) c :=
        hbinom (a + b) c
      _ = a ^ p + b ^ p + c ^ p +
          (p : R) • (D a b + D (a + b) c) := by
        rw [hbinom a b]
        simp only [add_assoc]
        module
  have hDkill : (p : R) • (D a b + D (a + b) c) = 0 := by
    rw [← hq_pow, hsum_pow, ha_pow, hb_pow, hc_pow]
    simp
  exfalso
  sorry

/-- In particular, the characteristic-two algebra in the source has no flat
lift to a `ℤ/4ℤ`-algebra. -/
theorem no_flat_zmodFour_sixVariableQuadratic_lift :
    ¬ ∃ (B : Type) (_ : CommRing B) (_ : Algebra (ZMod 4) B),
      Module.Flat (ZMod 4) B ∧
        Nonempty
          (principalSpecialFiber (R := ZMod 4) (B := B) (2 : ZMod 4)
            ≃+* sixVariableQuadraticAlgebra 2) := by
  exact no_flat_sixVariableQuadratic_lift 2 Nat.prime_two

end Formalization.Books.Exercises.Unit05
