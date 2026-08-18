import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
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
theorem sixVariablePowerLift_specialFiber (p : ℕ) (hp : Nat.Prime p) :
    Nonempty (sixVariablePowerLiftSpecialFiber p ≃+* sixVariablePowerAlgebra p) := by
  sorry

/-- The second exercise supplies a flat `ℤ/p²ℤ`-algebra lifting the displayed
characteristic-`p` algebra. -/
theorem exists_flat_zmodSquare_lift (p : ℕ) (hp : Nat.Prime p) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra (ZMod (p ^ 2)) B),
      Module.Flat (ZMod (p ^ 2)) B ∧
        Nonempty
          (principalSpecialFiber (R := ZMod (p ^ 2)) (B := B) (p : ZMod (p ^ 2))
            ≃+* sixVariablePowerAlgebra p) := by
  refine ⟨sixVariablePowerLift p, inferInstance, inferInstance, ?_⟩
  exact ⟨sixVariablePowerLift_flat p hp, sixVariablePowerLift_specialFiber p hp⟩

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
