import Formalization.Books.Brauer.Unit01.BrauerGroup
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

/-!
# Skolem--Noether

The source theorem is recorded with units, so the conjugating element is
invertible by construction rather than merely assumed to be a division-ring
element.
-/

namespace Formalization.Books.Brauer

theorem skolem_noether (k A B : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]
    [Ring B] [Algebra k B] [IsSimpleRing B]
    (f g : B →ₐ[k] A) :
    ∃ x : Aˣ, ∀ b : B,
      f b = (x : A) * g b * (x⁻¹ : Aˣ) := by
  sorry

theorem finite_central_simple_automorphism_inner (k A : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [IsSimpleRing A] (f : A ≃ₐ[k] A) :
    ∃ x : Aˣ, ∀ a : A,
      f a = (x : A) * a * (x⁻¹ : Aˣ) := by
  sorry

theorem matrix_automorphism_inner (k : Type*) (n : ℕ) [Field k] [NeZero n]
    (f : Matrix (Fin n) (Fin n) k ≃ₐ[k] Matrix (Fin n) (Fin n) k) :
    ∃ x : (Matrix (Fin n) (Fin n) k)ˣ, ∀ a,
      f a = (x : Matrix (Fin n) (Fin n) k) * a * (x⁻¹ : _) := by
  classical
  let V := Fin n → k
  let e : Module.End k V ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
    LinearMap.toMatrixAlgEquiv (Pi.basisFun k (Fin n))
  let h : Module.End k V ≃ₐ[k] Module.End k V :=
    e.trans (f.trans e.symm)
  obtain ⟨T, hT⟩ := h.eq_linearEquivConjAlgEquiv
  let u : (Module.End k V)ˣ :=
    { val := T.toLinearMap
      inv := T.symm.toLinearMap
      val_inv := by
        apply LinearMap.ext
        intro v
        simp [Module.End.mul_eq_comp]
      inv_val := by
        apply LinearMap.ext
        intro v
        simp [Module.End.mul_eq_comp] }
  let x : (Matrix (Fin n) (Fin n) k)ˣ :=
    Units.map e.toRingEquiv.toMonoidHom u
  refine ⟨x, ?_⟩
  intro a
  have hTa := DFunLike.congr_fun hT (e.symm a)
  have hTa' := congrArg e hTa
  have hTa'' : f a =
      e (T.toLinearMap ∘ₗ e.symm a ∘ₗ T.symm.toLinearMap) := by
    calc
      f a = e (h (e.symm a)) := by simp [h]
      _ = e (T.toLinearMap ∘ₗ e.symm a ∘ₗ T.symm.toLinearMap) := by
        simpa [LinearEquiv.conjAlgEquiv_apply] using hTa'
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp] at hTa''
  simpa [h, x, u, mul_assoc] using hTa''

end Formalization.Books.Brauer
