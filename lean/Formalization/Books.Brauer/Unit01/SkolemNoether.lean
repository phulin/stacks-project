import Formalization.«Books.Brauer».Unit01.BrauerGroup
import Mathlib.Algebra.Algebra.Equiv

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
  sorry

end Formalization.Books.Brauer
