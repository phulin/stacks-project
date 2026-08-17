import Mathlib.Algebra.Algebra.Bilinear

/-!
# 2. Conventions

The source uses “ring” for a commutative ring with `1`; this is Mathlib's
`CommRing` typeclass.  An `R`-algebra is represented by Mathlib's canonical
`Algebra R A` typeclass, together with `Ring A` for the unital associative
ring structure on the algebra.  This does not add a `Nontrivial` assumption,
so the zero ring is included.

The multiplication map in the source is Mathlib's `LinearMap.mul R A`.  The
centrality of the structure map is the field exposed by `Algebra.commutes`,
and the compatibility between the scalar action and that map is
`Algebra.smul_def`.
-/

namespace Sdga

universe u v

/-- The module structure required by the convention is supplied by `Algebra`. -/
abbrev algebra_convention_module (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A] : Module R A :=
  inferInstance

/-- Mathlib's canonical bilinear multiplication map has the source's product. -/
theorem algebra_convention_multiplication_is_bilinear
    (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A] :
    ∃ μ : A →ₗ[R] A →ₗ[R] A, ∀ a b : A, μ a b = a * b := by
  exact ⟨LinearMap.mul R A, fun _ _ => rfl⟩

/-- The multiplication in an algebra is associative. -/
theorem algebra_convention_multiplication_associative
    (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (a b c : A) :
    (a * b) * c = a * (b * c) := by
  exact mul_assoc a b c

/-- The multiplication in an algebra has a two-sided identity. -/
theorem algebra_convention_multiplication_identity
    (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (a : A) :
    (1 : A) * a = a ∧ a * 1 = a := by
  exact ⟨one_mul a, mul_one a⟩

/-- The scalar action is multiplication by the image of the structure map. -/
theorem algebra_convention_smul_eq_algebraMap_mul
    (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (r : R) (a : A) :
    r • a = algebraMap R A r * a := by
  exact Algebra.smul_def r a

/-- The image of the structure map lies in the center of the algebra. -/
theorem algebra_convention_algebraMap_is_central
    (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (r : R) (a : A) :
    algebraMap R A r * a = a * algebraMap R A r := by
  exact Algebra.commutes r a

end Sdga
