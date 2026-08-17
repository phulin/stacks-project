import Formalization.Books.Brauer.Unit01.SkolemNoether
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

/-!
# The centralizer theorem

The canonical `Subalgebra.centralizer` is used throughout.  A small
source-facing predicate packages the textbook notion of a maximal
commutative subalgebra.
-/

namespace Formalization.Books.Brauer

open scoped TensorProduct

/-- A commutative subalgebra maximal among commutative subalgebras. -/
def IsMaximalCommutativeSubalgebra (k A : Type*) [CommSemiring k]
    [Semiring A] [Algebra k A] (S : Subalgebra k A) : Prop :=
  (∀ x y : S, Commute (x : A) (y : A)) ∧
    ∀ T : Subalgebra k A,
      (∀ x y : T, Commute (x : A) (y : A)) → S ≤ T → T = S

theorem centralizer_theorem (k A : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]
    (B : Subalgebra k A) [IsSimpleRing B] :
    let C := Subalgebra.centralizer k (B : Set A)
    IsSimpleRing C ∧
      Module.finrank k A = Module.finrank k B * Module.finrank k C ∧
        Subalgebra.centralizer k (C : Set A) = B := by
  sorry

theorem central_simple_tensor_decomposition (k A : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [IsSimpleRing A] (B : Subalgebra k A)
    [IsSimpleRing B] [Algebra.IsCentral k B] :
    let C := Subalgebra.centralizer k (B : Set A)
    IsSimpleRing C ∧ Algebra.IsCentral k C ∧
      Nonempty (B ⊗[k] C ≃ₐ[k] A) := by
  sorry

theorem self_centralizing_subfield_tfae (k A K : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Algebra.IsCentral k A]
    [IsSimpleRing A] [Field K] [Algebra k K] [FiniteDimensional k K]
    (f : K →ₐ[k] A) (hf : Function.Injective f) :
    List.TFAE
      [Module.finrank k A = Module.finrank k K ^ 2,
        Subalgebra.centralizer k (Set.range f) = AlgHom.range f,
        IsMaximalCommutativeSubalgebra k A (AlgHom.range f)] := by
  sorry

theorem maximal_subfield_dimension_square (k A K : Type*) [Field k]
    [DivisionRing A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [Field K] [Algebra k K]
    [FiniteDimensional k K] (f : K →ₐ[k] A) (hf : Function.Injective f)
    (hmax : IsMaximalCommutativeSubalgebra k A (AlgHom.range f)) :
    Module.finrank k A = Module.finrank k K ^ 2 := by
  exact ((self_centralizing_subfield_tfae k A K f hf).out 2 0).mp hmax

end Formalization.Books.Brauer
