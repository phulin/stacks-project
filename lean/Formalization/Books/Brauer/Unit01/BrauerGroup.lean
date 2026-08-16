import Formalization.Books.Brauer.Unit01.AlgebraLemmas
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The Brauer group of a field

Mathlib already supplies the canonical `CSA`, similarity relation, setoid, and
quotient used here.  This file adds the source-facing interfaces for the
group, base-change, division-representative, and dimension assertions.
-/

namespace Formalization.Books.Brauer

open scoped TensorProduct

/-- The similarity class of a finite central simple algebra. -/
def brauerClass (k : Type*) [Field k] (A : CSA k) : BrauerGroup k :=
  Quotient.mk (Brauer.CSA_Setoid k) A

/- The canonical right-hand tensor algebra is local in Mathlib, so this
   relation packages the source's base-change representative without
   introducing a competing algebra structure. -/
def IsBaseChangeRepresentative (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] (A : CSA k) (B : CSA k') : Prop :=
  letI : Algebra k' (A.carrier ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  Nonempty ((A.carrier ⊗[k] k') ≃ₐ[k'] B.carrier)

theorem similarity_is_equivalence (k : Type*) [Field k] :
    Equivalence (@IsBrauerEquivalent k _) :=
  IsBrauerEquivalent.is_eqv

theorem similarity_has_unique_division_representative (k : Type*) [Field k] :
    ∀ A : CSA k,
      ∃ D : CSA k,
        Nonempty (DivisionRing (D : Type*)) ∧
          IsBrauerEquivalent A D ∧
            ∀ E : CSA k, Nonempty (DivisionRing (E : Type*)) →
              IsBrauerEquivalent A E →
                Nonempty (D.carrier ≃ₐ[k] E.carrier) := by
  sorry

theorem matrix_division_similarity_iff (k K K' : Type*) [Field k]
    [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] [DivisionRing K'] [Algebra k K']
    [FiniteDimensional k K'] [Algebra.IsCentral k K'] :
    (∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧
      Nonempty (Matrix (Fin n) (Fin n) K ≃ₐ[k]
        Matrix (Fin m) (Fin m) K')) ↔
      Nonempty (K ≃ₐ[k] K') := by
  sorry

theorem brauer_group_tensor_operation_interface (k : Type*) [Field k] :
    ∃ mul : BrauerGroup k → BrauerGroup k → BrauerGroup k,
      ∀ A B : CSA k, ∃ C : CSA k,
        mul (brauerClass k A) (brauerClass k B) = brauerClass k C ∧
          Nonempty ((A.carrier ⊗[k] B.carrier) ≃ₐ[k] C.carrier) := by
  sorry

theorem brauer_group_is_abelian (k : Type*) [Field k] :
    Nonempty (CommGroup (BrauerGroup k)) := by
  sorry

theorem brauer_group_base_change_hom (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] [CommGroup (BrauerGroup k)]
    [CommGroup (BrauerGroup k')] :
    Nonempty (BrauerGroup k →* BrauerGroup k') := by
  sorry

theorem brauer_group_base_change_interface (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] [CommGroup (BrauerGroup k)]
    [CommGroup (BrauerGroup k')] :
    ∃ f : BrauerGroup k →* BrauerGroup k',
      ∀ A : CSA k, ∃ B : CSA k',
        f (brauerClass k A) = brauerClass k' B ∧
          IsBaseChangeRepresentative k k' A B := by
  sorry

theorem brauer_group_zero_iff (k : Type*) [Field k]
    [CommGroup (BrauerGroup k)] :
    (∀ x : BrauerGroup k, x = 1) ↔
      (∀ (K : Type*) [DivisionRing K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsCentral k K],
        Nonempty (K ≃ₐ[k] k)) := by
  sorry

theorem brauer_group_algebraically_closed (k : Type*) [Field k]
    [IsAlgClosed k] [CommGroup (BrauerGroup k)] :
    ∀ x : BrauerGroup k, x = 1 := by
  sorry

theorem finite_central_simple_dimension_square (k A : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [IsSimpleRing A] :
    ∃ d : ℕ, Module.finrank k A = d ^ 2 := by
  sorry

end Formalization.Books.Brauer
