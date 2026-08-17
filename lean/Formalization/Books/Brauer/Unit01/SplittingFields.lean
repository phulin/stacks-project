import Formalization.Books.Brauer.Unit01.Centralizer
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.JacobsonNoether

/-!
# Splitting fields

The right-hand tensor-product algebra is installed locally by the splitting
predicates, following Mathlib's convention that this structure is not a
global instance because the left and right actions can otherwise be
ambiguous.
-/

namespace Formalization.Books.Brauer

open scoped TensorProduct

universe u_k u_A u_K

/-- `k'` splits `A` in the specified matrix degree. -/
def SplitsInDegree (k A k' : Type*) [Field k] [Ring A] [Algebra k A]
    [Field k'] [Algebra k k'] (d : ℕ) : Prop :=
  letI : Algebra k' (A ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  Nonempty ((A ⊗[k] k') ≃ₐ[k'] Matrix (Fin d) (Fin d) k')

/-- A field extension splits an algebra when it splits it in some matrix degree. -/
def Splits (k A k' : Type*) [Field k] [Ring A] [Algebra k A]
    [Field k'] [Algebra k k'] : Prop :=
  ∃ d : ℕ, SplitsInDegree k A k' d

theorem splits_iff_exists_matrix_degree (k A k' : Type*) [Field k] [Ring A]
    [Algebra k A] [Field k'] [Algebra k k'] :
    Splits k A k' ↔ ∃ d : ℕ, SplitsInDegree k A k' d := by
  rfl

theorem splits_iff_base_change_class_eq_one (k k' : Type*) [Field k]
    [Field k'] [Algebra k k'] (A : CSA k) :
    Splits k A.carrier k' ↔
      ∃ B : CSA k',
        IsBaseChangeRepresentative k k' A B ∧ brauerClass k' B = 1 := by
  sorry

theorem splitting_iff_similar_embedded_subfield (k k' : Type*) [Field k]
    [Field k'] [Algebra k k'] [FiniteDimensional k k'] (A : CSA k) :
    Splits k A.carrier k' ↔
      ∃ B : CSA k, IsBrauerEquivalent A B ∧
        ∃ f : k' →ₐ[k] B.carrier,
          Function.Injective f ∧
            Module.finrank k B.carrier = Module.finrank k k' ^ 2 := by
  sorry

theorem maximal_subfield_splits (k K k' : Type*) [Field k]
    [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (f : k' →ₐ[k] K) (hf : Function.Injective f)
    (hmax : IsMaximalCommutativeSubalgebra k K (AlgHom.range f)) :
    Splits k K k' := by
  sorry

theorem splitting_field_degree_dvd (k K k' : Type*) [Field k]
    [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (d : ℕ)
    (hd : Module.finrank k K = d ^ 2) (h : Splits k K k') :
    d ∣ Module.finrank k k' := by
  sorry

/-- A separable maximal subfield of a finite central division algebra. -/
structure SeparableMaximalSubfield (k : Type u_k) (K : Type u_K)
    [Field k] [DivisionRing K]
    [Algebra k K] where
  carrier : Type u_K
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [finite : FiniteDimensional k carrier]
  embedding : carrier →ₐ[k] K
  injective : Function.Injective embedding
  maximal : IsMaximalCommutativeSubalgebra k K (AlgHom.range embedding)
  [separable : Algebra.IsSeparable k carrier]

theorem exists_separable_maximal_subfield (k K : Type*) [Field k]
    [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] :
    Nonempty (SeparableMaximalSubfield k K) := by
  sorry

/-- A finite separable extension which splits a given algebra. -/
structure FiniteSeparableSplittingField (k : Type u_k) (A : Type u_A) [Field k] [Ring A]
    [Algebra k A] where
  carrier : Type u_k
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [finite : FiniteDimensional k carrier]
  [separable : Algebra.IsSeparable k carrier]
  degree : ℕ
  degree_pos : 0 < degree
  splitting : SplitsInDegree k A carrier degree

theorem brauer_class_has_finite_separable_splitting_field (k : Type*)
    [Field k] :
    ∀ A : CSA k, Nonempty (FiniteSeparableSplittingField k A.carrier) := by
  sorry

/-- A finite Galois splitting field, packaged with its typeclass data. -/
structure FiniteGaloisSplittingField (k : Type u_k) (A : Type u_A) [Field k] [Ring A]
    [Algebra k A] where
  carrier : Type u_k
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [finite : FiniteDimensional k carrier]
  [galois : IsGalois k carrier]
  degree : ℕ
  degree_pos : 0 < degree
  splitting : SplitsInDegree k A carrier degree

/-- A Wedderburn presentation by a matrix algebra over a finite central skew field. -/
structure MatrixDivisionPresentation (k : Type u_k) (A : Type u_A) [Field k] [Ring A]
    [Algebra k A] where
  degree : ℕ
  degree_pos : 0 < degree
  division : Type u_A
  [divisionRing : DivisionRing division]
  [algebra : Algebra k division]
  [finite : FiniteDimensional k division]
  [central : Algebra.IsCentral k division]
  equivalence : Nonempty
    (A ≃ₐ[k] Matrix (Fin degree) (Fin degree) division)

theorem finite_central_simple_tfae (k A : Type*) [Field k] [Ring A]
    [Algebra k A] :
    List.TFAE
      [FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A,
        FiniteDimensional k A ∧
          Subalgebra.center k A = ⊥ ∧ IsSimpleRing A,
        ∃ d : ℕ, 0 < d ∧ SplitsInDegree k A (AlgebraicClosure k) d,
        ∃ d : ℕ, 0 < d ∧ SplitsInDegree k A (SeparableClosure k) d,
        Nonempty (FiniteGaloisSplittingField k A),
        Nonempty (MatrixDivisionPresentation k A)] := by
  sorry

theorem finite_central_simple_degree_is_unique (k A : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [IsSimpleRing A] :
    ∃! d : ℕ, 0 < d ∧ SplitsInDegree k A (AlgebraicClosure k) d := by
  let K := AlgebraicClosure k
  letI : Algebra K (A ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  have hbase := base_change_finite_central_simple k A K
  letI : FiniteDimensional K (A ⊗[k] K) := hbase.1
  letI : Algebra.IsCentral K (A ⊗[k] K) := hbase.2.1
  letI : IsSimpleRing (A ⊗[k] K) := hbase.2.2
  obtain ⟨d, hd, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K (A ⊗[k] K)
  have hbase_finrank : Module.finrank K (A ⊗[k] K) = Module.finrank k A := by
    calc
      Module.finrank K (A ⊗[k] K) = Module.finrank K (K ⊗[k] A) :=
        (Algebra.TensorProduct.commRight k K A).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k A := by rw [Module.finrank_baseChange]
  have hdegree : 0 < d := Nat.pos_iff_ne_zero.mpr hd.out
  refine ⟨d, ⟨hdegree, ?_⟩, ?_⟩
  · exact ⟨e⟩
  · intro d' hd'
    rcases hd' with ⟨hdegree', hsplit⟩
    dsimp [SplitsInDegree] at hsplit
    obtain ⟨e'⟩ := hsplit
    have hdsq : d' ^ 2 = Module.finrank k A := by
      calc
        d' ^ 2 = Module.finrank K (Matrix (Fin d') (Fin d') K) := by
          simp [Module.finrank_matrix, pow_two]
        _ = Module.finrank K (A ⊗[k] K) := e'.toLinearEquiv.finrank_eq.symm
        _ = Module.finrank k A := hbase_finrank
    have hdsq0 : d ^ 2 = Module.finrank k A := by
      calc
        d ^ 2 = Module.finrank K (Matrix (Fin d) (Fin d) K) := by
          simp [Module.finrank_matrix, pow_two]
        _ = Module.finrank K (A ⊗[k] K) := e.toLinearEquiv.finrank_eq.symm
        _ = Module.finrank k A := hbase_finrank
    exact Nat.pow_left_injective (n := 2) (by decide) (hdsq.trans hdsq0.symm)

end Formalization.Books.Brauer
