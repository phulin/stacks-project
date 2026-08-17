import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.Discriminant

/-!
# Fields, Chapter 20: Trace and norm

The source's trace, norm, trace pairing, and basis discriminant are Mathlib's
`Algebra.trace`, `Algebra.norm`, `Algebra.traceForm`, and `Algebra.discr`.
The textbook packages the last of these as a square class of the base field;
Mathlib exposes the representative attached to a basis, so this file adds the
small square-class quotient needed for the source-facing extension invariant.
-/

namespace Formalization.Books.Fields.Unit20

noncomputable section

open Polynomial
open scoped BigOperators

universe u v

/-! ## Finite-dimensional multiplication, trace, and norm -/

/- A finite extension has the finite basis used in the source's matrix
   construction.  The multiplication matrix itself is Mathlib's canonical
   `Algebra.leftMulMatrix`; no parallel matrix representation is introduced. -/
/-- A finite field extension has a basis indexed by its finite dimension. -/
theorem finite_extension_has_fin_basis
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Nonempty (Module.Basis (Fin (Module.finrank K L)) K L) :=
  ⟨Module.finBasis K L⟩

/-- The matrix of multiplication by an element is the matrix of the canonical
    `K`-linear multiplication map in the chosen basis. -/
theorem multiplication_matrix_representation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (b : Module.Basis (Fin n) K L) (α : L) :
    Algebra.leftMulMatrix b α =
      LinearMap.toMatrix b b (Algebra.lmul K L α) :=
  Algebra.leftMulMatrix_apply b α

/-- In any chosen finite basis, the canonical trace is the matrix trace of
    multiplication. -/
theorem field_trace_from_multiplication_matrix
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {n : ℕ}
    (b : Module.Basis (Fin n) K L) (α : L) :
    Algebra.trace K L α = Matrix.trace (Algebra.leftMulMatrix b α) := by
  exact Algebra.trace_eq_matrix_trace b α

/-- In any chosen finite basis, the canonical norm is the determinant of the
    multiplication matrix. -/
theorem field_norm_from_multiplication_matrix
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {n : ℕ}
    (b : Module.Basis (Fin n) K L) (α : L) :
    Algebra.norm K α = Matrix.det (Algebra.leftMulMatrix b α) := by
  exact Algebra.norm_eq_matrix_det b α

/- The definitions in the source are exactly the canonical determinant and
   linear-map trace constructions. -/
/-- The field trace is the linear-map trace of multiplication. -/
theorem field_trace_definition
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (α : L) :
  Algebra.trace K L α = LinearMap.trace K L (Algebra.lmul K L α) :=
  Algebra.trace_apply K α

/-- The field norm is the determinant of multiplication. -/
theorem field_norm_definition
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (α : L) :
  Algebra.norm K α = LinearMap.det (Algebra.lmul K L α) :=
  Algebra.norm_apply K α

/-- The trace of a scalar is its extension degree times that scalar. -/
theorem field_trace_algebraMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : K) :
    Algebra.trace K L (algebraMap K L x) = Module.finrank K L • x :=
  Algebra.trace_algebraMap x

/-- The norm is multiplicative. -/
theorem field_norm_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x y : L) :
    Algebra.norm K (x * y) = Algebra.norm K x * Algebra.norm K y :=
  map_mul (Algebra.norm K) x y

/-- The norm of a scalar is the scalar raised to the extension degree. -/
theorem field_norm_algebraMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : K) :
    Algebra.norm K (algebraMap K L x) = x ^ Module.finrank K L :=
  Algebra.norm_algebraMap x

/-! ## Characteristic and minimal polynomials -/

/-- The characteristic polynomial of multiplication is a power of the
    minimal polynomial, with the expected degree relation. -/
theorem characteristic_polynomial_multiplication_eq_pow_minpoly
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (α : L) :
    ∃ e : ℕ,
      e * (minpoly K α).natDegree = Module.finrank K L ∧
        (Algebra.lmul K L α).charpoly = (minpoly K α) ^ e := by
  sorry

/-- Trace and norm are read from the first and last coefficients of the
    minimal polynomial. -/
theorem field_trace_and_norm_from_minpoly
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (α : L) (P : Polynomial K)
    (hP : P = minpoly K α) :
    ∃ e : ℕ,
      e * P.natDegree = Module.finrank K L ∧
        Algebra.norm K α = (-1 : K) ^ Module.finrank K L * (P.coeff 0) ^ e ∧
          Algebra.trace K L α = -(e : K) * P.nextCoeff := by
  sorry

/-! ## Restriction of scalars and towers -/

/-- Trace and determinant after restriction of scalars are obtained by taking
    the trace and norm of the corresponding `L`-valued invariants. -/
theorem trace_and_determinant_restrictScalars
    {K L V : Type*} [Field K] [Field L] [AddCommGroup V]
    [Algebra K L] [Module K V] [Module L V] [IsScalarTower K L V]
    [FiniteDimensional K L] [FiniteDimensional L V]
    (φ : V →ₗ[L] V) :
    LinearMap.trace K V (φ.restrictScalars K) =
        Algebra.trace K L (LinearMap.trace L V φ) ∧
      LinearMap.det (φ.restrictScalars K) =
        Algebra.norm K (LinearMap.det φ) := by
  sorry

/-- Trace is transitive in a finite tower of field extensions. -/
theorem field_trace_tower
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] (x : M) :
    Algebra.trace K M x =
      Algebra.trace K L (Algebra.trace L M x) := by
  exact (Algebra.trace_trace (R := K) (S := L) (T := M) x).symm

/-- Norm is transitive in a finite tower of field extensions. -/
theorem field_norm_tower
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] (x : M) :
    Algebra.norm K x =
      Algebra.norm K (Algebra.norm L x) := by
  exact (Algebra.norm_norm (R := K) (S := L) (a := x)).symm

/-! ## The trace pairing and separability -/

/- The trace pairing is Mathlib's `Algebra.traceForm`; its type is already a
   `K`-bilinear form, and the following declarations expose the source-facing
   formula and symmetry. -/
/-- The trace pairing is given by the trace of a product. -/
theorem trace_pairing_definition
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (α β : L) :
  Algebra.traceForm K L α β = Algebra.trace K L (α * β) :=
  Algebra.traceForm_apply K α β

/-- The trace pairing is symmetric. -/
theorem trace_pairing_symmetric
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
  (Algebra.traceForm K L).IsSymm :=
  Algebra.traceForm_isSymm K

/-- For a finite field extension, separability, nonzero trace, and
    nondegeneracy of the trace pairing are equivalent. -/
theorem separable_iff_trace_nonzero_iff_trace_pairing_nondegenerate
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    (Algebra.IsSeparable K L ↔ Algebra.trace K L ≠ 0) ∧
      (Algebra.trace K L ≠ 0 ↔ (Algebra.traceForm K L).Nondegenerate) := by
  classical
  constructor
  · constructor
    · intro h
      exact @Algebra.trace_ne_zero K L _ _ _ _ h
    · intro h
      by_contra hs
      exact h (Algebra.trace_eq_zero_of_not_isSeparable hs)
  · constructor
    · intro h
      apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
      intro x hx
      by_contra hxn
      obtain ⟨z, hz⟩ : ∃ z : L, Algebra.trace K L z ≠ 0 := by
        by_contra hz'
        apply h
        ext z
        by_contra hz
        exact hz' ⟨z, hz⟩
      have hxz := hx (x⁻¹ * z)
      rw [Algebra.traceForm_apply] at hxz
      exact (hz (by simpa [mul_assoc, hxn] using hxz)).elim
    · intro h
      rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot] at h
      intro ht
      have h1 : (1 : L) ∈ LinearMap.ker (Algebra.traceForm K L) := by
        change (Algebra.traceForm K L) 1 = 0
        ext y
        simp [Algebra.traceForm_apply, ht]
      have h2 : (1 : L) ∈ (⊥ : Submodule K L) := h ▸ h1
      simp at h2

/-- A nonseparable finite extension has identically zero trace. -/
theorem field_trace_eq_zero_of_not_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (h : ¬ Algebra.IsSeparable K L) :
    Algebra.trace K L = 0 :=
  Algebra.trace_eq_zero_of_not_isSeparable h

/-- The trace is surjective in a finite separable field extension. -/
theorem field_trace_surjective_of_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Function.Surjective (Algebra.trace K L) :=
  Algebra.trace_surjective K L

/-- The trace vanishes on a simple purely inseparable prime-degree extension.
    The source's condition `L = K(α)` is represented by the canonical
    intermediate field `IntermediateField.adjoin K {α}`. -/
theorem field_trace_eq_zero_of_purely_inseparable_simple_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : ℕ) [CharP K p] (hp : p.Prime) (α : L)
    (hα : α ∉ (algebraMap K L).range)
    (hαp : α ^ p ∈ (algebraMap K L).range)
    (hgen : IntermediateField.adjoin K ({α} : Set L) = ⊤) :
    Algebra.trace K L = 0 := by
  sorry

/-! ## Discriminants and square classes -/

/- Mathlib's discriminant is attached to a finite family.  The source's
   quotient `K/(K^*)^2` is represented by the orbit quotient for multiplication
   by squares of units; this also keeps the zero class distinct. -/
def squareClassSetoid (K : Type u) [Field K] : Setoid K where
  r x y := ∃ u : Kˣ, y = (u : K) ^ 2 * x
  iseqv := {
    refl := fun x => ⟨1, by simp⟩
    symm := by
      intro x y ⟨u, h⟩
      refine ⟨u⁻¹, ?_⟩
      rw [h]
      simp
    trans := by
      intro x y z ⟨u, hxy⟩ ⟨v, hyz⟩
      refine ⟨v * u, ?_⟩
      rw [hyz, hxy]
      simp [mul_pow, mul_assoc, mul_comm]
  }

/-- The square-class quotient of a field, including the separate zero class. -/
abbrev SquareClass (K : Type u) [Field K] := Quotient (squareClassSetoid K)

/-- The class of a field element modulo multiplication by a square unit. -/
def squareClassMk {K : Type u} [Field K] (x : K) : SquareClass K :=
  Quotient.mk (squareClassSetoid K) x

/-- Multiplication by a square unit does not change a square class. -/
theorem squareClassMk_square_mul {K : Type u} [Field K] (x : K) (u : Kˣ) :
    squareClassMk ((u : K) ^ 2 * x) = squareClassMk x := by
  symm
  exact Quotient.sound ⟨u, rfl⟩

/- The source first defines the discriminant of an arbitrary bilinear form.
   `BilinForm.toMatrix` is Mathlib's canonical coordinate form of the map
   `V → V*`; taking its determinant gives the same square-class invariant. -/
/-- The discriminant square class of a finite-dimensional bilinear form. -/
noncomputable def bilinearFormDiscriminant
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : LinearMap.BilinForm K V) : SquareClass K :=
  squareClassMk ((Q.toMatrix (Module.finBasis K V)).det)

/-- The bilinear-form discriminant can be computed from any finite basis. -/
theorem bilinearFormDiscriminant_eq_of_basis
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : LinearMap.BilinForm K V)
    {n : ℕ} (b : Module.Basis (Fin n) K V) :
    bilinearFormDiscriminant K V Q = squareClassMk ((Q.toMatrix b).det) := by
  classical
  let hcard : Fintype.card (Fin n) = Module.finrank K V := by
    simpa using (Module.finrank_eq_card_basis b).symm
  let e : Fin n ≃ Fin (Module.finrank K V) := Fintype.equivFinOfCardEq hcard
  let b' := b.reindex e
  have hmatrix : Q.toMatrix b' =
      (Q.toMatrix b).submatrix e.symm e.symm := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, b', Module.Basis.reindex_apply]
  have hreindex : (Q.toMatrix b').det = (Q.toMatrix b).det := by
    rw [hmatrix]
    exact Matrix.det_submatrix_equiv_self e.symm (Q.toMatrix b)
  have hmat := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
    (Module.finBasis K V) b' Q
  have hdet := congrArg Matrix.det hmat
  have hu : IsUnit ((Module.finBasis K V).toMatrix b').det := by
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b' (Module.finBasis K V)]
    exact LinearEquiv.isUnit_det (LinearEquiv.refl K V) b' (Module.finBasis K V)
  let u : Kˣ := hu.unit
  have hchange :
      (Q.toMatrix b').det =
        (u : K) ^ 2 * (Q.toMatrix (Module.finBasis K V)).det := by
    simpa [Matrix.det_mul, Matrix.det_transpose, pow_two, mul_assoc, mul_comm,
      mul_left_comm, hu.unit_spec, u] using hdet.symm
  rw [bilinearFormDiscriminant]
  apply Quotient.sound
  refine ⟨u, ?_⟩
  calc
    (Q.toMatrix b).det = (Q.toMatrix b').det := hreindex.symm
    _ = (u : K) ^ 2 * (Q.toMatrix (Module.finBasis K V)).det := hchange

/-- A change of basis changes a bilinear-form discriminant representative by
    a square unit. -/
theorem bilinearFormDiscriminant_basis_change_is_square
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (Q : LinearMap.BilinForm K V)
    (b b' : Module.Basis (Fin n) K V) :
    ∃ u : Kˣ,
      (Q.toMatrix b').det = (u : K) ^ 2 * (Q.toMatrix b).det := by
  sorry

/-- The determinant criterion for a bilinear form is basis independent. -/
theorem bilinearFormDiscriminant_representative_ne_zero_iff_nondegenerate
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : LinearMap.BilinForm K V) :
    (Q.toMatrix (Module.finBasis K V)).det ≠ 0 ↔ Q.Nondegenerate := by
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
    (Module.finBasis K V)).symm

/-- The square-class discriminant is nonzero exactly when the form is
    nondegenerate. -/
theorem bilinearFormDiscriminant_ne_zero_iff_nondegenerate
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : LinearMap.BilinForm K V) :
    bilinearFormDiscriminant K V Q ≠ squareClassMk (0 : K) ↔ Q.Nondegenerate := by
  classical
  have hzero : ∀ x : K, squareClassMk x = squareClassMk (0 : K) ↔ x = 0 := by
    intro x
    constructor
    · intro h
      rcases Quotient.exact h with ⟨u, hu⟩
      have hu' : (u : K) ^ 2 ≠ 0 := pow_ne_zero _ (Units.ne_zero u)
      exact (mul_eq_zero.mp hu.symm).resolve_left hu'
    · intro hx
      subst x
      rfl
  have hzero' : ∀ x : K, squareClassMk x ≠ squareClassMk (0 : K) ↔ x ≠ 0 :=
    fun x => not_congr (hzero x)
  rw [bilinearFormDiscriminant_eq_of_basis (Q := Q) (Module.finBasis K V), hzero']
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Module.finBasis K V)).symm

/- The finite basis representative in `fieldDiscriminant` is independent of
   the basis after passing to `SquareClass`. -/
/-- A change of basis changes the discriminant by a square unit. -/
theorem discriminant_basis_change_is_square
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (b b' : Module.Basis (Fin n) K L) :
    ∃ u : Kˣ,
      Algebra.discr K b' = (u : K) ^ 2 * Algebra.discr K b := by
  classical
  have h := Algebra.discr_of_matrix_vecMul (A := K) (B := L) (b : Fin n → L)
    (b.toMatrix b')
  rw [Module.Basis.toMatrix_map_vecMul] at h
  have hu : IsUnit (b.toMatrix b').det := by
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b' b]
    exact LinearEquiv.isUnit_det (LinearEquiv.refl K L) b' b
  refine ⟨hu.unit, ?_⟩
  simpa [hu.unit_spec] using h

/-- The discriminant of a finite extension as a square class of its base
    field. -/
noncomputable def fieldDiscriminant
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : SquareClass K :=
  squareClassMk (Algebra.discr K (Module.finBasis K L))

/-- The discriminant class is represented by the discriminant of any basis
    indexed by the finite dimension. -/
theorem fieldDiscriminant_eq_of_fin_basis
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (b : Module.Basis (Fin (Module.finrank K L)) K L) :
    fieldDiscriminant K L = squareClassMk (Algebra.discr K b) := by
  rw [fieldDiscriminant]
  rcases discriminant_basis_change_is_square
      (K := K) (L := L) (Module.finBasis K L) b with ⟨u, hu⟩
  exact Quotient.sound ⟨u, hu⟩

/-- The field discriminant is the bilinear-form discriminant of the trace
    pairing. -/
theorem fieldDiscriminant_eq_traceForm_discriminant
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    fieldDiscriminant K L =
      bilinearFormDiscriminant K L (Algebra.traceForm K L) := by
  rw [fieldDiscriminant, bilinearFormDiscriminant]
  congr 1
  rw [Algebra.discr_def, Algebra.traceMatrix_of_basis]

/-- The discriminant of a basis is the determinant of its trace matrix. -/
theorem discriminant_eq_det_trace_matrix
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (b : Module.Basis (Fin n) K L) :
  Algebra.discr K b = (Algebra.traceMatrix K b).det :=
  Algebra.discr_def K b

/-- In matrix coordinates, the trace matrix has entries
    `Trace(b i * b j)`. -/
theorem trace_matrix_basis_entry
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (b : Module.Basis (Fin n) K L) (i j : Fin n) :
    Algebra.traceMatrix K b i j = Algebra.trace K L (b i * b j) := by
  rfl

/-- The discriminant is nonzero exactly for separable finite extensions. -/
theorem field_discriminant_representative_ne_zero_iff_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Algebra.discr K (Module.finBasis K L) ≠ 0 ↔ Algebra.IsSeparable K L := by
  rw [Algebra.discr_def, Algebra.traceMatrix_of_basis]
  rw [← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
  exact ((separable_iff_trace_nonzero_iff_trace_pairing_nondegenerate
    (K := K) (L := L)).1.trans
      (separable_iff_trace_nonzero_iff_trace_pairing_nondegenerate
        (K := K) (L := L)).2).symm

/-- The square-class discriminant is nonzero exactly for separable finite
    extensions. -/
theorem fieldDiscriminant_ne_zero_iff_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    fieldDiscriminant K L ≠ squareClassMk (0 : K) ↔ Algebra.IsSeparable K L := by
  have hsep := separable_iff_trace_nonzero_iff_trace_pairing_nondegenerate
    (K := K) (L := L)
  rw [fieldDiscriminant_eq_traceForm_discriminant,
    bilinearFormDiscriminant_ne_zero_iff_nondegenerate]
  exact (hsep.1.trans hsep.2).symm

/-! ## The quadratic discriminant exercise -/

/-- The characteristic-two purely inseparable case of the quadratic exercise. -/
def quadraticDiscriminantPurelyInseparableCase
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop :=
  fieldDiscriminant K L = squareClassMk (0 : K) ∧
    ringChar K = 2 ∧ IsPurelyInseparable K L ∧
      ∃ a : K, ∃ α : L,
        α ^ 2 = algebraMap K L a ∧
          IntermediateField.adjoin K ({α} : Set L) = ⊤

/-- The characteristic-two separable case of the quadratic exercise. -/
def quadraticDiscriminantSeparableCase
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop :=
  fieldDiscriminant K L = squareClassMk (1 : K) ∧
    ringChar K = 2 ∧ Algebra.IsSeparable K L

/-- The odd-characteristic case of the quadratic exercise. -/
def quadraticDiscriminantOddCharacteristicCase
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop :=
  ringChar K ≠ 2 ∧
    ∃ a : K,
      fieldDiscriminant K L = squareClassMk a ∧
        ¬ IsSquare a ∧
          ∃ α : L,
            α ^ 2 = algebraMap K L a ∧
              IntermediateField.adjoin K ({α} : Set L) = ⊤

/-- Exactly one of the three cases in the quadratic discriminant exercise
    occurs for a degree-two finite field extension. -/
theorem quadratic_discriminant_trichotomy
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdegree : Module.finrank K L = 2) :
    (quadraticDiscriminantPurelyInseparableCase K L ∨
        quadraticDiscriminantSeparableCase K L ∨
        quadraticDiscriminantOddCharacteristicCase K L) ∧
      ¬ (quadraticDiscriminantPurelyInseparableCase K L ∧
        quadraticDiscriminantSeparableCase K L) ∧
      ¬ (quadraticDiscriminantPurelyInseparableCase K L ∧
        quadraticDiscriminantOddCharacteristicCase K L) ∧
      ¬ (quadraticDiscriminantSeparableCase K L ∧
        quadraticDiscriminantOddCharacteristicCase K L) := by
  sorry

end

end Formalization.Books.Fields.Unit20
