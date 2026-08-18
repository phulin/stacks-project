import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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

private theorem charpoly_blockDiagonal
    {K o n : Type*} [Field K] [Fintype o] [DecidableEq o]
    [Fintype n] [DecidableEq n] (M : o → Matrix n n K) :
    (Matrix.blockDiagonal M).charpoly = ∏ i, (M i).charpoly := by
  rw [Matrix.charpoly]
  have hcm :
      (Matrix.blockDiagonal M).charmatrix =
        Matrix.blockDiagonal (fun i => (M i).charmatrix) := by
    apply Matrix.ext
    intro ⟨i, k⟩ ⟨j, l⟩
    by_cases hkl : k = l
    · subst l
      simp [Matrix.charmatrix_apply, Matrix.blockDiagonal, Matrix.diagonal_apply]
    · simp [Matrix.charmatrix_apply, Matrix.blockDiagonal, Matrix.diagonal_apply, hkl]
  rw [hcm, Matrix.det_blockDiagonal]
  rfl

/-- The characteristic polynomial of multiplication is a power of the
    minimal polynomial, with the expected degree relation. -/
theorem characteristic_polynomial_multiplication_eq_pow_minpoly
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (α : L) :
    ∃ e : ℕ,
      e * (minpoly K α).natDegree = Module.finrank K L ∧
        (Algebra.lmul K L α).charpoly = (minpoly K α) ^ e := by
  let F := IntermediateField.adjoin K ({α} : Set L)
  let hαint : IsIntegral K α := IsIntegral.of_finite K α
  let pb := IntermediateField.adjoin.powerBasis hαint
  let c := Module.finBasis F L
  let e := Module.finrank F L
  have hpbdim : pb.dim = (minpoly K α).natDegree := by
    simpa [pb, IntermediateField.minpoly_gen] using (PowerBasis.natDegree_minpoly pb)
  have hdim : e * (minpoly K α).natDegree = Module.finrank K L := by
    dsimp [e]
    calc
      Module.finrank F L * (minpoly K α).natDegree =
          (minpoly K α).natDegree * Module.finrank F L := Nat.mul_comm _ _
      _ = pb.dim * Module.finrank F L := by rw [hpbdim]
      _ = Module.finrank K L := by
        rw [← PowerBasis.finrank pb]
        simpa [F] using
          (Module.finrank_mul_finrank K (IntermediateField.adjoin K ({α} : Set L)) L)
  have hm := Algebra.smulTower_leftMulMatrix_algebraMap pb.basis c pb.gen
  have halpha : (algebraMap F L) pb.gen = α := by rfl
  have hgen : (pb.gen : L) = α := by rfl
  have hmat : Algebra.leftMulMatrix (pb.basis.smulTower c) α =
      Matrix.blockDiagonal (fun _ => Algebra.leftMulMatrix pb.basis pb.gen) := by
    simpa [F, hgen] using hm
  refine ⟨e, hdim, ?_⟩
  rw [← LinearMap.charpoly_toMatrix (Algebra.lmul K L α) (pb.basis.smulTower c)]
  rw [← Algebra.leftMulMatrix_apply]
  rw [hmat, charpoly_blockDiagonal]
  rw [charpoly_leftMulMatrix]
  simp [e, pb, IntermediateField.minpoly_gen]

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
  subst P
  let F := IntermediateField.adjoin K ({α} : Set L)
  let e : ℕ := Module.finrank F L
  have hαint : IsIntegral K α := IsIntegral.of_finite K α
  have hdeg : e * (minpoly K α).natDegree = Module.finrank K L := by
    have hdim := Module.finrank_mul_finrank K F L
    rw [IntermediateField.adjoin.finrank hαint] at hdim
    simpa [e, F, Module.finrank, Nat.mul_comm] using hdim
  have hdeg' : Module.finrank F L * (minpoly K α).natDegree = Module.finrank K L := by
    simpa [e] using hdeg
  refine ⟨e, hdeg, ?_, ?_⟩
  · rw [Algebra.norm_eq_norm_adjoin K α]
    let pb := IntermediateField.adjoin.powerBasis hαint
    have hp := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    have hgen : pb.gen = IntermediateField.AdjoinSimple.gen K α := by
      rfl
    have hdim : pb.dim = (minpoly K α).natDegree := by
      rfl
    have hcoeff : (minpoly K pb.gen).coeff 0 = (minpoly K α).coeff 0 := by
      simp [pb, IntermediateField.minpoly_gen]
    rw [← hgen, hp, hdim, hcoeff, mul_pow, ← pow_mul, Nat.mul_comm, hdeg']
  · rw [_root_.trace_eq_finrank_mul_minpoly_nextCoeff (K := K) (L := L) α]
    simp [e, F, mul_neg, mul_comm]

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
  classical
  let bK := Module.finBasis K L
  let bV := Module.finBasis L V
  refine ⟨?_, LinearMap.det_restrictScalars (R := K) (S := L) (A := V) (f := φ)⟩
  rw [LinearMap.trace_eq_matrix_trace K (bK.smulTower' bV)]
  rw [LinearMap.restrictScalars_toMatrix]
  rw [Algebra.trace_eq_matrix_trace bK]
  rw [LinearMap.trace_eq_matrix_trace L bV]
  simp [Matrix.trace, Algebra.leftMulMatrix_apply]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [Matrix.sum_apply]
  rw [Finset.sum_comm]

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
  apply field_trace_eq_zero_of_not_separable
  intro hsep
  let F := IntermediateField.adjoin K ({α} : Set L)
  letI : Fact p.Prime := ⟨hp⟩
  have hpi : IsPurelyInseparable K F := by
    change IsPurelyInseparable K (IntermediateField.adjoin K ({α} : Set L))
    exact (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem
      (F := K) (E := L) p).2 ⟨1, by simpa using hαp⟩
  letI := hpi
  have hsepF : Algebra.IsSeparable K F := by
    change Algebra.IsSeparable K (IntermediateField.adjoin K ({α} : Set L))
    exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := L)).2 (Algebra.IsSeparable.isSeparable K α)
  letI := hsepF
  have hbot := IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable F
  have ha : α ∈ F := IntermediateField.subset_adjoin K _ (Set.mem_singleton α)
  have harange : α ∈ (algebraMap K L).range := by
    apply IntermediateField.mem_bot.mp
    exact hbot ▸ ha
  apply hα
  exact harange

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
  classical
  letI := b.finiteDimensional_of_finite
  have hb := bilinearFormDiscriminant_eq_of_basis (Q := Q) b
  have hb' := bilinearFormDiscriminant_eq_of_basis (Q := Q) b'
  have hclass : squareClassMk ((Q.toMatrix b).det) =
      squareClassMk ((Q.toMatrix b').det) := by
    rw [← hb, ← hb']
  rcases Quotient.exact hclass with ⟨u, hu⟩
  exact ⟨u, hu⟩

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
  classical
  by_cases hsep : Algebra.IsSeparable K L
  · letI := hsep
    let pb := Field.powerBasisOfFiniteOfSeparable K L
    have hpbdim : pb.dim = 2 := by
      rw [← PowerBasis.finrank pb, hdegree]
    have htrace := Algebra.traceForm_toMatrix_powerBasis pb
    have htrace_one : Algebra.trace K L 1 = 2 := by
      rw [show (1 : L) = algebraMap K L 1 by simp, Algebra.trace_algebraMap]
      simp [hdegree]
    have hPdeg : (minpoly K pb.gen).natDegree = 2 := by
      simpa [PowerBasis.natDegree_minpoly pb] using hpbdim
    have hPform : minpoly K pb.gen =
        X ^ 2 + C ((minpoly K pb.gen).coeff 1) * X +
          C ((minpoly K pb.gen).coeff 0) := by
      apply Polynomial.ext
      intro n
      by_cases hn : n = 0
      · subst n
        simp
      by_cases hn1 : n = 1
      · subst n
        simp
      by_cases hn2 : n = 2
      · subst n
        have hlead : (minpoly K pb.gen).coeff 2 = 1 := by
          calc
            (minpoly K pb.gen).coeff 2 =
                (minpoly K pb.gen).coeff (minpoly K pb.gen).natDegree := by
                  rw [hPdeg]
            _ = (minpoly K pb.gen).leadingCoeff :=
              Polynomial.coeff_natDegree
            _ = 1 := (minpoly.monic (Algebra.IsIntegral.isIntegral pb.gen)).leadingCoeff
        simpa [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hlead
      have hnlt : 2 < n := by omega
      have hn1' : 1 ≠ n := Ne.symm hn1
      have hn2' : 2 ≠ n := Ne.symm hn2
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      · simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
        simp [hn, hn1, hn2, hn1', hn2']
      rw [hPdeg]
      exact hnlt
    obtain ⟨e, he, hnorm, htr⟩ :=
      field_trace_and_norm_from_minpoly (K := K) (L := L) pb.gen
        (minpoly K pb.gen) rfl
    have he' : e = 1 := by
      have he'' : e * 2 = 2 := by simpa [hPdeg, hdegree] using he
      omega
    subst e
    have htr' : Algebra.trace K L pb.gen = -(minpoly K pb.gen).nextCoeff := by
      simpa using htr
    have hnorm' : Algebra.norm K pb.gen = (minpoly K pb.gen).coeff 0 := by
      simpa [hdegree] using hnorm
    have hnext : (minpoly K pb.gen).nextCoeff =
        (minpoly K pb.gen).coeff 1 := by
      rw [Polynomial.nextCoeff_of_natDegree_pos]
      · rw [hPdeg]
      · rw [hPdeg]
        norm_num
    have hroot : pb.gen ^ 2 +
        algebraMap K L ((minpoly K pb.gen).coeff 1) * pb.gen +
          algebraMap K L ((minpoly K pb.gen).coeff 0) = 0 := by
      have hroot' := minpoly.aeval K pb.gen
      rw [hPform] at hroot'
      simpa [aeval_def, Algebra.smul_def, mul_add, add_mul] using hroot'
    have hroot_trace := congrArg (Algebra.trace K L) hroot
    have htrace_sq : Algebra.trace K L (pb.gen * pb.gen) =
        (Algebra.trace K L pb.gen) ^ 2 - 2 * Algebra.norm K pb.gen := by
      rw [← Algebra.smul_def] at hroot_trace
      simp only [map_add, map_zero, map_smul, field_trace_algebraMap] at hroot_trace
      simp [hdegree] at hroot_trace
      rw [pow_two] at hroot_trace ⊢
      rw [htr', hnext] at hroot_trace
      rw [htr', hnext, hnorm']
      ring_nf at hroot_trace ⊢
      linear_combination hroot_trace
    have hdisc' : Algebra.discr K pb.basis =
        (Algebra.trace K L pb.gen) ^ 2 - 4 * Algebra.norm K pb.gen := by
      rw [Algebra.discr_def, Algebra.traceMatrix_of_basis, htrace, hpbdim]
      simp [Matrix.det_fin_two]
      have htrace_sq' : Algebra.trace K L (pb.gen ^ 2) =
          (Algebra.trace K L pb.gen) ^ 2 - 2 * Algebra.norm K pb.gen := by
        simpa only [pow_two] using htrace_sq
      rw [htrace_one, htrace_sq']
      ring
    have hpbfd : fieldDiscriminant K L = squareClassMk (Algebra.discr K pb.basis) := by
      let f : Fin pb.dim ≃ Fin (Module.finrank K L) :=
        finCongr (PowerBasis.finrank pb).symm
      rw [fieldDiscriminant]
      rcases discriminant_basis_change_is_square
          (K := K) (L := L) (Module.finBasis K L) (pb.basis.reindex f) with ⟨u, hu⟩
      apply Quotient.sound
      refine ⟨u, ?_⟩
      calc
        Algebra.discr K pb.basis = Algebra.discr K (pb.basis.reindex f) :=
          by simpa only [Module.Basis.coe_reindex] using
            (Algebra.discr_reindex K pb.basis f).symm
        _ = (u : K) ^ 2 * Algebra.discr K (Module.finBasis K L) := hu
    by_cases hchar : ringChar K = 2
    · letI : CharP K 2 := ringChar.of_eq hchar
      have hdisc_ne : Algebra.discr K pb.basis ≠ 0 :=
        Algebra.discr_not_zero_of_basis K pb.basis
      have htne : Algebra.trace K L pb.gen ≠ 0 := by
        intro ht
        apply hdisc_ne
        rw [hdisc', ht]
        have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
        have hfour : (4 : K) = 0 := by
          calc
            (4 : K) = 2 + 2 := by norm_num
            _ = 0 := by rw [htwo]; simp
        rw [hfour]
        simp
      let u : Kˣ := Units.mk0 (Algebra.trace K L pb.gen) htne
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have hfour : (4 : K) = 0 := by
        calc
          (4 : K) = 2 + 2 := by norm_num
          _ = 0 := by rw [htwo]; simp
      have hclass : squareClassMk (Algebra.discr K pb.basis) =
          squareClassMk (1 : K) := by
        rw [hdisc', hfour]
        simp only [zero_mul, sub_zero]
        change squareClassMk ((u : K) ^ 2) = squareClassMk (1 : K)
        simpa only [mul_one] using squareClassMk_square_mul (1 : K) u
      have hfd : fieldDiscriminant K L = squareClassMk (1 : K) :=
        hpbfd.trans hclass
      refine ⟨Or.inr (Or.inl ?_), ?_, ?_, ?_⟩
      · exact ⟨hfd, hchar, hsep⟩
      · intro h
        rcases h with ⟨h0, h1⟩
        have hzero : squareClassMk (0 : K) ≠ squareClassMk (1 : K) := by
          intro hz
          rcases Quotient.exact hz with ⟨u, hu⟩
          simpa using hu
        exact hzero (h0.1.symm.trans h1.1)
      · intro h
        exact h.2.1 h.1.2.1
      · intro h
        exact h.2.1 h.1.2.1
    · have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
      let c1 : K := (minpoly K pb.gen).coeff 1
      let d : K := Algebra.discr K pb.basis
      let beta : L := (2 : K) • pb.gen + algebraMap K L c1
      have hd : d = c1 ^ 2 - 4 * (minpoly K pb.gen).coeff 0 := by
        dsimp [d, c1]
        rw [hdisc', htr', hnext, hnorm']
        ring
      have hbeta_sq : beta ^ 2 = algebraMap K L d := by
        have hbeta_sq' := hroot
        dsimp [beta, c1] at hbeta_sq' ⊢
        rw [Algebra.smul_def] at ⊢
        rw [hd]
        simp only [map_sub, map_mul, map_pow]
        have hmaptwo : algebraMap K L (2 : K) = (2 : L) := by
          simp only [map_ofNat]
        have hmapfour : algebraMap K L (4 : K) = (4 : L) := by
          simp only [map_ofNat]
        rw [hmaptwo, hmapfour]
        ring_nf at hbeta_sq' ⊢
        linear_combination (4 : L) * hbeta_sq'
      have hpbtop : IntermediateField.adjoin K ({pb.gen} : Set L) = ⊤ := by
        apply (Field.primitive_element_iff_minpoly_natDegree_eq K pb.gen).2
        simpa [hPdeg, hdegree]
      let G := IntermediateField.adjoin K ({beta} : Set L)
      have hbeta_mem : beta ∈ G :=
        IntermediateField.subset_adjoin K _ (Set.mem_singleton beta)
      have hc1_mem : algebraMap K L c1 ∈ G := G.algebraMap_mem c1
      have hgen_mem : pb.gen ∈ G := by
        have hdiff := G.sub_mem hbeta_mem hc1_mem
        have hsmul := G.smul_mem hdiff (x := (2 : K)⁻¹)
        have htwoL : algebraMap K L (2 : K) ≠ 0 := by
          intro hz
          apply htwo
          apply (algebraMap K L).injective
          simpa using hz
        simpa [G, beta, Algebra.smul_def, map_mul, map_inv₀,
          ← mul_assoc, inv_mul_cancel₀ htwoL] using hsmul
      have hGtop : G = ⊤ := by
        apply top_unique
        rw [← hpbtop]
        exact (IntermediateField.adjoin_simple_le_iff).2 hgen_mem
      have hgen_not_mem : pb.gen ∉ (algebraMap K L).range := by
        intro hgenrange
        have hbotmem : pb.gen ∈ (⊥ : IntermediateField K L) :=
          IntermediateField.mem_bot.mpr hgenrange
        have hle : IntermediateField.adjoin K ({pb.gen} : Set L) ≤
            (⊥ : IntermediateField K L) :=
          (IntermediateField.adjoin_le_iff).2 (by
            rintro x rfl
            exact hbotmem)
        have htopbot : (⊤ : IntermediateField K L) ≤ ⊥ := by
          simpa [hpbtop] using hle
        have heq : (⊥ : IntermediateField K L) = ⊤ :=
          le_antisymm bot_le htopbot
        have hfin :=
          (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).mp heq
        omega
      have hd_nonsquare : ¬ IsSquare d := by
        intro hsquare
        rcases hsquare with ⟨c, hc⟩
        have hprod : (beta - algebraMap K L c) *
            (beta + algebraMap K L c) = 0 := by
          calc
            (beta - algebraMap K L c) * (beta + algebraMap K L c) =
                beta ^ 2 - (algebraMap K L c) ^ 2 := by ring
            _ = algebraMap K L d - algebraMap K L (c ^ 2) := by
              rw [hbeta_sq, map_pow]
            _ = 0 := by rw [hc]; ring
        rcases mul_eq_zero.mp hprod with hminus | hplus
        · have hbeq : beta = algebraMap K L c := sub_eq_zero.mp hminus
          have hgen_eq : pb.gen = (2 : K)⁻¹ •
              (algebraMap K L (c - c1)) := by
            dsimp [beta] at hbeq
            have hrel : (2 : K) • pb.gen = algebraMap K L (c - c1) := by
              rw [Algebra.smul_def] at hbeq ⊢
              simp only [map_sub]
              linear_combination hbeq
            calc
              pb.gen = ((2 : K)⁻¹ * 2) • pb.gen := by
                rw [inv_mul_cancel₀ htwo, one_smul]
              _ = (2 : K)⁻¹ • ((2 : K) • pb.gen) := by rw [smul_smul]
              _ = (2 : K)⁻¹ • algebraMap K L (c - c1) := by rw [hrel]
          apply hgen_not_mem
          refine ⟨(2 : K)⁻¹ * (c - c1), ?_⟩
          simpa [Algebra.smul_def, map_mul, map_sub, inv_mul_cancel₀ htwo] using hgen_eq.symm
        · have hbeq : beta = -algebraMap K L c := by
            exact eq_neg_of_add_eq_zero_left hplus
          have hgen_eq : pb.gen = (2 : K)⁻¹ •
              (algebraMap K L (-c - c1)) := by
            dsimp [beta] at hbeq
            have hrel : (2 : K) • pb.gen = algebraMap K L (-c - c1) := by
              rw [Algebra.smul_def] at hbeq ⊢
              simp only [map_sub, map_neg]
              linear_combination hbeq
            calc
              pb.gen = ((2 : K)⁻¹ * 2) • pb.gen := by
                rw [inv_mul_cancel₀ htwo, one_smul]
              _ = (2 : K)⁻¹ • ((2 : K) • pb.gen) := by rw [smul_smul]
              _ = (2 : K)⁻¹ • algebraMap K L (-c - c1) := by rw [hrel]
          apply hgen_not_mem
          refine ⟨(2 : K)⁻¹ * (-c - c1), ?_⟩
          simpa [Algebra.smul_def, map_mul, map_sub, inv_mul_cancel₀ htwo] using hgen_eq.symm
      have hfd : fieldDiscriminant K L = squareClassMk d := by
        simpa [d] using hpbfd
      refine ⟨Or.inr (Or.inr ?_), ?_, ?_, ?_⟩
      · exact ⟨hchar, d, hfd, hd_nonsquare, beta, hbeta_sq, hGtop⟩
      · intro h
        have hzero : squareClassMk (0 : K) ≠ squareClassMk (1 : K) := by
          intro hz
          rcases Quotient.exact hz with ⟨u, hu⟩
          simpa using hu
        exact hzero (h.1.1.symm.trans h.2.1)
      · intro h
        exact h.2.1 h.1.2.1
      · intro h
        exact h.2.1 h.1.2.1
  · have hfd : fieldDiscriminant K L = squareClassMk (0 : K) := by
      by_contra hn
      exact hsep ((fieldDiscriminant_ne_zero_iff_separable (K := K) (L := L)).mp hn)
    have hdiv : Field.finSepDegree K L ∣ 2 := by
      simpa [hdegree] using Field.finSepDegree_dvd_finrank K L
    have hfinsep : Field.finSepDegree K L = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
      · exact hone
      · have hprod := Field.finSepDegree_mul_finInsepDegree K L
        rw [htwo] at hprod
        have hfininsep : Field.finInsepDegree K L = 1 := by
          omega
        have hsep' : Algebra.IsSeparable K L :=
          (isSeparable_iff_finInsepDegree_eq_one (F := K) (K := L)).2 hfininsep
        exact (hsep hsep').elim
    have hpi : IsPurelyInseparable K L :=
      (isPurelyInseparable_iff_finSepDegree_eq_one (F := K) (E := L)).2 hfinsep
    letI := hpi
    obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow K L (ringExpChar K)
    rw [hdegree] at hn
    have hq : ringExpChar K = 2 := by
      have hpow : ringExpChar K ^ n = 2 := hn.symm
      exact (Nat.Prime.pow_eq_iff Nat.prime_two).mp hpow |>.1
    have hchar : ringChar K = 2 := by
      dsimp [ringExpChar] at hq
      omega
    letI : CharP K 2 := ringChar.of_eq hchar
    have hbotne : (⊥ : IntermediateField K L) ≠ ⊤ := by
      intro heq
      have hfin :=
        (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).mp heq
      omega
    obtain ⟨α, -, hαbot⟩ :=
      SetLike.exists_of_lt (lt_of_le_of_ne bot_le hbotne)
    have hG : IntermediateField.adjoin K ({α} : Set L) = ⊤ := by
      have hprime : Nat.Prime (Module.finrank K L) := by
        simpa [hdegree] using Nat.prime_two
      rcases
          (IntermediateField.isSimpleOrder_of_finrank_prime K L hprime).eq_bot_or_eq_top
            (IntermediateField.adjoin K ({α} : Set L)) with hbot | htop
      · exfalso
        apply hαbot
        rw [← hbot]
        exact IntermediateField.subset_adjoin K _ (Set.mem_singleton α)
      · exact htop
    have hmindeg : (minpoly K α).natDegree = 2 := by
      have hminrank :=
        IntermediateField.adjoin.finrank (K := K) (L := L) (x := α)
          (Algebra.IsIntegral.isIntegral α)
      calc
        (minpoly K α).natDegree = Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) :=
          hminrank.symm
        _ = Module.finrank K L := by
          rw [hG]
          exact IntermediateField.finrank_top' (F := K) (E := L)
        _ = 2 := hdegree
    obtain ⟨m, y, hmin⟩ :=
      IsPurelyInseparable.minpoly_eq_X_pow_sub_C K 2 α
    have hpow : 2 ^ m = 2 := by
      calc
        2 ^ m = (X ^ 2 ^ m - C y).natDegree := by simp
        _ = (minpoly K α).natDegree := by rw [hmin]
        _ = 2 := hmindeg
    have hm : m = 1 := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hpow |>.2
    have hroot := minpoly.aeval K α
    rw [hmin, hm] at hroot
    have hαsq : α ^ 2 = algebraMap K L y := by
      have hroot' : α ^ 2 - algebraMap K L y = 0 := by
        simpa [aeval_def, Algebra.smul_def] using hroot
      exact sub_eq_zero.mp hroot'
    have hpure : quadraticDiscriminantPurelyInseparableCase K L := by
      exact ⟨hfd, hchar, hpi, y, α, hαsq, hG⟩
    refine ⟨Or.inl hpure, ?_, ?_, ?_⟩
    · intro h
      have hzero : squareClassMk (0 : K) ≠ squareClassMk (1 : K) := by
        intro hz
        rcases Quotient.exact hz with ⟨u, hu⟩
        simpa using hu
      exact hzero (hpure.1.symm.trans h.2.1)
    · intro h
      exact h.2.1 hpure.2.1
    · intro h
      exact hsep h.1.2.2

end

end Formalization.Books.Fields.Unit20
