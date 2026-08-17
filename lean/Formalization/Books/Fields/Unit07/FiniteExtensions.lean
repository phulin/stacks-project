import Formalization.Books.Fields.Unit06.FieldExtensions
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Data.Countable.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Tower
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Fields, Chapter 7: Finite extensions

The source writes field inclusions as `F / E`.  As in the preceding chapter,
this file uses Mathlib's canonical `Algebra` interface.  The degree is
`Module.rank`, and the source's finiteness condition is Mathlib's
`FiniteDimensional`/`Module.Finite` class.  Rational functions are represented
by `RatFunc`, simple algebraic extensions by `AdjoinRoot`, quadratic
extensions by `Algebra.IsQuadraticExtension`, and number fields by Mathlib's
existing `NumberField` class.

The source's finite linear relations in the rational-function example are
subsumed by the stronger family-level `LinearIndependent` declarations.  The
coefficient expansion and power-basis APIs likewise subsume the displayed
polynomial and spanning calculations.
-/

namespace Formalization.Books.Fields.Unit07

open scoped BigOperators

noncomputable section

universe u v w

/-! ## Degree and finite extensions -/

/- An algebra structure on a field extension supplies precisely the vector-space
   structure used in the opening sentence of the source. -/
/- A field extension has its canonical vector-space structure. -/
@[instance_reducible]
def field_extension_module
    (E F : Type*) [Field E] [Field F] [Algebra E F] : Module E F :=
  inferInstance

/- The scalar action in this module is multiplication in the target field,
   after mapping the scalar along the extension's algebra map. -/
/-- Scalars act on a field extension by multiplication in the larger field. -/
theorem field_extension_smul_eq_mul
    (E F : Type*) [Field E] [Field F] [Algebra E F] (x : E) (y : F) :
    x • y = algebraMap E F x * y :=
  Algebra.smul_def x y

/- The source's degree `[F : E]` is Mathlib's cardinal-valued dimension.
   Finite extensions are characterized by the separate `FiniteDimensional`
   predicate below, while `Module.rank` retains the value for infinite
   extensions. -/
/-- The degree of the extension `F/E`. -/
def fieldExtensionDegree (E F : Type*) [Field E] [AddCommGroup F] [Module E F] : Cardinal :=
  Module.rank E F

/-- The source's finite-extension condition, using Mathlib's canonical class. -/
abbrev FiniteFieldExtension (E F : Type*) [Field E] [Field F] [Algebra E F] :=
  FiniteDimensional E F

/- This is the exact cardinal formulation of the source's condition
   `[F : E] < ∞`. -/
/-- An extension is finite exactly when its degree is below the countable cardinal. -/
theorem finite_extension_iff_degree_lt_aleph0
    (E F : Type*) [Field E] [Field F] [Algebra E F] :
    FiniteFieldExtension E F ↔ fieldExtensionDegree E F < Cardinal.aleph0 := by
  change Module.Finite E F ↔ Module.rank E F < Cardinal.aleph0
  exact (Module.rank_lt_aleph0_iff (R := E) (M := F)).symm

/- The source's basis `1, i` is Mathlib's `Complex.basisOneI`; its values are
   recorded by the existing theorem `Complex.coe_basisOneI`. -/
/-- The complex extension of the reals has degree two and a two-element basis. -/
theorem complex_extension_example :
    Nonempty (Module.Basis (Fin 2) ℝ ℂ) ∧ fieldExtensionDegree ℝ ℂ = 2 := by
  refine ⟨⟨Complex.basisOneI⟩, ?_⟩
  exact Complex.rank_real_complex

/- The basis API also exposes the actual two values named in the source. -/
/-- The complex basis over the reals has values `1` and `I`. -/
theorem complex_basis_one_I :
    ⇑Complex.basisOneI = ![1, Complex.I] :=
  Complex.coe_basisOneI

/- A finite extension at the bottom of a tower is finite over every larger
   intermediate field.  This is Mathlib's `Module.Finite.right`, not a new
   tower-finiteness construction. -/
/-- In a tower `K/E/F`, finiteness of `K/F` implies finiteness of `K/E`. -/
theorem finite_extension_over_middle
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [Algebra.IsAlgebraic F E] [Algebra.IsAlgebraic E K]
    [FiniteDimensional F K] :
    FiniteDimensional E K :=
  Module.Finite.right F E K

/-! ## Rational functions -/

/-- The integer powers of the rational-function indeterminate are linearly independent. -/
theorem rational_function_integer_powers_linearIndependent (k : Type u) [Field k] :
    LinearIndependent k (fun n : ℤ => (RatFunc.X : RatFunc k) ^ n) := by
  sorry

/-- The rational-function field is not a finite extension of its coefficient field. -/
theorem rational_function_not_finite (k : Type u) [Field k] :
    ¬ FiniteFieldExtension k (RatFunc k) := by
  sorry

/-- The reciprocal family indexed by the coefficient field is linearly independent. -/
theorem rational_function_reciprocal_family_linearIndependent (k : Type u) [Field k] :
    LinearIndependent k (fun α : k =>
      ((RatFunc.X : RatFunc k) - algebraMap k (RatFunc k) α)⁻¹) := by
  sorry

/-- The reciprocal family gives a lower bound on the cardinal-valued dimension. -/
theorem rational_function_rank_ge_cardinal (k : Type u) [Field k] :
    Cardinal.mk k ≤ Module.rank k (RatFunc k) := by
  sorry

/-- If the coefficient field is uncountable, so is the dimension of `RatFunc k`. -/
theorem rational_function_uncountable_dimensional (k : Type u) [Field k]
    [Uncountable k] :
    Cardinal.aleph0 < Module.rank k (RatFunc k) := by
  sorry

/- The source's finite nonzero relations among distinct reciprocal functions
   are exactly the finite-relation consequence of the preceding family-level
   linear independence statement. -/

/-! ## Finite generation -/

/-- A finite field extension is finitely generated as a field extension. -/
theorem finite_extension_is_finitely_generated
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [FiniteDimensional E F] :
    ∃ S : Set F, S.Finite ∧ IntermediateField.adjoin E S = ⊤ := by
  sorry

/-- The rational-function field is generated by its indeterminate. -/
theorem rational_function_is_finitely_generated (k : Type u) [Field k] :
    IntermediateField.adjoin k ({RatFunc.X} : Set (RatFunc k)) = ⊤ := by
  sorry

/-- The rational-function example witnesses that finite generation does not imply finiteness. -/
theorem rational_function_finitely_generated_but_not_finite (k : Type u) [Field k] :
    (IntermediateField.adjoin k ({RatFunc.X} : Set (RatFunc k)) = ⊤) ∧
      ¬ FiniteFieldExtension k (RatFunc k) :=
  ⟨rational_function_is_finitely_generated k, rational_function_not_finite k⟩

/-! ## Simple algebraic extensions -/

/- This is the canonical finite coefficient expansion corresponding to the
   source's displayed equation `P = a_d t^d + ... + a_0`. -/
/-- Every polynomial is the finite sum of its coefficient monomials. -/
theorem polynomial_coefficient_expansion {k : Type*} [Semiring k]
    (P : Polynomial k) :
    P = ∑ i ∈ P.support, Polynomial.C (P.coeff i) * Polynomial.X ^ i :=
  P.as_sum_support_C_mul_X_pow

/- For an irreducible polynomial, the coefficient at the displayed top
   degree is nonzero, which is the source's `a_d ≠ 0`. -/
/-- The leading coefficient of an irreducible polynomial over a field is nonzero. -/
theorem simple_algebraic_extension_leading_coefficient_ne_zero
    {k : Type u} [Field k] {P : Polynomial k} (hP : Irreducible P) :
    P.leadingCoeff ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr hP.ne_zero

/- The quotient relation used in the source is already the defining root
   relation of `AdjoinRoot`. -/
/-- The distinguished root of an `AdjoinRoot` satisfies its defining polynomial. -/
theorem adjoinRoot_root_satisfies_polynomial {k : Type*} [CommRing k]
    (P : Polynomial k) :
    P.eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P) = 0 :=
  AdjoinRoot.eval₂_root P

/-- The powers `1, root P, ..., root P ^ (d - 1)` form the canonical power basis. -/
theorem simple_algebraic_extension_power_basis
    {k : Type u} [Field k] {P : Polynomial k} (hP : Irreducible P) :
    ∀ i : Fin P.natDegree,
      (AdjoinRoot.powerBasis hP.ne_zero).basis i =
        (AdjoinRoot.root P) ^ (i : ℕ) := by
  exact (AdjoinRoot.powerBasis hP.ne_zero).basis_eq_pow

/-- The degree of a simple algebraic extension is the polynomial degree. -/
theorem simple_algebraic_extension_degree
    {k : Type u} [Field k] {P : Polynomial k} (hP : Irreducible P) :
    Module.finrank k (AdjoinRoot P) = P.natDegree := by
  exact (AdjoinRoot.powerBasis hP.ne_zero).finrank

/-- The same degree formula expressed with the chapter's extension-degree definition. -/
theorem simple_algebraic_extension_field_degree
    {k : Type u} [Field k] {P : Polynomial k} (hP : Irreducible P) :
    fieldExtensionDegree k (AdjoinRoot P) = (P.natDegree : Cardinal) := by
  have hfinite : Module.Finite k (AdjoinRoot P) :=
    (AdjoinRoot.powerBasis hP.ne_zero).finite
  calc
    fieldExtensionDegree k (AdjoinRoot P) =
        Module.rank k (AdjoinRoot P) := rfl
    _ = (Module.finrank k (AdjoinRoot P) : Cardinal) :=
      (@Module.finrank_eq_rank k (AdjoinRoot P) _ _ _ _ hfinite).symm
    _ = (P.natDegree : Cardinal) := by
      rw [(AdjoinRoot.powerBasis hP.ne_zero).finrank, AdjoinRoot.powerBasis_dim]

/-! ## Quadratic extensions -/

/-- A nonsquare gives an irreducible quadratic polynomial. -/
theorem nonsquare_quadratic_polynomial_irreducible
    {k : Type u} [Field k] {α : k} (hα : ¬ IsSquare α) :
    Irreducible (Polynomial.X ^ 2 - Polynomial.C α) := by
  sorry

/-- The quotient by a nonsquare quadratic polynomial is a field. -/
theorem nonsquare_quadratic_extension_is_field
    {k : Type u} [Field k] {α : k} (hα : ¬ IsSquare α) :
    IsField (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C α)) := by
  exact Formalization.Books.Fields.Unit06.adjoinRoot_isField_of_irreducible
    (nonsquare_quadratic_polynomial_irreducible hα)

/-- The nonsquare quadratic construction has degree two. -/
theorem nonsquare_quadratic_extension_degree
    {k : Type u} [Field k] {α : k} (hα : ¬ IsSquare α) :
    fieldExtensionDegree k (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C α)) =
      (2 : Cardinal) := by
  sorry

/-- The nonsquare quadratic construction is a Mathlib quadratic extension. -/
theorem nonsquare_quadratic_is_quadratic_extension
    {k : Type u} [Field k] {α : k} (hα : ¬ IsSquare α) :
    Algebra.IsQuadraticExtension k (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C α)) := by
  sorry

/-! ## Multiplicativity and number fields -/

/-- Degree is multiplicative in a tower of field extensions. -/
theorem field_extension_degree_multiplicative
    {k : Type u} {E F : Type v} [Field k] [Field E] [Field F]
    [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F] :
    fieldExtensionDegree k F =
      fieldExtensionDegree E F * fieldExtensionDegree k E := by
  change Module.rank k F = Module.rank E F * Module.rank k E
  calc
    Module.rank k F = Module.rank k E * Module.rank E F :=
      (rank_mul_rank k E F).symm
    _ = Module.rank E F * Module.rank k E := mul_comm _ _

/- Mathlib's `NumberField` is exactly the source's definition, so no parallel
   number-field predicate is introduced. -/
/-- A Mathlib number field has characteristic zero and finite degree over `ℚ`. -/
theorem number_field_spec (K : Type u) [Field K] [NumberField K] :
    CharZero K ∧ FiniteDimensional ℚ K :=
  ⟨inferInstance, inferInstance⟩

/-- Characteristic zero and finite degree over `ℚ` give the canonical number-field class. -/
theorem number_field_of_charZero_of_finiteDimensional
    (K : Type u) [Field K] [CharZero K] [FiniteDimensional ℚ K] :
    NumberField K :=
  { to_charZero := inferInstance
    to_finiteDimensional := inferInstance }

end

end Formalization.Books.Fields.Unit07
