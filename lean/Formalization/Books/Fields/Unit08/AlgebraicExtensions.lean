import Formalization.Books.Fields.Unit07.FiniteExtensions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Fields, Chapter 8: Algebraic extensions

The source uses the phrase “algebraic over” for the existence of a nonzero
annihilating polynomial.  Mathlib's `IsAlgebraic` and `Algebra.IsAlgebraic`
are exactly those definitions, so this chapter keeps the canonical APIs
instead of introducing parallel predicates.  A field extension is represented
by an `Algebra` instance, and `k(α₁, ..., αₙ)` is represented by
`IntermediateField.adjoin k`.

The source's compact-Riemann-surface example refers to a function-field model
that is not present in this project.  The available `RatFunc` theorem is
recorded as the corresponding formal function-field example; the missing
Riemann-surface model is explicitly accounted for at that point below.
-/

namespace Formalization.Books.Fields.Unit08

noncomputable section

universe u v

/-! ## Algebraic elements and simple extensions -/

/- `IsAlgebraic` is Mathlib's source-faithful definition of an algebraic
   element: a nonzero polynomial evaluates to zero. -/
/-- The polynomial formulation of being algebraic over a ring. -/
theorem algebraic_element_iff_exists_nonzero_polynomial
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (α : A) :
    IsAlgebraic R α ↔
      ∃ p : Polynomial R, p ≠ 0 ∧ Polynomial.aeval α p = 0 :=
  Iff.rfl

/- `Algebra.IsAlgebraic` is the corresponding assertion that every element
   of the extension is algebraic. -/
/-- An algebraic extension is one whose elements are all algebraic. -/
theorem algebraic_extension_iff_all_elements_algebraic
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    Algebra.IsAlgebraic R A ↔ ∀ α : A, IsAlgebraic R α :=
  Algebra.isAlgebraic_def

/- The source's dichotomy into a rational function extension or an irreducible
   polynomial quotient is supplied by the preceding chapter's
   `simple_extension_classification`.  The following declarations expose the
   two canonical simple-extension presentations for an individual element. -/
/-- Every element is either algebraic or transcendental over the base field. -/
theorem simple_extension_algebraic_or_transcendental
    {F E : Type*} [Field F] [Field E] [Algebra F E] (α : E) :
    IsAlgebraic F α ∨ Transcendental F α := by
  by_cases hα : IsAlgebraic F α
  · exact Or.inl hα
  · exact Or.inr hα

/-- The minimal polynomial of an algebraic element is irreducible. -/
theorem simple_extension_minpoly_irreducible
    {F E : Type*} [Field F] [Field E] [Algebra F E] {α : E}
    (hα : IsAlgebraic F α) :
    Irreducible (minpoly F α) :=
  minpoly.irreducible hα.isIntegral

/-- The minimal polynomial of an algebraic element annihilates that element. -/
theorem simple_extension_minpoly_aeval_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E] {α : E}
    (_hα : IsAlgebraic F α) :
    Polynomial.aeval α (minpoly F α) = 0 :=
  minpoly.aeval F α

/- The quotient presentation in the source is Mathlib's `AdjoinRoot`; this
   definition is the canonical equivalence already built from the minimal
   polynomial. -/
/-- An algebraic simple extension is canonically a quotient by its minimal polynomial. -/
noncomputable def simple_extension_adjoinRoot_equiv
    {F E : Type*} [Field F] [Field E] [Algebra F E] {α : E}
    (hα : IsAlgebraic F α) :
    AdjoinRoot (minpoly F α) ≃ₐ[F]
      IntermediateField.adjoin F ({α} : Set E) :=
  IntermediateField.adjoinRootEquivAdjoin F hα.isIntegral

/- The other branch is Mathlib's rational-function presentation of a
   transcendental simple extension. -/
/-- A transcendental simple extension is canonically a rational function field. -/
noncomputable def simple_extension_ratFunc_equiv
    {F E : Type*} [Field F] [Field E] [Algebra F E] {α : E}
    (hα : Transcendental F α) :
    RatFunc F ≃ₐ[F] IntermediateField.adjoin F ({α} : Set E) :=
  RatFunc.algEquivOfTranscendental α hα

/-! ## Examples -/

/- The source's complex example is covered by the finite-dimensional complex
   extension already available in the preceding chapter. -/
/-- The complex numbers are algebraic over the real numbers. -/
theorem complex_is_algebraic_over_real : Algebra.IsAlgebraic ℝ ℂ := by
  infer_instance

/-- Every complex number is algebraic over the real numbers. -/
theorem complex_element_is_algebraic (α : ℂ) : IsAlgebraic ℝ α :=
  Algebra.IsAlgebraic.isAlgebraic α

/-- The quadratic equation displayed in the source for a complex number. -/
theorem complex_element_satisfies_real_quadratic (α : ℂ) :
    Polynomial.aeval α
        (Polynomial.X ^ 2 - Polynomial.C (2 * α.re) * Polynomial.X +
          Polynomial.C (α.re ^ 2 + α.im ^ 2)) = 0 := by
  apply Complex.ext <;> simp [Polynomial.aeval_def, pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring

/- The source's compact-Riemann-surface example needs a formal model of
   compact Riemann surfaces and their meromorphic function fields, which is
   not available here.  The actual function-field analogue supplied by
   Mathlib is the following theorem for rational functions. -/
/-- A nonconstant rational function generates an algebraic extension of its
    simple subfield inside the rational function field. -/
theorem rational_function_field_algebraic_over_nonconstant_subfield
    (f : RatFunc ℂ) (hf : ¬ ∃ c : ℂ, f = RatFunc.C c) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin ℂ ({f} : Set (RatFunc ℂ))) (RatFunc ℂ) := by
  exact RatFunc.isAlgebraic_adjoin_simple_X' f hf

/-! ## Towers and finiteness -/

/-- Algebraicity of an element persists after enlarging the coefficient field. -/
theorem algebraic_element_goes_up
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    {α : K} (hα : IsAlgebraic F α) :
    IsAlgebraic E α :=
  hα.tower_top E

/-- If the top of a field tower is algebraic over the bottom, it is algebraic
    over every intermediate field. -/
theorem algebraic_extension_goes_up
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    (hK : Algebra.IsAlgebraic F K) :
    Algebra.IsAlgebraic E K := by
  let _ : Algebra.IsAlgebraic F K := hK
  exact Algebra.IsAlgebraic.tower_top (K := F) (A := K) E

/- A finite extension is algebraic by Mathlib's canonical finite-module
   instance. -/
/-- Every finite field extension is algebraic. -/
theorem finite_extension_is_algebraic
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (hfinite : FiniteDimensional F E) :
    Algebra.IsAlgebraic F E := by
  let _ : FiniteDimensional F E := hfinite
  infer_instance

/- The source's stronger characterization is recorded with the canonical
   intermediate field for each simple extension. -/
/-- A monogenic field extension is finite exactly when its generator is algebraic. -/
theorem monogenic_extension_finite_iff_algebraic
    {F E : Type*} [Field F] [Field E] [Algebra F E] (α : E) :
    FiniteDimensional F (IntermediateField.adjoin F ({α} : Set E)) ↔
      IsAlgebraic F α := by
  constructor
  · intro h
    let _ : FiniteDimensional F (IntermediateField.adjoin F ({α} : Set E)) := h
    have hα' :
        IsAlgebraic F (⟨α, IntermediateField.mem_adjoin_simple_self F α⟩ :
          IntermediateField.adjoin F ({α} : Set E)) :=
      IsAlgebraic.of_finite F _
    exact
      (isAlgebraic_algHom_iff (IntermediateField.adjoin F ({α} : Set E)).val
        Subtype.val_injective).mpr hα'
  · intro hα
    exact IntermediateField.adjoin.finiteDimensional hα.isIntegral

/-- An extension is algebraic exactly when all of its simple subextensions are finite. -/
theorem algebraic_extension_iff_all_simple_extensions_finite
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    Algebra.IsAlgebraic F E ↔
      ∀ α : E,
        FiniteDimensional F (IntermediateField.adjoin F ({α} : Set E)) := by
  constructor
  · intro h α
    exact (monogenic_extension_finite_iff_algebraic α).mpr (h.isAlgebraic α)
  · intro h
    exact ⟨fun α => (monogenic_extension_finite_iff_algebraic α).mp (h α)⟩

/- The source warns that algebraic extensions need not be finite.  The
   algebraic closure of `ℚ` is a concrete standard witness. -/
/-- Algebraic extensions need not be finite-dimensional. -/
theorem algebraic_extension_not_necessarily_finite :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) ∧
      ¬ FiniteDimensional ℚ (AlgebraicClosure ℚ) := by
  constructor
  · exact AlgebraicClosure.isAlgebraic ℚ
  · intro hfinite
    let _ : FiniteDimensional ℚ (AlgebraicClosure ℚ) := hfinite
    let d := Module.finrank ℚ (AlgebraicClosure ℚ)
    obtain ⟨p, hp_lower, hp⟩ := Nat.exists_infinite_primes (d + 2)
    let _ : NeZero (p : ℚ) := ⟨by exact_mod_cast hp.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
    have hcycl : Polynomial.cyclotomic p ℚ = minpoly ℚ ζ :=
      hζ.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat hp.pos)
    have hdiv : (minpoly ℚ ζ).natDegree ∣ Module.finrank ℚ (AlgebraicClosure ℚ) :=
      minpoly.degree_dvd (IsIntegral.of_finite ℚ ζ)
    rw [← hcycl, Polynomial.natDegree_cyclotomic, Nat.totient_prime hp] at hdiv
    have hle : p - 1 ≤ d := Nat.le_of_dvd Module.finrank_pos hdiv
    omega

/-- A finite list of algebraic generators gives a finite extension. -/
theorem finitely_generated_algebraic_extension_is_finite
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (α : Fin n → E) (hα : ∀ i, IsAlgebraic F (α i)) :
    FiniteDimensional F (IntermediateField.adjoin F (Set.range α)) := by
  classical
  let _ : Finite (Set.range α) := Set.toFinite _
  exact IntermediateField.finiteDimensional_adjoin (fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    exact (hα i).isIntegral)

/- The source's examples of algebraic numbers are stated over the canonical
   rational-to-complex algebra. -/
/-- The complex number `√2` is algebraic over `ℚ`. -/
theorem sqrt_two_is_algebraic_number :
    IsAlgebraic ℚ ((Real.sqrt 2 : ℝ) : ℂ) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 2, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (by norm_num) 2
  · simp [Polynomial.aeval_def]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num

/-- The imaginary unit is algebraic over `ℚ`. -/
theorem imaginary_unit_is_algebraic_number : IsAlgebraic ℚ Complex.I := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C 1, ?_, ?_⟩
  · exact Polynomial.X_pow_add_C_ne_zero (by norm_num) 1
  · simp [Polynomial.aeval_def, Complex.I_sq]

/- The source mentions that `π` is not algebraic over `ℚ`.  We do not
   formalize this fact here: it is the deep transcendence theorem for `π`,
   and the required result is not currently available in Mathlib. -/

/-- The algebraic numbers form a field. -/
theorem algebraic_numbers_form_field : IsField (algebraicClosure ℚ ℂ) := by
  exact Field.toIsField _

/-! ## Algebraic elements and permanence -/

/- `algebraicClosure F E` is Mathlib's canonical intermediate field whose
   underlying set is exactly the algebraic elements. -/
/-- The algebraic elements in a field extension form an intermediate field. -/
theorem algebraic_elements_form_subextension
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    ∀ x : E, x ∈ algebraicClosure F E ↔ IsAlgebraic F x := by
  intro x
  exact mem_algebraicClosure_iff

/-- The algebraic-element subextension is itself algebraic over the base field. -/
theorem algebraic_elements_subextension_is_algebraic
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    Algebra.IsAlgebraic F (algebraicClosure F E) := by
  infer_instance

/-- Algebraicity is transitive in a tower of field extensions. -/
theorem algebraic_extension_permanence
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    (hE : Algebra.IsAlgebraic F E) (hK : Algebra.IsAlgebraic E K) :
    Algebra.IsAlgebraic F K := by
  let _ : Algebra.IsAlgebraic F E := hE
  let _ : Algebra.IsAlgebraic E K := hK
  exact Algebra.IsAlgebraic.trans F E K

/- The cardinality proof in the source is exactly Mathlib's polynomial-root
   counting theorem for algebraic extensions. -/
/-- An algebraic extension has cardinality at most the maximum of the base
    cardinality and `aleph₀`. -/
theorem algebraic_extension_cardinal_le_max
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] :
    Cardinal.lift.{u} (Cardinal.mk E) ≤
      Cardinal.lift.{v} (Cardinal.mk F) ⊔ Cardinal.aleph0 := by
  exact Algebra.IsAlgebraic.lift_cardinalMk_le_max F E

/-! ## Subalgebras and self-maps -/

/- A subring containing the base field is represented by a `Subalgebra`; this
   is the canonical bundled interface that records the two inclusions in the
   source. -/
/- The source's displayed inverse formula is the proof-level content of
   `Subalgebra.isField_of_algebraic`; no weaker duplicate lemma is needed. -/
/-- Every intermediate subalgebra of an algebraic field extension is a field. -/
theorem subalgebra_of_algebraic_extension_is_field
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] (R : Subalgebra F E) :
    IsField R :=
  Subalgebra.isField_of_algebraic R

/-- The same subalgebra conclusion applies when the ambient extension is
    supplied as finite or algebraic. -/
theorem subalgebra_of_finite_or_algebraic_extension_is_field
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (R : Subalgebra F E)
    (h : FiniteDimensional F E ∨ Algebra.IsAlgebraic F E) :
    IsField R := by
  rcases h with hfinite | halgebraic
  · let _ : FiniteDimensional F E := hfinite
    exact subalgebra_of_algebraic_extension_is_field R
  · let _ : Algebra.IsAlgebraic F E := halgebraic
    exact subalgebra_of_algebraic_extension_is_field R

/-- Every algebra endomorphism of an algebraic field extension is bijective. -/
theorem algebraic_extension_self_map_bijective
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] (f : E →ₐ[F] E) :
    Function.Bijective f :=
  Algebra.IsAlgebraic.algHom_bijective f

/- The source calls such a bijective algebra map an automorphism; Mathlib's
   usable representation is an `AlgEquiv`. -/
/-- An algebra self-map of an algebraic field extension is an automorphism. -/
noncomputable def algebraic_extension_self_map_automorphism
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] (f : E →ₐ[F] E) : E ≃ₐ[F] E :=
  AlgEquiv.ofBijective f (algebraic_extension_self_map_bijective f)

end

end Formalization.Books.Fields.Unit08
