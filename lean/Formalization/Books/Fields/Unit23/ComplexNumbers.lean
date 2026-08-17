import Formalization.Books.Fields.Unit10.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Sylow

/-!
# Fields, Chapter 23: The complex numbers

The source's algebraic-closedness assertion is already available as
`Formalization.Books.Fields.Unit10.complex_is_algebraically_closed`.  This
file records the calculus input and the field-theoretic consequences used in
the source discussion, using Mathlib's polynomial, Galois-group, and
`IsPGroup` interfaces.
-/

namespace Formalization.Books.Fields.Unit23

noncomputable section

/-! ## The real-root input -/

/- The source takes this fact from calculus.  `Odd P.natDegree` is the
   source's assertion that the polynomial has odd degree, and `P.IsRoot x` is
   Mathlib's evaluation-at-a-root predicate. -/
/-- Every odd-degree polynomial over the reals has a real root. -/
theorem real_polynomial_exists_root_of_odd_natDegree
    {P : Polynomial ℝ} (hP : Odd P.natDegree) :
    ∃ x : ℝ, P.IsRoot x := by
  sorry

/- The source's conclusion that there are no nontrivial odd-degree extensions
   is stated for finite extensions, since “degree” is then `Module.finrank`.
   An algebra equivalence to the base field is the canonical field-theoretic
   meaning of “trivial extension.” -/
/-- A finite odd-degree extension of `ℝ` is trivial. -/
theorem real_odd_degree_extension_is_trivial
    {K : Type*} [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K]
    (hK : Odd (Module.finrank ℝ K)) :
    Nonempty (K ≃ₐ[ℝ] ℝ) := by
  sorry

/-! ## Finite Galois extensions of the reals -/

/- The source's Sylow/fixed-field argument concludes that the Galois group is
   a 2-group.  `Gal(K / ℝ)` is Mathlib's canonical automorphism group and
   `IsPGroup 2` is its canonical p-group predicate. -/
/-- The Galois group of a finite Galois extension of `ℝ` is a 2-group. -/
theorem real_finite_galois_group_is_two_group
    {K : Type*} [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K]
    [IsGalois ℝ K] :
    IsPGroup 2 (Gal(K / ℝ)) := by
  sorry

/- The source's intermediate Sylow assertions are collected in this
   source-facing specification.  The fixed field is viewed as an extension
   of `ℝ`, while the equality with `⊥` identifies it with the base field. -/
/-- A Sylow 2-subgroup fixes exactly the real base field. -/
theorem real_sylow_fixed_field_spec
    {K : Type*} [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K]
    [IsGalois ℝ K] (P : Sylow 2 (Gal(K / ℝ))) :
    Odd (Module.finrank ℝ
      (IntermediateField.fixedField (P : Subgroup (Gal(K / ℝ))))) ∧
      IntermediateField.fixedField (P : Subgroup (Gal(K / ℝ))) = ⊥ ∧
        (P : Subgroup (Gal(K / ℝ))) = ⊤ := by
  sorry

/- The source's assertion that the only algebraic extensions of `ℝ` are `ℝ`
   and `ℂ` up to isomorphism is already supplied, in stronger form, by
   Mathlib's `Real.nonempty_algEquiv_or`.  This finite-Galois specialization
   records the source-facing interface without introducing a parallel
   quadratic-extension definition. -/
/-- A finite Galois extension of `ℝ` is `ℝ` or `ℂ` up to `ℝ`-algebra equivalence. -/
theorem real_finite_galois_extension_is_real_or_complex
    {K : Type*} [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K]
    [IsGalois ℝ K] :
    Nonempty (K ≃ₐ[ℝ] ℝ) ∨ Nonempty (K ≃ₐ[ℝ] ℂ) :=
  Real.nonempty_algEquiv_or K

/- The source writes `ℂ ⊂ K` for the nontrivial case.  For an arbitrary
   extension model, the source-faithful formulation is an `ℝ`-algebra
   equivalence; a literal subset would require choosing an embedding. -/
/-- A nontrivial finite Galois extension of `ℝ` is isomorphic to `ℂ`. -/
theorem nontrivial_real_finite_galois_extension_is_complex
    {K : Type*} [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K]
    [IsGalois ℝ K] (hK : Nontrivial (Gal(K / ℝ))) :
    Nonempty (K ≃ₐ[ℝ] ℂ) := by
  sorry

/- `Complex.finrank_real_complex` records that the nontrivial branch has
   degree two, as used in the source's Sylow discussion. -/

/- The source's further contradiction from a quadratic extension of `ℂ` is
   proof narration: `complex_exists_square_root` records the displayed input,
   while the final algebraic-closedness declaration below records the stronger
   conclusion. -/

/- The source uses the fact that every complex number has a square root.  This
   is a source-facing formulation of the root theorem already available as
   `Complex.exists_root` (and follows from the imported algebraic-closedness
   result). -/
/-- Every complex number has a square root. -/
theorem complex_exists_square_root (z : ℂ) :
    ∃ w : ℂ, w ^ 2 = z := by
  sorry

/- The normal-closure step in the source is also proof narration; Mathlib's
   `IntermediateField.normalClosure`/`IsNormalClosure` interfaces, exposed in
   earlier chapters, supply that construction. -/

/- The final labeled lemma in the source is the same assertion as the
   preceding chapter's source-facing theorem, so this is only a chapter-local
   name for that established declaration, not a new algebraic-closedness
   predicate or construction. -/
/-- **Fundamental theorem of algebra:** `ℂ` is algebraically closed. -/
theorem fundamental_theorem_of_algebra : IsAlgClosed ℂ :=
  Formalization.Books.Fields.Unit10.complex_is_algebraically_closed

end

end Formalization.Books.Fields.Unit23
