import Mathlib.CategoryTheory.Triangulated.Generators
import Formalization.Books.Derived.Unit35.OperationsOnFullSubcategories

/-!
# Derived Categories, Chapter 36: generators of triangulated categories

The canonical Mathlib `ObjectProperty.triangEnvelope` construction is the
source's generated subcategory.  The declarations below expose the source's
positive indexing, finite-window description, weak-generator condition, and
source-facing closure statements without duplicating Mathlib's envelope
construction.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit03
open Formalization.Books.Derived.Unit04
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit35
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u

namespace Formalization.Books.Derived.Unit36

section GeneratedSubcategories

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [CategoryTheory.IsTriangulated C]

/- The source only uses `⟨E⟩ₙ` for `n ≥ 1`.  The total Lean indexing below
  sends `n = 0` to Mathlib's zero-extension stage and is only unfolded at
  positive indices in the source-facing statements. -/

/-! The source's `⟨E⟩ₙ`, represented by Mathlib's canonical envelope stages. -/
abbrev generatedSubcategoryIter (E : C) (n : ℕ) : ObjectProperty C :=
  (ObjectProperty.singleton E).triangEnvelopeIter (n - 1)

/-! The source's `⟨E⟩ = ⋃ₙ ⟨E⟩ₙ`. -/
abbrev generatedSubcategory (E : C) : ObjectProperty C :=
  (ObjectProperty.singleton E).triangEnvelope

/-! The first generated stage `⟨E⟩₁`. -/
abbrev generatedSubcategoryOne (E : C) : ObjectProperty C :=
  generatedSubcategoryIter E 1

/-! The finite shift window `E[-m,m]` used in the source's explicit formula. -/
def generatorWindow (E : C) (m : ℕ) : ObjectProperty C :=
  shiftWindow (ObjectProperty.singleton E)
    (((-(m : ℤ) : ℤ) : EInt)) (((m : ℤ) : EInt))

/-! `⟨E⟩ₙ = smd(⟨E⟩₁ ⋆ ⟨E⟩ₙ₋₁)` for `n > 1`. -/
theorem generatedSubcategoryIter_succ (E : C) {n : ℕ} (hn : 1 ≤ n) :
    generatedSubcategoryIter E (n + 1) =
      smd (star (generatedSubcategoryOne E) (generatedSubcategoryIter E n)) := by
  sorry

/-! The first stage is the source's finite-sum-and-summand closure of all shifts. -/
theorem generatedSubcategoryOne_eq_smd_add_allShifts (E : C) :
    generatedSubcategoryOne E =
      smd (add (shiftWindow (ObjectProperty.singleton E)
        (⊥ : EInt) (⊤ : EInt))) := by
  sorry

/-! Every positive stage is strictly full and stable under direct summands. -/
omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategoryIter_isStrictlyFull (E : C) {n : ℕ} (_hn : 1 ≤ n) :
    (generatedSubcategoryIter E n).IsClosedUnderIsomorphisms := by
  infer_instance

omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategoryIter_isStableUnderRetracts (E : C) {n : ℕ} (_hn : 1 ≤ n) :
    (generatedSubcategoryIter E n).IsStableUnderRetracts := by
  infer_instance

/-! The source's assertion that each positive stage is preserved by shifts. -/
omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategoryIter_isStableUnderShifts (E : C) {n : ℕ} (_hn : 1 ≤ n) :
    (generatedSubcategoryIter E n).IsStableUnderShift ℤ := by
  infer_instance

/-! The source's assertion that each positive stage is additive. -/
theorem generatedSubcategoryIter_closedUnderFiniteDirectSums
    (E : C) {n : ℕ} (hn : 1 ≤ n) :
    ∀ (r : ℕ) (X : Fin r → C),
      (∀ i, generatedSubcategoryIter E n (X i)) →
        generatedSubcategoryIter E n (∐ X) := by
  sorry

/- A fixed stage is not asserted to be closed under arbitrary cones or
   extensions; the source explicitly warns that this need not hold. -/

/-! The explicit n-fold extension-product formula for a positive stage. -/
theorem generatedSubcategoryIter_eq_smd_starPower
    (E : C) {n : ℕ} (hn : 1 ≤ n) :
    generatedSubcategoryIter E n =
      smd (starPower (generatedSubcategoryOne E) n) := by
  sorry

/-! The same stage is the union over finite shift windows. -/
theorem generatedSubcategoryIter_eq_iSup_finite_windows
    (E : C) {n : ℕ} (hn : 1 ≤ n) :
    generatedSubcategoryIter E n =
      ⨆ m : {m : ℕ // 1 ≤ m},
        smd (starPower (add (generatorWindow E m.1)) n) := by
  sorry

/-! The generated subcategory is the increasing union of the positive stages. -/
theorem generatedSubcategory_eq_iSup (E : C) :
    generatedSubcategory E =
      ⨆ n : {n : ℕ // 1 ≤ n}, generatedSubcategoryIter E n := by
  sorry

/-! The source's combined finite-window formula for `⟨E⟩`. -/
theorem generatedSubcategory_eq_iSup_finite_windows (E : C) :
    generatedSubcategory E =
      ⨆ (n : {n : ℕ // 1 ≤ n}) (m : {m : ℕ // 1 ≤ m}),
        smd (starPower (add (generatorWindow E m.1)) n.1) := by
  sorry

/-! Concatenating positive stages adds their extension lengths. -/
theorem generatedSubcategoryIter_add
    (E : C) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    generatedSubcategoryIter E (n + n') =
      smd (star (generatedSubcategoryIter E n)
        (generatedSubcategoryIter E n')) := by
  sorry

/-!
The generated subcategory is the smallest strictly full, saturated,
triangulated subcategory containing `E`.
-/
theorem generatedSubcategory_is_smallest (E : C) :
    (generatedSubcategory E).IsClosedUnderIsomorphisms ∧
      IsSaturated (generatedSubcategory E) ∧
      (generatedSubcategory E).IsTriangulated ∧
      ObjectProperty.singleton E ≤ generatedSubcategory E ∧
      ∀ P : ObjectProperty C,
        P.IsClosedUnderIsomorphisms → P.IsTriangulated → IsSaturated P →
          generatedSubcategory E ≤ P := by
  sorry

end GeneratedSubcategories

section Generators

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [CategoryTheory.IsTriangulated C]

/- The strong and classical notions are Mathlib's canonical definitions for a
   singleton object property. -/
abbrev IsClassicalGenerator (E : C) : Prop :=
  (ObjectProperty.singleton E).IsClassicalTriangulatedGenerator

abbrev IsStrongGenerator (E : C) : Prop :=
  (ObjectProperty.singleton E).IsStrongTriangulatedGenerator

/-! The source's weak-generator condition. -/
def IsWeakGenerator (E : C) : Prop :=
  ∀ ⦃K : C⦄, ¬ IsZero K →
    ∃ (n : ℤ) (f : E ⟶ K⟦n⟧), f ≠ 0

/-! The source uses “weak generator” and “generator” synonymously. -/
abbrev IsGenerator (E : C) : Prop := IsWeakGenerator E

/-! A triangulated category has a strong generator if some object is one. -/
def HasStrongGenerator (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [CategoryTheory.IsTriangulated C] : Prop :=
  ∃ E : C, IsStrongGenerator E

omit [CategoryTheory.IsTriangulated C] in
theorem isClassicalGenerator_iff (E : C) :
    IsClassicalGenerator E ↔ generatedSubcategory E = (⊤ : ObjectProperty C) := Iff.rfl

/-! The positive-index form of the source's strong-generator definition. -/
theorem isStrongGenerator_iff (E : C) :
    IsStrongGenerator E ↔
      ∃ n : ℕ, 1 ≤ n ∧ generatedSubcategoryIter E n = (⊤ : ObjectProperty C) := by
  sorry

/-! The source's right-orthogonal characterization. -/
theorem rightOrthogonal_iff (E K : C) :
    (∀ i : ℤ, HomIsZero E (K⟦i⟧)) ↔
      ∀ E' : C, generatedSubcategory E E' → HomIsZero E' K := by
  sorry

/-! A classical generator is a weak generator. -/
theorem classical_generator_is_generator {E : C}
    (hE : IsClassicalGenerator E) : IsGenerator E := by
  sorry

/-! If the category has a strong generator, every classical generator is strong. -/
theorem classical_generator_is_strong_generator {E : C}
    (_hC : HasStrongGenerator C)
    (_hE : IsClassicalGenerator E) : IsStrongGenerator E := by
  sorry

/-!
The source's generator-check remark.  `hRetracts` is the canonical Lean
form of closure under direct summands used by `smd = retractClosure`; the
binary-summand hypothesis is retained as the displayed source condition.
-/
theorem property_holds_on_generatedSubcategory
    (E : C) (P : ObjectProperty C)
    (hIso : P.IsClosedUnderIsomorphisms)
    (hFiniteSums : ∀ (r : ℕ) (X : Fin r → C),
      (∀ i, P (X i)) → P (∐ X))
    (hTriangle : ∀ (T : Triangle C), T ∈ distTriang C →
      ((P T.obj₁ ∧ P T.obj₂) → P T.obj₃) ∧
        ((P T.obj₂ ∧ P T.obj₃) → P T.obj₁) ∧
        ((P T.obj₁ ∧ P T.obj₃) → P T.obj₂))
    (hSummands : ∀ ⦃K L : C⦄, P (K ⊞ L) → P K ∧ P L)
    (hRetracts : P.IsStableUnderRetracts)
    (hShifts : ∀ n : ℤ, P (E⟦n⟧)) :
    generatedSubcategory E ≤ P := by
  sorry

end Generators

end Formalization.Books.Derived.Unit36
