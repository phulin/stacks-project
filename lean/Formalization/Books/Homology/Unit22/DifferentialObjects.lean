import Formalization.Books.Homology.Unit20.DifferentialObjects
import Formalization.Books.Homology.Unit21.ExactCouples
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Homological Algebra, Chapter 22: Spectral sequences: differential objects

This file gives the source-facing interface for the differential-object
construction.  The unshifted construction and its categorical subobject
calculus are reused from Chapter 20.  Chapter 21 supplies the exact-couple
and translated-spectral-sequence interfaces used by the shifted variant.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace Formalization.Books.Homology.Unit22

/-! ## 22.1 Differential objects -/

/-! ### Differential objects, morphisms, and homology -/

/-
The source's unshifted objects have no ambient shift functor.  The preceding
chapter therefore records them as `PlainDifferentialObject`; these aliases
reuse that canonical project representation rather than introducing a second
category in this chapter.
-/

/-- A differential object `(A, d)` with `d ≫ d = 0`. -/
abbrev DifferentialObject (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  Formalization.Books.Homology.Unit20.PlainDifferentialObject C

/-- A morphism of differential objects, commuting with the differentials. -/
abbrev DifferentialObjectHom {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] (A B : DifferentialObject C) :=
  Formalization.Books.Homology.Unit20.PlainDifferentialObjectHom A B

/-- The category of unshifted differential objects is abelian. -/
theorem differentialObject_category_abelian {C : Type u} [Category.{v} C]
    [Abelian C] : Nonempty (Abelian (DifferentialObject C)) := by
  exact Formalization.Books.Homology.Unit20.plainDifferentialObject_abelian

/-- `H(A,d) = Ker(d) / Im(d)`, using the canonical categorical homology object. -/
abbrev differentialObjectHomology {C : Type u} [Category.{v} C]
    [Abelian C] (A : DifferentialObject C) : C :=
  Formalization.Books.Homology.Unit20.plainDifferentialHomology A

/-! ### Short exact sequences and the long homology sequence -/

/-- A short exact sequence of differential objects. -/
abbrev DifferentialObjectShortExact {C : Type u} [Category.{v} C]
    [Abelian C] (A B D : DifferentialObject C) :=
  Formalization.Books.Homology.Unit20.PlainDifferentialShortExact A B D

/-- The bi-infinite homology sequence attached to a short exact sequence.

The index is chosen so that the terms repeat as
`H(C), H(A), H(B), H(C), ...`, matching the displayed source sequence.
-/
abbrev DifferentialObjectLongExactSequence {C : Type u} [Category.{v} C]
    [Abelian C] (X : ℤ → C) :=
  Formalization.Books.Homology.Unit20.LongExactSequence X

abbrev differentialObjectHomologyLongTerm {C : Type u} [Category.{v} C]
    [Abelian C] (A B D : DifferentialObject C) (n : ℤ) : C :=
  Formalization.Books.Homology.Unit20.differentialHomologyLongTerm A B D n

theorem differentialObjectShortExact_homology_long_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : DifferentialObject C}
    (S : DifferentialObjectShortExact A B D) :
    Nonempty (DifferentialObjectLongExactSequence
      (differentialObjectHomologyLongTerm A B D)) := by
  exact Formalization.Books.Homology.Unit20.plainDifferentialShortExact_homology_long_exact S

/-! ### The injective self-map example -/

/-- An injective endomorphism `α` of a differential object. -/
abbrev DifferentialObjectInjectiveSelfMap {C : Type u} [Category.{v} C]
    [Abelian C] (A : DifferentialObject C) :=
  Formalization.Books.Homology.Unit20.PlainDifferentialInjectiveEndomorphism A

/-- Data for the induced differential on the quotient `A / α A`. -/
abbrev DifferentialObjectQuotientMapData {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :=
  Formalization.Books.Homology.Unit20.QuotientDifferentialMapData α

abbrev differentialObjectQuotientMapData {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    DifferentialObjectQuotientMapData α :=
  Formalization.Books.Homology.Unit20.quotientDifferentialMapData α

abbrev differentialObjectQuotientMap {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    cokernel α.hom.hom ⟶ cokernel α.hom.hom :=
  Formalization.Books.Homology.Unit20.quotientDifferentialMap α

/-- The quotient differential object `(A / α A, d)`. -/
abbrev differentialObjectQuotient {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : DifferentialObject C :=
  Formalization.Books.Homology.Unit20.quotientDifferentialObject α

/-- The short exact sequence `0 → (A,d) → (A,d) → (A/αA,d) → 0`. -/
abbrev differentialObjectSelfMapShortExact {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    DifferentialObjectShortExact A A (differentialObjectQuotient α) :=
  Formalization.Books.Homology.Unit20.differentialSelfMapShortExact α

/-! ### The associated exact couple and its pages -/

abbrev DifferentialObjectSelfMapExactCouple {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :=
  Formalization.Books.Homology.Unit21.ExactCouple C
    (differentialObjectHomology A) (differentialObjectHomology (differentialObjectQuotient α))

theorem differentialObjectSelfMap_exact_couple_exists
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    Nonempty (DifferentialObjectSelfMapExactCouple α) := by
  exact Formalization.Books.Homology.Unit20.differentialSelfMap_exactCouple_exists α

noncomputable def differentialObjectSelfMapExactCouple
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    DifferentialObjectSelfMapExactCouple α :=
  Formalization.Books.Homology.Unit20.differentialSelfMapExactCouple α

/-- The map `\overline{α}` in the self-map exact couple. -/
abbrev differentialObjectSelfMapBarAlpha
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    differentialObjectHomology A ⟶ differentialObjectHomology A :=
  (differentialObjectSelfMapExactCouple α).alpha

/-- The boundary map `f : H(A/αA) → H(A)`. -/
abbrev differentialObjectSelfMapBoundary
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    differentialObjectHomology (differentialObjectQuotient α) ⟶
      differentialObjectHomology A :=
  (differentialObjectSelfMapExactCouple α).f

/-- The quotient map `g : H(A) → H(A/αA)`. -/
abbrev differentialObjectSelfMapQuotientHomologyMap
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    differentialObjectHomology A ⟶
      differentialObjectHomology (differentialObjectQuotient α) :=
  (differentialObjectSelfMapExactCouple α).g

abbrev PlainSpectralSequence (C : Type u) [Category.{v} C] [Abelian C]
    (r₀ : ℤ := 1) :=
  Formalization.Books.Homology.Unit20.PlainSpectralSequence.{v, u, 0} C r₀

abbrev pageObject {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : C :=
  Formalization.Books.Homology.Unit20.plainPageObject E r hr

abbrev pageDifferential {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : pageObject E r hr ⟶ pageObject E r hr :=
  Formalization.Books.Homology.Unit20.plainPageDifferential E r hr

/-- The spectral sequence obtained from the self-map exact couple. -/
noncomputable def differentialObjectSelfMapAssociatedSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : PlainSpectralSequence C 1 :=
  Formalization.Books.Homology.Unit20.differentialSelfMapAssociatedSpectralSequence α

theorem differentialObjectSelfMap_E1
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    Nonempty (pageObject (differentialObjectSelfMapAssociatedSpectralSequence α) 1 ≅
      differentialObjectHomology (differentialObjectQuotient α)) := by
  exact Formalization.Books.Homology.Unit20.differentialSelfMap_E1 α

/-- The separately numbered zeroth page `E₀ = A / α A`. -/
abbrev differentialObjectSelfMapE₀ {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : C :=
  (differentialObjectQuotient α).carrier

/-- The zeroth differential `d₀ = d` on `E₀`. -/
abbrev differentialObjectSelfMapD₀ {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    differentialObjectSelfMapE₀ α ⟶ differentialObjectSelfMapE₀ α :=
  (differentialObjectQuotient α).d

/-
The exact-couple API starts at page one.  The source's convention starts the
same sequence at page zero, so the following data records the page-zero
identification and the compatibility of `d₀` with the canonical page
differential instead of silently identifying unrelated chosen cokernels.
-/
structure DifferentialObjectSelfMapSpectralSequenceData
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C} (α : DifferentialObjectInjectiveSelfMap A) where
  sequence : PlainSpectralSequence C 0
  pageZeroIso : pageObject sequence 0 ≅ differentialObjectSelfMapE₀ α
  pageZeroDifferential_compatibility :
    pageDifferential sequence 0 ≫ pageZeroIso.hom =
      pageZeroIso.hom ≫ differentialObjectSelfMapD₀ α
  pageOneIso : Nonempty (pageObject sequence 1 ≅
    differentialObjectHomology (differentialObjectQuotient α))

theorem differentialObjectSelfMapSpectralSequenceData_exists
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    Nonempty (DifferentialObjectSelfMapSpectralSequenceData α) := by
  sorry

noncomputable def differentialObjectSelfMapSpectralSequenceData
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    DifferentialObjectSelfMapSpectralSequenceData α :=
  Classical.choice (differentialObjectSelfMapSpectralSequenceData_exists α)

noncomputable def differentialObjectSelfMapSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : PlainSpectralSequence C 0 :=
  (differentialObjectSelfMapSpectralSequenceData α).sequence

theorem differentialObjectSelfMap_page_data_is_spectral_sequence
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    Nonempty (PlainSpectralSequence C 0) := by
  exact Formalization.Books.Homology.Unit20.differentialSelfMap_starting_at_zero_exists α

/-! ### The `Bᵣ` and `Zᵣ` subobjects -/

abbrev differentialObjectSelfMapAlphaPow {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : ℕ →
      (A.carrier ⟶ A.carrier) :=
  Formalization.Books.Homology.Unit20.selfMapAlphaPow α

abbrev differentialObjectSelfMapBoundaryPreimage {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject A.carrier :=
  Formalization.Books.Homology.Unit20.selfMapBoundaryPreimage α r

abbrev differentialObjectSelfMapCyclePreimage {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject A.carrier :=
  Formalization.Books.Homology.Unit20.selfMapCyclePreimage α r

theorem differentialObjectSelfMap_boundary_preimage_le_cycle_preimage
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    differentialObjectSelfMapBoundaryPreimage α r ≤
      differentialObjectSelfMapCyclePreimage α r := by
  exact Formalization.Books.Homology.Unit20.selfMap_boundary_preimage_le_cycle_preimage α r

abbrev differentialObjectSelfMapBoundaryPlus {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject A.carrier :=
  Formalization.Books.Homology.Unit20.selfMapBoundaryPlus α r

abbrev differentialObjectSelfMapCyclePlus {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject A.carrier :=
  Formalization.Books.Homology.Unit20.selfMapCyclePlus α r

theorem differentialObjectSelfMap_boundary_plus_le_cycle_plus
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    differentialObjectSelfMapBoundaryPlus α r ≤
      differentialObjectSelfMapCyclePlus α r := by
  exact Formalization.Books.Homology.Unit20.selfMap_boundary_plus_le_cycle_plus α r

abbrev differentialObjectSelfMapQuotientImageSubobject
    {C : Type u} [Category.{v} C] [Abelian C] {X Q : C}
    (π : X ⟶ Q) (B : Subobject X) : Subobject Q :=
  Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject π B

abbrev differentialObjectSelfMapBoundarySubobject
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject (differentialObjectSelfMapE₀ α) :=
  Formalization.Books.Homology.Unit20.selfMapBoundarySubobject α r

abbrev differentialObjectSelfMapCycleSubobject
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject (differentialObjectSelfMapE₀ α) :=
  Formalization.Books.Homology.Unit20.selfMapCycleSubobject α r

theorem differentialObjectSelfMap_boundary_le_cycle
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    differentialObjectSelfMapBoundarySubobject α r ≤
      differentialObjectSelfMapCycleSubobject α r := by
  exact Formalization.Books.Homology.Unit20.selfMap_boundary_le_cycle α r

def differentialObjectSelfMapB {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C} (α : DifferentialObjectInjectiveSelfMap A) :
    ℕ → Subobject (differentialObjectSelfMapE₀ α)
  | 0 => ⊥
  | n + 1 => differentialObjectSelfMapBoundarySubobject α (n + 1)

def differentialObjectSelfMapZ {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C} (α : DifferentialObjectInjectiveSelfMap A) :
    ℕ → Subobject (differentialObjectSelfMapE₀ α)
  | 0 => ⊤
  | n + 1 => differentialObjectSelfMapCycleSubobject α (n + 1)

theorem differentialObjectSelfMap_B_le_Z
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    differentialObjectSelfMapB α r ≤ differentialObjectSelfMapZ α r := by
  cases r with
  | zero => exact bot_le
  | succ n =>
    simpa [differentialObjectSelfMapB, differentialObjectSelfMapZ] using
      differentialObjectSelfMap_boundary_le_cycle α (n + 1)

theorem differentialObjectSelfMap_filtration
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    differentialObjectSelfMapB α 0 = ⊥ ∧
      differentialObjectSelfMapZ α 0 = ⊤ ∧
      (∀ r, differentialObjectSelfMapB α r ≤ differentialObjectSelfMapB α (r + 1)) ∧
      (∀ r, differentialObjectSelfMapZ α (r + 1) ≤ differentialObjectSelfMapZ α r) ∧
      (∀ r, differentialObjectSelfMapB α r ≤ differentialObjectSelfMapZ α r) := by
  sorry

noncomputable def differentialObjectSelfMapPageComponent
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) : C :=
  Formalization.Books.Homology.Unit20.selfMapPageComponent α r

noncomputable def differentialObjectSelfMapPageAsQuotient
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (differentialObjectSelfMapB α (r + 1))
    (differentialObjectSelfMapZ α (r + 1))
    (differentialObjectSelfMap_B_le_Z α (r + 1))

theorem differentialObjectSelfMap_page_quotient_description
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Nonempty (differentialObjectSelfMapPageComponent α (r + 1) ≅
      differentialObjectSelfMapPageAsQuotient α r) := by
  sorry

abbrev differentialObjectSelfMapPageClassOfCycle
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ)
    {T : C} (z : T ⟶ (differentialObjectSelfMapCyclePlus α r : C)) :
    T ⟶ differentialObjectSelfMapPageComponent α r :=
  Formalization.Books.Homology.Unit20.selfMapPageClassOfCycle α r z

/-- The categorical/test-object form of the rule defining `dᵣ` on the page. -/
abbrev DifferentialObjectSelfMapPageDifferentialRule
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :=
  Formalization.Books.Homology.Unit20.SelfMapPageDifferentialRule α r

theorem differentialObjectSelfMap_page_differential_rule
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) (_hr : 1 ≤ r) :
    Nonempty (DifferentialObjectSelfMapPageDifferentialRule α r) := by
  exact Formalization.Books.Homology.Unit20.selfMap_page_differential_rule_exists α r

/-
The two inclusions in the source warning are deliberately predicates, not
assumptions.  The only unconditional inclusion is the one proved above.
-/
abbrev differentialObjectSelfMapAlphaSubobject
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : Subobject A.carrier :=
  Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective

abbrev differentialObjectSelfMapWarningBoundaryInclusion
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) : Prop :=
  Formalization.Books.Homology.Unit20.selfMapWarningBoundaryInclusion α r

abbrev differentialObjectSelfMapWarningCycleInclusion
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) : Prop :=
  Formalization.Books.Homology.Unit20.selfMapWarningCycleInclusion α r

theorem differentialObjectSelfMap_page_formula
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    differentialObjectSelfMapPageComponent α r =
      Formalization.Books.Homology.Unit20.subquotientObject
        (differentialObjectSelfMapBoundaryPlus α r)
        (differentialObjectSelfMapCyclePlus α r)
        (differentialObjectSelfMap_boundary_plus_le_cycle_plus α r) := by
  exact Formalization.Books.Homology.Unit20.selfMap_page_formula α r

/-! ### Shifted differential objects -/

abbrev ShiftedDifferentialObject (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] (S : C ≌ C) :=
  Formalization.Books.Homology.Unit20.ShiftedDifferentialObject C S

abbrev ShiftedDifferentialObjectHom {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {S : C ≌ C}
    (A B : ShiftedDifferentialObject C S) :=
  Formalization.Books.Homology.Unit20.ShiftedDifferentialObjectHom A B

/-- The category of `S`-shifted differential objects is abelian. -/
theorem shiftedDifferentialObject_category_abelian
    {C : Type u} [Category.{v} C] [Abelian C] {S : C ≌ C} :
    Nonempty (Abelian (ShiftedDifferentialObject C S)) := by
  exact Formalization.Books.Homology.Unit20.shiftedDifferentialObject_abelian

/-- `H(A,d) = Ker(d) / Im(S⁻¹d)` for a shifted differential. -/
abbrev shiftedDifferentialObjectHomology {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} (A : ShiftedDifferentialObject C S) : C :=
  Formalization.Books.Homology.Unit20.shiftedDifferentialHomology A

abbrev shiftedDifferentialObjectShift {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} (A : ShiftedDifferentialObject C S) :
    ShiftedDifferentialObject C S :=
  Formalization.Books.Homology.Unit20.shiftedDifferentialObjectShift S A

theorem shiftedDifferentialObjectHomology_shift_iso
    {C : Type u} [Category.{v} C] [Abelian C] {S : C ≌ C}
    (A : ShiftedDifferentialObject C S) :
    Nonempty (shiftedDifferentialObjectHomology (shiftedDifferentialObjectShift A) ≅
      S.functor.obj (shiftedDifferentialObjectHomology A)) := by
  exact Formalization.Books.Homology.Unit20.shiftedDifferentialHomology_shift_iso A

/-- A source-faithful interface for the action of a commuting shift `T`.

The equation in `differential_formula` is the categorical form of `Td`;
`eqToHom` transports the target along the stated equality `TS = ST`.
-/
structure ShiftedDifferentialObjectTData
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (S T : C ≌ C) (hST : T.functor ⋙ S.functor = S.functor ⋙ T.functor)
    (A : ShiftedDifferentialObject C S) where
  differential : T.functor.obj A.carrier ⟶ S.functor.obj (T.functor.obj A.carrier)
  differential_squared : differential ≫ S.functor.map differential = 0
  differential_formula :
    differential = T.functor.map A.d ≫
      eqToHom (congrArg (fun F : C ⥤ C => F.obj A.carrier) hST).symm

theorem shiftedDifferentialObjectTData_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : C ≌ C) (hST : T.functor ⋙ S.functor = S.functor ⋙ T.functor)
    (A : ShiftedDifferentialObject C S) :
    Nonempty (ShiftedDifferentialObjectTData S T hST A) := by
  sorry

noncomputable def shiftedDifferentialObjectTData
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : C ≌ C) (hST : T.functor ⋙ S.functor = S.functor ⋙ T.functor)
    (A : ShiftedDifferentialObject C S) :
    ShiftedDifferentialObjectTData S T hST A :=
  Classical.choice (shiftedDifferentialObjectTData_exists S T hST A)

def shiftedDifferentialObjectT
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {S T : C ≌ C} {hST : T.functor ⋙ S.functor = S.functor ⋙ T.functor}
    {A : ShiftedDifferentialObject C S}
    (D : ShiftedDifferentialObjectTData S T hST A) :
    ShiftedDifferentialObject C S where
  carrier := T.functor.obj A.carrier
  d := D.differential
  d_squared := D.differential_squared

/-! ### Shifted short exact sequences and shifted homology -/

abbrev ShiftedDifferentialShortExact {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C}
    (A B D : ShiftedDifferentialObject C S) :=
  Formalization.Books.Homology.Unit20.ShiftedDifferentialShortExact A B D

abbrev ShiftedDifferentialLongExactSequence {C : Type u} [Category.{v} C]
    [Abelian C] (S : C ≌ C) (X : ℤ → C) :=
  Formalization.Books.Homology.Unit20.ShiftedLongExactSequence S X

theorem shiftedDifferentialShortExact_homology_long_exact
    {C : Type u} [Category.{v} C] [Abelian C] {S : C ≌ C}
    {A B D : ShiftedDifferentialObject C S}
    (Q : ShiftedDifferentialShortExact A B D) :
    ∃ X : ℤ → C, Nonempty (ShiftedDifferentialLongExactSequence S X) := by
  exact Formalization.Books.Homology.Unit20.shiftedDifferentialShortExact_homology_long_exact Q

/-! ### The shifted injective self-map and exact couple -/

abbrev ShiftedInjectiveSelfMapData (C : Type u) [Category.{v} C]
    [Abelian C] (S T : C ≌ C) :=
  Formalization.Books.Homology.Unit20.ShiftedSelfMapData C S T

abbrev shiftedSelfMapQuotient {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) :
    ShiftedDifferentialObject C S :=
  Formalization.Books.Homology.Unit20.shiftedSelfMapQuotient D

abbrev shiftedSelfMapE₁ {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) : C :=
  S.inverse.obj (shiftedDifferentialObjectHomology (shiftedSelfMapQuotient D))

abbrev ShiftedSelfMapExactCouple {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) :=
  Formalization.Books.Homology.Unit21.ShiftedExactCouple C (T.trans S) T
    (shiftedDifferentialObjectHomology D.A) (shiftedSelfMapE₁ D)

theorem shiftedSelfMap_exact_couple_exists
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    Nonempty (ShiftedSelfMapExactCouple D) := by
  exact Formalization.Books.Homology.Unit20.shiftedSelfMap_exact_couple_exists D

noncomputable def shiftedSelfMapExactCouple
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ShiftedSelfMapExactCouple D :=
  Classical.choice (shiftedSelfMap_exact_couple_exists D)

/-- The map `\overline{α} : H(A,d) → T⁻¹H(A,d)`. -/
abbrev shiftedSelfMapBarAlpha
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedDifferentialObjectHomology D.A ⟶
      T.inverse.obj (shiftedDifferentialObjectHomology D.A) :=
  (shiftedSelfMapExactCouple D).alpha

/-- The boundary map `f : S⁻¹H(Q,d) → H(A,d)`. -/
abbrev shiftedSelfMapBoundary
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedSelfMapE₁ D ⟶ shiftedDifferentialObjectHomology D.A :=
  (shiftedSelfMapExactCouple D).f

/-- The quotient map `g : H(A,d) → TS(S⁻¹H(Q,d))`. -/
abbrev shiftedSelfMapQuotientHomologyMap
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedDifferentialObjectHomology D.A ⟶
      (T.trans S).functor.obj (shiftedSelfMapE₁ D) :=
  (shiftedSelfMapExactCouple D).g

/-! ### The translated spectral sequence and the zeroth page -/

abbrev TranslatedSpectralSequence (C : Type u) [Category.{v} C]
    [Abelian C] :=
  Formalization.Books.Homology.Unit20.TranslatedSpectralSequence C

/-- The source convention for the target of `dᵣ`: `TʳS` for `r ≥ 1`. -/
def shiftedDifferentialObjectTranslation {C : Type u} [Category.{v} C]
    (S T : C ≌ C) (r : ℤ) : C ≌ C :=
  if r = 1 then T.trans S
  else if 1 ≤ r then
    (Formalization.Books.Homology.Unit21.shiftedEquivalenceIterate T
      (Int.toNat r)).trans S
  else S

structure ShiftedDifferentialObjectSpectralSequenceData
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) where
  sequence : TranslatedSpectralSequence C
  starts_at_one : sequence.r₀ = 1
  translation : ∀ r, sequence.translation r = shiftedDifferentialObjectTranslation S T r
  page_one : Nonempty (sequence.page 1 ≅ shiftedSelfMapE₁ D)

theorem shiftedDifferentialObjectSpectralSequenceData_exists
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    Nonempty (ShiftedDifferentialObjectSpectralSequenceData D) := by
  sorry

noncomputable def shiftedDifferentialObjectSpectralSequenceData
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ShiftedDifferentialObjectSpectralSequenceData D :=
  Classical.choice (shiftedDifferentialObjectSpectralSequenceData_exists D)

noncomputable def shiftedDifferentialObjectSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) : TranslatedSpectralSequence C :=
  (shiftedDifferentialObjectSpectralSequenceData D).sequence

theorem shiftedSelfMap_spectral_sequence
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ∃ X : TranslatedSpectralSequence C, X.r₀ = 1 ∧
      Nonempty (X.page 1 ≅ shiftedSelfMapE₁ D) := by
  exact Formalization.Books.Homology.Unit20.shiftedSelfMap_spectral_sequence D

/- The source's `E₀ = S⁻¹Q` and `d₀ = S⁻¹d`. -/
abbrev shiftedSelfMapE₀ {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) : C :=
  S.inverse.obj (shiftedSelfMapQuotient D).carrier

abbrev shiftedSelfMapD₀ {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedSelfMapE₀ D ⟶ (shiftedSelfMapQuotient D).carrier :=
  Formalization.Books.Homology.Unit20.translatedPreviousDifferential S
    (shiftedSelfMapQuotient D).d

/-! ### The shifted `Bᵣ` and `Zᵣ` formulas -/

abbrev shiftedEquivalenceIterate {C : Type u} [Category.{v} C]
    (T : C ≌ C) (n : ℕ) : C ≌ C :=
  Formalization.Books.Homology.Unit21.shiftedEquivalenceIterate T n

/-
The following powers are indexed by `n`, so they describe the source's page
`r = n + 1` without using truncated subtraction in a dependent morphism
type.
-/

def shiftedSelfMapInverseAlphaPow
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ∀ n : ℕ, D.A.carrier ⟶
      (shiftedEquivalenceIterate T.symm n).functor.obj D.A.carrier
  | 0 => 𝟙 D.A.carrier
  | n + 1 => shiftedSelfMapInverseAlphaPow D n ≫
      (shiftedEquivalenceIterate T.symm n).functor.map D.alpha.hom

def shiftedSelfMapTAlpha
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    T.functor.obj D.A.carrier ⟶ D.A.carrier :=
  T.functor.map D.alpha.hom ≫ T.counitIso.hom.app D.A.carrier

def shiftedSelfMapTAlphaPow
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ∀ n : ℕ, (shiftedEquivalenceIterate T n).functor.obj D.A.carrier ⟶ D.A.carrier
  | 0 => 𝟙 D.A.carrier
  | n + 1 =>
      (shiftedEquivalenceIterate T n).functor.map (shiftedSelfMapTAlpha D) ≫
        shiftedSelfMapTAlphaPow D n

def shiftedSelfMapForwardAlphaPow
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    (shiftedEquivalenceIterate T n).functor.obj D.A.carrier ⟶
      T.inverse.obj D.A.carrier :=
  shiftedSelfMapTAlphaPow D n ≫ D.alpha.hom

def shiftedSelfMapInverseAlphaTail
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ∀ n : ℕ, T.inverse.obj D.A.carrier ⟶
      (shiftedEquivalenceIterate T.symm (n + 1)).functor.obj D.A.carrier
  | 0 => 𝟙 (T.inverse.obj D.A.carrier)
  | n + 1 => shiftedSelfMapInverseAlphaTail D n ≫
      (shiftedEquivalenceIterate T.symm (n + 1)).functor.map D.alpha.hom

def shiftedSelfMapBoundaryTargetMap
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    (shiftedEquivalenceIterate T.symm (n + 1)).functor.obj
        (S.inverse.obj D.A.carrier) ⟶
      (shiftedEquivalenceIterate T.symm (n + 1)).functor.obj D.A.carrier :=
  (shiftedEquivalenceIterate T.symm (n + 1)).functor.map
    (Formalization.Books.Homology.Unit20.translatedPreviousDifferential S D.A.d)

def shiftedSelfMapBoundaryPreimage
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    Subobject (T.inverse.obj D.A.carrier) :=
  (Subobject.pullback (shiftedSelfMapInverseAlphaTail D n)).obj
    ((Subobject.«exists» (shiftedSelfMapBoundaryTargetMap D n)).obj ⊤)

def shiftedSelfMapCyclePreimage
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    Subobject (S.inverse.obj (T.inverse.obj D.A.carrier)) :=
  (Subobject.pullback
    (Formalization.Books.Homology.Unit20.translatedPreviousDifferential S
      D.targetDifferential)).obj
    ((Subobject.«exists» (shiftedSelfMapForwardAlphaPow D n)).obj ⊤)

/- The first formula in the source gives `S B_(n+1)` as a subobject of `Q`. -/
def shiftedSelfMapSB
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    Subobject ((shiftedSelfMapQuotient D).carrier) :=
  Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
    (cokernel.π D.alpha.hom) (shiftedSelfMapBoundaryPreimage D n)

theorem shiftedSelfMap_boundary_formula
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    shiftedSelfMapSB D n =
      Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
        (cokernel.π D.alpha.hom) (shiftedSelfMapBoundaryPreimage D n) := rfl

/- The second formula gives `Z_(n+1)` after applying `S⁻¹` to the quotient. -/
def shiftedSelfMapCycleSubobject
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    Subobject (shiftedSelfMapE₀ D) :=
  Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
    (S.inverse.map (cokernel.π D.alpha.hom))
    (shiftedSelfMapCyclePreimage D n)

theorem shiftedSelfMap_cycle_formula
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    shiftedSelfMapCycleSubobject D n =
      Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
        (S.inverse.map (cokernel.π D.alpha.hom)) (shiftedSelfMapCyclePreimage D n) := rfl

def shiftedSelfMapB
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ℕ → Subobject (shiftedSelfMapE₀ D)
  | 0 => ⊥
  | n + 1 => Subobject.mk (S.inverse.map (shiftedSelfMapSB D n).arrow)

def shiftedSelfMapZ
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ℕ → Subobject (shiftedSelfMapE₀ D)
  | 0 => ⊤
  | n + 1 => shiftedSelfMapCycleSubobject D n

theorem shiftedSelfMap_B_le_Z
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (r : ℕ) :
    shiftedSelfMapB D r ≤ shiftedSelfMapZ D r := by
  sorry

theorem shiftedSelfMap_filtration
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedSelfMapB D 0 = ⊥ ∧ shiftedSelfMapZ D 0 = ⊤ ∧
      (∀ r, shiftedSelfMapB D r ≤ shiftedSelfMapB D (r + 1)) ∧
      (∀ r, shiftedSelfMapZ D (r + 1) ≤ shiftedSelfMapZ D r) ∧
      (∀ r, shiftedSelfMapB D r ≤ shiftedSelfMapZ D r) := by
  sorry

noncomputable def shiftedSelfMapPageComponent
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (shiftedSelfMapB D (n + 1)) (shiftedSelfMapZ D (n + 1))
    (shiftedSelfMap_B_le_Z D (n + 1))

def shiftedSelfMapPageTranslation
    {C : Type u} [Category.{v} C] {S T : C ≌ C} (n : ℕ) : C ≌ C :=
  (shiftedEquivalenceIterate T (n + 1)).trans S

/-
This predicate is the source's lifting equation.  It is useful independently
of the chosen quotient representatives and is the categorical replacement for
the source's elementwise phrase “choose `x'` and `y`”.
-/
def shiftedSelfMapPageLiftCondition
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) {X : C}
    (x' : X ⟶ S.inverse.obj (T.inverse.obj D.A.carrier))
    (y : X ⟶ (shiftedEquivalenceIterate T n).functor.obj D.A.carrier) : Prop :=
  x' ≫ Formalization.Books.Homology.Unit20.translatedPreviousDifferential S
      D.targetDifferential =
    y ≫ shiftedSelfMapForwardAlphaPow D n

/-
The page differential has target `T^(n+1) S E_(n+1)` and squares to zero.
The source's “represented by the class of the image of `y`” is exposed by
the quotient page `shiftedSelfMapPageComponent` together with the explicit
lift equation `shiftedSelfMapPageLiftCondition`; this avoids pretending that
an arbitrary category has element terms.
-/
structure ShiftedSelfMapPageDifferentialRule
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) where
  differential : shiftedSelfMapPageComponent D n ⟶
    (shiftedSelfMapPageTranslation (S := S) (T := T) n).functor.obj
      (shiftedSelfMapPageComponent D n)
  differential_squared : differential ≫
      (shiftedSelfMapPageTranslation (S := S) (T := T) n).functor.map differential = 0

theorem shiftedSelfMap_page_differential_rule
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    Nonempty (ShiftedSelfMapPageDifferentialRule D n) := by
  sorry

/-! ### Source-facing accounting for the shifted page convention -/

theorem shiftedSelfMap_page_zero_differential
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedSelfMapD₀ D ≫ (shiftedSelfMapQuotient D).d = 0 := by
  exact Formalization.Books.Homology.Unit20.translatedPreviousDifferential_comp
    (shiftedSelfMapQuotient D).d (shiftedSelfMapQuotient D).d_squared

theorem shiftedSelfMap_page_translation_at_one
    {C : Type u} [Category.{v} C] {S T : C ≌ C} :
    shiftedDifferentialObjectTranslation S T 1 = T.trans S := by
  simp [shiftedDifferentialObjectTranslation]

end Formalization.Books.Homology.Unit22
