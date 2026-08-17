import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Commutative Algebra, Chapter 86: Mittag-Leffler systems

The source's inverse systems are represented by functors on the opposite of a
preorder.  Mathlib's `Functor.eventualRange` and `Functor.toEventualRanges`
are the canonical stable-image construction, and
`Functor.IsMittagLeffler` is the source's stabilization condition.
-/

namespace Formalization.Books.Algebra.Unit86

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21

universe u v w

noncomputable section

/-! ## The stable image and the Mittag-Leffler condition -/

/- The source's stable image `A'_i = ⋂_{j ≥ i} φ_{ji}(A_j)` is exactly
`Functor.eventualRange`.  The following is the source-facing form of the
canonical Mathlib characterization. -/
theorem isMittagLeffler_iff_eventualRange
    {I : Type u} [Preorder I] (F : InverseSystem I (Type v)) :
    F.IsMittagLeffler ↔
      ∀ i : Iᵒᵖ, ∃ (j : Iᵒᵖ) (f : j ⟶ i),
        F.eventualRange i = Set.range (F.map f) :=
  F.isMittagLeffler_iff_eventualRange

/- For a system of modules, the same stable image can also be recorded as a
submodule: the intersection of the ranges of all transition maps into the
chosen stage. -/
def moduleEventualRange
    {R : Type u} [Ring R] {I : Type v} [Preorder I]
    (F : InverseSystem I (ModuleCat.{w} R)) (i : Iᵒᵖ) :
    Submodule R (F.obj i) :=
  ⨅ (j : Iᵒᵖ) (f : j ⟶ i), LinearMap.range (F.map f).hom

theorem moduleEventualRange_map
    {R : Type u} [Ring R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I]
    (F : InverseSystem I (ModuleCat.{w} R))
    {i j : Iᵒᵖ} (f : i ⟶ j) :
    (F.map f).hom '' (moduleEventualRange F i : Set (F.obj i)) ⊆
      (moduleEventualRange F j : Set (F.obj j)) := by
  sorry

/- The module version in the source is the underlying-set condition. -/
abbrev IsMittagLefflerModuleSystem
    {R : Type u} [Ring R] {I : Type v} [Preorder I]
    (F : InverseSystem I (ModuleCat.{w} R)) : Prop :=
  (F ⋙ CategoryTheory.forget (ModuleCat.{w} R)).IsMittagLeffler

/-! ## Surjective systems and restriction to stable images -/

theorem isMittagLeffler_of_surjective
    {I : Type u} [Preorder I] (F : InverseSystem I (Type v))
    (hF : ∀ ⦃i j : Iᵒᵖ⦄ (f : i ⟶ j),
      Function.Surjective (F.map f)) :
    F.IsMittagLeffler :=
  F.isMittagLeffler_of_surjective hF

theorem eventualRange_map_mapsTo
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : InverseSystem I (Type v)) {i j : Iᵒᵖ} (f : i ⟶ j) :
    (F.eventualRange i).MapsTo (F.map f) (F.eventualRange j) :=
  F.eventualRange_mapsTo f

theorem eventualRange_map_surjective
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : InverseSystem I (Type v)) (hF : F.IsMittagLeffler)
    {i j : Iᵒᵖ} (f : i ⟶ j) :
    Function.Surjective (F.toEventualRanges.map f) := by
  exact F.surjective_toEventualRanges hF f

/- The source's equality of inverse limits is represented by the canonical
equivalence of compatible sections. -/
def eventualRange_sections_equiv
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : InverseSystem I (Type v)) :
    F.toEventualRanges.sections ≃ F.sections :=
  F.toEventualRangesSectionsEquiv

theorem module_isMittagLeffler_of_surjective
    {R : Type u} [Ring R] {I : Type v} [Preorder I]
    (F : InverseSystem I (ModuleCat.{w} R))
    (hF : ∀ ⦃i j : Iᵒᵖ⦄ (f : i ⟶ j),
      Function.Surjective ((F ⋙ CategoryTheory.forget (ModuleCat.{w} R)).map f)) :
    IsMittagLefflerModuleSystem F :=
  Functor.isMittagLeffler_of_surjective
    (F ⋙ CategoryTheory.forget (ModuleCat.{w} R)) hF

/-! ## Countable nonempty limits -/

theorem nonempty_limit_of_countable_mittagLeffler
    {I : Type u} [Preorder I] [Countable I]
    (hI : IsDirectedSet I) (F : InverseSystem I (Type v))
    (hF : F.IsMittagLeffler)
    (hne : ∀ i : Iᵒᵖ, Nonempty (F.obj i)) :
    F.sections.Nonempty := by
  sorry

/-! ## Exactness of countable inverse limits -/

/- A short exact sequence of inverse systems is exact objectwise.  This is the
pointwise form of the source's exact sequence
`0 → A_i → B_i → C_i → 0`. -/
def IsPointwiseShortExact
    {I : Type u} [Preorder I]
  (S : ShortComplex (InverseSystem I AddCommGrpCat)) : Prop :=
  ∀ i : Iᵒᵖ,
    (((evaluation (Iᵒᵖ) AddCommGrpCat).obj i).mapShortComplex.obj S).ShortExact

/- The short complex obtained by applying the inverse-limit functor to a
short complex of inverse systems. -/
noncomputable def inverseLimitShortComplex
    {I : Type u} [Preorder I]
    (S : ShortComplex (InverseSystem I AddCommGrpCat))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    ShortComplex AddCommGrpCat where
  f := limMap S.f
  g := limMap S.g
  zero := by
    apply limit.hom_ext
    intro i
    simp only [Category.assoc, limMap_π, zero_comp]
    rw [← Category.assoc, limMap_π S.f i, Category.assoc,
      ← NatTrans.comp_app, S.zero]
    simp

theorem inverse_limit_shortExact_of_countable_mittagLeffler
    {I : Type u} [Preorder I] [Countable I]
    (hI : IsDirectedSet I)
    (S : ShortComplex (InverseSystem I AddCommGrpCat))
    (hS : IsPointwiseShortExact S)
    (hML : (S.X₁ ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler)
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (inverseLimitShortComplex S).ShortExact := by
  sorry

end

end Formalization.Books.Algebra.Unit86
