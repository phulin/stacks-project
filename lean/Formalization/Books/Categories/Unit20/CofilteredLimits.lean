import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Categories, Chapter 20: Cofiltered limits

Mathlib's `CategoryTheory.IsCofiltered` is the canonical notion for a
cofiltered index category.  The source also defines when a diagram is
cofiltered: the index category need not itself identify the parallel maps,
provided that the diagram does.  `IsCofilteredDiagram` records precisely that
diagram-level condition.
-/

namespace Formalization.Books.Categories.Unit20

open CategoryTheory
open CategoryTheory.Limits

universe u v u' v' w

noncomputable section

/-! ## Cofiltered diagrams -/

/- The source calls a diagram `M : I ⥤ C` cofiltered (or codirected) when
   the index category is nonempty, every pair of objects has a common object
   mapping to it, and parallel maps become equal after applying `M` to a
   suitable map into their source.  The final equality is written with Lean's
   composition convention: `c ≫ a` is the source's `a ∘ c`. -/
def IsCofilteredDiagram {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C) : Prop :=
  Nonempty I ∧
    (∀ x y : I, ∃ z : I, Nonempty (z ⟶ x) ∧ Nonempty (z ⟶ y)) ∧
    (∀ {x y : I} (a b : x ⟶ y), ∃ (w : I) (c : w ⟶ x),
      M.map (c ≫ a) = M.map (c ≫ b))

/- `codirected` is the source's synonymous terminology for a cofiltered
   diagram. -/
abbrev IsCodirectedDiagram {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C) : Prop :=
  IsCofilteredDiagram M

/- The source's definition of a cofiltered index category is the special case
   of the identity diagram; Mathlib's `IsCofiltered` is its canonical index-
   category interface. -/
theorem isCofiltered_iff_id_isCofilteredDiagram
    (I : Type u) [Category.{v} I] :
    CategoryTheory.IsCofiltered I ↔
      IsCofilteredDiagram (𝟭 I) := by
  sorry

/- If the index category is already cofiltered, its equalizing morphisms make
   the diagram-level condition hold for every diagram. -/
theorem isCofilteredDiagram_of_isCofiltered
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] (M : I ⥤ C)
    [CategoryTheory.IsCofiltered I] :
    IsCofilteredDiagram M := by
  refine ⟨CategoryTheory.IsCofiltered.nonempty, ?_, ?_⟩
  · intro x y
    obtain ⟨z, f, g, _⟩ := IsCofilteredOrEmpty.cone_objs x y
    exact ⟨z, ⟨f⟩, ⟨g⟩⟩
  · intro x y a b
    obtain ⟨w, c, h⟩ := IsCofilteredOrEmpty.cone_maps a b
    exact ⟨w, c, congrArg M.map h⟩

/- The finite-set example in the source uses the diagram-level notion, not
   merely a cofiltered index category.  Smallness supplies the ordinary limit
   of a diagram of types through Mathlib's canonical `Type` limits. -/
theorem nonempty_limit_of_finite_nonempty_cofiltered_diagram
    {I : Type v} [Category.{w} I] [Small.{u} I]
    (S : I ⥤ Type u) (hS : IsCofilteredDiagram S)
    [∀ i : I, Finite (S.obj i)] [∀ i : I, Nonempty (S.obj i)] :
    Nonempty (limit S) := by
  sorry

/- The source warns that the finite/nonempty conclusion fails for arbitrary
   limits.  This concrete parallel-pair diagram has finite nonempty values,
   but its two maps disagree everywhere, so its limit is empty. -/
noncomputable def finite_nonempty_set_limit_counterexample :
    WalkingParallelPair ⥤ Type :=
  parallelPair
    (↾fun _ : PUnit.{1} => false)
    (↾fun _ : PUnit.{1} => true)

theorem finite_nonempty_set_limit_counterexample_spec :
    (∀ i, Finite (finite_nonempty_set_limit_counterexample.obj i)) ∧
      (∀ i, Nonempty (finite_nonempty_set_limit_counterexample.obj i)) ∧
      ¬ Nonempty (limit finite_nonempty_set_limit_counterexample) := by
  sorry

end

end Formalization.Books.Categories.Unit20
