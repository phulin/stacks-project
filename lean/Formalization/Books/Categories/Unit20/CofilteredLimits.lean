import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Quotient
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
  constructor
  · intro h
    have hne : Nonempty I := @CategoryTheory.IsCofiltered.nonempty I _ h
    refine ⟨hne, ?_, ?_⟩
    · intro x y
      obtain ⟨z, f, g, _⟩ :=
        @IsCofilteredOrEmpty.cone_objs I _ h.toIsCofilteredOrEmpty x y
      exact ⟨z, ⟨f⟩, ⟨g⟩⟩
    · intro x y a b
      obtain ⟨w, c, hc⟩ :=
        @IsCofilteredOrEmpty.cone_maps I _ h.toIsCofilteredOrEmpty x y a b
      exact ⟨w, c, by simpa using congrArg (fun k => (𝟭 I).map k) hc⟩
  · rintro ⟨hne, hobj, hmap⟩
    refine
      { cone_objs := ?_
        cone_maps := ?_
        nonempty := hne }
    · intro x y
      obtain ⟨z, f, g⟩ := hobj x y
      exact ⟨z, f.some, g.some, trivial⟩
    · intro x y a b
      obtain ⟨w, c, hc⟩ := hmap a b
      exact ⟨w, c, by simpa using hc⟩

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
  classical
  let r : HomRel I := S.homRel
  let q : I ⥤ CategoryTheory.Quotient r := CategoryTheory.Quotient.functor r
  have hQ : CategoryTheory.IsCofiltered (CategoryTheory.Quotient r) :=
    { cone_objs := by
        rintro ⟨x⟩ ⟨y⟩
        obtain ⟨z, f, g⟩ := hS.2.1 x y
        exact ⟨q.obj z, q.map f.some, q.map g.some, trivial⟩
      cone_maps := by
        intro X Y f g
        induction f using CategoryTheory.Quotient.induction with
        | h f =>
          refine Quot.inductionOn g ?_
          intro g
          obtain ⟨z, c, hc⟩ := hS.2.2 f g
          refine ⟨q.obj z, q.map c, ?_⟩
          change q.map c ≫ q.map f = q.map c ≫ q.map g
          rw [← q.map_comp, ← q.map_comp]
          simpa [q, r] using CategoryTheory.Quotient.sound r hc
      nonempty := ⟨⟨hS.1.some⟩⟩ }
  let T : CategoryTheory.Quotient r ⥤ Type u :=
    CategoryTheory.Quotient.lift r S (by
      intro x y f g h
      simpa [r] using h)
  have hQT : q ⋙ T = S := by
    apply CategoryTheory.Quotient.lift_spec
  have hfinite : ∀ j : CategoryTheory.Quotient r, Finite (T.obj j) := fun j => by
    change Finite (S.obj j.as)
    infer_instance
  have hnonempty : ∀ j : CategoryTheory.Quotient r, Nonempty (T.obj j) := fun j => by
    change Nonempty (S.obj j.as)
    infer_instance
  obtain ⟨u, hu⟩ :=
    @nonempty_sections_of_finite_cofiltered_system (CategoryTheory.Quotient r) _
      hQ.toIsCofilteredOrEmpty T hfinite hnonempty
  refine ⟨(Types.limitEquivSections S).symm ⟨fun i => u (q.obj i), ?_⟩⟩
  intro i j f
  have hmap : T.map (q.map f) = S.map f := by
    simpa using Functor.congr_hom hQT f
  rw [← hmap]
  exact hu (q.map f)

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
  constructor
  · intro i
    cases i
    · change Finite PUnit
      infer_instance
    · change Finite Bool
      infer_instance
  · constructor
    · intro i
      cases i
      · change Nonempty PUnit
        exact ⟨PUnit.unit⟩
      · change Nonempty Bool
        exact ⟨false⟩
    · intro h
      obtain ⟨x⟩ := h
      have hzero := ConcreteCategory.congr_hom (limit.w finite_nonempty_set_limit_counterexample
        WalkingParallelPairHom.left) x
      have hone := ConcreteCategory.congr_hom (limit.w finite_nonempty_set_limit_counterexample
        WalkingParallelPairHom.right) x
      dsimp at hzero hone
      simpa [finite_nonempty_set_limit_counterexample] using hzero.trans hone.symm

end

end Formalization.Books.Categories.Unit20
