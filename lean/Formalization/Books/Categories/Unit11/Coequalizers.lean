import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Categories, Chapter 11: Coequalizers

Mathlib represents a coequalizer as a colimiting cofork for a parallel pair.
`IsCoequalizer` exposes the source's equation together with this canonical
universal-property interface, while retaining Mathlib's `Cofork` and
`IsColimit` declarations.
-/

namespace Formalization.Books.Categories.Unit11

open CategoryTheory
open CategoryTheory.Limits

universe v u

/-! ## Coequalizers -/

/-- A morphism is a coequalizer of a parallel pair when its canonical cofork
is colimiting.  The existential records the coequalizing equation, and
`Nonempty` reflects Mathlib's proposition-valued existence interface for a
chosen colimit cocone. -/
def IsCoequalizer {C : Type u} [Category.{v} C]
    {X Y Z : C} (c : Y ⟶ Z) (a b : X ⟶ Y) : Prop :=
  ∃ h : a ≫ c = b ≫ c, Nonempty (IsColimit (Cofork.ofπ c h))

/-- The coequalizing equation carried by an `IsCoequalizer`. -/
theorem IsCoequalizer.condition
    {C : Type u} [Category.{v} C]
    {X Y Z : C} {a b : X ⟶ Y} {c : Y ⟶ Z}
    (h : IsCoequalizer c a b) : a ≫ c = b ≫ c := by
  exact h.choose

/-- The universal factorization property of an `IsCoequalizer`. -/
theorem IsCoequalizer.existsUnique
    {C : Type u} [Category.{v} C]
    {X Y Z : C} {a b : X ⟶ Y} {c : Y ⟶ Z}
    (h : IsCoequalizer c a b) {W : C} (t : Y ⟶ W)
    (ht : a ≫ t = b ≫ t) : ∃! s : Z ⟶ W, c ≫ s = t := by
  rcases h with ⟨hc, ⟨hlim⟩⟩
  exact Cofork.IsColimit.existsUnique hlim t ht

/-- The source definition is equivalent to the explicit coequalizing equation
and unique factorization property. -/
theorem isCoequalizer_iff
    {C : Type u} [Category.{v} C]
    {X Y Z : C} {a b : X ⟶ Y} {c : Y ⟶ Z} :
    IsCoequalizer c a b ↔
      a ≫ c = b ≫ c ∧
        ∀ {W : C} (t : Y ⟶ W), a ≫ t = b ≫ t →
          ∃! s : Z ⟶ W, c ≫ s = t := by
  constructor
  · intro h
    exact ⟨h.condition, fun t ht => h.existsUnique t ht⟩
  · rintro ⟨hc, hfactor⟩
    refine ⟨hc, ⟨Cofork.IsColimit.ofExistsUnique ?_⟩⟩
    intro s
    simpa using hfactor s.π s.condition

/-- Two coequalizers of the same parallel pair are uniquely isomorphic in a
way compatible with their coequalizer maps. -/
theorem coequalizer_unique_up_to_unique_iso
    {C : Type u} [Category.{v} C]
    {X Y Z Z' : C} {a b : X ⟶ Y}
    {c : Y ⟶ Z} {c' : Y ⟶ Z'}
    (hc : IsCoequalizer c a b) (hc' : IsCoequalizer c' a b) :
    ∃! i : Z ≅ Z', c ≫ i.hom = c' := by
  rcases hc with ⟨hcoeq, ⟨hlim⟩⟩
  rcases hc' with ⟨hcoeq', ⟨hlim'⟩⟩
  let i : (Cofork.ofπ c hcoeq).pt ≅ (Cofork.ofπ c' hcoeq').pt :=
    IsColimit.coconePointUniqueUpToIso hlim hlim'
  have hi : c ≫ i.hom = c' := by
    simpa [i] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hlim hlim'
        WalkingParallelPair.one
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply Iso.ext
  apply Cofork.IsColimit.hom_ext hlim
  exact hj.trans hi.symm

/- The source explains the preceding uniqueness by passing to the opposite
category, where coequalizers become equalizers.  The direct colimit proof above
uses Mathlib's canonical dual universal-property API, so no parallel opposite
category definition is needed here. -/

/- The source also notes the straightforward extension from two parallel
morphisms to more than two.  Mathlib's `Multicofork`/`HasMulticoequalizer`
interfaces provide that generalization; because the source gives no indexing
family or further assertion, no additional chapter-specific declaration is
needed. -/

end Formalization.Books.Categories.Unit11
