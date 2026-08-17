import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Categories, Chapter 23: Exact functors

The source defines left exact, right exact, and exact functors, and then
characterizes the first two notions by preservation of standard finite
limit and colimit shapes.  Mathlib's preservation classes and walking-shape
interfaces are used directly.
-/

namespace Formalization.Books.Categories.Unit23

open CategoryTheory
open CategoryTheory.Limits

universe u v u' v'

/-! ## Exact functors -/

/-- A functor out of a finitely complete category is left exact when it
preserves all finite limits. -/
def IsLeftExact {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] [HasFiniteLimits A]
    (F : A ⥤ B) : Prop :=
  PreservesFiniteLimits F

/-- A functor out of a finitely cocomplete category is right exact when it
preserves all finite colimits. -/
def IsRightExact {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] [HasFiniteColimits A]
    (F : A ⥤ B) : Prop :=
  PreservesFiniteColimits F

/-- A functor out of a category with finite limits and colimits is exact when
it is both left exact and right exact. -/
def IsExact {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] [HasFiniteLimits A]
    [HasFiniteColimits A] (F : A ⥤ B) : Prop :=
  IsLeftExact F ∧ IsRightExact F

/- The displayed identity in the source proof expressing an equalizer as two
   successive pullbacks is already represented by
   `Unit18.equalizerViaPullbacks_isEqualizer`; no parallel helper is needed. -/

/- The source's three-way equivalence is recorded as two adjacent pairwise
   equivalences, following the chapter's other three-criterion interfaces. -/
theorem isLeftExact_iff_preservesFiniteProducts_and_equalizers_iff_preservesTerminal_and_pullbacks
    {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] [HasFiniteLimits A]
    (F : A ⥤ B) :
    (IsLeftExact F ↔
      (PreservesFiniteProducts F ∧
        PreservesLimitsOfShape WalkingParallelPair F)) ∧
      ((PreservesFiniteProducts F ∧
          PreservesLimitsOfShape WalkingParallelPair F) ↔
        (PreservesLimitsOfShape (Discrete.{0} PEmpty) F ∧
          PreservesLimitsOfShape WalkingCospan F)) := by
  constructor <;> constructor
  · intro h
    let h' : PreservesFiniteLimits F := h
    exact
      ⟨⟨fun n => h'.preservesFiniteLimits (Discrete (Fin n))⟩,
        h'.preservesFiniteLimits WalkingParallelPair⟩
  · rintro ⟨h₁, h₂⟩
    exact
      @preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts A _ B _ _ _ F h₂ h₁
  · rintro ⟨h₁, h₂⟩
    let h' : PreservesFiniteLimits F :=
      @preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts A _ B _ _ _ F h₂ h₁
    exact
      ⟨h'.preservesFiniteLimits (Discrete.{0} PEmpty),
        h'.preservesFiniteLimits WalkingCospan⟩
  · rintro ⟨h₁, h₂⟩
    let h' : PreservesFiniteLimits F :=
      @preservesFiniteLimits_of_preservesTerminal_and_pullbacks A _ B _ _ _ F h₁ h₂
    exact
      ⟨⟨fun n => h'.preservesFiniteLimits (Discrete (Fin n))⟩,
        h'.preservesFiniteLimits WalkingParallelPair⟩

/- The dual characterization for right exact functors. -/
theorem isRightExact_iff_preservesFiniteCoproducts_and_coequalizers_iff_preservesInitial_and_pushouts
    {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] [HasFiniteColimits A]
    (F : A ⥤ B) :
    (IsRightExact F ↔
      (PreservesFiniteCoproducts F ∧
        PreservesColimitsOfShape WalkingParallelPair F)) ∧
      ((PreservesFiniteCoproducts F ∧
          PreservesColimitsOfShape WalkingParallelPair F) ↔
        (PreservesColimitsOfShape (Discrete.{0} PEmpty) F ∧
          PreservesColimitsOfShape WalkingSpan F)) := by
  constructor <;> constructor
  · intro h
    let h' : PreservesFiniteColimits F := h
    exact
      ⟨⟨fun n => h'.preservesFiniteColimits (Discrete (Fin n))⟩,
        h'.preservesFiniteColimits WalkingParallelPair⟩
  · rintro ⟨h₁, h₂⟩
    exact
      @preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts A _ B _ _ _ F h₂ h₁
  · rintro ⟨h₁, h₂⟩
    let h' : PreservesFiniteColimits F :=
      @preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts A _ B _ _ _ F h₂ h₁
    exact
      ⟨h'.preservesFiniteColimits (Discrete.{0} PEmpty),
        h'.preservesFiniteColimits WalkingSpan⟩
  · rintro ⟨h₁, h₂⟩
    let h' : PreservesFiniteColimits F :=
      @preservesFiniteColimits_of_preservesInitial_and_pushouts A _ B _ _ _ F h₁ h₂
    exact
      ⟨⟨fun n => h'.preservesFiniteColimits (Discrete (Fin n))⟩,
        h'.preservesFiniteColimits WalkingParallelPair⟩

end Formalization.Books.Categories.Unit23
