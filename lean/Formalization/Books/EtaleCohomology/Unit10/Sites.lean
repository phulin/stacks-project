import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Étale Cohomology, Chapter 10: Sites

The source section introduces families of morphisms with a fixed target and
sites as categories equipped with covering families.  Mathlib's
`CategoryTheory.Pretopology` uses presieves and assumes all pullbacks in the
underlying category, whereas the textbook keeps the indexed family data and
requires pullbacks only for members of a covering family.  The declarations
below retain that source-facing interface.  The example of a topological space
uses Mathlib's canonical category of open sets and its preorder pullbacks.
-/

namespace Formalization.Books.EtaleCohomology.Unit10

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u v

/-! ## Families with fixed target -/

/-- A family of morphisms whose codomain is the fixed object `U`. -/
structure FixedTargetFamily (C : Type u) [Category.{v} C] (U : C) where
  /-- The (possibly empty) indexing type of the family. -/
  index : Type u
  /-- The source object attached to each index. -/
  source : index → C
  /-- The morphism from each source object to the fixed target. -/
  hom : ∀ i, source i ⟶ U

namespace FixedTargetFamily

/-- The one-element family determined by a morphism. -/
def singleton {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U) :
    FixedTargetFamily C U where
  index := PUnit.{u + 1}
  source := fun _ => V
  hom := fun _ => f

/-- The empty family with fixed target `U`. -/
def empty {C : Type u} [Category.{v} C] (U : C) : FixedTargetFamily C U where
  index := ULift.{u} Empty
  source := fun i => i.down.elim
  hom := fun i => i.down.elim

/-- Compose a family over `U` with a covering family over each of its sources. -/
def compose {C : Type u} [Category.{v} C] {U : C}
    (F : FixedTargetFamily C U)
    (G : ∀ i, FixedTargetFamily C (F.source i)) :
    FixedTargetFamily C U where
  index := Σ i, (G i).index
  source := fun ij => (G ij.1).source ij.2
  hom := fun ij => (G ij.1).hom ij.2 ≫ F.hom ij.1

end FixedTargetFamily

/- The source section only refers to morphisms of these families and to
refinements, deferring their definitions to a later section.  Since it gives
no data or axioms for either notion here, no separate interface is introduced
at this point. -/

/-! ## Sites -/

/--
A site in the source's pretopological sense.

The `base_change` field explicitly records chosen pullback squares for every
member of a covering family, together with the covering family of their
projections.  This matches the source's local pullback hypothesis and does
not impose pullbacks on unrelated pairs of morphisms.  The smallness
convention is represented by the universe-bounded category `C` and by the
set-valued `coverings` field.
-/
structure Site (C : Type u) [Category.{v} C] where
  /-- The set of covering families with each fixed target. -/
  coverings : ∀ U : C, Set (FixedTargetFamily C U)
  /-- A singleton isomorphism is a covering family. -/
  has_isos : ∀ {U V : C} (f : V ⟶ U) [IsIso f],
    FixedTargetFamily.singleton f ∈ coverings U
  /-- Covering families are stable under composition of coverings. -/
  transitive : ∀ {U : C} (F : FixedTargetFamily C U)
    (G : ∀ i, FixedTargetFamily C (F.source i)),
    F ∈ coverings U → (∀ i, G i ∈ coverings (F.source i)) →
    FixedTargetFamily.compose F G ∈ coverings U
  /-- Covering families are stable under base change along any morphism. -/
  base_change : ∀ {U V : C} (F : FixedTargetFamily C U),
    F ∈ coverings U → (g : V ⟶ U) →
    ∃ (P : F.index → C)
      (pV : ∀ i, P i ⟶ V)
      (pU : ∀ i, P i ⟶ F.source i),
      (∀ i, IsPullback (pV i) (pU i) g (F.hom i)) ∧
      (({ index := F.index, source := P, hom := pV } :
        FixedTargetFamily C V) ∈ coverings V)

namespace Site

/-- A family is covering for a site when it belongs to the site's covering set. -/
def IsCovering {C : Type u} [Category.{v} C] (S : Site C)
    {U : C} (F : FixedTargetFamily C U) : Prop :=
  F ∈ S.coverings U

end Site

/-! ## The site of open subsets of a topological space -/

/-- A family of open inclusions covers its target when its sources have union
the target.  The pointwise formulation avoids choosing a union object. -/
def TopologicalCoveringFamily {X : Type u} [TopologicalSpace X]
    {U : Opens X} (F : FixedTargetFamily (Opens X) U) : Prop :=
  ∀ x : X, x ∈ U → ∃ i, x ∈ F.source i

/-- The pointwise covering predicate is equivalent to equality of the union with
the target open set. -/
theorem topologicalCoveringFamily_iff_iUnion_eq {X : Type u} [TopologicalSpace X]
    {U : Opens X} (F : FixedTargetFamily (Opens X) U) :
    TopologicalCoveringFamily F ↔ ⋃ i, (F.source i : Set X) = (U : Set X) := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
      exact (F.hom i).le hxi
    · intro hx
      obtain ⟨i, hxi⟩ := h x hx
      exact Set.mem_iUnion.2 ⟨i, hxi⟩
  · intro h x hx
    have hx' : x ∈ ⋃ i, (F.source i : Set X) := by
      rw [h]
      exact hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx'
    exact ⟨i, hxi⟩

/-- In the category of opens, the chosen pullback is the intersection. -/
theorem opens_pullback_eq_inf {X : Type u} [TopologicalSpace X]
    {U V W : Opens X} (f : U ⟶ W) (g : V ⟶ W) :
    pullback f g = U ⊓ V := by
  exact CompleteLattice.pullback_eq_inf f g

/-- The site of open subsets of `X` with the usual topological coverings. -/
def topologicalSpaceSite (X : Type u) [TopologicalSpace X] : Site (Opens X) where
  coverings U := {F | TopologicalCoveringFamily F}
  has_isos := by
    intro U V f _ x hx
    exact ⟨PUnit.unit, (leOfHom (inv f)) hx⟩
  transitive := by
    intro U F G hF hG x hx
    obtain ⟨i, hxi⟩ := hF x hx
    obtain ⟨j, hxj⟩ := hG i x hxi
    exact ⟨⟨i, j⟩, hxj⟩
  base_change := by
    intro U V F hF g
    let P : F.index → Opens X := fun i => F.source i ⊓ V
    let pV : ∀ i, P i ⟶ V := fun _ => homOfLE inf_le_right
    let pU : ∀ i, P i ⟶ F.source i := fun _ => homOfLE inf_le_left
    refine ⟨P, pV, pU, ?_, ?_⟩
    · intro i
      rw [isPullback_iff_isLimit_binaryFan_of_isThin]
      exact ⟨BinaryFan.IsLimit.mk _
        (fun a b => homOfLE (le_inf (leOfHom b) (leOfHom a)))
        (by subsingleton) (by subsingleton) (by subsingleton)⟩
    · intro x hx
      obtain ⟨i, hxi⟩ := hF x ((leOfHom g) hx)
      exact ⟨i, by simpa [P] using And.intro hxi hx⟩

theorem topologicalSpaceSite_isCovering_iff_iUnion_eq
    {X : Type u} [TopologicalSpace X] {U : Opens X}
    (F : FixedTargetFamily (Opens X) U) :
    Site.IsCovering (topologicalSpaceSite X) F ↔
      ⋃ i, (F.source i : Set X) = (U : Set X) := by
  change TopologicalCoveringFamily F ↔ _
  exact topologicalCoveringFamily_iff_iUnion_eq F

end Formalization.Books.EtaleCohomology.Unit10
