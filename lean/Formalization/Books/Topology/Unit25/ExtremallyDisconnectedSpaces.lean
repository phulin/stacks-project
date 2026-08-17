import Formalization.Books.Topology.Unit22.ProfiniteSpaces
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Topology.Category.Stonean.Basic

/-!
# Topology, Chapter 25: Extremally disconnected spaces

The source definition is Mathlib's `ExtremallyDisconnected` class.  The
projectivity and Stonean-cover statements are expressed using Mathlib's
`CompactT2.Projective`, `Stonean`, and `CompHaus.presentation` interfaces.
The source-facing predicates below retain the explicit section and minimal
cover formulations where those formulations are useful to later users.
-/

namespace Formalization.Books.Topology.Unit25

open Function Set
open Formalization.Books.Topology.Unit22

universe u v

noncomputable section

section IntroductoryFacts

variable {X : Type u} [TopologicalSpace X]

/- The source definition is exactly Mathlib's `ExtremallyDisconnected`; no
   parallel predicate is introduced. -/

/- The Hausdorff implication in the source is supplied by Mathlib's stronger
   `TotallySeparatedSpace` instance for extremally disconnected Hausdorff
   spaces, together with its totally disconnected consequence. -/

/-- A Hausdorff extremally disconnected space is totally disconnected. -/
theorem totallyDisconnectedSpace_of_t2Space_of_extremallyDisconnected
    [T2Space X] [ExtremallyDisconnected X] : TotallyDisconnectedSpace X := by
  infer_instance

/-- A compact Hausdorff extremally disconnected space is profinite. -/
theorem isProfiniteSpace_of_compact_t2Space_of_extremallyDisconnected
    [CompactSpace X] [T2Space X] [ExtremallyDisconnected X] :
    IsProfiniteSpace X := by
  exact (isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected (X := X)).2
    ⟨inferInstance, inferInstance, inferInstance⟩

/- The source's non-converse is recorded by the explicit p-adic example below.
   Mathlib's p-adic integers use `ℤ_[p]`; the prime hypothesis is the standard
   typeclass assumption needed by that construction. -/

/-- The p-adic integers are profinite but not extremally disconnected: the
nonzero elements of even valuation form an open set whose closure is not open.
-/
theorem padicIntegers_evenValuation_example (p : ℕ) [Fact p.Prime] :
    IsProfiniteSpace (ℤ_[p]) ∧
      ¬ @ExtremallyDisconnected (ℤ_[p]) inferInstance ∧
        let U : Set (ℤ_[p]) :=
          {x | x ≠ 0 ∧ Even (PadicInt.valuation x)}
        IsOpen U ∧ closure U = U ∪ ({0} : Set (ℤ_[p])) ∧
          ¬ IsOpen (closure U) := by
  sorry

end IntroductoryFacts

section TechnicalLemmas

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous surjection satisfying the source's minimal closed-subset
condition sends every open set into the closure of the complement of the image
of its complement.  This is the source-facing form of Mathlib's
`image_subset_closure_compl_image_compl_of_isOpen`. -/
theorem image_open_subset_closure_compl_image_compl_of_minimal
    (f : X → Y) (hf : Continuous f) (hsurj : Surjective f)
    (hminimal : ∀ E : Set X, E ≠ (univ : Set X) → IsClosed E →
      f '' E ≠ (univ : Set Y))
    {U : Set X} (hU : IsOpen U) :
    f '' U ⊆ closure ((f '' Uᶜ)ᶜ) := by
  exact image_subset_closure_compl_image_compl_of_isOpen hf hsurj hminimal hU

/-- In an extremally disconnected space, disjoint open sets have disjoint
closures. -/
theorem disjoint_closure_of_disjoint_open
    [ExtremallyDisconnected X] {U V : Set X}
    (hUV : Disjoint U V) (hU : IsOpen U) (hV : IsOpen V) :
    Disjoint (closure U) (closure V) :=
  ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen hUV hU hV

/-- A continuous surjection from a compact Hausdorff space to a compact
Hausdorff extremally disconnected space satisfying the source's minimality
condition is a homeomorphism. -/
theorem isHomeomorph_of_continuous_surjective_of_minimal_closed
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [ExtremallyDisconnected Y] (f : X → Y) (hf : Continuous f)
    (hsurj : Surjective f)
    (hminimal : ∀ E : Set X, E ≠ (univ : Set X) → IsClosed E →
      f '' E ≠ (univ : Set Y)) :
    IsHomeomorph f := by
  exact (ExtremallyDisconnected.homeoCompactToT2 hf hsurj hminimal).isHomeomorph

/-- A continuous surjection between compact Hausdorff spaces has a compact
surjective subset minimal under closed-subset inclusion. -/
theorem exists_compact_surjective_minimal_subset
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Surjective f) :
    ∃ E : Set X, CompactSpace E ∧ f '' E = (univ : Set Y) ∧
      ∀ E' : Set E, E' ≠ (univ : Set E) → IsClosed E' →
        E.domRestrict f '' E' ≠ (univ : Set Y) := by
  exact exists_compact_surjective_zorn_subset hf hsurj

end TechnicalLemmas

section Projectivity

variable {X : Type u} [TopologicalSpace X]

/-- Every continuous surjection from a compact Hausdorff space onto `X` has a
continuous section. -/
def HasContinuousSections (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : Prop :=
  ∀ (Y : Type v) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (f : Y → X), Continuous f → Surjective f →
      ∃ s : X → Y, Continuous s ∧ f ∘ s = id

/- `CompactT2.Projective` is Mathlib's canonical formulation of the displayed
   solid lifting diagram. -/

/-- The source's projectivity condition is equivalent to its extremal
disconnectedness condition. -/
theorem compactT2_projective_iff_extremallyDisconnected
    [CompactSpace X] [T2Space X] :
    CompactT2.Projective X ↔ ExtremallyDisconnected X := by
  exact CompactT2.projective_iff_extremallyDisconnected

/-- The three conditions in the source proposition are equivalent: extremal
disconnectedness, sections of compact-Hausdorff surjections, and the solid
lifting property for compact Hausdorff spaces. -/
theorem extremallyDisconnected_projectivity_characterization
    [CompactSpace X] [T2Space X] :
    List.TFAE
      [ExtremallyDisconnected X, HasContinuousSections X,
        CompactT2.Projective X] := by
  sorry

end Projectivity

section Rainwater

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- A nonidentity continuous surjective selfmap of a Hausdorff space has a
proper closed subset whose union with its image is the whole space. -/
theorem exists_proper_closed_union_image_of_continuous_surjective_not_id
    (f : X → X) (hf : Continuous f) (hsurj : Surjective f)
    (hnotid : f ≠ id) :
    ∃ E : Set X, E ≠ (univ : Set X) ∧ IsClosed E ∧
      (univ : Set X) = E ∪ f '' E := by
  sorry

end Rainwater

section StoneCech

variable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]

/-- The Stone--Čech compactification of a discrete space is extremally
disconnected. -/
theorem stoneCech_extremallyDisconnected :
    ExtremallyDisconnected (StoneCech X) := by
  exact CompactT2.Projective.extremallyDisconnected StoneCech.projective

/-- The Stone--Čech compactification of a discrete space has the section
property used in the source example. -/
theorem stoneCech_hasContinuousSections :
    HasContinuousSections (StoneCech X) := by
  sorry

/-- The Stone--Čech compactification of a discrete space is profinite. -/
theorem stoneCech_isProfiniteSpace :
    IsProfiniteSpace (StoneCech X) := by
  have hED : ExtremallyDisconnected (StoneCech X) :=
    stoneCech_extremallyDisconnected
  have hTD : TotallyDisconnectedSpace (StoneCech X) := by
    exact @totallyDisconnectedSpace_of_t2Space_of_extremallyDisconnected
      (StoneCech X) inferInstance inferInstance hED
  exact (isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected
    (X := StoneCech X)).2 ⟨inferInstance, inferInstance, hTD⟩

end StoneCech

section ProjectiveCovers

/-- A minimal Stonean cover packages a compact Hausdorff extremally
disconnected space, a continuous surjection to `X`, and the source's
minimality condition on closed subsets. -/
structure MinimalStoneanCover (X : CompHaus.{u}) where
  space : Stonean.{u}
  projection : space.toTop → X.toTop
  continuous_projection : Continuous projection
  surjective_projection : Surjective projection
  minimal :
    ∀ E : Set space.toTop, E ≠ (univ : Set space.toTop) →
      IsClosed E → projection '' E ≠ (univ : Set X.toTop)

/-- Every compact Hausdorff space has a minimal Stonean cover. -/
theorem exists_minimalStoneanCover (X : CompHaus.{u}) :
    Nonempty (MinimalStoneanCover X) := by
  sorry

/-- Minimal Stonean covers are unique up to a homeomorphism over the base. -/
theorem minimalStoneanCover_unique (X : CompHaus.{u})
    (C₁ C₂ : MinimalStoneanCover X) :
    ∃ e : C₁.space.toTop ≃ₜ C₂.space.toTop,
      C₂.projection ∘ e = C₁.projection := by
  sorry

/-- The source's canonical non-minimal projective cover is Mathlib's
`CompHaus.presentation`; its underlying map is continuous and surjective.
Minimalization and uniqueness are recorded by the cover declarations above.
-/
theorem canonicalStoneanCover_is_continuous_surjective (X : CompHaus.{u}) :
    Continuous (CompHaus.presentation.π X).hom.hom ∧
      Surjective (CompHaus.presentation.π X).hom.hom := by
  refine ⟨(CompHaus.presentation.π X).hom.hom.continuous, ?_⟩
  exact (CompHaus.epi_iff_surjective (CompHaus.presentation.π X)).mp inferInstance

/-- If `κ` is infinite and bounds the cardinality of the base, the cardinality
of a minimal Stonean cover is at most `2 ^ (2 ^ κ)`. -/
theorem minimalStoneanCover_cardinal_bound (X : CompHaus.{u})
    (C : MinimalStoneanCover X) (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ)
    (hX : Cardinal.mk X.toTop ≤ κ) :
    Cardinal.mk C.space.toTop ≤
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ) := by
  sorry

end ProjectiveCovers

end

end Formalization.Books.Topology.Unit25
