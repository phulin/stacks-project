import Formalization.Books.Topology.Unit09.NoetherianSpaces
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Zorn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Order
import Mathlib.Topology.WithTopology

/-!
# Topology, Chapter 11: Codimension and catenary spaces

The source defines codimension for irreducible closed subsets and then studies
catenary spaces.  Mathlib's `IrreducibleCloseds` is the canonical ordered type
of irreducible closed subsets, and `Order.coheight` is precisely the supremum
of the lengths of strict chains beginning at one of its elements.  Relative
codimension is represented by the same coheight in the order interval below
the ambient irreducible closed subset.
-/

namespace Formalization.Books.Topology.Unit11

open Set Function Order TopologicalSpace
open TopologicalSpace.IrreducibleCloseds

universe u v

section CodimensionAndCatenary

variable {X : Type u} [TopologicalSpace X]

/-! ## Codimension -/

/-
  The source's `codim(Y, X)` is `Order.coheight Y` in the ordered type of
  irreducible closed subsets of `X`.  Its codomain `ℕ∞` is Mathlib's canonical
  notation for the nonnegative naturals with an added infinity.
-/
noncomputable def codimension (Y : IrreducibleCloseds X) : ℕ∞ :=
  Order.coheight Y

theorem codimension_eq_iSup_length (Y : IrreducibleCloseds X) :
    codimension Y =
      ⨆ (p : LTSeries (IrreducibleCloseds X)) (_ : p.head = Y),
        (p.length : ℕ∞) := by
  simpa [codimension] using Order.coheight_eq_iSup_head_eq Y

/-
  This is the source's maximal-chain observation.  `Flag` is Mathlib's
  canonical maximal-chain interface; the source's warning that maximal
  extensions need not have a common length is reflected by the fact that no
  equal-length conclusion is included here.  The finite-codimension
  hypothesis is retained because it is part of the source assertion.
-/
theorem exists_maximal_chain_extension
    (Y : IrreducibleCloseds X) (p : LTSeries (IrreducibleCloseds X))
    (hp : p.head = Y) (_hfinite : codimension Y < ⊤) :
    ∃ F : Flag (IrreducibleCloseds X), Set.range p ⊆ F := by
  sorry

/-! ## Restriction to an open subset -/

/-
  Mathlib's `orderIsoOfIsOpenEmbedding` gives the exact order isomorphism
  between irreducible closed subsets of an open subspace and the irreducible
  closed subsets of the ambient space that meet it.  This is the canonical
  realization of the source's `Y ↦ Y ∩ U` correspondence.
-/
noncomputable def restrictIrreducibleClosedToOpen
    {U : Set X} (hU : IsOpen U) (Y : IrreducibleCloseds X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) : IrreducibleCloseds U := by
  let f : U → X := (↑)
  have hf : _root_.Topology.IsOpenEmbedding f := hU.isOpenEmbedding_subtypeVal
  have hmem : (f ⁻¹' (Y : Set X)).Nonempty := by
    rcases hYU with ⟨x, hxY, hxU⟩
    exact ⟨⟨x, hxU⟩, hxY⟩
  exact (orderIsoOfIsOpenEmbedding f hf).symm ⟨Y, hmem⟩

theorem restrictIrreducibleClosedToOpen_coe
    {U : Set X} (hU : IsOpen U) (Y : IrreducibleCloseds X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    (restrictIrreducibleClosedToOpen hU Y hYU : Set U) =
      (Subtype.val : U → X) ⁻¹' (Y : Set X) := by
  sorry

theorem codimension_at_generic_point
    (Y : IrreducibleCloseds X) {U : Set X} (hU : IsOpen U)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    codimension Y = codimension (restrictIrreducibleClosedToOpen hU Y hYU) := by
  sorry

/-! ## Catenary spaces -/

/-
  The order interval `Set.Iic T'` is the ordered collection of irreducible
  closed subsets contained in `T'`.  Its coheight at `T` is the source's
  `codim(T, T')`, since `T'` is the top irreducible closed subset of its
  subspace.
-/
noncomputable def relativeCodimension
    {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') : ℕ∞ :=
  Order.coheight (⟨T, hTT'⟩ : Set.Iic T')

theorem relativeCodimension_eq_iSup_length
    {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    relativeCodimension hTT' =
      ⨆ (p : LTSeries (Set.Iic T'))
        (_ : p.head = (⟨T, hTT'⟩ : Set.Iic T')),
        (p.length : ℕ∞) := by
  simpa [relativeCodimension] using
    Order.coheight_eq_iSup_head_eq (⟨T, hTT'⟩ : Set.Iic T')

/-
  A source chain between two endpoints is a finite strict series in the
  interval below the upper endpoint.  Maximality is expressed by saying that
  every other such series containing its range has the same range.
-/
def IsMaximalChainBetween {α : Type u} [Preorder α]
    (a b : α) (hab : a ≤ b) (p : LTSeries (Set.Iic b)) : Prop :=
  p.head = (⟨a, hab⟩ : Set.Iic b) ∧
    p.last = (⟨b, le_rfl⟩ : Set.Iic b) ∧
      ∀ q : LTSeries (Set.Iic b),
        q.head = (⟨a, hab⟩ : Set.Iic b) →
        q.last = (⟨b, le_rfl⟩ : Set.Iic b) →
        Set.range p ⊆ Set.range q →
        Set.range q ⊆ Set.range p

/- The source's definition of a catenary space. -/
def IsCatenary (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ ⦃T T' : IrreducibleCloseds X⦄ (hTT' : T < T'),
    relativeCodimension (le_of_lt hTT') < ⊤ ∧
      ∀ p : LTSeries (Set.Iic T'),
        IsMaximalChainBetween T T' (le_of_lt hTT') p →
          p.length = relativeCodimension (le_of_lt hTT')

theorem isCatenary_iff_openCover :
    IsCatenary X ↔
      ∃ (ι : Type v) (U : ι → Opens X),
        TopologicalSpace.IsOpenCover U ∧ ∀ i, IsCatenary (U i) := by
  sorry

theorem isCatenary_subtype_of_isLocallyClosed
    (hX : IsCatenary X) {Y : Set X} (hY : IsLocallyClosed Y) :
    IsCatenary Y := by
  sorry

theorem isCatenary_iff_finite_and_additive_relativeCodimension :
    IsCatenary X ↔
      (∀ ⦃Y Y' : IrreducibleCloseds X⦄ (hYY' : Y < Y'),
        relativeCodimension (le_of_lt hYY') < ⊤) ∧
        (∀ ⦃Y Y' Y'' : IrreducibleCloseds X⦄
          (hYY' : Y < Y') (hY'Y'' : Y' < Y''),
          relativeCodimension (le_of_lt (lt_trans hYY' hY'Y'')) =
            relativeCodimension (le_of_lt hYY') +
              relativeCodimension (le_of_lt hY'Y'')) := by
  sorry

/-! ## Noetherian space of infinite codimension -/

/-
  The example is put on a type synonym so that the generated topology does
  not conflict with the ordinary topology on the real unit interval.
-/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def unitIntervalTail (n : ℕ+) : Set UnitInterval :=
  (fun x : UnitInterval => (x : ℝ)) ⁻¹' Set.Ioi (1 - ((n : ℕ) : ℝ)⁻¹)

def unitIntervalOpenGenerators : Set (Set UnitInterval) :=
  ({∅, Set.univ} : Set (Set UnitInterval)) ∪ Set.range unitIntervalTail

@[instance_reducible]
def unitIntervalTopology : TopologicalSpace UnitInterval :=
  TopologicalSpace.generateFrom unitIntervalOpenGenerators

abbrev NoetherianInfiniteCodimensionSpace :=
  WithTopology UnitInterval unitIntervalTopology

def noetherianExampleTail (n : ℕ+) : Set NoetherianInfiniteCodimensionSpace :=
  (WithTopology.equiv UnitInterval unitIntervalTopology) ⁻¹' unitIntervalTail n

def noetherianExampleInitialSegment (n : ℕ+) :
    Set NoetherianInfiniteCodimensionSpace :=
  (noetherianExampleTail n)ᶜ

def noetherianExampleZero : NoetherianInfiniteCodimensionSpace :=
  (WithTopology.equiv UnitInterval unitIntervalTopology).symm
    ⟨0, ⟨le_rfl, zero_le_one⟩⟩

theorem noetherianExample_isOpen_iff {U : Set NoetherianInfiniteCodimensionSpace} :
    IsOpen U ↔
      U = ∅ ∨ U = Set.univ ∨ ∃ n : ℕ+, U = noetherianExampleTail n := by
  sorry

theorem noetherianExample_isClosed_iff {F : Set NoetherianInfiniteCodimensionSpace} :
    IsClosed F ↔
      F = ∅ ∨ F = {noetherianExampleZero} ∨
        (∃ n : ℕ+, 1 < n ∧ F = noetherianExampleInitialSegment n) ∨
          F = Set.univ := by
  sorry

theorem noetherianExample_isNoetherian :
    NoetherianSpace NoetherianInfiniteCodimensionSpace := by
  sorry

theorem noetherianExample_zero_isClosed :
    IsClosed ({noetherianExampleZero} : Set NoetherianInfiniteCodimensionSpace) := by
  sorry

theorem noetherianExample_initialSegment_isIrreducible
    (n : ℕ+) (hn : 1 < n) :
    IsIrreducible (noetherianExampleInitialSegment n) := by
  sorry

theorem noetherianExample_zero_isIrreducible :
    IsIrreducible ({noetherianExampleZero} : Set NoetherianInfiniteCodimensionSpace) :=
  isIrreducible_singleton

theorem noetherianExample_zero_codimension_eq_top :
    codimension
        (⟨{noetherianExampleZero}, noetherianExample_zero_isIrreducible,
          noetherianExample_zero_isClosed⟩ :
          IrreducibleCloseds NoetherianInfiniteCodimensionSpace) = ⊤ := by
  sorry

end CodimensionAndCatenary

end Formalization.Books.Topology.Unit11
