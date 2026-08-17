import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.EssentialFiniteness

/-!
# Commutative Algebra, Chapter 42: Separable extensions

The source extends separability from algebraic extensions to arbitrary field
extensions.  Mathlib's `IsTranscendenceBasis`, `IntermediateField.adjoin`,
`Algebra.IsSeparable`, `Algebra.EssFiniteType`, and
`IsPurelyInseparable` are used for the corresponding canonical notions.
-/

namespace Formalization.Books.Algebra.Unit42

universe u v

noncomputable section

open Set

/-! ## Separably generated and separable extensions -/

/- The source's separably generated extension is not a Mathlib predicate.
   A transcendence basis is represented by a family, and the field generated
   by that family is `IntermediateField.adjoin`. -/
/-- A field extension is separably generated when it has a transcendence basis
    over which the remaining algebraic extension is separable. -/
def IsSeparablyGenerated (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] : Prop :=
  ∃ (ι : Type v) (x : ι → K),
    IsTranscendenceBasis k x ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (range x)) K

/- The source's separable extension notion quantifies over all finitely
   generated intermediate fields.  `Algebra.EssFiniteType` is Mathlib's
   canonical finite-generation interface for field extensions. -/
/-- A field extension is separable when every finitely generated subextension
    is separably generated. -/
def IsSeparableExtension (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ (L : IntermediateField k K),
    Algebra.EssFiniteType k L → IsSeparablyGenerated k L

/-- Every intermediate field of a separable extension is separable. -/
theorem subextension_is_separable
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hK : IsSeparableExtension k K) (L : IntermediateField k K) :
    IsSeparableExtension k L := by
  sorry

/-! ## A finite separably generated extension -/

/-- A finitely generated separably generated field extension has a
    transcendence basis together with one further separable generator.

    The equality `Algebra.trdeg k K = r` uses the canonical cardinal
    coercion from `r : ℕ`; `Set.range x ∪ {y}` represents the field generated
    by the displayed `r + 1` elements. -/
theorem exists_finite_generators_of_separably_generated
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (hK : IsSeparablyGenerated k K) :
    ∃ (r : ℕ) (x : Fin r → K) (y : K),
      Algebra.trdeg k K = r ∧
        IsTranscendenceBasis k x ∧
          IntermediateField.adjoin k (range x ∪ {y}) = ⊤ ∧
            IsSeparable (IntermediateField.adjoin k (range x)) y := by
  sorry

/-! ## Purely inseparable base change -/

/- The displayed textbook diagram is bundled so that its two horizontal
   field-extension maps and its commutativity are explicit in Lean. -/
/-- A commuting base-change diagram in which both vertical field extensions
    are finite purely inseparable and the upper extension is separably
    generated. -/
structure PurelyInseparableBaseChange
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] where
  base : Type u
  top : Type v
  [baseField : Field base]
  [topField : Field top]
  [baseAlgebra : Algebra k base]
  [topAlgebra : Algebra k top]
  [topOverK : Algebra K top]
  [topOverBase : Algebra base top]
  [baseTower : IsScalarTower k base top]
  [topTower : IsScalarTower k K top]
  [baseFinite : FiniteDimensional k base]
  [basePurelyInseparable : IsPurelyInseparable k base]
  [topFinite : FiniteDimensional K top]
  [topPurelyInseparable : IsPurelyInseparable K top]
  topSeparablyGenerated : IsSeparablyGenerated base top

/- The source's construction is the existence statement below; the structure
   above records its diagram rather than introducing unbundled typeclass
   arguments at the theorem boundary. -/
/-- A finitely generated field extension becomes separably generated after a
    finite purely inseparable extension of the base and the top. -/
theorem exists_purely_inseparable_base_change
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    Nonempty (PurelyInseparableBaseChange k K) := by
  sorry

end

end Formalization.Books.Algebra.Unit42
