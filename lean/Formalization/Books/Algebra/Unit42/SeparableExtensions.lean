import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparablyGenerated
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

private theorem isSeparablyGenerated_of_algEquiv
    {k : Type u} {A : Type v} {B : Type v} [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (hA : IsSeparablyGenerated k A) : IsSeparablyGenerated k B := by
  rcases hA with ⟨ι, x, hx, hsep⟩
  refine ⟨ι, e ∘ x, e.isTranscendenceBasis hx, ?_⟩
  have hmap :
      (IntermediateField.adjoin k (range x)).map e.toAlgHom =
        IntermediateField.adjoin k (range (e ∘ x)) := by
    rw [IntermediateField.adjoin_map]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  rw [← hmap]
  let e₀ := IntermediateField.intermediateFieldMap e
    (IntermediateField.adjoin k (range x))
  have hcompat :
      RingHom.comp
          (algebraMap ((IntermediateField.adjoin k (range x)).map e.toAlgHom) B)
          e₀.toRingEquiv.toRingHom =
        RingHom.comp e.toRingEquiv.toRingHom
          (algebraMap (IntermediateField.adjoin k (range x)) A) := by
    ext z
    rfl
  exact Algebra.IsSeparable.of_equiv_equiv e₀.toRingEquiv e.toRingEquiv hcompat

/-- Every intermediate field of a separable extension is separable. -/
theorem subextension_is_separable
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hK : IsSeparableExtension k K) (L : IntermediateField k K) :
    IsSeparableExtension k L := by
  unfold IsSeparableExtension at hK ⊢
  intro M hM
  letI : Algebra.EssFiniteType k M := hM
  have hM' : Algebra.EssFiniteType k (IntermediateField.lift M) :=
    Algebra.EssFiniteType.of_surjective
      (IntermediateField.liftAlgEquiv M).toAlgHom
      (IntermediateField.liftAlgEquiv M).surjective
  exact isSeparablyGenerated_of_algEquiv
    (IntermediateField.liftAlgEquiv M).symm (hK (IntermediateField.lift M) hM')

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
  rcases hK with ⟨ι, z, hz, hsep⟩
  have hsepClosure :
      separableClosure (IntermediateField.adjoin k (range z)) K = ⊤ :=
    (separableClosure.eq_top_iff (IntermediateField.adjoin k (range z)) K).2 hsep
  obtain ⟨s, hs⟩ :=
    IntermediateField.exists_finset_maximalFor_isTranscendenceBasis_separableClosure k K
  have hz' : IsTranscendenceBasis k ((↑) : range z → K) := hz.to_subtype_range
  have hle :
      (separableClosure (IntermediateField.adjoin k (s : Set K)) K).restrictScalars k ≤
        (separableClosure (IntermediateField.adjoin k (range z)) K).restrictScalars k := by
    rw [hsepClosure]
    exact le_top
  have hmax := hs.2 hz' hle
  have htop :
      (⊤ : IntermediateField k K) ≤
        (separableClosure (IntermediateField.adjoin k (s : Set K)) K).restrictScalars k := by
    simpa [hsepClosure] using hmax
  have hclosureRestrict :
      (separableClosure (IntermediateField.adjoin k (s : Set K)) K).restrictScalars k = ⊤ :=
    top_unique htop
  have hclosure : separableClosure (IntermediateField.adjoin k (s : Set K)) K = ⊤ :=
    (IntermediateField.restrictScalars_eq_top_iff (K := k)).mp hclosureRestrict
  have hsepS : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K :=
    (separableClosure.eq_top_iff (IntermediateField.adjoin k (s : Set K)) K).mp hclosure
  let e := s.equivFin
  let x : Fin s.card → K := fun i => (e.symm i : K)
  have hx : IsTranscendenceBasis k x := by
    simpa [x, e, Function.comp_def] using hs.1.comp_equiv e.symm
  have hxrange : range x = (s : Set K) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro ha
      refine ⟨e ⟨a, ha⟩, ?_⟩
      simp [x]
  have hsepX : Algebra.IsSeparable (IntermediateField.adjoin k (range x)) K := by
    rw [hxrange]
    exact hsepS
  letI : Algebra.IsSeparable (IntermediateField.adjoin k (range x)) K := hsepX
  letI : Algebra.EssFiniteType (IntermediateField.adjoin k (range x)) K :=
    Algebra.EssFiniteType.of_comp k (IntermediateField.adjoin k (range x)) K
  letI : Algebra.IsAlgebraic (IntermediateField.adjoin k (range x)) K := inferInstance
  letI : Module.Finite (IntermediateField.adjoin k (range x)) K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  obtain ⟨y, hy⟩ := Field.exists_primitive_element
    (IntermediateField.adjoin k (range x)) K
  have hgen : IntermediateField.adjoin k (range x ∪ {y}) = ⊤ := by
    calc
      IntermediateField.adjoin k (range x ∪ {y}) =
          IntermediateField.adjoin k (range x) ⊔ IntermediateField.adjoin k {y} := by
            rw [IntermediateField.adjoin_union]
      _ = (IntermediateField.adjoin (IntermediateField.adjoin k (range x)) {y}).restrictScalars k := by
            rw [IntermediateField.restrictScalars_adjoin_eq_sup]
      _ = ⊤ := by rw [hy, IntermediateField.restrictScalars_top]
  have hysep : IsSeparable (IntermediateField.adjoin k (range x)) y :=
    Algebra.IsSeparable.isSeparable _ y
  exact ⟨s.card, x, y, by
    rw [← hs.1.cardinalMk_eq_trdeg]
    simp, hx, hgen, hysep⟩

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
