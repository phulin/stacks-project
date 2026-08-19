import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
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
open scoped BigOperators

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
  let : Algebra.EssFiniteType k M := hM
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
  let : Algebra.IsSeparable (IntermediateField.adjoin k (range x)) K := hsepX
  let : Algebra.EssFiniteType (IntermediateField.adjoin k (range x)) K :=
    Algebra.EssFiniteType.of_comp k (IntermediateField.adjoin k (range x)) K
  let : Algebra.IsAlgebraic (IntermediateField.adjoin k (range x)) K := inferInstance
  let : Module.Finite (IntermediateField.adjoin k (range x)) K :=
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

/-! ### Finite positive-characteristic root extensions -/

/- The construction below deliberately uses finite sets of roots in algebraic
   closures.  The relative perfect closure is usually not finite over its
   base, and its ambient universe is not the one required by the diagram. -/

/-- A chosen `p`-th root of an element in an algebraic closure. -/
noncomputable def pthRootInAlgebraicClosure
    (F : Type u) [Field F] (p : ℕ) (hp : 0 < p) (a : F) : AlgebraicClosure F :=
  Classical.choose <|
    IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) a) hp

@[simp]
theorem pthRootInAlgebraicClosure_pow
    (F : Type u) [Field F] (p : ℕ) (hp : 0 < p) (a : F) :
    pthRootInAlgebraicClosure F p hp a ^ p = algebraMap F (AlgebraicClosure F) a :=
  Classical.choose_spec <|
    IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) a) hp

/- A root step may start with any element already present in the current
   level.  Keeping this operation separate from the original one-step root
   above lets the tower below record successive, rather than merely
   exponentiated, extensions. -/
noncomputable def pthRootInAlgebraicClosureOfElement
    (F : Type u) [Field F] (p : ℕ) (hp : 0 < p)
    (a : AlgebraicClosure F) : AlgebraicClosure F :=
  Classical.choose <| IsAlgClosed.exists_pow_nat_eq a hp

@[simp]
theorem pthRootInAlgebraicClosureOfElement_pow
    (F : Type u) [Field F] (p : ℕ) (hp : 0 < p)
    (a : AlgebraicClosure F) :
    pthRootInAlgebraicClosureOfElement F p hp a ^ p = a :=
  Classical.choose_spec <| IsAlgClosed.exists_pow_nat_eq a hp

/- A `FinitePthRootTower` records every finite root step.  At stage `i`, the
   finite set `generators i` is contained in the preceding field and the next
   field is obtained by adjoining p-th roots of that set.  Thus a tower of
   length two genuinely exposes both successive exponent-one extensions
   needed for a p^2-root. -/
structure FinitePthRootTower
    (F : Type u) [Field F] (p : ℕ) (hp : 0 < p) where
  length : ℕ
  level : ℕ → IntermediateField F (AlgebraicClosure F)
  generators : ℕ → Finset (AlgebraicClosure F)
  base : level 0 = ⊥
  generators_mem : ∀ i, i < length → ∀ a ∈ generators i, a ∈ level i
  step : ∀ i, i < length →
    level (i + 1) =
      level i ⊔ IntermediateField.adjoin F
        (range fun a : generators i =>
          pthRootInAlgebraicClosureOfElement F p hp (a : AlgebraicClosure F))
  finite_dimensional : FiniteDimensional F (level length)
  purely_inseparable : IsPurelyInseparable F (level length)

/- The final level of the tower is the finite purely inseparable base field. -/
noncomputable def finitePthRootFieldAtLevel
    {F : Type u} [Field F] {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootTower F p hp) :
    IntermediateField F (AlgebraicClosure F) :=
  tower.level tower.length

theorem finitePthRootFieldAtLevel_finiteDimensional
    {F : Type u} [Field F] {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootTower F p hp) :
    FiniteDimensional F (finitePthRootFieldAtLevel tower) := by
  exact tower.finite_dimensional

theorem finitePthRootFieldAtLevel_isPurelyInseparable
    {F : Type u} [Field F] {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootTower F p hp) :
    IsPurelyInseparable F (finitePthRootFieldAtLevel tower) := by
  exact tower.purely_inseparable

/-- The finite field obtained by adjoining the selected roots of a finite set. -/
noncomputable def finitePthRootField
    (F : Type u) [Field F] (p : ℕ) (hp : 0 < p) (s : Finset F) :
    IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.adjoin F
    (range fun a : s => pthRootInAlgebraicClosure F p hp (a : F))

theorem finitePthRootField_finiteDimensional
    (F : Type u) [Field F] (p : ℕ) (hp : 0 < p) (s : Finset F) :
    FiniteDimensional F (finitePthRootField F p hp s) := by
  apply IntermediateField.finiteDimensional_adjoin
  rintro _ ⟨a, rfl⟩
  exact Algebra.IsIntegral.isIntegral _

theorem finitePthRootField_isPurelyInseparable
    (F : Type u) [Field F] (p : ℕ) (hp : 0 < p) [Fact p.Prime] [CharP F p]
    (s : Finset F) :
    IsPurelyInseparable F (finitePthRootField F p hp s) := by
  let : ExpChar F p := ExpChar.prime (Fact.out : Nat.Prime p)
  rw [finitePthRootField,
    IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem F (AlgebraicClosure F) p]
  rintro _ ⟨a, rfl⟩
  refine ⟨1, ?_⟩
  simp only [pow_one]
  rw [pthRootInAlgebraicClosure_pow F p hp (a : F)]
  exact ⟨a, rfl⟩

/-- The algebra map from the algebraic closure of the base into that of the top. -/
noncomputable def pthRootClosureMap
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] :
    AlgebraicClosure k →ₐ[k] AlgebraicClosure K :=
  IsAlgClosed.lift

/-- Adjoin the selected base roots and selected top roots to the original top. -/
noncomputable def finitePthRootTop
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) (s : Finset k) (t : Finset K) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K
    ((range fun a : s =>
      pthRootClosureMap k K (pthRootInAlgebraicClosure k p hp (a : k))) ∪
      (range fun b : t => pthRootInAlgebraicClosure K p hp (b : K)))

theorem finitePthRootTop_finiteDimensional
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) (s : Finset k) (t : Finset K) :
    FiniteDimensional K (finitePthRootTop k K p hp s t) := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x hx
  exact Algebra.IsIntegral.isIntegral x

theorem finitePthRootTop_isPurelyInseparable
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) [Fact p.Prime] [CharP k p] [CharP K p]
    (s : Finset k) (t : Finset K) :
    IsPurelyInseparable K (finitePthRootTop k K p hp s t) := by
  let : ExpChar K p := ExpChar.prime (Fact.out : Nat.Prime p)
  rw [finitePthRootTop,
    IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem K (AlgebraicClosure K) p]
  rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
  · refine ⟨1, ?_⟩
    change (pthRootClosureMap k K
      (pthRootInAlgebraicClosure k p hp (a : k))) ^ p ^ 1 ∈
      (algebraMap K (AlgebraicClosure K)).range
    simp only [pow_one]
    rw [← map_pow, pthRootInAlgebraicClosure_pow k p hp (a : k)]
    exact ⟨algebraMap k K a, by
      rw [← IsScalarTower.algebraMap_apply k K (AlgebraicClosure K) (a : k)]
      exact ((pthRootClosureMap k K).commutes a).symm⟩
  · refine ⟨1, ?_⟩
    change (pthRootInAlgebraicClosure K p hp (b : K)) ^ p ^ 1 ∈
      (algebraMap K (AlgebraicClosure K)).range
    simp only [pow_one]
    rw [pthRootInAlgebraicClosure_pow K p hp (b : K)]
    exact ⟨b, rfl⟩

/- The paired towers used by the textbook diagram.  `map_mem` is the
   compatibility condition saying that the chosen base tower maps into the
   chosen top tower; it is the only extra datum needed to package the final
   levels as an algebra. -/
structure FinitePthRootBaseChangeTower
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) where
  base : FinitePthRootTower k p hp
  top : FinitePthRootTower K p hp
  map_mem : ∀ x : finitePthRootFieldAtLevel base,
    pthRootClosureMap k K x ∈ finitePthRootFieldAtLevel top

/- The final level of the top tower. -/
noncomputable def finitePthRootTopAtLevel
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootBaseChangeTower k K p hp) :
    IntermediateField K (AlgebraicClosure K) :=
  finitePthRootFieldAtLevel tower.top

theorem finitePthRootTopAtLevel_finiteDimensional
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootBaseChangeTower k K p hp) :
    FiniteDimensional K (finitePthRootTopAtLevel tower) := by
  exact finitePthRootFieldAtLevel_finiteDimensional tower.top

theorem finitePthRootTopAtLevel_isPurelyInseparable
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootBaseChangeTower k K p hp) :
    IsPurelyInseparable K (finitePthRootTopAtLevel tower) := by
  exact finitePthRootFieldAtLevel_isPurelyInseparable tower.top

/- The image of the finite base root field lies in the finite top root
   field.  This is the map used to install the `base → top` algebra. -/
theorem finitePthRootField_map_mem_top
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) (s : Finset k) (t : Finset K)
    (x : finitePthRootField k p hp s) :
    pthRootClosureMap k K x ∈ finitePthRootTop k K p hp s t := by
  have hle :
      (finitePthRootField k p hp s).map (pthRootClosureMap k K) ≤
        (finitePthRootTop k K p hp s t).restrictScalars k := by
    rw [finitePthRootField, IntermediateField.adjoin_map]
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, ⟨a₀, rfl⟩, rfl⟩
    change _ ∈ finitePthRootTop k K p hp s t
    exact IntermediateField.subset_adjoin K _ (Or.inl ⟨a₀, rfl⟩)
  exact hle ((IntermediateField.map_mem_map
    (S := finitePthRootField k p hp s) (pthRootClosureMap k K)).2 x.property)

/-- Package the finite root construction with all of the tower instances used
    by the textbook diagram. -/
noncomputable def finitePthRootBaseToTop
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) (s : Finset k) (t : Finset K) :
    finitePthRootField k p hp s →+* finitePthRootTop k K p hp s t :=
  RingHom.codRestrict (pthRootClosureMap k K |>.comp
    (finitePthRootField k p hp s).val)
    (finitePthRootTop k K p hp s t)
    (fun x => finitePthRootField_map_mem_top k K p hp s t x)

noncomputable instance finitePthRootBaseAlgebra
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) (s : Finset k) (t : Finset K) :
    Algebra (finitePthRootField k p hp s) (finitePthRootTop k K p hp s t) :=
  RingHom.toAlgebra (finitePthRootBaseToTop k K p hp s t)

noncomputable instance finitePthRootBaseTower
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) (s : Finset k) (t : Finset K) :
    IsScalarTower k (finitePthRootField k p hp s)
      (finitePthRootTop k K p hp s t) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  change algebraMap k (AlgebraicClosure K) a =
    pthRootClosureMap k K (algebraMap k (AlgebraicClosure k) a)
  exact ((pthRootClosureMap k K).commutes a).symm

noncomputable def finitePthRootBaseChange
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) [Fact p.Prime] [CharP k p] [CharP K p]
    (s : Finset k) (t : Finset K)
    (hsep : IsSeparablyGenerated
      (finitePthRootField k p hp s) (finitePthRootTop k K p hp s t)) :
    PurelyInseparableBaseChange k K := by
  let B := finitePthRootField k p hp s
  let T := finitePthRootTop k K p hp s t
  letI : Algebra B T := finitePthRootBaseAlgebra k K p hp s t
  letI : IsScalarTower k B T := finitePthRootBaseTower k K p hp s t
  letI : FiniteDimensional k B := finitePthRootField_finiteDimensional k p hp s
  letI : IsPurelyInseparable k B := finitePthRootField_isPurelyInseparable k p hp s
  letI : FiniteDimensional K T := finitePthRootTop_finiteDimensional k K p hp s t
  letI : IsPurelyInseparable K T := finitePthRootTop_isPurelyInseparable k K p hp s t
  exact { base := B, top := T, topSeparablyGenerated := hsep }

/- The paired tower supplies the base-to-top map used to install the
   `base → top` algebra. -/
theorem finitePthRootFieldAtLevel_map_mem_top
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootBaseChangeTower k K p hp)
    (x : finitePthRootFieldAtLevel tower.base) :
    pthRootClosureMap k K x ∈ finitePthRootTopAtLevel tower :=
  tower.map_mem x

noncomputable def finitePthRootBaseToTopAtLevel
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootBaseChangeTower k K p hp) :
    finitePthRootFieldAtLevel tower.base →+*
      finitePthRootTopAtLevel tower :=
  RingHom.codRestrict (pthRootClosureMap k K |>.comp
    (finitePthRootFieldAtLevel tower.base).val)
    (finitePthRootTopAtLevel tower)
    (fun x => finitePthRootFieldAtLevel_map_mem_top tower x)

noncomputable instance finitePthRootBaseAlgebraAtLevel
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootBaseChangeTower k K p hp) :
    Algebra (finitePthRootFieldAtLevel tower.base)
      (finitePthRootTopAtLevel tower) :=
  RingHom.toAlgebra (finitePthRootBaseToTopAtLevel tower)

noncomputable instance finitePthRootBaseTowerAtLevel
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootBaseChangeTower k K p hp) :
    IsScalarTower k (finitePthRootFieldAtLevel tower.base)
      (finitePthRootTopAtLevel tower) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  change algebraMap k (AlgebraicClosure K) a =
    pthRootClosureMap k K (algebraMap k (AlgebraicClosure k) a)
  exact ((pthRootClosureMap k K).commutes a).symm

noncomputable def finitePthRootBaseChangeAtLevel
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {p : ℕ} {hp : 0 < p}
    (tower : FinitePthRootBaseChangeTower k K p hp)
    (hsep : IsSeparablyGenerated
      (finitePthRootFieldAtLevel tower.base)
      (finitePthRootTopAtLevel tower)) :
    PurelyInseparableBaseChange k K := by
  let B := finitePthRootFieldAtLevel tower.base
  let T := finitePthRootTopAtLevel tower
  letI : Algebra B T := finitePthRootBaseAlgebraAtLevel tower
  letI : IsScalarTower k B T := finitePthRootBaseTowerAtLevel tower
  letI : FiniteDimensional k B :=
    finitePthRootFieldAtLevel_finiteDimensional tower.base
  letI : IsPurelyInseparable k B :=
    finitePthRootFieldAtLevel_isPurelyInseparable tower.base
  letI : FiniteDimensional K T :=
    finitePthRootTopAtLevel_finiteDimensional tower
  letI : IsPurelyInseparable K T :=
    finitePthRootTopAtLevel_isPurelyInseparable tower
  exact { base := B, top := T, topSeparablyGenerated := hsep }

/- A finite collection of elements in a relative perfect closure is already
   contained in a finite succession of p-th-root layers.  The uniform exponent
   in this helper is what lets the paired tower use the corrected level-wise
   interface instead of pretending that one root layer suffices. -/
theorem exists_uniform_pow_mem_of_finset
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    (p : ℕ) [Fact p.Prime] [CharP F p] [IsPurelyInseparable F E]
    (s : Finset E) :
    ∃ n : ℕ, ∀ z ∈ s,
      z ^ (p ^ n) ∈ (algebraMap F E).range := by
  classical
  choose n b hb using fun z : E =>
    IsPurelyInseparable.pow_mem (F := F) (E := E) (q := p) (x := z)
  let N := s.sup n
  refine ⟨N, ?_⟩
  intro z hz
  have hn : n z ≤ N := Finset.le_sup hz
  refine ⟨b z ^ (p ^ (N - n z)), ?_⟩
  rw [map_pow, hb]
  rw [← pow_mul, ← pow_add]
  congr 2
  omega

/-- If the coefficients and variables occurring in a multivariable polynomial
have p-th roots in a field of characteristic `p`, then so does its value. -/
theorem exists_pth_root_eval₂
    {k : Type u} {L : Type v} {ι : Type*}
    [Field k] [Field L] (p : ℕ) [Fact p.Prime]
    [CharP k p] [CharP L p]
    (f : k →+* L) (y z : ι → L) (r : k → L)
    (s : Finset k) (P : MvPolynomial ι k)
    (hcoeff : ∀ m ∈ P.support, MvPolynomial.coeff m P ∈ s)
    (hr : ∀ a ∈ s, r a ^ p = f a)
    (hz : ∀ i, z i ^ p = y i) :
    ∃ q : L, q ^ p = MvPolynomial.eval₂ f y P := by
  classical
  refine ⟨∑ m ∈ P.support,
    r (MvPolynomial.coeff m P) * ∏ i ∈ m.support, z i ^ m i, ?_⟩
  rw [sum_pow_char, MvPolynomial.eval₂_eq]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mul_pow, hr _ (hcoeff m hm)]
  congr 1
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_mul, mul_comm, pow_mul, hz]

/-- The p-th-root construction for polynomial values passes to a rational
function value when the chosen denominator does not vanish. -/
theorem exists_pth_root_eval₂_div
    {k : Type u} {L : Type v} {ι : Type*}
    [Field k] [Field L] (p : ℕ) [Fact p.Prime]
    [CharP k p] [CharP L p]
    (f : k →+* L) (y z : ι → L) (r : k → L)
    (s : Finset k) (P Q : MvPolynomial ι k)
    (hP : ∀ m ∈ P.support, MvPolynomial.coeff m P ∈ s)
    (hQ : ∀ m ∈ Q.support, MvPolynomial.coeff m Q ∈ s)
    (hr : ∀ a ∈ s, r a ^ p = f a)
    (hz : ∀ i, z i ^ p = y i)
    (hQ0 : MvPolynomial.eval₂ f y Q ≠ 0) :
    ∃ q : L, q ^ p = MvPolynomial.eval₂ f y P /
      MvPolynomial.eval₂ f y Q := by
  obtain ⟨a, ha⟩ := exists_pth_root_eval₂ p f y z r s P hP hr hz
  obtain ⟨b, hb⟩ := exists_pth_root_eval₂ p f y z r s Q hQ hr hz
  have hb0 : b ≠ 0 := by
    intro h
    apply hQ0
    rw [← hb, h, zero_pow (Fact.out : Nat.Prime p).pos.ne']
  refine ⟨a / b, ?_⟩
  rw [div_pow, ha, hb]

/-- Finitely many elements of a rational function field can be represented
with numerators and denominators involving only finitely many coefficients of
the ground field. -/
theorem exists_finite_coefficients_reprField
    {k : Type u} {K : Type v} {ι : Type*}
    [Field k] [Field K] [Algebra k K]
    (x : ι → K) (hx : AlgebraicIndependent k x)
    (c : Finset (IntermediateField.adjoin k (Set.range x))) :
    ∃ (num den : IntermediateField.adjoin k (Set.range x) → MvPolynomial ι k)
      (s : Finset k),
      ∀ a ∈ c,
        hx.reprField a * algebraMap (MvPolynomial ι k)
            (FractionRing (MvPolynomial ι k)) (den a) =
          algebraMap (MvPolynomial ι k)
            (FractionRing (MvPolynomial ι k)) (num a) ∧
        den a ≠ 0 ∧
        (∀ m ∈ (num a).support, MvPolynomial.coeff m (num a) ∈ s) ∧
        ∀ m ∈ (den a).support, MvPolynomial.coeff m (den a) ∈ s := by
  classical
  choose q hq using fun a : IntermediateField.adjoin k (Set.range x) =>
    IsLocalization.surj (nonZeroDivisors (MvPolynomial ι k)) (hx.reprField a)
  let num : IntermediateField.adjoin k (Set.range x) → MvPolynomial ι k :=
    fun a => (q a).1
  let den : IntermediateField.adjoin k (Set.range x) → MvPolynomial ι k :=
    fun a => (q a).2.1
  let coeffs : MvPolynomial ι k → Finset k := fun f =>
    f.support.image fun m => MvPolynomial.coeff m f
  let s : Finset k := c.biUnion fun a => coeffs (num a) ∪ coeffs (den a)
  refine ⟨num, den, s, ?_⟩
  intro a ha
  refine ⟨hq a, nonZeroDivisors.ne_zero (q a).2.2, ?_, ?_⟩
  · intro m hm
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, Finset.mem_union_left _ ?_⟩
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
  · intro m hm
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, Finset.mem_union_right _ ?_⟩
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩

private theorem exists_finite_pth_root_tower_of_uniform
    {F : Type u} [Field F] (n : ℕ) (s : Finset (AlgebraicClosure F))
    [Fact p.Prime] [CharP F p]
    (hs : ∀ z ∈ s, z ^ (p ^ n) ∈ (algebraMap F (AlgebraicClosure F)).range) :
    ∃ tower : FinitePthRootTower F p hp,
      (∀ z ∈ s, z ∈ finitePthRootFieldAtLevel tower) ∧
        finitePthRootFieldAtLevel tower =
          IntermediateField.adjoin F (s : Set (AlgebraicClosure F)) := by
  classical
  induction n generalizing s with
  | zero =>
      let tower : FinitePthRootTower F p hp :=
        { length := 0
          level := fun _ => ⊥
          generators := fun _ => ∅
          base := rfl
          generators_mem := by
            intro i hi
            omega
          step := by
            intro i hi
            omega
          finite_dimensional := by infer_instance
          purely_inseparable := by infer_instance }
      refine ⟨tower, ?_, ?_⟩
      intro z hz
      simp only [finitePthRootFieldAtLevel]
      change z ∈ (⊥ : IntermediateField F (AlgebraicClosure F))
      apply IntermediateField.mem_bot.mpr
      simpa using hs z hz
      · apply le_antisymm
        · exact bot_le
        · rw [IntermediateField.adjoin_le_iff]
          intro z hz
          apply IntermediateField.mem_bot.mpr
          simpa using hs z (Finset.mem_coe.mp hz)
  | succ n ih =>
      let s' : Finset (AlgebraicClosure F) := s.image (fun z => z ^ p)
      have hs' : ∀ z ∈ s', z ^ (p ^ n) ∈
          (algebraMap F (AlgebraicClosure F)).range := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
        simpa [pow_succ', ← pow_mul] using hs w hw
      obtain ⟨tower, htower, htower_eq⟩ := ih s' hs'
      let L := finitePthRootFieldAtLevel tower
      let R : IntermediateField F (AlgebraicClosure F) :=
        IntermediateField.adjoin F (Set.range fun a : s' =>
          pthRootInAlgebraicClosureOfElement F p hp (a : AlgebraicClosure F))
      let final : IntermediateField F (AlgebraicClosure F) := L ⊔ R
      have hRfinite : FiniteDimensional F R := by
        apply IntermediateField.finiteDimensional_adjoin
        rintro _ ⟨a, rfl⟩
        exact Algebra.IsIntegral.isIntegral _
      have hfinalfinite : FiniteDimensional F final := by
        let : FiniteDimensional F L := tower.finite_dimensional
        let : FiniteDimensional F R := hRfinite
        exact inferInstance
      let : ExpChar F p := ExpChar.prime (Fact.out : Nat.Prime p)
      have hRpure : IsPurelyInseparable F R := by
        rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem F
          (AlgebraicClosure F) p]
        rintro _ ⟨a, rfl⟩
        let aL : L := ⟨a, htower (a : AlgebraicClosure F) a.property⟩
        let : Field L := inferInstance
        let : Algebra F L := inferInstance
        let : IsPurelyInseparable F L := tower.purely_inseparable
        obtain ⟨m, b, hb⟩ := IsPurelyInseparable.pow_mem (F := F) (E := L)
          (q := p) (x := aL)
        refine ⟨m + 1, b, ?_⟩
        rw [pow_succ', pow_mul,
          pthRootInAlgebraicClosureOfElement_pow F p hp (a : AlgebraicClosure F)]
        simpa [aL] using congrArg Subtype.val hb
      have hfinalpure : IsPurelyInseparable F final := by
        let : IsPurelyInseparable F L := tower.purely_inseparable
        let : IsPurelyInseparable F R := hRpure
        exact inferInstance
      let newLevel : ℕ → IntermediateField F (AlgebraicClosure F) :=
        fun i => if i ≤ tower.length then tower.level i else final
      let newGenerators : ℕ → Finset (AlgebraicClosure F) :=
        fun i => if i < tower.length then tower.generators i else s'
      let newTower : FinitePthRootTower F p hp :=
        { length := tower.length + 1
          level := newLevel
          generators := newGenerators
          base := by
            simp [newLevel, tower.base]
          generators_mem := by
            intro i hi a ha
            by_cases h : i < tower.length
            · have hi_le : i ≤ tower.length := Nat.le_of_lt h
              have ha' : a ∈ tower.generators i := by
                simpa [newGenerators, h] using ha
              dsimp [newLevel]
              rw [if_pos hi_le]
              exact tower.generators_mem i h a ha'
            · have hi' : i = tower.length := by omega
              have hi_le : i ≤ tower.length := Nat.le_of_eq hi'
              have ha'' : a ∈ s' := by simpa [newGenerators, hi'] using ha
              subst i
              dsimp [newLevel]
              rw [if_pos le_rfl]
              have ha' : a ∈ finitePthRootFieldAtLevel tower := htower a ha''
              simpa [finitePthRootFieldAtLevel] using ha'
          step := by
            intro i hi
            by_cases h : i < tower.length
            · have hi_le : i ≤ tower.length := Nat.le_of_lt h
              have hi_succ_le : i + 1 ≤ tower.length := by omega
              dsimp [newLevel, newGenerators]
              rw [if_pos hi_succ_le, if_pos hi_le, if_pos h]
              exact tower.step i h
            · have hi' : i = tower.length := by omega
              have hi_le : i ≤ tower.length := Nat.le_of_eq hi'
              have hi_succ_not_le : ¬ i + 1 ≤ tower.length := by omega
              subst i
              dsimp [newLevel, newGenerators]
              rw [if_neg hi_succ_not_le, if_pos hi_le, if_neg h]
              dsimp [final, L, R, finitePthRootFieldAtLevel]
          finite_dimensional := by
            have hnot : ¬ tower.length + 1 ≤ tower.length := by omega
            have hlevel : newLevel (tower.length + 1) = final := by
              dsimp [newLevel]
              exact if_neg hnot
            exact hlevel ▸ hfinalfinite
          purely_inseparable := by
            have hnot : ¬ tower.length + 1 ≤ tower.length := by omega
            have hlevel : newLevel (tower.length + 1) = final := by
              dsimp [newLevel]
              exact if_neg hnot
            exact hlevel ▸ hfinalpure }
      refine ⟨newTower, ?_, ?_⟩
      intro z hz
      have hz' : z ^ p ∈ s' := Finset.mem_image.mpr ⟨z, hz, rfl⟩
      let a : s' := ⟨z ^ p, hz'⟩
      have hroot : pthRootInAlgebraicClosureOfElement F p hp (a : AlgebraicClosure F) = z := by
        apply sub_eq_zero.mp
        apply eq_zero_of_pow_eq_zero
        rw [sub_pow_char, pthRootInAlgebraicClosureOfElement_pow F p hp,
          show (a : AlgebraicClosure F) = z ^ p by rfl]
        simp
      have hzR : z ∈ R := by
        change z ∈ IntermediateField.adjoin F (Set.range fun a : s' =>
          pthRootInAlgebraicClosureOfElement F p hp (a : AlgebraicClosure F))
        apply IntermediateField.subset_adjoin F _
        exact ⟨a, hroot⟩
      have hzfinal : z ∈ final := (show R ≤ final from le_sup_right) hzR
      change z ∈ newLevel (tower.length + 1)
      dsimp [newLevel]
      rw [if_neg (by omega : ¬tower.length + 1 ≤ tower.length)]
      exact hzfinal
      · have hfinal_eq : final =
            IntermediateField.adjoin F (s : Set (AlgebraicClosure F)) := by
          apply le_antisymm
          · rw [sup_le_iff]
            constructor
            · change finitePthRootFieldAtLevel tower ≤ _
              rw [htower_eq]
              rw [IntermediateField.adjoin_le_iff]
              intro z hz
              rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
              simpa using
                (IntermediateField.adjoin F (s : Set (AlgebraicClosure F))).pow_mem
                  (IntermediateField.subset_adjoin F _ hw) (p : ℤ)
                  
            · rw [IntermediateField.adjoin_le_iff]
              rintro _ ⟨a, rfl⟩
              rcases Finset.mem_image.mp a.property with ⟨w, hw, hwa⟩
              let hroot : pthRootInAlgebraicClosureOfElement F p hp
                  (a : AlgebraicClosure F) = w := by
                apply sub_eq_zero.mp
                apply eq_zero_of_pow_eq_zero
                rw [sub_pow_char,
                  pthRootInAlgebraicClosureOfElement_pow F p hp,
                  show (a : AlgebraicClosure F) = w ^ p by simpa [hwa]]
                simp
              change pthRootInAlgebraicClosureOfElement F p hp
                (a : AlgebraicClosure F) ∈ _
              rw [hroot]
              exact IntermediateField.subset_adjoin F _ hw
          · rw [IntermediateField.adjoin_le_iff]
            intro z hz
            have hz' : z ∈ s := Finset.mem_coe.mp hz
            have hz'' : z ^ p ∈ s' := Finset.mem_image.mpr ⟨z, hz', rfl⟩
            let a : s' := ⟨z ^ p, hz''⟩
            have hroot : pthRootInAlgebraicClosureOfElement F p hp
                (a : AlgebraicClosure F) = z := by
              apply sub_eq_zero.mp
              apply eq_zero_of_pow_eq_zero
              rw [sub_pow_char, pthRootInAlgebraicClosureOfElement_pow F p hp,
                show (a : AlgebraicClosure F) = z ^ p by rfl]
              simp
            exact (show R ≤ final from le_sup_right)
              (IntermediateField.subset_adjoin F _ ⟨a, hroot⟩)
        · change newLevel (tower.length + 1) = _
          dsimp [newLevel]
          rw [if_neg (by omega : ¬tower.length + 1 ≤ tower.length)]
          exact hfinal_eq

/-- A finite set of elements of the relative perfect closure is contained in
one finite p-th-root tower over the base field. -/
theorem exists_finite_pth_root_tower_of_perfectClosure_finset
    {F : Type u} [Field F] (p : ℕ) (hp : 0 < p)
    [Fact p.Prime] [CharP F p]
    (s : Finset (perfectClosure F (AlgebraicClosure F))) :
    ∃ tower : FinitePthRootTower F p hp,
      (∀ z ∈ s, (z : AlgebraicClosure F) ∈
        finitePthRootFieldAtLevel tower) ∧
        finitePthRootFieldAtLevel tower =
          IntermediateField.adjoin F
            (s.image (fun z : perfectClosure F (AlgebraicClosure F) =>
              (z : AlgebraicClosure F)) : Set (AlgebraicClosure F)) := by
  classical
  obtain ⟨n, hn⟩ := exists_uniform_pow_mem_of_finset
    (F := F) (E := perfectClosure F (AlgebraicClosure F)) p s
  let s' : Finset (AlgebraicClosure F) := s.image
    (fun z : perfectClosure F (AlgebraicClosure F) =>
      (z : AlgebraicClosure F))
  have hs' : ∀ z ∈ s', z ^ (p ^ n) ∈
      (algebraMap F (AlgebraicClosure F)).range := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b, hb⟩ := hn a ha
    refine ⟨b, ?_⟩
    exact congrArg Subtype.val hb
  obtain ⟨tower, htower, htower_eq⟩ :=
    exists_finite_pth_root_tower_of_uniform (p := p) (hp := hp) n s' hs'
  refine ⟨tower, ?_, ?_⟩
  · intro z hz
    exact htower (z : AlgebraicClosure F)
      (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  · exact htower_eq

/-- Any finite base root tower can be completed to a compatible paired tower
over a field extension which also contains a prescribed finite subset of the
relative perfect closure of the top field. -/
theorem FinitePthRootTower.exists_baseChangeTower_containing
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) [Fact p.Prime] [CharP k p] [CharP K p]
    (base : FinitePthRootTower k p hp)
    (t : Finset (perfectClosure K (AlgebraicClosure K))) :
    ∃ tower : FinitePthRootBaseChangeTower k K p hp,
      tower.base = base ∧ ∀ z ∈ t, (z : AlgebraicClosure K) ∈
        finitePthRootTopAtLevel tower := by
  classical
  let B := finitePthRootFieldAtLevel base
  let : FiniteDimensional k B := base.finite_dimensional
  let : IsPurelyInseparable k B := base.purely_inseparable
  let : Algebra.EssFiniteType k B := inferInstance
  obtain ⟨s, hs⟩ := IntermediateField.fg_top k B
  let lift (a : B) : perfectClosure K (AlgebraicClosure K) := by
    refine ⟨pthRootClosureMap k K (a : AlgebraicClosure k), ?_⟩
    let : ExpChar k p := ExpChar.prime (Fact.out : Nat.Prime p)
    let : ExpChar K p := ExpChar.prime (Fact.out : Nat.Prime p)
    obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem
      (F := k) (E := B) (q := p) (x := a)
    apply (mem_perfectClosure_iff_pow_mem p).2
    refine ⟨n, algebraMap k K b, ?_⟩
    have hb' : algebraMap k (AlgebraicClosure k) b =
        (a : AlgebraicClosure k) ^ (p ^ n) := congrArg Subtype.val hb
    rw [← map_pow, ← hb']
    rw [← IsScalarTower.algebraMap_apply k K (AlgebraicClosure K) b]
    exact ((pthRootClosureMap k K).commutes b).symm
  let roots : Finset (perfectClosure K (AlgebraicClosure K)) := s.image lift ∪ t
  obtain ⟨top, htop⟩ :=
    exists_finite_pth_root_tower_of_perfectClosure_finset p hp roots
  let tower : FinitePthRootBaseChangeTower k K p hp :=
    { base := base
      top := top
      map_mem := by
        intro x
        have hx : x ∈ IntermediateField.adjoin k (s : Set B) := by
          rw [hs]
          trivial
        apply IntermediateField.adjoin_induction (F := k) (s := (s : Set B))
          (p := fun y _ => pthRootClosureMap k K (y : AlgebraicClosure k) ∈
            finitePthRootFieldAtLevel top)
        · intro y hy
          exact htop (lift y) (Finset.mem_union_left _ <|
            Finset.mem_image.mpr ⟨y, hy, rfl⟩)
        · intro y
          change pthRootClosureMap k K (algebraMap k (AlgebraicClosure k) y) ∈ _
          rw [(pthRootClosureMap k K).commutes]
          exact (finitePthRootFieldAtLevel top).algebraMap_mem (algebraMap k K y)
        · intro x y hx hy hmx hmy
          simpa using (finitePthRootFieldAtLevel top).add_mem hmx hmy
        · intro x hx hmx
          simpa using (finitePthRootFieldAtLevel top).inv_mem hmx
        · intro x y hx hy hmx hmy
          simpa using (finitePthRootFieldAtLevel top).mul_mem hmx hmy
        · exact hx }
  refine ⟨tower, rfl, ?_⟩
  intro z hz
  exact htop z (Finset.mem_union_right _ hz)

/-- Any finite base root tower can be completed to a compatible paired tower
over a field extension. -/
theorem FinitePthRootTower.exists_baseChangeTower
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) [Fact p.Prime] [CharP k p] [CharP K p]
    (base : FinitePthRootTower k p hp) :
    ∃ tower : FinitePthRootBaseChangeTower k K p hp, tower.base = base := by
  obtain ⟨tower, hbase, _⟩ := base.exists_baseChangeTower_containing
    (K := K) p hp ∅
  exact ⟨tower, hbase⟩

/-- A finite family in a rational-function field acquires p-th roots in one
finite paired purely inseparable tower. -/
theorem exists_tower_pth_roots_adjoin_finset
    {k : Type u} {K : Type v} {ι : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype ι]
    (p : ℕ) (hp : 0 < p) [Fact p.Prime] [CharP k p] [CharP K p]
    (x : ι → K) (hx : AlgebraicIndependent k x)
    (c : Finset (IntermediateField.adjoin k (Set.range x))) :
    ∃ tower : FinitePthRootBaseChangeTower k K p hp,
      ∀ a ∈ c, ∃ q : finitePthRootTopAtLevel tower,
        q ^ p = (algebraMap K (finitePthRootTopAtLevel tower)) a := by
  classical
  obtain ⟨num, den, s, hrep⟩ := exists_finite_coefficients_reprField x hx c
  letI : ExpChar k p := ExpChar.prime (Fact.out : Nat.Prime p)
  letI : ExpChar K p := ExpChar.prime (Fact.out : Nat.Prime p)
  let baseRoot (a : k) : perfectClosure k (AlgebraicClosure k) :=
    ⟨pthRootInAlgebraicClosure k p hp a, by
      apply (mem_perfectClosure_iff_pow_mem p).2
      refine ⟨1, a, ?_⟩
      simp⟩
  let baseRoots := s.image baseRoot
  obtain ⟨base, hbase⟩ :=
    exists_finite_pth_root_tower_of_perfectClosure_finset p hp baseRoots
  let topRoot (i : ι) : perfectClosure K (AlgebraicClosure K) :=
    ⟨pthRootInAlgebraicClosure K p hp (x i), by
      apply (mem_perfectClosure_iff_pow_mem p).2
      refine ⟨1, x i, ?_⟩
      simp⟩
  let topRoots := Finset.univ.image topRoot
  obtain ⟨tower, htower, htop⟩ :=
    base.exists_baseChangeTower_containing (K := K) p hp topRoots
  subst base
  let B := finitePthRootFieldAtLevel tower.base
  let T := finitePthRootTopAtLevel tower
  letI : Algebra B T := finitePthRootBaseAlgebraAtLevel tower
  letI : IsScalarTower k B T := finitePthRootBaseTowerAtLevel tower
  let r (a : k) : T := by
    by_cases ha : a ∈ s
    · let ba : B := ⟨baseRoot a, hbase (baseRoot a)
          (Finset.mem_image.mpr ⟨a, ha, rfl⟩)⟩
      exact algebraMap B T ba
    · exact 0
  have hr : ∀ a ∈ s, r a ^ p = algebraMap k T a := by
    intro a ha
    simp only [r, dif_pos ha]
    apply Subtype.ext
    change (pthRootClosureMap k K (pthRootInAlgebraicClosure k p hp a)) ^ p =
      algebraMap k (AlgebraicClosure K) a
    rw [← map_pow, pthRootInAlgebraicClosure_pow]
    exact (pthRootClosureMap k K).commutes a
  let z (i : ι) : T := ⟨topRoot i, htop (topRoot i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  let y (i : ι) : T := algebraMap K T (x i)
  have hz : ∀ i, z i ^ p = y i := by
    intro i
    apply Subtype.ext
    exact pthRootInAlgebraicClosure_pow K p hp (x i)
  refine ⟨tower, ?_⟩
  intro a ha
  obtain ⟨hfrac, hden, hnumcoeff, hdencoeff⟩ := hrep a ha
  obtain ⟨qn, hqn⟩ := exists_pth_root_eval₂ p (algebraMap k T) y z r s
    (num a) hnumcoeff hr hz
  obtain ⟨qd, hqd⟩ := exists_pth_root_eval₂ p (algebraMap k T) y z r s
    (den a) hdencoeff hr hz
  let mapFT : IntermediateField.adjoin k (Set.range x) →+* T :=
    (algebraMap K T).comp (IntermediateField.adjoin k (Set.range x)).val
  let φ : FractionRing (MvPolynomial ι k) →+* T :=
    mapFT.comp hx.aevalEquivField.toRingEquiv.toRingHom
  have hφ (P : MvPolynomial ι k) :
      φ (algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) P) =
        MvPolynomial.eval₂ (algebraMap k T) y P := by
    change algebraMap K T
      (↑(hx.aevalEquivField
        (algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) P)) : K) = _
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    simpa only [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, y,
      IsScalarTower.algebraMap_eq k K T] using
      MvPolynomial.map_eval₂Hom (algebraMap k K) x (algebraMap K T) P
  have hmul := congrArg φ hfrac
  rw [map_mul, hφ, hφ] at hmul
  have hφa : φ (hx.reprField a) = mapFT a := by
    simp [φ, mapFT, AlgebraicIndependent.reprField]
  rw [hφa] at hmul
  have hden0 : MvPolynomial.eval₂ (algebraMap k T) y (den a) ≠ 0 := by
    intro h
    have hy : AlgebraicIndependent k y := by
      change AlgebraicIndependent k ((algebraMap K T) ∘ x)
      exact hx.map' (f := IsScalarTower.toAlgHom k K T) (algebraMap K T).injective
    exact hden ((algebraicIndependent_iff_injective_aeval.mp hy) (by
      simpa [MvPolynomial.aeval_eq_eval₂Hom] using h))
  have hqd0 : qd ≠ 0 := by
    intro h
    apply hden0
    rw [← hqd, h, zero_pow (Fact.out : Nat.Prime p).pos.ne']
  refine ⟨qn / qd, ?_⟩
  rw [div_pow, hqn, hqd]
  symm
  simpa [mapFT] using (eq_div_iff hden0).2 hmul

/-- The coefficients of the minimal polynomial of an element over a finite
rational-function field simultaneously acquire p-th roots in a finite paired
purely inseparable tower. -/
theorem exists_tower_pth_roots_minpoly_coefficients
    {k : Type u} {K : Type v} {ι : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype ι]
    (p : ℕ) (hp : 0 < p) [Fact p.Prime] [CharP k p] [CharP K p]
    (x : ι → K) (hx : AlgebraicIndependent k x) (a : K) :
    ∃ tower : FinitePthRootBaseChangeTower k K p hp,
      ∀ i : ℕ, ∃ q : finitePthRootTopAtLevel tower,
        q ^ p = algebraMap K (finitePthRootTopAtLevel tower)
          ((minpoly (IntermediateField.adjoin k (Set.range x)) a).coeff i : K) := by
  obtain ⟨tower, hcoeff⟩ := exists_tower_pth_roots_adjoin_finset p hp x hx
    (minpoly (IntermediateField.adjoin k (Set.range x)) a).coeffs
  refine ⟨tower, ?_⟩
  intro i
  by_cases hi : (minpoly (IntermediateField.adjoin k (Set.range x)) a).coeff i = 0
  · refine ⟨0, ?_⟩
    simp [hi, hp.ne']
  · exact hcoeff _ (Polynomial.coeff_mem_coeffs hi)

/- The coefficient-selection part is the positive-characteristic argument from
   the source.  Its finite output is exposed here so the construction above is
   reusable by later proof stages without introducing a perfect closure. -/
private theorem exists_finite_adjoin_coefficients
    {F U E : Type*} [Field F] [Field U] [Field E]
    [Algebra F E] [Algebra U E] {ι : Type*} (x : ι → E)
    (c : Finset (IntermediateField.adjoin F (range x))) :
    ∃ s : Finset F, ∀ a ∈ c,
      (a : E) ∈ IntermediateField.adjoin U
        (range x ∪ range fun b : s => algebraMap F E (b : F)) := by
  classical
  let T : Finset F → IntermediateField U E := fun s =>
    IntermediateField.adjoin U
      (range x ∪ range fun b : s => algebraMap F E (b : F))
  have hmono (s t : Finset F) (hst : s ⊆ t) : T s ≤ T t := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with hz | ⟨b, rfl⟩
    · exact IntermediateField.subset_adjoin U _ (Or.inl hz)
    · exact IntermediateField.subset_adjoin U _
        (Or.inr ⟨⟨(b : F), hst b.property⟩, rfl⟩)
  have ha (a : IntermediateField.adjoin F (range x)) :
      ∃ s : Finset F, (a : E) ∈ T s := by
    apply IntermediateField.adjoin_induction (F := F) (s := range x)
      (p := fun z _ => ∃ s : Finset F, (z : E) ∈ T s)
    · intro z hz
      rcases hz with ⟨i, rfl⟩
      refine ⟨∅, ?_⟩
      exact IntermediateField.subset_adjoin U _ (Or.inl ⟨i, rfl⟩)
    · intro z
      refine ⟨{z}, ?_⟩
      exact IntermediateField.subset_adjoin U _
        (Or.inr ⟨⟨z, Finset.mem_singleton_self z⟩, rfl⟩)
    · intro z w hz hw hzs hws
      rcases hzs with ⟨s, hz⟩
      rcases hws with ⟨t, hw⟩
      refine ⟨s ∪ t, ?_⟩
      exact (T (s ∪ t)).add_mem
        (hmono s (s ∪ t) (Finset.subset_union_left) hz)
        (hmono t (s ∪ t) (Finset.subset_union_right) hw)
    · intro z hz hzs
      rcases hzs with ⟨s, hz⟩
      exact ⟨s, (T s).inv_mem hz⟩
    · intro z w hz hw hzs hws
      rcases hzs with ⟨s, hz⟩
      rcases hws with ⟨t, hw⟩
      refine ⟨s ∪ t, ?_⟩
      exact (T (s ∪ t)).mul_mem
        (hmono s (s ∪ t) Finset.subset_union_left hz)
        (hmono t (s ∪ t) Finset.subset_union_right hw)
    · exact a.property
  choose s hs using ha
  let s' : Finset F := c.biUnion s
  refine ⟨s', ?_⟩
  intro a ha'
  have hsub : s a ⊆ s' := by
    intro b hb
    exact Finset.mem_biUnion.mpr ⟨a, ha', hb⟩
  exact hmono (s a) s' hsub (hs a)

private theorem isSeparable_of_finite_coefficients
    {F U E : Type*} [Field F] [Field U] [Field E]
    [Algebra F E] [Algebra U E] (z : E)
    (hz : IsSeparable F z)
    (hcoeff : ∀ n, ∃ b : U,
      algebraMap U E b = algebraMap F E ((minpoly F z).coeff n)) :
    IsSeparable U z := by
  classical
  let b : ℕ → U := fun n => Classical.choose (hcoeff n)
  have hb (n : ℕ) : algebraMap U E (b n) =
      algebraMap F E ((minpoly F z).coeff n) :=
    Classical.choose_spec (hcoeff n)
  let g : Polynomial U := (minpoly F z).support.sum fun n =>
    Polynomial.C (b n) * Polynomial.X ^ n
  have hmap : Polynomial.map (algebraMap U E) g =
      Polynomial.map (algebraMap F E) (minpoly F z) := by
    ext n
    simp only [Polynomial.coeff_map]
    by_cases hn : n ∈ (minpoly F z).support
    · simp [g, Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow,
        Finset.sum_eq_single, hn, hb]
    · have hzero : (minpoly F z).coeff n = 0 := by
        by_contra hzero
        exact hn (Polynomial.mem_support_iff.mpr hzero)
      simp [g, Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow,
        Finset.sum_eq_zero, hn, hzero]
  have hg : g.Separable := by
    apply (Polynomial.separable_map (algebraMap U E)).mp
    rw [hmap]
    exact (Polynomial.separable_map (algebraMap F E)).mpr hz
  have hzero : Polynomial.aeval z g = 0 := by
    change Polynomial.eval₂ (algebraMap U E) z g = 0
    calc
      Polynomial.eval₂ (algebraMap U E) z g =
          Polynomial.eval₂ (RingHom.id E) z
            (Polynomial.map (algebraMap U E) g) := by
          simp [Polynomial.eval₂, Polynomial.aeval_def]
      _ = Polynomial.eval₂ (RingHom.id E) z
            (Polynomial.map (algebraMap F E) (minpoly F z)) := by rw [hmap]
      _ = 0 := by simpa [Polynomial.aeval_def] using (minpoly.aeval F z)
  exact (show (minpoly U z).Separable from
    hg.of_dvd (minpoly.dvd U z hzero))

/- The coefficient-selection part of the positive-characteristic argument is
   finite because every element of the perfect closure and every coefficient
   used by a finite presentation occurs in a finite root tower. -/
theorem exists_finite_pth_root_coefficients_isSeparablyGenerated
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (p : ℕ) (hp : 0 < p) [Fact p.Prime]
    [CharP k p] [CharP K p] :
    ∃ tower : FinitePthRootBaseChangeTower k K p hp,
      IsSeparablyGenerated
        (finitePthRootFieldAtLevel tower.base)
        (finitePthRootTopAtLevel tower) := by
  classical
  let P := perfectClosure k (AlgebraicClosure k)
  let Q := perfectClosure K (AlgebraicClosure K)
  let pToQ : P →+* Q :=
    RingHom.codRestrict
      ((pthRootClosureMap k K).toRingHom.comp P.val) Q
      (fun x => by
        change pthRootClosureMap k K (x : AlgebraicClosure k) ∈ Q
        let : ExpChar k p := ExpChar.prime (Fact.out : Nat.Prime p)
        let : ExpChar K p := ExpChar.prime (Fact.out : Nat.Prime p)
        obtain ⟨n, b, hb⟩ :=
          (mem_perfectClosure_iff_pow_mem p).1 x.property
        apply (mem_perfectClosure_iff_pow_mem p).2
        refine ⟨n, algebraMap k K b, ?_⟩
        have hb' : algebraMap k (AlgebraicClosure k) b =
            (x : AlgebraicClosure k) ^ (p ^ n) := by
          simpa using hb
        rw [← map_pow, ← hb']
        rw [← IsScalarTower.algebraMap_apply k K (AlgebraicClosure K) b]
        exact ((pthRootClosureMap k K).commutes b).symm)
  letI : Algebra P Q := RingHom.toAlgebra pToQ
  let M : IntermediateField P Q :=
    IntermediateField.adjoin P (range fun x : K => algebraMap K Q x)
  letI : PerfectField P := inferInstance
  obtain ⟨sK, hsK⟩ := IntermediateField.fg_top k K
  let liftQ : K → Q := fun x => algebraMap K Q x
  let sQ : Finset Q := sK.image liftQ
  let A : IntermediateField P Q :=
    IntermediateField.adjoin P (sQ : Set Q)
  have hlift : ∀ x : K, liftQ x ∈ A := by
    intro x
    have hx : x ∈ IntermediateField.adjoin k (sK : Set K) := by
      rw [hsK]
      trivial
    apply IntermediateField.adjoin_induction (F := k) (s := (sK : Set K))
      (p := fun y _ => liftQ y ∈ A)
    · intro y hy
      apply IntermediateField.subset_adjoin P _
      exact Finset.mem_image.mpr
        ⟨y, Finset.mem_coe.mp hy, rfl⟩
    · intro y
      have h := A.algebraMap_mem (algebraMap k P y)
      convert h using 1
      change algebraMap K Q (algebraMap k K y) =
        pToQ (algebraMap k P y)
      apply Subtype.ext
      change algebraMap K (AlgebraicClosure K) (algebraMap k K y) =
        pthRootClosureMap k K (algebraMap k (AlgebraicClosure k) y)
      rw [← IsScalarTower.algebraMap_apply k K (AlgebraicClosure K)]
      exact ((pthRootClosureMap k K).commutes y).symm
    · intro y z hy hz hmy hmz
      simpa [liftQ] using A.add_mem hmy hmz
    · intro y hy hmy
      have h := A.inv_mem hmy
      convert h using 1
      simp [liftQ]
    · intro y z hy hz hmy hmz
      simpa [liftQ] using A.mul_mem hmy hmz
    · exact hx
  have hAM : A = M := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hz) with ⟨x, hx, rfl⟩
      exact IntermediateField.subset_adjoin P _ ⟨x, rfl⟩
    · change M ≤ A
      dsimp [M]
      intro z hz
      apply IntermediateField.adjoin_induction (F := P) (x := z)
        (s := range fun x : K => algebraMap K Q x)
        (p := fun y _ => y ∈ A)
      · rintro y ⟨x, rfl⟩
        exact hlift x
      · intro y
        exact A.algebraMap_mem y
      · intro x y hx hy hmx hmy
        exact A.add_mem hmx hmy
      · intro x hx hmx
        exact A.inv_mem hmx
      · intro x y hx hy hmx hmy
        exact A.mul_mem hmx hmy
      · exact hz
  have hMfg : Algebra.EssFiniteType P M := by
    apply (IntermediateField.essFiniteType_iff).2
    refine ⟨sQ, ?_⟩
    change A = M
    exact hAM
  obtain ⟨u, hu, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField P M
  let xM : u → M := fun z => z
  let F₀ : IntermediateField P M :=
    IntermediateField.adjoin P (range xM)
  let kToM : k →+* M :=
    (algebraMap P M).comp (algebraMap k P)
  letI : Algebra k M := RingHom.toAlgebra kToM
  let zM : K → M := fun a =>
    ⟨algebraMap K Q a, IntermediateField.subset_adjoin P _ ⟨a, rfl⟩⟩
  let c : Finset F₀ := sK.biUnion fun a =>
    (minpoly F₀ (zM a)).support.image fun n =>
      (minpoly F₀ (zM a)).coeff n
  obtain ⟨sP, hsP⟩ := exists_finite_adjoin_coefficients
    (F := P) (U := k) (E := M) xM c
  have hc (a : K) (ha : a ∈ sK) (n : ℕ)
      (hn : n ∈ (minpoly F₀ (zM a)).support) :
      (minpoly F₀ (zM a)).coeff n ∈ c := by
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, ?_⟩
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  obtain ⟨base, hbase, hbase_eq⟩ :=
    exists_finite_pth_root_tower_of_perfectClosure_finset
      (F := k) p hp sP
  let B := finitePthRootFieldAtLevel base
  letI : FiniteDimensional k B := base.finite_dimensional
  letI : IsPurelyInseparable k B := base.purely_inseparable
  obtain ⟨sB, hsB⟩ := IntermediateField.fg_top k B
  let liftB : B → Q := by
    intro b
    refine ⟨pthRootClosureMap k K (b : AlgebraicClosure k), ?_⟩
    let : ExpChar k p := ExpChar.prime (Fact.out : Nat.Prime p)
    let : ExpChar K p := ExpChar.prime (Fact.out : Nat.Prime p)
    obtain ⟨n, c₀, hc₀⟩ := IsPurelyInseparable.pow_mem
      (F := k) (E := B) (q := p) (x := b)
    apply (mem_perfectClosure_iff_pow_mem p).2
    refine ⟨n, algebraMap k K c₀, ?_⟩
    have hc₀' : algebraMap k (AlgebraicClosure k) c₀ =
        (b : AlgebraicClosure k) ^ (p ^ n) := congrArg Subtype.val hc₀
    rw [← map_pow, ← hc₀']
    rw [← IsScalarTower.algebraMap_apply k K (AlgebraicClosure K) c₀]
    exact ((pthRootClosureMap k K).commutes c₀).symm
  let uQ : M → Q := fun z => (z : Q)
  let q : Finset Q := sB.image liftB ∪
    u.image uQ
  obtain ⟨top, htop, htop_eq⟩ :=
    exists_finite_pth_root_tower_of_perfectClosure_finset
      (F := K) p hp q
  have hmap : ∀ x : B,
      pthRootClosureMap k K (x : AlgebraicClosure k) ∈
        finitePthRootFieldAtLevel top := by
    intro x
    have hx : x ∈ IntermediateField.adjoin k (sB : Set B) := by
      rw [hsB]
      trivial
    apply IntermediateField.adjoin_induction (F := k) (s := (sB : Set B))
      (p := fun y _ => pthRootClosureMap k K (y : AlgebraicClosure k) ∈
        finitePthRootFieldAtLevel top)
    · intro y hy
      exact htop (liftB y) (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
    · intro y
      change pthRootClosureMap k K (algebraMap k (AlgebraicClosure k) y) ∈ _
      rw [(pthRootClosureMap k K).commutes]
      exact (finitePthRootFieldAtLevel top).algebraMap_mem (algebraMap k K y)
    · intro x y hx hy hmx hmy
      simpa using (finitePthRootFieldAtLevel top).add_mem hmx hmy
    · intro x hx hmx
      simpa using (finitePthRootFieldAtLevel top).inv_mem hmx
    · intro x y hx hy hmx hmy
      simpa using (finitePthRootFieldAtLevel top).mul_mem hmx hmy
    · exact hx
  let T := finitePthRootFieldAtLevel top
  let tower : FinitePthRootBaseChangeTower k K p hp :=
    { base := base
      top := top
      map_mem := hmap }
  let bToAC : B →+* AlgebraicClosure K :=
    (pthRootClosureMap k K).comp B.val
  letI : Algebra B (AlgebraicClosure K) := RingHom.toAlgebra bToAC
  let xT : u → T := fun z =>
    ⟨(z : Q), htop (uQ (z : M)) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨z, z.property, rfl⟩))⟩
  let U : IntermediateField B (AlgebraicClosure K) :=
    IntermediateField.adjoin B (range fun z : u => (xT z : AlgebraicClosure K))
  have hBP : B ≤ P := by
    let : IsPurelyInseparable k B := base.purely_inseparable
    simpa [P] using le_perfectClosure k (AlgebraicClosure k) B
  let bToP : B →+* P := (IntermediateField.inclusion hBP).toRingHom
  letI : Algebra B P := RingHom.toAlgebra bToP
  let D : IntermediateField k M :=
    IntermediateField.adjoin k
      (range xM ∪ range fun b : sP => algebraMap P M (b : P))
  have htransport {a : F₀} (ha : (a : M) ∈ D) :
      (a : AlgebraicClosure K) ∈ U := by
    apply IntermediateField.adjoin_induction (F := k)
      (s := range xM ∪ range fun b : sP => algebraMap P M (b : P))
      (p := fun y _ => (y : AlgebraicClosure K) ∈ U)
    · rintro y (⟨z, rfl⟩ | ⟨b, rfl⟩)
      · change (xT z : AlgebraicClosure K) ∈ U
        exact U.subset_adjoin B _ ⟨z, rfl⟩
      · let bB : B := ⟨(b : P), hbase (b : P) b.property⟩
        have hbU : bToAC bB ∈ U := U.algebraMap_mem bB
        simpa [bB, bToAC, pToQ] using hbU
    · intro y
      have hyU := U.algebraMap_mem (algebraMap k B y)
      simpa [bToAC, pToQ] using hyU
    · intro x y hx hy hmx hmy
      simpa using U.add_mem hmx hmy
    · intro x hx hmx
      simpa using U.inv_mem hmx
    · intro x y hx hy hmx hmy
      simpa using U.mul_mem hmx hmy
    · exact ha

/- The source's construction is the existence statement below; the structure
   above records its diagram rather than introducing unbundled typeclass
   arguments at the theorem boundary. -/
/-- A finitely generated field extension becomes separably generated after a
    finite purely inseparable extension of the base and the top. -/
theorem exists_purely_inseparable_base_change
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    Nonempty (PurelyInseparableBaseChange k K) := by
  by_cases hzero : CharZero k
  · let : CharZero k := hzero
    obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
    let x : s → K := fun z => z
    have hxrange : range x = (s : Set K) := by
      ext z
      simp [x]
    let b : PurelyInseparableBaseChange k K :=
      { base := k, top := K,
        topSeparablyGenerated := ⟨s, x, hs, by rw [hxrange]; exact hsep⟩ }
    exact ⟨b⟩
  · obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
    · exact (hzero ‹CharZero k›).elim
    · let _ : Fact p.Prime := hp
      let _ : CharP k p := hpk
      let _ : CharP K p :=
        CharP.of_ringHom_of_ne_zero (algebraMap k K) p hp.out.ne_zero
      obtain ⟨tower, hsep⟩ :=
        exists_finite_pth_root_coefficients_isSeparablyGenerated
          (k := k) (K := K) p hp.out.pos
      exact ⟨finitePthRootBaseChangeAtLevel tower hsep⟩

end

end Formalization.Books.Algebra.Unit42
