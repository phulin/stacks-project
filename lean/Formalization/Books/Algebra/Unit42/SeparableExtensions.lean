import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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

/- The coefficient-selection part is the positive-characteristic argument from
   the source.  Its finite output is exposed here so the construction above is
   reusable by later proof stages without introducing a perfect closure. -/
theorem exists_finite_pth_root_coefficients_isSeparablyGenerated
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (p : ℕ) (hp : 0 < p) [Fact p.Prime]
    [CharP k p] [CharP K p] :
    ∃ tower : FinitePthRootBaseChangeTower k K p hp,
      IsSeparablyGenerated
        (finitePthRootFieldAtLevel tower.base)
        (finitePthRootTopAtLevel tower) := by
  sorry

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
