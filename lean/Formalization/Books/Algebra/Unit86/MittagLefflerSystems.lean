import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Commutative Algebra, Chapter 86: Mittag-Leffler systems

The source's inverse systems are represented by functors on the opposite of a
preorder.  Mathlib's `Functor.eventualRange` and `Functor.toEventualRanges`
are the canonical stable-image construction, and
`Functor.IsMittagLeffler` is the source's stabilization condition.
-/

namespace Formalization.Books.Algebra.Unit86

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21

universe u v w

noncomputable section

/-! ## The stable image and the Mittag-Leffler condition -/

/- The source's stable image `A'_i = ⋂_{j ≥ i} φ_{ji}(A_j)` is exactly
`Functor.eventualRange`.  The following is the source-facing form of the
canonical Mathlib characterization. -/
theorem isMittagLeffler_iff_eventualRange
    {I : Type u} [Preorder I] (F : InverseSystem I (Type v)) :
    F.IsMittagLeffler ↔
      ∀ i : Iᵒᵖ, ∃ (j : Iᵒᵖ) (f : j ⟶ i),
        F.eventualRange i = Set.range (F.map f) :=
  F.isMittagLeffler_iff_eventualRange

/- For a system of modules, the same stable image can also be recorded as a
submodule: the intersection of the ranges of all transition maps into the
chosen stage. -/
def moduleEventualRange
    {R : Type u} [Ring R] {I : Type v} [Preorder I]
    (F : InverseSystem I (ModuleCat.{w} R)) (i : Iᵒᵖ) :
    Submodule R (F.obj i) :=
  ⨅ (j : Iᵒᵖ) (f : j ⟶ i), LinearMap.range (F.map f).hom

theorem moduleEventualRange_map
    {R : Type u} [Ring R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I]
    (F : InverseSystem I (ModuleCat.{w} R))
    {i j : Iᵒᵖ} (f : i ⟶ j) :
    (F.map f).hom '' (moduleEventualRange F i : Set (F.obj i)) ⊆
      (moduleEventualRange F j : Set (F.obj j)) := by
  rintro y ⟨x, hx, rfl⟩
  have hx' : ∀ (k : Iᵒᵖ) (g : k ⟶ i),
      x ∈ LinearMap.range (F.map g).hom := by
    change x ∈ ⨅ (k : Iᵒᵖ) (g : k ⟶ i), LinearMap.range (F.map g).hom at hx
    simpa only [Submodule.mem_iInf] using hx
  change (F.map f).hom x ∈
    ⨅ (k : Iᵒᵖ) (g : k ⟶ j), LinearMap.range (F.map g).hom
  rw [Submodule.mem_iInf]
  intro k
  rw [Submodule.mem_iInf]
  intro g
  obtain ⟨l, a, b, hab⟩ := IsCofiltered.cospan f g
  obtain ⟨z, hz⟩ := hx' l a
  refine ⟨(F.map b).hom z, ?_⟩
  rw [← hz]
  change (F.map b ≫ F.map g) z = (F.map a ≫ F.map f) z
  rw [← F.map_comp, ← F.map_comp, hab]

/- The module version in the source is the underlying-set condition. -/
abbrev IsMittagLefflerModuleSystem
    {R : Type u} [Ring R] {I : Type v} [Preorder I]
    (F : InverseSystem I (ModuleCat.{w} R)) : Prop :=
  (F ⋙ CategoryTheory.forget (ModuleCat.{w} R)).IsMittagLeffler

/-! ## Surjective systems and restriction to stable images -/

theorem isMittagLeffler_of_surjective
    {I : Type u} [Preorder I] (F : InverseSystem I (Type v))
    (hF : ∀ ⦃i j : Iᵒᵖ⦄ (f : i ⟶ j),
      Function.Surjective (F.map f)) :
    F.IsMittagLeffler :=
  F.isMittagLeffler_of_surjective hF

theorem eventualRange_map_mapsTo
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : InverseSystem I (Type v)) {i j : Iᵒᵖ} (f : i ⟶ j) :
    (F.eventualRange i).MapsTo (F.map f) (F.eventualRange j) :=
  F.eventualRange_mapsTo f

theorem eventualRange_map_surjective
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : InverseSystem I (Type v)) (hF : F.IsMittagLeffler)
    {i j : Iᵒᵖ} (f : i ⟶ j) :
    Function.Surjective (F.toEventualRanges.map f) := by
  exact F.surjective_toEventualRanges hF f

/- The source's equality of inverse limits is represented by the canonical
equivalence of compatible sections. -/
def eventualRange_sections_equiv
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : InverseSystem I (Type v)) :
    F.toEventualRanges.sections ≃ F.sections :=
  F.toEventualRangesSectionsEquiv

theorem module_isMittagLeffler_of_surjective
    {R : Type u} [Ring R] {I : Type v} [Preorder I]
    (F : InverseSystem I (ModuleCat.{w} R))
    (hF : ∀ ⦃i j : Iᵒᵖ⦄ (f : i ⟶ j),
      Function.Surjective ((F ⋙ CategoryTheory.forget (ModuleCat.{w} R)).map f)) :
    IsMittagLefflerModuleSystem F :=
  Functor.isMittagLeffler_of_surjective
    (F ⋙ CategoryTheory.forget (ModuleCat.{w} R)) hF

/-! ## Countable nonempty limits -/

private theorem nonempty_sections_of_countable_surjective
    {I : Type u} [Preorder I] [Countable I]
    (hI : IsDirectedSet I) (F : InverseSystem I (Type v))
    (hne : ∀ i : Iᵒᵖ, Nonempty (F.obj i))
    (hF : ∀ ⦃i j : Iᵒᵖ⦄ (f : i ⟶ j), Function.Surjective (F.map f)) :
    F.sections.Nonempty := by
  let : Nonempty I := hI.1
  let : IsDirectedOrder I := hI.2
  let : IsFiltered I := isFiltered_of_directed_le_nonempty I
  let Q₀ : ℕ ⥤ I := IsFiltered.sequentialFunctor I
  let Q : ℕᵒᵖ ⥤ Iᵒᵖ := Q₀.op
  let : Q.Initial := by
    dsimp [Q]
    infer_instance
  let H : ℕᵒᵖ ⥤ Type v := Q ⋙ F
  have hH : ∀ n : ℕ, Function.Surjective
      (H.map (homOfLE (Nat.le_succ n)).op) := by
    intro n
    change Function.Surjective (F.map (Q.map (homOfLE (Nat.le_succ n)).op))
    exact hF _
  have hπ : Function.Surjective ((Types.limitCone H).π.app ⟨0⟩) :=
    Types.surjective_π_app_zero_of_surjective_map
      (Types.limitConeIsLimit H) hH
  let x₀ : H.obj ⟨0⟩ := Classical.choice (hne (Q.obj ⟨0⟩))
  obtain ⟨x, _⟩ := hπ x₀
  let eH : (Types.limitCone H).pt ≅ limit H :=
    (Types.limitConeIsLimit H).conePointUniqueUpToIso (limit.isLimit H)
  let eF : limit H ≅ limit F := Functor.Initial.limitIso Q F
  let s : F.sections := Types.limitEquivSections F (eF.hom (eH.hom x))
  exact ⟨s, s.property⟩

theorem nonempty_limit_of_countable_mittagLeffler
    {I : Type u} [Preorder I] [Countable I]
    (hI : IsDirectedSet I) (F : InverseSystem I (Type v))
    (hF : F.IsMittagLeffler)
    (hne : ∀ i : Iᵒᵖ, Nonempty (F.obj i)) :
    F.sections.Nonempty := by
  let : Nonempty I := hI.1
  let : IsDirectedOrder I := hI.2
  let : IsFiltered I := isFiltered_of_directed_le_nonempty I
  let : IsCofiltered Iᵒᵖ := isCofiltered_op_of_isFiltered I
  let : ∀ i : Iᵒᵖ, Nonempty (F.obj i) := hne
  let G := F.toEventualRanges
  have hGne : ∀ i : Iᵒᵖ, Nonempty (G.obj i) := by
    intro i
    exact F.toEventualRanges_nonempty hF i
  have hGsur : ∀ ⦃i j : Iᵒᵖ⦄ (f : i ⟶ j),
      Function.Surjective (G.map f) := by
    intro i j f
    exact F.surjective_toEventualRanges hF f
  obtain ⟨s, hs⟩ := nonempty_sections_of_countable_surjective hI G hGne hGsur
  let t : F.sections := F.toEventualRangesSectionsEquiv ⟨s, hs⟩
  exact ⟨t, t.property⟩

/-! ## Exactness of countable inverse limits -/

/- A short exact sequence of inverse systems is exact objectwise.  This is the
pointwise form of the source's exact sequence
`0 → A_i → B_i → C_i → 0`. -/
def IsPointwiseShortExact
    {I : Type u} [Preorder I]
  (S : ShortComplex (InverseSystem I AddCommGrpCat)) : Prop :=
  ∀ i : Iᵒᵖ,
    (((evaluation (Iᵒᵖ) AddCommGrpCat).obj i).mapShortComplex.obj S).ShortExact

/- The short complex obtained by applying the inverse-limit functor to a
short complex of inverse systems. -/
noncomputable def inverseLimitShortComplex
    {I : Type u} [Preorder I]
    (S : ShortComplex (InverseSystem I AddCommGrpCat))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    ShortComplex AddCommGrpCat where
  f := limMap S.f
  g := limMap S.g
  zero := by
    apply limit.hom_ext
    intro i
    simp only [Category.assoc, limMap_π, zero_comp]
    rw [← Category.assoc, limMap_π S.f i, Category.assoc,
      ← NatTrans.comp_app, S.zero]
    simp

theorem inverse_limit_shortExact_of_countable_mittagLeffler
    {I : Type u} [Preorder I] [Countable I]
    (hI : IsDirectedSet I)
    (S : ShortComplex (InverseSystem I AddCommGrpCat))
    (hS : IsPointwiseShortExact S)
    (hML : (S.X₁ ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler)
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (inverseLimitShortComplex S).ShortExact := by
  let : Nonempty I := hI.1
  let : IsDirectedOrder I := hI.2
  let : IsFiltered I := isFiltered_of_directed_le_nonempty I
  let : IsCofiltered Iᵒᵖ := isCofiltered_op_of_isFiltered I
  let hA : IsLimit ((CategoryTheory.forget AddCommGrpCat).mapCone
      (limit.cone S.X₁)) :=
    isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat) (limit.isLimit S.X₁)
  let hB : IsLimit ((CategoryTheory.forget AddCommGrpCat).mapCone
      (limit.cone S.X₂)) :=
    isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat) (limit.isLimit S.X₂)
  let hC : IsLimit ((CategoryTheory.forget AddCommGrpCat).mapCone
      (limit.cone S.X₃)) :=
    isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat) (limit.isLimit S.X₃)
  have hexact : ∀ i : Iᵒᵖ, ∀ z : S.X₂.obj i, (S.g.app i) z = 0 →
      ∃ y : S.X₁.obj i, (S.f.app i) y = z := by
    intro i z hz
    have hSi := hS i
    dsimp [Functor.mapShortComplex, ShortComplex.map, evaluation] at hSi
    simpa using (ShortComplex.ab_exact_iff _).1 hSi.exact z hz
  have hinj : ∀ i : Iᵒᵖ, Function.Injective (S.f.app i) := by
    intro i
    have hSi := hS i
    dsimp [Functor.mapShortComplex, ShortComplex.map, evaluation] at hSi
    apply (AddCommGrpCat.mono_iff_injective _).1
    exact hSi.mono_f
  have hsurj : ∀ i : Iᵒᵖ, Function.Surjective (S.g.app i) := by
    intro i
    have hSi := hS i
    dsimp [Functor.mapShortComplex, ShortComplex.map, evaluation] at hSi
    apply (AddCommGrpCat.epi_iff_surjective _).1
    exact hSi.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff]
    let L₁ : AddCommGrpCat := limit S.X₁
    let L₂ : AddCommGrpCat := limit S.X₂
    change ∀ (x₂ : L₂), (limMap S.g) x₂ = 0 →
      ∃ x₁ : L₁, (limMap S.f) x₁ = x₂
    intro x₂ hx₂
    have hxi : ∀ i : Iᵒᵖ, (S.g.app i) (limit.π S.X₂ i x₂) = 0 := by
      intro i
      rw [← ConcreteCategory.comp_apply, ← limMap_π S.g i, ConcreteCategory.comp_apply,
        hx₂]
      simp
    choose a ha using fun i => hexact i (limit.π S.X₂ i x₂) (hxi i)
    let sA : (S.X₁ ⋙ CategoryTheory.forget AddCommGrpCat).sections :=
      ⟨a, by
        intro i j f
        change (S.X₁.map f) (a i) = a j
        apply hinj j
        rw [← ConcreteCategory.comp_apply, S.f.naturality f,
          ConcreteCategory.comp_apply, ha i, ha j, ← ConcreteCategory.comp_apply,
          limit.w]
      ⟩
    refine ⟨(Types.isLimitEquivSections hA).symm sA, ?_⟩
    apply Concrete.limit_ext S.X₂
    intro i
    rw [← ConcreteCategory.comp_apply, limMap_π, ConcreteCategory.comp_apply]
    have hπ : (limit.π S.X₁ i) ((Types.isLimitEquivSections hA).symm sA) =
        sA.val i := by
      simpa [Types.isLimitEquivSections, Types.sectionOfCone] using
        (Types.isLimitEquivSections_symm_apply hA sA i)
    rw [hπ, ha i]
  · rw [AddCommGrpCat.mono_iff_injective]
    change Function.Injective (limMap S.f)
    intro x y hxy
    apply Concrete.limit_ext S.X₁
    intro i
    apply hinj i
    have hi := congrArg (fun z => (limit.π S.X₂ i) z) hxy
    have hlimx := congrArg (fun q => q x) (limMap_π S.f i)
    have hlimy := congrArg (fun q => q y) (limMap_π S.f i)
    simp only [ConcreteCategory.comp_apply] at hlimx hlimy
    rw [← hlimx, ← hlimy]
    exact hi
  · rw [AddCommGrpCat.epi_iff_surjective]
    change Function.Surjective (limMap S.g)
    intro x₃
    let eC := Types.isLimitEquivSections hC
    let sC : (S.X₃ ⋙ CategoryTheory.forget AddCommGrpCat).sections := eC x₃
    let E : Iᵒᵖ ⥤ Type _ :=
      { obj := fun i => {x : S.X₂.obj i // (S.g.app i) x = sC.val i}
        map := fun {i j} f => ↾(fun
          (x : {x : S.X₂.obj i // (S.g.app i) x = sC.val i}) =>
          (⟨S.X₂.map f x.1, by
            rw [← ConcreteCategory.comp_apply, S.g.naturality f,
              ConcreteCategory.comp_apply, x.2]
            change (S.X₃.map f) (sC.val i) = sC.val j
            exact sC.property f
          ⟩ : {x : S.X₂.obj j // (S.g.app j) x = sC.val j}))
        map_id := by
          intro i
          ext x
          simp
        map_comp := by
          intro i j k f g
          ext x
          simp }
    have hEne : ∀ i : Iᵒᵖ, Nonempty (E.obj i) := by
      intro i
      obtain ⟨x, hx⟩ := hsurj i (sC.val i)
      change Nonempty {x : S.X₂.obj i // (S.g.app i) x = sC.val i}
      exact ⟨⟨x, hx⟩⟩
    have hEML : E.IsMittagLeffler := by
      intro j
      obtain ⟨i, f, hf⟩ := hML j
      refine ⟨i, f, ?_⟩
      intro k g
      rintro _ ⟨eᵢ, rfl⟩
      obtain ⟨l, a, b, hab⟩ := IsCofiltered.cospan f g
      obtain ⟨eₗ⟩ := hEne l
      have hker : (S.g.app i) (eᵢ - (E.map a eₗ).1) = 0 := by
        rw [map_sub, eᵢ.2, (E.map a eₗ).2]
        simp
      obtain ⟨aᵢ, haᵢ⟩ :=
        hexact i (eᵢ.1 - (E.map a eₗ).1) hker
      obtain ⟨aₖ, haₖ⟩ := hf g ⟨aᵢ, rfl⟩
      let eₖ : E.obj k :=
        ⟨(E.map b eₗ).1 + (S.f.app k) aₖ, by
          rw [map_add, (E.map b eₗ).2]
          have hz := congrArg (fun q => q.app k) S.zero
          simp only [NatTrans.comp_app] at hz
          have hz' := congrArg (fun q => q aₖ) hz
          have hzero : (S.g.app k) ((S.f.app k) aₖ) = 0 := by
            simpa using hz'
          rw [hzero]
          simp
        ⟩
      refine ⟨eₖ, ?_⟩
      apply Subtype.ext
      change (S.X₂.map g) eₖ.1 = (S.X₂.map f) eᵢ
      dsimp [eₖ]
      have hga : (S.X₂.map g) ((E.map b eₗ).1) =
          (S.X₂.map f) ((E.map a eₗ).1) := by
        change (S.X₂.map g) (S.X₂.map b eₗ.1) =
          (S.X₂.map f) (S.X₂.map a eₗ.1)
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← S.X₂.map_comp, ← S.X₂.map_comp, hab]
      have hfa : (S.X₂.map f) ((S.f.app i) aᵢ) =
          (S.f.app j) ((S.X₁.map f) aᵢ) := by
        rw [← ConcreteCategory.comp_apply, ← S.f.naturality f,
          ConcreteCategory.comp_apply]
      have hgf : (S.X₂.map g) ((S.f.app k) aₖ) =
          (S.f.app j) ((S.X₁.map g) aₖ) := by
        rw [← ConcreteCategory.comp_apply, ← S.f.naturality g,
          ConcreteCategory.comp_apply]
      have hdiff : (S.f.app j) ((S.X₁.map f) aᵢ) =
          (S.X₂.map f) (eᵢ - (E.map a eₗ).1) := by
        rw [← hfa, haᵢ]
      have haₖ' : (S.X₁.map g) aₖ = (S.X₁.map f) aᵢ := by
        exact haₖ
      rw [map_add, hga, hgf, haₖ', hdiff, map_sub]
      abel
    obtain ⟨sE, hsE⟩ := nonempty_limit_of_countable_mittagLeffler hI E hEML hEne
    let sB : (S.X₂ ⋙ CategoryTheory.forget AddCommGrpCat).sections :=
      ⟨fun i => (sE i).1, by
        intro i j f
        exact congrArg Subtype.val (hsE f)
      ⟩
    let x₂ := (Types.isLimitEquivSections hB).symm sB
    refine ⟨x₂, ?_⟩
    apply Concrete.limit_ext S.X₃
    intro i
    rw [← ConcreteCategory.comp_apply, limMap_π, ConcreteCategory.comp_apply]
    have hπB : (limit.π S.X₂ i) x₂ = sB.val i := by
      simpa [x₂, Types.isLimitEquivSections, Types.sectionOfCone] using
        (Types.isLimitEquivSections_symm_apply hB sB i)
    have hπC : sC.val i = (limit.π S.X₃ i) x₃ := by
      simp [sC, eC, Types.isLimitEquivSections, Types.sectionOfCone]
    have hfiber : (S.g.app i) (sB.val i) = sC.val i := by
      change (S.g.app i) ((sE i).1) = sC.val i
      exact (sE i).2
    rw [hπB, hfiber, hπC]

end

end Formalization.Books.Algebra.Unit86
