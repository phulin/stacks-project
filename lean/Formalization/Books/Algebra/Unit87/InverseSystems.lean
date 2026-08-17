import Formalization.Books.Algebra.Unit86.MittagLefflerSystems
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.PNat.Basic

/-!
# Commutative Algebra, Chapter 87: Inverse systems

The source indexes inverse systems by the positive natural numbers.  The
canonical `InverseSystem` functor from the preceding chapters records all
transition maps and their identity and composition laws; the declarations
below expose the successive maps and the compatible-family description used
in this chapter.
-/

namespace Formalization.Books.Algebra.Unit87

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21

universe u w

noncomputable section

/-! ## Inverse systems over the positive integers -/

/- The source's sequence of modules and its converse description by all
transition maps are already exactly `InverseSystem ℕ+ (ModuleCat R)`. -/
abbrev NaturalInverseSystem (R : Type u) [Ring R] :=
  InverseSystem ℕ+ (ModuleCat.{w} R)

/- The map from stage `i` to stage `j` for `j ≤ i` is the image of the unique
morphism `op i ⟶ op j` in the opposite preorder category. -/
def transitionMap {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) {i j : ℕ+} (h : j ≤ i) :
    F.obj (Opposite.op i) ⟶ F.obj (Opposite.op j) :=
  F.map (opHomOfLE h)

@[simp] theorem transitionMap_refl {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) (i : ℕ+) :
    transitionMap F (i := i) (j := i) le_rfl = 𝟙 (F.obj (Opposite.op i)) := by
  simp [transitionMap, opHomOfLE]

/- Functoriality is the source's displayed identity
`φ_{ii''} = φ_{i'i''} ∘ φ_{ii'}`. -/
theorem transitionMap_comp {R : Type u} [Ring R]
    (F : NaturalInverseSystem R)
    {i j k : ℕ+} (hij : j ≤ i) (hjk : k ≤ j) :
    transitionMap F (i := i) (j := j) hij ≫
        transitionMap F (i := j) (j := k) hjk =
      transitionMap F (i := i) (j := k) (hjk.trans hij) := by
  change F.map (homOfLE hij).op ≫ F.map (homOfLE hjk).op =
    F.map (homOfLE (hjk.trans hij)).op
  rw [← F.map_comp, ← op_comp, homOfLE_comp]

/- The displayed arrow `φ_{i+1}` is the following special case of the
canonical transition map. -/
def successiveTransitionMap {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) (i : ℕ+) :
    F.obj (Opposite.op (i + 1)) ⟶ F.obj (Opposite.op i) :=
  transitionMap F (i := i + 1) (j := i) (PNat.lt_add_right i 1).le

/-! ## The inverse limit -/

/- This is the canonical type of compatible families for the underlying
type-valued diagram.  It is Mathlib's `Functor.sections`, not a parallel limit
construction. -/
abbrev inverseLimitFamilies {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) :
    Set (∀ i : ℕ+ᵒᵖ, F.obj i) :=
  (F ⋙ CategoryTheory.forget (ModuleCat.{w} R)).sections

/- The source writes the compatibility condition using only successive maps.
This set is the corresponding source-facing display. -/
def successiveCompatibleFamilies {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) :
    Set (∀ i : ℕ+ᵒᵖ, F.obj i) :=
  {x | ∀ i : ℕ+, successiveTransitionMap F i (x (Opposite.op (i + 1))) =
    x (Opposite.op i)}

theorem inverseLimitFamilies_iff_successiveCompatibleFamilies
    {R : Type u} [Ring R] (F : NaturalInverseSystem R)
    (x : ∀ i : ℕ+ᵒᵖ, F.obj i) :
    x ∈ inverseLimitFamilies F ↔ x ∈ successiveCompatibleFamilies F := by
  constructor
  · intro hx i
    exact hx (opHomOfLE (PNat.lt_add_right i 1).le)
  · intro hx
    change ∀ {i j : ℕ+ᵒᵖ} (f : i ⟶ j),
      (F.map f) (x i) = x j
    have hgeneral : ∀ (i j : ℕ+) (h : j ≤ i),
        (F.map (opHomOfLE h)) (x (Opposite.op i)) = x (Opposite.op j) := by
      intro i
      induction i using PNat.recOn with
      | one =>
          intro j h
          have hj : j = 1 := le_one_iff_eq_one.mp h
          subst j
          have hh : opHomOfLE h = 𝟙 (Opposite.op (1 : ℕ+)) :=
            Subsingleton.elim _ _
          rw [hh, F.map_id]
          rfl
      | succ i ih =>
          intro j h
          rcases eq_or_lt_of_le h with rfl | hj
          · have hh : opHomOfLE h = 𝟙 (Opposite.op (i + 1)) :=
              Subsingleton.elim _ _
            rw [hh, F.map_id]
            rfl
          · have hji : j ≤ i := PNat.lt_add_one_iff.mp hj
            have hnext : i ≤ i + 1 := (PNat.lt_add_right i 1).le
            have hstep := hx i
            change (F.map (opHomOfLE hnext)) (x (Opposite.op (i + 1))) =
              x (Opposite.op i) at hstep
            calc
              (F.map (opHomOfLE h)) (x (Opposite.op (i + 1))) =
                  ((F.map (opHomOfLE hnext)) ≫ F.map (opHomOfLE hji))
                    (x (Opposite.op (i + 1))) := by
                have hcomp : F.map (opHomOfLE h) =
                    F.map (opHomOfLE hnext) ≫ F.map (opHomOfLE hji) := by
                  rw [← F.map_comp]
                  congr 1
                rw [hcomp]
              _ = (F.map (opHomOfLE hji))
                    ((F.map (opHomOfLE hnext)) (x (Opposite.op (i + 1)))) := rfl
              _ = x (Opposite.op j) := by rw [hstep, ih j hji]
    intro i j f
    let h : j.unop ≤ i.unop := le_of_op_hom f
    have hf : f = opHomOfLE h := Subsingleton.elim _ _
    rw [hf]
    exact hgeneral i.unop j.unop h

/- The categorical inverse limit is the preceding chapter's canonical
`InverseSystemLimit`; `limit.isLimit` records its module-level universal
property, while the bridge below identifies its chosen object with the
compatible-family construction. -/
abbrev inverseLimitModule {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) : ModuleCat.{w} R :=
  InverseSystemLimit F

noncomputable def inverseLimitModule_isLimit {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) :
    IsLimit (limit.cone F) :=
  limit.isLimit F

/- The chosen categorical limit is canonically equivalent to the displayed
compatible-family set.  `ModuleCat` limits are preserved by the forgetful
functor, and `Types.limitEquivSections` identifies the resulting type limit
with `Functor.sections`. -/
noncomputable def inverseLimitModule_equiv_families {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) :
    (inverseLimitModule F : Type w) ≃ inverseLimitFamilies F :=
  (preservesLimitIso (CategoryTheory.forget (ModuleCat.{w} R)) F).toEquiv.trans
    (Types.limitEquivSections
      (F ⋙ CategoryTheory.forget (ModuleCat.{w} R)))

/-! ## Exactness of inverse limits -/

/- A short exact sequence of inverse systems is exact at every positive
integer.  A `ShortComplex` of functors also records the maps between the
short exact sequences and their commutativity. -/
def IsPointwiseShortExact {R : Type u} [Ring R]
    (S : ShortComplex (InverseSystem ℕ+ (ModuleCat.{w} R))) : Prop :=
  ∀ i : ℕ+ᵒᵖ,
    (((evaluation (ℕ+ᵒᵖ) (ModuleCat.{w} R)).obj i).mapShortComplex.obj S).ShortExact

/- Applying the inverse-limit functor to the two maps of a short complex. -/
noncomputable def inverseLimitShortComplex {R : Type u} [Ring R]
    (S : ShortComplex (InverseSystem ℕ+ (ModuleCat.{w} R))) :
    ShortComplex (ModuleCat.{w} R) where
  f := limMap S.f
  g := limMap S.g
  zero := by
    apply limit.hom_ext
    intro i
    simp only [Category.assoc, limMap_π, zero_comp]
    rw [← Category.assoc, limMap_π S.f i, Category.assoc,
      ← NatTrans.comp_app, S.zero]
    simp

/- This is the chapter's lemma.  Its hypotheses use Mathlib's canonical
Mittag--Leffler predicate on the underlying inverse system, which is exactly
the stabilization of the images `K_c → K_i` in the source.  The proof is the
specialization of the preceding chapter's general exactness theorem. -/
theorem inverse_limit_shortExact_of_mittagLeffler
    {R : Type u} [Ring R]
    (S : ShortComplex (InverseSystem ℕ+ (ModuleCat.{w} R)))
    (hS : IsPointwiseShortExact S)
    (hML : (S.X₁ ⋙ CategoryTheory.forget (ModuleCat.{w} R)).IsMittagLeffler) :
    (inverseLimitShortComplex S).ShortExact := by
  let hA : IsLimit ((CategoryTheory.forget (ModuleCat.{w} R)).mapCone
      (limit.cone S.X₁)) :=
    isLimitOfPreserves (CategoryTheory.forget (ModuleCat.{w} R)) (limit.isLimit S.X₁)
  let hB : IsLimit ((CategoryTheory.forget (ModuleCat.{w} R)).mapCone
      (limit.cone S.X₂)) :=
    isLimitOfPreserves (CategoryTheory.forget (ModuleCat.{w} R)) (limit.isLimit S.X₂)
  let hC : IsLimit ((CategoryTheory.forget (ModuleCat.{w} R)).mapCone
      (limit.cone S.X₃)) :=
    isLimitOfPreserves (CategoryTheory.forget (ModuleCat.{w} R)) (limit.isLimit S.X₃)
  have hexact : ∀ i : ℕ+ᵒᵖ, ∀ z : S.X₂.obj i, (S.g.app i) z = 0 →
      ∃ y : S.X₁.obj i, (S.f.app i) y = z := by
    intro i z hz
    have hSi := hS i
    dsimp [Functor.mapShortComplex, ShortComplex.map, evaluation] at hSi
    simpa using (ShortComplex.moduleCat_exact_iff _).1 hSi.exact z hz
  have hinj : ∀ i : ℕ+ᵒᵖ, Function.Injective (S.f.app i) := by
    intro i
    have hSi := hS i
    dsimp [Functor.mapShortComplex, ShortComplex.map, evaluation] at hSi
    apply (ModuleCat.mono_iff_injective _).1
    exact hSi.mono_f
  have hsurj : ∀ i : ℕ+ᵒᵖ, Function.Surjective (S.g.app i) := by
    intro i
    have hSi := hS i
    dsimp [Functor.mapShortComplex, ShortComplex.map, evaluation] at hSi
    apply (ModuleCat.epi_iff_surjective _).1
    exact hSi.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    let L₁ : ModuleCat.{w} R := limit S.X₁
    let L₂ : ModuleCat.{w} R := limit S.X₂
    change ∀ (x₂ : L₂), (limMap S.g) x₂ = 0 →
      ∃ x₁ : L₁, (limMap S.f) x₁ = x₂
    intro x₂ hx₂
    have hxi : ∀ i : ℕ+ᵒᵖ, (S.g.app i) (limit.π S.X₂ i x₂) = 0 := by
      intro i
      rw [← ConcreteCategory.comp_apply, ← limMap_π S.g i, ConcreteCategory.comp_apply,
        hx₂]
      simp
    choose a ha using fun i => hexact i (limit.π S.X₂ i x₂) (hxi i)
    let sA : (S.X₁ ⋙ CategoryTheory.forget (ModuleCat.{w} R)).sections :=
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
  · rw [ModuleCat.mono_iff_injective]
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
  · rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (limMap S.g)
    intro x₃
    let eC := Types.isLimitEquivSections hC
    let sC : (S.X₃ ⋙ CategoryTheory.forget (ModuleCat.{w} R)).sections := eC x₃
    let E : ℕ+ᵒᵖ ⥤ Type _ :=
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
    have hEne : ∀ i : ℕ+ᵒᵖ, Nonempty (E.obj i) := by
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
    let hI : IsDirectedSet ℕ+ := ⟨inferInstance, inferInstance⟩
    obtain ⟨sE, hsE⟩ := Formalization.Books.Algebra.Unit86.nonempty_limit_of_countable_mittagLeffler
      hI E hEML hEne
    let sB : (S.X₂ ⋙ CategoryTheory.forget (ModuleCat.{w} R)).sections :=
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
      exact (Types.isLimitEquivSections_apply hC i x₃).symm
    have hfiber : (S.g.app i) (sB.val i) = sC.val i := by
      change (S.g.app i) ((sE i).1) = sC.val i
      exact (sE i).2
    rw [hπB, hfiber, hπC]

end

end Formalization.Books.Algebra.Unit87
