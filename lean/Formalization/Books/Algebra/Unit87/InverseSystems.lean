import Formalization.Books.Algebra.Unit86.MittagLefflerSystems
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.PNat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

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
open scoped TensorProduct

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

/-! ## Tensor products and inverse limits -/

/-- Tensoring a finite-rank free module on the left is canonically a finite
product. -/
noncomputable def finiteFreeTensorEquiv
    {R : Type u} [CommRing R] (n : ℕ) (M : ModuleCat.{u} R) :
    ((MonoidalCategory.tensorLeft (ModuleCat.of R (Fin n → R))).obj M : Type u) ≃ₗ[R]
      (Fin n → M) :=
  (TensorProduct.comm R (Fin n → R) M).trans
    (TensorProduct.piScalarRight R R M (Fin n))

@[simp] theorem finiteFreeTensorEquiv_map
    {R : Type u} [CommRing R] (n : ℕ) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (x : (Fin n → R) ⊗[R] M) :
    finiteFreeTensorEquiv n N (f.hom.lTensor (Fin n → R) x) =
      fun k => f (finiteFreeTensorEquiv n M x k) := by
  induction x with
  | zero =>
      ext k
      simp
  | tmul p m =>
      ext k
      change p k • f m = f (p k • m)
      exact (map_smul f.hom (p k) m).symm
  | add x y hx hy =>
      ext k
      simpa using congrFun (congrArg₂ (· + ·) hx hy) k

@[simp] theorem finiteFreeTensorEquiv_tensorLeft_map
    {R : Type u} [CommRing R] (n : ℕ) {M N : ModuleCat.{u} R}
    (f : M ⟶ N)
    (x : (MonoidalCategory.tensorLeft
      (ModuleCat.of R (Fin n → R))).obj M) :
    finiteFreeTensorEquiv n N
        ((MonoidalCategory.tensorLeft
          (ModuleCat.of R (Fin n → R))).map f x) =
      fun k => f (finiteFreeTensorEquiv n M x k) :=
  finiteFreeTensorEquiv_map n f x

/-- The canonical comparison from a finite free module tensored with a limit
to the limit of the stagewise tensor products is bijective. -/
theorem finiteFreeTensor_limitPost_bijective
    {R : Type u} [CommRing R] {I : Type w} [Preorder I] [UnivLE.{w, u}]
    (F : InverseSystem I (ModuleCat.{u} R)) (n : ℕ) :
    Function.Bijective (limit.post F
      (MonoidalCategory.tensorLeft (ModuleCat.of R (Fin n → R)))) := by
  let P : ModuleCat.{u} R := ModuleCat.of R (Fin n → R)
  let G : InverseSystem I (ModuleCat.{u} R) :=
    F ⋙ MonoidalCategory.tensorLeft P
  let hF : IsLimit ((CategoryTheory.forget (ModuleCat.{u} R)).mapCone
      (limit.cone F)) :=
    isLimitOfPreserves (CategoryTheory.forget (ModuleCat.{u} R)) (limit.isLimit F)
  let hG : IsLimit ((CategoryTheory.forget (ModuleCat.{u} R)).mapCone
      (limit.cone G)) :=
    isLimitOfPreserves (CategoryTheory.forget (ModuleCat.{u} R)) (limit.isLimit G)
  let eF := Types.isLimitEquivSections hF
  let eG := Types.isLimitEquivSections hG
  constructor
  · intro x y hxy
    apply (finiteFreeTensorEquiv n (limit F)).injective
    funext k
    apply Concrete.limit_ext F
    intro i
    have hi := congrArg (fun z => (limit.π G i) z) hxy
    have hpostx :
        (limit.π G i) ((limit.post F (MonoidalCategory.tensorLeft P)) x) =
          ((MonoidalCategory.tensorLeft P).map (limit.π F i)) x := by
      exact congrArg (fun q => q x)
        (limit.post_π F (MonoidalCategory.tensorLeft P) i)
    have hposty :
        (limit.π G i) ((limit.post F (MonoidalCategory.tensorLeft P)) y) =
          ((MonoidalCategory.tensorLeft P).map (limit.π F i)) y := by
      exact congrArg (fun q => q y)
        (limit.post_π F (MonoidalCategory.tensorLeft P) i)
    change (limit.π G i)
        ((limit.post F (MonoidalCategory.tensorLeft P)) x) =
      (limit.π G i)
        ((limit.post F (MonoidalCategory.tensorLeft P)) y) at hi
    rw [hpostx, hposty] at hi
    change (limit.π F i).hom.lTensor (Fin n → R) x =
      (limit.π F i).hom.lTensor (Fin n → R) y at hi
    have hi' := congrArg (fun z => finiteFreeTensorEquiv n (F.obj i) z k) hi
    simpa only [finiteFreeTensorEquiv_map] using hi'
  · intro z
    let sG : (G ⋙ CategoryTheory.forget (ModuleCat.{u} R)).sections := eG z
    let s : Fin n → (F ⋙ CategoryTheory.forget (ModuleCat.{u} R)).sections :=
      fun k => ⟨fun i => finiteFreeTensorEquiv n (F.obj i) (sG.val i) k, by
        intro i j f
        have hf := congrArg
          (fun t => finiteFreeTensorEquiv n (F.obj j) t k) (sG.property f)
        change finiteFreeTensorEquiv n (F.obj j)
            ((F.map f).hom.lTensor (Fin n → R) (sG.val i)) k =
          finiteFreeTensorEquiv n (F.obj j) (sG.val j) k at hf
        change (F.map f)
            (finiteFreeTensorEquiv n (F.obj i) (sG.val i) k) =
          finiteFreeTensorEquiv n (F.obj j) (sG.val j) k
        simpa only [finiteFreeTensorEquiv_map] using hf⟩
    let x : (MonoidalCategory.tensorLeft P).obj (limit F) :=
      (finiteFreeTensorEquiv n (limit F)).symm (fun k => eF.symm (s k))
    refine ⟨x, ?_⟩
    apply Concrete.limit_ext G
    intro i
    apply (finiteFreeTensorEquiv n (F.obj i)).injective
    funext k
    have hpost :
        (limit.π G i) ((limit.post F (MonoidalCategory.tensorLeft P)) x) =
          ((MonoidalCategory.tensorLeft P).map (limit.π F i)) x := by
      exact congrArg (fun q => q x)
        (limit.post_π F (MonoidalCategory.tensorLeft P) i)
    have hπF : (limit.π F i) (eF.symm (s k)) = (s k).val i := by
      simpa [eF] using Types.isLimitEquivSections_symm_apply hF (s k) i
    have hπG : sG.val i = (limit.π G i) z := by
      exact Types.isLimitEquivSections_apply hG i z
    rw [hpost]
    change finiteFreeTensorEquiv n (F.obj i)
        ((limit.π F i).hom.lTensor (Fin n → R) x) k =
      finiteFreeTensorEquiv n (F.obj i) ((limit.π G i) z) k
    rw [show finiteFreeTensorEquiv n (F.obj i)
        ((limit.π F i).hom.lTensor (Fin n → R) x) k =
          (limit.π F i) (finiteFreeTensorEquiv n (limit F) x k) by
      exact congrFun (finiteFreeTensorEquiv_map n (limit.π F i) x) k]
    rw [show finiteFreeTensorEquiv n (limit F) x = fun k => eF.symm (s k) by
      simp [x], hπF]
    change finiteFreeTensorEquiv n (F.obj i) (sG.val i) k =
      finiteFreeTensorEquiv n (F.obj i) ((limit.π G i) z) k
    rw [hπG]

/-- For a finite presentation matrix `d`, this is the inverse system of
kernels of `d ⊗ 1` at the stages of `F`. -/
def tensorPresentationKernelSystem
    {R : Type u} [CommRing R] {I : Type w} [Preorder I]
    {m n : ℕ} (d : (Fin m → R) →ₗ[R] (Fin n → R))
    (F : InverseSystem I (ModuleCat.{u} R)) : InverseSystem I (Type u) where
  obj i := LinearMap.ker (d.rTensor (F.obj i))
  map {i j} f := ↾(fun x =>
    (⟨(F.map f).hom.lTensor (Fin m → R) x.1, by
      change d.rTensor (F.obj j)
        ((F.map f).hom.lTensor (Fin m → R) x.1) = 0
      rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, x.2, map_zero]
    ⟩ : LinearMap.ker (d.rTensor (F.obj j))))
  map_id := by
    intro i
    ext x
    change (F.map (𝟙 i)).hom.lTensor (Fin m → R) x = x
    simp
  map_comp := by
    intro i j k f g
    ext x
    change (F.map (f ≫ g)).hom.lTensor (Fin m → R) x =
      (F.map g).hom.lTensor (Fin m → R)
        ((F.map f).hom.lTensor (Fin m → R) x)
    rw [F.map_comp]
    exact LinearMap.lTensor_comp_apply (Fin m → R) _ _ x.1

/-- For an inverse sequence, surjectivity of the successive transition maps
implies surjectivity of every transition map. -/
theorem inverseSystem_map_surjective_of_successive
    {R : Type u} [Ring R] (F : InverseSystem ℕ (ModuleCat.{u} R))
    (hsurj : ∀ n : ℕ,
      Function.Surjective (F.map (opHomOfLE (Nat.le_succ n)))) :
    ∀ ⦃i j : ℕᵒᵖ⦄ (f : i ⟶ j), Function.Surjective (F.map f) := by
  have hgeneral : ∀ (i j : ℕ) (h : j ≤ i),
      Function.Surjective (F.map (opHomOfLE h)) := by
    intro i
    induction i with
    | zero =>
        intro j h
        have hj : j = 0 := Nat.eq_zero_of_le_zero h
        subst j
        have hf : opHomOfLE h = 𝟙 (Opposite.op 0) := Subsingleton.elim _ _
        rw [hf, F.map_id]
        exact Function.surjective_id
    | succ i ih =>
        intro j h
        rcases eq_or_lt_of_le h with rfl | hj
        · have hf : opHomOfLE h = 𝟙 (Opposite.op (i + 1)) :=
            Subsingleton.elim _ _
          rw [hf, F.map_id]
          exact Function.surjective_id
        · have hji : j ≤ i := Nat.le_of_lt_succ hj
          have hcomp : F.map (opHomOfLE h) =
              F.map (opHomOfLE (Nat.le_succ i)) ≫ F.map (opHomOfLE hji) := by
            rw [← F.map_comp]
            congr 1
          rw [hcomp]
          exact (ih j hji).comp (hsurj i)
  intro i j f
  let h : j.unop ≤ i.unop := le_of_op_hom f
  have hf : f = opHomOfLE h := Subsingleton.elim _ _
  rw [hf]
  exact hgeneral i.unop j.unop h

/-- Tensoring a countable inverse limit by a module with a chosen finite
presentation commutes with the limit when the transition maps are surjective
and the inverse system of relation kernels is Mittag--Leffler.  The latter is
the `Tor₁` obstruction in applications. -/
theorem tensor_inverseSystemLimit_iso_of_finitePresentation
    {R : Type u} [CommRing R] {I : Type w} [Preorder I] [Countable I]
    [UnivLE.{w, u}]
    (hI : IsDirectedSet I) (F : InverseSystem I (ModuleCat.{u} R))
    (Q : ModuleCat.{u} R) {m n : ℕ}
    (d : (Fin m → R) →ₗ[R] (Fin n → R))
    (q : (Fin n → R) →ₗ[R] Q)
    (hexact : Function.Exact d q) (hq : Function.Surjective q)
    (hsurj : ∀ ⦃i j : Iᵒᵖ⦄ (f : i ⟶ j),
      Function.Surjective (F.map f))
    (hML : (tensorPresentationKernelSystem d F).IsMittagLeffler) :
    Nonempty ((MonoidalCategory.tensorLeft Q).obj (InverseSystemLimit F) ≅
      (InverseSystemLimit
        (F ⋙ MonoidalCategory.tensorLeft Q) : ModuleCat.{u} R)) := by
  let : Nonempty I := hI.1
  let : IsDirectedOrder I := hI.2
  let : IsFiltered I := isFiltered_of_directed_le_nonempty I
  let : IsCofiltered Iᵒᵖ := isCofiltered_op_of_isFiltered I
  let Pm : ModuleCat.{u} R := ModuleCat.of R (Fin m → R)
  let Pn : ModuleCat.{u} R := ModuleCat.of R (Fin n → R)
  let Gm : InverseSystem I (ModuleCat.{u} R) :=
    F ⋙ MonoidalCategory.tensorLeft Pm
  let Gn : InverseSystem I (ModuleCat.{u} R) :=
    F ⋙ MonoidalCategory.tensorLeft Pn
  let GQ : InverseSystem I (ModuleCat.{u} R) :=
    F ⋙ MonoidalCategory.tensorLeft Q
  let cQ := limit.post F (MonoidalCategory.tensorLeft Q)
  have hfree_m := finiteFreeTensor_limitPost_bijective F m
  have hfree_n := finiteFreeTensor_limitPost_bijective F n
  have hcQ_surjective : Function.Surjective cQ := by
    intro x
    let E : Iᵒᵖ ⥤ Type u :=
      { obj := fun i => {y : (Fin n → R) ⊗[R] F.obj i //
            q.rTensor (F.obj i) y = (limit.π GQ i) x}
        map := fun {i j} f => ↾(fun y =>
          (⟨(F.map f).hom.lTensor (Fin n → R) y.1, by
            rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
              ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, y.2]
            have hx := congrArg (fun a => a x) (limit.w GQ f)
            change (F.map f).hom.lTensor Q ((limit.π GQ i) x) =
              (limit.π GQ j) x at hx
            exact hx
          ⟩ : {y : (Fin n → R) ⊗[R] F.obj j //
            q.rTensor (F.obj j) y = (limit.π GQ j) x}))
        map_id := by
          intro i
          ext y
          change (F.map (𝟙 i)).hom.lTensor (Fin n → R) y = y
          simp
        map_comp := by
          intro i j k f g
          ext y
          change (F.map (f ≫ g)).hom.lTensor (Fin n → R) y =
            (F.map g).hom.lTensor (Fin n → R)
              ((F.map f).hom.lTensor (Fin n → R) y)
          rw [F.map_comp]
          exact LinearMap.lTensor_comp_apply (Fin n → R) _ _ y.1 }
    have hEne : ∀ i : Iᵒᵖ, Nonempty (E.obj i) := by
      intro i
      obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective (F.obj i) hq
        ((limit.π GQ i) x)
      exact ⟨⟨y, hy⟩⟩
    have hEsur : ∀ ⦃i j : Iᵒᵖ⦄ (f : i ⟶ j),
        Function.Surjective (E.map f) := by
      intro i j f yj
      obtain ⟨yi, hyi⟩ := LinearMap.rTensor_surjective (F.obj i) hq
        ((limit.π GQ i) x)
      have hdiff : q.rTensor (F.obj j)
          (yj.1 - (F.map f).hom.lTensor (Fin n → R) yi) = 0 := by
        rw [map_sub, yj.2]
        rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
          ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hyi]
        have hx := congrArg (fun a => a x) (limit.w GQ f)
        change (F.map f).hom.lTensor Q ((limit.π GQ i) x) =
          (limit.π GQ j) x at hx
        exact sub_eq_zero.mpr hx.symm
      have hexj := rTensor_exact (F.obj j) hexact hq
      obtain ⟨zj, hzj⟩ := (hexj _).mp hdiff
      obtain ⟨zi, hzi⟩ := LinearMap.lTensor_surjective (Fin m → R)
        (hsurj f) zj
      let yi' : E.obj i :=
        ⟨yi + d.rTensor (F.obj i) zi, by
          rw [map_add, hyi]
          have hz : q.rTensor (F.obj i) (d.rTensor (F.obj i) zi) = 0 :=
            (rTensor_exact (F.obj i) hexact hq _).mpr ⟨zi, rfl⟩
          rw [hz, add_zero]
        ⟩
      refine ⟨yi', ?_⟩
      apply Subtype.ext
      change (F.map f).hom.lTensor (Fin n → R) yi'.1 = yj.1
      dsimp [yi']
      rw [map_add]
      have hcomm : (F.map f).hom.lTensor (Fin n → R)
          (d.rTensor (F.obj i) zi) =
          d.rTensor (F.obj j)
            ((F.map f).hom.lTensor (Fin m → R) zi) := by
        rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
          ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply]
      rw [hcomm, hzi, hzj]
      abel
    have hEML : E.IsMittagLeffler :=
      Functor.isMittagLeffler_of_surjective E hEsur
    obtain ⟨sE, hsE⟩ :=
      Formalization.Books.Algebra.Unit86.nonempty_limit_of_countable_mittagLeffler
        hI E hEML hEne
    let hGn : IsLimit ((CategoryTheory.forget (ModuleCat.{u} R)).mapCone
        (limit.cone Gn)) :=
      isLimitOfPreserves (CategoryTheory.forget (ModuleCat.{u} R)) (limit.isLimit Gn)
    let sGn : (Gn ⋙ CategoryTheory.forget (ModuleCat.{u} R)).sections :=
      ⟨fun i => (sE i).1, by
        intro i j f
        exact congrArg Subtype.val (hsE f)⟩
    let yn : (limit Gn : ModuleCat.{u} R) :=
      (Types.isLimitEquivSections hGn).symm sGn
    obtain ⟨y, hy⟩ := hfree_n.2 yn
    refine ⟨q.rTensor (limit F : ModuleCat.{u} R) y, ?_⟩
    apply Concrete.limit_ext GQ
    intro i
    have hyn : (limit.π Gn i) yn = (sE i).1 := by
      simpa [yn, sGn] using
        Types.isLimitEquivSections_symm_apply hGn sGn i
    have hyi := congrArg (fun a => (limit.π Gn i) a) hy
    change (limit.π Gn i)
        ((limit.post F (MonoidalCategory.tensorLeft Pn)) y) =
      (limit.π Gn i) yn at hyi
    have hpostn : (limit.π Gn i)
        ((limit.post F (MonoidalCategory.tensorLeft Pn)) y) =
          ((MonoidalCategory.tensorLeft Pn).map (limit.π F i)) y := by
      exact congrArg (fun a => a y)
        (limit.post_π F (MonoidalCategory.tensorLeft Pn) i)
    rw [hpostn] at hyi
    change (limit.π GQ i)
        (cQ (q.rTensor (limit F : ModuleCat.{u} R) y)) =
      (limit.π GQ i) x
    have hcpost : (limit.π GQ i)
        (cQ (q.rTensor (limit F : ModuleCat.{u} R) y)) =
        ((MonoidalCategory.tensorLeft Q).map (limit.π F i))
          (q.rTensor (limit F : ModuleCat.{u} R) y) := by
      exact congrArg
        (fun a => a (q.rTensor (limit F : ModuleCat.{u} R) y))
        (limit.post_π F (MonoidalCategory.tensorLeft Q) i)
    rw [hcpost]
    change (limit.π F i).hom.lTensor Q
        (q.rTensor (limit F : ModuleCat.{u} R) y) =
      (limit.π GQ i) x
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply]
    change q.rTensor (F.obj i)
        ((MonoidalCategory.tensorLeft Pn).map (limit.π F i) y) =
      (limit.π GQ i) x
    rw [hyi, hyn]
    exact (sE i).2
  have hcQ_injective : Function.Injective cQ := by
    suffices hzero : ∀ z, cQ z = 0 → z = 0 by
      intro z z' hzz'
      apply sub_eq_zero.mp
      apply hzero (z - z')
      rw [map_sub, hzz', sub_self]
    intro z hz
    obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective
      (limit F : ModuleCat.{u} R) hq z
    have hrel : ∀ i : Iᵒᵖ, q.rTensor (F.obj i)
        ((limit.π F i).hom.lTensor (Fin n → R) y) = 0 := by
      intro i
      have hi := congrArg (fun a => (limit.π GQ i) a) hz
      have hpostQ : (limit.π GQ i) (cQ z) =
          ((MonoidalCategory.tensorLeft Q).map (limit.π F i)) z := by
        exact congrArg (fun a => a z)
          (limit.post_π F (MonoidalCategory.tensorLeft Q) i)
      rw [hpostQ] at hi
      rw [map_zero] at hi
      change (limit.π F i).hom.lTensor Q z = 0 at hi
      have hi' : (limit.π F i).hom.lTensor Q z = 0 := hi
      rw [← hy] at hi'
      rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply] at hi'
      exact hi'
    let E : Iᵒᵖ ⥤ Type u :=
      { obj := fun i => {a : (Fin m → R) ⊗[R] F.obj i //
            d.rTensor (F.obj i) a =
              (limit.π F i).hom.lTensor (Fin n → R) y}
        map := fun {i j} f => ↾(fun a =>
          (⟨(F.map f).hom.lTensor (Fin m → R) a.1, by
            rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
              ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, a.2]
            rw [← LinearMap.lTensor_comp_apply]
            have hw := congrArg ModuleCat.Hom.hom (limit.w F f)
            exact congrArg (fun p => p.lTensor (Fin n → R) y) hw
          ⟩ : {a : (Fin m → R) ⊗[R] F.obj j //
            d.rTensor (F.obj j) a =
              (limit.π F j).hom.lTensor (Fin n → R) y}))
        map_id := by
          intro i
          ext a
          change (F.map (𝟙 i)).hom.lTensor (Fin m → R) a = a
          simp
        map_comp := by
          intro i j k f g
          ext a
          change (F.map (f ≫ g)).hom.lTensor (Fin m → R) a =
            (F.map g).hom.lTensor (Fin m → R)
              ((F.map f).hom.lTensor (Fin m → R) a)
          rw [F.map_comp]
          exact LinearMap.lTensor_comp_apply (Fin m → R) _ _ a.1 }
    have hEne : ∀ i : Iᵒᵖ, Nonempty (E.obj i) := by
      intro i
      obtain ⟨a, ha⟩ :=
        ((rTensor_exact (F.obj i) hexact hq) _).mp (hrel i)
      exact ⟨⟨a, ha⟩⟩
    have hEML : E.IsMittagLeffler := by
      intro j
      obtain ⟨i, f, hf⟩ := hML j
      refine ⟨i, f, ?_⟩
      intro k g
      rintro _ ⟨eᵢ, rfl⟩
      obtain ⟨l, a, b, hab⟩ := IsCofiltered.cospan f g
      obtain ⟨eₗ⟩ := hEne l
      let aᵢ : (tensorPresentationKernelSystem d F).obj i :=
        ⟨eᵢ.1 - (E.map a eₗ).1, by
          change d.rTensor (F.obj i) (eᵢ.1 - (E.map a eₗ).1) = 0
          rw [map_sub, eᵢ.2, (E.map a eₗ).2, sub_self]
        ⟩
      obtain ⟨aₖ, haₖ⟩ := hf g ⟨aᵢ, rfl⟩
      let eₖ : E.obj k :=
        ⟨(E.map b eₗ).1 + aₖ.1, by
          rw [map_add, (E.map b eₗ).2, aₖ.2, add_zero]
        ⟩
      refine ⟨eₖ, ?_⟩
      apply Subtype.ext
      change (F.map g).hom.lTensor (Fin m → R) eₖ.1 =
        (F.map f).hom.lTensor (Fin m → R) eᵢ.1
      dsimp [eₖ]
      rw [map_add]
      have hga : (F.map g).hom.lTensor (Fin m → R) (E.map b eₗ).1 =
          (F.map f).hom.lTensor (Fin m → R) (E.map a eₗ).1 := by
        change (F.map g).hom.lTensor (Fin m → R)
            ((F.map b).hom.lTensor (Fin m → R) eₗ.1) =
          (F.map f).hom.lTensor (Fin m → R)
            ((F.map a).hom.lTensor (Fin m → R) eₗ.1)
        rw [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
        have hmaps : F.map b ≫ F.map g = F.map a ≫ F.map f := by
          rw [← F.map_comp, ← F.map_comp, hab]
        exact congrArg (fun p => p.lTensor (Fin m → R) eₗ.1)
          (congrArg ModuleCat.Hom.hom hmaps)
      have haₖ' : (F.map g).hom.lTensor (Fin m → R) aₖ.1 =
          (F.map f).hom.lTensor (Fin m → R) aᵢ.1 :=
        congrArg Subtype.val haₖ
      rw [hga, haₖ']
      dsimp [aᵢ]
      rw [map_sub]
      abel
    obtain ⟨sE, hsE⟩ :=
      Formalization.Books.Algebra.Unit86.nonempty_limit_of_countable_mittagLeffler
        hI E hEML hEne
    let hGm : IsLimit ((CategoryTheory.forget (ModuleCat.{u} R)).mapCone
        (limit.cone Gm)) :=
      isLimitOfPreserves (CategoryTheory.forget (ModuleCat.{u} R)) (limit.isLimit Gm)
    let sGm : (Gm ⋙ CategoryTheory.forget (ModuleCat.{u} R)).sections :=
      ⟨fun i => (sE i).1, by
        intro i j f
        exact congrArg Subtype.val (hsE f)⟩
    let ym : (limit Gm : ModuleCat.{u} R) :=
      (Types.isLimitEquivSections hGm).symm sGm
    obtain ⟨a, ha⟩ := hfree_m.2 ym
    have hdy : d.rTensor (limit F : ModuleCat.{u} R) a = y := by
      apply hfree_n.1
      apply Concrete.limit_ext Gn
      intro i
      have hym : (limit.π Gm i) ym = (sE i).1 := by
        simpa [ym, sGm] using
          Types.isLimitEquivSections_symm_apply hGm sGm i
      have hai := congrArg (fun t => (limit.π Gm i) t) ha
      change (limit.π Gm i)
          ((limit.post F (MonoidalCategory.tensorLeft Pm)) a) =
        (limit.π Gm i) ym at hai
      have hpostm : (limit.π Gm i)
          ((limit.post F (MonoidalCategory.tensorLeft Pm)) a) =
            ((MonoidalCategory.tensorLeft Pm).map (limit.π F i)) a := by
        exact congrArg (fun p => p a)
          (limit.post_π F (MonoidalCategory.tensorLeft Pm) i)
      rw [hpostm] at hai
      have hpostn_left : (limit.π Gn i)
          ((limit.post F (MonoidalCategory.tensorLeft Pn))
            (d.rTensor (limit F : ModuleCat.{u} R) a)) =
        ((MonoidalCategory.tensorLeft Pn).map (limit.π F i))
          (d.rTensor (limit F : ModuleCat.{u} R) a) := by
        exact congrArg (fun p => p (d.rTensor (limit F : ModuleCat.{u} R) a))
          (limit.post_π F (MonoidalCategory.tensorLeft Pn) i)
      have hpostn_right : (limit.π Gn i)
          ((limit.post F (MonoidalCategory.tensorLeft Pn)) y) =
        ((MonoidalCategory.tensorLeft Pn).map (limit.π F i)) y := by
        exact congrArg (fun p => p y)
          (limit.post_π F (MonoidalCategory.tensorLeft Pn) i)
      rw [hpostn_left, hpostn_right]
      have hai' : (limit.π F i).hom.lTensor (Fin m → R) a =
          (sE i).1 := by
        change (limit.π F i).hom.lTensor (Fin m → R) a =
          (limit.π Gm i) ym at hai
        rw [hym] at hai
        exact hai
      change (limit.π F i).hom.lTensor (Fin n → R)
          (d.rTensor (limit F : ModuleCat.{u} R) a) =
        (limit.π F i).hom.lTensor (Fin n → R) y
      rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hai']
      exact (sE i).2
    rw [← hy, ← hdy]
    exact (rTensor_exact (limit F : ModuleCat.{u} R) hexact hq _).mpr
      ⟨a, rfl⟩
  have hcQ_bijective : Function.Bijective cQ :=
    ⟨hcQ_injective, hcQ_surjective⟩
  have : IsIso cQ :=
    (ConcreteCategory.isIso_iff_bijective cQ).2 hcQ_bijective
  exact ⟨asIso cQ⟩

/-- The `ℕ`-indexed form of
`tensor_inverseSystemLimit_iso_of_finitePresentation`, with surjectivity
assumed only for the displayed successive transition maps. -/
theorem tensor_inverseSystemLimit_iso_of_finitePresentation_of_surjective
    {R : Type u} [CommRing R]
    (F : InverseSystem ℕ (ModuleCat.{u} R)) (Q : ModuleCat.{u} R)
    {m n : ℕ} (d : (Fin m → R) →ₗ[R] (Fin n → R))
    (q : (Fin n → R) →ₗ[R] Q)
    (hexact : Function.Exact d q) (hq : Function.Surjective q)
    (hsurj : ∀ k : ℕ,
      Function.Surjective (F.map (opHomOfLE (Nat.le_succ k))))
    (hML : (tensorPresentationKernelSystem d F).IsMittagLeffler) :
    Nonempty ((MonoidalCategory.tensorLeft Q).obj (InverseSystemLimit F) ≅
      (InverseSystemLimit
        (F ⋙ MonoidalCategory.tensorLeft Q) : ModuleCat.{u} R)) := by
  apply tensor_inverseSystemLimit_iso_of_finitePresentation
    (⟨inferInstance, inferInstance⟩ : IsDirectedSet ℕ)
    F Q d q hexact hq
  · exact inverseSystem_map_surjective_of_successive F hsurj
  · exact hML

end

end Formalization.Books.Algebra.Unit87
