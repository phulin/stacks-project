import Formalization.Books.Homology.Unit04.KaroubianCategories
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Preadditive.Transfer
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Homological Algebra, Chapter 5: Abelian categories

This file records the statements in the chapter using Mathlib's canonical
interfaces for abelian categories, short complexes, homological complexes,
pullbacks and pushouts, and diagram lemmas.  The substantial proposition
proofs are left for the proof stage; the constructions below use the existing
universal-property and exact-sequence APIs directly.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped ZeroObject

universe v u

namespace Formalization.Books.Homology.Unit05

/-! ## Abelian categories and injective/surjective morphisms -/

theorem abelian_iff_coimage_image_comparison_isIso
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteProducts C] [HasKernels C] [HasCokernels C] :
    Nonempty (Abelian C) ↔
      ∀ {X Y : C} (f : X ⟶ Y),
        IsIso (Abelian.coimageImageComparison f) := by
  constructor
  · rintro ⟨h⟩
    letI : Abelian C := h
    letI : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
    letI : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
    intro X Y f
    have hpre : h.toPreadditive = (inferInstance : Preadditive C) := Subsingleton.elim _ _
    cases hpre
    exact Abelian.instIsIsoCoimageImageComparison f
  · intro h
    letI : ∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := h
    exact ⟨Abelian.ofCoimageImageComparisonIsIso⟩

theorem preadditive_opposite
    {C : Type u} [Category.{v} C] [Preadditive C] :
    Nonempty (Preadditive Cᵒᵖ) := ⟨inferInstance⟩

theorem additive_opposite_iff
    {C : Type u} [Category.{v} C] :
    Nonempty (Formalization.Books.Homology.Unit03.AdditiveCategory C) ↔
      Nonempty (Formalization.Books.Homology.Unit03.AdditiveCategory Cᵒᵖ) := by
  constructor
  · rintro ⟨h⟩
    letI : Formalization.Books.Homology.Unit03.AdditiveCategory C := h
    letI : HasFiniteBiproducts C :=
      Formalization.Books.Homology.Unit03.additiveCategory_hasFiniteBiproducts C
    exact ⟨{ toPreadditive := inferInstance, toHasFiniteProducts := inferInstance }⟩
  · rintro ⟨h⟩
    letI : Formalization.Books.Homology.Unit03.AdditiveCategory Cᵒᵖ := h
    letI : Preadditive Cᵒᵖᵒᵖ := inferInstance
    letI : Preadditive C :=
      Preadditive.ofFullyFaithful (opOpEquivalence C).fullyFaithfulInverse
    letI : HasFiniteCoproducts C := Limits.hasFiniteCoproducts_of_opposite
    letI : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteCoproducts
    exact ⟨{ toPreadditive := inferInstance, toHasFiniteProducts := inferInstance }⟩

theorem abelian_opposite_iff
    {C : Type u} [Category.{v} C] :
    Nonempty (Abelian C) ↔ Nonempty (Abelian Cᵒᵖ) := by
  constructor
  · rintro ⟨h⟩
    letI : Abelian C := h
    exact ⟨inferInstance⟩
  · rintro ⟨h⟩
    letI : Abelian Cᵒᵖ := h
    letI : Abelian Cᵒᵖᵒᵖ := inferInstance
    letI : Preadditive Cᵒᵖᵒᵖ := inferInstance
    letI : Preadditive C :=
      Preadditive.ofFullyFaithful (opOpEquivalence C).fullyFaithfulInverse
    letI : HasFiniteCoproducts C := Limits.hasFiniteCoproducts_of_opposite
    letI : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteCoproducts
    exact ⟨abelianOfEquivalence (opOp C)⟩

theorem abelian_coimage_image_comparison_isIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) :
    IsIso (Abelian.coimageImageComparison f) := inferInstance

def InjectiveMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  IsZero (kernel f)

def SurjectiveMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  IsZero (cokernel f)

theorem injective_iff_mono
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) :
    InjectiveMorphism f ↔ Mono f := by
  exact (mono_iff_isZero_kernel f).symm

theorem surjective_iff_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) :
    SurjectiveMorphism f ↔ Epi f := by
  exact (epi_iff_isZero_cokernel f).symm

theorem isIso_iff_injective_and_surjective
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ InjectiveMorphism f ∧ SurjectiveMorphism f := by
  rw [isIso_iff_mono_and_epi]
  exact and_congr (injective_iff_mono f).symm (surjective_iff_epi f).symm

noncomputable abbrev quotientOfSubobject
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) [Mono f] : C :=
  cokernel f

theorem abelian_has_finite_limits_and_colimits
    {C : Type u} [Category.{v} C] [Abelian C] :
    HasFiniteLimits C ∧ HasFiniteColimits C :=
  ⟨inferInstance, inferInstance⟩

/-! ## Fibre products and pushouts -/

noncomputable def fibre_product_is_kernel
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} (a : X ⟶ Y) (b : Z ⟶ Y) :
    IsLimit (Abelian.PullbackToBiproductIsKernel.pullbackToBiproductFork a b) :=
  Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct a b

noncomputable def pushout_is_cokernel
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) :
    IsColimit (Abelian.BiproductToPushoutIsCokernel.biproductToPushoutCofork a b) :=
  Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout a b

/-! ## Complexes and exactness -/

abbrev FiniteComplex (C : Type u) [Category.{v} C] [HasZeroMorphisms C] (n : ℕ) :=
  ComposableArrows C n

abbrev FiniteExactComplex
    {C : Type u} [Category.{v} C] [Abelian C] {n : ℕ}
    (K : ComposableArrows C n) : Prop :=
  K.Exact

theorem short_complex_exact_iff_image_eq_kernel
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} :
    S.Exact ↔ imageSubobject S.f = kernelSubobject S.g :=
  ShortComplex.exact_iff_image_eq_kernel S

abbrev ChainComplexOverNat (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  ChainComplex C ℕ

abbrev ChainComplexOverInt (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  ChainComplex C ℤ

abbrev CochainComplexOverNat (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  CochainComplex C ℕ

abbrev ExactAt
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι) : Prop :=
  K.ExactAt i

abbrev AcyclicComplex
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) : Prop :=
  K.Acyclic

abbrev ShortExactSequence
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] :=
  ShortComplex C

def IsShortExactSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) : Prop :=
  S.ShortExact

def IsSplitShortExactSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) : Prop :=
  S.ShortExact ∧ Nonempty S.Splitting

noncomputable def split_of_section
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 _) : S.Splitting :=
  ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f

noncomputable def split_of_retraction
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (r : S.X₂ ⟶ S.X₁) (hr : S.f ≫ r = 𝟙 _) : S.Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction S hS.exact r hr hS.epi_g

theorem split_short_exact_section_exists_unique
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 _) :
    ∃! r : S.X₂ ⟶ S.X₁,
      ∃ h : S.Splitting, h.s = s ∧ h.r = r := by
  let h₀ := split_of_section hS s hs
  refine ⟨h₀.r, ⟨h₀, rfl, rfl⟩, ?_⟩
  intro r hr
  obtain ⟨h, hs', hr'⟩ := hr
  have h₀s : h₀.s = s := rfl
  have hh : h = h₀ := ShortComplex.Splitting.ext_s h h₀ (hs'.trans h₀s.symm)
  exact hr'.symm.trans (congrArg (fun t : S.Splitting => t.r) hh)

theorem split_short_exact_retraction_exists_unique
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (r : S.X₂ ⟶ S.X₁) (hr : S.f ≫ r = 𝟙 _) :
    ∃! s : S.X₃ ⟶ S.X₂,
      ∃ h : S.Splitting, h.r = r ∧ h.s = s := by
  let h₀ := split_of_retraction hS r hr
  refine ⟨h₀.s, ⟨h₀, rfl, rfl⟩, ?_⟩
  intro s hs
  obtain ⟨h, hr', hs'⟩ := hs
  have h₀r : h₀.r = r := rfl
  have hh : h = h₀ := ShortComplex.Splitting.ext_r h h₀ (hr'.trans h₀r.symm)
  exact hs'.symm.trans (congrArg (fun t : S.Splitting => t.s) hh)

noncomputable def contravariantHomSequence
    {C : Type u} [Category.{v} C] [Preadditive C]
    {M₁ M₂ M₃ : C} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (N : C) :
    ComposableArrows AddCommGrpCat.{v} 3 :=
  ComposableArrows.mk₃
    (0 : (0 : AddCommGrpCat.{v}) ⟶
      (preadditiveYoneda.obj N).obj (Opposite.op M₃))
    ((preadditiveYoneda.obj N).map g.op)
    ((preadditiveYoneda.obj N).map f.op)

noncomputable def covariantHomSequence
    {C : Type u} [Category.{v} C] [Preadditive C]
    {M₁ M₂ M₃ : C} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (N : C) :
    ComposableArrows AddCommGrpCat.{v} 3 :=
  ComposableArrows.mk₃
    (0 : (0 : AddCommGrpCat.{v}) ⟶
      (preadditiveCoyoneda.obj (Opposite.op N)).obj M₁)
    ((preadditiveCoyoneda.obj (Opposite.op N)).map f)
    ((preadditiveCoyoneda.obj (Opposite.op N)).map g)

theorem contravariant_hom_exact_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    {M₁ M₂ M₃ : C} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (hfg : f ≫ g = 0) :
    (ComposableArrows.mk₃ f g (0 : M₃ ⟶ (0 : C))).Exact ↔
      ∀ N : C, (contravariantHomSequence f g N).Exact := by
  let F : ∀ N : C, Cᵒᵖ ⥤ AddCommGrpCat.{v} := fun N => preadditiveYoneda.obj N
  have hJ : JointlyReflectIsomorphisms F := by
    constructor
    intro X Y q hq
    letI : IsIso (coyoneda.map q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro N
      rw [isIso_iff_bijective]
      change Function.Bijective (fun g : X.unop ⟶ N => q.unop ≫ g)
      have h := ConcreteCategory.bijective_of_isIso ((F N).map q)
      change Function.Bijective (fun g : X.unop ⟶ N => q.unop ≫ g) at h
      exact h
    exact Coyoneda.isIso q
  constructor
  · intro h
    let S := ShortComplex.mk f g hfg
    have hS : S.Exact := by
      exact h.exact 0
    have hSop : S.op.Exact := hS.op
    have hEpi : Epi g := by
      have h' := (ShortComplex.exact_iff_epi
        ((ComposableArrows.mk₃ f g (0 : M₃ ⟶ (0 : C))).sc h.toIsComplex 1)
        (by change (0 : M₃ ⟶ (0 : C)) = 0; rfl)).1
        (h.exact 1)
      change Epi g at h'
      exact h'
    letI : Epi g := hEpi
    intro N
    letI : Mono g.op := op_mono_of_epi g
    have htail : (ShortComplex.mk
        ((F N).map g.op) ((F N).map f.op)
        (by simp [F, ← Functor.map_comp, ← op_comp, hfg])).Exact := by
      letI : Mono S.op.f := by
        change Mono g.op
        exact op_mono_of_epi g
      exact hSop.map_of_mono_of_preservesKernel (F N) inferInstance inferInstance
    have hhead : (ShortComplex.mk (0 : (0 : AddCommGrpCat.{v}) ⟶
        (F N).obj (Opposite.op M₃))
        ((F N).map g.op) zero_comp).Exact := by
      apply (ShortComplex.exact_iff_mono _ rfl).2
      infer_instance
    apply ComposableArrows.exact_of_δ₀
    · change (ComposableArrows.mk₂ (0 : (0 : AddCommGrpCat.{v}) ⟶
          (F N).obj (Opposite.op M₃)) ((F N).map g.op)).Exact
      exact hhead.exact_toComposableArrows
    · change (ComposableArrows.mk₂ ((F N).map g.op) ((F N).map f.op)).Exact
      exact htail.exact_toComposableArrows
  · intro h
    have hMono : Mono g.op := by
      letI : ∀ N : C, Mono ((F N).map g.op) := fun N => by
        have hN := (h N).exact 0
        change (ShortComplex.mk (0 : (0 : AddCommGrpCat.{v}) ⟶
          (F N).obj (Opposite.op M₃)) ((F N).map g.op) zero_comp).Exact at hN
        exact (ShortComplex.exact_iff_mono _ rfl).1 hN
      apply hJ.jointlyReflectMonomorphisms.mono g.op
    letI : Mono g.op := hMono
    have hEpi : Epi g := unop_epi_of_mono g.op
    let S : ShortComplex C := ShortComplex.mk f g hfg
    let T := S.op
    have hSop : T.Exact := by
      apply (ShortComplex.exact_iff_epi_kernel_lift (S := T)).2
      let u := kernel.lift f.op g.op (by simp [← op_comp, hfg])
      change Epi u
      letI : ∀ N : C, IsIso ((F N).map u) := fun N => by
        letI : Mono ((F N).map g.op) := by
          exact inferInstance
        have hNtail : (ShortComplex.mk ((F N).map g.op) ((F N).map f.op)
            (by simp [F, ← Functor.map_comp, ← op_comp, hfg])).Exact := by
          have hN := (h N).exact 1
          change (ShortComplex.mk ((F N).map g.op) ((F N).map f.op)
            (by simp [F, ← Functor.map_comp, ← op_comp, hfg])).Exact at hN
          exact hN
        have hmap := hNtail.fIsKernel
        let hkernel := KernelFork.mapIsLimit
          (KernelFork.ofι (kernel.ι f.op) (kernel.condition f.op))
          (kernelIsKernel f.op) (F N)
        let e := IsLimit.conePointUniqueUpToIso hkernel hmap
        have heq : (F N).map u = e.inv := by
          apply (cancel_mono ((F N).map (kernel.ι f.op))).1
          rw [← Functor.map_comp]
          simp only [u, kernel.lift_ι]
          change (F N).map g.op = e.inv ≫ (F N).map (kernel.ι f.op)
          simpa using
            (IsLimit.conePointUniqueUpToIso_inv_comp hkernel hmap
              WalkingParallelPair.zero).symm
        rw [heq]
        change IsIso e.inv
        infer_instance
      haveI : IsIso u := hJ.isIso u
      infer_instance
    have hS : S.Exact := hSop.unop
    refine ⟨?_, ?_⟩
    ·
      refine ⟨?_⟩
      intro i hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · dsimp
        exact hfg
      · dsimp
        change g ≫ (0 : M₃ ⟶ (0 : C)) = 0
        simp
    · intro i hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · change (ShortComplex.mk f g hfg).Exact
        exact hS
      · have h0 : (ShortComplex.mk g (0 : M₃ ⟶ (0 : C)) (by simp)).Exact :=
          (ShortComplex.exact_iff_epi _ (by rfl)).2 hEpi
        change (ShortComplex.mk g (0 : M₃ ⟶ (0 : C)) (by simp)).Exact
        exact h0

theorem covariant_hom_exact_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    {M₁ M₂ M₃ : C} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (hfg : f ≫ g = 0) :
    (ComposableArrows.mk₃ (0 : (0 : C) ⟶ M₁) f g).Exact ↔
      ∀ N : C, (covariantHomSequence f g N).Exact := by
  let G : ∀ N : C, C ⥤ AddCommGrpCat.{v} :=
    fun N => preadditiveCoyoneda.obj (Opposite.op N)
  have hJ : JointlyReflectIsomorphisms G := by
    constructor
    intro X Y q hq
    letI : IsIso ((yoneda : C ⥤ Cᵒᵖ ⥤ Type v).map q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro N
      rw [isIso_iff_bijective]
      change Function.Bijective (fun g : N.unop ⟶ X => g ≫ q)
      have h := ConcreteCategory.bijective_of_isIso ((G N.unop).map q)
      change Function.Bijective (fun g : N.unop ⟶ X => g ≫ q) at h
      exact h
    exact Yoneda.isIso q
  constructor
  · intro h
    let S := ShortComplex.mk f g hfg
    have hS : S.Exact := by
      have h' := h.exact 1
      change (ShortComplex.mk f g hfg).Exact at h'
      exact h'
    have hMono : Mono f := by
      have h' := h.exact 0
      change (ShortComplex.mk (0 : (0 : C) ⟶ M₁) f zero_comp).Exact at h'
      exact (ShortComplex.exact_iff_mono _ rfl).1 h'
    letI : Mono f := hMono
    intro N
    have htail : (ShortComplex.mk ((G N).map f) ((G N).map g)
        (by simp [G, ← Functor.map_comp, hfg])).Exact := by
      exact hS.map_of_mono_of_preservesKernel (G N) inferInstance inferInstance
    have hhead : (ShortComplex.mk (0 : (0 : AddCommGrpCat.{v}) ⟶
        (G N).obj M₁) ((G N).map f) zero_comp).Exact := by
      apply (ShortComplex.exact_iff_mono _ rfl).2
      infer_instance
    apply ComposableArrows.exact_of_δ₀
    · change (ComposableArrows.mk₂ (0 : (0 : AddCommGrpCat.{v}) ⟶
          (G N).obj M₁) ((G N).map f)).Exact
      exact hhead.exact_toComposableArrows
    · change (ComposableArrows.mk₂ ((G N).map f) ((G N).map g)).Exact
      exact htail.exact_toComposableArrows
  · intro h
    have hMono : Mono f := by
      letI : ∀ N : C, Mono ((G N).map f) := fun N => by
        have hN := (h N).exact 0
        change (ShortComplex.mk (0 : (0 : AddCommGrpCat.{v}) ⟶
          (G N).obj M₁) ((G N).map f) zero_comp).Exact at hN
        exact (ShortComplex.exact_iff_mono _ rfl).1 hN
      apply hJ.jointlyReflectMonomorphisms.mono f
    letI : Mono f := hMono
    let S : ShortComplex C := ShortComplex.mk f g hfg
    have hS : S.Exact := by
      apply (ShortComplex.exact_iff_epi_kernel_lift (S := S)).2
      let u := kernel.lift g f (by simp [hfg])
      change Epi u
      let : ∀ N : C, IsIso ((G N).map u) := fun N => by
        let : Mono ((G N).map f) := by
          exact inferInstance
        have hNtail : (ShortComplex.mk ((G N).map f) ((G N).map g)
            (by simp [G, ← Functor.map_comp, hfg])).Exact := by
          have hN := (h N).exact 1
          change (ShortComplex.mk ((G N).map f) ((G N).map g)
            (by simp [G, ← Functor.map_comp, hfg])).Exact at hN
          exact hN
        have hmap := hNtail.fIsKernel
        let hkernel := KernelFork.mapIsLimit
          (KernelFork.ofι (kernel.ι g) (kernel.condition g))
          (kernelIsKernel g) (G N)
        let e := IsLimit.conePointUniqueUpToIso hkernel hmap
        have heq : (G N).map u = e.inv := by
          apply (cancel_mono ((G N).map (kernel.ι g))).1
          rw [← Functor.map_comp]
          simp only [u, kernel.lift_ι]
          change (G N).map f = e.inv ≫ (G N).map (kernel.ι g)
          simpa using
            (IsLimit.conePointUniqueUpToIso_inv_comp hkernel hmap
              WalkingParallelPair.zero).symm
        rw [heq]
        change IsIso e.inv
        infer_instance
      have : IsIso u := hJ.isIso u
      infer_instance
    refine ⟨?_, ?_⟩
    · refine ⟨?_⟩
      intro i hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · dsimp
        change (0 : (0 : C) ⟶ M₁) ≫ f = 0
        simp
      · dsimp
        exact hfg
    · intro i hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · change (ShortComplex.mk (0 : (0 : C) ⟶ M₁) f (by simp)).Exact
        exact (ShortComplex.exact_iff_mono _ rfl).2 hMono
      · change (ShortComplex.mk f g hfg).Exact
        exact hS

/-! ## Cartesian and cocartesian squares -/

abbrev CartesianSquare
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {W X Y Z : C} (f : W ⟶ Y) (g : W ⟶ X) (h : Y ⟶ Z) (k : X ⟶ Z) :=
  IsPullback f g h k

abbrev CocartesianSquare
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {W X Y Z : C} (f : W ⟶ Y) (g : W ⟶ X) (h : Y ⟶ Z) (k : X ⟶ Z) :=
  IsPushout f g h k

theorem cartesian_iff_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {W X Y Z : C} (f : W ⟶ Y) (g : W ⟶ X) (h : Y ⟶ Z) (k : X ⟶ Z)
    (comm : f ≫ h = g ≫ k) :
    IsPullback f g h k ↔
      (ComposableArrows.mk₃ (0 : (0 : C) ⟶ W)
        (biprod.lift g f) (biprod.desc k (-h))).Exact := by
  let sq : CommSq g f k h := ⟨comm.symm⟩
  constructor
  · intro hpb
    have hsc : (ShortComplex.mk (biprod.lift g f) (biprod.desc k (-h))
        (by simp [comm])).Exact := by
      simpa [CommSq.shortComplex'] using hpb.flip.exact_shortComplex'
    have hmono : Mono (biprod.lift g f) := by
      simpa [CommSq.shortComplex'] using hpb.flip.mono_shortComplex'_f
    refine ⟨?_, ?_⟩
    · refine ⟨?_⟩
      intro i hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · dsimp
        change (0 : (0 : C) ⟶ W) ≫ biprod.lift g f = 0
        simp
      · dsimp
        change biprod.lift g f ≫ biprod.desc k (-h) = 0
        simp [comm]
    · intro i hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · change (ShortComplex.mk (0 : (0 : C) ⟶ W) (biprod.lift g f)
          (by simp)).Exact
        exact (ShortComplex.exact_iff_mono _ rfl).2 hmono
      · change (ShortComplex.mk (biprod.lift g f) (biprod.desc k (-h))
          (by simp [comm])).Exact
        exact hsc
  · intro hex
    have hmono : Mono (biprod.lift g f) := by
      have h' := hex.exact 0
      change (ShortComplex.mk (0 : (0 : C) ⟶ W) (biprod.lift g f)
        (by simp)).Exact at h'
      exact (ShortComplex.exact_iff_mono _ rfl).1 h'
    let : Mono (biprod.lift g f) := hmono
    have hsc : (ShortComplex.mk (biprod.lift g f) (biprod.desc k (-h))
        (by simp [comm])).Exact := by
      have h' := hex.exact 1
      change (ShortComplex.mk (biprod.lift g f) (biprod.desc k (-h))
        (by simp [comm])).Exact at h'
      exact h'
    apply IsPullback.flip
    refine IsPullback.of_isLimit
      (c := PullbackCone.mk g f (by simpa [sq] using sq.w)) ?_
    simpa [sq] using
      (sq.isLimitEquivIsLimitKernelFork).symm (by simpa [sq] using hsc.fIsKernel)

theorem cocartesian_iff_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {W X Y Z : C} (f : W ⟶ Y) (g : W ⟶ X) (h : Y ⟶ Z) (k : X ⟶ Z)
    (comm : f ≫ h = g ≫ k) :
    IsPushout f g h k ↔
      (ComposableArrows.mk₃ (biprod.lift g (-f)) (biprod.desc k h)
        (0 : Z ⟶ (0 : C))).Exact := by
  sorry

theorem cartesian_kernel_map_isIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}
    (sq : IsPullback f g h k) :
    IsIso (kernel.map f k g h sq.w) :=
  isIso_kernel_map_of_isPullback sq

theorem cocartesian_cokernel_map_isIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}
    (sq : IsPushout f g h k) :
    IsIso (cokernel.map f k g h sq.w) :=
  isIso_cokernel_map_of_isPushout sq

theorem cartesian_epi_is_cocartesian
    {C : Type u} [Category.{v} C] [Abelian C]
    {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}
    (sq : IsPullback f g h k) [Epi k] :
    IsPushout f g h k ∧ Epi f := by
  sorry

theorem cocartesian_mono_is_cartesian
    {C : Type u} [Category.{v} C] [Abelian C]
    {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}
    (sq : IsPushout f g h k) [Mono g] :
    IsPullback f g h k ∧ Mono h := by
  sorry

theorem pullback_projection_surjective
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [Epi a] :
    Epi (pullback.snd a b) := inferInstance

theorem pushout_injection_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [Mono a] :
    Mono (pushout.inr a b) := inferInstance

/-! ## Fibre-product exactness and induced kernel/cokernel sequences -/

theorem exact_iff_epi_refinement
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0) :
    (ShortComplex.mk f g hfg).Exact ↔
      ∀ {W : C} (h : W ⟶ Y) (hh : h ≫ g = 0),
        ∃ (V : C) (k : V ⟶ W) (l : V ⟶ X),
          Epi k ∧ k ≫ h = l ≫ f := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  constructor
  · intro h W x hx
    obtain ⟨V, k, hk, l, hl⟩ := h x hx
    exact ⟨V, k, l, hk, hl⟩
  · intro h A x hx
    obtain ⟨V, k, l, hk, hl⟩ := h x hx
    exact ⟨V, k, hk, l, hl⟩

noncomputable def inducedKernelMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y U V : C} (f : X ⟶ Y) (k : U ⟶ V)
    (α : X ⟶ U) (β : Y ⟶ V) (comm : f ≫ β = α ≫ k) :
    kernel α ⟶ kernel β :=
  kernel.map α β f k comm.symm

noncomputable def inducedCokernelMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y U V : C} (f : X ⟶ Y) (k : U ⟶ V)
    (α : X ⟶ U) (β : Y ⟶ V) (comm : f ≫ β = α ≫ k) :
    cokernel α ⟶ cokernel β :=
  cokernel.map α β f k comm.symm

theorem induced_kernel_maps_comp_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z U V W : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : U ⟶ V} {l : V ⟶ W}
    {α : X ⟶ U} {β : Y ⟶ V} {γ : Z ⟶ W}
    (hfg : f ≫ g = 0)
    (h₁ : f ≫ β = α ≫ k) (h₂ : g ≫ γ = β ≫ l) :
    inducedKernelMap f k α β h₁ ≫ inducedKernelMap g l β γ h₂ = 0 := by
  apply (cancel_mono (kernel.ι γ)).1
  simp [inducedKernelMap, Category.assoc, hfg]

theorem induced_cokernel_maps_comp_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z U V W : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : U ⟶ V} {l : V ⟶ W}
    {α : X ⟶ U} {β : Y ⟶ V} {γ : Z ⟶ W}
    (hkl : k ≫ l = 0)
    (h₁ : f ≫ β = α ≫ k) (h₂ : g ≫ γ = β ≫ l) :
    inducedCokernelMap f k α β h₁ ≫ inducedCokernelMap g l β γ h₂ = 0 := by
  apply (cancel_epi (cokernel.π α)).1
  simp [inducedCokernelMap, Category.assoc]
  rw [← Category.assoc, hkl, zero_comp]

theorem exact_kernel_sequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z U V W : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : U ⟶ V} {l : V ⟶ W}
    {α : X ⟶ U} {β : Y ⟶ V} {γ : Z ⟶ W}
    (hfg : f ≫ g = 0)
    (h₁ : f ≫ β = α ≫ k) (h₂ : g ≫ γ = β ≫ l)
    (hrow : (ShortComplex.mk f g hfg).Exact) [Mono k] :
    (ShortComplex.mk
      (inducedKernelMap f k α β h₁)
      (inducedKernelMap g l β γ h₂)
      (induced_kernel_maps_comp_zero hfg h₁ h₂)).Exact := by
  sorry

theorem exact_cokernel_sequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z U V W : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : U ⟶ V} {l : V ⟶ W}
    {α : X ⟶ U} {β : Y ⟶ V} {γ : Z ⟶ W}
    (hkl : k ≫ l = 0)
    (h₁ : f ≫ β = α ≫ k) (h₂ : g ≫ γ = β ≫ l)
    (hrow : (ShortComplex.mk k l hkl).Exact) [Epi g] :
    (ShortComplex.mk
      (inducedCokernelMap f k α β h₁)
      (inducedCokernelMap g l β γ h₂)
      (induced_cokernel_maps_comp_zero hkl h₁ h₂)).Exact := by
  sorry

/-! ## The snake lemma and its naturality -/

abbrev SnakeInput
    (C : Type u) [Category.{v} C] [Abelian C] :=
  ShortComplex.SnakeInput C

noncomputable def snakeConnectingMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex.SnakeInput C) : S.L₀.X₃ ⟶ S.L₃.X₁ :=
  S.δ

noncomputable def snakeExactSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex.SnakeInput C) : ComposableArrows C 5 :=
  S.composableArrows

theorem snake_connecting_morphism_characterization
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex.SnakeInput C) {A : C}
    (x₃ : A ⟶ S.L₀.X₃) (x₂ : A ⟶ S.L₁.X₂) (x₁ : A ⟶ S.L₂.X₁)
    (h₂ : x₂ ≫ S.L₁.g = x₃ ≫ S.v₀₁.τ₃)
    (h₁ : x₁ ≫ S.L₂.f = x₂ ≫ S.v₁₂.τ₂) :
    x₃ ≫ snakeConnectingMorphism S = x₁ ≫ S.v₂₃.τ₁ := by
  exact S.δ_eq x₃ x₂ x₁ h₂ h₁

theorem snake_connecting_morphism_exists_unique
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex.SnakeInput C) :
    ∃! δ : S.L₀.X₃ ⟶ S.L₃.X₁,
      ∀ {A : C} (x₃ : A ⟶ S.L₀.X₃) (x₂ : A ⟶ S.L₁.X₂) (x₁ : A ⟶ S.L₂.X₁),
        x₂ ≫ S.L₁.g = x₃ ≫ S.v₀₁.τ₃ →
        x₁ ≫ S.L₂.f = x₂ ≫ S.v₁₂.τ₂ →
        x₃ ≫ δ = x₁ ≫ S.v₂₃.τ₁ := by
  set_option backward.isDefEq.respectTransparency false in
  refine ⟨S.δ, ?_, ?_⟩
  · intro A x₃ x₂ x₁ h₂ h₁
    exact S.δ_eq x₃ x₂ x₁ h₂ h₁
  · intro δ' hδ'
    apply (cancel_epi (pullback.snd S.L₁.g S.v₀₁.τ₃)).1
    let e : pullback S.L₁.g S.v₀₁.τ₃ = S.P := rfl
    have h := hδ' (pullback.snd S.L₁.g S.v₀₁.τ₃)
      (pullback.fst S.L₁.g S.v₀₁.τ₃) (eqToHom e ≫ S.φ₁) pullback.condition
      (by
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, eqToHom_map,
          Category.comp_id]
        simpa [ShortComplex.SnakeInput.φ₂] using S.φ₁_L₂_f)
    simpa [e] using h

theorem snake_exact_sequence_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex.SnakeInput C) :
    (snakeExactSequence S).Exact :=
  S.snake_lemma

theorem snake_first_map_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex.SnakeInput C) [Mono S.L₁.f] :
    Mono S.L₀.f := inferInstance

theorem snake_last_map_surjective
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex.SnakeInput C) [Epi S.L₂.g] :
    Epi S.L₃.g := inferInstance

theorem snake_connecting_morphism_natural
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex.SnakeInput C} (φ : S₁ ⟶ S₂) :
    snakeConnectingMorphism S₁ ≫ φ.f₃.τ₁ =
      φ.f₀.τ₃ ≫ snakeConnectingMorphism S₂ :=
  S₁.naturality_δ φ

noncomputable def snakeExactSequenceMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex.SnakeInput C} (φ : S₁ ⟶ S₂) :
    snakeExactSequence S₁ ⟶ snakeExactSequence S₂ :=
  ShortComplex.SnakeInput.composableArrowsFunctor.map φ

/-! ## The four lemma and the five lemma -/

theorem four_lemma_surjective
    {C : Type u} [Category.{v} C] [Abelian C]
    {R₁ R₂ : ComposableArrows C 3} (φ : R₁ ⟶ R₂)
    (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    [Epi (ComposableArrows.app' φ 0)]
    [Epi (ComposableArrows.app' φ 2)]
    [Mono (ComposableArrows.app' φ 3)] :
    Epi (ComposableArrows.app' φ 1) :=
  CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono φ hR₁ hR₂
    inferInstance inferInstance inferInstance

theorem four_lemma_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    {R₁ R₂ : ComposableArrows C 3} (φ : R₁ ⟶ R₂)
    (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    [Epi (ComposableArrows.app' φ 0)]
    [Mono (ComposableArrows.app' φ 1)]
    [Mono (ComposableArrows.app' φ 3)] :
    Mono (ComposableArrows.app' φ 2) :=
  CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono φ hR₁ hR₂
    inferInstance inferInstance inferInstance

theorem five_lemma
    {C : Type u} [Category.{v} C] [Abelian C]
    {R₁ R₂ : ComposableArrows C 4} (φ : R₁ ⟶ R₂)
    (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    [Epi (ComposableArrows.app' φ 0)]
    [IsIso (ComposableArrows.app' φ 1)]
    [IsIso (ComposableArrows.app' φ 3)]
    [Mono (ComposableArrows.app' φ 4)] :
    IsIso (ComposableArrows.app' φ 2) :=
  CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR₁ hR₂ φ
    inferInstance inferInstance inferInstance inferInstance

end Formalization.Books.Homology.Unit05
