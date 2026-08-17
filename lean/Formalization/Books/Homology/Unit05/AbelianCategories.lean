import Formalization.Books.Homology.Unit04.KaroubianCategories
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

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
  sorry

theorem preadditive_opposite
    {C : Type u} [Category.{v} C] [Preadditive C] :
    Nonempty (Preadditive Cᵒᵖ) := ⟨inferInstance⟩

theorem additive_opposite_iff
    {C : Type u} [Category.{v} C] :
    Nonempty (Formalization.Books.Homology.Unit03.AdditiveCategory C) ↔
      Nonempty (Formalization.Books.Homology.Unit03.AdditiveCategory Cᵒᵖ) := by
  sorry

theorem abelian_opposite_iff
    {C : Type u} [Category.{v} C] :
    Nonempty (Abelian C) ↔ Nonempty (Abelian Cᵒᵖ) := by
  sorry

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
  sorry

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
  sorry

theorem split_short_exact_retraction_exists_unique
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (r : S.X₂ ⟶ S.X₁) (hr : S.f ≫ r = 𝟙 _) :
    ∃! s : S.X₃ ⟶ S.X₂,
      ∃ h : S.Splitting, h.r = r ∧ h.s = s := by
  sorry

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
  sorry

theorem covariant_hom_exact_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    {M₁ M₂ M₃ : C} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (hfg : f ≫ g = 0) :
    (ComposableArrows.mk₃ (0 : (0 : C) ⟶ M₁) f g).Exact ↔
      ∀ N : C, (covariantHomSequence f g N).Exact := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
