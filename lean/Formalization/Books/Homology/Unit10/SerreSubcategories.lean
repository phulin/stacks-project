import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Homological Algebra, Chapter 10: Serre subcategories

Mathlib's `ObjectProperty.IsSerreClass` is the canonical interface for the
source's Serre subcategories.  A property `P` presents the corresponding full
subcategory as `P.FullSubcategory`; its closure-under-isomorphisms instance is
the source's strictly-full condition.  The quotient construction is likewise
the canonical localization at `P.isoModSerre`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

universe v u v' u'

namespace CategoryTheory
namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The exact-five-term closure condition used for weak Serre subcategories.

The parent `Nonempty` field records the source's nonemptiness requirement;
`P.FullSubcategory` supplies the corresponding full subcategory. -/
class IsWeakSerreClass (P : ObjectProperty C) : Prop extends P.Nonempty where
  prop_X₂_of_exact {S : ComposableArrows C 4} (hS : S.Exact)
      (h₀ : P (S.obj' 0)) (h₁ : P (S.obj' 1))
      (h₃ : P (S.obj' 3)) (h₄ : P (S.obj' 4)) : P (S.obj' 2)

lemma prop_X₂_of_exact_weakSerre {P : ObjectProperty C} [P.IsWeakSerreClass]
    {S : ComposableArrows C 4} (hS : S.Exact)
    (h₀ : P (S.obj' 0)) (h₁ : P (S.obj' 1))
    (h₃ : P (S.obj' 3)) (h₄ : P (S.obj' 4)) : P (S.obj' 2) :=
  IsWeakSerreClass.prop_X₂_of_exact hS h₀ h₁ h₃ h₄

end ObjectProperty
end CategoryTheory

namespace Formalization.Books.Homology.Unit10

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ## Serre and weak Serre subcategories -/

/- `ObjectProperty.IsSerreClass` is Mathlib's source-faithful definition of a
Serre subcategory.  Its `FullSubcategory` is full, and closure under
isomorphisms is the strict-full condition. -/

theorem serre_subcategory_is_nonempty_and_full
    (P : ObjectProperty C) [P.IsSerreClass] :
    Nonempty P.FullSubcategory ∧ Nonempty P.ι.FullyFaithful := by
  exact ⟨inferInstance, ⟨P.fullyFaithfulι⟩⟩

theorem serre_subcategory_characterization
    (P : ObjectProperty C) :
    P.IsSerreClass ↔
      P (0 : C) ∧
        P.IsClosedUnderIsomorphisms ∧
          (P.IsClosedUnderSubobjects ∧ P.IsClosedUnderQuotients) ∧
            P.IsClosedUnderExtensions := by
  constructor
  · intro h
    have hsub : P.IsClosedUnderSubobjects := h.toIsClosedUnderSubobjects
    have hquot : P.IsClosedUnderQuotients := h.toIsClosedUnderQuotients
    have hext : P.IsClosedUnderExtensions := h.toIsClosedUnderExtensions
    obtain ⟨Z, hZ, hP⟩ := h.toContainsZero.exists_zero
    have h0 : P (0 : C) := hsub.prop_of_mono (hZ.iso (isZero_zero C)).inv hP
    have hIso : P.IsClosedUnderIsomorphisms :=
      { of_iso := fun e hX => hsub.prop_of_mono e.inv hX }
    exact ⟨h0, hIso, ⟨hsub, hquot⟩, hext⟩
  · rintro ⟨h0, _, ⟨hsub, hquot⟩, hext⟩
    refine @ObjectProperty.IsSerreClass.mk C _ _ P ?_ ?_ ?_ ?_
    · exact ⟨⟨0, isZero_zero C, h0⟩⟩
    · exact hsub
    · exact hquot
    · exact hext
/-
  constructor
  · intro h
    have hsub : P.IsClosedUnderSubobjects := h.toIsClosedUnderSubobjects
    have hquot : P.IsClosedUnderQuotients := h.toIsClosedUnderQuotients
    have hext : P.IsClosedUnderExtensions := h.toIsClosedUnderExtensions
    obtain ⟨Z, hZ, hP⟩ := h.toContainsZero.exists_zero
    have h0 : P (0 : C) := hsub.prop_of_mono (hZ.iso (isZero_zero C)).inv hP
    have hIso : P.IsClosedUnderIsomorphisms :=
      { of_iso := fun e hX => hsub.prop_of_mono e.inv hX }
    exact ⟨h0, hIso, ⟨hsub, hquot⟩, hext⟩
  · rintro ⟨h0, _, ⟨hsub, hquot⟩, hext⟩
    refine @ObjectProperty.IsSerreClass.mk C _ _ P ?_ ?_ ?_ ?_
    · exact ⟨⟨0, isZero_zero C, h0⟩⟩
    · exact hsub
    · exact hquot
    · exact hext

theorem serre_subcategory_is_abelian_and_inclusion_exact
    (P : ObjectProperty C) [P.IsSerreClass] :
    Nonempty (Abelian P.FullSubcategory) ∧
      exactFunctor P.FullSubcategory C P.ι := by
  have hBin : P.IsClosedUnderBinaryProducts :=
    ObjectProperty.IsClosedUnderLimitsOfShape.mk' (P := P)
      (J := Discrete WalkingPair) (by
        rintro _ ⟨F, hF⟩
        exact P.prop_of_iso
          (IsLimit.conePointsIsoOfNatIso (BinaryBiproduct.isLimit _ _)
            (limit.isLimit F) (diagramIsoPair F).symm)
          (P.prop_biprod (hF _) (hF _)))
  have hFinite : P.IsClosedUnderFiniteProducts :=
    @ObjectProperty.IsClosedUnderFiniteProducts.mk' C _ P inferInstance inferInstance hBin
  letI : Abelian P.FullSubcategory :=
    @ObjectProperty.instAbelianFullSubcategoryOfContainsZeroOfIsClosedUnderKernelsOfIsClosedUnderCokernelsOfIsClosedUnderFiniteProducts
      C _ P inferInstance inferInstance inferInstance inferInstance hFinite
  refine ⟨⟨inferInstance⟩, ?_⟩
  rw [exactFunctor_iff]
  constructor
  · apply (Functor.preservesFiniteLimits_tfae P.ι).out 2 3 |>.mp
    intro X Y f
    exact P.preservesKernels_ι f
  · apply (Functor.preservesFiniteColimits_tfae P.ι).out 2 3 |>.mp
    intro X Y f
    exact P.preservesCokernels_ι f

/- The class above is the source's nonempty full subcategory closed under
exact five-term sequences. -/

theorem weak_serre_subcategory_definition
    (P : ObjectProperty C) :
    P.IsWeakSerreClass ↔
      Nonempty P.FullSubcategory ∧
        ∀ (S : ComposableArrows C 4), S.Exact →
          P (S.obj' 0) → P (S.obj' 1) → P (S.obj' 3) → P (S.obj' 4) →
          P (S.obj' 2) := by
  constructor
  · intro h
    obtain ⟨X, hX⟩ := h.toNonempty.exists_prop
    refine ⟨⟨⟨X, hX⟩⟩, ?_⟩
    intro S hS h₀ h₁ h₃ h₄
    exact h.prop_X₂_of_exact hS h₀ h₁ h₃ h₄
  · rintro ⟨⟨X, hX⟩, hprop⟩
    refine @ObjectProperty.IsWeakSerreClass.mk C _ _ P ?_ ?_
    · exact ⟨X, hX⟩
    · exact fun {S} hS h₀ h₁ h₃ h₄ => hprop S hS h₀ h₁ h₃ h₄

theorem weak_serre_subcategory_is_nonempty_and_full
    (P : ObjectProperty C) [P.IsWeakSerreClass] :
    Nonempty P.FullSubcategory ∧ Nonempty P.ι.FullyFaithful := by
  exact ⟨inferInstance, ⟨P.fullyFaithfulι⟩⟩

theorem weak_serre_subcategory_characterization
    (P : ObjectProperty C) :
    P.IsWeakSerreClass ↔
      P (0 : C) ∧
        P.IsClosedUnderIsomorphisms ∧
          (P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels) ∧
            P.IsClosedUnderExtensions := by
  constructor
  · intro h
    obtain ⟨X, hX⟩ := h.toNonempty.exists_prop
    have hzero : P (0 : C) := by
      let T := ComposableArrows.mk₄ (𝟙 X) (0 : X ⟶ 0) (0 : 0 ⟶ X) (𝟙 X)
      have hT : T.Exact := by
        refine ComposableArrows.Exact.mk
          (ComposableArrows.IsComplex.mk (fun i hi => ?_)) ?_
        · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases hi' with rfl | rfl | rfl
          · change (𝟙 X) ≫ (0 : X ⟶ 0) = 0
            simp
          · change (0 : X ⟶ 0) ≫ (0 : 0 ⟶ X) = 0
            simp
          · change (0 : 0 ⟶ X) ≫ (𝟙 X) = 0
            simp
        · intro i hi
          have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases hi' with rfl | rfl | rfl
          · exact (ShortComplex.exact_iff_epi _ (by simp)).2 inferInstance
          · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
          · exact (ShortComplex.exact_iff_mono _ (by simp)).2 inferInstance
      exact h.prop_X₂_of_exact hT hX hX hX hX
    have hIso : P.IsClosedUnderIsomorphisms := by
      refine { of_iso := ?_ }
      intro X Y e hX
      let T := ComposableArrows.mk₄ (0 : (0 : C) ⟶ X) e.hom (0 : Y ⟶ (0 : C))
        (0 : (0 : C) ⟶ (0 : C))
      have hT : T.Exact := by
        refine ComposableArrows.Exact.mk
          (ComposableArrows.IsComplex.mk (fun i hi => ?_)) ?_
        · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases hi' with rfl | rfl | rfl
          · change (0 : (0 : C) ⟶ X) ≫ e.hom = 0
            simp
          · change e.hom ≫ (0 : Y ⟶ (0 : C)) = 0
            simp
          · change (0 : Y ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ (0 : C)) = 0
            simp
        · intro i hi
          have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases hi' with rfl | rfl | rfl
          · exact (ShortComplex.exact_iff_mono _ (by simp)).2 inferInstance
          · exact (ShortComplex.exact_iff_epi _ (by simp)).2 inferInstance
          · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
      exact h.prop_X₂_of_exact hT hzero hX hzero hzero
    have hK : P.IsClosedUnderKernels := by
      refine ⟨?_⟩
      intro Z hZ
      rcases hZ with ⟨f, k, hk, ⟨hX, hY⟩⟩
      exact P.prop_of_isLimit_kernelFork hk hX hY
    have hC : P.IsClosedUnderCokernels := by
      refine ⟨?_⟩
      intro Z hZ
      rcases hZ with ⟨f, k, hk, ⟨hX, hY⟩⟩
      exact P.prop_of_isColimit_cokernelCofork hk hX hY
    have hExt : P.IsClosedUnderExtensions := by
      refine ⟨?_⟩
      intro S hS h₁ h₃
      let T := ComposableArrows.mk₄ (0 : 0 ⟶ S.X₁) S.f S.g (0 : S.X₃ ⟶ 0)
      have hT : T.Exact := by
        refine ComposableArrows.Exact.mk
          (ComposableArrows.IsComplex.mk (fun i hi => ?_)) ?_
        · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases hi' with rfl | rfl | rfl
          · simp [T]
          · simpa [T] using hS.zero
          · simp [T]
        · intro i hi
          have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases hi' with rfl | rfl | rfl
          · exact (ShortComplex.exact_iff_mono _ (by simp)).2 hS.mono_f
          · simpa [T] using hS.exact
          · exact (ShortComplex.exact_iff_epi _ (by simp)).2 hS.epi_g
      exact h.prop_X₂_of_exact hT hzero h₁ h₃ hzero
    exact ⟨hzero, hIso, ⟨hK, hC⟩, hExt⟩
  · rintro ⟨hzero, hIso, ⟨hK, hC⟩, hExt⟩
    refine @ObjectProperty.IsWeakSerreClass.mk C _ _ P ?_ ?_
    · exact ⟨0, hzero⟩
    · intro S hS h₀ h₁ h₃ h₄
      letI : P.IsClosedUnderKernels := hK
      letI : P.IsClosedUnderCokernels := hC
      letI : P.IsClosedUnderExtensions := hExt
      let f₀ := S.map' 0 1
      let f₁ := S.map' 1 2
      let f₂ := S.map' 2 3
      let f₃ := S.map' 3 4
      let Q := cokernel f₀
      let K := kernel f₃
      let u := cokernel.desc f₀ f₁ (hS.toIsComplex.zero 0)
      let v := kernel.lift f₃ f₂ (hS.toIsComplex.zero 2)
      have hQ : P Q := P.prop_cokernel f₀ h₀ h₁
      have hK' : P K := P.prop_kernel f₃ h₃ h₄
      let T₁ : ShortComplex C := ShortComplex.mk u f₂ (by
        apply (cancel_epi (cokernel.π f₀)).1
        dsimp [u]
        rw [Category.assoc, cokernel.π_desc, hS.toIsComplex.zero 1])
      have hT₁ : T₁.Exact := by
        let φ : S.sc hS.toIsComplex 1 ⟶ T₁ := ShortComplex.homMk
          (cokernel.π f₀) (𝟙 _) (𝟙 _)
          (by dsimp [T₁, u]; simp)
          (by dsimp [T₁]; simp)
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (hS.exact 1)
      let T : ShortComplex C := ShortComplex.mk u v (by
        apply (cancel_mono (kernel.ι f₃)).1
        dsimp [v]
        rw [Category.assoc, kernel.lift_ι]
        apply (cancel_epi (cokernel.π f₀)).1
        dsimp [u]
        rw [Category.assoc, cokernel.π_desc, hS.toIsComplex.zero 1])
      have hT : T.Exact := by
        let φ : T ⟶ T₁ := ShortComplex.homMk
          (𝟙 _) (𝟙 _) (kernel.ι f₃)
          (by dsimp [T, T₁]; simp)
          (by dsimp [T, T₁, v]; simp)
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hT₁
      letI : Mono u := by
        dsimp [u]
        exact (hS.exact 0).mono_cokernelDesc
      letI : Epi v := by
        dsimp [v]
        exact (hS.exact 2).epi_kernelLift
      exact hExt.prop_X₂_of_shortExact (ShortComplex.ShortExact.mk' hT inferInstance inferInstance)
        hQ hK'
-/

theorem weak_serre_subcategory_is_abelian_and_inclusion_exact
    (P : ObjectProperty C) [P.IsWeakSerreClass] :
    Nonempty (Abelian P.FullSubcategory) ∧
      exactFunctor P.FullSubcategory C P.ι := by
  have hWeak : P.IsWeakSerreClass := inferInstance
  obtain ⟨X, hX⟩ := hWeak.toNonempty.exists_prop
  have hzero : P (0 : C) := by
    let T := ComposableArrows.mk₄ (𝟙 X) (0 : X ⟶ 0) (0 : 0 ⟶ X) (𝟙 X)
    have hT : T.Exact := by
      refine ComposableArrows.Exact.mk
        (ComposableArrows.IsComplex.mk (fun i hi => ?_)) ?_
      · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · change (𝟙 X) ≫ (0 : X ⟶ 0) = 0
          simp
        · change (0 : X ⟶ 0) ≫ (0 : 0 ⟶ X) = 0
          simp
        · change (0 : 0 ⟶ X) ≫ (𝟙 X) = 0
          simp
      · intro i hi
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · change (ShortComplex.mk (𝟙 X) (0 : X ⟶ 0) (by simp)).Exact
          exact (ShortComplex.exact_iff_epi _ rfl).2 inferInstance
        · dsimp [T]
          exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
        · change (ShortComplex.mk (0 : 0 ⟶ X) (𝟙 X) (by simp)).Exact
          exact (ShortComplex.exact_iff_mono _ rfl).2 inferInstance
    exact hWeak.prop_X₂_of_exact hT hX hX hX hX
  have hIso : P.IsClosedUnderIsomorphisms := by
    refine { of_iso := ?_ }
    intro X Y e hX
    let T := ComposableArrows.mk₄ (0 : (0 : C) ⟶ X) e.hom (0 : Y ⟶ (0 : C))
      (0 : (0 : C) ⟶ (0 : C))
    have hT : T.Exact := by
      refine ComposableArrows.Exact.mk
        (ComposableArrows.IsComplex.mk (fun i hi => ?_)) ?_
      · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · change (0 : (0 : C) ⟶ X) ≫ e.hom = 0
          simp
        · change e.hom ≫ (0 : Y ⟶ (0 : C)) = 0
          simp
        · change (0 : Y ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ (0 : C)) = 0
          simp
      · intro i hi
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · change (ShortComplex.mk (0 : (0 : C) ⟶ X) e.hom (by simp)).Exact
          exact (ShortComplex.exact_iff_mono _ rfl).2 inferInstance
        · change (ShortComplex.mk e.hom (0 : Y ⟶ (0 : C)) (by simp)).Exact
          exact (ShortComplex.exact_iff_epi _ rfl).2 inferInstance
        · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
    exact hWeak.prop_X₂_of_exact hT hzero hX hzero hzero
  have hK : P.IsClosedUnderKernels := by
    refine ⟨?_⟩
    intro Z hZ
    rcases hZ with ⟨f, k, hk, ⟨hX, hY⟩⟩
    let T := ComposableArrows.mk₄
      (0 : (0 : C) ⟶ (0 : C)) (0 : (0 : C) ⟶ k.pt) k.ι f
    have hT : T.Exact := by
      refine ComposableArrows.Exact.mk
        (ComposableArrows.IsComplex.mk (fun i hi => ?_)) ?_
      · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · change (0 : (0 : C) ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ k.pt) = 0
          simp
        · change (0 : (0 : C) ⟶ k.pt) ≫ k.ι = 0
          simp
        · change k.ι ≫ f = 0
          exact k.condition
      · intro i hi
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · change (ShortComplex.mk (0 : (0 : C) ⟶ (0 : C))
            (0 : (0 : C) ⟶ k.pt) (by simp)).Exact
          exact (ShortComplex.exact_iff_epi _ (by simp)).2 inferInstance
        · change (ShortComplex.mk (0 : (0 : C) ⟶ k.pt) k.ι (by simp)).Exact
          exact (ShortComplex.exact_iff_mono _ (by simp)).2 (Fork.IsLimit.mono hk)
        · change (ShortComplex.mk k.ι f k.condition).Exact
          exact ShortComplex.exact_of_f_is_kernel _
            (IsLimit.ofIsoLimit hk (Fork.ext (Iso.refl _)))
    exact hWeak.prop_X₂_of_exact hT hzero hzero hX hY
  have hC : P.IsClosedUnderCokernels := by
    refine ⟨?_⟩
    intro Z hZ
    rcases hZ with ⟨f, k, hk, ⟨hX, hY⟩⟩
    let T := ComposableArrows.mk₄ f k.π
      (0 : k.pt ⟶ (0 : C)) (0 : (0 : C) ⟶ (0 : C))
    have hT : T.Exact := by
      refine ComposableArrows.Exact.mk
        (ComposableArrows.IsComplex.mk (fun i hi => ?_)) ?_
      · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · change f ≫ k.π = 0
          exact k.condition
        · change k.π ≫ (0 : k.pt ⟶ (0 : C)) = 0
          simp
        · change (0 : k.pt ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ (0 : C)) = 0
          simp
      · intro i hi
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · change (ShortComplex.mk f k.π k.condition).Exact
          exact ShortComplex.exact_of_g_is_cokernel _
            (IsColimit.ofIsoColimit hk (Cofork.ext (Iso.refl _)))
        · change (ShortComplex.mk k.π (0 : k.pt ⟶ (0 : C)) (by simp)).Exact
          letI : Epi k.π := Cofork.IsColimit.epi hk
          exact (ShortComplex.exact_iff_epi _ (by simp)).2 inferInstance
        · change (ShortComplex.mk (0 : k.pt ⟶ (0 : C))
            (0 : (0 : C) ⟶ (0 : C)) (by simp)).Exact
          exact (ShortComplex.exact_iff_epi _ (by simp)).2 inferInstance
    exact hWeak.prop_X₂_of_exact hT hX hY hzero hzero
  have hExt : P.IsClosedUnderExtensions := by
    refine ⟨?_⟩
    intro S hS h₁ h₃
    let T := ComposableArrows.mk₄ (0 : 0 ⟶ S.X₁) S.f S.g (0 : S.X₃ ⟶ 0)
    have hT : T.Exact := by
      refine ComposableArrows.Exact.mk
        (ComposableArrows.IsComplex.mk (fun i hi => ?_)) ?_
      · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · change (0 : (0 : C) ⟶ S.X₁) ≫ S.f = 0
          simp
        · change S.f ≫ S.g = 0
          exact S.zero
        · change S.g ≫ (0 : S.X₃ ⟶ (0 : C)) = 0
          simp
      · intro i hi
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · change (ShortComplex.mk (0 : (0 : C) ⟶ S.X₁) S.f (by simp)).Exact
          exact (ShortComplex.exact_iff_mono _ rfl).2 hS.mono_f
        · change (ShortComplex.mk S.f S.g S.zero).Exact
          exact hS.exact
        · exact (ShortComplex.exact_iff_epi _
            (by change (0 : S.X₃ ⟶ (0 : C)) = 0; simp)).2 hS.epi_g
    exact hWeak.prop_X₂_of_exact hT hzero h₁ h₃ hzero
  let _ : P.ContainsZero := ⟨⟨0, isZero_zero C, hzero⟩⟩
  let _ : P.IsClosedUnderIsomorphisms := hIso
  let _ : P.IsClosedUnderKernels := hK
  let _ : P.IsClosedUnderCokernels := hC
  let _ : P.IsClosedUnderExtensions := hExt
  have hBin : P.IsClosedUnderBinaryProducts :=
    ObjectProperty.IsClosedUnderLimitsOfShape.mk' (P := P)
      (J := Discrete WalkingPair) (by
        rintro _ ⟨F, hF⟩
        exact P.prop_of_iso
          (IsLimit.conePointsIsoOfNatIso (BinaryBiproduct.isLimit _ _)
            (limit.isLimit F) (diagramIsoPair F).symm)
          (P.prop_biprod (hF _) (hF _)))
  have hFinite : P.IsClosedUnderFiniteProducts :=
    @ObjectProperty.IsClosedUnderFiniteProducts.mk' C _ P inferInstance inferInstance hBin
  let _ : Abelian P.FullSubcategory := inferInstance
  refine ⟨⟨inferInstance⟩, ?_⟩
  rw [exactFunctor_iff]
  constructor
  · apply (Functor.preservesFiniteLimits_tfae P.ι).out 2 3 |>.mp
    intro X Y f
    exact P.preservesKernels_ι f
  · apply (Functor.preservesFiniteColimits_tfae P.ι).out 2 3 |>.mp
    intro X Y f
    exact P.preservesCokernels_ι f

/-! ## Kernels of exact functors -/

theorem exact_functor_kernel_is_serre_subcategory
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ₑ D) :
    (Functor.kernel F.obj).IsSerreClass := by
  infer_instance

/- The source's `Ker(F)` is the full subcategory associated to Mathlib's
canonical object property `Functor.kernel F`. -/
abbrev kernelCategory
    {D : Type u'} [Category.{v'} D]
    [Abelian D] (F : C ⥤ₑ D) : Type u :=
  (Functor.kernel F.obj).FullSubcategory

/-! ## The Serre quotient -/

abbrev serreQuotient (P : ObjectProperty C) [P.IsSerreClass] :=
  P.isoModSerre.Localization

noncomputable abbrev serreQuotientFunctor
    (P : ObjectProperty C) [P.IsSerreClass] :
    C ⥤ serreQuotient P :=
  P.isoModSerre.Q

@[instance_reducible]
noncomputable def serreQuotientAbelian
    (P : ObjectProperty C) [P.IsSerreClass] :
    Abelian (serreQuotient P) :=
  ObjectProperty.SerreClassLocalization.abelian
    (serreQuotientFunctor P) P

noncomputable def serreQuotientExactFunctor
    (P : ObjectProperty C) [P.IsSerreClass] :
    C ⥤ₑ serreQuotient P := by
  letI : PreservesFiniteLimits (serreQuotientFunctor P) :=
    ObjectProperty.SerreClassLocalization.preservesFiniteLimits
      (serreQuotientFunctor P) P
  letI : PreservesFiniteColimits (serreQuotientFunctor P) :=
    ObjectProperty.SerreClassLocalization.preservesFiniteColimits
      (serreQuotientFunctor P) P
  exact ExactFunctor.of (serreQuotientFunctor P)

theorem serre_quotient_is_abelian_exact_essentially_surjective
    (P : ObjectProperty C) [P.IsSerreClass] :
    Nonempty (Abelian (serreQuotient P)) ∧
      exactFunctor C (serreQuotient P) (serreQuotientFunctor P) ∧
        (serreQuotientFunctor P).EssSurj ∧
          Functor.kernel (serreQuotientFunctor P) = P := by
  refine ⟨⟨serreQuotientAbelian P⟩, (serreQuotientExactFunctor P).property, ?_, ?_⟩
  · exact Localization.essSurj (serreQuotientFunctor P) P.isoModSerre
  · ext X
    exact ObjectProperty.SerreClassLocalization.isZero_obj_iff
      (serreQuotientFunctor P) P X

/- The source's universal property is stated using exact functors as objects
of Mathlib's bundled `ExactFunctor` category. -/
theorem serre_quotient_universal_property
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (P : ObjectProperty C) [P.IsSerreClass]
    (G : C ⥤ₑ D) (hG : P ≤ Functor.kernel G.obj) :
    ∃! H : serreQuotient P ⥤ₑ D,
      serreQuotientFunctor P ⋙ H.obj = G.obj := by
  letI : PreservesFiniteLimits G.obj := G.property.1
  letI : PreservesFiniteColimits G.obj := G.property.2
  letI : PreservesFiniteLimits (serreQuotientFunctor P) :=
    ObjectProperty.SerreClassLocalization.preservesFiniteLimits
      (serreQuotientFunctor P) P
  letI : PreservesFiniteColimits (serreQuotientFunctor P) :=
    ObjectProperty.SerreClassLocalization.preservesFiniteColimits
      (serreQuotientFunctor P) P
  have hInv : P.isoModSerre.IsInvertedBy G.obj :=
    (ObjectProperty.isoModSerre_isInvertedBy_iff P G.obj).2 hG
  let H₀ : serreQuotient P ⥤ D :=
    Localization.Construction.lift G.obj hInv
  have hH₀ : exactFunctor (serreQuotient P) D H₀ := by
    apply (ObjectProperty.SerreClassLocalization.exactFunctor_comp_iff
      (serreQuotientFunctor P) P H₀).mp
    dsimp [H₀, serreQuotientFunctor, serreQuotient]
    rw [Localization.Construction.fac]
    exact G.property
  let H : serreQuotient P ⥤ₑ D := ⟨H₀, hH₀⟩
  refine ⟨H, ?_, ?_⟩
  · change serreQuotientFunctor P ⋙ H₀ = G.obj
    simpa [H₀, serreQuotientFunctor, serreQuotient] using
      (Localization.Construction.fac G.obj hInv)
  · intro H₁ h
    apply ObjectProperty.FullSubcategory.ext
    apply Localization.Construction.uniq
    have hFac : serreQuotientFunctor P ⋙ H.obj = G.obj := by
      change serreQuotientFunctor P ⋙ H₀ = G.obj
      simpa [H₀, serreQuotientFunctor, serreQuotient] using
        (Localization.Construction.fac G.obj hInv)
    exact h.trans hFac.symm

noncomputable def inducedSerreQuotientFunctor
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (P : ObjectProperty C) [P.IsSerreClass]
    (G : C ⥤ₑ D) (hG : P ≤ Functor.kernel G.obj) :
    serreQuotient P ⥤ₑ D :=
  (serre_quotient_universal_property P G hG).choose

theorem inducedSerreQuotientFunctor_fac
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (P : ObjectProperty C) [P.IsSerreClass]
    (G : C ⥤ₑ D) (hG : P ≤ Functor.kernel G.obj) :
    serreQuotientFunctor P ⋙ (inducedSerreQuotientFunctor P G hG).obj = G.obj :=
  (serre_quotient_universal_property P G hG).choose_spec.1

/-! ## Faithfulness of the induced functor -/

theorem quotient_by_kernel_exact_functor_iff_faithful
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (P : ObjectProperty C) [P.IsSerreClass]
    (G : C ⥤ₑ D) (hG : P ≤ Functor.kernel G.obj) :
    P = Functor.kernel G.obj ↔
      (inducedSerreQuotientFunctor P G hG).obj.Faithful := by
  letI : Abelian (serreQuotient P) := serreQuotientAbelian P
  letI : PreservesFiniteLimits G.obj := G.property.1
  letI : PreservesFiniteColimits G.obj := G.property.2
  constructor
  · intro hEq
    letI : (inducedSerreQuotientFunctor P G hG).obj.Additive :=
      (exactFunctor_le_additiveFunctor (serreQuotient P) D)
        _ (inducedSerreQuotientFunctor P G hG).property
    apply Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions
      (L := serreQuotientFunctor P) (W := P.isoModSerre)
      (inducedSerreQuotientFunctor P G hG).obj
    intro X Y f hf
    have hGmap : G.obj.map f = 0 := by
      rw [← inducedSerreQuotientFunctor_fac P G hG]
      simpa using hf
    have hPimg : P (Abelian.image f) := by
      rw [hEq]
      have hGι : G.obj.map (Abelian.image.ι f) = 0 := by
        apply (cancel_epi (G.obj.map (Abelian.factorThruImage f))).1
        rw [← G.obj.map_comp, Abelian.image.fac, hGmap]
        simp
      have hKzero : IsZero (kernel (G.obj.map (Abelian.image.ι f))) :=
        isZero_kernel_of_mono _
      have hIso : kernel (G.obj.map (Abelian.image.ι f)) ≅
          G.obj.obj (Abelian.image f) :=
        kernelIsoOfEq hGι ≪≫ kernelZeroIsoSource
      exact hKzero.of_iso hIso.symm
    exact (ObjectProperty.SerreClassLocalization.map_eq_zero_iff
      (serreQuotientFunctor P) P f).2 hPimg
  · intro hF
    letI : (inducedSerreQuotientFunctor P G hG).obj.Faithful := hF
    apply le_antisymm hG
    intro X hX
    have hHX : IsZero ((inducedSerreQuotientFunctor P G hG).obj.obj
        ((serreQuotientFunctor P).obj X)) := by
      change IsZero ((serreQuotientFunctor P ⋙
        (inducedSerreQuotientFunctor P G hG).obj).obj X)
      rw [inducedSerreQuotientFunctor_fac P G hG]
      exact hX
    have hId : (inducedSerreQuotientFunctor P G hG).obj.map
        (𝟙 ((serreQuotientFunctor P).obj X)) = 0 := by
      rw [(inducedSerreQuotientFunctor P G hG).obj.map_id]
      exact hHX.eq_of_src _ _
    have hId' : (𝟙 ((serreQuotientFunctor P).obj X)) = 0 := by
      apply (inducedSerreQuotientFunctor P G hG).obj.map_injective
      simpa using hId
    exact (ObjectProperty.SerreClassLocalization.isZero_obj_iff
      (serreQuotientFunctor P) P X).1
      ((IsZero.iff_id_eq_zero ((serreQuotientFunctor P).obj X)).2 hId')

end Formalization.Books.Homology.Unit10
