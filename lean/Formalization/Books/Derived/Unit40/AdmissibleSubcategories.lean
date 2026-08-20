import Formalization.Books.Derived.Unit06.Quotients
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Derived Categories, Chapter 40: admissible subcategories

The source's full subcategories are represented by Mathlib's canonical
`ObjectProperty` interface.  Orthogonals, distinguished decomposition
triangles, adjunctions of inclusions, and Verdier quotient functors are kept
as explicit source-facing predicates and interfaces below.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit04
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit03
open Formalization.Books.Homology.Unit03

universe v u

namespace Formalization.Books.Derived.Unit40

section AdmissibleSubcategories

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-! ## Orthogonals and distinguished decompositions -/

/- A full subcategory is represented by an object property; its canonical
   full subcategory is `P.FullSubcategory`. -/

/- The source's notation `Hom(X, Y) = 0` is represented by the established
   `HomIsZero` predicate, namely that every morphism from `X` to `Y` is zero. -/

/-- The right orthogonal of a full subcategory. -/
def rightOrthogonal (P : ObjectProperty C) : ObjectProperty C :=
  fun X => ∀ (A : C), P A → HomIsZero A X

/-- The left orthogonal of a full subcategory. -/
def leftOrthogonal (P : ObjectProperty C) : ObjectProperty C :=
  fun X => ∀ (A : C), P A → HomIsZero X A

/-- A distinguished triangle decomposing `X` into a `P`-part and a `Q`-part. -/
def HasTriangleDecomposition
    (P Q : ObjectProperty C) (X : C) : Prop :=
  ∃ (A B : C) (f : A ⟶ X) (g : X ⟶ B)
    (h : B ⟶ A⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C ∧ P A ∧ Q B

/-- A distinguished triangle of the form used for a right adjoint. -/
def HasRightDecomposition (P : ObjectProperty C) (X : C) : Prop :=
  HasTriangleDecomposition P (rightOrthogonal P) X

/-- A distinguished triangle of the form used for a left adjoint. -/
def HasLeftDecomposition (P : ObjectProperty C) (X : C) : Prop :=
  HasTriangleDecomposition (leftOrthogonal P) P X

/-! ## The two preliminary orthogonality lemmas -/

/-- The right-orthogonality criterion for a distinguished triangle.

The map in the second condition is the map induced by the first arrow of
the triangle on representable morphism spaces. -/
theorem pre_prepare_adjoint
    (P : ObjectProperty C) (hP : P.IsStableUnderShift ℤ)
    [CategoryTheory.IsTriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) :
    rightOrthogonal P T.obj₃ ↔
      ∀ (A : C), P A →
        Function.Bijective (fun f : A ⟶ T.obj₁ => f ≫ T.mor₁) := by
  constructor
  · intro h A hA
    constructor
    · intro f g hfg
      have hk : (f - g) ≫ T.mor₁ = 0 := by
        rw [sub_comp, sub_eq_zero]
        exact hfg
      obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₁ T hT
        ((f - g)⟦(1 : ℤ)⟧')
        (by
          rw [← Functor.map_comp]
          simpa only [Functor.map_zero] using congrArg (fun k => k⟦(1 : ℤ)⟧') hk)
      have hAshift : P (A⟦(1 : ℤ)⟧) := by
        exact (hP.isStableUnderShiftBy (1 : ℤ)).le_shift _ hA
      have hq0 : q = 0 :=
        h (A⟦(1 : ℤ)⟧) hAshift q
      have hshift : (f - g)⟦(1 : ℤ)⟧' = 0 := by
        rw [hq, hq0]
        simp
      apply sub_eq_zero.mp
      apply (Functor.map_injective (shiftFunctor C (1 : ℤ)))
      simpa only [Functor.map_zero] using hshift
    · intro g
      obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ T hT g (by
        exact h _ hA (g ≫ T.mor₂))
      exact ⟨q, hq.symm⟩
  · intro h A hA f
    let e := shiftEquiv C (1 : ℤ)
    let adj := e.symm.toAdjunction
    let k : A ⟶ e.functor.obj T.obj₁ := f ≫ T.mor₃
    have hk : k ≫ e.symm.inverse.map T.mor₁ = 0 := by
      change (f ≫ T.mor₃) ≫ (shiftFunctor C (1 : ℤ)).map T.mor₁ = 0
      rw [Category.assoc, comp_distTriang_mor_zero₃₁ _ hT, comp_zero]
    let q := (adj.homEquiv A T.obj₁).symm k
    have hq : q ≫ T.mor₁ = 0 := by
      dsimp [q]
      rw [← adj.homEquiv_naturality_right_symm k T.mor₁, hk]
      simp [Adjunction.homEquiv_counit]
    have hAshift : P (e.symm.functor.obj A) := by
      change P (A⟦(-1 : ℤ)⟧)
      exact (hP.isStableUnderShiftBy (-1 : ℤ)).le_shift _ hA
    have hq0 : q = 0 := by
      apply (h (e.symm.functor.obj A) hAshift).1
      change q ≫ T.mor₁ = 0 ≫ T.mor₁
      rw [hq, zero_comp]
    have hk0 : k = 0 := by
      change (adj.homEquiv A T.obj₁).symm k = 0 at hq0
      have hq0' := congrArg (adj.homEquiv A T.obj₁) hq0
      simpa [Adjunction.homEquiv_unit] using hq0'
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ T hT f hk0
    obtain ⟨q', hq'⟩ := (h A hA).2 g
    rw [hg, ← hq', Category.assoc, comp_distTriang_mor_zero₁₂ _ hT, comp_zero]

/-- The left-orthogonality criterion dual to `pre_prepare_adjoint`. -/
theorem pre_prepare_adjoint_dual
    (P : ObjectProperty C) (hP : P.IsStableUnderShift ℤ)
    [CategoryTheory.IsTriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) :
    leftOrthogonal P T.obj₁ ↔
      ∀ (B : C), P B →
        Function.Bijective (fun f : T.obj₃ ⟶ B => T.mor₂ ≫ f) := by
  constructor
  · intro h B hB
    constructor
    · intro f g hfg
      have hk : T.mor₂ ≫ (f - g) = 0 := by
        rw [comp_sub, sub_eq_zero]
        exact hfg
      obtain ⟨q, hq⟩ := Triangle.yoneda_exact₃ T hT (f - g) hk
      let e := shiftEquiv C (1 : ℤ)
      let adj := e.toAdjunction
      let : e.functor.Additive := by
        change (shiftFunctor C (1 : ℤ)).Additive
        infer_instance
      have hBshift : P (e.inverse.obj B) := by
        change P (B⟦(-1 : ℤ)⟧)
        exact (hP.isStableUnderShiftBy (-1 : ℤ)).le_shift _ hB
      have hq0 : q = 0 := by
        let q' : e.functor.obj T.obj₁ ⟶ B := q
        have hq0' : q' = 0 := by
          apply (adj.homEquiv T.obj₁ B).injective
          have hq' : (adj.homEquiv T.obj₁ B) q' = 0 :=
            h (e.inverse.obj B) hBshift (adj.homEquiv T.obj₁ B q')
          rw [hq']
          exact (adj.homAddEquiv_zero T.obj₁ B).symm
        change q' = 0
        exact hq0'
      apply sub_eq_zero.mp
      rw [hq, hq0]
      simp
    · intro g
      obtain ⟨f, hf⟩ := Triangle.yoneda_exact₂ T hT g (by
        exact h B hB (T.mor₁ ≫ g))
      exact ⟨f, hf.symm⟩
  · intro h B hB f
    let e := shiftEquiv C (1 : ℤ)
    let adj := e.symm.toAdjunction
    let : e.symm.functor.Additive := by
      change (shiftFunctor C (-1 : ℤ)).Additive
      infer_instance
    let r : e.symm.functor.obj T.obj₃ ⟶ B := by
      change T.invRotate.obj₁ ⟶ B
      exact T.invRotate.mor₁ ≫ f
    have hr : e.symm.functor.map T.mor₂ ≫ r = 0 := by
      dsimp [r, e]
      change (shiftFunctor C (-1)).map T.mor₂ ≫
        (T.invRotate.mor₁ ≫ f) = 0
      dsimp [Triangle.invRotate, shiftEquiv, shiftEquiv']
      change (shiftFunctor C (-1)).map T.mor₂ ≫
        (-(shiftFunctor C (-1)).map T.mor₃ ≫
          (shiftFunctorCompIsoId C 1 (-1) (add_neg_cancel 1)).hom.app T.obj₁) ≫ f = 0
      rw [← Category.assoc, comp_neg, ← Category.assoc, ← Functor.map_comp,
        comp_distTriang_mor_zero₂₃ _ hT]
      simp
    let q := adj.homEquiv T.obj₃ B r
    have hq : T.mor₂ ≫ q = 0 := by
      dsimp [q]
      rw [← adj.homEquiv_naturality_left, hr]
      rw [Adjunction.homEquiv_unit]
      simp
    have hBshift : P (e.functor.obj B) := by
      change P (B⟦(1 : ℤ)⟧)
      exact (hP.isStableUnderShiftBy (1 : ℤ)).le_shift _ hB
    have hq0 : q = 0 := by
      apply (h (e.functor.obj B) hBshift).1
      change T.mor₂ ≫ q = T.mor₂ ≫ 0
      rw [hq, comp_zero]
    have hr0 : r = 0 := by
      apply (adj.homEquiv T.obj₃ B).injective
      change q = (adj.homEquiv T.obj₃ B) 0
      rw [hq0]
      exact (adj.homAddEquiv_zero T.obj₃ B).symm
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T.invRotate
      (inv_rot_of_distTriang _ hT) f (by
        change r = 0
        exact hr0)
    obtain ⟨s, hs⟩ := (h B hB).2 g
    rw [hg, ← hs]
    change T.mor₁ ≫ (T.mor₂ ≫ s) = 0
    rw [← Category.assoc, comp_distTriang_mor_zero₁₂ _ hT, zero_comp]

/-! ## Orthogonals are triangulated and saturated -/

/-- Both orthogonals are strictly full, saturated, and triangulated. -/
theorem orthogonal_triangulated
    (P : ObjectProperty C) (hP : P.IsStableUnderShift ℤ)
    [CategoryTheory.IsTriangulated C] :
    ((rightOrthogonal P).IsClosedUnderIsomorphisms ∧
        IsSaturated (rightOrthogonal P) ∧
        (rightOrthogonal P).IsTriangulated) ∧
      ((leftOrthogonal P).IsClosedUnderIsomorphisms ∧
        IsSaturated (leftOrthogonal P) ∧
        (leftOrthogonal P).IsTriangulated) := by
  have hP' : P.IsStableUnderShift ℤ := hP
  have hright : rightOrthogonal P = ObjectProperty.rightOrthogonal P := by
    ext X
    constructor
    · intro h A f hA
      exact h A hA f
    · intro h A hA f
      exact h f hA
  have hleft : leftOrthogonal P = ObjectProperty.leftOrthogonal P := by
    ext X
    constructor
    · intro h A f hA
      exact h A hA f
    · intro h A hA f
      exact h f hA
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · rw [hright]
      let : P.IsStableUnderShift ℤ := hP'
      infer_instance
    · intro X Y hXY
      have hsum : rightOrthogonal P (X ⊞ Y) := by
        obtain ⟨Z, hZ, ⟨e⟩⟩ := hXY
        rw [hright] at hZ ⊢
        exact ObjectProperty.prop_of_iso (P := ObjectProperty.rightOrthogonal P) e.symm hZ
      constructor
      · apply ObjectProperty.le_isoClosure
        intro A hA f
        have hf := hsum A hA (f ≫ biprod.inl)
        simpa only [Category.assoc, biprod.inl_fst, Category.comp_id, zero_comp] using
          congrArg (fun k => k ≫ biprod.fst) hf
      · apply ObjectProperty.le_isoClosure
        intro A hA f
        have hf := hsum A hA (f ≫ biprod.inr)
        simpa only [Category.assoc, biprod.inr_snd, Category.comp_id, zero_comp] using
          congrArg (fun k => k ≫ biprod.snd) hf
    · rw [hright]
      let : P.IsStableUnderShift ℤ := hP'
      infer_instance
  · refine ⟨?_, ?_, ?_⟩
    · rw [hleft]
      let : P.IsStableUnderShift ℤ := hP'
      infer_instance
    · intro X Y hXY
      have hsum : leftOrthogonal P (X ⊞ Y) := by
        obtain ⟨Z, hZ, ⟨e⟩⟩ := hXY
        rw [hleft] at hZ ⊢
        exact ObjectProperty.prop_of_iso (P := ObjectProperty.leftOrthogonal P) e.symm hZ
      constructor
      · apply ObjectProperty.le_isoClosure
        intro A hA f
        have hf := hsum A hA (biprod.fst ≫ f)
        simpa only [biprod.inl_fst_assoc, Category.comp_id, comp_zero] using
          congrArg (fun k => biprod.inl ≫ k) hf
      · apply ObjectProperty.le_isoClosure
        intro A hA f
        have hf := hsum A hA (biprod.snd ≫ f)
        simpa only [biprod.inr_snd_assoc, Category.comp_id, comp_zero] using
          congrArg (fun k => biprod.inr ≫ k) hf
    · rw [hleft]
      let : P.IsStableUnderShift ℤ := hP'
      infer_instance

/-! ## Closure of adjoint decompositions -/

/-- Right-adjoint decompositions satisfy two-out-of-three for triangles. -/
theorem prepare_adjoint_two_out_of_three
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) :
    (HasRightDecomposition P T.obj₁ ∧
        HasRightDecomposition P T.obj₂ →
          HasRightDecomposition P T.obj₃) ∧
      (HasRightDecomposition P T.obj₁ ∧
        HasRightDecomposition P T.obj₃ →
          HasRightDecomposition P T.obj₂) ∧
      (HasRightDecomposition P T.obj₂ ∧
        HasRightDecomposition P T.obj₃ →
          HasRightDecomposition P T.obj₁) := by
  let hP : P.IsStableUnderShift ℤ := inferInstance
  have horth := orthogonal_triangulated P hP
  let _rightClosed : (rightOrthogonal P).IsClosedUnderIsomorphisms := horth.1.1
  let _rightTriangulated : (rightOrthogonal P).IsTriangulated := horth.1.2.2
  have transfer_right
      {A X B B' : C} {f : A ⟶ X}
      {g : X ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
      {g' : X ⟶ B'} {h' : B' ⟶ A⟦(1 : ℤ)⟧}
      (hD : Triangle.mk f g h ∈ distTriang C)
      (hD' : Triangle.mk f g' h' ∈ distTriang C)
      (hB : rightOrthogonal P B) : rightOrthogonal P B' := by
    obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk f g h) (Triangle.mk f g' h') hD hD' (𝟙 _) (𝟙 _) (by
        change f ≫ 𝟙 X = 𝟙 A ≫ f
        simp)
    let φ := Triangle.homMk (Triangle.mk f g h) (Triangle.mk f g' h')
      (𝟙 A) (𝟙 X) c (by
        change f ≫ 𝟙 X = 𝟙 A ≫ f
        simp) hc₂ hc₃
    let _ : IsIso φ.hom₁ := by
      change IsIso (𝟙 A)
      infer_instance
    let _ : IsIso φ.hom₂ := by
      change IsIso (𝟙 X)
      infer_instance
    have hc : IsIso c := by
      change IsIso φ.hom₃
      apply isIso₃_of_isIso₁₂ φ hD hD'
      · exact inferInstance
      · exact inferInstance
    exact (rightOrthogonal P).prop_of_iso (@asIso _ _ _ _ c hc) hB
  have shift_right :
      ∀ {X : C}, HasRightDecomposition P X →
        ∀ n : ℤ, HasRightDecomposition P (X⟦n⟧) := by
    intro X hX n
    rcases hX with ⟨A, B, f, g, h, hD, hA, hB⟩
    let D := (Triangle.shiftFunctor C n).obj (Triangle.mk f g h)
    refine ⟨D.obj₁, D.obj₃, D.mor₁, D.mor₂, D.mor₃, ?_, ?_, ?_⟩
    · change D ∈ distTriang C
      exact Triangle.shift_distinguished (Triangle.mk f g h) hD n
    · change P (A⟦n⟧)
      exact (hP.isStableUnderShiftBy n).le_shift _ hA
    · change rightOrthogonal P (B⟦n⟧)
      exact ((inferInstance : (rightOrthogonal P).IsStableUnderShift ℤ).isStableUnderShiftBy n).le_shift _ hB
  have iso_right {X Y : C} (e : X ≅ Y) (hX : HasRightDecomposition P X) :
      HasRightDecomposition P Y := by
    rcases hX with ⟨A, B, f, g, h, hD, hA, hB⟩
    refine ⟨A, B, f ≫ e.hom, e.inv ≫ g, h, ?_, hA, hB⟩
    exact isomorphic_distinguished _ hD _
      (Triangle.isoMk _ _ (Iso.refl A) e.symm (Iso.refl B)
        (by
          change (f ≫ e.hom) ≫ e.inv = 𝟙 A ≫ f
          simp)
        (by
          change (e.inv ≫ g) ≫ 𝟙 B = e.inv ≫ g
          simp)
        (by
          change h ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 A) = 𝟙 B ≫ h
          simp))
  have first_case :
      ∀ {S : Triangle C}, S ∈ distTriang C →
        HasRightDecomposition P S.obj₁ →
        HasRightDecomposition P S.obj₂ →
        HasRightDecomposition P S.obj₃ := by
    intro S hS hS₁ hS₂
    rcases hS₁ with ⟨A₁, B₁, f₁, g₁, h₁, hD₁, hA₁, hB₁⟩
    rcases hS₂ with ⟨A₂, B₂, f₂, g₂, h₂, hD₂, hA₂, hB₂⟩
    have ha' := (((pre_prepare_adjoint P hP hD₂).1 hB₂ A₁ hA₁).2
      (f₁ ≫ S.mor₁))
    change ∃ a : A₁ ⟶ A₂, a ≫ f₂ = f₁ ≫ S.mor₁ at ha'
    obtain ⟨a, ha⟩ := ha'
    obtain ⟨d⟩ := three_by_three_completion f₁ f₂ a S.mor₁ ha.symm
    have hB₀ : rightOrthogonal P d.Z :=
      transfer_right hD₁ d.row₀ hB₁
    have hB₁' : rightOrthogonal P d.Z' :=
      transfer_right hD₂ d.row₁ hB₂
    obtain ⟨A₃, hA₃, ⟨eA⟩⟩ :=
      P.ext_of_isTriangulatedClosed₃' (Triangle.mk a d.a' d.a'') d.col₀ hA₁ hA₂
    have eA' : d.X'' ≅ A₃ := by
      simpa using eA
    have hB₃ : rightOrthogonal P d.Z'' :=
      (rightOrthogonal P).ext_of_isTriangulatedClosed₃
        (Triangle.mk d.c d.c' d.c'') d.col₂ hB₀ hB₁'
    have hD₃ : Triangle.mk (eA'.inv ≫ d.f'') d.g''
        (d.h'' ≫ eA'.hom⟦(1 : ℤ)⟧') ∈ distTriang C := by
      let U : Triangle C :=
        { obj₁ := A₃
          obj₂ := d.Y''
          obj₃ := d.Z''
          mor₁ := eA'.inv ≫ d.f''
          mor₂ := d.g''
          mor₃ := d.h'' ≫ eA'.hom⟦(1 : ℤ)⟧' }
      let V : Triangle C :=
        { obj₁ := d.X''
          obj₂ := d.Y''
          obj₃ := d.Z''
          mor₁ := d.f''
          mor₂ := d.g''
          mor₃ := d.h'' }
      have hV : V ∈ distTriang C := by
        simpa [V, Triangle.mk] using d.row₂
      have hU : U ∈ distTriang C := by
        exact isomorphic_distinguished V hV U
          (Triangle.isoMk U V eA'.symm (Iso.refl d.Y'') (Iso.refl d.Z'')
            (by simp [U, V])
            (by simp [U, V])
            (by
              simp only [U, V, Category.assoc, Iso.refl_hom, Category.id_comp]
              rw [← Functor.map_comp]
              simp))
      simpa [U, Triangle.mk] using hU
    have hY : HasRightDecomposition P d.Y'' :=
      ⟨A₃, d.Z'', eA'.inv ≫ d.f'', d.g'', d.h'' ≫ eA'.hom⟦(1 : ℤ)⟧',
        hD₃, hA₃, hB₃⟩
    obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk S.mor₁ d.b' d.b'') S d.col₁ hS (𝟙 S.obj₁) (𝟙 S.obj₂) (by
        change S.mor₁ ≫ 𝟙 S.obj₂ = 𝟙 S.obj₁ ≫ S.mor₁
        simp)
    let φ := Triangle.homMk (Triangle.mk S.mor₁ d.b' d.b'') S
      (𝟙 S.obj₁) (𝟙 S.obj₂) c (by
        change S.mor₁ ≫ 𝟙 S.obj₂ = 𝟙 S.obj₁ ≫ S.mor₁
        simp) hc₂ hc₃
    let _ : IsIso φ.hom₁ := by
      change IsIso (𝟙 S.obj₁)
      infer_instance
    let _ : IsIso φ.hom₂ := by
      change IsIso (𝟙 S.obj₂)
      infer_instance
    let _ : IsIso c := by
      change IsIso φ.hom₃
      exact isIso₃_of_isIso₁₂ φ d.col₁ hS inferInstance inferInstance
    exact iso_right (asIso c) hY
  constructor
  · intro h₁₂
    exact first_case hT h₁₂.1 h₁₂.2
  constructor
  · intro h₁₃
    exact first_case (inv_rot_of_distTriang _ hT)
      (shift_right h₁₃.2 (-1 : ℤ)) h₁₃.1
  · intro h₂₃
    apply iso_right (shiftShiftNeg T.obj₁ (1 : ℤ))
    exact shift_right (first_case (rot_of_distTriang _ hT) h₂₃.1 h₂₃.2) (-1 : ℤ)
/-
  let hP : P.IsStableUnderShift ℤ := inferInstance
  have horth := orthogonal_triangulated P hP
  letI : (rightOrthogonal P).IsClosedUnderIsomorphisms := horth.1.1
  letI : (rightOrthogonal P).IsTriangulated := horth.1.2.2
  have transfer_right
      {A X B B' : C} {f : A ⟶ X}
      {g : X ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
      {g' : X ⟶ B'} {h' : B' ⟶ A⟦(1 : ℤ)⟧}
      (hD : Triangle.mk f g h ∈ distTriang C)
      (hD' : Triangle.mk f g' h' ∈ distTriang C)
      (hB : rightOrthogonal P B) : rightOrthogonal P B' := by
    obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk f g h) (Triangle.mk f g' h') hD hD' (𝟙 _) (𝟙 _) (by
        change f ≫ 𝟙 X = 𝟙 A ≫ f
        simp)
    let φ := Triangle.homMk (Triangle.mk f g h) (Triangle.mk f g' h')
      (𝟙 A) (𝟙 X) c (by
        change f ≫ 𝟙 X = 𝟙 A ≫ f
        simp) hc₂ hc₃
    haveI : IsIso φ.hom₁ := by
      change IsIso (𝟙 A)
      infer_instance
    haveI : IsIso φ.hom₂ := by
      change IsIso (𝟙 X)
      infer_instance
    have hc : IsIso c := by
      change IsIso φ.hom₃
      apply isIso₃_of_isIso₁₂ φ hD hD'
      · exact inferInstance
      · exact inferInstance
    letI : IsIso c := hc
    exact (rightOrthogonal P).prop_of_iso (@asIso _ _ _ _ c hc) hB
  have first_case :
      ∀ {S : Triangle C}, S ∈ distTriang C →
        HasRightDecomposition P S.obj₁ →
        HasRightDecomposition P S.obj₂ →
        HasRightDecomposition P S.obj₃ := by
    intro S hS hS₁ hS₂
    rcases hS₁ with ⟨A₁, B₁, f₁, g₁, h₁, hD₁, hA₁, hB₁⟩
    rcases hS₂ with ⟨A₂, B₂, f₂, g₂, h₂, hD₂, hA₂, hB₂⟩
    have ha' := (((pre_prepare_adjoint P hP hD₂).1 hB₂ A₁ hA₁).2
      (f₁ ≫ S.mor₁))
    change ∃ a : A₁ ⟶ A₂, a ≫ f₂ = f₁ ≫ S.mor₁ at ha'
    obtain ⟨a, ha⟩ := ha'
    obtain ⟨d⟩ := three_by_three_completion f₁ f₂ a S.mor₁ ha.symm
    have hB₀ : rightOrthogonal P d.Z :=
      transfer_right hD₁ d.row₀ hB₁
    have hB₁' : rightOrthogonal P d.Z' :=
      transfer_right hD₂ d.row₁ hB₂
    obtain ⟨A₃, hA₃, ⟨eA⟩⟩ :=
      P.ext_of_isTriangulatedClosed₃' (Triangle.mk a d.a' d.a'') d.col₀ hA₁ hA₂
    have eA' : d.X'' ≅ A₃ := by
      simpa using eA
    have hB₃ : rightOrthogonal P d.Z'' :=
      (rightOrthogonal P).ext_of_isTriangulatedClosed₃
        (Triangle.mk d.c d.c' d.c'') d.col₂ hB₀ hB₁'
    have hD₃ : Triangle.mk (eA'.inv ≫ d.f'') d.g''
        (d.h'' ≫ eA'.hom⟦(1 : ℤ)⟧') ∈ distTriang C := by
      let U : Triangle C :=
        { obj₁ := A₃
          obj₂ := d.Y''
          obj₃ := d.Z''
          mor₁ := eA'.inv ≫ d.f''
          mor₂ := d.g''
          mor₃ := d.h'' ≫ eA'.hom⟦(1 : ℤ)⟧' }
      let V : Triangle C :=
        { obj₁ := d.X''
          obj₂ := d.Y''
          obj₃ := d.Z''
          mor₁ := d.f''
          mor₂ := d.g''
          mor₃ := d.h'' }
      have hV : V ∈ distTriang C := by
        simpa [V, Triangle.mk] using d.row₂
      have hU : U ∈ distTriang C := by
        exact isomorphic_distinguished V hV U
          (Triangle.isoMk U V eA'.symm (Iso.refl d.Y'') (Iso.refl d.Z'')
            (by simp [U, V])
            (by simp [U, V])
            (by
              simp only [U, V, Category.assoc, Iso.refl_hom, Category.id_comp]
              rw [← Functor.map_comp, eA'.hom_inv_id, Functor.map_id,
                Category.comp_id]))
      simpa [U] using hU
    have hY : HasRightDecomposition P d.Y'' :=
      ⟨A₃, d.Z'', eA'.inv ≫ d.f'', d.g'', d.h'' ≫ eA'.hom⟦(1 : ℤ)⟧',
        hD₃, hA₃, hB₃⟩
    obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk S.mor₁ d.b' d.b'') S d.col₁ hS (𝟙 S.obj₁) (𝟙 S.obj₂) (by
        change S.mor₁ ≫ 𝟙 S.obj₂ = 𝟙 S.obj₁ ≫ S.mor₁
        simp)
    let φ := Triangle.homMk (Triangle.mk S.mor₁ d.b' d.b'') S
      (𝟙 S.obj₁) (𝟙 S.obj₂) c (by
        change S.mor₁ ≫ 𝟙 S.obj₂ = 𝟙 S.obj₁ ≫ S.mor₁
        simp) hc₂ hc₃
    haveI : IsIso φ.hom₁ := by
      change IsIso (𝟙 S.obj₁)
      infer_instance
    haveI : IsIso φ.hom₂ := by
      change IsIso (𝟙 S.obj₂)
      infer_instance
    haveI : IsIso c := by
      change IsIso φ.hom₃
      exact isIso₃_of_isIso₁₂ φ d.col₁ hS inferInstance inferInstance
  exact iso_right (asIso c) hY
  have shift_right :
      ∀ {X : C}, HasRightDecomposition P X →
        ∀ n : ℤ, HasRightDecomposition P (X⟦n⟧) := by
    intro X hX n
    rcases hX with ⟨A, B, f, g, h, hD, hA, hB⟩
    let D := (Triangle.shiftFunctor C n).obj (Triangle.mk f g h)
    refine ⟨D.obj₁, D.obj₃, D.mor₁, D.mor₂, D.mor₃, ?_, ?_, ?_⟩
    · change D ∈ distTriang C
      exact Triangle.shift_distinguished (Triangle.mk f g h) hD n
    · change P (A⟦n⟧)
      exact (hP.isStableUnderShiftBy n).le_shift _ hA
    · change rightOrthogonal P (B⟦n⟧)
      exact ((inferInstance : (rightOrthogonal P).IsStableUnderShift ℤ).isStableUnderShiftBy n).le_shift _ hB
  have iso_right {X Y : C} (e : X ≅ Y) (hX : HasRightDecomposition P X) :
      HasRightDecomposition P Y := by
    rcases hX with ⟨A, B, f, g, h, hD, hA, hB⟩
    refine ⟨A, B, f ≫ e.hom, e.inv ≫ g, h, ?_, hA, hB⟩
    exact isomorphic_distinguished _ hD _
      (Triangle.isoMk _ _ (Iso.refl A) e.symm (Iso.refl B)
        (by
          change (f ≫ e.hom) ≫ e.inv = 𝟙 A ≫ f
          simp)
        (by
          change (e.inv ≫ g) ≫ 𝟙 B = e.inv ≫ g
          simp)
        (by
          change h ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 A) = 𝟙 B ≫ h
          simp))
  constructor
  · intro h₁₂
    exact first_case hT h₁₂.1 h₁₂.2
  constructor
  · intro h₁₃
    exact first_case (inv_rot_of_distTriang _ hT)
      (shift_right h₁₃.2 (-1 : ℤ)) h₁₃.1
  · intro h₂₃
    apply iso_right (shiftShiftNeg T.obj₁ (1 : ℤ))
    exact shift_right (first_case (rot_of_distTriang _ hT) h₂₃.1 h₂₃.2) (-1 : ℤ) -/

/-- Right-adjoint decompositions are closed under binary direct sums. -/
theorem prepare_adjoint_biproduct
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    {X Y : C} (hX : HasRightDecomposition P X)
    (hY : HasRightDecomposition P Y) :
    HasRightDecomposition P (X ⊞ Y) := by
  exact ((prepare_adjoint_two_out_of_three P
    (T := Triangle.mk (biprod.inl : X ⟶ X ⊞ Y)
      (biprod.snd : X ⊞ Y ⟶ Y)
      (0 : Y ⟶ X⟦(1 : ℤ)⟧))
    (split_triangle_distinguished X Y)).2.1 ⟨hX, hY⟩)

/-- Left-adjoint decompositions satisfy two-out-of-three for triangles. -/
theorem prepare_adjoint_dual_two_out_of_three
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) :
    (HasLeftDecomposition P T.obj₁ ∧
        HasLeftDecomposition P T.obj₂ →
          HasLeftDecomposition P T.obj₃) ∧
      (HasLeftDecomposition P T.obj₁ ∧
        HasLeftDecomposition P T.obj₃ →
          HasLeftDecomposition P T.obj₂) ∧
      (HasLeftDecomposition P T.obj₂ ∧
        HasLeftDecomposition P T.obj₃ →
          HasLeftDecomposition P T.obj₁) := by
  let hP : P.IsStableUnderShift ℤ := inferInstance
  have horth := orthogonal_triangulated P hP
  let _leftClosed : (leftOrthogonal P).IsClosedUnderIsomorphisms := horth.2.1
  let _leftTriangulated : (leftOrthogonal P).IsTriangulated := horth.2.2.2
  have transfer_isoClosure
      {A X B B' : C} {f : A ⟶ X}
      {g : X ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
      {g' : X ⟶ B'} {h' : B' ⟶ A⟦(1 : ℤ)⟧}
      (hD : Triangle.mk f g h ∈ distTriang C)
      (hD' : Triangle.mk f g' h' ∈ distTriang C)
      (hB : P B) : P.isoClosure B' := by
    obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk f g h) (Triangle.mk f g' h') hD hD' (𝟙 _) (𝟙 _) (by
        change f ≫ 𝟙 X = 𝟙 A ≫ f
        simp)
    let φ := Triangle.homMk (Triangle.mk f g h) (Triangle.mk f g' h')
      (𝟙 A) (𝟙 X) c (by
        change f ≫ 𝟙 X = 𝟙 A ≫ f
        simp) hc₂ hc₃
    let _ : IsIso φ.hom₁ := by
      change IsIso (𝟙 A)
      infer_instance
    let _ : IsIso φ.hom₂ := by
      change IsIso (𝟙 X)
      infer_instance
    have hc : IsIso c := by
      change IsIso φ.hom₃
      apply isIso₃_of_isIso₁₂ φ hD hD'
      · exact inferInstance
      · exact inferInstance
    exact ⟨B, hB, ⟨(@asIso _ _ _ _ c hc).symm⟩⟩
  have shift_left :
      ∀ {X : C}, HasLeftDecomposition P X →
        ∀ n : ℤ, HasLeftDecomposition P (X⟦n⟧) := by
    intro X hX n
    rcases hX with ⟨A, B, f, g, h, hD, hA, hB⟩
    let D := (Triangle.shiftFunctor C n).obj (Triangle.mk f g h)
    refine ⟨D.obj₁, D.obj₃, D.mor₁, D.mor₂, D.mor₃, ?_, ?_, ?_⟩
    · change D ∈ distTriang C
      exact Triangle.shift_distinguished (Triangle.mk f g h) hD n
    · change leftOrthogonal P (A⟦n⟧)
      exact ((inferInstance : (leftOrthogonal P).IsStableUnderShift ℤ).isStableUnderShiftBy n).le_shift _ hA
    · change P (B⟦n⟧)
      exact (hP.isStableUnderShiftBy n).le_shift _ hB
  have iso_left {X Y : C} (e : X ≅ Y) (hX : HasLeftDecomposition P X) :
      HasLeftDecomposition P Y := by
    rcases hX with ⟨A, B, f, g, h, hD, hA, hB⟩
    refine ⟨A, B, f ≫ e.hom, e.inv ≫ g, h, ?_, hA, hB⟩
    exact isomorphic_distinguished _ hD _
      (Triangle.isoMk _ _ (Iso.refl A) e.symm (Iso.refl B)
        (by
          change (f ≫ e.hom) ≫ e.inv = 𝟙 A ≫ f
          simp)
        (by
          change (e.inv ≫ g) ≫ 𝟙 B = e.inv ≫ g
          simp)
        (by
          change h ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 A) = 𝟙 B ≫ h
          simp))
  have first_case :
      ∀ {S : Triangle C}, S ∈ distTriang C →
        HasLeftDecomposition P S.obj₁ →
        HasLeftDecomposition P S.obj₂ →
        HasLeftDecomposition P S.obj₃ := by
    intro S hS hS₁ hS₂
    rcases hS₁ with ⟨A₁, B₁, f₁, g₁, h₁, hD₁, hA₁, hB₁⟩
    rcases hS₂ with ⟨A₂, B₂, f₂, g₂, h₂, hD₂, hA₂, hB₂⟩
    have hc' := (((pre_prepare_adjoint_dual P hP hD₁).1 hA₁ B₂ hB₂).2
      (S.mor₁ ≫ g₂))
    change ∃ c : B₁ ⟶ B₂, g₁ ≫ c = S.mor₁ ≫ g₂ at hc'
    obtain ⟨c, hc⟩ := hc'
    obtain ⟨a, ha, ha'⟩ := complete_distinguished_triangle_morphism₁
      (Triangle.mk f₁ g₁ h₁) (Triangle.mk f₂ g₂ h₂) hD₁ hD₂
      S.mor₁ c hc
    obtain ⟨d⟩ := three_by_three_completion f₁ f₂ a S.mor₁ ha
    have hA₃ : leftOrthogonal P d.X'' :=
      (leftOrthogonal P).ext_of_isTriangulatedClosed₃
        (Triangle.mk a d.a' d.a'') d.col₀ hA₁ hA₂
    have hB₀ : P.isoClosure d.Z :=
      transfer_isoClosure hD₁ d.row₀ hB₁
    have hB₁' : P.isoClosure d.Z' :=
      transfer_isoClosure hD₂ d.row₁ hB₂
    have hB₃' : P.isoClosure d.Z'' :=
      (P.isoClosure).ext_of_isTriangulatedClosed₃
        (Triangle.mk d.c d.c' d.c'') d.col₂ hB₀ hB₁'
    obtain ⟨B₃, hB₃, ⟨eB⟩⟩ := hB₃'
    have eB' : d.Z'' ≅ B₃ := by
      simpa using eB
    have hD₃ : Triangle.mk d.f'' (d.g'' ≫ eB'.hom)
        (eB'.inv ≫ d.h'') ∈ distTriang C := by
      let U : Triangle C :=
        { obj₁ := d.X''
          obj₂ := d.Y''
          obj₃ := B₃
          mor₁ := d.f''
          mor₂ := d.g'' ≫ eB'.hom
          mor₃ := eB'.inv ≫ d.h'' }
      let V : Triangle C :=
        { obj₁ := d.X''
          obj₂ := d.Y''
          obj₃ := d.Z''
          mor₁ := d.f''
          mor₂ := d.g''
          mor₃ := d.h'' }
      have hV : V ∈ distTriang C := by
        simpa [V, Triangle.mk] using d.row₂
      have hU : U ∈ distTriang C := by
        exact isomorphic_distinguished V hV U
          (Triangle.isoMk U V (Iso.refl d.X'') (Iso.refl d.Y'') eB'.symm
            (by simp [U, V])
            (by
              simp only [U, V, Category.assoc, Iso.refl_hom, Category.id_comp]
              simp)
            (by
              simp only [U, V, Category.assoc, Iso.refl_hom]
              simp))
      simpa [U, Triangle.mk] using hU
    have hY : HasLeftDecomposition P d.Y'' :=
      ⟨d.X'', B₃, d.f'', d.g'' ≫ eB'.hom, eB'.inv ≫ d.h'',
        hD₃, hA₃, hB₃⟩
    obtain ⟨c', hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk S.mor₁ d.b' d.b'') S d.col₁ hS (𝟙 S.obj₁) (𝟙 S.obj₂) (by
        change S.mor₁ ≫ 𝟙 S.obj₂ = 𝟙 S.obj₁ ≫ S.mor₁
        simp)
    let φ := Triangle.homMk (Triangle.mk S.mor₁ d.b' d.b'') S
      (𝟙 S.obj₁) (𝟙 S.obj₂) c' (by
        change S.mor₁ ≫ 𝟙 S.obj₂ = 𝟙 S.obj₁ ≫ S.mor₁
        simp) hc₂ hc₃
    let _ : IsIso φ.hom₁ := by
      change IsIso (𝟙 S.obj₁)
      infer_instance
    let _ : IsIso φ.hom₂ := by
      change IsIso (𝟙 S.obj₂)
      infer_instance
    let _ : IsIso c' := by
      change IsIso φ.hom₃
      exact isIso₃_of_isIso₁₂ φ d.col₁ hS inferInstance inferInstance
    exact iso_left (asIso c') hY
  constructor
  · intro h₁₂
    exact first_case hT h₁₂.1 h₁₂.2
  constructor
  · intro h₁₃
    exact first_case (inv_rot_of_distTriang _ hT)
      (shift_left h₁₃.2 (-1 : ℤ)) h₁₃.1
  · intro h₂₃
    apply iso_left (shiftShiftNeg T.obj₁ (1 : ℤ))
    exact shift_left (first_case (rot_of_distTriang _ hT) h₂₃.1 h₂₃.2) (-1 : ℤ)

/-- Left-adjoint decompositions are closed under binary direct sums. -/
theorem prepare_adjoint_dual_biproduct
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    {X Y : C} (hX : HasLeftDecomposition P X)
    (hY : HasLeftDecomposition P Y) :
    HasLeftDecomposition P (X ⊞ Y) := by
  exact ((prepare_adjoint_dual_two_out_of_three P
    (T := Triangle.mk (biprod.inl : X ⟶ X ⊞ Y)
      (biprod.snd : X ⊞ Y ⟶ Y)
      (0 : Y ⟶ X⟦(1 : ℤ)⟧))
    (split_triangle_distinguished X Y)).2.1 ⟨hX, hY⟩)

/-! ## Adjoints of inclusions -/

/-- The inclusion of `P` has a right adjoint. -/
def HasRightAdjoint (P : ObjectProperty C) : Prop :=
  ∃ (v : C ⥤ P.FullSubcategory), Nonempty (P.ι ⊣ v)

/-- The inclusion of `P` has a left adjoint. -/
def HasLeftAdjoint (P : ObjectProperty C) : Prop :=
  ∃ (v : C ⥤ P.FullSubcategory), Nonempty (v ⊣ P.ι)

/-- A right adjoint of the inclusion is equivalent to right decompositions. -/
theorem right_adjoint_iff_decomposition
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C] :
    HasRightAdjoint P ↔ ∀ X : C, HasRightDecomposition P X := by
  let hP : P.IsStableUnderShift ℤ := inferInstance
  constructor
  · rintro ⟨v, ⟨adj⟩⟩ X
    let A := P.ι.obj (v.obj X)
    let i := adj.counit.app X
    obtain ⟨B, g, h, hD⟩ := distinguished_cone_exists i
    refine ⟨A, B, i, g, h, hD, (v.obj X).property, ?_⟩
    apply (pre_prepare_adjoint P hP hD).2
    intro A' hA'
    let A₀ : P.FullSubcategory := ⟨A', hA'⟩
    have hbij' : Function.Bijective
        (fun q : A₀ ⟶ v.obj X => P.ι.map q ≫ i) := by
      constructor
      · intro q r hqr
        have hqr' := congrArg (adj.homEquiv A₀ X) hqr
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at hqr'
        have hi : (adj.homEquiv (v.obj X) X) i = 𝟙 (v.obj X) := by
          apply (adj.homEquiv (v.obj X) X).symm.injective
          rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
          simp [i]
        rw [hi] at hqr'
        simpa using hqr'
      · intro f
        refine ⟨adj.homEquiv A₀ X f, ?_⟩
        have hf := adj.homEquiv_counit A₀ X (adj.homEquiv A₀ X f)
        simpa using hf.symm
    have hbij : Function.Bijective (fun q : A' ⟶ A => q ≫ i) := by
      constructor
      · intro q r hqr
        have hqr' :
            ({ hom := q } : A₀ ⟶ v.obj X) = { hom := r } := by
          apply hbij'.1
          simpa using hqr
        exact congrArg (fun k => k.hom) hqr'
      · intro f
        obtain ⟨q, hq⟩ := hbij'.2 f
        refine ⟨q.hom, ?_⟩
        simpa using hq
    exact hbij
  · intro hdec
    have hdata : ∀ X : C, ∃ (A B : C) (f : A ⟶ X) (g : X ⟶ B)
        (h : B ⟶ A⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧ P A ∧ rightOrthogonal P B := hdec
    choose A B f g h hD hA hB using hdata
    have hbij (X : P.FullSubcategory) (Y : C) :
        Function.Bijective (fun q : X.obj ⟶ A Y => q ≫ f Y) :=
      (pre_prepare_adjoint P hP (hD Y)).1 (hB Y) X.obj X.property
    let preimage (X : P.FullSubcategory) {Y : C} (φ : X.obj ⟶ Y) :
        X.obj ⟶ A Y := Classical.choose ((hbij X Y).2 φ)
    have preimage_spec (X : P.FullSubcategory) {Y : C} (φ : X.obj ⟶ Y) :
        preimage X φ ≫ f Y = φ := Classical.choose_spec ((hbij X Y).2 φ)
    let chosen (X : C) : P.FullSubcategory := ⟨A X, hA X⟩
    let vmap {X Y : C} (φ : X ⟶ Y) : A X ⟶ A Y :=
      preimage (chosen X) (f X ≫ φ)
    have vmap_spec {X Y : C} (φ : X ⟶ Y) :
        vmap φ ≫ f Y = f X ≫ φ := preimage_spec (chosen X) (f X ≫ φ)
    let v : C ⥤ P.FullSubcategory :=
      { obj := fun X => ⟨A X, hA X⟩
        map := fun {X Y} φ => { hom := vmap φ }
        map_id := by
          intro X
          ext
          change vmap (𝟙 X) = 𝟙 (A X)
          apply (hbij (chosen X) X).1
          change vmap (𝟙 X) ≫ f X = 𝟙 (A X) ≫ f X
          rw [vmap_spec]
          simp
        map_comp := by
          intro X Y Z φ ψ
          ext
          apply (hbij (chosen X) Z).1
          calc
            vmap (φ ≫ ψ) ≫ f Z = f X ≫ (φ ≫ ψ) := vmap_spec (φ ≫ ψ)
            _ = (f X ≫ φ) ≫ ψ := by simp only [Category.assoc]
            _ = (vmap φ ≫ f Y) ≫ ψ := by rw [vmap_spec φ]
            _ = vmap φ ≫ (vmap ψ ≫ f Z) := by
              rw [vmap_spec ψ]
              simp only [Category.assoc]
            _ = (vmap φ ≫ vmap ψ) ≫ f Z := by simp only [Category.assoc] }
    let homEquiv : ∀ (X : P.FullSubcategory) (Y : C),
        (P.ι.obj X ⟶ Y) ≃ (X ⟶ v.obj Y) := fun X Y =>
      { toFun := fun φ => { hom := preimage X φ }
        invFun := fun ψ => by
          change X.obj ⟶ Y
          exact P.ι.map ψ ≫ f Y
        left_inv := by
          intro φ
          simpa using preimage_spec X φ
        right_inv := by
          intro ψ
          ext
          apply (hbij X Y).1
          change preimage X (ψ.hom ≫ f Y) ≫ f Y = ψ.hom ≫ f Y
          exact preimage_spec X (ψ.hom ≫ f Y) }
    refine ⟨v, ⟨Adjunction.mkOfHomEquiv {
      homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro X X' Y φ ψ
        change (φ.hom ≫ ψ.hom) ≫ f Y = φ.hom ≫ (ψ.hom ≫ f Y)
        simp only [Category.assoc]
      homEquiv_naturality_right := by
        intro X Y Y' φ ψ
        ext
        apply (hbij X Y').1
        change preimage X (φ ≫ ψ) ≫ f Y' =
          (preimage X φ ≫ vmap ψ) ≫ f Y'
        rw [preimage_spec]
        simp only [Category.assoc]
        rw [vmap_spec, ← Category.assoc, preimage_spec] }⟩⟩

private theorem right_adjoint_isoClosure_eq_left_orthogonal
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasRightAdjoint P) :
    P.isoClosure = leftOrthogonal (rightOrthogonal P) := by
  let hstable : P.IsStableUnderShift ℤ := inferInstance
  have hdec : ∀ X : C, HasRightDecomposition P X :=
    (right_adjoint_iff_decomposition P).1 hP
  ext X
  constructor
  · rintro ⟨Z, hZ, ⟨e⟩⟩
    intro B hB fX
    have hf : e.inv ≫ fX = 0 := hB Z hZ (e.inv ≫ fX)
    calc
      fX = 𝟙 _ ≫ fX := by simp
      _ = (e.hom ≫ e.inv) ≫ fX := by simp
      _ = e.hom ≫ (e.inv ≫ fX) := by simp only [Category.assoc]
      _ = 0 := by rw [hf, comp_zero]
  · intro hX
    obtain ⟨A, B, f, g, h, hD, hA, hB⟩ := hdec X
    have hg : g = 0 := hX B hB g
    obtain ⟨q, hq⟩ := Triangle.yoneda_exact₃ (Triangle.mk f g h) hD
      (𝟙 B) (by
        change g ≫ 𝟙 B = 0
        rw [hg, zero_comp])
    have hq0 : q = 0 :=
      hB (A⟦(1 : ℤ)⟧)
        ((hstable.isStableUnderShiftBy (1 : ℤ)).le_shift _ hA) q
    have hq' : 𝟙 B = h ≫ q := by simpa [Triangle.mk] using hq
    have hBid : 𝟙 B = 0 := by
      calc
        𝟙 B = h ≫ q := hq'
        _ = h ≫ 0 := by rw [hq0]; rfl
        _ = 0 := by simp only [comp_zero]
    have hBzero : IsZero B := (IsZero.iff_id_eq_zero B).mpr hBid
    have hfiso : IsIso f := (third_object_zero_characterization f).2.2 (by
      intro Z g' h' hT'
      obtain ⟨e, _, _⟩ := distinguished_cone_unique hD hT'
      let eB : Z ≅ B :=
        { hom := e.inv.hom₃
          inv := e.hom.hom₃
          hom_inv_id := by exact e.inv_hom_id_triangle_hom₃
          inv_hom_id := by exact e.hom_inv_id_triangle_hom₃ }
      apply (IsZero.iff_id_eq_zero Z).mpr
      calc
        𝟙 Z = eB.hom ≫ eB.inv := eB.hom_inv_id.symm
        _ = eB.hom ≫ 𝟙 B ≫ eB.inv := by simp
        _ = 0 := by simp [hBid])
    exact ⟨A, hA, ⟨(@asIso _ _ _ _ f hfiso).symm⟩⟩

/-- A right adjoint makes the subcategory saturated. -/
theorem right_adjoint_saturated
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasRightAdjoint P) :
  IsSaturated P := by
  have hEq := right_adjoint_isoClosure_eq_left_orthogonal P hP
  have hright : rightOrthogonal P = ObjectProperty.rightOrthogonal P := by
    ext X
    constructor
    · intro h A f hA
      exact h A hA f
    · intro h A hA f
      exact h f hA
  have hrightStable : (rightOrthogonal P).IsStableUnderShift ℤ := by
    rw [hright]
    infer_instance
  have horth := orthogonal_triangulated (rightOrthogonal P)
    hrightStable
  intro X Y hXY
  rw [hEq] at hXY ⊢
  obtain ⟨hX, hY⟩ := horth.2.2.1
    (ObjectProperty.le_isoClosure (leftOrthogonal (rightOrthogonal P)) (X ⊞ Y) hXY)
  constructor
  · obtain ⟨Z, hZ, ⟨e⟩⟩ := hX
    exact @ObjectProperty.prop_of_iso _ _ (leftOrthogonal (rightOrthogonal P))
      horth.2.1 _ _ e.symm hZ
  · obtain ⟨Z, hZ, ⟨e⟩⟩ := hY
    exact @ObjectProperty.prop_of_iso _ _ (leftOrthogonal (rightOrthogonal P))
      horth.2.1 _ _ e.symm hZ

/-- Under strict fullness, a right-admissible subcategory is the left
orthogonal of its right orthogonal. -/
theorem right_adjoint_eq_left_orthogonal
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasRightAdjoint P)
    (hstrict : P.IsClosedUnderIsomorphisms) :
    P = leftOrthogonal (rightOrthogonal P) := by
  have hEq := right_adjoint_isoClosure_eq_left_orthogonal P hP
  apply le_antisymm
  · intro X hX
    rw [← hEq]
    exact ObjectProperty.le_isoClosure P X hX
  · intro X hX
    have hX' : P.isoClosure X := by
      rw [hEq]
      exact hX
    obtain ⟨Z, hZ, ⟨e⟩⟩ := hX'
    exact @ObjectProperty.prop_of_iso _ _ P hstrict _ _ e.symm hZ

/-- A left adjoint of the inclusion is equivalent to left decompositions. -/
theorem left_adjoint_iff_decomposition
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C] :
    HasLeftAdjoint P ↔ ∀ X : C, HasLeftDecomposition P X := by
  let hP : P.IsStableUnderShift ℤ := inferInstance
  constructor
  · rintro ⟨v, ⟨adj⟩⟩ X
    let B := P.ι.obj (v.obj X)
    let g := adj.unit.app X
    obtain ⟨Z, f, h, hD⟩ := distinguished_cone_exists g
    let T := Triangle.mk g f h
    have hT : T.invRotate ∈ distTriang C := inv_rot_of_distTriang _ hD
    refine ⟨T.invRotate.obj₁, T.invRotate.obj₃, T.invRotate.mor₁, T.invRotate.mor₂,
      T.invRotate.mor₃, hT, ?_, (v.obj X).property⟩
    apply (pre_prepare_adjoint_dual P hP hT).2
    intro B' hB'
    let B₀ : P.FullSubcategory := ⟨B', hB'⟩
    have hbij' : Function.Bijective
        (fun q : v.obj X ⟶ B₀ => g ≫ P.ι.map q) := by
      constructor
      · intro q r hqr
        apply (adj.homEquiv X B₀).injective
        rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
        simpa [g] using hqr
      · intro f'
        refine ⟨(adj.homEquiv X B₀).symm f', ?_⟩
        have hf := (adj.homEquiv X B₀).apply_symm_apply f'
        rw [Adjunction.homEquiv_unit] at hf
        simpa [g] using hf
    have hbij : Function.Bijective (fun q : B ⟶ B' => g ≫ q) := by
      constructor
      · intro q r hqr
        have hqr' :
            ({ hom := q } : v.obj X ⟶ B₀) = { hom := r } := by
          apply hbij'.1
          simpa using hqr
        exact congrArg (fun k => k.hom) hqr'
      · intro f'
        obtain ⟨q, hq⟩ := hbij'.2 f'
        refine ⟨q.hom, ?_⟩
        simpa using hq
    exact hbij
  · intro hdec
    have hdata : ∀ X : C, ∃ (A B : C) (f : A ⟶ X) (g : X ⟶ B)
        (h : B ⟶ A⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧ leftOrthogonal P A ∧ P B := hdec
    choose A B f g h hD hA hB using hdata
    have hbij (X : C) (Y : P.FullSubcategory) :
        Function.Bijective (fun q : B X ⟶ Y.obj => g X ≫ q) :=
      (pre_prepare_adjoint_dual P hP (hD X)).1 (hA X) Y.obj Y.property
    let preimage (X : C) (Y : P.FullSubcategory) (φ : X ⟶ Y.obj) :
        B X ⟶ Y.obj := Classical.choose ((hbij X Y).2 φ)
    have preimage_spec (X : C) (Y : P.FullSubcategory) (φ : X ⟶ Y.obj) :
        g X ≫ preimage X Y φ = φ := Classical.choose_spec ((hbij X Y).2 φ)
    let chosen (X : C) : P.FullSubcategory := ⟨B X, hB X⟩
    let vmap {X Y : C} (φ : X ⟶ Y) : B X ⟶ B Y :=
      preimage X (chosen Y) (φ ≫ g Y)
    have vmap_spec {X Y : C} (φ : X ⟶ Y) :
        g X ≫ vmap φ = φ ≫ g Y := preimage_spec X (chosen Y) (φ ≫ g Y)
    let v : C ⥤ P.FullSubcategory :=
      { obj := fun X => ⟨B X, hB X⟩
        map := fun {X Y} φ => { hom := vmap φ }
        map_id := by
          intro X
          ext
          change vmap (𝟙 X) = 𝟙 (B X)
          apply (hbij X (chosen X)).1
          change g X ≫ vmap (𝟙 X) = g X ≫ 𝟙 (B X)
          rw [vmap_spec]
          simp
        map_comp := by
          intro X Y Z φ ψ
          ext
          apply (hbij X (chosen Z)).1
          calc
            g X ≫ vmap (φ ≫ ψ) = (φ ≫ ψ) ≫ g Z := vmap_spec (φ ≫ ψ)
            _ = φ ≫ (ψ ≫ g Z) := by simp only [Category.assoc]
            _ = φ ≫ (g Y ≫ vmap ψ) := by rw [vmap_spec ψ]
            _ = (φ ≫ g Y) ≫ vmap ψ := by simp only [Category.assoc]
            _ = (g X ≫ vmap φ) ≫ vmap ψ := by rw [vmap_spec φ]
            _ = g X ≫ (vmap φ ≫ vmap ψ) := by simp only [Category.assoc] }
    let homEquiv : ∀ (X : C) (Y : P.FullSubcategory),
        (v.obj X ⟶ Y) ≃ (X ⟶ P.ι.obj Y) := fun X Y =>
      { toFun := fun ψ => g X ≫ P.ι.map ψ
        invFun := fun φ => { hom := preimage X Y φ }
        left_inv := by
          intro ψ
          ext
          apply (hbij X Y).1
          change g X ≫ preimage X Y (g X ≫ ψ.hom) = g X ≫ ψ.hom
          exact preimage_spec X Y (g X ≫ ψ.hom)
        right_inv := by
          intro φ
          simpa using preimage_spec X Y φ }
    refine ⟨v, ⟨Adjunction.mkOfHomEquiv {
      homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro X X' Y φ ψ
        ext
        apply (hbij X Y).1
        change g X ≫ preimage X Y (φ ≫ ψ) =
          g X ≫ (vmap φ ≫ preimage X' Y ψ)
        calc
          g X ≫ preimage X Y (φ ≫ ψ) = φ ≫ ψ :=
            preimage_spec X Y (φ ≫ ψ)
          _ = φ ≫ (g X' ≫ preimage X' Y ψ) := by
            rw [preimage_spec]
          _ = (φ ≫ g X') ≫ preimage X' Y ψ := by
            simp only [Category.assoc]
          _ = (g X ≫ vmap φ) ≫ preimage X' Y ψ := by rw [vmap_spec]
          _ = g X ≫ (vmap φ ≫ preimage X' Y ψ) := by simp only [Category.assoc]
      homEquiv_naturality_right := by
        intro X Y Y' φ ψ
        change g X ≫ (φ.hom ≫ ψ.hom) = (g X ≫ φ.hom) ≫ ψ.hom
        simp only [Category.assoc] }⟩⟩

private theorem left_adjoint_isoClosure_eq_right_orthogonal
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasLeftAdjoint P) :
    P.isoClosure = rightOrthogonal (leftOrthogonal P) := by
  let hstable : P.IsStableUnderShift ℤ := inferInstance
  have hdec : ∀ X : C, HasLeftDecomposition P X :=
    (left_adjoint_iff_decomposition P).1 hP
  ext X
  constructor
  · rintro ⟨Z, hZ, ⟨e⟩⟩
    intro A hA fX
    have hf : fX ≫ e.hom = 0 := hA Z hZ (fX ≫ e.hom)
    calc
      fX = fX ≫ 𝟙 _ := by simp
      _ = fX ≫ (e.hom ≫ e.inv) := by simp
      _ = (fX ≫ e.hom) ≫ e.inv := by simp only [Category.assoc]
      _ = 0 := by rw [hf, zero_comp]
  · intro hX
    obtain ⟨A, B, f, g, h, hD, hA, hB⟩ := hdec X
    have hf : f = 0 := hX A hA f
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₁ (Triangle.mk f g h) hD
      (𝟙 (A⟦(1 : ℤ)⟧)) (by
        change 𝟙 (A⟦(1 : ℤ)⟧) ≫ (shiftFunctor C (1 : ℤ)).map f = 0
        simp [hf])
    have horthP := orthogonal_triangulated P hstable
    let : (leftOrthogonal P).IsTriangulated := horthP.2.2.2
    have hAshift : (leftOrthogonal P).IsStableUnderShift ℤ := by
      infer_instance
    have hq0 : q = 0 := by
      exact (hAshift.isStableUnderShiftBy (1 : ℤ)).le_shift _ hA B hB q
    have hAid : 𝟙 (A⟦(1 : ℤ)⟧) = 0 := by
      calc
        𝟙 (A⟦(1 : ℤ)⟧) = q ≫ h := by simpa [Triangle.mk] using hq
        _ = 0 := by
          rw [hq0]
          exact zero_comp
    have hgiso : IsIso g := (third_object_zero_characterization g).2.2 (by
      intro Z g' h' hT'
      have hT := rot_of_distTriang (Triangle.mk f g h) hD
      obtain ⟨e, _, _⟩ := distinguished_cone_unique hT hT'
      let eA : Z ≅ A⟦(1 : ℤ)⟧ :=
        { hom := e.inv.hom₃
          inv := e.hom.hom₃
          hom_inv_id := by exact e.inv_hom_id_triangle_hom₃
          inv_hom_id := by exact e.hom_inv_id_triangle_hom₃ }
      apply (IsZero.iff_id_eq_zero Z).mpr
      calc
        𝟙 Z = eA.hom ≫ eA.inv := eA.hom_inv_id.symm
        _ = eA.hom ≫ 𝟙 (A⟦(1 : ℤ)⟧) ≫ eA.inv := by simp
        _ = 0 := by simp [hAid])
    exact ⟨B, hB, ⟨(@asIso _ _ _ _ g hgiso)⟩⟩

/-- A left adjoint makes the subcategory saturated. -/
theorem left_adjoint_saturated
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasLeftAdjoint P) :
    IsSaturated P := by
  have hEq := left_adjoint_isoClosure_eq_right_orthogonal P hP
  have hleft : leftOrthogonal P = ObjectProperty.leftOrthogonal P := by
    ext X
    constructor
    · intro h A f hA
      exact h A hA f
    · intro h A hA f
      exact h f hA
  have hleftStable : (leftOrthogonal P).IsStableUnderShift ℤ := by
    rw [hleft]
    infer_instance
  have horth := orthogonal_triangulated (leftOrthogonal P) hleftStable
  intro X Y hXY
  rw [hEq] at hXY ⊢
  obtain ⟨hX, hY⟩ := horth.1.2.1
    (ObjectProperty.le_isoClosure (rightOrthogonal (leftOrthogonal P))
      (X ⊞ Y) hXY)
  constructor
  · obtain ⟨Z, hZ, ⟨e⟩⟩ := hX
    exact @ObjectProperty.prop_of_iso _ _ (rightOrthogonal (leftOrthogonal P))
      horth.1.1 _ _ e.symm hZ
  · obtain ⟨Z, hZ, ⟨e⟩⟩ := hY
    exact @ObjectProperty.prop_of_iso _ _ (rightOrthogonal (leftOrthogonal P))
      horth.1.1 _ _ e.symm hZ

/-- Under strict fullness, a left-admissible subcategory is the right
orthogonal of its left orthogonal. -/
theorem left_adjoint_eq_right_orthogonal
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasLeftAdjoint P)
    (hstrict : P.IsClosedUnderIsomorphisms) :
    P = rightOrthogonal (leftOrthogonal P) := by
  have hEq := left_adjoint_isoClosure_eq_right_orthogonal P hP
  apply le_antisymm
  · intro X hX
    rw [← hEq]
    exact ObjectProperty.le_isoClosure P X hX
  · intro X hX
    have hX' : P.isoClosure X := by
      rw [hEq]
      exact hX
    obtain ⟨Z, hZ, ⟨e⟩⟩ := hX'
    exact @ObjectProperty.prop_of_iso _ _ P hstrict _ _ e.symm hZ

/-! ## Right, left, and two-sided admissibility -/

/-- A strictly full triangulated subcategory with a right adjoint inclusion. -/
def RightAdmissible (P : ObjectProperty C) : Prop :=
  P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧ HasRightAdjoint P

/-- A strictly full triangulated subcategory with a left adjoint inclusion. -/
def LeftAdmissible (P : ObjectProperty C) : Prop :=
  P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧ HasLeftAdjoint P

/-- A subcategory which is both right and left admissible. -/
def TwoSidedAdmissible (P : ObjectProperty C) : Prop :=
  RightAdmissible P ∧ LeftAdmissible P

/-- Right admissibility can equivalently be expressed by decompositions. -/
theorem right_admissible_iff_decomposition
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C] :
    RightAdmissible P ↔
      P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧
        (∀ X : C, HasRightDecomposition P X) := by
  constructor
  · rintro ⟨hstrict, htri, hP⟩
    let := htri
    exact ⟨hstrict, htri, (right_adjoint_iff_decomposition P).1 hP⟩
  · rintro ⟨hstrict, htri, hdec⟩
    let := htri
    exact ⟨hstrict, htri, (right_adjoint_iff_decomposition P).2 hdec⟩

/-- Left admissibility can equivalently be expressed by decompositions. -/
theorem left_admissible_iff_decomposition
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C] :
    LeftAdmissible P ↔
      P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧
        (∀ X : C, HasLeftDecomposition P X) := by
  constructor
  · rintro ⟨hstrict, htri, hP⟩
    let := htri
    exact ⟨hstrict, htri, (left_adjoint_iff_decomposition P).1 hP⟩
  · rintro ⟨hstrict, htri, hdec⟩
    let := htri
    exact ⟨hstrict, htri, (left_adjoint_iff_decomposition P).2 hdec⟩

/-! ## Canonicality of the right-adjoint triangle -/

/-- Two right-adjoint decomposition triangles over the same object are
isomorphic by a triangle isomorphism whose middle component is the identity. -/
theorem right_admissible_decomposition_iso
    (P : ObjectProperty C) (hP : RightAdmissible P)
    [CategoryTheory.IsTriangulated C]
    {X A A' B B' : C}
    {f : A ⟶ X} {g : X ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    {f' : A' ⟶ X} {g' : X ⟶ B'} {h' : B' ⟶ A'⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hT' : Triangle.mk f' g' h' ∈ distTriang C)
    (hA : P A) (hB : rightOrthogonal P B)
    (hA' : P A') (hB' : rightOrthogonal P B') :
    ∃ e : Triangle.mk f g h ≅ Triangle.mk f' g' h',
      e.hom.hom₂ = 𝟙 X := by
  rcases hP with ⟨hstrict, htri, hAdj⟩
  let _ : P.IsTriangulated := htri
  let hstable : P.IsStableUnderShift ℤ := inferInstance
  have hbij : Function.Bijective (fun q : A ⟶ A' => q ≫ f') :=
    (pre_prepare_adjoint P hstable hT').1 hB' A hA
  have hbij' : Function.Bijective (fun q : A' ⟶ A => q ≫ f) :=
    (pre_prepare_adjoint P hstable hT).1 hB A' hA'
  have hbij₀ : Function.Bijective (fun q : A ⟶ A => q ≫ f) :=
    (pre_prepare_adjoint P hstable hT).1 hB A hA
  have hbij₀' : Function.Bijective (fun q : A' ⟶ A' => q ≫ f') :=
    (pre_prepare_adjoint P hstable hT').1 hB' A' hA'
  obtain ⟨a, ha⟩ := hbij.2 f
  obtain ⟨b, hb⟩ := hbij'.2 f'
  change a ≫ f' = f at ha
  change b ≫ f = f' at hb
  have hcomm : f ≫ 𝟙 X = a ≫ f' := by
    simpa using ha.symm
  have hcomm' : f' ≫ 𝟙 X = b ≫ f := by
    simpa using hb.symm
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
    (Triangle.mk f g h) (Triangle.mk f' g' h') hT hT' a (𝟙 X) hcomm
  have hab : a ≫ b = 𝟙 A := by
    apply hbij₀.1
    calc
      (a ≫ b) ≫ f = a ≫ (b ≫ f) := by simp only [Category.assoc]
      _ = a ≫ f' := by rw [hb]
      _ = f := ha
      _ = (𝟙 A) ≫ f := by simp
  have hba : b ≫ a = 𝟙 A' := by
    apply hbij₀'.1
    calc
      (b ≫ a) ≫ f' = b ≫ (a ≫ f') := by simp only [Category.assoc]
      _ = b ≫ f := by rw [ha]
      _ = f' := hb
      _ = (𝟙 A') ≫ f' := by simp
  let ea : A ≅ A' :=
    { hom := a
      inv := b
      hom_inv_id := hab
      inv_hom_id := hba }
  let φ := Triangle.homMk (Triangle.mk f g h) (Triangle.mk f' g' h')
    a (𝟙 X) c hcomm hc₂ hc₃
  let _ : IsIso φ.hom₁ := by
    change IsIso a
    exact ea.isIso_hom
  let _ : IsIso φ.hom₂ := by
    change IsIso (𝟙 X)
    infer_instance
  have hc : IsIso c := by
    change IsIso φ.hom₃
    exact isIso₃_of_isIso₁₂ φ hT hT' inferInstance inferInstance
  let _ : IsIso c := hc
  let e := Triangle.isoMk (Triangle.mk f g h) (Triangle.mk f' g' h')
    ea (Iso.refl X) (asIso c) hcomm hc₂ hc₃
  exact ⟨e, rfl⟩

/-! ## The summary proposition -/

/-- The three equivalent conditions for an admissible pair. -/
def AdmissiblePairConditionOne
    (A B : ObjectProperty C) : Prop :=
  RightAdmissible A ∧ B = rightOrthogonal A

def AdmissiblePairConditionTwo
    (A B : ObjectProperty C) : Prop :=
  LeftAdmissible B ∧ A = leftOrthogonal B

def AdmissiblePairConditionThree
    (A B : ObjectProperty C) : Prop :=
  A.IsClosedUnderIsomorphisms ∧
    A.IsTriangulated ∧
    B.IsClosedUnderIsomorphisms ∧
    B.IsTriangulated ∧
    (∀ (X Y : C), A X → B Y → HomIsZero X Y) ∧
    (∀ X : C, HasTriangleDecomposition A B X)

/-- The quotient equivalences and adjoint factorizations in the summary. -/
def AdmissiblePairConclusion
    (A B : ObjectProperty C) : Prop :=
    Functor.IsEquivalence (A.ι ⋙ quotientFunctor B) ∧
    Functor.IsEquivalence (B.ι ⋙ quotientFunctor A) ∧
    (∃ (v : quotientCategory B ⥤ A.FullSubcategory),
      Nonempty (A.ι ⊣ quotientFunctor B ⋙ v)) ∧
    (∃ (u : quotientCategory A ⥤ B.FullSubcategory),
      Nonempty (quotientFunctor A ⋙ u ⊣ B.ι))

/-- The source's equivalence of conditions and its quotient/adjoint
conclusions for an admissible pair. -/
theorem summarize_admissible
    (A B : ObjectProperty C) [CategoryTheory.IsTriangulated C] :
    (AdmissiblePairConditionOne A B ↔
      AdmissiblePairConditionTwo A B) ∧
      (AdmissiblePairConditionTwo A B ↔
        AdmissiblePairConditionThree A B) ∧
      (AdmissiblePairConditionOne A B → AdmissiblePairConclusion A B) := by
  dsimp [AdmissiblePairConditionOne, AdmissiblePairConditionTwo]
  constructor
  · constructor
    · rintro ⟨⟨hAc, hAt, hAdj⟩, hBA⟩
      have : A.IsTriangulated := hAt
      have horth := orthogonal_triangulated A (by infer_instance)
      have hdecA : ∀ X : C, HasRightDecomposition A X :=
        (right_adjoint_iff_decomposition A).1 hAdj
      have hdecB : ∀ X : C, HasLeftDecomposition B X := by
        intro X
        obtain ⟨A', B', f, g, h, hT, hA', hB'⟩ := hdecA X
        have hB' : B B' := by
          rw [hBA]
          exact hB'
        refine ⟨A', B', f, g, h, hT, ?_, hB'⟩
        rw [hBA, ← right_adjoint_eq_left_orthogonal A hAdj hAc]
        simpa [hBA] using hA'
      have hBstrict : B.IsClosedUnderIsomorphisms := by
        rw [hBA]
        exact horth.1.1
      have hBtri : B.IsTriangulated := by
        rw [hBA]
        exact horth.1.2.2
      have : B.IsTriangulated := hBtri
      refine ⟨⟨hBstrict, hBtri, (left_adjoint_iff_decomposition B).2 hdecB⟩, ?_⟩
      simpa [hBA] using (right_adjoint_eq_left_orthogonal A hAdj hAc)
    · rintro ⟨⟨hBc, hBt, hBAdj⟩, hAB⟩
      have : B.IsTriangulated := hBt
      have horth := orthogonal_triangulated B (by infer_instance)
      have hdecB : ∀ X : C, HasLeftDecomposition B X :=
        (left_adjoint_iff_decomposition B).1 hBAdj
      have hdecA : ∀ X : C, HasRightDecomposition A X := by
        intro X
        obtain ⟨A', B', f, g, h, hT, hA', hB'⟩ := hdecB X
        have hBorth : rightOrthogonal A B' := by
          intro X₀ hX₀
          rw [hAB] at hX₀
          exact hX₀ B' hB'
        refine ⟨A', B', f, g, h, hT, ?_, hBorth⟩
        rw [hAB]
        exact hA'
      have hAstrict : A.IsClosedUnderIsomorphisms := by
        rw [hAB]
        exact horth.2.1
      have hAtri : A.IsTriangulated := by
        rw [hAB]
        exact horth.2.2.2
      have : A.IsTriangulated := hAtri
      refine ⟨⟨hAstrict, hAtri, (right_adjoint_iff_decomposition A).2 hdecA⟩, ?_⟩
      simpa [hAB] using (left_adjoint_eq_right_orthogonal B hBAdj hBc)
  · constructor
    · dsimp [AdmissiblePairConditionThree]
      constructor
      · rintro ⟨⟨hBc, hBt, hBAdj⟩, hAB⟩
        have : B.IsTriangulated := hBt
        have horth := orthogonal_triangulated B (by infer_instance)
        have hAstrict : A.IsClosedUnderIsomorphisms := by
          rw [hAB]
          exact horth.2.1
        have hAtri : A.IsTriangulated := by
          rw [hAB]
          exact horth.2.2.2
        have : A.IsTriangulated := hAtri
        have hdecB : ∀ X : C, HasLeftDecomposition B X :=
          (left_adjoint_iff_decomposition B).1 hBAdj
        refine ⟨hAstrict, hAtri, hBc, hBt, ?_, ?_⟩
        · intro X Y hX hY
          rw [hAB] at hX
          exact hX Y hY
        · intro X
          obtain ⟨A', B', f, g, h, hT, hA', hB'⟩ := hdecB X
          refine ⟨A', B', f, g, h, hT, ?_, hB'⟩
          rw [hAB]
          exact hA'
      · rintro ⟨hAc, hAt, hBc, hBt, hHom, hdec⟩
        have : B.IsTriangulated := hBt
        have hBAdj : HasLeftAdjoint B := by
          apply (left_adjoint_iff_decomposition B).2
          intro X
          obtain ⟨A', B', f, g, h, hT, hA', hB'⟩ := hdec X
          refine ⟨A', B', f, g, h, hT, ?_, hB'⟩
          intro Y hY
          exact hHom _ _ hA' hY
        refine ⟨⟨hBc, hBt, hBAdj⟩, ?_⟩
        apply le_antisymm
        · intro X hX Y hY f
          exact hHom _ _ hX hY f
        · intro X hX
          obtain ⟨A', B', f, g, h, hT, hA', hB'⟩ := hdec X
          have hg : g = 0 := hX B' hB' g
          have hBorth : rightOrthogonal A B' := by
            intro A₀ hA₀
            exact hHom _ _ hA₀ hB'
          have hzero : g ≫ 𝟙 B' = 0 := by
            rw [hg, zero_comp]
          obtain ⟨q, hq⟩ := Triangle.yoneda_exact₃ (Triangle.mk f g h) hT
            (𝟙 B') hzero
          let q' : A'⟦(1 : ℤ)⟧ ⟶ B' := by
            simpa only [Triangle.mk] using q
          have hq0 : q' = 0 :=
            hBorth (A'⟦(1 : ℤ)⟧)
              ((hAt.isStableUnderShiftBy (1 : ℤ)).le_shift _ hA') q'
          have hBid : 𝟙 B' = 0 := by
            calc
              𝟙 B' = h ≫ q' := by simpa [Triangle.mk, q'] using hq
              _ = 0 := by rw [hq0]; exact comp_zero
          have hfiso : IsIso f := (third_object_zero_characterization f).2.2 (by
            intro Z g' h' hT'
            obtain ⟨e, _, _⟩ := distinguished_cone_unique hT hT'
            let eB : Z ≅ B' :=
              { hom := e.inv.hom₃
                inv := e.hom.hom₃
                hom_inv_id := by exact e.inv_hom_id_triangle_hom₃
                inv_hom_id := by exact e.hom_inv_id_triangle_hom₃ }
            apply (IsZero.iff_id_eq_zero Z).mpr
            calc
              𝟙 Z = eB.hom ≫ eB.inv := eB.hom_inv_id.symm
              _ = eB.hom ≫ 𝟙 B' ≫ eB.inv := by simp
              _ = 0 := by simp [hBid])
          have hX' : A.isoClosure X :=
            ⟨A', hA', ⟨(@asIso _ _ _ _ f hfiso).symm⟩⟩
          obtain ⟨Z, hZ, ⟨e⟩⟩ := hX'
          exact @ObjectProperty.prop_of_iso _ _ A hAc _ _ e.symm hZ
    · intro h
      rcases h with ⟨hRA, hBA⟩
      rcases hRA with ⟨hAc, hAt, hAdj⟩
      subst B
      have : A.IsTriangulated := hAt
      have horth := orthogonal_triangulated A (by infer_instance)
      have hBstrict := horth.1.1
      have : (rightOrthogonal A).IsClosedUnderIsomorphisms := hBstrict
      have : (rightOrthogonal A).IsTriangulated := horth.1.2.2
      have hBsat : IsSaturated (rightOrthogonal A) := horth.1.2.1
      have hS :=
        (quotientMorphismProperty_isSaturated_iff (rightOrthogonal A)).2 hBsat
      rcases hAdj with ⟨v, ⟨adj⟩⟩
      let : v.CommShift ℤ := adj.rightAdjointCommShift ℤ
      have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
      have : v.IsTriangulated := adj.isTriangulated_rightAdjoint
      have hvzero : ∀ Z : C, rightOrthogonal A Z → IsZero (v.obj Z) := by
        intro Z hZ
        apply (IsZero.iff_id_eq_zero _).2
        have hc : adj.counit.app Z = 0 :=
          hZ (v.obj Z).obj (v.obj Z).property (adj.counit.app Z)
        have hi : (adj.homEquiv (v.obj Z) Z) (adj.counit.app Z) =
            𝟙 (v.obj Z) := by
          apply (adj.homEquiv (v.obj Z) Z).symm.injective
          rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
          simp
        calc
          𝟙 (v.obj Z) = (adj.homEquiv (v.obj Z) Z) (adj.counit.app Z) := hi.symm
          _ = (adj.homEquiv (v.obj Z) Z) 0 := by rw [hc]
          _ = 0 := adj.homAddEquiv_zero _ _
      have hInv :
          (quotientMorphismProperty (rightOrthogonal A)).IsInvertedBy v := by
        intro X Y f hf
        change (rightOrthogonal A).isoClosure.trW f at hf
        obtain ⟨Z, g, h, hT, hZ⟩ := hf
        obtain ⟨Z', hZ', ⟨e⟩⟩ := hZ
        have hZ'' : rightOrthogonal A Z :=
          @ObjectProperty.prop_of_iso _ _ (rightOrthogonal A)
            hBstrict _ _ e.symm hZ'
        have hT' := v.map_distinguished (Triangle.mk f g h) hT
        exact (Triangle.isZero₃_iff_isIso₁ _ hT').1 (hvzero Z hZ'')
      let vbar := quotientFactor (rightOrthogonal A) v hInv
      have hfac : quotientFunctor (rightOrthogonal A) ⋙ vbar = v :=
        quotientFactor_fac (rightOrthogonal A) v hInv
      have hadjbar : Nonempty
          (A.ι ⊣ quotientFunctor (rightOrthogonal A) ⋙ vbar) := by
        exact ⟨adj.ofNatIsoRight (eqToIso hfac).symm⟩
      have hdecA : ∀ X : C, HasRightDecomposition A X :=
        (right_adjoint_iff_decomposition A).1 ⟨v, ⟨adj⟩⟩
      have hcov : ∀ X : C, ∃ (X' : A.FullSubcategory)
          (s : A.ι.obj X' ⟶ X), quotientMorphismProperty (rightOrthogonal A) s := by
        intro X
        obtain ⟨A', B', f, g, h, hT, hA', hB'⟩ := hdecA X
        refine ⟨⟨A', hA'⟩, f, ?_⟩
        apply (quotientMorphismProperty_iff (rightOrthogonal A) f).2
        exact ⟨B', g, h, hT, ⟨B', hB', ⟨Iso.refl _⟩⟩⟩
      let F₀ := Formalization.Books.Derived.Unit05.fullSubcategoryLocalizationFunctor
        (quotientMorphismProperty (rightOrthogonal A)) A
      have hF₀ : F₀.IsEquivalence := by
        dsimp [F₀]
        exact Formalization.Books.Derived.Unit05.fullSubcategoryLocalization_isEquivalence
          hS A hcov
      let R := Formalization.Books.Derived.Unit05.restrictedMorphismProperty
        (quotientMorphismProperty (rightOrthogonal A)) A
      have hRiso : R ≤ MorphismProperty.isomorphisms A.FullSubcategory := by
        intro X Y f hf
        change quotientMorphismProperty (rightOrthogonal A) (A.ι.map f) at hf
        have hvf : IsIso (v.map (A.ι.map f)) := hInv (A.ι.map f) hf
        have : IsIso (v.map (A.ι.map f)) := hvf
        have : IsIso adj.unit := by infer_instance
        have : IsIso ((A.ι ⋙ v).map f) := by
          change IsIso (v.map (A.ι.map f))
          infer_instance
        have : IsIso (f ≫ adj.unit.app Y) := by
          change IsIso ((𝟭 A.FullSubcategory).map f ≫ adj.unit.app Y)
          rw [adj.unit.naturality]
          infer_instance
        exact IsIso.of_isIso_comp_right f (adj.unit.app Y)
      have : (𝟭 A.FullSubcategory).IsLocalization R :=
        Functor.IsLocalization.for_id R hRiso
      let eA : R.Localization ≌ A.FullSubcategory :=
        Localization.uniq R.Q (𝟭 A.FullSubcategory) R
      have : F₀.IsEquivalence := hF₀
      have hfac₀ : R.Q ⋙ F₀ = A.ι ⋙ quotientFunctor (rightOrthogonal A) := by
        dsimp [R, F₀,
          Formalization.Books.Derived.Unit05.fullSubcategoryLocalizationFunctor]
        exact Localization.Construction.fac _ _
      have hcomp : eA.inverse ⋙ F₀ ≅ A.ι ⋙ quotientFunctor (rightOrthogonal A) := by
        calc
          eA.inverse ⋙ F₀ ≅ (𝟭 A.FullSubcategory ⋙ eA.inverse) ⋙ F₀ :=
            Functor.isoWhiskerRight (Functor.leftUnitor eA.inverse).symm F₀
          _ ≅ R.Q ⋙ F₀ :=
            Functor.isoWhiskerRight (Localization.compUniqInverse
              R.Q (𝟭 A.FullSubcategory) R) F₀
          _ ≅ A.ι ⋙ quotientFunctor (rightOrthogonal A) := eqToIso hfac₀
      have hFeq : Functor.IsEquivalence
          (A.ι ⋙ quotientFunctor (rightOrthogonal A)) :=
        Functor.isEquivalence_of_iso hcomp
      have hAdj' : HasRightAdjoint A := ⟨v, ⟨adj⟩⟩
      have hEqA : A = leftOrthogonal (rightOrthogonal A) :=
        right_adjoint_eq_left_orthogonal A hAdj' hAc
      have hdecB : ∀ X : C, HasLeftDecomposition (rightOrthogonal A) X := by
        intro X
        obtain ⟨A', B', f, g, h, hT, hA', hB'⟩ := hdecA X
        refine ⟨A', B', f, g, h, hT, ?_, hB'⟩
        rw [← hEqA]
        exact hA'
      have hBleft : HasLeftAdjoint (rightOrthogonal A) :=
        (left_adjoint_iff_decomposition (rightOrthogonal A)).2 hdecB
      rcases hBleft with ⟨u, ⟨ladj⟩⟩
      let : u.CommShift ℤ := ladj.leftAdjointCommShift ℤ
      have : ladj.CommShift ℤ := ladj.commShift_of_rightAdjoint ℤ
      have : u.IsTriangulated := ladj.isTriangulated_leftAdjoint
      have huzero : ∀ Z : C, A Z → IsZero (u.obj Z) := by
        intro Z hZ
        apply (IsZero.iff_id_eq_zero _).2
        have hZ' : leftOrthogonal (rightOrthogonal A) Z := by
          exact hEqA ▸ hZ
        have hu : ladj.unit.app Z = 0 := by
          exact hZ' (u.obj Z).obj (u.obj Z).property (ladj.unit.app Z)
        have hi : (ladj.homEquiv Z (u.obj Z)).symm (ladj.unit.app Z) =
            𝟙 (u.obj Z) := by
          apply (ladj.homEquiv Z (u.obj Z)).injective
          rw [Equiv.apply_symm_apply, ladj.homEquiv_unit]
          simp
        calc
          𝟙 (u.obj Z) = (ladj.homEquiv Z (u.obj Z)).symm
              (ladj.unit.app Z) := hi.symm
          _ = (ladj.homEquiv Z (u.obj Z)).symm 0 := by rw [hu]
          _ = 0 := ladj.homAddEquiv_symm_zero _ _
      have hInvA : (quotientMorphismProperty A).IsInvertedBy u := by
        intro X Y f hf
        change A.isoClosure.trW f at hf
        obtain ⟨Z, g, h, hT, hZ⟩ := hf
        obtain ⟨Z', hZ', ⟨e⟩⟩ := hZ
        have hZ'' : A Z :=
          @ObjectProperty.prop_of_iso _ _ A hAc _ _ e.symm hZ'
        have hT' := u.map_distinguished (Triangle.mk f g h) hT
        exact (Triangle.isZero₃_iff_isIso₁ _ hT').1 (huzero Z hZ'')
      have hSiff : ∀ (X Y : C) (f : X ⟶ Y),
          quotientMorphismProperty A f ↔ IsIso (u.map f) := by
        intro X Y f
        constructor
        · intro hf
          exact hInvA f hf
        · intro hf
          have : IsIso (u.map f) := hf
          obtain ⟨Z, g, h, hT⟩ := distinguished_cone_exists f
          have hT' := u.map_distinguished (Triangle.mk f g h) hT
          have hUZ : IsZero (u.obj Z) :=
            (Triangle.isZero₃_iff_isIso₁ _ hT').2 hf
          have hZA' : leftOrthogonal (rightOrthogonal A) Z := by
            intro X' hX' k
            have hk : (ladj.homEquiv Z ⟨X', hX'⟩).symm k = 0 := by
              calc
                (ladj.homEquiv Z ⟨X', hX'⟩).symm k =
                    𝟙 (u.obj Z) ≫
                      (ladj.homEquiv Z ⟨X', hX'⟩).symm k := by simp
                _ = 0 := by rw [(IsZero.iff_id_eq_zero _).1 hUZ, zero_comp]
            calc
              k = (ladj.homEquiv Z ⟨X', hX'⟩)
                  ((ladj.homEquiv Z ⟨X', hX'⟩).symm k) :=
                (Equiv.apply_symm_apply _ k).symm
              _ = (ladj.homEquiv Z ⟨X', hX'⟩) 0 := by rw [hk]
              _ = 0 := ladj.homAddEquiv_zero _ _
          have hZA : A Z := hEqA.symm ▸ hZA'
          apply (quotientMorphismProperty_iff A f).2
          exact ⟨Z, g, h, hT, ⟨Z, hZA, ⟨Iso.refl _⟩⟩⟩
      let ubar := quotientFactor A u hInvA
      have hfacA : quotientFunctor A ⋙ ubar = u :=
        quotientFactor_fac A u hInvA
      have hleftAdj : Nonempty (quotientFunctor A ⋙ ubar ⊣ (rightOrthogonal A).ι) := by
        exact ⟨ladj.ofNatIsoLeft (eqToIso hfacA).symm⟩
      let W := (MorphismProperty.isomorphisms (rightOrthogonal A).FullSubcategory).inverseImage u
      have hW : W = quotientMorphismProperty A := by
        ext X Y f
        change IsIso (u.map f) ↔ quotientMorphismProperty A f
        exact (hSiff X Y f).symm
      have : u.IsLocalization (quotientMorphismProperty A) := by
        rw [← hW]
        exact ladj.isLocalization_leftAdjoint'
      let eB : quotientCategory A ≌ (rightOrthogonal A).FullSubcategory :=
        Localization.uniq (quotientFunctor A) u (quotientMorphismProperty A)
      have hcompB : u ⋙ eB.inverse ≅ quotientFunctor A :=
        Localization.compUniqInverse (quotientFunctor A) u
          (quotientMorphismProperty A)
      have : IsIso ladj.counit := by infer_instance
      have hjeq : (rightOrthogonal A).ι ⋙ quotientFunctor A ≅ eB.inverse := by
        calc
          (rightOrthogonal A).ι ⋙ quotientFunctor A ≅
              (rightOrthogonal A).ι ⋙ (u ⋙ eB.inverse) :=
            Functor.isoWhiskerLeft (rightOrthogonal A).ι hcompB.symm
          _ ≅ ((rightOrthogonal A).ι ⋙ u) ⋙ eB.inverse :=
            (Functor.associator _ _ _).symm
          _ ≅ (𝟭 (rightOrthogonal A).FullSubcategory) ⋙ eB.inverse :=
            Functor.isoWhiskerRight (asIso ladj.counit) eB.inverse
          _ ≅ eB.inverse := Functor.leftUnitor _
      have hBeq : Functor.IsEquivalence
          ((rightOrthogonal A).ι ⋙ quotientFunctor A) :=
        Functor.isEquivalence_of_iso hjeq.symm
      exact ⟨hFeq, hBeq, ⟨vbar, hadjbar⟩, ⟨ubar, hleftAdj⟩⟩

end AdmissibleSubcategories

end Formalization.Books.Derived.Unit40
