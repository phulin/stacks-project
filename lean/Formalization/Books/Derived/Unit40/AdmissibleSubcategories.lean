import Formalization.Books.Derived.Unit06.Quotients
import Mathlib.CategoryTheory.Adjunction.Additive
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
      letI : e.functor.Additive := by
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
    letI : e.symm.functor.Additive := by
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
      letI : P.IsStableUnderShift ℤ := hP'
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
      letI : P.IsStableUnderShift ℤ := hP'
      infer_instance
  · refine ⟨?_, ?_, ?_⟩
    · rw [hleft]
      letI : P.IsStableUnderShift ℤ := hP'
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
      letI : P.IsStableUnderShift ℤ := hP'
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
    exact shift_right (first_case (rot_of_distTriang _ hT) h₂₃.1 h₂₃.2) (-1 : ℤ)

/-- Right-adjoint decompositions are closed under binary direct sums. -/
theorem prepare_adjoint_biproduct
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    {X Y : C} (hX : HasRightDecomposition P X)
    (hY : HasRightDecomposition P Y) :
    HasRightDecomposition P (X ⊞ Y) := by
  sorry

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
  sorry

/-- Left-adjoint decompositions are closed under binary direct sums. -/
theorem prepare_adjoint_dual_biproduct
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    {X Y : C} (hX : HasLeftDecomposition P X)
    (hY : HasLeftDecomposition P Y) :
    HasLeftDecomposition P (X ⊞ Y) := by
  sorry

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
  sorry

/-- A right adjoint makes the subcategory saturated. -/
theorem right_adjoint_saturated
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasRightAdjoint P) :
    IsSaturated P := by
  sorry

/-- Under strict fullness, a right-admissible subcategory is the left
orthogonal of its right orthogonal. -/
theorem right_adjoint_eq_left_orthogonal
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasRightAdjoint P)
    (hstrict : P.IsClosedUnderIsomorphisms) :
    P = leftOrthogonal (rightOrthogonal P) := by
  sorry

/-- A left adjoint of the inclusion is equivalent to left decompositions. -/
theorem left_adjoint_iff_decomposition
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C] :
    HasLeftAdjoint P ↔ ∀ X : C, HasLeftDecomposition P X := by
  sorry

/-- A left adjoint makes the subcategory saturated. -/
theorem left_adjoint_saturated
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasLeftAdjoint P) :
    IsSaturated P := by
  sorry

/-- Under strict fullness, a left-admissible subcategory is the right
orthogonal of its left orthogonal. -/
theorem left_adjoint_eq_right_orthogonal
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasLeftAdjoint P)
    (hstrict : P.IsClosedUnderIsomorphisms) :
    P = rightOrthogonal (leftOrthogonal P) := by
  sorry

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
  sorry

/-- Left admissibility can equivalently be expressed by decompositions. -/
theorem left_admissible_iff_decomposition
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C] :
    LeftAdmissible P ↔
      P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧
        (∀ X : C, HasLeftDecomposition P X) := by
  sorry

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
  sorry

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
  sorry

end AdmissibleSubcategories

end Formalization.Books.Derived.Unit40
