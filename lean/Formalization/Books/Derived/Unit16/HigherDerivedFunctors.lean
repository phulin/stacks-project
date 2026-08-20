import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Formalization.Books.Derived.Unit16.Core

/-!
# Derived Categories, Chapter 16: higher derived functors

The declarations below follow the numbered statements in the source.  The
proofs are intentionally deferred; the interfaces retain the source's
hypotheses and use the canonical derived-category objects from `Core`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit14
open Formalization.Books.Derived.Unit16
open Formalization.Books.Homology.Unit07
open Formalization.Books.Homology.Unit12
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u w' v' u'

namespace Formalization.Books.Derived.Unit16

/-! ## 16.1. Negative vanishing -/

/-- Negative cohomology remains zero after applying a right derived functor.

The source allows a partially defined derived functor here; the selected
`RightDerivedFunctorData` is the chapter's interface for its value on all of
`D⁺`. -/
theorem rightDerived_negative_vanishing
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F)
    (K : DPlus A) (a : ℤ)
    (hK : ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.Plus.homologyFunctor A i).obj K)) :
    ∀ i : ℤ, i < a →
      IsZero (rightDerivedCohomology R.functor K i) := by
  sorry

/-- Truncating a bounded-below derived object above degree `a` does not
  change the cohomology of its right derived image through degree `a`. -/
theorem rightDerived_truncation_cohomology_iso
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F)
    (K : DPlus A) (a : ℤ) :
    ∀ i : ℤ, i ≤ a →
      IsIso ((DerivedCategory.Plus.homologyFunctor B i).map
        (R.functor.map (derivedPlusTruncLEMap K a))) := by
  /-
  Prior attempt: apply exactness to the canonical truncation triangle, use
  negative vanishing for its third term, and conclude from the long exact
  cohomology sequence.  The attempt did not elaborate because the current
  t-structure, shift, and homology-sequence interfaces do not line up with
  the selected `RightDerivedFunctorData` without the missing pointwise
  derived-value comparison.

  obtain ⟨eR⟩ := R.exact
  haveI : R.functor.CommShift ℤ := eR.commShift
  haveI : R.functor.IsTriangulated := eR.isTriangulated
  intro i hi
  let T := (DerivedCategory.Plus.TStructure.t.triangleLEGT a).obj K
  have hT : T ∈ distTriang (DPlus A) :=
    DerivedCategory.Plus.TStructure.t.triangleLEGT_distinguished a K
  have hT₃ : T.obj₃.IsGE (a + 1) := by
    dsimp [T]
    infer_instance
  letI : T.obj₃.IsGE (a + 1) := hT₃
  let U : Triangle (DPlus B) := R.functor.mapTriangle.obj T
  have hU : U ∈ distTriang (DPlus B) := R.functor.map_distinguished T hT
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let hfive := H.homologySequenceComposableArrows₅ U (i - 1) i (by lia)
  have hneg₁ : IsZero ((H.shift (i - 1)).obj U.obj₃) := by
    have h := rightDerived_negative_vanishing
      R T.obj₃ (a + 1) (by
        intro j hj
        exact (DerivedCategory.Plus.isZero_homology_of_isGE T.obj₃
          (a + 1) j hj)) (i - 1) (by lia)
    change IsZero (rightDerivedCohomology R.functor T.obj₃ (i - 1))
    exact h
  have hneg₂ : IsZero ((H.shift i).obj U.obj₃) := by
    have h := rightDerived_negative_vanishing
      R T.obj₃ (a + 1) (by
        intro j hj
        exact (DerivedCategory.Plus.isZero_homology_of_isGE T.obj₃
          (a + 1) j hj)) i (by lia)
    change IsZero (rightDerivedCohomology R.functor T.obj₃ i)
    exact h
  have hδ : ((H.shift (i - 1)).map U.mor₂) ≫
      H.homologySequenceδ U (i - 1) i (by lia) = 0 := by
    apply hneg₁.eq_of_src
  have hnext : ((H.shift i).map U.mor₂) = 0 :=
    by
      apply hneg₂.eq_of_src
  have hmono : Mono ((H.shift i).map U.mor₁) := by
    let h₃ := hfive.exact 3
    exact h₃.mono_g hδ
  have hepi : Epi ((H.shift i).map U.mor₁) := by
    let h₄ := hfive.exact 4
    exact h₄.epi_f hnext
  letI : Mono ((H.shift i).map U.mor₁) := hmono
  letI : Epi ((H.shift i).map U.mor₁) := hepi
  have : IsIso ((H.shift i).map U.mor₁) := by infer_instance
  simpa [H, U, T, derivedPlusTruncLEMap] using this
  -/
  sorry

/-! ## 16.2. Higher derived functors -/

/-- The source's definition `RⁱF = Hⁱ ∘ RF`, evaluated on objects of `A` in
  degree zero. -/
theorem higherRightDerivedFunctor_is_the_source_definition
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] (R : RightDerivedFunctorData F) (i : ℤ) :
    (higherRightDerivedFunctor F R.functor i) =
      (DerivedCategory.Plus.singleFunctor A 0 ⋙ R.functor ⋙
        DerivedCategory.Plus.homologyFunctor B i) :=
  rfl

/-! ## 16.3. Left exact functors and their higher derived functors -/

/-- All negative higher right derived functors vanish. -/
theorem higherRightDerivedFunctor_vanishes_below_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F) :
    ∀ i : ℤ, i < 0 → ∀ X : A,
      IsZero ((higherRightDerivedFunctor F R.functor i).obj X) := by
  intro i hi X
  refine rightDerived_negative_vanishing
    R ((DerivedCategory.Plus.singleFunctor A 0).obj X) 0 ?_ i hi
  intro j hj
  exact DerivedCategory.Plus.isZero_homology_of_isGE
    ((DerivedCategory.Plus.singleFunctor A 0).obj X) 0 j hj

/-- The zeroth right derived functor is left exact. -/
theorem higherRightDerivedFunctor_zero_is_left_exact
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F) :
    IsLeftExact (higherRightDerivedFunctor F R.functor 0) := by
  /-
  Prior attempt: map the single-triangle associated to a short exact
  sequence, use negative vanishing in the resulting long exact sequence,
  and identify the two exact short complexes.  The attempt was retained
  here because its current errors are interface mismatches, not a changed
  theorem statement.

  obtain ⟨eR⟩ := R.exact
  haveI : R.functor.CommShift ℤ := eR.commShift
  haveI : R.functor.IsTriangulated := eR.isTriangulated
  apply (left_exact_iff_maps_short_exact_on_left _).2
  intro S hS
  let X : A ⥤ DPlus A := DerivedCategory.Plus.singleFunctor A 0
  let δ : X.obj S.X₃ ⟶
      (shiftFunctor (DPlus A) (1 : ℤ)).obj (X.obj S.X₁) :=
    DerivedCategory.Plus.ι.preimage
      (hS.singleTriangle.mor₃ ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app (X.obj S.X₁))
  let T : Triangle (DPlus A) :=
    Triangle.mk (X.map S.f) (X.map S.g) δ
  have hT : T ∈ distTriang (DPlus A) := by
    apply (Functor.map_distinguished_iff DerivedCategory.Plus.ι T).1
    simpa [T, δ, X, Functor.mapTriangle,
      ShortComplex.ShortExact.singleTriangle] using hS.singleTriangle_distinguished
  let U : Triangle (DPlus B) := R.functor.mapTriangle.obj T
  have hU : U ∈ distTriang (DPlus B) := R.functor.map_distinguished T hT
  let H := DerivedCategory.Plus.homologyFunctor B 0
  have hfive := H.homologySequenceComposableArrows₅ U (-1) 0 (by simp)
  have hneg : IsZero ((H.shift (-1)).obj U.obj₃) := by
    have h := rightDerived_negative_vanishing
      R (X.obj S.X₃) 0 (by
        intro j hj
        exact DerivedCategory.Plus.isZero_homology_of_isGE
          (X.obj S.X₃) 0 j hj) (-1) (by omega)
    simpa [H, U, T, X] using h
  rw [ComposableArrows.exact_iff_δ₀]
  constructor
  · change (ShortComplex.mk (0 : (0 : B) ⟶ _)
      (H.map (R.functor.map (X.map S.f))) _).Exact
    let e : ShortComplex.mk (0 : (0 : B) ⟶ _)
        (H.map (R.functor.map (X.map S.f))) _ ≅
        ShortComplex.mk ((H.shift (-1)).map U.mor₃)
          ((H.shift 0).map U.mor₁) _ :=
      ShortComplex.isoMk hneg.isoZero.symm (Iso.refl _) (Iso.refl _)
        (by simp) (by simp)
    apply (ShortComplex.exact_iff_of_iso e).2
    exact hfive.exact 3
  · change (ShortComplex.mk (H.map (R.functor.map (X.map S.f)))
      (H.map (R.functor.map (X.map S.g))) _).Exact
    simpa [H, U, T, X] using hfive.exact 4
  -/
  sorry

/-- The canonical map `F ⟶ R⁰F` is an isomorphism exactly when `F` is left
  exact. -/
theorem rightDerived_zero_comparison_isIso_iff_left_exact
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F) :
    IsIso R.zeroComparison ↔ IsLeftExact F := by
  sorry

/-! ## 16.4. Acyclic objects -/

/-- The derived-category criterion for a right acyclic object. -/
theorem rightAcyclic_iff_zero_comparison_and_positive_vanishing
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F) (X : A) :
    RightAcyclic R X ↔
      IsIso (R.zeroComparison.app X) ∧
        ∀ i : ℤ, 0 < i →
          IsZero ((higherRightDerivedFunctor F R.functor i).obj X) := by
  sorry

/-- For a left exact functor, positive-degree vanishing is equivalent to
  right acyclicity. -/
theorem rightAcyclic_iff_positive_vanishing_of_left_exact
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F)
    (hF : IsLeftExact F) (X : A) :
    RightAcyclic R X ↔
      ∀ i : ℤ, 0 < i →
        IsZero ((higherRightDerivedFunctor F R.functor i).obj X) := by
  sorry

/-! ## 16.5. Acyclic short exact sequences -/

/-- The three two-out-of-three acyclicity criteria for a short exact
  sequence, together with exactness after applying `F`. -/
theorem rightAcyclic_shortExact_two_out_of_three
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F)
    (hF : IsLeftExact F) (S : ShortComplex A) (hS : S.ShortExact) :
    ((RightAcyclic R S.X₁ ∧ RightAcyclic R S.X₃) →
      RightAcyclic R S.X₂ ∧ (S.map F).ShortExact) ∧
    ((RightAcyclic R S.X₁ ∧ RightAcyclic R S.X₂) →
      RightAcyclic R S.X₃ ∧ (S.map F).ShortExact) ∧
    ((RightAcyclic R S.X₂ ∧ RightAcyclic R S.X₃ ∧ Epi (F.map S.g)) →
      RightAcyclic R S.X₁ ∧ (S.map F).ShortExact) := by
  sorry

/-! ## 16.6. The right derived delta-functor -/

/-- The right derived functors carry canonical connecting morphisms and form
  a cohomological delta-functor. -/
theorem rightDerived_deltaFunctor_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F) :
    Nonempty (RightDerivedDeltaFunctorData R) := by
  sorry

/-- A right derived delta-functor is universal when every object embeds in a
  right acyclic object. -/
theorem rightDerived_deltaFunctor_universal
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F)
    (Δ : RightDerivedDeltaFunctorData R)
    (hA : InjectsIntoRightAcyclic R) :
    (rightDerivedDeltaFunctor R Δ).IsUniversal := by
  sorry

/-! ## 16.7. The Leray acyclicity lemma -/

/-- A bounded-below complex of pointwise right acyclic objects computes the
  pointwise right derived functor. -/
theorem rightDerived_leray_acyclicity
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] (K : CompPlus A)
    (hK : AllTermsRightAcyclicForF F K)
    (hDefined :
      RightDerivedPlusDefined F ((HomotopyCategory.Plus.quotient A).obj K)) :
    ComputesRightDerived (quasiIsoPlusProperty A)
      (boundedQuasiIsoProperty_properties A).1 (rightDerivedInputFunctor F)
      ((HomotopyCategory.Plus.quotient A).obj K) := by
  sorry

/-! ## 16.8. Enough acyclic objects -/

/-- Enough right acyclic objects make the right derived functor everywhere
  defined on `D⁺`, exact, and computable on bounded-below acyclic
  complexes. -/
theorem enough_right_acyclics
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] :
    InjectsIntoRightAcyclicForF F →
      ∃ R : RightDerivedFunctorData F,
        InjectsIntoRightAcyclic R ∧
          ∀ K : CompPlus A,
            AllTermsRightAcyclic R K → ComputesRightDerivedComplex R K := by
  sorry

/-- The dual enough-left-acyclic statement for `D⁻`. -/
theorem enough_left_acyclics
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] :
    QuotientOfLeftAcyclicForF F →
      ∃ L : LeftDerivedFunctorData F,
        QuotientOfLeftAcyclic L ∧
          ∀ K : CompMinus A,
            AllTermsLeftAcyclic L K → ComputesLeftDerivedComplex L K := by
  sorry

/-! ## 16.9. Exact functors -/

/-- An exact functor has no higher derived terms: its bounded and unbounded
  right derived functors are everywhere defined, every object is acyclic, all
  complexes compute them, and only degree zero survives in the bounded
  theory. -/
theorem exactFunctor_rightDerived_consequences
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsExact F) :
    letI : F.Additive := left_or_right_exact_additive F (Or.inl hF.1)
    ∃ R : RightDerivedFunctorData F,
      (∀ X : A, RightAcyclic R X) ∧
        (∀ i : ℤ, i ≠ 0 → ∀ X : A,
          IsZero ((higherRightDerivedFunctor F R.functor i).obj X)) ∧
        ∃ U : UnboundedRightDerivedFunctorData F,
          UnboundedRightDerivedRestricts R U ∧
            ∀ K : BookComplex A, ComputesUnboundedRightDerivedComplex U K := by
  sorry

end Formalization.Books.Derived.Unit16
