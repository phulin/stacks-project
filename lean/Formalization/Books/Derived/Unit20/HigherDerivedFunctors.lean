import Formalization.Books.Derived.Unit20.RightDerivedProperties
import Formalization.Books.Derived.Unit16.HigherDerivedFunctors
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Homology.Unit07.AdditiveFunctors
import Formalization.Books.Homology.Unit12.CohomologicalDeltaFunctors
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Derived Categories, Chapter 20: higher derived functors

The higher derived functors are defined by applying the canonical cohomology
functors to the bounded-below right-derived functor.  Long exact sequences are
represented by the finite exact windows supplied by Mathlib's homological
functor API.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit07
open Formalization.Books.Homology.Unit12
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w w'

namespace Formalization.Books.Derived.Unit20

/-! ## The higher derived functors -/

/-- The bounded-below right-derived functor attached to a left exact functor,
using the canonical additivity consequence for functors between abelian
categories. -/
noncomputable def leftExactRightDerivedComplexFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) :
    CompPlus A ⥤ DPlus B := by
  let hAdd : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  letI : F.Additive := hAdd
  exact rightDerivedComplexFunctor F

/-- The integer-indexed higher right-derived functor `R^i F`. -/
noncomputable def higherRightDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) (i : ℤ) : A ⥤ B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  exact
    DerivedCategory.Plus.singleFunctor A 0 ⋙
      F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor B i

/-- The triangle in `D⁺(B)` whose cohomology sequence is the long sequence
attached to a short exact sequence of bounded-below complexes. -/
noncomputable def rightDerivedTriangle
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {S : ShortComplex (CompPlus A)}
    (δ : (leftExactRightDerivedComplexFunctor F hF).obj S.X₃ ⟶
      (shiftFunctor (DPlus B) (1 : ℤ)).obj
        ((leftExactRightDerivedComplexFunctor F hF).obj S.X₁)) :
    Triangle (DPlus B) :=
  Triangle.mk
    ((leftExactRightDerivedComplexFunctor F hF).map S.f)
    ((leftExactRightDerivedComplexFunctor F hF).map S.g)
    δ

/-- A finite exact window of the long cohomology sequence associated to a
right-derived triangle. -/
noncomputable def rightDerivedLongExactWindow
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {S : ShortComplex (CompPlus A)}
    (δ : (leftExactRightDerivedComplexFunctor F hF).obj S.X₃ ⟶
      (shiftFunctor (DPlus B) (1 : ℤ)).obj
        ((leftExactRightDerivedComplexFunctor F hF).obj S.X₁))
    (n : ℤ) : ComposableArrows B 5 :=
  (DerivedCategory.Plus.homologyFunctor B 0).homologySequenceComposableArrows₅
    (rightDerivedTriangle F hF δ) n (n + 1) rfl

/-- A short exact sequence of bounded-below complexes has the associated long
exact cohomology sequence after applying the right-derived functor. -/
theorem rightDerived_shortExact_longExact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {S : ShortComplex (CompPlus A)} (hS : S.ShortExact) :
    ∃ δ : (leftExactRightDerivedComplexFunctor F hF).obj S.X₃ ⟶
      (shiftFunctor (DPlus B) (1 : ℤ)).obj
        ((leftExactRightDerivedComplexFunctor F hF).obj S.X₁),
      rightDerivedTriangle F hF δ ∈ distTriang (DPlus B) ∧
        ∀ n : ℤ, (rightDerivedLongExactWindow F hF δ n).Exact := by
  let hAdd : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  obtain ⟨d⟩ := @rightDerivedComplexFunctor_isDeltaFunctor A _ _ _ B _ _ _ _ F hAdd
  refine ⟨d.delta S hS, ?_, ?_⟩
  · exact d.distinguished S hS
  · intro n
    exact (DerivedCategory.Plus.homologyFunctor B 0).homologySequenceComposableArrows₅_exact
      (rightDerivedTriangle F hF (d.delta S hS)) (d.distinguished S hS) n (n + 1) rfl

/-! ## Normalizations and universality -/

private noncomputable def leftExactRightDerivedSourceIso
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) (hAdd : F.Additive) :
    F ≅ @Formalization.Books.Derived.Unit16.rightDerivedSourceCohomology
      A _ _ B _ _ _ _ F hAdd := by
  letI : F.Additive := hAdd
  have eMap :
      HomotopyCategory.Plus.singleFunctor A 0 ⋙ F.mapHomotopyCategoryPlus ≅
        F ⋙ HomotopyCategory.Plus.singleFunctor B 0 := by
    refine NatIso.ofComponents (fun X => ?_) ?_
    · exact (HomotopyCategory.Plus.fullyFaithfulι B).preimageIso (by
        change
          (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((CochainComplex.singleFunctor A 0).obj X)) ≅
            (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor B 0).obj (F.obj X))
        exact
          (HomotopyCategory.quotient B (ComplexShape.up ℤ)).mapIso
            ((HomologicalComplex.singleMapHomologicalComplex
              F (ComplexShape.up ℤ) 0).app X))
    · intro X Y f
      apply (HomotopyCategory.Plus.fullyFaithfulι B).map_injective
      change
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
                ((CochainComplex.singleFunctor A 0).map f)) ≫
            (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
              ((HomologicalComplex.singleMapHomologicalComplex
                F (ComplexShape.up ℤ) 0).hom.app Y) =
          (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
              ((HomologicalComplex.singleMapHomologicalComplex
                F (ComplexShape.up ℤ) 0).hom.app X) ≫
            (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
              ((CochainComplex.singleFunctor B 0).map (F.map f))
      convert congrArg (fun k =>
          (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map k)
          ((HomologicalComplex.singleMapHomologicalComplex
            F (ComplexShape.up ℤ) 0).hom.naturality f) using 1 <;>
        simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  have eB :
      HomotopyCategory.Plus.singleFunctor B 0 ⋙
          DerivedCategory.Plus.Qh ⋙
            DerivedCategory.Plus.homologyFunctor B 0 ≅ 𝟭 B := by
    let e₀ :
        (HomotopyCategory.Plus.singleFunctor B 0 ⋙
            (DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι)) ⋙
            DerivedCategory.homologyFunctor B 0 ≅
          (HomotopyCategory.Plus.singleFunctor B 0 ⋙
            (HomotopyCategory.Plus.ι B ⋙ DerivedCategory.Qh)) ⋙
            DerivedCategory.homologyFunctor B 0 :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (HomotopyCategory.Plus.singleFunctor B 0)
          (DerivedCategory.Plus.QhCompιIsoιCompQh B))
        (DerivedCategory.homologyFunctor B 0)
    exact
      (Functor.associator
        (HomotopyCategory.Plus.singleFunctor B 0)
        (DerivedCategory.Plus.Qh (C := B))
        (DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor B 0)).symm ≪≫
        (Functor.associator
          (HomotopyCategory.Plus.singleFunctor B 0 ⋙
            DerivedCategory.Plus.Qh (C := B))
          DerivedCategory.Plus.ι
          (DerivedCategory.homologyFunctor B 0)).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.associator
            (HomotopyCategory.Plus.singleFunctor B 0)
            (DerivedCategory.Plus.Qh (C := B))
            DerivedCategory.Plus.ι)
          (DerivedCategory.homologyFunctor B 0) ≪≫
        e₀ ≪≫
        Functor.isoWhiskerRight
          (Functor.associator
            (HomotopyCategory.Plus.singleFunctor B 0)
            (HomotopyCategory.Plus.ι B)
            (DerivedCategory.Qh (C := B))).symm
          (DerivedCategory.homologyFunctor B 0) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerRight
          (HomotopyCategory.Plus.singleFunctorCompιIso B 0)
          (DerivedCategory.Qh (C := B) ⋙
            DerivedCategory.homologyFunctor B 0) ≪≫
        DerivedCategory.singleFunctorCompHomologyFunctorIso B 0
  exact
    (Functor.isoWhiskerRight eMap
        (DerivedCategory.Plus.Qh (C := B) ⋙
          DerivedCategory.Plus.homologyFunctor B 0) ≪≫
      Functor.isoWhiskerLeft F eB ≪≫
      Functor.rightUnitor F).symm

/-- Objectwise vanishing of a functor. -/
def FunctorObjectwiseIsZero
    {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B]
    (G : A ⥤ B) : Prop :=
  ∀ X : A, IsZero (G.obj X)

/-- The family of higher right-derived functors, with its universal
cohomological δ-functor structure. -/
def IsUniversalHigherRightDerivedDeltaFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) : Prop :=
  ∃ G : CohomologicalDeltaFunctor A B,
    G.IsUniversal ∧
      ∀ n : ℕ, G.functor n = higherRightDerivedFunctor F hF (n : ℤ)

/-- Negative higher right-derived functors vanish. -/
theorem higherRightDerivedFunctor_isZero_of_negative
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) (i : ℤ) (hi : i < 0) :
    FunctorObjectwiseIsZero (higherRightDerivedFunctor F hF i) := by
  intro X
  let hAdd : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  have hFzero : CategoryTheory.Functor.PreservesZeroMorphisms F := by
    constructor
    intro U V
    apply add_left_cancel (a := F.map (0 : U ⟶ V))
    exact (hAdd.map_add (f := (0 : U ⟶ V)) (g := (0 : U ⟶ V))).symm.trans
      (by simp)
  let K : DPlus A := (DerivedCategory.Plus.singleFunctor A 0).obj X
  let hK : K.IsGE 0 := by
    infer_instance
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    @DerivedCategory.Plus.exists_injective_nonempty_iso A _ _ _ _ K 0 hK
  let J : KPlus A :=
    (HomotopyCategory.Plus.quotient A).obj
      ((InjectiveObject.ι A).mapCochainComplexPlus.obj L)
  have hsource :
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj J).IsGE 0 := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    apply (DerivedCategory.isGE_Q_obj_iff
      ((F.mapCochainComplexPlus.obj
        ((InjectiveObject.ι A).mapCochainComplexPlus.obj L)).obj) 0).2
    apply (CochainComplex.isGE_iff _ 0).2
    intro j hj
    have hzeroI : IsZero (L.obj.X j) :=
      hL.1 j (by
        simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hj)
    have hzeroA : IsZero ((InjectiveObject.ι A).obj (L.obj.X j)) := by
      exact Functor.map_isZero _ hzeroI
    exact HomologicalComplex.ExactAt.of_isZero
      (@Functor.map_isZero _ _ _ _ _ _ F hFzero _
        (by simpa using hzeroA))
  let RF :=
    @Functor.rightDerivedFunctorPlus A B _ _ _ _ _ _ F hAdd _
  have hunit :
      IsIso ((@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ _ _ F hAdd _).app J) :=
    inferInstance
  have htargetJ :
      (RF.obj ((DerivedCategory.Plus.Qh (C := A)).obj J)).IsGE 0 :=
    { ge := (DerivedCategory.Plus.TStructure.t.ge 0).prop_of_iso
        (asIso ((@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ _ _ F hAdd _).app J))
        hsource.ge }
  have hRFiso :
      RF.obj ((DerivedCategory.Plus.Qh (C := A)).obj J) ≅ RF.obj K := by
    change RF.obj ((DerivedCategory.Plus.Q (C := A)).obj
        ((InjectiveObject.ι A).mapCochainComplexPlus.obj L)) ≅ RF.obj K
    exact RF.mapIso e
  have htarget : (RF.obj K).IsGE 0 :=
    { ge := (DerivedCategory.Plus.TStructure.t.ge 0).prop_of_iso
        hRFiso htargetJ.ge }
  exact @DerivedCategory.Plus.isZero_homology_of_isGE B _ _ _ (RF.obj K) 0 htarget i hi

/-- The degree-zero higher right-derived functor is naturally isomorphic to
the original left exact functor. -/
theorem higherRightDerivedFunctor_zero_iso
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) :
    Nonempty (higherRightDerivedFunctor F hF 0 ≅ F) := by
  let hAdd : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  letI : F.Additive := hAdd
  let RF := @Functor.rightDerivedFunctorPlus A B _ _ _ _ _ _ F hAdd _
  let R : Formalization.Books.Derived.Unit16.RightDerivedFunctorData F :=
    { functor := RF
      unit := @Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ _ _ F hAdd _
      isRightDerived := by
        change
          (@Functor.rightDerivedFunctorPlus A B _ _ _ _ _ _ F hAdd _).IsRightDerivedFunctor
            (@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ _ _ F hAdd _)
            (quasiIsoPlusProperty A)
        infer_instance
      exact := rightDerivedFunctorPlus_isExact F
      zeroSourceIso := leftExactRightDerivedSourceIso F hF hAdd }
  have hR : IsIso R.zeroComparison := by
    apply
      (Formalization.Books.Derived.Unit16.rightDerived_zero_comparison_isIso_iff_left_exact R).2
    exact hF
  exact ⟨(asIso R.zeroComparison).symm⟩

/-- Positive higher right-derived functors vanish on injective objects. -/
theorem higherRightDerivedFunctor_obj_isZero_of_injective
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    (i : ℤ) (hi : 0 < i) (I : A) [Injective I] :
    IsZero ((higherRightDerivedFunctor F hF i).obj I) := by
  let hAdd : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  have hFzero : CategoryTheory.Functor.PreservesZeroMorphisms F := by
    constructor
    intro U V
    apply add_left_cancel (a := F.map (0 : U ⟶ V))
    exact (hAdd.map_add (f := (0 : U ⟶ V)) (g := (0 : U ⟶ V))).symm.trans
      (by simp)
  let L : CochainComplex.Plus (InjectiveObject A) :=
    ⟨(HomologicalComplex.single (InjectiveObject A) (ComplexShape.up ℤ) 0).obj
        ⟨I, inferInstance⟩, ⟨0, inferInstance⟩⟩
  let J : KPlus A :=
    (HomotopyCategory.Plus.quotient A).obj
      ((InjectiveObject.ι A).mapCochainComplexPlus.obj L)
  let K : DPlus A :=
    (DerivedCategory.Plus.singleFunctor A 0).obj I
  have e0 :
      (DerivedCategory.Q (C := A)).obj
          ((InjectiveObject.ι A).mapCochainComplexPlus.obj L).obj ≅
        (DerivedCategory.singleFunctor A 0).obj I := by
    dsimp [L]
    change
      (DerivedCategory.Q (C := A)).obj
          (((InjectiveObject.ι A).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (InjectiveObject A)
              (ComplexShape.up ℤ) 0).obj ⟨I, inferInstance⟩)) ≅
        (DerivedCategory.singleFunctor A 0).obj I
    exact
      (DerivedCategory.Q (C := A)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (InjectiveObject.ι A) (ComplexShape.up ℤ) 0).app
          ⟨I, inferInstance⟩)
  have e : (DerivedCategory.Plus.Qh.obj J) ≅ K := by
    apply DerivedCategory.Plus.ι.preimageIso
    exact
      (DerivedCategory.quotientCompQhIso A).app
          ((InjectiveObject.ι A).mapCochainComplexPlus.obj L).obj ≪≫
        e0 ≪≫
        asIso ((DerivedCategory.Plus.singleFunctorιIso A 0).inv.app I)
  have hsource :
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj J).IsLE 0 := by
    rw [← DerivedCategory.Plus.isLE_ι_obj_iff]
    apply (DerivedCategory.isLE_Q_obj_iff
      ((F.mapCochainComplexPlus.obj
        ((InjectiveObject.ι A).mapCochainComplexPlus.obj L)).obj) 0).2
    apply (CochainComplex.isLE_iff _ 0).2
    intro j hj
    have hzeroI : IsZero (L.obj.X j) := by
      dsimp [L]
      exact HomologicalComplex.isZero_single_obj_X
        (c := ComplexShape.up ℤ) (j := 0)
        (A := (⟨I, inferInstance⟩ : InjectiveObject A)) (i := j)
        (by omega)
    have hzeroA : IsZero ((InjectiveObject.ι A).obj (L.obj.X j)) := by
      exact Functor.map_isZero _ hzeroI
    exact HomologicalComplex.ExactAt.of_isZero
      (@Functor.map_isZero _ _ _ _ _ _ F hFzero _
        (by simpa using hzeroA))
  let RF :=
    @Functor.rightDerivedFunctorPlus A B _ _ _ _ _ _ F hAdd _
  have hRFiso :
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj J) ≅ RF.obj K := by
    exact
      asIso ((@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ _ _ F hAdd _).app J) ≪≫
        RF.mapIso e
  have htarget : (RF.obj K).IsLE 0 :=
    { le := (DerivedCategory.Plus.TStructure.t.le 0).prop_of_iso
        hRFiso hsource.le }
  exact @DerivedCategory.Plus.isZero_homology_of_isLE B _ _ _ (RF.obj K) 0 htarget i hi

/-- The higher right-derived functors form the universal cohomological
δ-functor extending `F`. -/
theorem higherRightDerivedFunctor_universal
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) :
    IsUniversalHigherRightDerivedDeltaFunctor F hF := by
  let hAdd : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  letI : F.Additive := hAdd
  let RF := @Functor.rightDerivedFunctorPlus A B _ _ _ _ _ _ F hAdd _
  let R : Formalization.Books.Derived.Unit16.RightDerivedFunctorData F :=
    { functor := RF
      unit := @Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ _ _ F hAdd _
      isRightDerived := by
        change
          (@Functor.rightDerivedFunctorPlus A B _ _ _ _ _ _ F hAdd _).IsRightDerivedFunctor
            (@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ _ _ F hAdd _)
            (quasiIsoPlusProperty A)
        infer_instance
      exact := rightDerivedFunctorPlus_isExact F
      zeroSourceIso := leftExactRightDerivedSourceIso F hF hAdd }
  have hR : IsIso R.zeroComparison := by
    apply
      (Formalization.Books.Derived.Unit16.rightDerived_zero_comparison_isIso_iff_left_exact R).2
    exact hF
  have hA : Formalization.Books.Derived.Unit16.InjectsIntoRightAcyclic R := by
    intro X
    obtain ⟨p⟩ := EnoughInjectives.presentation X
    refine ⟨p.J, p.f, inferInstance, ?_⟩
    apply
      (Formalization.Books.Derived.Unit16.rightAcyclic_iff_zero_comparison_and_positive_vanishing
        R p.J).2
    refine ⟨inferInstance, ?_⟩
    intro i hi
    exact higherRightDerivedFunctor_obj_isZero_of_injective F hF i hi p.J
  obtain ⟨Δ⟩ := Formalization.Books.Derived.Unit16.rightDerived_deltaFunctor_exists R
  have hU :=
    Formalization.Books.Derived.Unit16.rightDerived_deltaFunctor_universal R Δ hA
  refine ⟨Formalization.Books.Derived.Unit16.rightDerivedDeltaFunctor R Δ, hU, ?_⟩
  intro n
  rfl

end Formalization.Books.Derived.Unit20
