import Formalization.Books.Derived.Unit20.InjectiveResolutions
import Formalization.Books.Derived.Unit04.ElementaryResults
import Formalization.Books.Derived.Unit12.CanonicalDeltaFunctor
import Formalization.Books.Derived.Unit03.Definitions
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Derived Categories, Chapter 20: properties of right derived functors

The canonical bounded-below right-derived functor is used throughout.  The
exactness and δ-functor assertions are retained as interfaces for the prove
stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit03
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit14
open Formalization.Books.Derived.Unit20
open Formalization.Books.Categories.Unit22
open Formalization.Books.Categories.Unit27
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w w'

namespace Formalization.Books.Derived.Unit20

/-! ## The induced functors -/

/-- The right derived functor on bounded-below complexes. -/
noncomputable abbrev rightDerivedComplexFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    CompPlus A ⥤ DPlus B :=
  DerivedCategory.Plus.Q (C := A) ⋙ F.rightDerivedFunctorPlus

/-- The right derived functor after passing from complexes to the homotopy
category. -/
noncomputable abbrev rightDerivedHomotopyFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    KPlus A ⥤ DPlus B :=
  DerivedCategory.Plus.Qh (C := A) ⋙ F.rightDerivedFunctorPlus

/-- The right derived functor restricted to stalk complexes in degree zero. -/
noncomputable abbrev rightDerivedObjectFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    A ⥤ DPlus B :=
  DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus

/-! ## Exactness and δ-functors -/

/-- The canonical right-derived functor is exact on the bounded-below derived
categories.  The shift-commutation datum is exposed explicitly because
Mathlib's right-derived construction does not yet install it as a global
instance. -/
theorem rightDerivedFunctorPlus_isExact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    Nonempty (ExactTriangulatedFunctorData F.rightDerivedFunctorPlus) := by
  let : Formalization.Books.Homology.Unit03.AdditiveCategory (DPlus B) := {
    toPreadditive := inferInstance,
    toHasFiniteProducts := inferInstance }
  let : Formalization.Books.Homology.Unit03.AdditiveCategory (DPlus A) := {
    toPreadditive := inferInstance,
    toHasFiniteProducts := inferInstance }
  let hF : Nonempty (ExactTriangulatedFunctorData (rightDerivedSourceFunctor F)) := by
    have hP : Nonempty (ExactTriangulatedFunctorData F.mapHomotopyCategoryPlus) :=
      (additive_homotopy_functors_are_exact F).2.1
    obtain ⟨hP⟩ := hP
    let : F.mapHomotopyCategoryPlus.CommShift ℤ := hP.commShift
    have hPT : F.mapHomotopyCategoryPlus.IsTriangulated := hP.isTriangulated
    let : F.mapHomotopyCategoryPlus.IsTriangulated := hPT
    let hG : (rightDerivedSourceFunctor F).CommShift ℤ := by
      dsimp [rightDerivedSourceFunctor]
      infer_instance
    let : (rightDerivedSourceFunctor F).CommShift ℤ := hG
    have hT : (rightDerivedSourceFunctor F).IsTriangulated := by
      dsimp [rightDerivedSourceFunctor]
      infer_instance
    exact ⟨{ commShift := hG, isTriangulated := hT }⟩
  obtain ⟨hF⟩ := hF
  let : (rightDerivedSourceFunctor F).CommShift ℤ := hF.commShift
  let hFT : (rightDerivedSourceFunctor F).IsTriangulated := hF.isTriangulated
  let : (rightDerivedSourceFunctor F).IsTriangulated := hFT
  let hS : Formalization.Books.Categories.Unit27.SaturatedMultiplicativeSystem
      (quasiIsoPlusProperty A) := (boundedQuasiIsoProperty_properties A).1
  let _ : Formalization.Books.Categories.Unit27.LeftMultiplicativeSystem
      (quasiIsoPlusProperty A) := hS.1.1
  let _ : Formalization.Books.Categories.Unit27.RightMultiplicativeSystem
      (quasiIsoPlusProperty A) := hS.1.2
  let _ : Formalization.Books.Derived.Unit05.CompatibleWithTriangulation
      (quasiIsoPlusProperty A) := by
    change MorphismProperty.IsCompatibleWithTriangulation
      (HomotopyCategory.Plus.quasiIso A)
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  have hDef : Formalization.Books.Derived.Unit14.RightDerivable
      (quasiIsoPlusProperty A) hS
      (rightDerivedSourceFunctor F) :=
    rightDerived_everywhere_defined_of_enoughInjectives
      (rightDerivedSourceFunctor F) ⟨hF⟩
  obtain ⟨hP, hG⟩ := Formalization.Books.Derived.Unit14.rightDerivedFunctor_isExact hS
    (rightDerivedSourceFunctor F)
  obtain ⟨hG, hGT0⟩ := hG
  let P := Formalization.Books.Derived.Unit14.rightDerivedProperty
    (quasiIsoPlusProperty A) hS
    (rightDerivedSourceFunctor F)
  let J : (KPlus A) ⥤ P.FullSubcategory :=
    P.lift (𝟭 (KPlus A)) hDef
  let eJ : J ⋙ P.ι ≅ 𝟭 (KPlus A) := P.liftCompιIso (𝟭 _) hDef
  let hJ : J.CommShift ℤ := by
    let : P.ι.CommShift ℤ := inferInstance
    let : (𝟭 (KPlus A)).CommShift ℤ := inferInstance
    exact Functor.CommShift.ofComp eJ ℤ
  let : P.IsTriangulated := hP
  let : J.CommShift ℤ := hJ
  let : NatTrans.CommShift eJ.hom ℤ := Functor.CommShift.ofComp_compatibility eJ ℤ
  have hJT : J.IsTriangulated := by
    have hcomp : (J ⋙ P.ι).IsTriangulated := by
      rw [Functor.isTriangulated_iff_of_iso eJ]
      infer_instance
    constructor
    intro T hT
    rw [← P.ι.map_distinguished_iff]
    exact isomorphic_distinguished _ (hcomp.map_distinguished T hT) _
      ((Functor.mapTriangleCompIso J P.ι).app T).symm
  let hG' : (J ⋙ Formalization.Books.Derived.Unit14.rightDerivedFunctor
      (quasiIsoPlusProperty A) hS
      (rightDerivedSourceFunctor F)).CommShift ℤ := by
    let : (Formalization.Books.Derived.Unit14.rightDerivedFunctor
      (quasiIsoPlusProperty A) hS
      (rightDerivedSourceFunctor F)).CommShift ℤ := hG
    infer_instance
  let : (J ⋙ Formalization.Books.Derived.Unit14.rightDerivedFunctor
      (quasiIsoPlusProperty A) hS
      (rightDerivedSourceFunctor F)).CommShift ℤ := hG'
  have hGT : (J ⋙ Formalization.Books.Derived.Unit14.rightDerivedFunctor
      (quasiIsoPlusProperty A) hS
      (rightDerivedSourceFunctor F)).IsTriangulated := by
    let : P.IsTriangulated := hP
    let : (Formalization.Books.Derived.Unit14.rightDerivedFunctor
      (quasiIsoPlusProperty A) hS
      (rightDerivedSourceFunctor F)).CommShift ℤ := hG
    let : (Formalization.Books.Derived.Unit14.rightDerivedFunctor
      (quasiIsoPlusProperty A) hS
      (rightDerivedSourceFunctor F)).IsTriangulated := hGT0
    infer_instance
  let G0 : KPlus A ⥤ DPlus B :=
    J ⋙ Formalization.Books.Derived.Unit14.rightDerivedFunctor
      (quasiIsoPlusProperty A) hS
      (rightDerivedSourceFunctor F)
  have hG0 : Nonempty (ExactTriangulatedFunctorData G0) :=
    ⟨{ commShift := hG', isTriangulated := hGT }⟩
  obtain ⟨hG0⟩ := hG0
  let : G0.CommShift ℤ := hG0.commShift
  let hG0T : G0.IsTriangulated := hG0.isTriangulated
  let : G0.IsTriangulated := hG0T
  let β : rightDerivedSourceFunctor F ⟶ G0 := {
    app := fun X => Formalization.Books.Derived.Unit14.rightDerivedCanonicalMap
      (quasiIsoPlusProperty A) hS (rightDerivedSourceFunctor F) X (hDef X)
    naturality := by
      intro X Y f
      dsimp [G0, J, P, Formalization.Books.Derived.Unit14.rightDerivedFunctor,
        Formalization.Books.Derived.Unit14.rightDerivedEverywhereFunctor]
      let q : Formalization.Books.Derived.Unit14.RightDerivedSquare
          (quasiIsoPlusProperty A) f := {
        source := Formalization.Books.Derived.Unit14.rightDerivedIdentityIndex
          (quasiIsoPlusProperty A) X
        target := Formalization.Books.Derived.Unit14.rightDerivedIdentityIndex
          (quasiIsoPlusProperty A) Y
        dotted := f
        comm := by
          change (𝟙 X) ≫ f = f ≫ (𝟙 Y)
          simp }
      have hJobj (Z : KPlus A) :
          ((P.lift (𝟭 (KPlus A)) hDef).obj Z).obj = Z := by
        rfl
      have hJmap {Z W : KPlus A} (g : Z ⟶ W) :
          ((P.lift (𝟭 (KPlus A)) hDef).map g).hom = g := by
        rfl
      convert (Formalization.Books.Derived.Unit14.rightDerivedMap_condition hS
        (rightDerivedSourceFunctor F) f (hDef X) (hDef Y) q) using 1 ;
        simp [Formalization.Books.Derived.Unit14.rightDerivedCanonicalMap,
          Formalization.Books.Derived.Unit14.rightDerivedValue,
          Formalization.Books.Derived.Unit14.rightDerivedDiagram,
          Formalization.Books.Derived.Unit14.rightDerivedIdentityIndex,
          P, q, MorphismProperty.Under.mk] ;
        constructor <;> intro h <;>
          simpa [hJobj, hJmap, J, P, G0] using h }
  have hβ : ∀ (Y : HomotopyCategory.Plus (InjectiveObject A)),
      IsIso (β.app ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Y)) := by
    intro Y
    let _ : Formalization.Books.Homology.Unit03.AdditiveCategory (InjectiveObject A) := {
      toPreadditive := inferInstance,
      toHasFiniteProducts := inferInstance }
    obtain ⟨I, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective Y
    let K : CompPlus A :=
      (InjectiveObject.ι A).mapCochainComplexPlus.obj I
    have hI : IsTermwiseInjectiveComplex
        K := by
      intro n
      change Injective ((InjectiveObject.ι A).obj (I.obj.X n))
      infer_instance
    let X : KPlus A := (HomotopyCategory.Plus.quotient A).obj K
    have hobj :
        (HomotopyCategory.Plus.quotient A).obj
            ((InjectiveObject.ι A).mapCochainComplexPlus.obj I) =
          (InjectiveObject.ι A).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient (InjectiveObject A)).obj I) := by
      rfl
    have hXiso : IsIso (Formalization.Books.Derived.Unit14.rightDerivedCanonicalMap
        (quasiIsoPlusProperty A) hS (rightDerivedSourceFunctor F)
        ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient (InjectiveObject A)).obj I))
        (hDef ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient (InjectiveObject A)).obj I)))) := by
      let S : MorphismProperty (KPlus A) := quasiIsoPlusProperty A
      let Qh := DerivedCategory.Plus.Qh (C := A)
      let _ : Formalization.Books.Categories.Unit27.LeftMultiplicativeSystem S := hS.1.1
      let _ : IsFiltered (Formalization.Books.Categories.Unit27.LeftDenominatorCategory S X) :=
        Formalization.Books.Categories.Unit27.left_denominator_category_is_filtered X
      have hK : CochainComplex.IsKInjective X.1.as := by
        change CochainComplex.IsKInjective K.obj
        obtain ⟨n, hn⟩ := K.property
        let _ : K.obj.IsStrictlyGE n := hn
        let _ : ∀ n : ℤ, Injective (K.obj.X n) := hI
        exact CochainComplex.isKInjective_of_injective K.obj n
      have hRetract : ∀ s : Formalization.Books.Categories.Unit27.LeftDenominatorCategory S X,
          ∃ r : s.right ⟶ X, s.hom ≫ r = 𝟙 X := by
        intro s
        let _ : IsIso (Qh.map s.hom) := Localization.inverts Qh S s.hom s.prop
        obtain ⟨r, hr⟩ :=
          (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective s.right X hK).surjective
            (inv (Qh.map s.hom))
        refine ⟨r, ?_⟩
        apply
          (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective X X hK).injective
        rw [Functor.map_comp, hr]
        simp
      let r : ∀ s : Formalization.Books.Categories.Unit27.LeftDenominatorCategory S X, s.right ⟶ X :=
        fun s => (hRetract s).choose
      have hr (s : Formalization.Books.Categories.Unit27.LeftDenominatorCategory S X) : s.hom ≫ r s = 𝟙 X :=
        (hRetract s).choose_spec
      have hRetractUnique (s : Formalization.Books.Categories.Unit27.LeftDenominatorCategory S X)
          (a b : s.right ⟶ X) (ha : s.hom ≫ a = 𝟙 X)
          (hb : s.hom ≫ b = 𝟙 X) : a = b := by
        let _ : IsIso (Qh.map s.hom) := Localization.inverts Qh S s.hom s.prop
        apply
          (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective s.right X hK).injective
        apply (cancel_epi (Qh.map s.hom)).1
        rw [← Qh.map_comp, ← Qh.map_comp, ha, hb]
      let M := Formalization.Books.Derived.Unit14.rightDerivedDiagram S
        (rightDerivedSourceFunctor F) X
      let c : Cocone M :=
        { pt := (rightDerivedSourceFunctor F).obj X
          ι :=
            { app := fun s => (rightDerivedSourceFunctor F).map (r s)
              naturality := by
                intro s t f
                change (rightDerivedSourceFunctor F).map f.right ≫
                    (rightDerivedSourceFunctor F).map (r t) =
                  (rightDerivedSourceFunctor F).map (r s) ≫ 𝟙 _
                simp only [Category.comp_id]
                rw [← (rightDerivedSourceFunctor F).map_comp]
                exact congrArg (fun q => (rightDerivedSourceFunctor F).map q)
                  (hRetractUnique s (f.right ≫ r t) (r s)
                    (by rw [← Category.assoc, MorphismProperty.Under.w f, hr])
                    (hr s)) } }
      let hX' : rightDerivedDefined S hS (rightDerivedSourceFunctor F) X :=
        ⟨c, by
          have hr₀ : r (rightDerivedIdentityIndex S X) = 𝟙 X := by
            apply hRetractUnique (rightDerivedIdentityIndex S X)
              (r (rightDerivedIdentityIndex S X)) (𝟙 X)
            · exact hr (rightDerivedIdentityIndex S X)
            · change (𝟙 X) ≫ 𝟙 X = 𝟙 X
              simp
          refine ⟨rightDerivedIdentityIndex S X, 𝟙 _, ?_, ?_⟩
          · change 𝟙 ((rightDerivedSourceFunctor F).obj X) ≫
                (rightDerivedSourceFunctor F).map
              (r (rightDerivedIdentityIndex S X)) = 𝟙 _
            rw [hr₀]
            simp
          · intro j
            let g : j ⟶ rightDerivedIdentityIndex S X :=
              MorphismProperty.Under.homMk (r j) (hr j)
            refine ⟨rightDerivedIdentityIndex S X, 𝟙 _, g, ?_⟩
            dsimp [rightDerivedIdentityIndex, MorphismProperty.Under.mk]
            dsimp [M, c, g, Formalization.Books.Derived.Unit14.rightDerivedDiagram,
              rightDerivedIdentityIndex,
              MorphismProperty.Under.mk]
            simp⟩
      have hc' : IsEssentiallyConstantInd M
          (rightDerivedCocone S hS (rightDerivedSourceFunctor F) X hX') := by
        exact Classical.choose_spec hX'
      obtain ⟨i, s, hs, hfactor⟩ := hc'
      let gi : i ⟶ rightDerivedIdentityIndex S X :=
        MorphismProperty.Under.homMk (r i) (hr i)
      have hgi : M.map gi ≫
          (rightDerivedCocone S hS (rightDerivedSourceFunctor F) X hX').ι.app
            (rightDerivedIdentityIndex S X) =
          (rightDerivedCocone S hS (rightDerivedSourceFunctor F) X hX').ι.app i := by
        exact (rightDerivedCocone S hS (rightDerivedSourceFunctor F) X hX').w gi
      obtain ⟨k, f, g, hfg⟩ := hfactor (rightDerivedIdentityIndex S X)
      let gk : k ⟶ rightDerivedIdentityIndex S X :=
        MorphismProperty.Under.homMk (r k) (hr k)
      have hgk : g ≫ gk = 𝟙 (rightDerivedIdentityIndex S X) := by
        dsimp [rightDerivedIdentityIndex, MorphismProperty.Under.mk] at g gk ⊢
        apply MorphismProperty.Under.Hom.ext
        rw [MorphismProperty.Comma.comp_right]
        dsimp [MorphismProperty.Under.homMk]
        change g.right ≫ r k = 𝟙 X
        have hg : g.right = k.hom := by
          simpa using MorphismProperty.Under.w g
        rw [hg, hr k]
      let a := (rightDerivedCocone S hS (rightDerivedSourceFunctor F) X hX').ι.app
        (rightDerivedIdentityIndex S X)
      let b := s ≫ M.map gi
      let q := s ≫ M.map f ≫ M.map gk
      have hba : b ≫ a = 𝟙 _ := by
        dsimp [b]
        rw [Category.assoc, hgi, hs]
      have haq : a ≫ q = 𝟙 (M.obj (rightDerivedIdentityIndex S X)) := by
        calc
          a ≫ q = (a ≫ s ≫ M.map f) ≫ M.map gk := by simp [q, Category.assoc]
          _ = M.map g ≫ M.map gk := by rw [hfg]
          _ = M.map (g ≫ gk) := by rw [M.map_comp]
          _ = 𝟙 _ := by rw [hgk]; simp
      have hbq : b = q := by
        calc
          b = b ≫ 𝟙 _ := by simp
          _ = b ≫ (a ≫ q) := by rw [haq]
          _ = (b ≫ a) ≫ q := by simp [Category.assoc]
          _ = q := by rw [hba]; apply Category.id_comp
      have ha : IsIso a := by
        let _ : IsIso a := IsIso.mk ⟨q, haq, by rw [← hbq, hba]; simp⟩
        infer_instance
      have haFinal : IsIso ((rightDerivedCocone S hS
          (rightDerivedSourceFunctor F) X hX').ι.app
            (rightDerivedIdentityIndex S X)) := by
        simpa [a, rightDerivedIdentityIndex, MorphismProperty.Under.mk] using ha
      let Y : KPlus A :=
        (HomotopyCategory.Plus.quotient A).obj
          ((InjectiveObject.ι A).mapCochainComplexPlus.obj I)
      let hD0 : rightDerivedDefined S hS (rightDerivedSourceFunctor F) Y :=
        hDef ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient (InjectiveObject A)).obj I))
      rw [← hobj]
      change IsIso ((rightDerivedSourceFunctor F).map (𝟙 Y) ≫
        (rightDerivedCocone S hS (rightDerivedSourceFunctor F) Y hD0).ι.app
          (rightDerivedIdentityIndex S Y))
      exact IsIso.comp_isIso'
        (Functor.map_isIso (rightDerivedSourceFunctor F) (𝟙 Y)) haFinal
    dsimp [β, G0, J, P, Functor.mapHomotopyCategoryPlus]
    exact hXiso
  have hInv : (quasiIsoPlusProperty A).IsInvertedBy G0 := by
    have hInv0 := Formalization.Books.Derived.Unit14.rightDerivedEverywhereFunctor_inverts
      hS (rightDerivedSourceFunctor F) hDef
    intro X Y f hf
    dsimp [G0, J, P, Formalization.Books.Derived.Unit14.rightDerivedFunctor,
      Formalization.Books.Derived.Unit14.rightDerivedEverywhereFunctor]
    exact hInv0 f hf
  let H : DPlus A ⥤ DPlus B :=
    Localization.lift G0 hInv (DerivedCategory.Plus.Qh (C := A))
  let eH : DerivedCategory.Plus.Qh (C := A) ⋙ H ≅ G0 :=
    Localization.Lifting.iso (DerivedCategory.Plus.Qh (C := A))
      (quasiIsoPlusProperty A) G0 H
  let hHC : H.CommShift ℤ := by
    let : G0.CommShift ℤ := hG0.commShift
    exact Functor.commShiftOfLocalization
      (DerivedCategory.Plus.Qh (C := A)) (quasiIsoPlusProperty A) ℤ G0 H
  let : H.CommShift ℤ := hHC
  let : ∀ n : ℤ, (shiftFunctor (DPlus A) n).Additive := by
    intro n
    have := Functor.additive_of_iso
      ((ObjectProperty.ι ((DerivedCategory.TStructure.t (C := A)).plus)).commShiftIso n).symm
    apply Functor.additive_of_comp_faithful
      (shiftFunctor (DPlus A) n)
      (ObjectProperty.ι ((DerivedCategory.TStructure.t (C := A)).plus))
  let : NatTrans.CommShift eH.hom ℤ := by
    dsimp [eH]
    infer_instance
  have hHT : H.IsTriangulated := by
    let : G0.IsTriangulated := hG0T
    apply Functor.isTriangulated_of_precomp_iso eH
  let α : rightDerivedSourceFunctor F ⟶
      DerivedCategory.Plus.Qh (C := A) ⋙ H := β ≫ eH.inv
  have hHright : H.IsRightDerivedFunctor
      (F := rightDerivedSourceFunctor F)
      (L := DerivedCategory.Plus.Qh (C := A)) α
        (quasiIsoPlusProperty A) := by
    apply (HomotopyCategory.Plus.localizerMorphism_derives
      (rightDerivedSourceFunctor F)).isRightDerivedFunctor_of_isIso α
    intro Y
    dsimp [α]
    let : IsIso (β.app ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Y)) := hβ Y
    infer_instance
  let S : MorphismProperty (KPlus A) := quasiIsoPlusProperty A
  have hHrightS : H.IsRightDerivedFunctor
      (F := rightDerivedSourceFunctor F)
      (L := DerivedCategory.Plus.Qh (C := A)) α
        S := by simpa [S] using hHright
  have instHright : H.IsRightDerivedFunctor
      (F := rightDerivedSourceFunctor F)
      (L := DerivedCategory.Plus.Qh (C := A)) α S := hHrightS
  have : H.IsRightDerivedFunctor α S := hHrightS
  have instCanonical : F.rightDerivedFunctorPlus.IsRightDerivedFunctor
      F.rightDerivedFunctorPlusUnit S := by infer_instance
  have : F.rightDerivedFunctorPlus.IsRightDerivedFunctor
      (F := rightDerivedSourceFunctor F)
      (L := DerivedCategory.Plus.Qh (C := A)) F.rightDerivedFunctorPlusUnit S := by
    simpa [rightDerivedSourceFunctor] using instCanonical
  let eRF : F.rightDerivedFunctorPlus ≅ H :=
    Functor.rightDerivedUnique (F := rightDerivedSourceFunctor F)
      (L := DerivedCategory.Plus.Qh (C := A)) F.rightDerivedFunctorPlus H
      F.rightDerivedFunctorPlusUnit α S
  let hRF : F.rightDerivedFunctorPlus.CommShift ℤ :=
    Functor.CommShift.ofIso eRF.symm ℤ
  let : F.rightDerivedFunctorPlus.CommShift ℤ := hRF
  let : NatTrans.CommShift eRF.symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility eRF.symm ℤ
  let : NatTrans.CommShift eRF.hom ℤ :=
    NatTrans.CommShift.of_iso_inv eRF.symm ℤ
  have hRFT : F.rightDerivedFunctorPlus.IsTriangulated := by
    rw [Functor.isTriangulated_iff_of_iso eRF]
    exact hHT
  exact ⟨{ commShift := hRF, isTriangulated := hRFT }⟩

/-- The right-derived functor induces an exact functor from `K⁺(A)` to
`D⁺(B)`. -/
theorem rightDerivedHomotopyFunctor_isExact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    Nonempty (ExactTriangulatedFunctorData (rightDerivedHomotopyFunctor F)) := by
  obtain ⟨hF⟩ := rightDerivedFunctorPlus_isExact F
  let : F.rightDerivedFunctorPlus.CommShift ℤ := hF.commShift
  let hT : F.rightDerivedFunctorPlus.IsTriangulated := hF.isTriangulated
  let : F.rightDerivedFunctorPlus.IsTriangulated := hT
  exact ⟨{ commShift := by infer_instance, isTriangulated := by infer_instance }⟩

/-- The right-derived functor on bounded-below complexes carries the
canonical δ-functor structure. -/
theorem rightDerivedComplexFunctor_isDeltaFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    Nonempty (DeltaFunctor (rightDerivedComplexFunctor F)) := by
  obtain ⟨hRF⟩ := rightDerivedFunctorPlus_isExact F
  let : F.rightDerivedFunctorPlus.CommShift ℤ := hRF.commShift
  let : F.rightDerivedFunctorPlus.IsTriangulated := hRF.isTriangulated
  let d := Classical.choice
    (Formalization.Books.Derived.Unit12.canonicalPlusFunctor_isDeltaFunctor A)
  refine ⟨{
    delta := fun S hS =>
      F.rightDerivedFunctorPlus.map (d.delta S hS) ≫
        (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.Plus.Q (C := A)).obj S.X₁)
    distinguished := by
      intro S hS
      change Triangle.mk
          (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.Q (C := A)).map S.f))
          (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.Q (C := A)).map S.g))
          (F.rightDerivedFunctorPlus.map (d.delta S hS) ≫
            (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app
              ((DerivedCategory.Plus.Q (C := A)).obj S.X₁)) ∈
        distTriang (DPlus B)
      exact F.rightDerivedFunctorPlus.map_distinguished
        (Triangle.mk ((DerivedCategory.Plus.Q (C := A)).map S.f)
          ((DerivedCategory.Plus.Q (C := A)).map S.g) (d.delta S hS))
        (d.distinguished S hS)
    naturality := by
      intro S₁ S₂ φ h₁ h₂
      dsimp
      rw [← Category.assoc, ← F.rightDerivedFunctorPlus.map_comp,
        d.naturality φ h₁ h₂, F.rightDerivedFunctorPlus.map_comp]
      rw [Category.assoc]
      have hcomm := (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.naturality
        ((DerivedCategory.Plus.Q (C := A)).map φ.τ₁)
      have hcomm' := congrArg
        (fun k => F.rightDerivedFunctorPlus.map (d.delta S₁ h₁) ≫ k) hcomm
      simp [Category.assoc] at hcomm' ⊢
  }⟩

/-- The right-derived functor on objects carries the induced δ-functor
structure. -/
theorem rightDerivedObjectFunctor_isDeltaFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    Nonempty (DeltaFunctor (rightDerivedObjectFunctor F)) := by
  obtain ⟨d⟩ := rightDerivedComplexFunctor_isDeltaFunctor F
  let K : A ⥤ CompPlus A :=
    (CochainComplex.plus A).lift (CochainComplex.singleFunctor A 0) (by
      intro X
      exact ⟨0, inferInstance⟩)
  let : K.PreservesZeroMorphisms := by
    dsimp [K, ObjectProperty.lift]
    constructor
    intro X Y
    exact congrArg (fun f => ObjectProperty.homMk f)
      (Functor.map_zero (CochainComplex.singleFunctor A 0) X Y)
  have hmap : ∀ (S : ShortComplex A), S.ShortExact →
      (S.map K).ShortExact := by
    intro S hS
    dsimp [K, ObjectProperty.lift]
    let _ : PreservesFiniteLimits (CochainComplex.singleFunctor A 0) := by
      dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
      infer_instance
    let _ : PreservesFiniteColimits (CochainComplex.singleFunctor A 0) := by
      dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
      infer_instance
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (CochainComplex.plus A).ι
    simpa [K, ObjectProperty.lift, ShortComplex.map] using
      hS.map_of_exact (CochainComplex.singleFunctor A 0)
  let e : K ⋙ DerivedCategory.Plus.Q (C := A) ≅
      DerivedCategory.Plus.singleFunctor A 0 := by
    let i : ∀ X : A,
        (DerivedCategory.Plus.ι).obj ((K ⋙ DerivedCategory.Plus.Q).obj X) ≅
          (DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor A 0).obj X) :=
      fun X => by
        change
          (DerivedCategory.Q (C := A)).obj ((K.obj X).obj) ≅
            (DerivedCategory.singleFunctor A 0).obj X
        dsimp [K]
        exact Iso.refl _
    refine NatIso.ofComponents (fun X => (DerivedCategory.Plus.ι).preimageIso (i X)) ?_
    intro X Y f
    apply (DerivedCategory.Plus.ι).map_injective
    simp only [Functor.map_comp]
    have hY :
        (DerivedCategory.Plus.ι).map
            ((DerivedCategory.Plus.ι).preimageIso (i Y)).hom = (i Y).hom := by
      change (DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.ι).preimage (i Y).hom) = (i Y).hom
      exact CategoryTheory.Functor.map_preimage
        (F := DerivedCategory.Plus.ι (C := A)) (i Y).hom
    have hX :
        (DerivedCategory.Plus.ι).map
            ((DerivedCategory.Plus.ι).preimageIso (i X)).hom = (i X).hom := by
      change (DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.ι).preimage (i X).hom) = (i X).hom
      exact CategoryTheory.Functor.map_preimage
        (F := DerivedCategory.Plus.ι (C := A)) (i X).hom
    rw [hY, hX]
    dsimp [i]
    have hKmap : K.map f =
        ObjectProperty.homMk ((CochainComplex.singleFunctor A 0).map f) := by
      rfl
    change
      (DerivedCategory.Plus.Q.map (K.map f)).hom ≫
          𝟙 _ =
        𝟙 _ ≫ ((DerivedCategory.Plus.singleFunctor A 0).map f).hom
    simp only [Category.comp_id, Category.id_comp]
    rw [hKmap]
    rfl
  let dK : DeltaFunctor (K ⋙ rightDerivedComplexFunctor F) := {
    delta := fun S hS => d.delta (S.map K) (hmap S hS)
    distinguished := by
      intro S hS
      exact d.distinguished (S.map K) (hmap S hS)
    naturality := by
      intro S₁ S₂ φ h₁ h₂
      exact d.naturality ((Functor.mapShortComplex K).map φ)
        (hmap S₁ h₁) (hmap S₂ h₂) }
  let eRF : K ⋙ rightDerivedComplexFunctor F ≅
      rightDerivedObjectFunctor F := by
    dsimp [rightDerivedComplexFunctor, rightDerivedObjectFunctor]
    exact Functor.isoWhiskerRight e F.rightDerivedFunctorPlus
  refine ⟨{
    delta := fun S hS =>
      (eRF.app S.X₃).inv ≫ dK.delta S hS ≫
        (shiftFunctor (DPlus B) (1 : ℤ)).map (eRF.app S.X₁).hom
    distinguished := by
      intro S hS
      apply isomorphic_distinguished _ (dK.distinguished S hS) _
      exact (Triangle.isoMk
          (Triangle.mk ((K ⋙ rightDerivedComplexFunctor F).map S.f)
            ((K ⋙ rightDerivedComplexFunctor F).map S.g) (dK.delta S hS))
          (Triangle.mk ((rightDerivedObjectFunctor F).map S.f)
            ((rightDerivedObjectFunctor F).map S.g)
            ((eRF.app S.X₃).inv ≫ dK.delta S hS ≫
              (shiftFunctor (DPlus B) (1 : ℤ)).map (eRF.app S.X₁).hom))
          (eRF.app S.X₁) (eRF.app S.X₂) (eRF.app S.X₃)
          (eRF.hom.naturality S.f) (eRF.hom.naturality S.g) (by
            change dK.delta S hS ≫
                (shiftFunctor (DPlus B) (1 : ℤ)).map (eRF.app S.X₁).hom =
              (eRF.app S.X₃).hom ≫ (eRF.app S.X₃).inv ≫ dK.delta S hS ≫
                (shiftFunctor (DPlus B) (1 : ℤ)).map (eRF.app S.X₁).hom
            rw [← Category.assoc, (eRF.app S.X₃).hom_inv_id,
              Category.id_comp])).symm
    naturality := by
      intro S₁ S₂ φ h₁ h₂
      dsimp
      calc
        (rightDerivedObjectFunctor F).map φ.τ₃ ≫
              (eRF.inv.app S₂.X₃ ≫ dK.delta S₂ h₂ ≫
                (shiftFunctor (DPlus B) (1 : ℤ)).map (eRF.hom.app S₂.X₁)) =
            ((rightDerivedObjectFunctor F).map φ.τ₃ ≫ eRF.inv.app S₂.X₃) ≫
              dK.delta S₂ h₂ ≫
                (shiftFunctor (DPlus B) (1 : ℤ)).map (eRF.hom.app S₂.X₁) := by
          simp only [Category.assoc]
        _ = (eRF.inv.app S₁.X₃ ≫
              (K ⋙ rightDerivedComplexFunctor F).map φ.τ₃) ≫
              dK.delta S₂ h₂ ≫
                (shiftFunctor (DPlus B) (1 : ℤ)).map (eRF.hom.app S₂.X₁) := by
          rw [eRF.inv.naturality φ.τ₃]
        _ = eRF.inv.app S₁.X₃ ≫
              ((K ⋙ rightDerivedComplexFunctor F).map φ.τ₃ ≫
                dK.delta S₂ h₂) ≫
                (shiftFunctor (DPlus B) (1 : ℤ)).map (eRF.hom.app S₂.X₁) := by
          simp only [Category.assoc]
        _ = eRF.inv.app S₁.X₃ ≫
              (dK.delta S₁ h₁ ≫
                (shiftFunctor (DPlus B) (1 : ℤ)).map
                  ((K ⋙ rightDerivedComplexFunctor F).map φ.τ₁)) ≫
                (shiftFunctor (DPlus B) (1 : ℤ)).map (eRF.hom.app S₂.X₁) := by
          rw [dK.naturality φ h₁ h₂]
        _ = eRF.inv.app S₁.X₃ ≫ dK.delta S₁ h₁ ≫
              (shiftFunctor (DPlus B) (1 : ℤ)).map
                ((K ⋙ rightDerivedComplexFunctor F).map φ.τ₁ ≫
                  eRF.hom.app S₂.X₁) := by
          rw [Functor.map_comp]
          simp only [Category.assoc]
        _ = eRF.inv.app S₁.X₃ ≫ dK.delta S₁ h₁ ≫
              (shiftFunctor (DPlus B) (1 : ℤ)).map
                (eRF.hom.app S₁.X₁ ≫
                  (rightDerivedObjectFunctor F).map φ.τ₁) := by
          rw [eRF.hom.naturality φ.τ₁]
        _ = (eRF.inv.app S₁.X₃ ≫ dK.delta S₁ h₁ ≫
              (shiftFunctor (DPlus B) (1 : ℤ)).map (eRF.hom.app S₁.X₁)) ≫
              (shiftFunctor (DPlus B) (1 : ℤ)).map
                ((rightDerivedObjectFunctor F).map φ.τ₁) := by
          rw [Functor.map_comp]
          simp only [Category.assoc]
  }⟩

end Formalization.Books.Derived.Unit20
