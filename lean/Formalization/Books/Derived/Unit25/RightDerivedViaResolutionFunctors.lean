import Formalization.Books.Derived.Unit20.InjectiveResolutions
import Formalization.Books.Derived.Unit23.ResolutionFunctors

/-!
# Derived Categories, Chapter 25: right derived functors via resolution functors

The source section identifies a right derived functor with the functor obtained
by applying the original functor to a functorial injective resolution.  Unit23
supplies the resolution package and its quasi-inverse; this file records the
resulting derived functor, its objectwise computation, and the exact lift before
localizing the target.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Derived.Unit23
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w w' v u v' u'

namespace Formalization.Books.Derived.Unit25

/-! ## The functor on complexes of injectives -/

/- The arrow labelled `F` in the source diagram is the termwise application of
   `F`, followed by passage to the bounded-below derived category of `B`. -/
noncomputable def resolutionFunctorDerivedTarget
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    KPlus (Formalization.Books.Derived.Unit23.InjectiveSubcategory A) ⥤ DPlus B :=
    injectiveHomotopyInclusion (A := A) ⋙
    additiveHomotopyPlusFunctor F ⋙ plusDerivedLocalizationFunctor B

private lemma resolutionFunctorDerivedTarget_obj_eq_unit_target
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    (X : KPlus (Formalization.Books.Derived.Unit23.InjectiveSubcategory A)) :
    (DerivedCategory.Plus.Qh (C := B)).obj
          (F.mapHomotopyCategoryPlus.obj
            ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X)) =
      (resolutionFunctorDerivedTarget F).obj X := by
  rfl

private lemma resolutionFunctorDerivedTarget_obj_eq_unit_target_naturality
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    {X Y : KPlus (Formalization.Books.Derived.Unit23.InjectiveSubcategory A)}
    (f : X ⟶ Y) :
    (DerivedCategory.Plus.Qh (C := B)).map
          (F.mapHomotopyCategoryPlus.map
            ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.map f)) ≫
        eqToHom (resolutionFunctorDerivedTarget_obj_eq_unit_target F Y) =
      eqToHom (resolutionFunctorDerivedTarget_obj_eq_unit_target F X) ≫
        (resolutionFunctorDerivedTarget F).map f := by
  cases resolutionFunctorDerivedTarget_obj_eq_unit_target F X
  cases resolutionFunctorDerivedTarget_obj_eq_unit_target F Y
  dsimp [resolutionFunctorDerivedTarget, injectiveHomotopyInclusion,
    additiveHomotopyPlusFunctor, plusDerivedLocalizationFunctor]
  simp only [Category.comp_id, Category.id_comp]

/-! ## The quasi-inverse and the derived functor -/

/- The functor `j'` from the source is the chosen witness supplied by the
   preceding chapter's quasi-inverse theorem. -/
noncomputable def resolutionFunctorQuasiInverse
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    DPlus A ⥤ KPlus (Formalization.Books.Derived.Unit23.InjectiveSubcategory A) :=
  Classical.choose (resolution_functor_quasi_inverse P)

theorem resolutionFunctorQuasiInverse_spec
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    plusDerivedLocalizationFunctor A ⋙ resolutionFunctorQuasiInverse R P = P.functor ∧
      QuasiInverseOf
        (injectiveToDerivedFunctor (A := A))
        (resolutionFunctorQuasiInverse R P) := by
  exact (Classical.choose_spec (resolution_functor_quasi_inverse P)).1

/- The diagonal arrow in the source diagram is the composite along its upper
   and right-hand sides. -/
noncomputable def rightDerivedFunctorViaResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    DPlus A ⥤ DPlus B :=
  resolutionFunctorQuasiInverse R P ⋙ resolutionFunctorDerivedTarget F

theorem rightDerivedFunctorViaResolution_two_commutes
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    Nonempty
      (rightDerivedFunctorViaResolution F R P ≅
        resolutionFunctorQuasiInverse R P ⋙ resolutionFunctorDerivedTarget F) := by
  exact ⟨Iso.refl _⟩

/- The source's computation `RF(K) = F(j(K))`, expressed as the canonical
   objectwise isomorphism available from the chosen quasi-inverse. -/
theorem rightDerivedFunctorViaResolution_on_resolution
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R)
    (K : KPlus A) :
    Nonempty
      ((rightDerivedFunctorViaResolution F R P).obj
      ((plusDerivedLocalizationFunctor A).obj K) ≅
        (resolutionFunctorDerivedTarget F).obj (R.j K)) := by
  have hobj :
      (resolutionFunctorQuasiInverse R P).obj
          ((plusDerivedLocalizationFunctor A).obj K) = R.j K := by
    calc
      _ = P.functor.obj K := by
        exact congrArg (fun H : KPlus A ⥤ KPlus (InjectiveSubcategory A) =>
          H.obj K) (resolutionFunctorQuasiInverse_spec R P).1
      _ = R.j K := P.objectwise K
  exact ⟨eqToIso (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
    (resolutionFunctorDerivedTarget F).obj X) hobj)⟩

/- The defining property of the right derived functor: its unit is a left Kan
   extension along the bounded-below quasi-isomorphism localization. -/
theorem rightDerivedFunctorViaResolution_isRightDerived
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    ∃ α : rightDerivedSourceFunctor F ⟶
        plusDerivedLocalizationFunctor A ⋙
          rightDerivedFunctorViaResolution F R P,
      (rightDerivedFunctorViaResolution F R P).IsRightDerivedFunctor α
        (quasiIsoPlusProperty A) := by
  obtain ⟨_, hcounit⟩ := (resolutionFunctorQuasiInverse_spec R P).2
  let ε : resolutionFunctorQuasiInverse R P ⋙
      injectiveToDerivedFunctor (A := A) ≅ 𝟭 (DPlus A) :=
    Classical.choice hcounit
  let γ : injectiveToDerivedFunctor (A := A) ⋙
      F.rightDerivedFunctorPlus ≅ resolutionFunctorDerivedTarget F :=
    NatIso.ofComponents (fun X => by
      have htarget :
          (DerivedCategory.Plus.Qh (C := B)).obj
              (F.mapHomotopyCategoryPlus.obj
                ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X)) =
            (resolutionFunctorDerivedTarget F).obj X := by
        exact resolutionFunctorDerivedTarget_obj_eq_unit_target F X
      change F.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.Qh (C := A)).obj
            ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X)) ≅
        (resolutionFunctorDerivedTarget F).obj X
      exact (asIso (F.rightDerivedFunctorPlusUnit.app
        ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X))).symm ≪≫
        eqToIso htarget)
    (by
      intro X Y f
      have htargetX :
          (DerivedCategory.Plus.Qh (C := B)).obj
              (F.mapHomotopyCategoryPlus.obj
                ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X)) =
            (resolutionFunctorDerivedTarget F).obj X := by
        exact resolutionFunctorDerivedTarget_obj_eq_unit_target F X
      have htargetY :
          (DerivedCategory.Plus.Qh (C := B)).obj
              (F.mapHomotopyCategoryPlus.obj
                ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Y)) =
            (resolutionFunctorDerivedTarget F).obj Y := by
        exact resolutionFunctorDerivedTarget_obj_eq_unit_target F Y
      dsimp
      dsimp only [injectiveToDerivedFunctor, injectiveHomotopyInclusion,
        additiveHomotopyPlusFunctor, plusDerivedLocalizationFunctor,
        Functor.comp_map]
      simp only [Functor.comp_obj, id_eq, Iso.trans_hom, Iso.symm_hom,
        eqToIso.hom, Category.assoc]
      have hα := F.rightDerivedFunctorPlusUnit.naturality
        ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.map f)
      have hα' :
          (asIso (F.rightDerivedFunctorPlusUnit.app
            ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X))).hom ≫
              F.rightDerivedFunctorPlus.map
                ((DerivedCategory.Plus.Qh (C := A)).map
                  ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.map f)) =
            (DerivedCategory.Plus.Qh (C := B)).map
                (F.mapHomotopyCategoryPlus.map
                  ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.map f)) ≫
              (asIso (F.rightDerivedFunctorPlusUnit.app
                ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Y))).hom := by
        change F.rightDerivedFunctorPlusUnit.app
            ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X) ≫
              F.rightDerivedFunctorPlus.map
                ((DerivedCategory.Plus.Qh (C := A)).map
                  ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.map f)) =
          (DerivedCategory.Plus.Qh (C := B)).map
              (F.mapHomotopyCategoryPlus.map
                ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.map f)) ≫
            F.rightDerivedFunctorPlusUnit.app
              ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Y)
        simpa only [Functor.comp_map] using hα.symm
      have hunit :
          F.rightDerivedFunctorPlus.map
              ((DerivedCategory.Plus.Qh (C := A)).map
                ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.map f)) ≫
            (asIso (F.rightDerivedFunctorPlusUnit.app
              ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Y))).inv =
          (asIso (F.rightDerivedFunctorPlusUnit.app
            ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X))).inv ≫
            (DerivedCategory.Plus.Qh (C := B)).map
              (F.mapHomotopyCategoryPlus.map
                ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.map f)) := by
        rw [← cancel_mono (asIso (F.rightDerivedFunctorPlusUnit.app
          ((CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Y))).hom]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [← hα']
        simp only [Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hunit]
      rw [Category.assoc,
        resolutionFunctorDerivedTarget_obj_eq_unit_target_naturality F f]
      )
  let e : F.rightDerivedFunctorPlus ≅
      rightDerivedFunctorViaResolution F R P := by
    change F.rightDerivedFunctorPlus ≅
      resolutionFunctorQuasiInverse R P ⋙ resolutionFunctorDerivedTarget F
    exact (Functor.leftUnitor F.rightDerivedFunctorPlus).symm ≪≫
      Functor.isoWhiskerRight ε.symm F.rightDerivedFunctorPlus ≪≫
      Functor.associator (resolutionFunctorQuasiInverse R P)
        (injectiveToDerivedFunctor (A := A)) F.rightDerivedFunctorPlus ≪≫
      Functor.isoWhiskerLeft (resolutionFunctorQuasiInverse R P) γ
  let α : rightDerivedSourceFunctor F ⟶
      plusDerivedLocalizationFunctor A ⋙
        rightDerivedFunctorViaResolution F R P :=
    F.rightDerivedFunctorPlusUnit ≫
      Functor.whiskerLeft (plusDerivedLocalizationFunctor A) e.hom
  have hcomm :
      F.rightDerivedFunctorPlusUnit ≫
          Functor.whiskerLeft (plusDerivedLocalizationFunctor A) e.hom = α := by
    change F.rightDerivedFunctorPlusUnit ≫
        Functor.whiskerLeft (plusDerivedLocalizationFunctor A) e.hom =
      F.rightDerivedFunctorPlusUnit ≫
        Functor.whiskerLeft (plusDerivedLocalizationFunctor A) e.hom
    rfl
  exact ⟨α, (Functor.isRightDerivedFunctor_iff_of_iso
    (RF := F.rightDerivedFunctorPlus) (α := F.rightDerivedFunctorPlusUnit)
    (α' := α) (W := quasiIsoPlusProperty A) e hcomm).mp (by
      infer_instance)⟩

/-! ## The exact lift before localizing the target -/

/- The source's lifted functor `F ∘ j'` still lands in the bounded-below
   homotopy category, before applying the target localization. -/
noncomputable def resolutionFunctorExactLift
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    DPlus A ⥤ KPlus B :=
  resolutionFunctorQuasiInverse R P ⋙
    injectiveHomotopyInclusion (A := A) ⋙ additiveHomotopyPlusFunctor F

theorem resolutionFunctorExactLift_isExact
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    Nonempty (ExactTriangulatedFunctorData (resolutionFunctorExactLift F R P)) := by
  let hE := Classical.choice
    (injective_homotopy_to_derived_equivalence (A := A)).1
  let : (injectiveToDerivedFunctor (A := A)).CommShift ℤ := hE.commShift
  let : Functor.IsEquivalence (injectiveToDerivedFunctor (A := A)) :=
    (injective_homotopy_to_derived_equivalence (A := A)).2
  let E := (injectiveToDerivedFunctor (A := A)).asEquivalence
  let : E.functor.CommShift ℤ := by
    change (injectiveToDerivedFunctor (A := A)).CommShift ℤ
    exact hE.commShift
  let : E.functor.IsTriangulated := hE.isTriangulated
  let : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
  let : E.CommShift ℤ := E.commShift_of_functor ℤ
  let : E.inverse.IsTriangulated := by
    exact E.toAdjunction.isTriangulated_rightAdjoint
  obtain ⟨_, hcounit⟩ := (resolutionFunctorQuasiInverse_spec R P).2
  let hcomp : resolutionFunctorQuasiInverse R P ⋙
      injectiveToDerivedFunctor (A := A) ≅
      E.inverse ⋙ injectiveToDerivedFunctor (A := A) := by
    simpa [E] using
      (Classical.choice hcounit ≪≫ E.counitIso.symm)
  let hQI : resolutionFunctorQuasiInverse R P ≅ E.inverse :=
    Functor.fullyFaithfulCancelRight (injectiveToDerivedFunctor (A := A)) hcomp
  let : (resolutionFunctorQuasiInverse R P).CommShift ℤ :=
    Functor.CommShift.ofIso hQI.symm ℤ
  let : (resolutionFunctorQuasiInverse R P).IsTriangulated := by
    let : NatTrans.CommShift hQI.symm.hom ℤ :=
      Functor.CommShift.ofIso_compatibility hQI.symm ℤ
    exact Functor.isTriangulated_of_iso hQI.symm
  let hT := Classical.choice (additive_homotopy_functors_are_exact F).2.1
  let : (injectiveHomotopyInclusion (A := A)).CommShift ℤ := by
    dsimp [injectiveHomotopyInclusion, additiveHomotopyPlusFunctor]
    infer_instance
  let : (injectiveHomotopyInclusion (A := A)).IsTriangulated := by
    dsimp [injectiveHomotopyInclusion, additiveHomotopyPlusFunctor]
    infer_instance
  let : (additiveHomotopyPlusFunctor F).CommShift ℤ := hT.commShift
  let : (additiveHomotopyPlusFunctor F).IsTriangulated := hT.isTriangulated
  dsimp [resolutionFunctorExactLift]
  refine ⟨{ commShift := ?_, isTriangulated := ?_ }⟩
  · infer_instance
  · infer_instance

end Formalization.Books.Derived.Unit25
