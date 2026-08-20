import Formalization.Books.Cohomology.Unit20.Core

/-!
# Cohomology of Sheaves, Chapter 20, Section 1: Derived pullback
-/

noncomputable section

open CategoryTheory
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v

namespace Formalization.Books.Cohomology.Unit20

/-! The K-flat construction and its exact derived functor. -/

structure DerivedPullbackData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (P : PullbackPushforwardData f) (T : TensorComplexData Y) where
  functor : ModuleDerived Y ⥤ ModuleDerived X
  exact : ∃ h : functor.CommShift ℤ,
    letI : functor.CommShift ℤ := h
    functor.IsTriangulated
  computed_on_kFlat : ∀ (G : ModuleComplex Y),
    ∀ R : KFlatResolution T G,
      Nonempty (functor.obj (derivedObjectOfComplex Y G) ≅
        derivedObjectOfComplex X ((pullbackComplexFunctor P).obj R.complex))

theorem exists_derivedPullbackData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (P : PullbackPushforwardData f) (T : TensorComplexData Y) :
    Nonempty (DerivedPullbackData f P T) := by
  sorry

noncomputable def derivedPullback
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ModuleDerived Y ⥤ ModuleDerived X :=
  let P := pullbackPushforwardData f
  let T := tensorComplexData _
  (Classical.choice (exists_derivedPullbackData f P T)).functor

theorem derivedPullback_isExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ∃ h : (derivedPullback f).CommShift ℤ,
      letI : (derivedPullback f).CommShift ℤ := h
      (derivedPullback f).IsTriangulated := by
  sorry

theorem derivedPullback_computed_by_kFlat_resolution
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : ModuleComplex Y) :
    ∀ R : KFlatResolution (tensorComplexData Y) G,
      Nonempty ((derivedPullback f).obj (derivedObjectOfComplex Y G) ≅
        derivedObjectOfComplex X
          ((pullbackComplexFunctor (pullbackPushforwardData f)).obj R.complex)) := by
  sorry

/-! Pullback is compatible with composition. -/

theorem derivedPullback_comp
    {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z) :
    (derivedPullback g ⋙ derivedPullback f) =
      derivedPullback (RingedSpaceHom.comp f g) := by
  sorry

/-! Derived tensor products and their pullback comparison. -/

structure DerivedTensorData (X : RingedSpace.{v}) where
  tensor : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X
  computed_on_kFlat : ∀ (K L : ModuleComplex X),
    IsKFlatComplex (tensorComplexData X) K →
      IsKFlatComplex (tensorComplexData X) L →
      Nonempty ((tensor.obj (derivedObjectOfComplex X K)).obj
        (derivedObjectOfComplex X L) ≅
        derivedObjectOfComplex X
          (((tensorComplexData X).tensor.obj K).obj L))

theorem exists_derivedTensorData (X : RingedSpace.{v}) :
    Nonempty (DerivedTensorData X) := by
  sorry

noncomputable def derivedTensorData (X : RingedSpace.{v}) :
    DerivedTensorData X :=
  Classical.choice (exists_derivedTensorData X)

noncomputable abbrev derivedTensor
    (X : RingedSpace.{v}) (K L : ModuleDerived X) : ModuleDerived X :=
  (derivedTensorData X).tensor.obj K |>.obj L

theorem derivedPullback_tensor_iso
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : ModuleDerived Y) :
    Nonempty ((derivedPullback f).obj (derivedTensor Y K L) ≅
      derivedTensor X ((derivedPullback f).obj K)
        ((derivedPullback f).obj L)) := by
  sorry

/-! The variant tensor expression over the inverse-image structure sheaf. -/

abbrev InverseImageStructureSheaf
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :=
  (Formalization.Books.Sheaves.Unit24.sheafRingPullback f.continuous).obj
    Y.structureSheaf

noncomputable instance inverseImageModule_hasDerivedCategory
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    HasDerivedCategory (Mod (InverseImageStructureSheaf f)) :=
  HasDerivedCategory.standard _

abbrev InverseImageModuleDerived
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :=
  DerivedCategory (Mod (InverseImageStructureSheaf f))

structure DerivedInverseImageTensorData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  inverseImage : ModuleDerived Y ⥤ InverseImageModuleDerived f
  tensor : ModuleDerived X ⥤ InverseImageModuleDerived f ⥤ ModuleDerived X
  comparison : ∀ (K : ModuleDerived X) (L : ModuleDerived Y),
    Nonempty ((tensor.obj K).obj (inverseImage.obj L) ≅
      derivedTensor X K ((derivedPullback f).obj L))

theorem exists_derivedInverseImageTensorData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (DerivedInverseImageTensorData f) := by
  sorry

noncomputable def derivedInverseImageTensorData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    DerivedInverseImageTensorData f :=
  Classical.choice (exists_derivedInverseImageTensorData f)

theorem derivedInverseImage_tensor_iso
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : ModuleDerived X) (G : ModuleDerived Y) :
    Nonempty (((derivedInverseImageTensorData f).tensor.obj K).obj
      ((derivedInverseImageTensorData f).inverseImage.obj G) ≅
      derivedTensor X K ((derivedPullback f).obj G)) := by
  exact (derivedInverseImageTensorData f).comparison K G

/-! The source's six-vertex tensor/pullback diagram is recorded as a
    commutative diagram in the derived category. -/

noncomputable abbrev tensorComplex
    (X : RingedSpace.{v}) (K M : ModuleComplex X) : ModuleComplex X :=
  ((tensorComplexData X).tensor.obj K).obj M

structure TensorPullCompatibilityData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : ModuleComplex Y) where
  top :
    (derivedPullback f).obj
        (derivedTensor Y (derivedObjectOfComplex Y K)
          (derivedObjectOfComplex Y M)) ⟶
      (derivedPullback f).obj (derivedObjectOfComplex Y (tensorComplex Y K M))
  left :
    (derivedPullback f).obj
        (derivedTensor Y (derivedObjectOfComplex Y K)
          (derivedObjectOfComplex Y M)) ⟶
      derivedTensor X
        ((derivedPullback f).obj (derivedObjectOfComplex Y K))
        ((derivedPullback f).obj (derivedObjectOfComplex Y M))
  right :
    (derivedPullback f).obj (derivedObjectOfComplex Y (tensorComplex Y K M)) ⟶
      derivedObjectOfComplex X
        ((pullbackComplexFunctor (pullbackPushforwardData f)).obj
          (tensorComplex Y K M))
  middle :
    derivedTensor X
        ((derivedPullback f).obj (derivedObjectOfComplex Y K))
        ((derivedPullback f).obj (derivedObjectOfComplex Y M)) ⟶
      derivedTensor X
        (derivedObjectOfComplex X
          ((pullbackComplexFunctor (pullbackPushforwardData f)).obj K))
        (derivedObjectOfComplex X
          ((pullbackComplexFunctor (pullbackPushforwardData f)).obj M))
  lowerRight :
    derivedObjectOfComplex X
        ((pullbackComplexFunctor (pullbackPushforwardData f)).obj
          (tensorComplex Y K M)) ⟶
      derivedObjectOfComplex X
        (tensorComplex X
          ((pullbackComplexFunctor (pullbackPushforwardData f)).obj K)
          ((pullbackComplexFunctor (pullbackPushforwardData f)).obj M))
  bottom :
    derivedTensor X
        (derivedObjectOfComplex X
          ((pullbackComplexFunctor (pullbackPushforwardData f)).obj K))
        (derivedObjectOfComplex X
          ((pullbackComplexFunctor (pullbackPushforwardData f)).obj M)) ⟶
      derivedObjectOfComplex X
        (tensorComplex X
          ((pullbackComplexFunctor (pullbackPushforwardData f)).obj K)
          ((pullbackComplexFunctor (pullbackPushforwardData f)).obj M))
  commutes : top ≫ right ≫ lowerRight = left ≫ middle ≫ bottom

theorem tensor_pull_compatibility
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : ModuleComplex Y) :
    Nonempty (TensorPullCompatibilityData f K M) := by
  sorry

end Formalization.Books.Cohomology.Unit20
