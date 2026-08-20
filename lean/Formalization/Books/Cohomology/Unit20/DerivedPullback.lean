import Formalization.Books.Cohomology.Unit20.Core

/-!
# Cohomology of Sheaves, Chapter 20, Section 1: Derived pullback
-/

noncomputable section

open CategoryTheory
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Sheaves.Unit25

universe v

namespace Formalization.Books.Cohomology.Unit20

/-! The K-flat construction and its exact derived functor. -/

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

structure DerivedInverseImageTensorData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  tensor : ModuleDerived X ⥤ ModuleDerived Y ⥤ ModuleDerived X
  comparison : ∀ (K : ModuleDerived X) (L : ModuleDerived Y),
    Nonempty ((tensor.obj K).obj L ≅
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
    Nonempty (((derivedInverseImageTensorData f).tensor.obj K).obj G ≅
      derivedTensor X K ((derivedPullback f).obj G)) := by
  exact (derivedInverseImageTensorData f).comparison K G

/-! The source's six-vertex tensor/pullback diagram is recorded as a
    natural commutativity assertion. -/

structure TensorPullCompatibilityData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : ModuleComplex Y) where
  left :
    (derivedPullback f).obj
        (derivedTensor Y (derivedObjectOfComplex Y K)
          (derivedObjectOfComplex Y M)) ⟶
      derivedTensor X
        ((derivedPullback f).obj (derivedObjectOfComplex Y K))
        ((derivedPullback f).obj (derivedObjectOfComplex Y M))
  right :
    (derivedPullback f).obj
        (derivedTensor Y (derivedObjectOfComplex Y K)
          (derivedObjectOfComplex Y M)) ⟶
      derivedTensor X
        ((derivedPullback f).obj (derivedObjectOfComplex Y K))
        ((derivedPullback f).obj (derivedObjectOfComplex Y M))
  commutes : left = right

theorem tensor_pull_compatibility
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : ModuleComplex Y) :
    Nonempty (TensorPullCompatibilityData f K M) := by
  sorry

end Formalization.Books.Cohomology.Unit20
