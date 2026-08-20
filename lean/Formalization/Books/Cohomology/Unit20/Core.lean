import Formalization.Books.Cohomology.Unit03.DerivedFunctors
import Formalization.Books.Cohomology.Unit08.CechCohomology
import Formalization.Books.Cohomology.Unit19
import Formalization.Books.Derived.Unit31.KInjectiveComplexes
import Formalization.Books.Homology.Unit24.FilteredComplexes
import Formalization.Books.Sheaves.Unit26.RingedSpaceModules

/-!
# Cohomology of Sheaves, Chapter 20: shared derived-category interfaces

This file contains only the chapter-local interfaces used by the six source
sections.  They keep the full (unbounded) derived categories explicit and
package the K-flat and tensor constructions that the source uses.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit31
open Formalization.Books.Homology.Unit24
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v u

namespace Formalization.Books.Cohomology.Unit20

/-! ## The categories and complexes in the source notation -/

abbrev ModuleComplex (X : RingedSpace.{v}) :=
  BookComplex (Mod X.structureSheaf)

abbrev ModuleHomotopy (X : RingedSpace.{v}) :=
  BookHomotopyCategory (Mod X.structureSheaf)

abbrev ModuleDerived (X : RingedSpace.{v}) :=
  DerivedCategory (Mod X.structureSheaf)

abbrev ModuleDerivedQuotient (X : RingedSpace.{v}) :
    ModuleComplex X ⥤ ModuleDerived X :=
  DerivedCategory.Q

abbrev ModuleHomotopyQuotient (X : RingedSpace.{v}) :
    ModuleComplex X ⥤ ModuleHomotopy X :=
  HomotopyCategory.quotient (Mod X.structureSheaf) (ComplexShape.up ℤ)

noncomputable def derivedObjectOfComplex
    (X : RingedSpace.{v}) (K : ModuleComplex X) : ModuleDerived X :=
  (ModuleDerivedQuotient X).obj K

/-! ## Pullback and K-flat resolutions -/

structure PullbackPushforwardData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  pullback : Mod Y.structureSheaf ⥤ Mod X.structureSheaf
  pullback_additive : pullback.Additive
  adjunction : pullback ⊣
    Formalization.Books.Sheaves.Unit26.ringedSpaceModulePushforward f

theorem exists_pullbackPushforwardData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (PullbackPushforwardData f) := by
  sorry

noncomputable def pullbackPushforwardData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    PullbackPushforwardData f :=
  Classical.choice (exists_pullbackPushforwardData f)

noncomputable def pullbackComplexFunctor
    {X Y : RingedSpace.{v}} {f : RingedSpaceHom X Y}
    (P : PullbackPushforwardData f) :
    ModuleComplex Y ⥤ ModuleComplex X := by
  letI : P.pullback.Additive := P.pullback_additive
  exact P.pullback.mapHomologicalComplex (ComplexShape.up ℤ)

structure TensorComplexData (X : RingedSpace.{v}) where
  tensor : ModuleComplex X ⥤ ModuleComplex X ⥤ ModuleComplex X

def IsKFlatComplex {X : RingedSpace.{v}} (T : TensorComplexData X)
    (K : ModuleComplex X) : Prop :=
  ∀ F : ModuleComplex X, F.Acyclic →
    AcyclicComplex ((T.tensor.obj F).obj K)

structure KFlatResolution
    {X : RingedSpace.{v}} (T : TensorComplexData X)
    (G : ModuleComplex X) where
  complex : ModuleComplex X
  map : complex ⟶ G
  kFlat : IsKFlatComplex T complex
  quasiIso : QuasiIso map

theorem exists_tensorComplexData (X : RingedSpace.{v}) :
    Nonempty (TensorComplexData X) := by
  sorry

noncomputable def tensorComplexData (X : RingedSpace.{v}) :
    TensorComplexData X :=
  Classical.choice (exists_tensorComplexData X)

theorem exists_kFlatResolution
    {X : RingedSpace.{v}} (T : TensorComplexData X)
    (G : ModuleComplex X) :
    Nonempty (KFlatResolution T G) := by
  sorry

/-! ## Unbounded right-derived functors and adjunctions -/

structure UnboundedRightDerivedData
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A]
    {D : Type u} [Category.{v} D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D]
    (F : BookHomotopyCategory A ⥤ D) where
  functor : DerivedCategory A ⥤ D
  comparison : F ⟶ (DerivedCategory.Qh (C := A)) ⋙ functor
  isRightDerived : Functor.IsRightDerivedFunctor functor comparison
    (quasiIsoHomotopyProperty A)
  computes_on_kInjectives : ∀ I : BookComplex A, I.IsKInjective →
    IsIso (comparison.app ((HomotopyCategory.quotient A
      (ComplexShape.up ℤ)).obj I))

theorem exists_unboundedRightDerivedData
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A]
    {D : Type u} [Category.{v} D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D]
    (F : BookHomotopyCategory A ⥤ D)
    (hF : Nonempty (ExactTriangulatedFunctorData F))
    (hEnough : ∀ K : BookComplex A, HasKInjectiveResolution A K) :
    Nonempty (UnboundedRightDerivedData F) := by
  sorry

structure DerivedAdjunctionData
    {X Y : RingedSpace.{v}}
    (L : ModuleDerived Y ⥤ ModuleDerived X)
    (R : ModuleDerived X ⥤ ModuleDerived Y) where
  adjunction : L ⊣ R

/-! ## Reusable diagram packages -/

structure CommutingSquare {C : Type u} [Category.{v} C]
    {A B C' D : C} (top : A ⟶ B) (left : A ⟶ C')
    (right : B ⟶ D) (bottom : C' ⟶ D) : Prop where
  comm : top ≫ right = left ≫ bottom

end Formalization.Books.Cohomology.Unit20
