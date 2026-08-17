import Formalization.Books.Functors.Unit02.Core

/-!
# Functors on module categories: statements

The propositions below formalize the precise assertions in the section of the
book on functors on module categories.  Proofs are intentionally deferred to
the proving stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit90
open Formalization.Books.Categories.Unit23
open Formalization.Books.Categories.Unit26
open Formalization.Books.Homology.Unit03

universe u v u' v' w

namespace Formalization.Books.Functors.Unit02

/-! ## Extension from finitely presented modules -/

theorem functor_on_finitely_presented_modules
    (A : Type u) [Ring A]
    (B : Type u') [Category.{v'} B]
    [HasFilteredColimitsOfSize.{u, u} B]
    (F : FinitelyPresentedModuleCat.{u, u} A ⥤ B) :
    ∃ E : FilteredColimitExtension
        (finitelyPresentedModuleProperty.{u, u} A) F,
      ∀ E' : FilteredColimitExtension
          (finitelyPresentedModuleProperty.{u, u} A) F,
        ∃! e : E.functor ≅ E'.functor,
          Functor.isoWhiskerLeft
              (finitelyPresentedModuleProperty.{u, u} A).ι e ≪≫
              E'.restrictionIso = E.restrictionIso := by
  sorry

theorem additiveCategory_has_arbitrary_direct_sums
    (B : Type u') [Category.{v'} B] [AdditiveCategory B]
    [HasFilteredColimitsOfSize.{w, w} B] :
    HasCoproducts.{w} B := by
  infer_instance

theorem additive_extension_of_finitely_presented_modules
    (A : Type u) [Ring A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B]
    [HasFilteredColimitsOfSize.{u, u} B]
    (F : FinitelyPresentedModuleCat.{u, u} A ⥤ B)
    (E : FilteredColimitExtension
      (finitelyPresentedModuleProperty.{u, u} A) F)
    [Functor.Additive F] :
    Functor.Additive E.functor ∧
      PreservesArbitraryDirectSums E.functor := by
  sorry

theorem additiveCategory_has_arbitrary_colimits
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B]
    [HasFilteredColimitsOfSize.{w, w} B] :
    HasColimitsOfSize.{w, w} B := by
  let hCoProd : HasCoproducts.{w} B :=
    additiveCategory_hasCoproducts_of_hasFilteredColimits B
  let hCoEq : HasCoequalizers B := Preadditive.hasCoequalizers_of_hasCokernels
  exact @has_colimits_of_hasCoequalizers_and_coproducts B _ hCoProd hCoEq

theorem right_exact_extension_of_finitely_presented_modules
    (A : Type u) [Ring A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B]
    [HasFilteredColimitsOfSize.{u, u} B]
    (F : FinitelyPresentedModuleCat.{u, u} A ⥤ B)
    (E : FilteredColimitExtension
      (finitelyPresentedModuleProperty.{u, u} A) F)
    (hF : IsRightExact F) :
    Functor.Additive E.functor ∧
      IsRightExact E.functor ∧
        PreservesArbitraryDirectSums E.functor := by
  sorry

theorem additiveCategory_has_finite_limits
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasKernels B] :
    HasFiniteLimits B := by
  exact hasFiniteLimits_of_additive_of_hasKernels B

theorem left_exact_extension_of_finitely_presented_modules
    (A : Type u) [CommRing A] (hA : IsCoherentRing A)
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasKernels B]
    [HasFilteredColimitsOfSize.{u, u} B]
    (hComm : FilteredColimitsCommuteWithKernels B)
    (F : FinitelyPresentedModuleCat.{u, u} A ⥤ B)
    (E : FilteredColimitExtension
      (finitelyPresentedModuleProperty.{u, u} A) F)
    (hF : @IsLeftExact
      (FinitelyPresentedModuleCat.{u, u} A) _ B _
      (finitelyPresentedModuleCat_hasFiniteLimits_of_coherent.{u, u} A hA) F) :
    Functor.Additive E.functor ∧
      IsLeftExact E.functor ∧
        PreservesArbitraryDirectSums E.functor := by
  sorry

theorem additiveCategory_has_finite_colimits
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B] :
    HasFiniteColimits B := by
  exact hasFiniteColimits_of_additive_of_hasCokernels B

/-! ## Classification by the image of the regular module -/

def regularModule (A : Type u) [CommRing A] : ModuleCat.{u} A :=
  ModuleCat.of A A

def regularModuleFp (A : Type u) [CommRing A] :
    FinitelyPresentedModuleCat.{u, u} A :=
  ⟨regularModule A, by
    change Module.FinitePresentation A (A : Type u)
    infer_instance⟩

def regularModuleScalar (A : Type u) [CommRing A] (a : A) :
    regularModule A ⟶ regularModule A :=
  ModuleCat.ofHom (LinearMap.mulLeft A a)

def regularModuleFpScalar (A : Type u) [CommRing A] (a : A) :
    regularModuleFp A ⟶ regularModuleFp A :=
  ObjectProperty.homMk (regularModuleScalar A a)

def moduleActionOfFinitelyPresentedFunctor
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [Preadditive B]
    (F : FinitelyPresentedModuleCat.{u, u} A ⥤ B) :
    ModuleActionObject A B where
  carrier := F.obj (regularModuleFp A)
  action :=
    { toFun := fun a => F.map (regularModuleFpScalar A a)
      map_one' := by sorry
      map_mul' := by sorry
      map_zero' := by sorry
      map_add' := by sorry }

def evaluationOnFinitelyPresentedModules
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B] :
    RightExactFunctorCat (FinitelyPresentedModuleCat.{u, u} A) B ⥤
      ModuleActionCat A B where
  obj F := moduleActionOfFinitelyPresentedFunctor A B F.1
  map f :=
    { hom := f.hom.app (regularModuleFp A)
      comm := by sorry }
  map_id := by
    intro F
    apply ModuleActionObject.hom_ext
    rfl
  map_comp := by
    intro F G H f g
    apply ModuleActionObject.hom_ext
    rfl

theorem functor_on_finitely_presented_modules_classification
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B] :
    (evaluationOnFinitelyPresentedModules A B).IsEquivalence := by
  sorry

def moduleActionOfModuleFunctor
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [Preadditive B]
    (F : ModuleCat.{u} A ⥤ B) :
    ModuleActionObject A B where
  carrier := F.obj (regularModule A)
  action :=
    { toFun := fun a => F.map (regularModuleScalar A a)
      map_one' := by sorry
      map_mul' := by sorry
      map_zero' := by sorry
      map_add' := by sorry }

def evaluationOnModules
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B]
    [HasCoproducts.{u} B] :
    RightExactDirectSumsFunctorCat (ModuleCat.{u} A) B ⥤
      ModuleActionCat A B where
  obj F := moduleActionOfModuleFunctor A B F.1
  map f :=
    { hom := f.hom.app (regularModule A)
      comm := by sorry }
  map_id := by
    intro F
    apply ModuleActionObject.hom_ext
    rfl
  map_comp := by
    intro F G H f g
    apply ModuleActionObject.hom_ext
    rfl

theorem functor_on_modules_classification
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B]
    [HasCoproducts.{u} B] :
    (evaluationOnModules A B).IsEquivalence := by
  sorry

end Formalization.Books.Functors.Unit02
