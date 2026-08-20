import Formalization.Books.Cohomology.Unit10

/-!
# Cohomology of Sheaves, Chapter 11: functoriality of cohomology

The source constructs the maps induced by an `f`-map first in the bounded-below
derived category, then after derived global sections, and finally on
cohomology.  The resolution remark is retained as an explicit commutative
resolution-square interface.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Categories.Unit23
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit10
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit07
open Formalization.Books.Modules.Unit03
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v u

namespace Formalization.Books.Cohomology.Unit11

/-! ## Complexes and the derived-category map -/

/- The pushforward functor is already available on modules.  This is its
   canonical termwise prolongation to bounded-below complexes. -/
noncomputable def ringedSpaceModulePushforwardComplex
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    CompPlus (Mod X.structureSheaf) ⥤ CompPlus (Mod Y.structureSheaf) := by
  let P := sheafModuleRingedSpacePushforward f
  letI : P.Additive := left_or_right_exact_additive P
    (Or.inl (sheafModuleRingedSpacePushforward_isLeftExact f))
  exact ObjectProperty.lift (CochainComplex.plus (Mod Y.structureSheaf))
    ((CochainComplex.Plus.ι (Mod X.structureSheaf)) ⋙
      P.mapHomologicalComplex (.up ℤ))
    (by
      intro K
      obtain ⟨n, hn⟩ := K.property
      refine ⟨n, ?_⟩
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      change IsZero (P.obj (K.1.X i))
      exact Functor.map_isZero _ (K.1.isZero_of_isStrictlyGE n i))

/- A morphism of bounded-below complexes of modules of the kind used in the
   source lemma. -/
abbrev RingedSpaceComplexFMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : CompPlus (Mod Y.structureSheaf))
    (F : CompPlus (Mod X.structureSheaf)) : Type _ :=
  G ⟶ (ringedSpaceModulePushforwardComplex f).obj F

abbrev ringedSpaceDerivedPushforwardOnComplexes
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    CompPlus (Mod X.structureSheaf) ⥤ DPlus (Mod Y.structureSheaf) :=
  rightDerivedFunctorOfLeftExactOnComplexes
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f)

/- The canonical derived morphism is recorded as data so that its source-level
   functoriality can be stated independently of a choice of resolutions. -/
structure RingedSpaceFunctorialityData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    {G : CompPlus (Mod Y.structureSheaf)}
    {F : CompPlus (Mod X.structureSheaf)}
    (φ : RingedSpaceComplexFMap f G F) where
  morphism :
    (DerivedCategory.Plus.Q (C := Mod Y.structureSheaf)).obj G ⟶
      (ringedSpaceDerivedPushforwardOnComplexes f).obj F

theorem exists_ringedSpaceFunctorialityData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    {G : CompPlus (Mod Y.structureSheaf)}
    {F : CompPlus (Mod X.structureSheaf)}
    (φ : RingedSpaceComplexFMap f G F) :
    Nonempty (RingedSpaceFunctorialityData f φ) := by
  sorry

noncomputable def ringedSpaceFunctorialityMorphism
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    {G : CompPlus (Mod Y.structureSheaf)}
    {F : CompPlus (Mod X.structureSheaf)}
    (φ : RingedSpaceComplexFMap f G F) :
    (DerivedCategory.Plus.Q (C := Mod Y.structureSheaf)).obj G ⟶
      (ringedSpaceDerivedPushforwardOnComplexes f).obj F :=
  (Classical.choice (exists_ringedSpaceFunctorialityData f φ)).morphism

/- A map between source triples consists of maps of the source and coefficient
   complexes for which the square defining an `f`-map commutes. -/
structure RingedSpaceFunctorialityTripleHom
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    {G₁ G₂ : CompPlus (Mod Y.structureSheaf)}
    {F₁ F₂ : CompPlus (Mod X.structureSheaf)}
    {φ₁ : RingedSpaceComplexFMap f G₁ F₁}
    {φ₂ : RingedSpaceComplexFMap f G₂ F₂} where
  source : G₁ ⟶ G₂
  coefficient : F₁ ⟶ F₂
  commutes :
    source ≫ φ₂ = φ₁ ≫ (ringedSpaceModulePushforwardComplex f).map coefficient

theorem ringedSpaceFunctorialityMorphism_natural
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    {G₁ G₂ : CompPlus (Mod Y.structureSheaf)}
    {F₁ F₂ : CompPlus (Mod X.structureSheaf)}
    {φ₁ : RingedSpaceComplexFMap f G₁ F₁}
    {φ₂ : RingedSpaceComplexFMap f G₂ F₂}
    (h : RingedSpaceFunctorialityTripleHom f (φ₁ := φ₁) (φ₂ := φ₂)) :
    (DerivedCategory.Plus.Q (C := Mod Y.structureSheaf)).map h.source ≫
        ringedSpaceFunctorialityMorphism f φ₂ =
      ringedSpaceFunctorialityMorphism f φ₁ ≫
        (ringedSpaceDerivedPushforwardOnComplexes f).map h.coefficient := by
  sorry

/-! ## Module `f`-maps, derived sections, and cohomology -/

theorem exists_ringedSpaceModuleFunctorialityMorphism
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (F : Mod X.structureSheaf)
    (φ : RingedSpaceModuleFMap f G F) :
    Nonempty (
      (DerivedCategory.Plus.singleFunctor (Mod Y.structureSheaf) 0).obj G ⟶
        (ringedSpaceModuleDerivedPushforward f).obj
          ((DerivedCategory.Plus.singleFunctor (Mod X.structureSheaf) 0).obj F)) := by
  sorry

noncomputable def ringedSpaceModuleFunctorialityMorphism
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (F : Mod X.structureSheaf)
    (φ : RingedSpaceModuleFMap f G F) :
    (DerivedCategory.Plus.singleFunctor (Mod Y.structureSheaf) 0).obj G ⟶
      (ringedSpaceModuleDerivedPushforward f).obj
        ((DerivedCategory.Plus.singleFunctor (Mod X.structureSheaf) 0).obj F) :=
  Classical.choice (exists_ringedSpaceModuleFunctorialityMorphism f G F φ)

noncomputable abbrev ringedSpaceModuleDerivedGlobalSectionsObject
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    DPlus (ModuleCat.{v} (X.structureSheaf.obj.obj
      (op (⊤ : Opens X.carrier)))) :=
  (ringedSpaceModuleTotalDerivedSections X (⊤ : Opens X.carrier)).obj
    ((DerivedCategory.Plus.singleFunctor (Mod X.structureSheaf) 0).obj F)

noncomputable def ringedSpaceModuleDerivedGlobalSectionsOverBase
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) :
    DPlus (ModuleCat.{v} (Y.structureSheaf.obj.obj
      (op (⊤ : Opens Y.carrier)))) := by
  let C := Classical.choice (exists_lerayDerivedSectionsComparisonData f)
  exact C.global_restriction.obj
    (ringedSpaceModuleDerivedGlobalSectionsObject X F)

noncomputable def ringedSpaceModuleGlobalSectionsComplex
    (X : RingedSpace.{v}) :
    CompPlus (Mod X.structureSheaf) ⥤
      CompPlus (ModuleCat.{v} (X.structureSheaf.obj.obj
        (op (⊤ : Opens X.carrier)))) := by
  let P := ringedSpaceModuleGlobalSections X
  letI : P.Additive := left_or_right_exact_additive P
    (Or.inl (ringedSpaceModuleGlobalSections_isLeftExact X))
  exact ObjectProperty.lift
    (CochainComplex.plus
      (ModuleCat.{v} (X.structureSheaf.obj.obj
        (op (⊤ : Opens X.carrier)))))
    ((CochainComplex.Plus.ι (Mod X.structureSheaf)) ⋙
      P.mapHomologicalComplex (.up ℤ))
    (by
      intro K
      obtain ⟨n, hn⟩ := K.property
      refine ⟨n, ?_⟩
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      change IsZero (P.obj (K.1.X i))
      exact Functor.map_isZero _ (K.1.isZero_of_isStrictlyGE n i))

noncomputable def ringedSpaceModuleFunctorialDerivedGlobalMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (F : Mod X.structureSheaf)
    (φ : RingedSpaceModuleFMap f G F) :
    ringedSpaceModuleDerivedGlobalSectionsObject Y G ⟶
      ringedSpaceModuleDerivedGlobalSectionsOverBase f F := by
  let C := Classical.choice (exists_lerayDerivedSectionsComparisonData f)
  let h := congrArg
    (fun H : DPlus (Mod X.structureSheaf) ⥤
      DPlus (ModuleCat.{v} (Y.structureSheaf.obj.obj
        (op (⊤ : Opens Y.carrier)))) =>
      H.obj ((DerivedCategory.Plus.singleFunctor (Mod X.structureSheaf) 0).obj F))
    C.global_commutes
  exact
    (ringedSpaceModuleTotalDerivedSections Y (⊤ : Opens Y.carrier)).map
        (ringedSpaceModuleFunctorialityMorphism f G F φ) ≫
      eqToHom h.symm

noncomputable def ringedSpaceModuleFunctorialCohomologyMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (F : Mod X.structureSheaf)
    (φ : RingedSpaceModuleFMap f G F) (i : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{v} (Y.structureSheaf.obj.obj
        (op (⊤ : Opens Y.carrier)))) i).obj
      (ringedSpaceModuleDerivedGlobalSectionsObject Y G)) ⟶
    ((DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{v} (Y.structureSheaf.obj.obj
        (op (⊤ : Opens Y.carrier)))) i).obj
      (ringedSpaceModuleDerivedGlobalSectionsOverBase f F)) :=
  (DerivedCategory.Plus.homologyFunctor
    (ModuleCat.{v} (Y.structureSheaf.obj.obj
      (op (⊤ : Opens Y.carrier)))) i).map
    (ringedSpaceModuleFunctorialDerivedGlobalMap f G F φ)

/-! ## The resolution-level square from the source remark -/

structure BoundedBelowInjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : CompPlus A) where
  target : CompPlus A
  map : K ⟶ target
  target_injective : ∀ n : ℤ, Injective (target.obj.X n)
  map_quasiIso : CochainComplex.Plus.quasiIso A map

structure RingedSpaceFunctorialityResolutionData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    {G : CompPlus (Mod Y.structureSheaf)}
    {F : CompPlus (Mod X.structureSheaf)}
    (φ : RingedSpaceComplexFMap f G F) where
  F_resolution : BoundedBelowInjectiveResolution F
  G_resolution : BoundedBelowInjectiveResolution G
  pushforward_resolution :
    BoundedBelowInjectiveResolution
      ((ringedSpaceModulePushforwardComplex f).obj F_resolution.target)
  beta : G_resolution.target ⟶ pushforward_resolution.target
  commutes :
    G_resolution.map ≫ beta =
      φ ≫ (ringedSpaceModulePushforwardComplex f).map F_resolution.map ≫
        pushforward_resolution.map
  global_sections_pushforward_component : ∀ n : ℤ, Nonempty
    (((ringedSpaceModuleGlobalSections Y).obj
        (((ringedSpaceModulePushforwardComplex f).obj
          F_resolution.target).obj.X n)) ≅
      ((ringedSpaceOpenSectionsRestriction f (⊤ : Opens Y.carrier)).obj
        ((ringedSpaceModuleGlobalSections X).obj
          (F_resolution.target.obj.X n))))
  global_sections_pushforward_quasiIso :
    CochainComplex.Plus.quasiIso (ModuleCat.{v} (Y.structureSheaf.obj.obj
      (op (⊤ : Opens Y.carrier))))
      ((ringedSpaceModuleGlobalSectionsComplex Y).map
        pushforward_resolution.map)

theorem exists_ringedSpaceFunctorialityResolutionData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    {G : CompPlus (Mod Y.structureSheaf)}
    {F : CompPlus (Mod X.structureSheaf)}
    (φ : RingedSpaceComplexFMap f G F) :
    Nonempty (RingedSpaceFunctorialityResolutionData f φ) := by
  sorry

end Formalization.Books.Cohomology.Unit11
