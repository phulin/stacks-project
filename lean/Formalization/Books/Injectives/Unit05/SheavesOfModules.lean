import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.Sheaves.Unit25.Infrastructure
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Injectives, Chapter 5: Sheaves of modules on a ringed space

The ringed-space and sheaf-of-modules objects are the canonical interfaces
from the earlier Sheaves chapters.  The pointwise construction in the source
is represented by the existing module skyscrapers and their product; the
underlying additive sheaf is also recorded separately so that the formula
`U ↦ ∏ x ∈ U, I x` remains visible.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Homology.Unit27
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

namespace Formalization.Books.Injectives.Unit05

/-! ## Stalkwise modules and the pointwise product -/

/-- The `𝒪_{X,x}`-module obtained by taking the stalk of an `𝒪_X`-module. -/
abbrev stalkModule (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (x : X) :=
  ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x))

/-- The additive skyscraper used to describe the underlying sheaf of a module
skyscraper.  The generic Mathlib construction is used with classical
decidability of membership in an open. -/
noncomputable def additiveSkyscraperSheaf (X : RingedSpace.{v}) (x : X)
    (A : AddCommGrpCat.{v}) : TopCat.Sheaf AddCommGrpCat.{v} X.carrier := by
  classical
  exact skyscraperSheaf x A

/-- Data for a sheaf of `𝒪_X`-modules whose underlying additive sheaf is the
skyscraper with prescribed value `I` at `x`. -/
structure ModuleSkyscraperData (X : RingedSpace.{v}) (x : X)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) where
  sheaf : Mod X.structureSheaf
  underlying_iso :
    Nonempty (sheaf.val.presheaf ≅
      (additiveSkyscraperSheaf X x (AddCommGrpCat.of (I : Type v))).presheaf)

/-- Existence of the module-valued skyscraper construction.  The underlying
additive sheaf is the canonical Mathlib skyscraper; the scalar action is the
source's varying stalk-sheaf action. -/
theorem exists_moduleSkyscraperSheaf (X : RingedSpace.{v}) (x : X)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    Nonempty (ModuleSkyscraperData X x I) := by
  sorry

/-- A chosen module-valued skyscraper sheaf. -/
noncomputable def moduleSkyscraperSheaf (X : RingedSpace.{v}) (x : X)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    Mod X.structureSheaf :=
  (Classical.choice (exists_moduleSkyscraperSheaf X x I)).sheaf

/-- The family of modules occurring in the source's pointwise formula. -/
abbrev pointwiseProductValue (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
    (U : Opens X.carrier) : Type v :=
  ∀ x : U, (I x : Type v)

/-- The underlying additive sheaf `U ↦ ∏_{x ∈ U} I_x`, expressed as the
product of the canonical additive skyscraper sheaves. -/
noncomputable def pointwiseProductSheaf (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    TopCat.Sheaf AddCommGrpCat.{v} X.carrier :=
  ∏ᶜ fun x : X => additiveSkyscraperSheaf X x (AddCommGrpCat.of (I x : Type v))

/-- The value of the pointwise product sheaf is the product over the points
of the open set, with the zero factors outside the open set omitted. -/
theorem pointwiseProductSheaf_value_formula (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
    (U : Opens X.carrier) :
    Nonempty
      ((pointwiseProductSheaf X I).presheaf.obj (op U) ≅
        AddCommGrpCat.of (pointwiseProductValue X I U)) := by
  sorry

/-! ## The module skyscraper product -/

/-- The sheaf of `𝒪_X`-modules obtained by taking the product of the module
skyscrapers with stalk values `I_x`. -/
noncomputable def skyscraperProduct (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    Mod X.structureSheaf :=
  ∏ᶜ fun x : X => moduleSkyscraperSheaf X x (I x)

/-- The underlying additive presheaf of the module skyscraper product is the
pointwise product presheaf. -/
theorem skyscraperProduct_underlying_iso (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    Nonempty
      ((skyscraperProduct X I).val.presheaf ≅
        (pointwiseProductSheaf X I).presheaf) := by
  sorry

/-- The displayed section formula for the `𝒪_X`-module product. -/
theorem skyscraperProduct_value_formula (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
    (U : Opens X.carrier) :
    Nonempty
      ((skyscraperProduct X I).val.presheaf.obj (op U) ≅
        AddCommGrpCat.of (pointwiseProductValue X I U)) := by
  sorry

/-! ## The canonical stalk map and injectivity -/

/-- Stalkwise data for the injective modules `I_x` and the embeddings of the
stalks of a fixed sheaf `F`. -/
structure StalkwiseInjectiveEmbeddingData
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) where
  I : ∀ x : X, ModuleCat.{v}
    (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)
  j : ∀ x : X, stalkModule X F x ⟶ I x
  mono_j : ∀ x : X, Mono (j x)
  injective_I : ∀ x : X, Injective (I x)

/-- The stalk/skyscraper Hom correspondence used in the source. -/
theorem exists_stalkSkyscraperHomEquiv (X : RingedSpace.{v}) (x : X)
    (F : Mod X.structureSheaf)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    Nonempty ((stalkModule X F x ⟶ I) ≃
      (F ⟶ moduleSkyscraperSheaf X x I)) := by
  sorry

/-- A chosen stalk/skyscraper Hom equivalence. -/
noncomputable def stalkSkyscraperHomEquiv (X : RingedSpace.{v}) (x : X)
    (F : Mod X.structureSheaf)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    (stalkModule X F x ⟶ I) ≃
      (F ⟶ moduleSkyscraperSheaf X x I) :=
  Classical.choice (exists_stalkSkyscraperHomEquiv X x F I)

/-- Each module skyscraper with injective support stalk is injective. -/
theorem moduleSkyscraper_injective (X : RingedSpace.{v}) (x : X)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
    (hI : Injective I) :
    Injective (moduleSkyscraperSheaf X x I) := by
  sorry

/-- A product of module skyscrapers with injective stalk values is injective. -/
theorem skyscraperProduct_injective (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
    (hI : ∀ x : X, Injective (I x)) :
    Injective (skyscraperProduct X I) := by
  sorry

/-- The source's canonical map from a sheaf to the product of the chosen
injective stalk modules. -/
noncomputable def stalkwiseProductMap (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (D : StalkwiseInjectiveEmbeddingData X F) :
    F ⟶ skyscraperProduct X D.I :=
  Pi.lift fun x => stalkSkyscraperHomEquiv X x F (D.I x) (D.j x)

/-- The component of the product map at `x` is the skyscraper morphism
corresponding to the stalk embedding `j_x`; this is the Lean form of
`s ↦ (j_x(s_x))_x`. -/
theorem stalkwiseProductMap_component (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (D : StalkwiseInjectiveEmbeddingData X F)
    (x : X) :
    stalkwiseProductMap X F D ≫
        Pi.π (fun x : X => moduleSkyscraperSheaf X x (D.I x)) x =
      stalkSkyscraperHomEquiv X x F (D.I x) (D.j x) := by
  sorry

/-- The canonical stalkwise map is a monomorphism. -/
theorem stalkwiseProductMap_mono (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (D : StalkwiseInjectiveEmbeddingData X F) :
    Mono (stalkwiseProductMap X F D) := by
  sorry

/-- The target of the canonical stalkwise map is injective. -/
theorem stalkwiseProductMap_target_injective (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (D : StalkwiseInjectiveEmbeddingData X F) :
    Injective (skyscraperProduct X D.I) :=
  skyscraperProduct_injective X D.I D.injective_I

/-- Stalkwise injective embedding data exist for every sheaf of modules. -/
theorem exists_stalkwiseInjectiveEmbeddingData (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) :
    Nonempty (StalkwiseInjectiveEmbeddingData X F) := by
  sorry

/-! ## Enough injectives and functorial embeddings -/

/-- The category of sheaves of modules on a ringed space has enough
injectives, and the embeddings can be chosen functorially. -/
theorem sheafOfModules_has_enough_injectives (X : RingedSpace.{v}) :
    EnoughInjectives (Mod X.structureSheaf) ∧
      HasFunctorialInjectiveEmbeddings (C := Mod X.structureSheaf) := by
  sorry

end Formalization.Books.Injectives.Unit05
