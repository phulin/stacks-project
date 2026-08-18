import Formalization.Books.Cohomology.Unit07.LocalityOfCohomology
import Formalization.Books.Homology.Unit20.DifferentialObjects
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian

/-!
# Cohomology of Sheaves, Chapter 8: Mayer--Vietoris

This file records the injective restriction lemma and the absolute and
relative Mayer--Vietoris long exact sequences.  Cohomology objects and open
restrictions are the canonical constructions from Chapters 3 and 7.  The
long exact sequence itself is represented by the earlier Homology
`LongExactSequence` interface, with additive groups used for the absolute
sequence and sheaves of modules on the target for the relative sequence.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open scoped ZeroObject
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit07
open Formalization.Books.Homology.Unit20
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v u

namespace Formalization.Books.Cohomology.Unit08

/-! ## A morphism of long exact sequences -/

/-- A degree-preserving morphism of the long exact sequences used below. -/
structure LongExactSequenceMorphism {C : Type u} [Category.{v} C]
    [Abelian C] {X Y : ℤ → C}
    (S : LongExactSequence X) (T : LongExactSequence Y) where
  app : ∀ n, X n ⟶ Y n
  comm : ∀ n, S.differential n ≫ app (n + 1) =
    app n ≫ T.differential n

/-! ## The injective restriction lemma -/

/- The source's restriction map is Mathlib's presheaf-of-modules map.  Its
   codomain is a restriction-of-scalars module, whose underlying additive
   group is the group of sections on the smaller open. -/
theorem injective_restriction_surjective
  (X : RingedSpace.{v}) {U' U : Opens X.carrier} (h : U' ≤ U)
    (I : Mod X.structureSheaf) [Injective I] :
    Function.Surjective (moduleRestriction I.val h).hom := by
  sorry

/-! ## Absolute Mayer--Vietoris -/

/-- The additive group underlying `Hⁱ(U, F)`. -/
noncomputable abbrev cohomologyOnOpenAdditive
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) : AddCommGrpCat.{v} :=
  (forget₂ (ModuleCat (X.structureSheaf.obj.obj (op U))) AddCommGrpCat).obj
    (ringedSpaceModuleSectionsCohomologyObject X U F i)

/-- The additive group underlying the middle term
`Hⁱ(U, F) ⊕ Hⁱ(V, F)`. -/
noncomputable abbrev mayerVietorisMiddleAdditive
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) : AddCommGrpCat.{v} :=
  cohomologyOnOpenAdditive X U F i ⨯ cohomologyOnOpenAdditive X V F i

/-- The terms of the absolute Mayer--Vietoris sequence, indexed so that
negative indices are zero and the nonnegative part begins
`H⁰(X,F), H⁰(U,F) ⊕ H⁰(V,F), H⁰(U ∩ V,F), H¹(X,F), ...`. -/
noncomputable def mayerVietorisTerm
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (F : Mod X.structureSheaf) (n : ℤ) : AddCommGrpCat.{v} :=
  if n < 0 then 0
  else if n % 3 = 0 then
    cohomologyOnOpenAdditive X (⊤ : Opens X.carrier) F (n / 3)
  else if n % 3 = 1 then
    mayerVietorisMiddleAdditive X U V F (n / 3)
  else
    cohomologyOnOpenAdditive X (U ⊓ V) F (n / 3)

/-- The canonical termwise map induced by a morphism of coefficient sheaves. -/
noncomputable def mayerVietorisTermMap
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    {F G : Mod X.structureSheaf} (φ : F ⟶ G) (n : ℤ) :
    mayerVietorisTerm X U V F n ⟶ mayerVietorisTerm X U V G n := by
  by_cases hn : n < 0
  · simp only [mayerVietorisTerm, hn, ↓reduceIte]
    exact 0
  · by_cases h₀ : n % 3 = 0
    · simp only [mayerVietorisTerm, hn, ↓reduceIte, h₀]
      exact (forget₂
        (ModuleCat (X.structureSheaf.obj.obj
          (op (⊤ : Opens X.carrier)))) AddCommGrpCat).map
        ((ringedSpaceModuleSectionsCohomology X
          (⊤ : Opens X.carrier) (n / 3)).map φ)
    · by_cases h₁ : n % 3 = 1
      · simp only [mayerVietorisTerm, hn, ↓reduceIte, h₀, h₁]
        exact Limits.prod.map
          ((forget₂
            (ModuleCat (X.structureSheaf.obj.obj (op U))) AddCommGrpCat).map
            ((ringedSpaceModuleSectionsCohomology X U (n / 3)).map φ))
          ((forget₂
            (ModuleCat (X.structureSheaf.obj.obj (op V))) AddCommGrpCat).map
            ((ringedSpaceModuleSectionsCohomology X V (n / 3)).map φ))
      · simp only [mayerVietorisTerm, hn, ↓reduceIte, h₀, h₁]
        exact (forget₂
          (ModuleCat (X.structureSheaf.obj.obj (op (U ⊓ V)))) AddCommGrpCat).map
          ((ringedSpaceModuleSectionsCohomology X (U ⊓ V) (n / 3)).map φ)

/-- The absolute Mayer--Vietoris long exact sequence, including its
functoriality in the coefficient module. -/
theorem exists_mayer_vietoris_long_exact
    (X : RingedSpace.{v}) {U V : Opens X.carrier}
    (hcover : (U : Set X.carrier) ∪ (V : Set X.carrier) = Set.univ) :
    ∃ S : ∀ F : Mod X.structureSheaf,
      LongExactSequence (mayerVietorisTerm X U V F),
      ∀ (F G : Mod X.structureSheaf) (φ : F ⟶ G),
        Nonempty (LongExactSequenceMorphism (S F) (S G)) ∧
          ∀ (η : LongExactSequenceMorphism (S F) (S G)) (n : ℤ),
            η.app n = mayerVietorisTermMap X U V φ n := by
  sorry

/-! ## Relative Mayer--Vietoris -/

/-- The open restrictions of a coefficient module used in the relative
sequence. -/
noncomputable abbrev relativeMayerVietorisRestriction
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) :
    Mod (ringedOpenSubspace X U).structureSheaf :=
  (openModuleRestrictionFunctor X U).obj F

/-- The target morphism obtained by restricting `f` to an open subspace. -/
noncomputable abbrev relativeMayerVietorisMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (U : Opens X.carrier) :
    RingedSpaceHom (ringedOpenSubspace X U) Y :=
  RingedSpaceHom.comp (ringedOpenInclusion X U) f

/-- The terms of the relative Mayer--Vietoris sequence. -/
noncomputable def relativeMayerVietorisTerm
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (U V : Opens X.carrier) (F : Mod X.structureSheaf) (n : ℤ) :
    Mod Y.structureSheaf :=
  if n < 0 then 0
  else if n % 3 = 0 then
    ringedSpaceModuleHigherDirectImageObject f F (n / 3)
  else if n % 3 = 1 then
    (ringedSpaceModuleHigherDirectImageObject
      (relativeMayerVietorisMap f U)
      (relativeMayerVietorisRestriction X U F) (n / 3)) ⨯
      (ringedSpaceModuleHigherDirectImageObject
        (relativeMayerVietorisMap f V)
        (relativeMayerVietorisRestriction X V F) (n / 3))
  else
    ringedSpaceModuleHigherDirectImageObject
      (relativeMayerVietorisMap f (U ⊓ V))
      (relativeMayerVietorisRestriction X (U ⊓ V) F) (n / 3)

/-- The canonical termwise map for the relative sequence. -/
noncomputable def relativeMayerVietorisTermMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (U V : Opens X.carrier) {F G : Mod X.structureSheaf}
    (φ : F ⟶ G) (n : ℤ) :
    relativeMayerVietorisTerm f U V F n ⟶
      relativeMayerVietorisTerm f U V G n := by
  by_cases hn : n < 0
  · simp only [relativeMayerVietorisTerm, hn, ↓reduceIte]
    exact 0
  · by_cases h₀ : n % 3 = 0
    · simp only [relativeMayerVietorisTerm, hn, ↓reduceIte, h₀]
      exact (ringedSpaceModuleHigherDirectImage f (n / 3)).map φ
    · by_cases h₁ : n % 3 = 1
      · simp only [relativeMayerVietorisTerm, hn, ↓reduceIte, h₀, h₁]
        exact Limits.prod.map
          ((ringedSpaceModuleHigherDirectImage
            (relativeMayerVietorisMap f U) (n / 3)).map
            ((openModuleRestrictionFunctor X U).map φ))
          ((ringedSpaceModuleHigherDirectImage
            (relativeMayerVietorisMap f V) (n / 3)).map
            ((openModuleRestrictionFunctor X V).map φ))
      · simp only [relativeMayerVietorisTerm, hn, ↓reduceIte, h₀, h₁]
        exact (ringedSpaceModuleHigherDirectImage
          (relativeMayerVietorisMap f (U ⊓ V)) (n / 3)).map
          ((openModuleRestrictionFunctor X (U ⊓ V)).map φ)

/-- The relative Mayer--Vietoris long exact sequence and its functoriality. -/
theorem exists_relative_mayer_vietoris_long_exact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    {U V : Opens X.carrier}
    (hcover : (U : Set X.carrier) ∪ (V : Set X.carrier) = Set.univ) :
    ∃ S : ∀ F : Mod X.structureSheaf,
      LongExactSequence (relativeMayerVietorisTerm f U V F),
      ∀ (F G : Mod X.structureSheaf) (φ : F ⟶ G),
        Nonempty (LongExactSequenceMorphism (S F) (S G)) ∧
          ∀ (η : LongExactSequenceMorphism (S F) (S G)) (n : ℤ),
            η.app n = relativeMayerVietorisTermMap f U V φ n := by
  sorry

end Formalization.Books.Cohomology.Unit08
