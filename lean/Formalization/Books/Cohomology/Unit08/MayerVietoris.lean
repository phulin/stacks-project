import Formalization.Books.Cohomology.Unit07.LocalityOfCohomology
import Formalization.Books.Homology.Unit20.DifferentialObjects
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Cohomology of Sheaves, Chapter 8: Mayer--Vietoris

This file records the absolute and relative Mayer--Vietoris long exact
sequences.  The absolute sequence is Mathlib's Mayer--Vietoris sequence for
the underlying sheaf of abelian groups; this file only packages that API for
sheaves of modules on a ringed space.  The relative sequence uses the higher
direct images from Chapters 3 and 7.
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

/-! ## Absolute Mayer--Vietoris -/

/-- The underlying sheaf of abelian groups of a sheaf of modules. -/
abbrev underlyingAdditiveSheaf
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :=
  (SheafOfModules.toSheaf X.structureSheaf).obj F

/-- The cohomology `Hⁱ(U, F)` of an open subset, computed by Mathlib on the
underlying sheaf of abelian groups. -/
abbrev cohomologyOnOpenAdditive
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℕ) : AddCommGrpCat.{v} :=
  CategoryTheory.Sheaf.H'.{v} (underlyingAdditiveSheaf X F) i U

/-- Restriction in cohomology along an inclusion of open subsets. -/
abbrev cohomologyOnOpenRestriction
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℕ)
    {U V : Opens X.carrier} (h : U ≤ V) :
    cohomologyOnOpenAdditive X V F i ⟶ cohomologyOnOpenAdditive X U F i :=
  ((underlyingAdditiveSheaf X F).cohomologyPresheaf i).map (homOfLE h).op

/-- The connecting map in the Mayer--Vietoris sequence of two open subsets. -/
noncomputable abbrev mayerVietorisδ
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (U V : Opens X.carrier) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    cohomologyOnOpenAdditive X (U ⊓ V) F n₀ ⟶
      cohomologyOnOpenAdditive X (U ⊔ V) F n₁ :=
  (Opens.mayerVietorisSquare U V).δ (underlyingAdditiveSheaf X F) n₀ n₁ h

/-- Six consecutive terms of the Mayer--Vietoris long exact sequence. -/
noncomputable abbrev mayerVietorisSequence
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (U V : Opens X.carrier) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{v} 5 :=
  (Opens.mayerVietorisSquare U V).sequence
    (underlyingAdditiveSheaf X F) n₀ n₁ h

/-- The Mayer--Vietoris sequence of two open subsets is exact. -/
theorem mayerVietorisSequence_exact
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (U V : Opens X.carrier) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (mayerVietorisSequence X F U V n₀ n₁ h).Exact :=
  (Opens.mayerVietorisSquare U V).sequence_exact
    (underlyingAdditiveSheaf X F) n₀ n₁ h

/-! ## Relative Mayer--Vietoris -/

/-- A degree-preserving morphism between the source-facing relative long
exact sequences. -/
structure LongExactSequenceMorphism {C : Type u} [Category.{v} C]
    [Abelian C] {X Y : ℤ → C}
    (S : LongExactSequence X) (T : LongExactSequence Y) where
  app : ∀ n, X n ⟶ Y n
  comm : ∀ n, S.differential n ≫ app (n + 1) =
    app n ≫ T.differential n

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
      · simp only [relativeMayerVietorisTerm, hn, ↓reduceIte, h₁]
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
