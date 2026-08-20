import Formalization.Books.Cohomology.Unit07.LocalityOfCohomology
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Cohomology of Sheaves, Chapter 8: Mayer--Vietoris

This file records the absolute and relative Mayer--Vietoris long exact
sequences.  The absolute sequence is Mathlib's Mayer--Vietoris sequence for
the underlying sheaf of abelian groups; this file only packages that API for
sheaves of modules on a ringed space.  The relative sequence is the same
construction after pulling back an arbitrary open subset of the target.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit07
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
abbrev mathlibCohomologyOnOpen
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℕ) : AddCommGrpCat.{v} :=
  CategoryTheory.Sheaf.H'.{v} (underlyingAdditiveSheaf X F) i U

/-- The chapter's derived-functor model of `Hⁱ(U, F)`.  The
Mayer--Vietoris sequence below deliberately uses `mathlibCohomologyOnOpen`;
a comparison between these two models belongs with the general comparison of
derived-functor and `Ext`-based sheaf cohomology. -/
noncomputable abbrev cohomologyOnOpenAdditive
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) : AddCommGrpCat.{v} :=
  (forget₂ (ModuleCat (X.structureSheaf.obj.obj (op U))) AddCommGrpCat).obj
    (ringedSpaceModuleSectionsCohomologyObject X U F i)

/-- Restriction in cohomology along an inclusion of open subsets. -/
abbrev mathlibCohomologyOnOpenRestriction
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℕ)
    {U V : Opens X.carrier} (h : U ≤ V) :
    mathlibCohomologyOnOpen X V F i ⟶ mathlibCohomologyOnOpen X U F i :=
  ((underlyingAdditiveSheaf X F).cohomologyPresheaf i).map (homOfLE h).op

/-- The connecting map in the Mayer--Vietoris sequence of two open subsets. -/
noncomputable abbrev mayerVietorisδ
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (U V : Opens X.carrier) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    mathlibCohomologyOnOpen X (U ⊓ V) F n₀ ⟶
      mathlibCohomologyOnOpen X (U ⊔ V) F n₁ :=
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

/-- The inverse image of an open subset along a morphism of ringed spaces. -/
abbrev relativeOpen {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (W : Opens Y.carrier) : Opens X.carrier :=
  (Opens.map f.continuous).obj W

/-- Cohomology on the intersection of an open subset of `X` with the inverse
image of an open subset of the target.  These are the sectionwise values from
which the relative Mayer--Vietoris sequence is assembled. -/
abbrev relativeCohomologyOn
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (U : Opens X.carrier)
    (n : ℕ) (W : Opens Y.carrier) : AddCommGrpCat.{v} :=
  mathlibCohomologyOnOpen X (relativeOpen f W ⊓ U) F n

/-- The connecting map in relative Mayer--Vietoris, evaluated on an open
subset of the target. -/
noncomputable abbrev relativeMayerVietorisδ
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (U V : Opens X.carrier)
    (W : Opens Y.carrier) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :=
  mayerVietorisδ X F (relativeOpen f W ⊓ U) (relativeOpen f W ⊓ V) n₀ n₁ h

/-- Six consecutive terms of the relative Mayer--Vietoris sequence,
evaluated on an open subset of the target. -/
noncomputable abbrev relativeMayerVietorisSequence
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (U V : Opens X.carrier)
    (W : Opens Y.carrier) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{v} 5 :=
  mayerVietorisSequence X F
    (relativeOpen f W ⊓ U) (relativeOpen f W ⊓ V) n₀ n₁ h

/-- The sectionwise relative Mayer--Vietoris sequence is exact. -/
theorem relativeMayerVietorisSequence_exact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (U V : Opens X.carrier)
    (W : Opens Y.carrier) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (relativeMayerVietorisSequence f F U V W n₀ n₁ h).Exact :=
  mayerVietorisSequence_exact X F
    (relativeOpen f W ⊓ U) (relativeOpen f W ⊓ V) n₀ n₁ h

/-- If `U` and `V` cover `X`, their intersections with the inverse image of
any target open cover that inverse image. -/
lemma relativeOpen_inf_sup {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    {U V : Opens X.carrier} (hcover : U ⊔ V = ⊤) (W : Opens Y.carrier) :
    (relativeOpen f W ⊓ U) ⊔ (relativeOpen f W ⊓ V) = relativeOpen f W := by
  rw [← inf_sup_left, hcover, inf_top_eq]

end Formalization.Books.Cohomology.Unit08
