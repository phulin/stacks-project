import Formalization.Books.Cohomology.Unit08.CechCohomology
import Formalization.Books.Derived.Unit17.Core

/-!
# Cohomology of Sheaves, Chapter 13: the base change map

The source constructs base change for a commutative square of ringed spaces
when the two horizontal morphisms are flat.  The flatness interface is the
earlier `FlatRingedSpaceHomData`: it packages the pullback/pushforward
adjunction and exactness of pullback, which is exactly the input needed here.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Formalization.Books.Categories.Unit23
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit17
open Formalization.Books.Homology.Unit03
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v u

namespace Formalization.Books.Cohomology.Unit13

/-! ## Flat pullback on the bounded-below derived category -/

/- The earlier Chapters 8 and 20 deliberately retain exactness as the
  source-facing flatness hypothesis.  Bundling that existing functor with its
  exactness proof lets Mathlib's exact-derived construction do the actual
  derived-category work. -/
noncomputable def flatPullbackExactFunctor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hf : FlatRingedSpaceHomData f) :
    Mod Y.structureSheaf ⥤ₑ Mod X.structureSheaf :=
  ⟨hf.pullback, hf.pullback_isExact⟩

/- Exact functors preserve the canonical bounded-below part of the derived
  category.  This is the one general derived-category interface needed to
  restrict `exactDerivedFunctor` to `D⁺`; its proof belongs to the proof stage. -/
theorem exactDerivedFunctor_preserves_derivedPlus
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A]
    {B : Type u} [Category.{v} B] [Abelian B]
    [HasDerivedCategory B]
    (F : A ⥤ₑ B) :
    ∀ K : DPlus A,
      derivedPlusProperty B
        ((DerivedCategory.Plus.ι (C := A) ⋙ exactDerivedFunctor F).obj K) := by
  sorry

/-- The derived pullback `g^* : D⁺(Y) ⥤ D⁺(X)` for a flat morphism. -/
noncomputable def flatPullbackDerivedFunctor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hf : FlatRingedSpaceHomData f) :
    DPlus (Mod Y.structureSheaf) ⥤ DPlus (Mod X.structureSheaf) :=
  ObjectProperty.lift (derivedPlusProperty (Mod X.structureSheaf))
    (DerivedCategory.Plus.ι (C := Mod Y.structureSheaf) ⋙
      exactDerivedFunctor (flatPullbackExactFunctor f hf))
    (exactDerivedFunctor_preserves_derivedPlus
      (flatPullbackExactFunctor f hf))

/- The source's bounded-below complexes are sent to `D⁺` by the canonical
  homotopy quotient followed by the bounded-below derived localization. -/
noncomputable def boundedBelowComplexToDPlus
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A] :
    CompPlus A ⥤ DPlus A :=
  HomotopyCategory.Plus.quotient A ⋙ DerivedCategory.Plus.Qh (C := A)

/-! ## The commutative square -/

/-- A commutative square of ringed spaces, with the source's names. -/
structure BaseChangeSquare where
  X' : RingedSpace.{v}
  X : RingedSpace.{v}
  S' : RingedSpace.{v}
  S : RingedSpace.{v}
  g' : RingedSpaceHom X' X
  f' : RingedSpaceHom X' S'
  g : RingedSpaceHom S' S
  f : RingedSpaceHom X S
  comm : RingedSpaceHom.comp g' f = RingedSpaceHom.comp f' g

/- The displayed equality `f_*(g')_* = g_*(f')_*` in the construction is
  the canonical pushforward-composition comparison, transported across the
  commutativity field of the square. -/
noncomputable def pushforwardSquareIso (B : BaseChangeSquare) :
    (ringedSpaceModulePushforward B.g' ⋙
        ringedSpaceModulePushforward B.f) ≅
      (ringedSpaceModulePushforward B.f' ⋙
        ringedSpaceModulePushforward B.g) :=
  ringedSpaceModulePushforwardCompIso B.g' B.f ≪≫
    eqToIso (by rw [B.comm]) ≪≫
    (ringedSpaceModulePushforwardCompIso B.f' B.g).symm

/-! ## The base change transformation -/

/-- The source and target functors of the bounded-below base-change map. -/
noncomputable def baseChangeSourceFunctor (B : BaseChangeSquare)
    (hg : FlatRingedSpaceHomData B.g) :
    DPlus (Mod B.X.structureSheaf) ⥤
      DPlus (Mod B.S'.structureSheaf) :=
  ringedSpaceModuleDerivedPushforward B.f ⋙
    flatPullbackDerivedFunctor B.g hg

noncomputable def baseChangeTargetFunctor (B : BaseChangeSquare)
    (hg' : FlatRingedSpaceHomData B.g') :
    DPlus (Mod B.X.structureSheaf) ⥤
      DPlus (Mod B.S'.structureSheaf) :=
  flatPullbackDerivedFunctor B.g' hg' ⋙
    ringedSpaceModuleDerivedPushforward B.f'

/-- The canonical bounded-below base-change transformation. -/
structure BaseChangeMapData (B : BaseChangeSquare)
    (hg : FlatRingedSpaceHomData B.g)
    (hg' : FlatRingedSpaceHomData B.g') where
  transformation :
    baseChangeSourceFunctor B hg ⟶ baseChangeTargetFunctor B hg'

/-- Existence of the canonical base-change map in `D⁺(S')`. -/
theorem exists_canonicalBaseChangeMap (B : BaseChangeSquare)
    (hg : FlatRingedSpaceHomData B.g)
    (hg' : FlatRingedSpaceHomData B.g') :
    Nonempty (BaseChangeMapData B hg hg') := by
  sorry

/-- A chosen canonical base-change transformation. -/
noncomputable def canonicalBaseChangeMap (B : BaseChangeSquare)
    (hg : FlatRingedSpaceHomData B.g)
    (hg' : FlatRingedSpaceHomData B.g') :
    baseChangeSourceFunctor B hg ⟶ baseChangeTargetFunctor B hg' :=
  (Classical.choice (exists_canonicalBaseChangeMap B hg hg')).transformation

/-- The source statement for a bounded-below complex, expressed at its
    associated object of `D⁺`. -/
theorem exists_baseChangeMap_flat (B : BaseChangeSquare)
    (hg : FlatRingedSpaceHomData B.g)
    (hg' : FlatRingedSpaceHomData B.g')
    (F : CompPlus (Mod B.X.structureSheaf)) :
    Nonempty (
      (baseChangeSourceFunctor B hg).obj
          (boundedBelowComplexToDPlus.obj F) ⟶
        (baseChangeTargetFunctor B hg').obj
          (boundedBelowComplexToDPlus.obj F)) := by
  exact ⟨(canonicalBaseChangeMap B hg hg').app
    (boundedBelowComplexToDPlus.obj F)⟩

/- The construction chooses an injective resolution of `F` and one of
  `g'^*F`; the earlier `ComplexInjectiveResolution` package and its
  `injective_resolution_lift_up_to_homotopy` / uniqueness theorem are the
  resolution and homotopy interfaces used by the proof. -/

/-! ## The unbounded warning -/

/- The source's final remark is a type-level warning: in general the derived
  pullbacks are `Lg^*` and `L(g')^*`, and the complexes need not be bounded
  below.  The declaration below records the exact natural-transformation type
  without asserting an unproved general existence theorem. -/
abbrev unboundedBaseChangeMap
    (B : BaseChangeSquare)
    (Lg : DerivedCategory (Mod B.S.structureSheaf) ⥤
      DerivedCategory (Mod B.S'.structureSheaf))
    (Lg' : DerivedCategory (Mod B.X.structureSheaf) ⥤
      DerivedCategory (Mod B.X'.structureSheaf))
    (Rf : DerivedCategory (Mod B.X.structureSheaf) ⥤
      DerivedCategory (Mod B.S.structureSheaf))
    (Rf' : DerivedCategory (Mod B.X'.structureSheaf) ⥤
      DerivedCategory (Mod B.S'.structureSheaf)) :
    Type _ := (Rf ⋙ Lg) ⟶ (Lg' ⋙ Rf')

end Formalization.Books.Cohomology.Unit13
