import Formalization.Books.Cohomology.Unit34.InternalHom
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Cohomology of Sheaves, Chapter 36: Global derived hom

This file records the global derived Hom object, its cohomology/Ext
identifications, and the functorial pullback map from the source section.
-/

noncomputable section

open CategoryTheory
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit34

universe v

namespace Formalization.Books.Cohomology.Unit36

/-! ## Global derived Hom and its cohomology -/

/-- The global derived Hom object `RΓ(X, R𝒮Hom(K, L))`. -/
noncomputable abbrev globalDerivedHom
    (X : RingedSpace.{v}) (K L : Derived X) : GlobalDerived X :=
  (derivedGlobalSections X).obj (derivedSheafHom X K L)

/-- The degree-`p` cohomology module of the global derived Hom object. -/
noncomputable abbrev globalDerivedHomCohomology
    (X : RingedSpace.{v}) (K L : Derived X) (p : ℤ) : GlobalModule X :=
  (globalCohomologyObject X p).obj (derivedSheafHom X K L)

/-- The derived `Ext^p` group, represented as a shifted morphism in the
derived category. -/
abbrev derivedExt
    (X : RingedSpace.{v}) (K L : Derived X) (p : ℤ) : Type _ :=
  ShiftedHom K L p

/-- Degree-zero global derived Hom is the ordinary derived-category Hom. -/
theorem globalDerivedHom_homology_zero
    (X : RingedSpace.{v}) (K L : Derived X) :
    Nonempty ((globalDerivedHomCohomology X K L 0 : Type v) ≃+
      (K ⟶ L)) := by
  sorry

/-- The degree-`p` global derived Hom cohomology is the derived `Ext^p` group. -/
theorem globalDerivedHom_homology_ext
    (X : RingedSpace.{v}) (K L : Derived X) (p : ℤ) :
    Nonempty ((globalDerivedHomCohomology X K L p : Type v) ≃+
      derivedExt X K L p) := by
  sorry

/-! ## Functoriality for a morphism of ringed spaces -/

/- The canonical ring map on global sections for a morphism of commutative
ringed spaces.  The existing `ringedSpaceGlobalSectionsMap` has the same
construction for the older, noncommutative ringed-space interface, whereas
Chapter 34 uses `CommutativeRingedSpace`; the map is therefore recorded as a
small chapter-local interface. -/
structure CommRingedSpaceGlobalSectionsMapData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom Y X) where
  map : X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)) →+*
    Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier))

theorem exists_commRingedSpaceGlobalSectionsMapData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom Y X) :
    Nonempty (CommRingedSpaceGlobalSectionsMapData f) := by
  sorry

noncomputable def commRingedSpaceGlobalSectionsMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom Y X) :
    X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)) →+*
      Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier)) :=
  (Classical.choice (exists_commRingedSpaceGlobalSectionsMapData f)).map

/- The source places the target of the pullback map in
`D(Γ(X, O_X))`.  We therefore view the `Y`-global object as an `X`-module
through the induced map on global sections. -/
noncomputable abbrev globalDerivedRestrictionScalars
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom Y X) :
    GlobalDerived Y ⥤ GlobalDerived X :=
  (ModuleCat.restrictScalars (commRingedSpaceGlobalSectionsMap f)).mapDerivedCategory

structure GlobalDerivedHomPullbackData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom Y X)
    (K L : Derived X) where
  map : globalDerivedHom X K L ⟶
    (globalDerivedRestrictionScalars f).obj
      (globalDerivedHom Y ((derivedPullback f).obj K)
        ((derivedPullback f).obj L))

theorem exists_globalDerivedHomPullbackData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom Y X)
    (K L : Derived X) :
    Nonempty (GlobalDerivedHomPullbackData f K L) := by
  sorry

/-- The canonical pullback map on global derived Hom objects. -/
noncomputable def globalDerivedHomPullback
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom Y X)
    (K L : Derived X) :
    globalDerivedHom X K L ⟶
      (globalDerivedRestrictionScalars f).obj
        (globalDerivedHom Y ((derivedPullback f).obj K)
          ((derivedPullback f).obj L)) :=
  (Classical.choice (exists_globalDerivedHomPullbackData f K L)).map

end Formalization.Books.Cohomology.Unit36
