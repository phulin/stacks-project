import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Formalization.Books.MoreAlgebra.Unit02.AdviceForReader
import Formalization.Books.Sheaves.Unit22.RingedSpaces

/-!
# Derived Categories of Schemes, Chapter 2: Conventions

The source identifies an object of an abelian category with the complex
concentrated in degree zero and then uses the corresponding objects in the
homotopy and derived categories.  Mathlib's single functors are the canonical
implementation of this convention.

For a ring, the source's `K(A)` and `D(A)` are represented by the homotopy and
unbounded derived categories of `ModuleCat A`.  For a ringed space, the
coefficient category is the canonical category `Mod X.structureSheaf` of
sheaves of modules over its structure sheaf.
-/

namespace Formalization.Books.Perfect.Unit02

open CategoryTheory
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe w v u

/-! ## Objects concentrated in degree zero -/

/--
The cochain complex used for the source's convention that an object `M` of an
abelian category is viewed as a complex with `M` in degree zero.
-/
noncomputable abbrev degreeZeroComplex
    (C : Type u) [Category.{v} C] [Abelian C] (M : C) :
    CochainComplex C ℤ :=
  (CochainComplex.singleFunctor C 0).obj M

/-- The corresponding object of the homotopy category `K(C)`. -/
noncomputable abbrev degreeZeroHomotopyObject
    (C : Type u) [Category.{v} C] [Abelian C] (M : C) :
    HomotopyCategory C (ComplexShape.up ℤ) :=
  (HomotopyCategory.singleFunctor C 0).obj M

/-- The corresponding object of the derived category `D(C)`. -/
noncomputable abbrev degreeZeroDerivedObject
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (M : C) :
    DerivedCategory C :=
  (DerivedCategory.singleFunctor C 0).obj M

/-! ## The categories denoted by `K(A)` and `D(A)` for a ring -/

/-- The homotopy category of complexes of left `R`-modules. -/
abbrev moduleHomotopyCategory (R : Type u) [Ring R] : Type _ :=
  HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)

/-- The unbounded derived category of left `R`-modules. -/
abbrev moduleDerivedCategory (R : Type u) [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] : Type _ :=
  Formalization.Books.MoreAlgebra.Unit02.UnboundedDerivedCategory R

/-! ## The categories denoted by `K(𝒪_X)` and `D(𝒪_X)` -/

/-- The coefficient category of sheaves of modules on a ringed space. -/
abbrev ringedSpaceModuleCategory (X : RingedSpace.{v}) : Type _ :=
  Mod X.structureSheaf

/-- The homotopy category of complexes of modules on a ringed space. -/
abbrev ringedSpaceModuleHomotopyCategory (X : RingedSpace.{v}) : Type _ :=
  HomotopyCategory (ringedSpaceModuleCategory X) (ComplexShape.up ℤ)

/-- The derived category of complexes of modules on a ringed space. -/
abbrev ringedSpaceModuleDerivedCategory (X : RingedSpace.{v})
    [HasDerivedCategory.{w} (ringedSpaceModuleCategory X)] : Type _ :=
  DerivedCategory (ringedSpaceModuleCategory X)

end Formalization.Books.Perfect.Unit02
