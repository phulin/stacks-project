import Formalization.Books.Sheaves.Unit06.PresheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Topology.Sheaves.Sheaf

/-!
# Sheaves on Spaces, Chapter 10: Sheaves of modules

This file formalizes the precise statements in `books/sheaves.tex`, lines
856--892.  Mathlib's `SheafOfModules` is the canonical implementation of the
source definition: its `val` field is a presheaf of modules over the ring
presheaf underlying the sheaf of rings, and its `isSheaf` field asserts that
the underlying presheaf of abelian groups is a sheaf.

The source's final warning is reflected by the type of `RingSheaf`: the
sheaf-of-modules interface below requires an actual sheaf of rings, while the
presheaf-only construction belongs to Chapter 6.
-/

namespace Formalization.Books.Sheaves.Unit10

open CategoryTheory TopologicalSpace

universe w v

/-! ## Sheaves of modules and their morphisms -/

/-- A sheaf of rings on the topological space `X`. -/
abbrev RingSheaf (X : TopCat.{v}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) (RingCat.{w})

/-- A sheaf of modules over the sheaf of rings `O`.

This is Mathlib's canonical `SheafOfModules` structure.  Its sheaf field is
the source's requirement that the underlying presheaf of abelian groups be a
sheaf.
-/
abbrev SheafOfOModules {X : TopCat.{v}} (O : RingSheaf.{w, v} X) :=
  _root_.SheafOfModules.{w} O

/-- The category `Mod(O)` of sheaves of `O`-modules. -/
abbrev Mod {X : TopCat.{v}} (O : RingSheaf.{w, v} X) :=
  SheafOfOModules O

/-- A morphism of sheaves of `O`-modules. -/
abbrev SheafOfOModulesMorphism {X : TopCat.{v}}
    {O : RingSheaf.{w, v} X} {F G : Mod O} := F ⟶ G

/-- The source's `Hom_O(F, G)`, represented by the canonical hom type. -/
abbrev OModuleHom {X : TopCat.{v}} {O : RingSheaf.{w, v} X}
    (F G : Mod O) := F ⟶ G

end Formalization.Books.Sheaves.Unit10
