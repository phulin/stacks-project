import Formalization.Books.Sheaves.Unit22.RingedSpaces
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Sheaves of Modules, Chapter 2: Pathology

The source section records that a ringed space may have the zero ring as its
structure sheaf.  The existing Chapter 22 `RingedSpace` is the canonical
ringed-space interface, so this file only adds the zero example and the
source-facing consequences that are not already definitions or Mathlib APIs.
-/

namespace Formalization.Books.Modules.Unit02

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## The zero structure sheaf -/

/-- The terminal (hence one-element, or zero) sheaf of rings on `X`. -/
noncomputable def zeroRingSheaf (X : TopCat.{v}) : RingSheaf.{v, v} X :=
  Sheaf.terminal (Opens.grothendieckTopology X)
    (terminalIsTerminal (C := RingCat.{v}))

/-- A ringed space whose structure sheaf is the zero sheaf. -/
noncomputable def zeroRingedSpace (X : TopCat.{v}) : RingedSpace.{v} where
  carrier := X
  structureSheaf := zeroRingSheaf X

/-- The zero structure sheaf is terminal among sheaves of rings. -/
noncomputable def zeroRingSheaf_isTerminal (X : TopCat.{v}) :
    IsTerminal (zeroRingSheaf X) := by
  exact Sheaf.isTerminalTerminal _ (terminalIsTerminal (C := RingCat.{v}))

/-- The assertion that the structure sheaf is the zero ring on an open. -/
def StructureSheafIsZeroOn (X : RingedSpace.{v}) (U : Opens X.carrier) : Prop :=
  Nonempty (IsTerminal (X.structureSheaf.obj.obj (op U)))

/-- The zero ringed space has zero sections on every open subset. -/
theorem zeroRingedSpace_structureSheaf_isZeroOn
    (X : TopCat.{v}) (U : Opens X) :
    StructureSheafIsZeroOn (zeroRingedSpace X) U := by
  exact ⟨terminalIsTerminal⟩

/-! ## Modules over the zero structure sheaf -/

/-- The category of modules over the zero structure sheaf is still abelian. -/
theorem zeroRingedSpace_module_category_isAbelian (X : TopCat.{v}) :
    Nonempty (Abelian (Mod (zeroRingedSpace X).structureSheaf)) := by
  exact ⟨inferInstance⟩

/-- Every module over the zero structure sheaf is a zero object; this is the
source's assertion that the module category has only the zero object. -/
theorem zeroRingedSpace_module_category_isZero
    (X : TopCat.{v}) (F : Mod (zeroRingedSpace X).structureSheaf) :
    IsZero F := by
  sorry

/-! ## The locally ringed-space warning -/

/-- On a locally ringed space, sections over a nonempty open cannot be the
zero ring.  This is the precise nonempty-open form of the source warning. -/
theorem locallyRingedSpace_nonempty_open_sections_nontrivial
    (X : AlgebraicGeometry.LocallyRingedSpace.{v})
    (U : Opens X.carrier) [Nonempty U] :
    Nontrivial (X.presheaf.obj (op U)) :=
  AlgebraicGeometry.LocallyRingedSpace.component_nontrivial X U

end

end Formalization.Books.Modules.Unit02
