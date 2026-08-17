import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Formalization.Books.Sheaves.Unit17.Sheafification

/-!
# Sheaves on Spaces, Chapter 17, Section 3: Sheafification of presheaves of
algebraic structures

The source span is `books/sheaves.tex:1778-1820`.  The category-valued
presheaf and the underlying set-valued presheaf are the canonical objects
from Chapter 5.  The existence theorem records the source's two properties:
the underlying sheaf is the ordinary sheafification, and maps to a sheaf
factor uniquely through the chosen algebraic sheafification.
-/

namespace Formalization.Books.Sheaves.Unit17

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit15

universe u v

noncomputable section

/-! ## The source-facing existence package -/

/-- A candidate sheafification of a presheaf valued in an algebraic category.

The underlying isomorphism identifies the underlying sheaf with ordinary
sheafification, and `underlying_unit` records that this identification is
the one induced by the algebraic unit rather than an unrelated isomorphism. -/
structure AlgebraicSheafificationData
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    (F : PresheafWithValues X C) where
  sheaf : TopCat.Sheaf C X
  unit : F ⟶ sheaf.presheaf
  underlying_iso :
    underlyingPresheaf U sheaf.presheaf ≅
      (sheafification (underlyingPresheaf U F)).presheaf
  underlying_unit :
    underlyingPresheafMorphism U unit ≫ underlying_iso.hom =
      sheafificationUnit (underlyingPresheaf U F)

/-- The chosen algebraic sheafification object. -/
abbrev algebraicSheafification
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    {F : PresheafWithValues X C}
    (D : AlgebraicSheafificationData U F) : TopCat.Sheaf C X :=
  D.sheaf

/-- The chosen unit into the algebraic sheafification. -/
abbrev algebraicSheafificationUnit
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    {F : PresheafWithValues X C}
    (D : AlgebraicSheafificationData U F) : F ⟶
      (algebraicSheafification U D).presheaf :=
  D.unit

/-- Existence and the universal factorization property for algebraic
sheafification. -/
theorem exists_algebraicSheafification
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    (F : PresheafWithValues X C) :
    ∃ D : AlgebraicSheafificationData U F,
      ∀ (G : TopCat.Sheaf C X) (φ : F ⟶ G.presheaf),
        ∃! ψ : D.sheaf ⟶ G, D.unit ≫ ψ.1 = φ := by
  sorry

/-- The underlying sheaf assertion in the source, exposed independently for
users that do not need the universal property. -/
theorem algebraicSheafification_underlying_iso
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    {F : PresheafWithValues X C}
    (D : AlgebraicSheafificationData U F) :
    Nonempty
      (underlyingPresheaf U D.sheaf.presheaf ≅
        (sheafification (underlyingPresheaf U F)).presheaf) := by
  exact ⟨D.underlying_iso⟩

end

end Formalization.Books.Sheaves.Unit17
