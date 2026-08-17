import Formalization.Books.Sheaves.Unit17.AlgebraicStructures

/-!
# Sheaves on Spaces, Chapter 19: Sheafification of presheaves of algebraic structures

The source span is `books/sheaves.tex:1778-1820`.  The exact source section
was already formalized in the earlier canonical algebraic-sheafification API;
this module exposes that API in the chapter-19 namespace without introducing
a second sheafification construction.

The source's proof-level fibre-product diagram is accounted for by the
`AlgebraicSheafificationData` package and the underlying set and algebraic
structure interfaces from Chapters 5, 15, and 17.  The formal statements here
retain the source's hypotheses, underlying-sheaf identification, and unique
factorization property.
-/

namespace Formalization.Books.Sheaves.Unit19

open CategoryTheory Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit15

universe u v

noncomputable section

/-! ## The source-facing algebraic sheafification interface -/

/-- A candidate sheafification of a presheaf valued in an algebraic category.

This is the canonical source-facing package from Chapter 17, re-exported in
the namespace of the present source section. -/
abbrev AlgebraicSheafificationData
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    (F : PresheafWithValues X C) : Type (max u v) :=
  Formalization.Books.Sheaves.Unit17.AlgebraicSheafificationData U F

/-- The chosen algebraic sheafification object. -/
abbrev algebraicSheafification
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    {F : PresheafWithValues X C}
    (D : AlgebraicSheafificationData U F) : TopCat.Sheaf C X :=
  Formalization.Books.Sheaves.Unit17.algebraicSheafification U D

/-- The chosen morphism from the presheaf to its algebraic sheafification. -/
abbrev algebraicSheafificationUnit
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    {F : PresheafWithValues X C}
    (D : AlgebraicSheafificationData U F) : F ⟶
      (algebraicSheafification U D).presheaf :=
  Formalization.Books.Sheaves.Unit17.algebraicSheafificationUnit U D

/-- Existence and the unique factorization property of algebraic
sheafification. -/
theorem exists_algebraicSheafification
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    (F : PresheafWithValues X C) :
    ∃ D : AlgebraicSheafificationData U F,
      ∀ (G : TopCat.Sheaf C X) (φ : F ⟶ G.presheaf),
        ∃! ψ : D.sheaf ⟶ G, D.unit ≫ ψ.hom = φ := by
  exact Formalization.Books.Sheaves.Unit17.exists_algebraicSheafification U F

/-- The underlying sheaf of sets of the algebraic sheafification is the
ordinary sheafification of the underlying presheaf. -/
theorem algebraicSheafification_underlying_iso
    {C : Type u} [Category.{v} C] (U : C ⥤ Type v)
    [AlgebraicStructureType C U] {X : TopCat.{v}}
    {F : PresheafWithValues X C}
    (D : AlgebraicSheafificationData U F) :
    Nonempty
      (underlyingPresheaf U D.sheaf.presheaf ≅
        (Formalization.Books.Sheaves.Unit17.sheafification
          (underlyingPresheaf U F)).presheaf) := by
  exact Formalization.Books.Sheaves.Unit17.algebraicSheafification_underlying_iso
    U D

end

end Formalization.Books.Sheaves.Unit19
