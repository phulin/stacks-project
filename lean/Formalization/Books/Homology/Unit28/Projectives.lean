import Formalization.Books.Homology.Unit06.Extensions
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Homological Algebra, Chapter 28: Projectives

The source's projective objects and categories with enough projectives are
Mathlib's canonical `Projective`, `ProjectivePresentation`, and
`EnoughProjectives` interfaces.  Short exact sequences are represented by
`ShortComplex.ShortExact`, and their splittings by `ShortComplex.Splitting`.
The extension group in the characterization is the extension-class group
constructed in Chapter 6.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace Formalization.Books.Homology.Unit28

/-! ## Projective objects -/

/-- The four conditions in the source's characterization of a projective
object.  The second condition uses Mathlib's exact-functor property for the
preadditive co-Yoneda functor, whose value at `B` is the module of morphisms
`P ⟶ B` (and hence in particular the underlying Hom group). -/
def projectiveConditions
    {C : Type u} [Category.{v} C] [Abelian C] (P : C) : List Prop :=
  [ Projective P,
    exactFunctor C (ModuleCat.{v} (End P)ᵐᵒᵖ) (preadditiveCoyonedaObj P),
    ∀ (A B : C) (f : A ⟶ B) (g : B ⟶ P) (h : f ≫ g = 0),
      (ShortComplex.mk f g h).ShortExact →
        Nonempty (ShortComplex.mk f g h).Splitting,
    ∀ (A : C) (ξ : Formalization.Books.Homology.Unit06.Ext P A), ξ = 0 ]

/-- Projectivity is equivalent to exactness of the covariant Hom functor,
splitting of every short exact sequence ending in `P`, and vanishing of all
extension classes with first argument `P`. -/
theorem projective_characterization
    {C : Type u} [Category.{v} C] [Abelian C] (P : C) :
    List.TFAE (projectiveConditions P) := by
  sorry

/-! ## Coproducts and enough projectives -/

/-- A coproduct of a family of projective objects is projective whenever the
coproduct exists.  The proof uses Mathlib's canonical coproduct instance. -/
theorem projective_coproduct
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type v} (P : ι → C) [HasCoproduct P]
    [∀ i, Projective (P i)] :
    Projective (∐ P) := by
  infer_instance

/- The source's “enough projectives” definition is exactly Mathlib's
   `EnoughProjectives C`, whose presentations are
   `ProjectivePresentation X`. -/

/-! ## Functorial projective surjections -/

/-- The source's functorial choice of projective epimorphisms.  The functor
lands in the canonical arrow category; `Arrow.rightFunc` records the target,
`Arrow.left` the source, and `Arrow.hom` the chosen morphism. -/
def HasFunctorialProjectiveSurjections
    {C : Type u} [Category.{v} C] [Abelian C] : Prop :=
  ∃ P : C ⥤ Arrow C,
    P ⋙ Arrow.rightFunc = 𝟭 C ∧
      (∀ A : C, Epi (Arrow.hom (P.obj A))) ∧
        ∀ A : C, Projective (Arrow.left (P.obj A))

end Formalization.Books.Homology.Unit28
