import Formalization.Books.Homology.Unit06.Extensions
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Data.List.TFAE

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
open scoped ZeroObject

universe v u w

namespace Formalization.Books.Homology.Unit28

/-! ## Projective objects -/

/-- The four conditions in the source's characterization of a projective
object.  The second condition uses the chapter's exact-functor interface for
the preadditive co-Yoneda functor, whose value at `B` is the group of
morphisms `P ⟶ B`. -/
def projectiveConditions
    {C : Type u} [Category.{v} C] [Abelian C] (P : C) : List Prop :=
  [ Projective P,
    Formalization.Books.Categories.Unit23.IsExact
      (preadditiveCoyoneda.obj (Opposite.op P)),
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
coproduct exists.  The proof uses the coproduct universal property and
projective factorization for each summand. -/
theorem projective_coproduct
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} (P : ι → C) [HasCoproduct P]
    [∀ i, Projective (P i)] :
    Projective (∐ P) := by
  refine Projective.mk (fun {E X} f e _ => ?_)
  refine ⟨Sigma.desc (fun i => Projective.factorThru (Sigma.ι P i ≫ f) e), ?_⟩
  apply Sigma.hom_ext
  intro i
  simp

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
