import Formalization.Books.Homology.Unit06.Extensions
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Homological Algebra, Chapter 27: Injectives

The source's injective objects and categories with enough injectives are
Mathlib's `Injective` and `EnoughInjectives` interfaces.  The chapter-facing
characterization below uses the preadditive Yoneda functor, short exact
complexes, and the extension group from Chapter 6.  The final definition is
the one piece of source infrastructure not already present in Mathlib.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit06

universe v u w

namespace Formalization.Books.Homology.Unit27

/-! ## Injective objects and their characterizations -/

/- The source's definition of an injective object is exactly Mathlib's
   `CategoryTheory.Injective`, so no parallel predicate is introduced. -/

/- The four items in the source lemma are combined into one conjunction.  The
   Hom functor is the canonical preadditive Yoneda functor, and its exactness
   is the `IsExact` interface from Categories, Chapter 23. -/
theorem injective_iff_characterizations
    {C : Type u} [Category.{v} C] [Abelian C] (I : C) :
    Injective I ↔
      IsExact (preadditiveYoneda.obj I) ∧
        (∀ {A B : C} (f : I ⟶ A) (g : A ⟶ B) (h : f ≫ g = 0),
          (ShortComplex.mk f g h).ShortExact →
            Nonempty (ShortComplex.mk f g h).Splitting) ∧
        (∀ B : C, ∀ e : Ext B I, e = 0) := by
  constructor
  · intro hI
    let : Injective I := hI
    refine ⟨?_, ?_⟩
    · let hP : (preadditiveYoneda.obj I).PreservesEpimorphisms :=
        (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj I).mp hI
      let : (preadditiveYoneda.obj I).PreservesEpimorphisms := hP
      let : (preadditiveYoneda.obj I).PreservesHomology := by
        apply Functor.preservesHomology_of_preservesEpis_and_kernels
      change PreservesFiniteLimits (preadditiveYoneda.obj I) ∧
        PreservesFiniteColimits (preadditiveYoneda.obj I)
      exact ⟨inferInstance,
        Functor.preservesFiniteColimits_of_preservesHomology _⟩
    · refine ⟨?_, ?_⟩
      · intro A B f g h hS
        exact ⟨hS.splittingOfInjective⟩
      · intro B e
        refine Quotient.inductionOn e ?_
        intro E
        change extensionClass E = zeroExtClass
        apply Quotient.sound
        let s : E.toShortComplex.Splitting := E.shortExact.splittingOfInjective
        dsimp [Extension.toShortComplex] at s
        let i : E.middle ≅ I ⊞ B := s.isoBinaryBiproduct
        let f : ExtensionHom E (splitExtension I B) :=
          { middle := by simpa [splitExtension] using i.hom
            comm_left := by
              dsimp [splitExtension]
              apply biprod.hom_ext
              · dsimp [i, ShortComplex.Splitting.isoBinaryBiproduct]
                simp only [Category.assoc, biprod.lift_fst]
                simpa using s.f_r
              · dsimp [i, ShortComplex.Splitting.isoBinaryBiproduct]
                simp [E.zero]
            comm_right := by
              dsimp [splitExtension]
              simp [i, s] }
        let g : ExtensionHom (splitExtension I B) E :=
          { middle := by simpa [splitExtension] using i.inv
            comm_left := by
              dsimp [splitExtension]
              dsimp [i, ShortComplex.Splitting.isoBinaryBiproduct]
              simp
            comm_right := by
              dsimp [splitExtension]
              apply biprod.hom_ext'
              · dsimp [i, ShortComplex.Splitting.isoBinaryBiproduct]
                simp [E.zero]
              · dsimp [i, ShortComplex.Splitting.isoBinaryBiproduct]
                simpa using s.s_g }
        exact ⟨{ hom := f,
                  inv := g,
                  hom_inv_id := by
                    apply ExtensionHom.ext
                    change i.hom ≫ i.inv = 𝟙 E.middle
                    exact i.hom_inv_id,
                  inv_hom_id := by
                    apply ExtensionHom.ext
                    change i.inv ≫ i.hom = 𝟙 (I ⊞ B)
                    exact i.inv_hom_id }⟩
  · intro h
    rcases h with ⟨hExact, _, _⟩
    change PreservesFiniteLimits (preadditiveYoneda.obj I) ∧
      PreservesFiniteColimits (preadditiveYoneda.obj I) at hExact
    let : PreservesFiniteColimits (preadditiveYoneda.obj I) := hExact.2
    apply (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj I).mpr
    infer_instance

/- Mathlib already provides the product instance used by the source lemma:
   arbitrary products of injective objects are injective whenever the product
   exists. -/
theorem product_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    {Ω : Type w} (I : Ω → C) [HasProduct I]
    [∀ ω, Injective (I ω)] :
    Injective (∏ᶜ I) := by
  infer_instance

/- The source's definition of enough injectives is exactly Mathlib's
   `CategoryTheory.EnoughInjectives`, whose presentations are
   `CategoryTheory.InjectivePresentation`s. -/

/-! ## Functorial injective embeddings -/

/-- A functorial choice of a monomorphism from every object to an injective
object, represented as a functor to the arrow category. -/
def HasFunctorialInjectiveEmbeddings
    {C : Type u} [Category.{v} C] [Abelian C] : Prop :=
  ∃ (J : C ⥤ Arrow C),
    J ⋙ Arrow.leftFunc = 𝟭 C ∧
      (∀ A : C, Mono (J.obj A).hom) ∧
        (∀ A : C, Injective (J.obj A).right)

end Formalization.Books.Homology.Unit27
