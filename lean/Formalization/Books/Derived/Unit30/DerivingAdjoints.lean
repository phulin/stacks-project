import Formalization.Books.Derived.Unit14.DerivedFunctors
import Formalization.Books.Derived.Unit15.ClassicalDerivedFunctors
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# Derived Categories, Chapter 30: deriving adjoints

The source's partially defined `RF` and `LG` are represented using the
canonical essentially-constant derived-value functors from Chapter 14.  The
hom-set isomorphism is an `Equiv`, with its two naturality equations recorded
explicitly; this is the source's assertion that the isomorphism is functorial
in both variables.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit27
open Formalization.Books.Derived.Unit05
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit14
open Formalization.Books.Derived.Unit15
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w w'

namespace Formalization.Books.Derived.Unit30

/-! ## The two partially defined derived functors -/

/-- The partial right derived functor associated to `F ⋙ Q'`. -/
noncomputable def partialRightDerivedFunctor
    {D D' E' : Type*} [Category* D] [Category* D'] [Category* E']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (F : D ⥤ D') (Q' : D' ⥤ E') :
    rightDerivedSubcategory S hS (F ⋙ Q') ⥤ E' :=
  rightDerivedFunctor S hS (F ⋙ Q')

/-- The partial left derived functor associated to `G ⋙ Q`. -/
noncomputable def partialLeftDerivedFunctor
    {D D' E : Type*} [Category* D] [Category* D'] [Category* E]
    (S' : MorphismProperty D') (hS' : SaturatedMultiplicativeSystem S')
    (G : D' ⥤ D) (Q : D ⥤ E) :
    leftDerivedSubcategory S' hS' (G ⋙ Q) ⥤ E :=
  leftDerivedFunctor S' hS' (G ⋙ Q)

/-! ## The functorial partial Hom-equivalence -/

/-- The source's canonical Hom-equivalence for two partially defined derived
functors.  The two naturality fields below are the precise form of
functoriality in `K` and `M`.

The argument `adj` records that the original functors are adjoint; the
localized functors and the derived values in the fields are the canonical
ones supplied by Chapters 5 and 14.
-/
structure PartialDerivedAdjunction
    {D D' E E' : Type*} [Category* D] [Category* D'] [Category* E] [Category* E']
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (S' : MorphismProperty D') (hS' : SaturatedMultiplicativeSystem S')
    (Q : D ⥤ E) (Q' : D' ⥤ E')
    (F : D ⥤ D') (G : D' ⥤ D) (adj : G ⊣ F) where
  /-- The bijection `Hom(Q'M, RF(K)) ≃ Hom(LG(M), QK)`. -/
  homEquiv :
    ∀ (K : rightDerivedSubcategory S hS (F ⋙ Q'))
      (M : leftDerivedSubcategory S' hS' (G ⋙ Q)),
      (Q'.obj M.obj ⟶
          (partialRightDerivedFunctor S hS F Q').obj K) ≃
        ((partialLeftDerivedFunctor S' hS' G Q).obj M ⟶ Q.obj K.obj)
  /-- Naturality in the source variable `K`. -/
  homEquiv_naturality_source :
    ∀ {K K' : rightDerivedSubcategory S hS (F ⋙ Q')}
      (f : K ⟶ K')
      (M : leftDerivedSubcategory S' hS' (G ⋙ Q))
      (φ : Q'.obj M.obj ⟶ (partialRightDerivedFunctor S hS F Q').obj K),
      homEquiv K' M
          (φ ≫ (partialRightDerivedFunctor S hS F Q').map f) =
        homEquiv K M φ ≫ Q.map f.hom
  /-- Naturality in the target variable `M`. -/
  homEquiv_naturality_target :
    ∀ (K : rightDerivedSubcategory S hS (F ⋙ Q'))
      {M M' : leftDerivedSubcategory S' hS' (G ⋙ Q)}
      (g : M ⟶ M')
      (φ : Q'.obj M'.obj ⟶ (partialRightDerivedFunctor S hS F Q').obj K),
      homEquiv K M (Q'.map g.hom ≫ φ) =
        (partialLeftDerivedFunctor S' hS' G Q).map g ≫ homEquiv K M' φ

/-! ## The general triangulated statement -/

section Triangulated

variable {D D' : Type*} [Category* D] [Category* D']
  [Preadditive D] [Preadditive D'] [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']

/-- The pre-derived adjunction Hom-equivalence from the source's first lemma.

`S.Q` and `S'.Q` are Mathlib's canonical localization functors.  The
compatibility assumptions are retained as typeclasses, while the established
Chapter 14 API uses the stronger saturated multiplicative-system witnesses
`hS` and `hS'` to define the partial derived values.
-/
theorem preDerivedAdjunction
    (S : MorphismProperty D) (hS : SaturatedMultiplicativeSystem S)
    (S' : MorphismProperty D') (hS' : SaturatedMultiplicativeSystem S')
    [CompatibleWithTriangulation S] [CompatibleWithTriangulation S']
    (F : D ⥤ D') (G : D' ⥤ D) (adj : G ⊣ F)
    [F.CommShift ℤ] [F.IsTriangulated]
    [G.CommShift ℤ] [G.IsTriangulated] :
    Nonempty
      (PartialDerivedAdjunction S hS S' hS' S.Q S'.Q F G adj) := by
  sorry

end Triangulated

/-! ## The abelian-complex specialization -/

section AdditiveHomotopy

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]

/- The additive adjunction on abelian categories induces the adjunction on
   unbounded homotopy categories used by the specialization below.  Mathlib
   provides the homotopy functors but not this bundled adjunction interface. -/

/-- An additive adjunction induces an adjunction on unbounded homotopy
categories. -/
theorem additiveHomotopyAdjunction_exists
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    (adj : G ⊣ F) :
    Nonempty (additiveHomotopyFunctor G ⊣ additiveHomotopyFunctor F) := by
  sorry

/- The source uses an adjunction as data; this chosen version makes the
   preceding existence interface directly usable in the specialization. -/
noncomputable def additiveHomotopyAdjunction
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    (adj : G ⊣ F) :
    additiveHomotopyFunctor G ⊣ additiveHomotopyFunctor F :=
  Classical.choice (additiveHomotopyAdjunction_exists F G adj)

end AdditiveHomotopy

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]

/-- The source's abelian-category lemma, with `K(𝒜)` and `K(ℬ)` localized to
the canonical unbounded derived categories. -/
theorem preDerivedAdjunction_abelian
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    (adj : G ⊣ F) :
    Nonempty
      (PartialDerivedAdjunction
        (S := quasiIsoHomotopyProperty A)
        (hS := (quasiIsoHomotopyProperty_properties A).1)
        (S' := quasiIsoHomotopyProperty B)
        (hS' := (quasiIsoHomotopyProperty_properties B).1)
        (Q := DerivedCategory.Qh (C := A))
        (Q' := DerivedCategory.Qh (C := B))
        (F := additiveHomotopyFunctor F)
        (G := additiveHomotopyFunctor G)
        (adj := additiveHomotopyAdjunction F G adj)) := by
  sorry

end Abelian

/-! ## Everywhere-defined derived functors -/

section EverywhereDefined

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]

/-- `RF` is a right derived functor on the unbounded derived category when it
carries the canonical localization comparison map and satisfies Mathlib's
right-derived universal property. -/
def IsUnboundedRightDerivedFunctor
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B) : Prop :=
  ∃ α : classicalHomotopyToDerived F ⟶
      (DerivedCategory.Qh (C := A)) ⋙ RF,
    Functor.IsRightDerivedFunctor RF α (quasiIsoHomotopyProperty A)

/-- `LG` is a left derived functor on the unbounded derived category when it
carries the canonical localization comparison map and satisfies Mathlib's
left-derived universal property. -/
def IsUnboundedLeftDerivedFunctor
    (G : B ⥤ A) [G.Additive]
    (LG : DerivedCategory B ⥤ DerivedCategory A) : Prop :=
  ∃ β : (DerivedCategory.Qh (C := B)) ⋙ LG ⟶ classicalHomotopyToDerived G,
    Functor.IsLeftDerivedFunctor LG β (quasiIsoHomotopyProperty B)

/-- The source's final lemma: everywhere-defined derived functors preserve the
original adjunction, so `LG` is left adjoint to `RF`. -/
theorem derivedAdjunction
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    (adj : G ⊣ F)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (LG : DerivedCategory B ⥤ DerivedCategory A)
    (hRF : IsUnboundedRightDerivedFunctor F RF)
    (hLG : IsUnboundedLeftDerivedFunctor G LG) :
    Nonempty (LG ⊣ RF) := by
  sorry

end EverywhereDefined

end Formalization.Books.Derived.Unit30
