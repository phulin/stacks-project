import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homological Algebra, Chapter 12: Cohomological delta-functors

The source packages a family of additive functors together with connecting
morphisms for short exact sequences.  The exactness of the resulting long
sequence is recorded by `LongExactness`; Mathlib's `ShortComplex.Exact` is
used at each three-term portion of that sequence.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit23
open scoped ZeroObject

universe v u v' u'

namespace Formalization.Books.Homology.Unit12

/-! ## Exact portions of a long sequence -/

/-- A composable pair of morphisms together with its exactness. -/
structure ExactPair
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop where
  zero : f ≫ g = 0
  exact : (ShortComplex.mk f g zero).Exact

/-- The four kinds of exact portions in the long sequence attached to a
short exact sequence.  The `at_left` field starts in degree one, since the
degree-zero left endpoint is the explicit zero object in `at_zero`. -/
structure LongExactness
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : ℕ → A ⥤ B)
    (delta : ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
      (F n).obj S.X₃ ⟶ (F (n + 1)).obj S.X₁)
    (S : ShortComplex A) (hS : S.ShortExact) : Prop where
  at_zero :
    ExactPair
      (0 : (0 : B) ⟶ (F 0).obj S.X₁)
      ((F 0).map S.f)
  at_left : ∀ n : ℕ,
    ExactPair
      (delta S hS n)
      ((F (n + 1)).map S.f)
  at_middle : ∀ n : ℕ,
    ExactPair
      ((F n).map S.f)
      ((F n).map S.g)
  at_right : ∀ n : ℕ,
    ExactPair
      ((F n).map S.g)
      (delta S hS n)

/-! ## Cohomological delta-functors -/

/-- A cohomological delta-functor from one abelian category to another. -/
structure CohomologicalDeltaFunctor
    (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type u') [Category.{v'} B] [Abelian B] where
  /-- The additive functor in each nonnegative degree. -/
  functor : ℕ → A ⥤ B
  /-- Additivity of every member of the family. -/
  additive : ∀ n : ℕ, (functor n).Additive
  /-- The connecting morphism for every short exact sequence and degree. -/
  delta : ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
    (functor n).obj S.X₃ ⟶ (functor (n + 1)).obj S.X₁
  /-- Exactness of the long sequence associated to every short exact sequence. -/
  exact : ∀ (S : ShortComplex A) (hS : S.ShortExact),
    LongExactness functor delta S hS
  /-- Naturality of the connecting morphisms in morphisms of short exact sequences. -/
  natural : ∀ {S₁ S₂ : ShortComplex A}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ),
    delta S₁ h₁ n ≫ (functor (n + 1)).map φ.τ₁ =
      (functor n).map φ.τ₃ ≫ delta S₂ h₂ n

/-- The observation in the source that the degree-zero functor is left exact. -/
theorem CohomologicalDeltaFunctor.isLeftExact_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B) :
    IsLeftExact (F.functor 0) := by
  sorry

/-! ## Morphisms and universal delta-functors -/

/-- A morphism of cohomological delta-functors. -/
structure DeltaFunctorMorphism
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F G : CohomologicalDeltaFunctor A B) where
  /-- The natural transformation in each degree. -/
  app : ∀ n : ℕ, F.functor n ⟶ G.functor n
  /-- Compatibility with the connecting morphisms. -/
  comm : ∀ (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ),
    F.delta S hS n ≫ (app (n + 1)).app S.X₁ =
      (app n).app S.X₃ ≫ G.delta S hS n

namespace CohomologicalDeltaFunctor

/-- The universal property of a cohomological delta-functor. -/
def IsUniversal
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B) : Prop :=
  ∀ (G : CohomologicalDeltaFunctor A B)
    (t : F.functor 0 ⟶ G.functor 0),
    ∃! φ : DeltaFunctorMorphism F G, φ.app 0 = t

/-- Effaceability in every positive degree. -/
def IsEffaceable
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (X : A),
    ∃ (Y : A) (u : X ⟶ Y),
      Mono u ∧ (F.functor n).map u = 0

end CohomologicalDeltaFunctor

/-- An effaceable cohomological delta-functor is universal. -/
theorem effaceable_isUniversal
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B)
    (hF : F.IsEffaceable) :
    F.IsUniversal := by
  sorry

/-! ## Isomorphisms and uniqueness -/

/-- An isomorphism of cohomological delta-functors, degree by degree. -/
structure DeltaFunctorIso
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F G : CohomologicalDeltaFunctor A B) where
  hom : DeltaFunctorMorphism F G
  inv : DeltaFunctorMorphism G F
  hom_inv_id : ∀ n : ℕ, hom.app n ≫ inv.app n = 𝟙 _
  inv_hom_id : ∀ n : ℕ, inv.app n ≫ hom.app n = 𝟙 _

/-- Universal delta-functors are uniquely isomorphic once the degree-zero
natural isomorphism is fixed.  Taking the identity when the degree-zero
functors are equal gives the source's uniqueness statement. -/
theorem universal_deltaFunctor_unique_iso
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F G : CohomologicalDeltaFunctor A B)
    (hF : F.IsUniversal) (hG : G.IsUniversal)
    (e₀ : F.functor 0 ≅ G.functor 0) :
    ∃! e : DeltaFunctorIso F G, e.hom.app 0 = e₀.hom := by
  sorry

end Formalization.Books.Homology.Unit12
