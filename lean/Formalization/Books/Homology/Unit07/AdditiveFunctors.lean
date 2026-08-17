import Formalization.Books.Homology.Unit06.Extensions
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homological Algebra, Chapter 7: Additive functors

The source uses the usual additive, exact, and adjoint functors.  The
declarations below use Mathlib's canonical comparison morphisms, preservation
classes, short-exact complexes, adjunctions, and the extension classes from
Chapter 6.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit06
open scoped ZeroObject

universe v u v' u'

namespace Formalization.Books.Homology.Unit07

/- `AdditiveCategory` in Chapter 3 records finite products, while the
   comparison morphisms below use Mathlib's binary-biproduct instance. -/
instance additiveCategory_hasBinaryBiproducts
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    HasBinaryBiproducts C :=
  hasBinaryBiproducts_of_finite_biproducts C

/-! ## Additive functors and biproducts -/

/- The two comparison morphisms are Mathlib's canonical versions of the
   maps in the source's items (2) and (3), respectively.  The displayed
   matrix and commutative diagram in the source proof are proof scaffolding
   for this comparison, so no parallel matrix API is introduced here. -/
theorem additive_iff_biprod_comparison_isIso
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    [AdditiveCategory C] [AdditiveCategory D] (F : C ⥤ D) :
    (F.Additive ↔ ∀ X Y : C, IsIso (F.biprodComparison' X Y)) ∧
      ((∀ X Y : C, IsIso (F.biprodComparison' X Y)) ↔
        ∀ X Y : C, IsIso (F.biprodComparison X Y)) := by
  sorry

/-! ## Exact functors and short exact sequences -/

/- The source writes exact sequences with zero objects at one or both ends.
   `ComposableArrows` records those endpoint maps explicitly and lets the
   exactness predicate express exactness at all internal objects without
   assuming in advance that `F` preserves zero morphisms. -/

def leftExactImageSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) (S : ShortComplex C) : ComposableArrows D 3 :=
  ComposableArrows.mk₃
    (0 : (0 : D) ⟶ F.obj S.X₁)
    (F.map S.f)
    (F.map S.g)

def rightExactImageSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) (S : ShortComplex C) : ComposableArrows D 3 :=
  ComposableArrows.mk₃
    (F.map S.f)
    (F.map S.g)
    (0 : F.obj S.X₃ ⟶ (0 : D))

def exactImageSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) (S : ShortComplex C) : ComposableArrows D 4 :=
  ComposableArrows.mk₄
    (0 : (0 : D) ⟶ F.obj S.X₁)
    (F.map S.f)
    (F.map S.g)
    (0 : F.obj S.X₃ ⟶ (0 : D))

def mapsShortExactOnLeft
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → (leftExactImageSequence F S).Exact

def mapsShortExactOnRight
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → (rightExactImageSequence F S).Exact

def mapsShortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → (exactImageSequence F S).Exact

theorem left_or_right_exact_additive
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) :
    (IsLeftExact F ∨ IsRightExact F) → F.Additive := by
  sorry

theorem left_exact_iff_maps_short_exact_on_left
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) :
    IsLeftExact F ↔ mapsShortExactOnLeft F := by
  sorry

theorem right_exact_iff_maps_short_exact_on_right
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) :
    IsRightExact F ↔ mapsShortExactOnRight F := by
  sorry

theorem exact_iff_maps_short_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) :
    IsExact F ↔ mapsShortExact F := by
  sorry

/-! ## Exact functors and extension classes -/

/- Applying an exact functor to the middle term and both structure maps gives
   the extension denoted `F(E)` in the source. -/
noncomputable def mapExtensionOfExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F) (E : Extension C A B) :
    Extension D (F.obj A) (F.obj B) := by
  letI : PreservesFiniteLimits F := hF.1
  letI : PreservesFiniteColimits F := hF.2
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF.1)
  exact
    { middle := F.obj E.middle
      inclusion := F.map E.inclusion
      projection := F.map E.projection
      zero := by
        rw [← F.map_comp, E.zero, F.map_zero]
      shortExact := by
        simpa [Extension.toShortComplex, ShortComplex.map] using
          E.shortExact.map_of_exact F }

theorem mapExtensionOfExact_preserves_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F)
    {E E' : Extension C A B} (h : Nonempty (E ≅ E')) :
    Nonempty (mapExtensionOfExact F hF E ≅ mapExtensionOfExact F hF E') := by
  sorry

noncomputable def mapExtensionClassOfExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F) :
    Ext B A → Ext (F.obj B) (F.obj A) :=
  Quotient.map (mapExtensionOfExact F hF) (by
    intro E E' h
    exact mapExtensionOfExact_preserves_iso F hF h)

theorem mapExtensionClassOfExact_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F) :
    mapExtensionClassOfExact F hF (0 : Ext B A) = 0 := by
  sorry

theorem mapExtensionClassOfExact_add
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F)
    (x y : Ext B A) :
    mapExtensionClassOfExact F hF (x + y) =
      mapExtensionClassOfExact F hF x + mapExtensionClassOfExact F hF y := by
  sorry

/-- The abelian-group homomorphism on extension classes induced by an exact functor. -/
noncomputable def exactFunctorExtMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F) :
    Ext B A →+ Ext (F.obj B) (F.obj A) where
  toFun := mapExtensionClassOfExact F hF
  map_zero' := mapExtensionClassOfExact_zero F hF
  map_add' := mapExtensionClassOfExact_add F hF

theorem exactFunctorExtMap_extensionClass
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F) (E : Extension C A B) :
    exactFunctorExtMap F hF (extensionClass E) =
      extensionClass (mapExtensionOfExact F hF E) := by
  rfl

/-! ## The adjoint criterion for abelian categories -/

/- The source's displayed kernel/cokernel identities and the subsequent
   coimage--image calculation are the proof route to this criterion.  Their
   objects are represented here by the canonical kernel, cokernel, coimage,
   and image interfaces already used by the abelian-category chapters. -/
theorem abelian_of_exact_retract_right_adjoint
    {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B]
    [AdditiveCategory A] [Abelian B]
    (hAddB : Nonempty (AdditiveCategory B))
    {a : A ⥤ B} {b : B ⥤ A}
    [a.Additive] [b.Additive]
    (hAdj : Nonempty (b ⊣ a))
    (hLeft : IsLeftExact b)
    (hba : Nonempty (a ⋙ b ≅ 𝟭 A)) :
    Nonempty (Abelian A) := by
  sorry

end Formalization.Books.Homology.Unit07
