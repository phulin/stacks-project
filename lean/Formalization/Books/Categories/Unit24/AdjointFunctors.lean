import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint

/-!
# Categories, Chapter 24: Adjoint functors

The source's adjunction is Mathlib's `Adjunction`: its hom-set equivalences,
unit, counit, and triangle identities are the canonical interface.  The
declarations below record the chapter-facing criteria and consequences while
reusing Mathlib's preservation and mate APIs.
-/

namespace Formalization.Books.Categories.Unit24

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open Opposite

universe u v u' v' w w'

noncomputable section

/-! ## Definition of adjunction -/

/- The source asks for functorial hom-set bijections.  Mathlib packages this
   data canonically as `Adjunction`; the proposition below records the
   existence of such an adjunction for a fixed pair of functors. -/
def IsLeftAdjoint {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D) (v : D ⥤ C) : Prop :=
  Nonempty (u ⊣ v)

/- The source's dual terminology is the same adjunction relation with the
   functors displayed in the opposite order. -/
def IsRightAdjoint {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (v : D ⥤ C) (u : C ⥤ D) : Prop :=
  IsLeftAdjoint u v

theorem is_left_adjoint_iff_is_right_adjoint
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} :
    IsLeftAdjoint u v ↔ IsRightAdjoint v u :=
  Iff.rfl

/- For `h : u ⊣ v`, `h.homEquiv` is the source's functorial family of
   bijections, while `h.unit` and `h.counit` are its adjunction maps.  The
   identity-correspondence assertions are already exactly
   `Adjunction.homEquiv_id` and `Adjunction.homEquiv_symm_id`; naturality in
   both variables is provided by `Adjunction.homEquiv_naturality_left` and
   `Adjunction.homEquiv_naturality_right`. -/

/- The three equivalent descriptions of a corresponding pair of morphisms. -/
theorem hom_equiv_iff_unit_formula
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    {X : C} {Y : D} (α : u.obj X ⟶ Y) (β : X ⟶ v.obj Y) :
    h.homEquiv X Y α = β ↔
      β = h.unit.app X ≫ v.map α := by
  sorry

theorem hom_equiv_iff_counit_formula
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    {X : C} {Y : D} (α : u.obj X ⟶ Y) (β : X ⟶ v.obj Y) :
    h.homEquiv X Y α = β ↔
      α = u.map β ≫ h.counit.app Y := by
  sorry

theorem unit_formula_iff_counit_formula
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    {X : C} {Y : D} (α : u.obj X ⟶ Y) (β : X ⟶ v.obj Y) :
    (β = h.unit.app X ≫ v.map α) ↔
      (α = u.map β ≫ h.counit.app Y) := by
  sorry

/-! ## Existence from representability -/

/- The presheaf `u.op ⋙ yoneda.obj Y` has value
   `Hom_D(u(X), Y)` at `op X`. -/
theorem right_adjoint_of_representable_hom
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    (u : C ⥤ D)
    (h : ∀ Y : D, Functor.IsRepresentable (u.op ⋙ yoneda.obj Y)) :
    ∃ v : D ⥤ C, Nonempty (u ⊣ v) := by
  sorry

/-! ## Fully faithful adjoints -/

theorem fully_faithful_left_of_comp
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    (hcomp : Nonempty (u ⋙ v).FullyFaithful) :
    Nonempty u.FullyFaithful := by
  sorry

theorem fully_faithful_right_of_comp
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    (hcomp : Nonempty (v ⋙ u).FullyFaithful) :
    Nonempty v.FullyFaithful := by
  sorry

/- Each source chain is recorded by adjacent equivalences.  `u ⋙ v` is the
   Lean composition corresponding to `v ∘ u`, and `v ⋙ u` to `u ∘ v`. -/
theorem adjoint_fully_faithful_criteria
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v) :
    ((Nonempty u.FullyFaithful ↔ Nonempty (𝟭 C ≅ u ⋙ v)) ∧
      (Nonempty (𝟭 C ≅ u ⋙ v) ↔ IsIso h.unit)) ∧
    ((Nonempty v.FullyFaithful ↔ Nonempty (v ⋙ u ≅ 𝟭 D)) ∧
      (Nonempty (v ⋙ u ≅ 𝟭 D) ↔ IsIso h.counit)) := by
  sorry

/-! ## Preservation of limits and colimits -/

/- The source's displayed equalities are represented by the stronger
   statement that the mapped chosen cone or cocone is universal. -/
theorem left_adjoint_preserves_colimit
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    {I : Type w} [Category.{w'} I] (M : I ⥤ C) [HasColimit M] :
    Nonempty (IsColimit (u.mapCocone (colimit.cocone M))) := by
  sorry

theorem right_adjoint_preserves_limit
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    {I : Type w} [Category.{w'} I] (M : I ⥤ D) [HasLimit M] :
    Nonempty (IsLimit (v.mapCone (limit.cone M))) := by
  sorry

theorem left_adjoint_is_right_exact
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    [HasFiniteColimits C] :
    Formalization.Books.Categories.Unit23.IsRightExact u := by
  sorry

theorem right_adjoint_is_left_exact
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    [HasFiniteLimits D] :
    Formalization.Books.Categories.Unit23.IsLeftExact v := by
  sorry

/-! ## Unit-counit (triangle) identities -/

theorem unit_counit_left_triangle
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v) (X : C) :
    u.map (h.unit.app X) ≫ h.counit.app (u.obj X) = 𝟙 (u.obj X) :=
  h.left_triangle_components X

theorem unit_counit_right_triangle
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v) (Y : D) :
    h.unit.app (v.obj Y) ≫ v.map (h.counit.app Y) = 𝟙 (v.obj Y) :=
  h.right_triangle_components Y

/-! ## Transformations between adjoint functors -/

/- Mathlib's `conjugateEquiv` is the mate correspondence in precisely the
   special case used by the source. -/
def mateOfLeftTransformation
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u₁ u₂ : C ⥤ D} {v₁ v₂ : D ⥤ C}
    (h₁ : u₁ ⊣ v₁) (h₂ : u₂ ⊣ v₂) (β : u₂ ⟶ u₁) : v₁ ⟶ v₂ :=
  conjugateEquiv h₁ h₂ β

theorem mate_counit_square
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    {u₁ u₂ : C ⥤ D} {v₁ v₂ : D ⥤ C}
    (h₁ : u₁ ⊣ v₁) (h₂ : u₂ ⊣ v₂) (β : u₂ ⟶ u₁) :
    Functor.whiskerLeft v₁ β ≫ h₁.counit =
      Functor.whiskerRight (mateOfLeftTransformation h₁ h₂ β) u₂ ≫ h₂.counit := by
  sorry

/-! ## Composition of adjunctions -/

def composedAdjunction
    {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B]
    {C : Type w} [Category.{w'} C]
    {v : A ⥤ B} {v' : B ⥤ C} {u : B ⥤ A} {u' : C ⥤ B}
    (h : u ⊣ v) (h' : u' ⊣ v') :
    (u' ⋙ u) ⊣ (v ⋙ v') :=
  h'.comp h

theorem composed_counit_formula
    {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B]
    {C : Type w} [Category.{w'} C]
    {v : A ⥤ B} {v' : B ⥤ C} {u : B ⥤ A} {u' : C ⥤ B}
    (h : u ⊣ v) (h' : u' ⊣ v') (X : A) :
    (composedAdjunction h h').counit.app X =
      u.map (h'.counit.app (v.obj X)) ≫ h.counit.app X := by
  sorry

end

end Formalization.Books.Categories.Unit24
