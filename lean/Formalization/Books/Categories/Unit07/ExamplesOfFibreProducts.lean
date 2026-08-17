import Formalization.Books.Categories.Unit06.FibreProducts
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Categories, Chapter 7: Examples of fibre products

The category of sets is represented by `Type u`.  Its fibre product is made
explicit by Mathlib's `Types.PullbackObj`, the subtype of pairs satisfying the
equality in the base.
For the structured categories listed in the source, Mathlib's concrete
category limit instances already construct the corresponding structured
fibre products, so the declarations below record their existence without
introducing parallel category-theoretic definitions.
-/

namespace Formalization.Books.Categories.Unit07

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit06

universe u

/-! ## Fibre products of sets -/

/-- The projections in the source's set-theoretic construction are the legs of
Mathlib's explicit `Types.PullbackObj` cone. -/
theorem types_pullback_condition {X Y Z : Type u} (f : X → Y) (g : Z → Y) :
    (Types.pullbackCone (TypeCat.ofHom f) (TypeCat.ofHom g)).fst ≫ TypeCat.ofHom f =
      (Types.pullbackCone (TypeCat.ofHom f) (TypeCat.ofHom g)).snd ≫ TypeCat.ofHom g := by
  exact (Types.pullbackCone (TypeCat.ofHom f) (TypeCat.ofHom g)).condition

/-- The explicit set-theoretic construction satisfies the pullback universal
property. -/
theorem types_pullback_isPullback {X Y Z : Type u} (f : X → Y) (g : Z → Y) :
    @IsPullback (Type u) _ (Types.PullbackObj (TypeCat.ofHom f) (TypeCat.ofHom g)) X Z Y
      (Types.pullbackCone (TypeCat.ofHom f) (TypeCat.ofHom g)).fst
      (Types.pullbackCone (TypeCat.ofHom f) (TypeCat.ofHom g)).snd
      (TypeCat.ofHom f) (TypeCat.ofHom g) := by
  exact IsPullback.of_isLimit
    (Types.pullbackLimitCone (TypeCat.ofHom f) (TypeCat.ofHom g)).isLimit

/-- Compatible maps into the two factors give the explicit map into the
set-theoretic fibre product. -/
theorem types_pullback_map_exists {W X Y Z : Type u} (f : X → Y) (g : Z → Y)
    (α : W ⟶ X) (β : W ⟶ Z)
    (h : α ≫ TypeCat.ofHom f = β ≫ TypeCat.ofHom g) :
    ∃ γ : W ⟶ Types.PullbackObj (TypeCat.ofHom f) (TypeCat.ofHom g), ∀ w,
      (γ w : X × Z) = (α w, β w) := by
  refine ⟨TypeCat.ofHom (fun w => ⟨(α w, β w), ConcreteCategory.congr_hom h w⟩), ?_⟩
  intro w
  rfl

/-- The explicit set-theoretic construction has the source's universal
property for compatible maps. -/
theorem types_pullback_universal_property {W X Y Z : Type u} (f : X → Y) (g : Z → Y)
    (α : W ⟶ X) (β : W ⟶ Z)
    (h : α ≫ TypeCat.ofHom f = β ≫ TypeCat.ofHom g) :
    ∃! γ : W ⟶ Types.PullbackObj (TypeCat.ofHom f) (TypeCat.ofHom g),
      γ ≫ (Types.pullbackCone (TypeCat.ofHom f) (TypeCat.ofHom g)).fst = α ∧
        γ ≫ (Types.pullbackCone (TypeCat.ofHom f) (TypeCat.ofHom g)).snd = β := by
  exact fibre_product_universal_property (types_pullback_isPullback f g) α β h

/-- The category of sets has all fibre products. -/
theorem types_have_fibre_products : HasPullbacks (Type u) := by
  infer_instance

/-- Every morphism in the category of sets is representable. -/
theorem type_morphism_is_representable {X Y : Type u} (f : X ⟶ Y) :
    HasPullbacksAlong f := by
  intro W g
  infer_instance

/-! ## Structured examples -/

/-- The subgroup underlying the group-theoretic fibre product. -/
def groupFibreProductSubgroup {X Y Z : Type u} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Z →* Y) : Subgroup (X × Z) where
  carrier := {xz | f xz.1 = g xz.2}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change f (a.1 * b.1) = g (a.2 * b.2)
    rw [map_mul, map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change f a.1⁻¹ = g a.2⁻¹
    rw [map_inv, map_inv, ha]

@[simp]
theorem groupFibreProductSubgroup.mem_iff {X Y Z : Type u} [Group X] [Group Y]
    [Group Z] (f : X →* Y) (g : Z →* Y) (xz : X × Z) :
    xz ∈ groupFibreProductSubgroup f g ↔ f xz.1 = g xz.2 := by
  rfl

/-- Multiplication on the group fibre product is coordinatewise. -/
theorem groupFibreProduct_mul_formula {X Y Z : Type u} [Group X] [Group Y]
    [Group Z] (f : X →* Y) (g : Z →* Y)
    (a b : groupFibreProductSubgroup f g) :
    ((a * b : groupFibreProductSubgroup f g) : X × Z) =
      ((a : X × Z).1 * (b : X × Z).1, (a : X × Z).2 * (b : X × Z).2) := by
  rfl

/-
The following declarations use the existing concrete-category limit
constructions.  They account for the source's list of categories in which
the underlying-set fibre-product construction carries the relevant
structure and satisfies the categorical universal property.
-/

/-- The category of groups has fibre products. -/
theorem groups_have_fibre_products : HasPullbacks (GrpCat.{u}) := by
  infer_instance

/-- The underlying type functor preserves the fibre products of groups. -/
theorem groups_underlying_fibre_products :
    PreservesLimitsOfShape WalkingCospan (forget GrpCat.{u}) := by
  infer_instance

/-- For a fixed group `G`, the category of left `G`-sets has fibre products. -/
abbrev GSetCategory (G : Type u) [Group G] := Action (Type u) G

theorem g_sets_have_fibre_products (G : Type u) [Group G] :
    HasPullbacks (GSetCategory G) := by
  infer_instance

/-- The underlying type functor preserves the fibre products of `G`-sets. -/
theorem g_sets_underlying_fibre_products (G : Type u) [Group G] :
    PreservesLimitsOfShape WalkingCospan (forget (GSetCategory G)) := by
  change PreservesLimitsOfShape WalkingCospan (Action.forget (Type u) G)
  infer_instance

/-- The category of (not necessarily commutative) rings has fibre products. -/
theorem rings_have_fibre_products : HasPullbacks (RingCat.{u}) := by
  infer_instance

/-- The underlying type functor preserves the fibre products of rings. -/
theorem rings_underlying_fibre_products :
    PreservesLimitsOfShape WalkingCospan (forget RingCat.{u}) := by
  infer_instance

/-- The category of modules over a fixed ring has fibre products. -/
theorem modules_have_fibre_products (R : Type u) [Ring R] :
    HasPullbacks (ModuleCat.{u} R) := by
  infer_instance

/-- The underlying type functor preserves the fibre products of modules. -/
theorem modules_underlying_fibre_products (R : Type u) [Ring R] :
    PreservesLimitsOfShape WalkingCospan (forget (ModuleCat.{u} R)) := by
  infer_instance

end Formalization.Books.Categories.Unit07
