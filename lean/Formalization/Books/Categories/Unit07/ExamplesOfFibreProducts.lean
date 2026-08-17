import Formalization.Books.Categories.Unit06.FibreProducts
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Categories, Chapter 7: Examples of fibre products

The category of sets is represented by `Type u`.  Its fibre product is made
explicit below as the subtype of pairs satisfying the equality in the base.
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

/-- The set-theoretic fibre product of two maps with common codomain. -/
def setFibreProduct {X Y Z : Type u} (f : X → Y) (g : Z → Y) : Type u :=
  {xz : X × Z // f xz.1 = g xz.2}

/-- The first projection from the set-theoretic fibre product. -/
def setFibreProduct.fst {X Y Z : Type u} (f : X → Y) (g : Z → Y) :
    setFibreProduct f g ⟶ X :=
  TypeCat.ofHom (fun xz => xz.1.1)

/-- The second projection from the set-theoretic fibre product. -/
def setFibreProduct.snd {X Y Z : Type u} (f : X → Y) (g : Z → Y) :
    setFibreProduct f g ⟶ Z :=
  TypeCat.ofHom (fun xz => xz.1.2)

/-- The map into the set-theoretic fibre product induced by compatible maps. -/
def setFibreProduct.lift {W X Y Z : Type u} (f : X → Y) (g : Z → Y)
    (α : W ⟶ X) (β : W ⟶ Z)
    (h : α ≫ TypeCat.ofHom f = β ≫ TypeCat.ofHom g) :
    W ⟶ setFibreProduct f g :=
  TypeCat.ofHom (fun w =>
    ⟨(α w, β w), ConcreteCategory.congr_hom h w⟩)

@[simp]
theorem setFibreProduct.fst_lift {W X Y Z : Type u} (f : X → Y) (g : Z → Y)
    (α : W ⟶ X) (β : W ⟶ Z)
    (h : α ≫ TypeCat.ofHom f = β ≫ TypeCat.ofHom g) :
    setFibreProduct.lift f g α β h ≫ setFibreProduct.fst f g = α := by
  apply ConcreteCategory.hom_ext
  intro w
  rfl

@[simp]
theorem setFibreProduct.snd_lift {W X Y Z : Type u} (f : X → Y) (g : Z → Y)
    (α : W ⟶ X) (β : W ⟶ Z)
    (h : α ≫ TypeCat.ofHom f = β ≫ TypeCat.ofHom g) :
    setFibreProduct.lift f g α β h ≫ setFibreProduct.snd f g = β := by
  apply ConcreteCategory.hom_ext
  intro w
  rfl

/-- The defining equality makes the square of projections commute. -/
theorem setFibreProduct.condition {X Y Z : Type u} (f : X → Y) (g : Z → Y) :
    setFibreProduct.fst f g ≫ TypeCat.ofHom f =
      setFibreProduct.snd f g ≫ TypeCat.ofHom g := by
  apply ConcreteCategory.hom_ext
  intro xz
  exact xz.2

/-- The explicit set-theoretic construction satisfies the pullback universal property. -/
theorem setFibreProduct.isPullback {X Y Z : Type u} (f : X → Y) (g : Z → Y) :
    @IsPullback (Type u) _ (setFibreProduct f g) X Z Y
      (setFibreProduct.fst f g) (setFibreProduct.snd f g)
      (TypeCat.ofHom f) (TypeCat.ofHom g) := by
  apply IsPullback.mk'
  · exact setFibreProduct.condition f g
  · intro W φ ψ hφ hψ
    apply ConcreteCategory.hom_ext
    intro w
    apply Subtype.ext
    apply Prod.ext
    · change (setFibreProduct.fst f g) (φ w) = (setFibreProduct.fst f g) (ψ w)
      exact ConcreteCategory.congr_hom hφ w
    · change (setFibreProduct.snd f g) (φ w) = (setFibreProduct.snd f g) (ψ w)
      exact ConcreteCategory.congr_hom hψ w
  · intro W α β h
    refine ⟨setFibreProduct.lift f g α β h, ?_, ?_⟩
    · exact setFibreProduct.fst_lift f g α β h
    · exact setFibreProduct.snd_lift f g α β h

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
    PreservesLimitsOfShape WalkingCospan (Action.forget (Type u) G) := by
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
