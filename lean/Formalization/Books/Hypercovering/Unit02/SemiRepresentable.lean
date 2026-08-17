import Formalization.Books.Categories.Unit03.Opposite
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Hypercoverings, Chapter 2: Semi-representable objects

The source section is formalized with Mathlib's `FormalCoproduct` category.  Its
objects are indexed families of objects of a category and its morphisms are
exactly a function on indices together with one morphism in the original
category over each index.  The source's unbounded ``big'' category is recorded
by the universe-polymorphic abbreviation `SemiRepresentable`; the concrete
functors in this file use the hom-set universe of the base category.
-/

namespace Formalization.Books.Hypercovering.Unit02

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit03
open Opposite

universe w v u

noncomputable section

/-! ## Definition of semi-representable objects -/

/-- The category of semi-representable objects with `w`-small index families.

This is Mathlib's canonical `FormalCoproduct` category; in particular, its
`Hom` structure is the source's pair consisting of an index map and component
morphisms. -/
abbrev SemiRepresentable (C : Type u) [Category.{v} C] :=
  FormalCoproduct.{w} C

/-- The semi-representable objects over `X`, namely semi-representable objects
in the slice category `C/X`. -/
abbrev SemiRepresentableOver (C : Type u) [Category.{v} C] (X : C) :=
  SemiRepresentable.{v} (Over X)

/-- The presheaf category over the representable presheaf `h_X`. -/
abbrev PresheafOver (C : Type u) [Category.{v} C] (X : C) :=
  Over (representablePresheaf X)

/-! ## The forgetful functor on objects over `X` -/

/-- Forget the maps to `X` from a semi-representable object over `X`. -/
def semiRepresentableOverForget {C : Type u} [Category.{v} C] (X : C) :
    SemiRepresentableOver C X ⥤ SemiRepresentable.{v} C where
  obj K :=
    { I := K.I
      obj := fun i => (K.obj i).left }
  map {K L} f :=
    { f := f.f
      φ := fun i => (f.φ i).left }
  map_id K := by
    exact FormalCoproduct.hom_ext rfl (fun i => by simp)
  map_comp f g := by
    exact FormalCoproduct.hom_ext rfl (fun i => by simp)

/-! ## The functor to presheaves -/

/-- The functor associating to a semi-representable object the coproduct of
the corresponding representable presheaves. -/
abbrev semiRepresentablePresheafFunctor {C : Type u} [Category.{v} C] :
    SemiRepresentable.{v} C ⥤ Presheaf C :=
  FormalCoproduct.yoneda

/- The displayed formula in the source is definitional for the canonical
`FormalCoproduct.yoneda` construction. -/
@[simp]
theorem semiRepresentablePresheafFunctor_obj
    {C : Type u} [Category.{v} C] (K : SemiRepresentable.{v} C) :
    (semiRepresentablePresheafFunctor (C := C)).obj K =
      ∐ fun i : K.I => representablePresheaf (K.obj i) :=
  rfl

/-! ## The functor over `h_X` -/

/-- The map of representable presheaves induced by an object of `C/X`. -/
def representablePresheafMapOfOver {C : Type u} [Category.{v} C]
    {X : C} (U : Over X) :
    representablePresheaf U.left ⟶ representablePresheaf X :=
  (functorOfPoints (C := C)).map U.hom

/-- The underlying presheaf of a semi-representable object over `X`. -/
abbrev semiRepresentableOverUnderlying {C : Type u} [Category.{v} C]
    (X : C) :
    SemiRepresentableOver C X ⥤ Presheaf C :=
  semiRepresentableOverForget X ⋙ semiRepresentablePresheafFunctor

/-- The canonical map from the underlying presheaf of a family over `X` to
`h_X`, assembled from the maps of its representable summands. -/
def semiRepresentableOverStructureMap {C : Type u} [Category.{v} C]
    (X : C) (K : SemiRepresentableOver C X) :
    (semiRepresentableOverUnderlying X).obj K ⟶ representablePresheaf X :=
  Sigma.desc fun i => representablePresheafMapOfOver (K.obj i)

@[simp]
theorem semiRepresentableOverStructureMap_ι
    {C : Type u} [Category.{v} C] {X : C}
    (K : SemiRepresentableOver C X) (i : K.I) :
    Sigma.ι (fun i : K.I => representablePresheaf (K.obj i).left) i ≫
        semiRepresentableOverStructureMap X K =
      representablePresheafMapOfOver (K.obj i) := by
  exact Sigma.ι_desc _ _

/-- The functor from semi-representable objects over `X` to presheaves over
`h_X`.  The target `Over (h_X)` is the source's
`PSh(C)/h_X`. -/
def semiRepresentableOverPresheafFunctor {C : Type u} [Category.{v} C]
    (X : C) :
    SemiRepresentableOver C X ⥤ PresheafOver C X :=
  Functor.toOver (semiRepresentableOverUnderlying X) (representablePresheaf X)
    (fun K => semiRepresentableOverStructureMap X K) (by
      intro K L f
      refine Sigma.hom_ext _ _ (fun i => ?_)
      change K.I at i
      change
        (Sigma.ι (fun j : K.I => representablePresheaf (K.obj j).left) i ≫
            (Sigma.desc fun j : K.I =>
              (functorOfPoints (C := C)).map (f.φ j).left ≫
                Sigma.ι (fun j : L.I => representablePresheaf (L.obj j).left) (f.f j)) ≫
              Sigma.desc (fun j : L.I => representablePresheafMapOfOver (L.obj j))) =
          Sigma.ι (fun j : K.I => representablePresheaf (K.obj j).left) i ≫
            Sigma.desc (fun j : K.I => representablePresheafMapOfOver (K.obj j))
      simp only [Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
      simpa only [representablePresheafMapOfOver, Functor.map_comp] using
        congrArg (fun h => (functorOfPoints (C := C)).map h) (f.φ i).w)

/- The upper-left-to-lower-left part of the source's square is recovered by
forgetting the target map in the slice. -/
@[simp]
theorem semiRepresentableOverPresheafFunctor_forget
    {C : Type u} [Category.{v} C] {X : C} :
    semiRepresentableOverPresheafFunctor X ⋙
        (Over.forget (representablePresheaf X) :
          PresheafOver C X ⥤ Presheaf C) =
      semiRepresentableOverUnderlying X :=
  rfl

/-! ## Limits and colimits -/

/-- `SR(C)` has the coproducts represented by disjoint unions of families. -/
theorem semiRepresentable_has_coproducts
    {C : Type u} [Category.{v} C] :
    HasCoproducts.{v} (SemiRepresentable.{v} C) := by
  infer_instance

/-- The functor to presheaves commutes with coproducts. -/
theorem semiRepresentablePresheafFunctor_preserves_coproducts
    {C : Type u} [Category.{v} C] (J : Type v) :
    PreservesColimitsOfShape (Discrete J)
      (semiRepresentablePresheafFunctor (C := C)) := by
  infer_instance

/-- The functor to presheaves commutes with all limits which exist. -/
theorem semiRepresentablePresheafFunctor_preserves_limits
    {C : Type u} [Category.{v} C] :
    PreservesLimits (semiRepresentablePresheafFunctor (C := C)) := by
  sorry

/-- Fibre products in `C` induce fibre products in `SR(C)`. -/
theorem semiRepresentable_has_fibre_products
    {C : Type u} [Category.{v} C] [HasPullbacks C] :
    HasPullbacks (SemiRepresentable.{v} C) := by
  infer_instance

/-- Products of pairs in `C` induce products of pairs in `SR(C)`. -/
theorem semiRepresentable_has_binary_products
    {C : Type u} [Category.{v} C] [HasBinaryProducts C] :
    HasBinaryProducts (SemiRepresentable.{v} C) := by
  sorry

/-- Equalizers in `C` induce equalizers in `SR(C)`. -/
theorem semiRepresentable_has_equalizers
    {C : Type u} [Category.{v} C] [HasEqualizers C] :
    HasEqualizers (SemiRepresentable.{v} C) := by
  sorry

/-- A final object of `C` gives a final semi-representable object. -/
theorem semiRepresentable_has_terminal
    {C : Type u} [Category.{v} C] [HasTerminal C] :
    HasTerminal (SemiRepresentable.{v} C) := by
  infer_instance

/-- `SR(C/X)` has coproducts. -/
theorem semiRepresentableOver_has_coproducts
    {C : Type u} [Category.{v} C] (X : C) :
    HasCoproducts.{v} (SemiRepresentableOver C X) := by
  infer_instance

/-- The functor from `SR(C/X)` to `PSh(C)/h_X` commutes with coproducts. -/
theorem semiRepresentableOverPresheafFunctor_preserves_coproducts
    {C : Type u} [Category.{v} C] (X : C) (J : Type v) :
    PreservesColimitsOfShape (Discrete J)
      (semiRepresentableOverPresheafFunctor X) := by
  sorry

/-- If `C` has fibre products, then `SR(C/X)` has finite limits. -/
theorem semiRepresentableOver_has_finite_limits
    {C : Type u} [Category.{v} C] (X : C) [HasPullbacks C] :
    HasFiniteLimits (SemiRepresentableOver C X) := by
  let _ : HasPullbacks (Over X) := inferInstance
  let _ : HasTerminal (Over X) := Over.over_hasTerminal X
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- If `C` has fibre products, the functor to `PSh(C)/h_X` commutes with
finite limits. -/
theorem semiRepresentableOverPresheafFunctor_preserves_finite_limits
    {C : Type u} [Category.{v} C] (X : C) [HasPullbacks C] :
    PreservesFiniteLimits (semiRepresentableOverPresheafFunctor X) := by
  sorry

end

end Formalization.Books.Hypercovering.Unit02
