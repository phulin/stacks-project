import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Differential Graded Algebra, Chapter 24: Linear categories

The source convention that a ring is commutative is represented by
`CommRing`.  Mathlib's `CategoryTheory.Linear` is the canonical interface for
the first definition: together with the required `Preadditive` instance it
provides an `R`-module on every Hom type and scalar-compatible composition.
The source does not assume an additive category in the stronger sense used by
the book (for example, finite biproducts), and no such assumption is added
here.

The source's functor definition asks for a homomorphism of `R`-modules on
every Hom type.  Mathlib exposes the additive and scalar-preserving parts as
the separate `Functor.Additive` and `Functor.Linear` interfaces, so the
chapter-facing interface below records both.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v v' w w'

namespace Formalization.Books.Dga.Unit24

/-! ## Linear categories -/

/-
The textbook's first definition is already supplied by Mathlib's
`CategoryTheory.Linear R C`.  Its `homModule`, `smul_comp`, and `comp_smul`
fields are the module and bilinearity data in the source.
-/

/-- The tensor-product form of composition in an `R`-linear category.

The tensor factors are ordered as in the source, namely
`Hom(Y, Z) ⊗[R] Hom(X, Y)`, so a pure tensor `g ⊗ f` is sent to `f ≫ g`.
-/
def linearCompositionTensorProduct
    (R : Type u) {C : Type v}
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C]
    (X Y Z : C) :
    (Y ⟶ Z) ⊗[R] (X ⟶ Y) →ₗ[R] (X ⟶ Z) :=
  TensorProduct.lift (LinearMap.flip (CategoryTheory.Linear.comp X Y Z))

/-! ## Linear functors -/

/-- A functor whose maps on Hom types are homomorphisms of `R`-modules.

`Functor.Additive` supplies preservation of addition and
`Functor.Linear` supplies preservation of scalar multiplication.  Together
they give exactly the source's Hom-module homomorphism condition.
-/
class RLinearFunctor
    (R : Type u) {C : Type v} {D : Type v'}
    [CommRing R] [Category.{w} C] [Category.{w'} D]
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : C ⥤ D) : Prop where
  additive : Functor.Additive F
  linear : Functor.Linear R F

namespace RLinearFunctor

variable {R : Type u} {C : Type v} {D : Type v'}
  [CommRing R] [Category.{w} C] [Category.{w'} D]
  [Preadditive C] [Preadditive D]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  {F : C ⥤ D} (hF : RLinearFunctor R F)

/-- The Hom-module homomorphism induced by an `R`-linear functor. -/
def mapLinearMap {X Y : C} : (X ⟶ Y) →ₗ[R] (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  map_add' := by
    intro f g
    exact hF.additive.map_add
  map_smul' := by
    intro r f
    exact hF.linear.map_smul f r

end RLinearFunctor

end Formalization.Books.Dga.Unit24
