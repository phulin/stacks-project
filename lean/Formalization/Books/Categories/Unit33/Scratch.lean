import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import Mathlib.CategoryTheory.Category.Cat

namespace Formalization.Books.Categories.Unit33Scratch

open CategoryTheory
open CategoryTheory.Bicategory

universe v u

example {C : Type u} [Category.{v} C]
    (A : C → Cat.{v, u})
    (M : ∀ {X Y : C}, (X ⟶ Y) → (A X : Type u) ⥤ (A Y : Type u))
    (I : ∀ (X : C), M (𝟙 X) ≅ 𝟭 (A X : Type u))
    (K : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      M (f ≫ g) ≅ M f ⋙ M g)
    : True := by
  let A' : C → Bicategory.Pith (Cat.{v, u}) := fun X => .mk (A X)
  let M' : ∀ {X Y : C}, (X ⟶ Y) → (A' X ⟶ A' Y) := fun {_ _} f =>
    Core.mk (M f).toCatHom
  let I' : ∀ (X : C), M' (𝟙 X) ≅ 𝟙 _ := fun X =>
    Core.isoMk (Cat.Hom.isoMk (I X))
  let K' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      M' (f ≫ g) ≅ M' f ≫ M' g := fun f g =>
    Core.isoMk (Cat.Hom.isoMk (K f g))
  trivial

end Formalization.Books.Categories.Unit33Scratch
