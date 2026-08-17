import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import Mathlib.CategoryTheory.Category.Cat

namespace Scratch

open CategoryTheory
open CategoryTheory.Bicategory

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C]
variable {A : Type u} [Category.{v} A]

variable (map : ∀ {R S : C}, (R ⟶ S) → (A ⥤ A))
variable (unit : ∀ U : C, map (𝟙 U) ≅ 𝟭 A)
variable (comp : ∀ {R S T : C} (f : R ⟶ S) (g : S ⟶ T),
    map (f ≫ g) ≅ map g ⋙ map f)

def test : Pseudofunctor (LocallyDiscrete Cᵒᵖ) (Bicategory.Pith (Cat.{v, u})) := by
  exact LocallyDiscrete.mkPseudofunctor
    (fun _ : Cᵒᵖ => Bicategory.Pith.mk (Cat.of A))
    (fun {U V} f => Core.mk (map f.unop).toCatHom)
    (fun U => Core.isoMk (Cat.Hom.isoMk (unit U.unop)))
    (fun {U V W} f g => by
      exact Core.isoMk (Cat.Hom.isoMk (comp g.unop f.unop)))

def test2 : Pseudofunctor (LocallyDiscrete Cᵒᵖ) (Bicategory.Pith (Cat.{v, u})) := by
  exact pseudofunctorOfIsLocallyDiscrete
    (fun _ : LocallyDiscrete Cᵒᵖ => Bicategory.Pith.mk (Cat.of A))
    (fun {U V} f => Core.mk (map f.as.unop).toCatHom)
    (fun U => Core.isoMk (Cat.Hom.isoMk (unit U.as.unop)))
    (fun {U V W} f g => by
      exact Core.isoMk (Cat.Hom.isoMk (comp g.as.unop f.as.unop)))

end

end Scratch
