import Formalization.Books.SpacesCohomology.Unit02.Core

/-!
# Extension-by-zero interfaces

The extension-by-zero results occur in the source's colimits-and-cohomology
unit. They live here so their proof obligations are owned by Unit05 rather
than by the introductory unit's shared interface.
-/

namespace Formalization.Books.SpacesCohomology.Unit01

open CategoryTheory CategoryTheory.Limits

universe u

section TypedExtensionByZero

variable [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]

structure ExtensionByZeroWarning where
  unrelated_to_compact_support : Prop

structure ExtensionByZeroAdjunction {U X : AlgebraicSpace.{u}}
    (f : SpaceHom U X) where
  hom_equivalence : ∀ (G : SheafObj U) (F : SheafObj X),
    Nonempty (SheafHom (extensionByZero f G) F ≃+
      SheafHom G (restrictSheaf f F))
  warning : ExtensionByZeroWarning

theorem extension_by_zero_left_adjoint
    (S U X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom U X) (hf : IsEtale f) :
    Nonempty (ExtensionByZeroAdjunction f) := by
  sorry

structure EtaleLiftData {U X : AlgebraicSpace.{u}}
    (f : SpaceHom U X) (x : X) where
  Lift : Type u
  point : Lift → U
  over : ∀ i, f (point i) = x
  injective : Function.Injective point
  complete : ∀ u : U, f u = x ↔ ∃ i, point i = u

abbrev StalkDirectSum {U X : AlgebraicSpace.{u}} {f : SpaceHom U X} {x : X}
    (L : EtaleLiftData f x) (G : SheafObj U) : Type u :=
  DirectSum L.Lift (fun i => Stalk U G (L.point i))

theorem extension_by_zero_stalk
    (S U X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom U X) (hf : IsEtale f) (x : X)
    (G : SheafObj U) (L : EtaleLiftData f x) :
    Nonempty (Stalk X (extensionByZero f G) x ≃+ StalkDirectSum L G) := by
  sorry

noncomputable def productEtaleMap {U₁ U₂ X : AlgebraicSpace.{u}}
    (f₁ : SpaceHom U₁ X) (f₂ : SpaceHom U₂ X) :
    SpaceHom (relativeProduct U₁ U₂ X f₁ f₂) X :=
  relativeProductFst f₁ f₂ ≫ f₁

theorem extension_by_zero_product_tensor
    (S U₁ U₂ X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f₁ : SpaceHom U₁ X) (f₂ : SpaceHom U₂ X)
    (hf₁ : IsEtale f₁) (hf₂ : IsEtale f₂) :
    Nonempty (SheafIso X
      (tensorSheaf X (extensionByZero f₁ (constantSheaf U₁))
        (extensionByZero f₂ (constantSheaf U₂)))
      (extensionByZero (productEtaleMap f₁ f₂)
        (constantSheaf (relativeProduct U₁ U₂ X f₁ f₂)))) := by
  sorry

structure EtaleCoproductData {U₁ U₂ X : AlgebraicSpace.{u}}
    (f₁ : SpaceHom U₁ X) (f₂ : SpaceHom U₂ X) where
  carrier : AlgebraicSpace.{u}
  inl : SpaceHom U₁ carrier
  inr : SpaceHom U₂ carrier
  map : SpaceHom carrier X
  coproduct_property : Prop
  sumSheaf : SheafObj X
  sum_identification : Nonempty (SheafIso X
    (extensionByZero map (constantSheaf carrier)) sumSheaf)

theorem extension_by_zero_coproduct
    (S U₁ U₂ X : AlgebraicSpace.{u}) (_hS : IsScheme S)
    (f₁ : SpaceHom U₁ X) (f₂ : SpaceHom U₂ X)
    (_hf₁ : IsEtale f₁) (_hf₂ : IsEtale f₂)
    (C : EtaleCoproductData f₁ f₂) :
    Nonempty (SheafIso X
      (extensionByZero C.map (constantSheaf C.carrier)) C.sumSheaf) := by
  exact C.sum_identification

end TypedExtensionByZero

end Formalization.Books.SpacesCohomology.Unit01
