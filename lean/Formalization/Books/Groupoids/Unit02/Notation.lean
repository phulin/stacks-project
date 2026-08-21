import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Yoneda

/-!
# Groupoid Schemes, Chapter 2: Notation

This file formalizes the relative functor-of-points and fibre-product notation
used in the source section `Notation` of `books/groupoids.tex`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Formalization.Books.Groupoids.Unit02

universe u

/-! ## Schemes over a base and relative points -/

/-- Schemes over a fixed scheme, represented by the canonical over category. -/
abbrev SchemeOver (S : Scheme.{u}) := Over S

/-- The set of `T`-valued points of `U` over the base scheme. -/
abbrev points {S : Scheme.{u}} (U T : SchemeOver S) := (T ⟶ U)

/-- The map on relative points induced by a morphism over the base. -/
def pointsMap {S : Scheme.{u}} {X Y : SchemeOver S} (f : X ⟶ Y) (T : SchemeOver S) :
    points X T → points Y T := fun x ↦ x ≫ f

/-- Composition in the test scheme is contravariant, as for the relative functor of points. -/
def pointsRestriction {S : Scheme.{u}} (X T₁ T₂ : SchemeOver S) (g : T₁ ⟶ T₂) :
    points X T₂ → points X T₁ := fun x ↦ g ≫ x

/-- The relative functor of points of a scheme over `S`. -/
abbrev relativeFunctorOfPoints {S : Scheme.{u}} (X : SchemeOver S) :
    (SchemeOver S)ᵒᵖ ⥤ Type u := yoneda.obj X

/-- The objectwise description of the relative functor of points. -/
theorem relativeFunctorOfPoints_obj {S : Scheme.{u}} (X T : SchemeOver S) :
    (relativeFunctorOfPoints X).obj (Opposite.op T) = points X T := rfl

/-! ## Yoneda's identification -/

/-- A morphism over `S` and the corresponding natural transformation of relative points. -/
abbrev relativeYonedaMap {S : Scheme.{u}} {X Y : SchemeOver S} (f : X ⟶ Y) :
    relativeFunctorOfPoints X ⟶ relativeFunctorOfPoints Y := yoneda.map f

/-- Yoneda identifies morphisms over `S` with natural transformations of relative points. -/
noncomputable def relativeYonedaHomEquiv {S : Scheme.{u}} (X Y : SchemeOver S) :
    (X ⟶ Y) ≃ (relativeFunctorOfPoints X ⟶ relativeFunctorOfPoints Y) :=
  Functor.FullyFaithful.homEquiv (Yoneda.fullyFaithful (C := SchemeOver S))

/-! ## Fibre products and their point maps -/

/-- The underlying scheme-theoretic fibre product of two schemes over `S`. -/
abbrev fiberProduct {S : Scheme.{u}} (X Y : SchemeOver S) : Scheme.{u} :=
  (Limits.prod X Y).left

/-- The fibre product, regarded as a scheme over `S`. -/
abbrev fiberProductOver {S : Scheme.{u}} (X Y : SchemeOver S) : SchemeOver S :=
  Limits.prod X Y

/-- The first projection from a relative fibre product. -/
abbrev fiberProductFst {S : Scheme.{u}} (X Y : SchemeOver S) :
    fiberProductOver X Y ⟶ X :=
  Limits.prod.fst

/-- The second projection from a relative fibre product. -/
abbrev fiberProductSnd {S : Scheme.{u}} (X Y : SchemeOver S) :
    fiberProductOver X Y ⟶ Y :=
  Limits.prod.snd

/-- A compatible pair of relative points is the same as a point of the fibre product. -/
def fiberProductPointsEquiv {S : Scheme.{u}} (X Y T : SchemeOver S) :
    points (fiberProductOver X Y) T ≃ points X T × points Y T where
  toFun p := ⟨p ≫ fiberProductFst X Y, p ≫ fiberProductSnd X Y⟩
  invFun p := Limits.prod.lift p.1 p.2
  left_inv p := by
    apply Limits.prod.hom_ext
    · exact Limits.prod.lift_fst _ _
    · exact Limits.prod.lift_snd _ _
  right_inv p := by
    apply Prod.ext
    · exact Limits.prod.lift_fst _ _
    · exact Limits.prod.lift_snd _ _

/-- The map on pairs of points induced by a morphism between relative fibre products. -/
def fiberProductPointsMap {S : Scheme.{u}} {X Y Z : SchemeOver S}
    (m : fiberProductOver X Y ⟶ fiberProductOver Z Z) (T : SchemeOver S) :
    points X T × points Y T → points Z T × points Z T :=
  (fiberProductPointsEquiv Z Z T).toFun ∘ pointsMap m T ∘
    (fiberProductPointsEquiv X Y T).invFun

/-! ## Zero-based projections -/

/-- The first and second projections of a relative fibre product, indexed from zero. -/
abbrev pr₀ {S : Scheme.{u}} (X Y : SchemeOver S) : fiberProductOver X Y ⟶ X :=
  fiberProductFst X Y

abbrev pr₁ {S : Scheme.{u}} (X Y : SchemeOver S) : fiberProductOver X Y ⟶ Y :=
  fiberProductSnd X Y

end Formalization.Books.Groupoids.Unit02
