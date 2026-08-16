import Formalization.Books.SpacesCohomology.Unit01.Core

/-!
# Cohomology of Algebraic Spaces, Chapter 1: conventions

The standing fppf-site convention is recorded in the section documentation.
The only book-facing construction in this section is the relative self-product
notation, implemented using the existing pullback in `TopCat`.
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

structure BigFppfSiteConvention where
  schemes_are_objects : Prop
  admissible_rings : Prop

structure RelativeProductConvention (S X : AlgebraicSpace.{u})
    (f : SpaceHom X S) where
  product : AlgebraicSpace.{u}
  first_projection : SpaceHom product X
  second_projection : SpaceHom product X
  universal_property : Prop

noncomputable def relativeSelfProduct (S X : AlgebraicSpace.{u})
    (f : SpaceHom X S) : AlgebraicSpace.{u} :=
  relativeProduct X X S f f

noncomputable def relativeSelfProductFst (S X : AlgebraicSpace.{u})
    (f : SpaceHom X S) : SpaceHom (relativeSelfProduct S X f) X :=
  relativeProductFst f f

noncomputable def relativeSelfProductSnd (S X : AlgebraicSpace.{u})
    (f : SpaceHom X S) : SpaceHom (relativeSelfProduct S X f) X :=
  relativeProductSnd f f

end Formalization.Books.SpacesCohomology.Unit01
