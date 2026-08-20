import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Formalization.Books.Descent.Unit19.Core

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Formalization.Books.Descent.Unit19

/-! ## Variants on descending properties -/

/-- Flat and surjective descent of reduced schemes. -/
theorem descend_reduced_of_flat_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsReduced X] : IsReduced Y := by
  refine @AlgebraicGeometry.isReduced_of_isReduced_stalk Y ?_
  intro y
  obtain ⟨x, rfl⟩ := ‹Surjective f›.surj y
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact isReduced_of_injective (f.stalkMap x).hom
    (‹RingHom.FaithfullyFlat _›.injective)

/-- Locally finitely presented, flat and surjective descent of regular spaces. -/
theorem descend_regular_of_lfp_flat_surjective
    {X Y : AlgebraicSpaceInterface.Space.{u}}
    [AlgebraicSpaceInterface.AlgebraicSpaceTheory.{u}]
    [AlgebraicSpaceInterface.RegularSpaceTheory.{u}]
    (f : AlgebraicSpaceInterface.Hom X Y)
    (hfp : AlgebraicSpaceInterface.IsLocallyOfFinitePresentation f)
    (hflat : AlgebraicSpaceInterface.IsFlat f)
    (hsurj : AlgebraicSpaceInterface.IsSurjective f)
    (hX : AlgebraicSpaceInterface.IsRegular X) :
    AlgebraicSpaceInterface.IsRegular Y := by
  sorry

end Formalization.Books.Descent.Unit19
