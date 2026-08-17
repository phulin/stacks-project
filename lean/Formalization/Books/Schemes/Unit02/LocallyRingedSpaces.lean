import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField

/-!
# Schemes, Chapter 2: Locally ringed spaces

The source's ringed spaces and locally ringed spaces are Mathlib's canonical
`AlgebraicGeometry.RingedSpace` and `AlgebraicGeometry.LocallyRingedSpace`.
The latter already supplies the stalkwise local-ring condition, its morphisms,
their category structure, stalk maps, and the fact that an isomorphism of the
underlying sheafed spaces lifts to an isomorphism of locally ringed spaces.

The aliases and statements below expose those constructions in the chapter
namespace and record the source's terminology for stalks, maximal ideals,
residue fields, local maps, composition, and the smooth-manifold example.
The smooth-manifold construction is Mathlib's
`ChartedSpace.locallyRingedSpace`; its stalk evaluation theorem identifies the
maximal ideal with the germs vanishing at the chosen point.

The source's remarks about spectra as the eventual building blocks of schemes
are covered by Mathlib's `Scheme` and `Spec` interfaces and introduce no new
object at this point in the source order.
-/

namespace Formalization.Books.Schemes.Unit02

open CategoryTheory
open AlgebraicGeometry
open Manifold
open TopologicalSpace
open scoped ContDiff

universe u

noncomputable section

/-! ## Locally ringed spaces and their stalk data -/

/-- The source's locally ringed spaces, using Mathlib's canonical structure. -/
abbrev LocallyRingedSpace := AlgebraicGeometry.LocallyRingedSpace

/-- A morphism of locally ringed spaces. -/
abbrev LocallyRingedSpaceHom (X Y : LocallyRingedSpace.{u}) := X ⟶ Y

/-- The local ring at a point, namely the stalk of the structure sheaf. -/
abbrev localRing (X : LocallyRingedSpace.{u}) (x : X) : CommRingCat.{u} :=
  X.presheaf.stalk x

/-- The maximal ideal of the local ring at a point. -/
abbrev maximalIdeal (X : LocallyRingedSpace.{u}) (x : X) : Ideal (localRing X x) :=
  IsLocalRing.maximalIdeal (localRing X x)

/-- The residue field at a point. -/
abbrev residueField (X : LocallyRingedSpace.{u}) (x : X) : CommRingCat.{u} :=
  AlgebraicGeometry.LocallyRingedSpace.residueField X x

/-- Every stalk of a locally ringed space is a local ring. -/
theorem localRing_isLocal (X : LocallyRingedSpace.{u}) (x : X) :
    IsLocalRing (localRing X x) :=
  X.isLocalRing x

/-- The residue field is the quotient of the stalk by its maximal ideal. -/
theorem residueField_eq_quotient (X : LocallyRingedSpace.{u}) (x : X) :
    IsLocalRing.ResidueField (localRing X x) =
      ((localRing X x) ⧸ (maximalIdeal X x)) :=
  rfl

/-! ## Stalk maps and local morphisms -/

/-- The ring map on stalks induced by a locally ringed space morphism. -/
abbrev stalkMap {X Y : LocallyRingedSpace.{u}}
    (f : LocallyRingedSpaceHom X Y) (x : X) :
    localRing Y (f.base x) ⟶ localRing X x :=
  AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap f x

/-- The stalk map of a locally ringed space morphism is local. -/
theorem isLocalHom_stalkMap {X Y : LocallyRingedSpace.{u}}
    (f : LocallyRingedSpaceHom X Y) (x : X) :
    IsLocalHom (stalkMap f x).hom :=
  AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap f x

/-- For local rings, locality is equivalent to mapping the maximal ideal into
the maximal ideal. -/
theorem isLocalHom_iff_maps_maximalIdeal
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (φ : R →+* S) :
    IsLocalHom φ ↔
      φ '' (IsLocalRing.maximalIdeal R : Set R) ⊆
        (IsLocalRing.maximalIdeal S : Set S) :=
  (IsLocalRing.local_hom_TFAE φ).out 0 1

/-! ## Composition and the category structure -/

/-- The stalk map of a composite is the displayed composite of stalk maps. -/
theorem stalkMap_comp {X Y Z : LocallyRingedSpace.{u}}
    (f : LocallyRingedSpaceHom X Y) (g : LocallyRingedSpaceHom Y Z) (x : X) :
    stalkMap (f ≫ g) x = stalkMap g (f.base x) ≫ stalkMap f x :=
  AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp f g x

/-!
The category instance on `AlgebraicGeometry.LocallyRingedSpace` uses the
identity and composite stalk-map formulas above and
`RingHom.isLocalHom_comp`; therefore the source's assertion that locally
ringed spaces and their morphisms form a category is already represented by
that canonical instance.
-/

/-! ## Smooth manifolds -/

/-- The locally ringed space attached to a smooth manifold. -/
abbrev smoothManifoldLocallyRingedSpace
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
    {HM : Type*} [TopologicalSpace HM]
    (IM : ModelWithCorners 𝕜 EM HM)
    (M : Type u) [TopologicalSpace M] [ChartedSpace HM M] :
    LocallyRingedSpace.{u} :=
  ChartedSpace.locallyRingedSpace IM M

/-- A smooth map induces a morphism of the corresponding locally ringed
spaces. -/
noncomputable abbrev smoothManifoldLocallyRingedSpaceMap
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
    {HM : Type*} [TopologicalSpace HM]
    (IM : ModelWithCorners 𝕜 EM HM)
    {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
    {HN : Type*} [TopologicalSpace HN]
    (IN : ModelWithCorners 𝕜 EN HN)
    {N : Type u} [TopologicalSpace N] [ChartedSpace HN N]
    (f : M → N) (hf : ContMDiff IM IN ∞ f) :
    smoothManifoldLocallyRingedSpace IM M ⟶
      smoothManifoldLocallyRingedSpace IN N :=
  ChartedSpace.locallyRingedSpaceMap f hf

/-- For the smooth-function sheaf, the maximal ideal in the stalk at `x` is
the ideal of germs vanishing at `x`. -/
theorem smoothStalk_maximalIdeal_eq_vanishingIdeal
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
    {HM : Type*} [TopologicalSpace HM]
    (IM : ModelWithCorners 𝕜 EM HM)
    {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
    (x : M) :
    (IsLocalRing.maximalIdeal
        ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) : Set _) =
      (RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x)).carrier := by
  change nonunits ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) = _
  exact smoothSheafCommRing.nonunits_stalk IM x

/-! ## Isomorphisms -/

/-- An isomorphism of the underlying ringed spaces lifts to an isomorphism of
locally ringed spaces. -/
noncomputable def ringedSpaceIso_isLocallyRingedSpaceIso
    {X Y : LocallyRingedSpace.{u}}
    (e : X.toRingedSpace ≅ Y.toRingedSpace) : X ≅ Y :=
  AlgebraicGeometry.LocallyRingedSpace.isoOfSheafedSpaceIso e

end

end Formalization.Books.Schemes.Unit02
