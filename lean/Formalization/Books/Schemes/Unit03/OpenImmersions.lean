import Formalization.Books.Schemes.Unit02.LocallyRingedSpaces
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Schemes, Chapter 3: Open immersions of locally ringed spaces

Mathlib already provides the canonical open-immersion class for locally ringed
spaces, the restriction of a locally ringed space to an open embedding, the
associated open immersion, and the universal lifting property.  This file
records the source-facing names and statements while retaining those
constructions.
-/

namespace Formalization.Books.Schemes.Unit03

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

universe u

noncomputable section

/-! ## Open immersions and open subspaces -/

/-- The source's definition of an open immersion of locally ringed spaces. -/
abbrev IsOpenImmersion {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion f

/-- The locally ringed space obtained by restricting `X` to the open subset `U`.

This is Mathlib's canonical restriction along the open embedding of the open
subspace, so its structure sheaf is the restriction of `X`'s structure sheaf.
-/
abbrev openSubspace (X : LocallyRingedSpace.{u}) (U : Opens X) :
    LocallyRingedSpace.{u} :=
  X.restrict U.isOpenEmbedding

/-- The canonical morphism from an open subspace to the ambient locally ringed space. -/
abbrev openSubspaceInclusion (X : LocallyRingedSpace.{u}) (U : Opens X) :
    openSubspace X U ⟶ X :=
  X.ofRestrict U.isOpenEmbedding

/-- The restriction construction has the expected presheaf (and hence structure-sheaf) body. -/
theorem openSubspace_presheaf (X : LocallyRingedSpace.{u}) (U : Opens X) :
    (openSubspace X U).presheaf = U.isOpenEmbedding.functor.op ⋙ X.presheaf :=
  rfl

/-- The stalk of an open subspace is canonically the ambient stalk at the same point. -/
noncomputable def openSubspace_stalkIso (X : LocallyRingedSpace.{u}) (U : Opens X)
    (u : openSubspace X U) :
    (openSubspace X U).presheaf.stalk u ≅
      X.presheaf.stalk ((openSubspaceInclusion X U).base u) :=
  X.restrictStalkIso U.isOpenEmbedding u

/-- The stalks of the open subspace are local rings. -/
theorem openSubspace_isLocalRing (X : LocallyRingedSpace.{u}) (U : Opens X)
    (u : openSubspace X U) :
    IsLocalRing ((openSubspace X U).presheaf.stalk u) :=
  inferInstance

/-- The canonical inclusion of an open subspace is an open immersion. -/
instance openSubspaceInclusion_isOpenImmersion
    (X : LocallyRingedSpace.{u}) (U : Opens X) :
    IsOpenImmersion (openSubspaceInclusion X U) := by
  infer_instance

/-! ## An open immersion and the open subspace on its image -/

/-- Mathlib's canonical model for the open subspace associated to the image of
an open immersion.  Its underlying space is the source of the open embedding,
which is canonically homeomorphic to the literal image subtype. -/
abbrev openSubspaceOfImage {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    [H : IsOpenImmersion f] : LocallyRingedSpace.{u} :=
  Y.restrict H.base_open

/-- The inclusion of the open subspace associated to the image of an open immersion. -/
abbrev openSubspaceOfImageInclusion {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    [H : IsOpenImmersion f] : openSubspaceOfImage f ⟶ Y :=
  Y.ofRestrict H.base_open

/-- The source of an open immersion is isomorphic to the open subspace on its image. -/
noncomputable def openImmersion_imageIso {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    [H : IsOpenImmersion f] : X ≅ openSubspaceOfImage f :=
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict f

/-- The image isomorphism followed by the open-subspace inclusion is the original map. -/
theorem openImmersion_imageIso_fac {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    [H : IsOpenImmersion f] :
    (openImmersion_imageIso f).hom ≫ openSubspaceOfImageInclusion f = f :=
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f

/-- The image isomorphism is the unique isomorphism compatible with the inclusion. -/
theorem openImmersion_imageIso_unique {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    [H : IsOpenImmersion f] (g : X ≅ openSubspaceOfImage f)
    (hg : g.hom ≫ openSubspaceOfImageInclusion f = f) :
    g = openImmersion_imageIso f := by
  apply Iso.ext
  apply (cancel_mono (openSubspaceOfImageInclusion f)).1
  rw [hg, openImmersion_imageIso_fac]

/-! ## Restricting a morphism to open subspaces -/

/-- The morphism induced by `f` between open subspaces `U` and `V` when
`f(U) ⊆ V`.  It is obtained from the canonical lifting property of the open
subspace inclusion of `V`. -/
noncomputable def restrictHom {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (U : Opens X) (V : Opens Y) (hf : Set.MapsTo f.base U.1 V.1) :
    openSubspace X U ⟶ openSubspace Y V :=
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift
    (openSubspaceInclusion Y V)
    (openSubspaceInclusion X U ≫ f) (by
      rintro y ⟨x, rfl⟩
      exact ⟨⟨f.base ((openSubspaceInclusion X U).base x),
        hf x.property⟩, rfl⟩)

/-- The restricted morphism makes the defining square commute. -/
theorem restrictHom_fac {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (U : Opens X) (V : Opens Y) (hf : Set.MapsTo f.base U.1 V.1) :
    restrictHom f U V hf ≫ openSubspaceInclusion Y V =
      openSubspaceInclusion X U ≫ f :=
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac
    (openSubspaceInclusion Y V) (openSubspaceInclusion X U ≫ f) _

/-- The restricted morphism is the unique morphism making the defining square commute. -/
theorem restrictHom_unique {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (U : Opens X) (V : Opens Y) (hf : Set.MapsTo f.base U.1 V.1)
    (g : openSubspace X U ⟶ openSubspace Y V)
    (hg : g ≫ openSubspaceInclusion Y V = openSubspaceInclusion X U ≫ f) :
    g = restrictHom f U V hf := by
  apply AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq
    (f := openSubspaceInclusion Y V)
    (g := openSubspaceInclusion X U ≫ f) _ g hg

/-! ## The implicit factorization convention -/

/-- Factor a morphism through an open subspace containing its image. -/
noncomputable def factorThroughOpenSubspace {X Y : LocallyRingedSpace.{u}}
    (f : Y ⟶ X) (U : Opens X) (hf : Set.range f.base ⊆ U.1) :
    Y ⟶ openSubspace X U :=
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift
    (openSubspaceInclusion X U) f (by
      rintro x ⟨y, rfl⟩
      exact ⟨⟨f.base y, hf ⟨y, rfl⟩⟩, rfl⟩)

/-- The factorization through an open subspace composes back to the original map. -/
theorem factorThroughOpenSubspace_fac {X Y : LocallyRingedSpace.{u}}
    (f : Y ⟶ X) (U : Opens X) (hf : Set.range f.base ⊆ U.1) :
    factorThroughOpenSubspace f U hf ≫ openSubspaceInclusion X U = f :=
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac
    (openSubspaceInclusion X U) f _

/-- The factorization through an open subspace is unique. -/
theorem factorThroughOpenSubspace_unique {X Y : LocallyRingedSpace.{u}}
    (f : Y ⟶ X) (U : Opens X) (hf : Set.range f.base ⊆ U.1)
    (g : Y ⟶ openSubspace X U)
    (hg : g ≫ openSubspaceInclusion X U = f) :
    g = factorThroughOpenSubspace f U hf := by
  apply AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq
    (f := openSubspaceInclusion X U) (g := f) _ g hg

end

end Formalization.Books.Schemes.Unit03
