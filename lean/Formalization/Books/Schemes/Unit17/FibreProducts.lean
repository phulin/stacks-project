import Formalization.Books.Schemes.Unit16.FibreProducts
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Schemes, Chapter 17: Fibre products of schemes

This file records the chapter's review of the fibre-product universal property and its
source-facing descriptions. The underlying objects and maps use Mathlib's canonical pullback
and open-cover constructions. In particular, `Scheme.Pullback.Triplet`, `Triplet.tensor`, and
`Scheme.Pullback.carrierEquiv` are the canonical point and residue-field interfaces.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

namespace Formalization.Books.Schemes.Unit17

universe u

/-! ## The fibre-product universal property -/

/-- The fibre product of two morphisms of schemes with common target. -/
abbrev schemeFibreProduct {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) : Scheme.{u} :=
  pullback f g

/-- The first projection from a scheme fibre product. -/
abbrev schemeFibreProductFst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    schemeFibreProduct f g ⟶ X :=
  pullback.fst f g

/-- The second projection from a scheme fibre product. -/
abbrev schemeFibreProductSnd {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    schemeFibreProduct f g ⟶ Y :=
  pullback.snd f g

/-- The commutative pullback cone displaying the scheme fibre product. -/
def schemeFibreProductCone {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    PullbackCone f g :=
  PullbackCone.mk (schemeFibreProductFst f g) (schemeFibreProductSnd f g) (by
    exact pullback.condition)

/-- The canonical projections satisfy the fibre-product universal property. -/
theorem schemeFibreProduct_isPullback {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (schemeFibreProductFst f g) (schemeFibreProductSnd f g) f g := by
  exact IsPullback.of_hasPullback f g

/-! ## Affine fibre products -/

/-- A fibre product of three affine schemes is affine. -/
theorem schemeFibreProduct_isAffine {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [hX : IsAffine X] [hY : IsAffine Y] [hS : IsAffine S] :
    IsAffine (schemeFibreProduct f g) := by
  infer_instance

/-! ## Restriction to open subschemes -/

/-- The canonical map from the open fibre product to the ambient fibre product.

Here `hV` and `hW` express the source conditions `f(V) ⊆ U` and `g(W) ⊆ U` as inclusions
of opens into the corresponding preimages. -/
def openFibreProductCanonical {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U) :
    pullback (f.resLE U V hV) (g.resLE U W hW) ⟶ schemeFibreProduct f g :=
  pullback.map (f.resLE U V hV) (g.resLE U W hW) f g V.ι W.ι U.ι
    (Scheme.Hom.resLE_comp_ι f hV)
    (Scheme.Hom.resLE_comp_ι g hW)

/-- The open fibre product identifies with the intersection of the two inverse-image opens. -/
instance openFibreProductCanonical_isOpenImmersion
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U) :
    IsOpenImmersion (openFibreProductCanonical f g U V W hV hW) := by
  sorry

/-- The range of the canonical open-fibre-product map is the expected intersection. -/
theorem openFibreProductCanonical_opensRange
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U) :
    (openFibreProductCanonical f g U V W hV hW).opensRange =
      (schemeFibreProductFst f g) ⁻¹ᵁ V ⊓ (schemeFibreProductSnd f g) ⁻¹ᵁ W := by
  sorry

/-- The two ways of forming the open fibre product are canonically isomorphic. -/
theorem openFibreProduct_iso_overS
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U) :
    Nonempty
      (pullback (f.resLE U V hV) (g.resLE U W hW) ≅
        pullback (V.ι ≫ f) (W.ι ≫ g)) := by
  sorry

/-- If the three open subschemes are affine, their open fibre product is affine. -/
theorem openFibreProduct_isAffine
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U)
    [hUaff : IsAffine U.toScheme] [hVaff : IsAffine V.toScheme]
    [hWaff : IsAffine W.toScheme] :
    IsAffine (pullback (f.resLE U V hV) (g.resLE U W hW)) := by
  infer_instance

/-! ## Affine open covers of fibre products -/

/-- Data for the affine open coverings used in the bare-hands fibre-product construction. -/
structure AffineFibreProductCoverData {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  /-- An open cover of the base whose members are affine. -/
  U : S.OpenCover
  U_affine : ∀ i, IsAffine (U.X i)
  /-- An open cover of each preimage of a base member in `X`, with affine members. -/
  V : ∀ i, ((U.pullback₁ f).X i).OpenCover
  V_affine : ∀ i j, IsAffine ((V i).X j)
  /-- An open cover of each preimage of a base member in `Y`, with affine members. -/
  W : ∀ i, ((U.pullback₁ g).X i).OpenCover
  W_affine : ∀ i j, IsAffine ((W i).X j)

/-- Assemble the compatible affine pieces into an open cover of the fibre product. -/
def affineFibreProductOpenCover {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (D : AffineFibreProductCoverData f g) :
    (schemeFibreProduct f g).OpenCover :=
  (Scheme.Pullback.openCoverOfBase D.U f g).bind (fun i ↦
    Scheme.Pullback.openCoverOfLeftRight (D.V i) (D.W i)
      (D.U.pullbackHom f i) (D.U.pullbackHom g i))

/-- Every member assembled by `affineFibreProductOpenCover` is affine. -/
theorem affineFibreProductOpenCover_isAffine
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (D : AffineFibreProductCoverData f g) :
    ∀ i, IsAffine ((affineFibreProductOpenCover D).X i) := by
  sorry

/-! ## Points of a fibre product -/

/-- The point data for a fibre product: a compatible triplet and a prime of its residue-field
tensor product. -/
abbrev fibreProductPointData {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :=
  Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor

/-- The prime ideal in the tensor product represented by a point datum. -/
def fibreProductPointPrimeIdeal {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (a : fibreProductPointData f g) : Ideal a.1.tensor :=
  a.2.asIdeal

/-- The source's bijection between points of a fibre product and compatible point data. -/
def fibreProductPointsEquiv {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    schemeFibreProduct f g ≃ fibreProductPointData f g :=
  Scheme.Pullback.carrierEquiv

/-- The residue field of a fibre-product point agrees with the residue field of its associated
prime in the tensor product. -/
theorem fibreProductPoints_residueField_correspondence
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (z : schemeFibreProduct f g) :
    Nonempty
      ((schemeFibreProduct f g).residueField z ≅
        (Spec (fibreProductPointsEquiv f g z).1.tensor).residueField
          (fibreProductPointsEquiv f g z).2) := by
  sorry

/-! ## Immersions and base change -/

/-- Closed immersions remain closed immersions after base change. -/
theorem pullback_snd_isClosedImmersion_of_isClosedImmersion
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [hf : IsClosedImmersion f] :
    IsClosedImmersion (schemeFibreProductSnd f g) := by
  infer_instance

/-- In the canonical ideal-sheaf presentation, the ideal after base change is Mathlib's
`IdealSheafData.comap`, the image of the pulled-back ideal in the new structure sheaf. -/
theorem closedImmersion_baseChange_ideal
    {Y Z : Scheme.{u}} (I : Y.IdealSheafData) (g : Z ⟶ Y) :
    Nonempty
      ((I.comap g).subscheme ≅
        schemeFibreProduct I.subschemeι g) := by
  exact ⟨I.comapIso g ≪≫ pullbackSymmetry g I.subschemeι⟩

/-- Open immersions remain open immersions after base change. -/
theorem pullback_snd_isOpenImmersion_of_isOpenImmersion
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [hf : IsOpenImmersion f] :
    IsOpenImmersion (schemeFibreProductSnd f g) := by
  infer_instance

/-- Immersions remain immersions after base change. -/
theorem pullback_snd_isImmersion_of_isImmersion
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [hf : IsImmersion f] :
    IsImmersion (schemeFibreProductSnd f g) := by
  infer_instance

/-! ## Inverse images of closed subschemes -/

/-- A closed subscheme in the canonical ideal-sheaf presentation. -/
abbrev ClosedSubscheme (Y : Scheme.{u}) := Y.IdealSheafData

/-- The scheme underlying a canonical closed subscheme. -/
abbrev closedSubschemeScheme {Y : Scheme.{u}} (Z : ClosedSubscheme Y) : Scheme.{u} :=
  Z.subscheme

/-- The inclusion of a canonical closed subscheme. -/
abbrev closedSubschemeInclusion {Y : Scheme.{u}} (Z : ClosedSubscheme Y) :
    closedSubschemeScheme Z ⟶ Y :=
  Z.subschemeι

/-- The inverse image of a closed subscheme, defined by the fibre product. -/
def inverseImageClosedSubscheme {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : ClosedSubscheme Y) :
    Scheme.{u} :=
  schemeFibreProduct (closedSubschemeInclusion Z) f

/-- The inclusion of the inverse-image closed subscheme into `X`. -/
def inverseImageClosedSubschemeInclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Z : ClosedSubscheme Y) : inverseImageClosedSubscheme f Z ⟶ X :=
  schemeFibreProductSnd (closedSubschemeInclusion Z) f

/-- The ideal-sheaf presentation of the inverse image. -/
abbrev inverseImageClosedSubschemeIdeal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Z : ClosedSubscheme Y) : X.IdealSheafData :=
  Z.comap f

/-- The canonical identification of the fibre-product inverse image with its ideal-sheaf model. -/
def inverseImageClosedSubschemeIdealIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Z : ClosedSubscheme Y) :
    inverseImageClosedSubscheme f Z ≅
      (inverseImageClosedSubschemeIdeal f Z).subscheme :=
  (Z.comapIso f ≪≫ pullbackSymmetry f Z.subschemeι).symm

/-- The inverse-image inclusion is a closed immersion. -/
instance inverseImageClosedSubschemeInclusion_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : ClosedSubscheme Y) :
    IsClosedImmersion (inverseImageClosedSubschemeInclusion f Z) := by
  sorry

end Formalization.Books.Schemes.Unit17
