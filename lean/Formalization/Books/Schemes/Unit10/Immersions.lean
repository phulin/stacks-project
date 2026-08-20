import Formalization.Books.Schemes.Unit04.ClosedImmersions
import Formalization.Books.Schemes.Unit09.Schemes
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Topology.Constructions

/-!
# Schemes, Chapter 10: Immersions of schemes

This file records the closed-subspace lemma, the scheme-level immersion definitions,
the closed-image criterion, and the locally closed factorization from the source.
The canonical scheme and ideal-sheaf constructions are Mathlib's Scheme,
Scheme.IdealSheafData, and IdealSheafData.subscheme; the locally-ringed-space
kernel and closed-subspace interfaces are the source-facing constructions from
Chapter 4.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open Topology
namespace Formalization.Books.Schemes.Unit10

universe u

abbrev LocallyRingedSpace :=
  Formalization.Books.Schemes.Unit02.LocallyRingedSpace
abbrev IdealSheaf := Formalization.Books.Schemes.Unit04.IdealSheaf
abbrev LocallyGenerated {X : LocallyRingedSpace.{u}} (I : IdealSheaf X) : Prop :=
  Formalization.Books.Schemes.Unit04.LocallyGenerated I

/-! ## Closed subspaces of schemes -/

/-- The kernel ideal sheaf of a locally-ringed-space morphism. -/
abbrev closedImmersionKernelIdeal {Z : LocallyRingedSpace.{u}}
    {X : Scheme.{u}} (i : Z ⟶ X.toLocallyRingedSpace) :
    IdealSheaf X.toLocallyRingedSpace :=
  Formalization.Books.Schemes.Unit04.closedImmersionIdeal i

/-- In the scheme context, the local-generation criterion is the source's
quasi-coherence criterion for an ideal sheaf. -/
abbrev IsQuasiCoherentIdealSheaf {X : Scheme.{u}}
    (I : IdealSheaf X.toLocallyRingedSpace) : Prop :=
  LocallyGenerated I

theorem locallyGenerated_iff_quasiCoherentIdealSheaf
    {X : Scheme.{u}} (I : IdealSheaf X.toLocallyRingedSpace) :
    LocallyGenerated I ↔ IsQuasiCoherentIdealSheaf I :=
  Iff.rfl

/-- A scheme presentation of a locally-ringed-space morphism. -/
structure ClosedImmersionSchemeModel {Z : LocallyRingedSpace.{u}}
    {X : Scheme.{u}} (i : Z ⟶ X.toLocallyRingedSpace) where
  scheme : Scheme.{u}
  iso : Z ≅ scheme.toLocallyRingedSpace
  map : scheme ⟶ X
  map_isClosedImmersion : AlgebraicGeometry.IsClosedImmersion map
  commutes : iso.hom ≫ map.toLRSHom = i

/-- The affine quotient chart supplied by a closed immersion over an affine open. -/
structure ClosedImmersionAffineChart {Z : LocallyRingedSpace.{u}}
    {X : Scheme.{u}} {i : Z ⟶ X.toLocallyRingedSpace}
    (M : ClosedImmersionSchemeModel i) (U : X.affineOpens) where
  ideal : Ideal (Γ(X, U))
  ideal_eq_kernel : ideal = M.map.ker.ideal U
  sourceIso :
    (M.map ⁻¹ᵁ U.1).toScheme ≅
      AlgebraicGeometry.Spec (CommRingCat.of (Γ(X, U) ⧸ ideal))
  targetIso : U.1.toScheme ≅ AlgebraicGeometry.Spec (CommRingCat.of (Γ(X, U)))
  commutes :
    sourceIso.hom ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (Ideal.Quotient.mk ideal)) ≫ targetIso.inv =
      M.map ∣_ U.1

/-- A closed immersion with scheme target has a scheme source. -/
theorem exists_closedImmersionSchemeModel
    {Z : LocallyRingedSpace.{u}} {X : Scheme.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace)
    (hi : Formalization.Books.Schemes.Unit04.IsClosedImmersion i) :
    Nonempty (ClosedImmersionSchemeModel i) := by
  sorry

theorem closedImmersion_source_is_scheme
    {Z : LocallyRingedSpace.{u}} {X : Scheme.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace)
    (hi : Formalization.Books.Schemes.Unit04.IsClosedImmersion i) :
    Unit09.IsSchemeLocallyRingedSpace Z := by
  obtain ⟨M⟩ := exists_closedImmersionSchemeModel i hi
  exact ⟨M.scheme, ⟨M.iso⟩⟩

/-- The kernel ideal of a closed immersion is quasi-coherent in the source's
local-generation presentation. -/
theorem closedImmersion_kernel_is_quasiCoherent
    {Z : LocallyRingedSpace.{u}} {X : Scheme.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace)
    (hi : Formalization.Books.Schemes.Unit04.IsClosedImmersion i) :
    IsQuasiCoherentIdealSheaf (closedImmersionKernelIdeal i) := by
  exact hi.ideal_locallyGenerated

theorem exists_closedImmersionAffineChart
    {Z : LocallyRingedSpace.{u}} {X : Scheme.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace)
    (_hi : Formalization.Books.Schemes.Unit04.IsClosedImmersion i)
    (M : ClosedImmersionSchemeModel i) (U : X.affineOpens) :
    Nonempty (ClosedImmersionAffineChart M U) := by
  sorry

/-- Data for the scheme structure on a closed subspace defined by a locally-generated ideal. -/
structure ClosedSubspaceSchemeData (X : Scheme.{u})
    (I : IdealSheaf X.toLocallyRingedSpace) (hI : LocallyGenerated I) where
  scheme : Scheme.{u}
  iso : Formalization.Books.Schemes.Unit04.closedSubspace
      X.toLocallyRingedSpace I hI ≅ scheme.toLocallyRingedSpace

theorem exists_closedSubspaceSchemeData (X : Scheme.{u})
    (I : IdealSheaf X.toLocallyRingedSpace) (hI : LocallyGenerated I) :
    Nonempty (ClosedSubspaceSchemeData X I hI) := by
  sorry

/-- A scheme structure on the closed subspace associated to a locally-generated ideal. -/
noncomputable def closedSubspaceScheme (X : Scheme.{u})
    (I : IdealSheaf X.toLocallyRingedSpace) (hI : LocallyGenerated I) : Scheme.{u} :=
  (Classical.choice (exists_closedSubspaceSchemeData X I hI)).scheme

theorem closedSubspace_is_scheme (X : Scheme.{u})
    (I : IdealSheaf X.toLocallyRingedSpace) (hI : LocallyGenerated I) :
    Unit09.IsSchemeLocallyRingedSpace
      (Formalization.Books.Schemes.Unit04.closedSubspace
        X.toLocallyRingedSpace I hI) := by
  obtain ⟨M⟩ := exists_closedSubspaceSchemeData X I hI
  exact ⟨M.scheme, ⟨M.iso⟩⟩

/-- The affine chart of the closed subscheme attached to an ideal sheaf datum. -/
noncomputable def closedSubschemeAffineChart
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    I.glueDataObj U ⟶ U.1.toScheme :=
  I.glueDataObjι U

theorem closedSubschemeAffineChart_eq_quotient
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    closedSubschemeAffineChart I U =
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ U.2.isoSpec.inv :=
  rfl

/-- The kernel on an affine chart is the chosen ideal. -/
theorem closedSubschemeAffineChart_kernel
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    RingHom.ker (closedSubschemeAffineChart I U).appTop.hom =
      (I.ideal U).comap U.1.topIso.hom.hom :=
  I.ker_glueDataObjι_appTop U

/-- The restriction of the closed-subscheme structure sheaf has the quotient
global-sections description used to express the associated ideal on an affine. -/
noncomputable def closedSubschemeAffineRestrictionIso
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) ≅
      CommRingCat.of (Γ(X, U) ⧸ I.ideal U) :=
  I.subschemeObjIso U

theorem closedSubschemeAffineRestriction_kernel
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    RingHom.ker (I.subschemeι.app U).hom = I.ideal U :=
  I.ker_subschemeι_app U

/-! ## Scheme-level immersion definitions -/

/-- An open immersion of schemes, using Mathlib's canonical property. -/
abbrev IsOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsOpenImmersion f

/-- An open subscheme is the canonical scheme associated to an open of a scheme. -/
abbrev openSubscheme (X : Scheme.{u}) (U : X.Opens) : Scheme.{u} :=
  U.toScheme

/-- The inclusion of an open subscheme. -/
abbrev openSubschemeInclusion (X : Scheme.{u}) (U : X.Opens) :
    openSubscheme X U ⟶ X :=
  U.ι

/-- A closed immersion of schemes, using Mathlib's canonical property. -/
abbrev IsClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsClosedImmersion f

/-- A closed subscheme is the canonical subscheme associated to an ideal sheaf datum. -/
abbrev closedSubscheme (X : Scheme.{u}) (I : X.IdealSheafData) : Scheme.{u} :=
  I.subscheme

/-- The inclusion of the closed subscheme associated to an ideal sheaf datum. -/
abbrev closedSubschemeInclusion (X : Scheme.{u}) (I : X.IdealSheafData) :
    closedSubscheme X I ⟶ X :=
  I.subschemeι

/-- An immersion, or locally closed immersion, of schemes. -/
abbrev IsImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsImmersion f

theorem isImmersion_iff_closed_then_open {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsImmersion f ↔
      ∃ (Z : Scheme.{u}) (i : X ⟶ Z) (j : Z ⟶ Y),
        IsClosedImmersion i ∧ IsOpenImmersion j ∧ i ≫ j = f :=
  AlgebraicGeometry.IsImmersion.isImmersion_iff_exists

theorem openImmersion_isomorphic_to_openSubscheme
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsOpenImmersion f) :
    ∃ U : Y.Opens, ∃ e : X ≅ openSubscheme Y U,
      e.hom ≫ openSubschemeInclusion Y U = f := by
  let _ := hf
  exact ⟨f.opensRange, f.isoOpensRange, f.isoOpensRange_hom_ι⟩

theorem closedImmersion_isomorphic_to_closedSubscheme
    {X Y : Scheme.{u}} (f : X ⟶ Y) (_hf : IsClosedImmersion f) :
    ∃ I : Y.IdealSheafData, ∃ e : X ≅ closedSubscheme Y I,
      e.hom ≫ closedSubschemeInclusion Y I = f := by
  sorry

/-! ## Closed images and the largest closed factor -/

theorem immersion_isClosedImmersion_iff_isClosed_range
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsImmersion f) :
    IsClosedImmersion f ↔ IsClosed (Set.range f) := by
  sorry

/-- The boundary of the image of an immersion. -/
def immersionBoundary {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsImmersion f) : Set Y :=
  closure (Set.range f) \ Set.range f

/-- The largest open subscheme in which an immersion is closed. -/
def immersionLargestClosedOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsImmersion f) : Y.Opens :=
  f.coborderRange

theorem immersionLargestClosedOpen_coe
    {X Y : Scheme.{u}} (f : X ⟶ Y) (_hf : IsImmersion f) :
    (immersionLargestClosedOpen f _hf : Set Y) = (immersionBoundary f _hf)ᶜ := by
  sorry

theorem immersionLargestClosedOpen_factor
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsImmersion f) :
    IsClosedImmersion f.liftCoborder ∧ f.liftCoborder ≫ f.coborderRange.ι = f := by
  let _ := hf
  exact ⟨inferInstance, f.liftCoborder_ι⟩

theorem immersionLargestClosedOpen_is_largest
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsImmersion f)
    (V : Y.Opens)
    (hV : ∃ g : X ⟶ V.toScheme,
      IsClosedImmersion g ∧ g ≫ V.ι = f) :
    V ≤ immersionLargestClosedOpen f hf := by
  sorry

/-- A reverse factorization of an immersion, with an open immersion first. -/
def HasReverseImmersionFactorization {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ (Z : Scheme.{u}) (i : X ⟶ Z) (j : Z ⟶ Y),
    IsOpenImmersion i ∧ IsClosedImmersion j ∧ i ≫ j = f

theorem not_all_immersions_have_reverse_factorization :
    ¬ (∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsImmersion f →
      HasReverseImmersionFactorization f) := by
  sorry

/-! ## Locally closed subschemes and their order -/

/-- A locally closed subscheme is a closed subscheme of an open subscheme whose
closure together with the open equals the ambient scheme. -/
structure LocallyClosedSubscheme (X : Scheme.{u}) where
  openPart : X.Opens
  ideal : openPart.toScheme.IdealSheafData
  closure_union_open :
    closure (Set.range (ideal.subschemeι ≫ openPart.ι)) ∪ (openPart : Set X) = Set.univ

abbrev LocallyClosedSubscheme.scheme {X : Scheme.{u}}
    (Z : LocallyClosedSubscheme X) : Scheme.{u} :=
  Z.ideal.subscheme

abbrev LocallyClosedSubscheme.inclusion {X : Scheme.{u}}
    (Z : LocallyClosedSubscheme X) : Z.scheme ⟶ X :=
  Z.ideal.subschemeι ≫ Z.openPart.ι

/-- The collection of locally closed subschemes of X is a set-sized type. -/
abbrev LocallyClosedSubschemes (X : Scheme.{u}) := Set (LocallyClosedSubscheme X)

/-- Containment is factorization of the ambient morphism. -/
def LocallyClosedSubscheme.IsContainedIn {X : Scheme.{u}}
    (Z Z' : LocallyClosedSubscheme X) : Prop :=
  ∃ g : Z.scheme ⟶ Z'.scheme, g ≫ Z'.inclusion = Z.inclusion

instance locallyClosedSubschemePartialOrder (X : Scheme.{u}) :
    PartialOrder (LocallyClosedSubscheme X) where
  le Z Z' := LocallyClosedSubscheme.IsContainedIn Z Z'
  le_refl Z := ⟨𝟙 _, by simp [LocallyClosedSubscheme.inclusion]⟩
  le_trans Z₁ Z₂ Z₃ h₁ h₂ := by
    obtain ⟨g₁, hg₁⟩ := h₁
    obtain ⟨g₂, hg₂⟩ := h₂
    exact ⟨g₁ ≫ g₂, by rw [Category.assoc, hg₂, hg₁]⟩
  le_antisymm := by
    intro Z Z' h h'
    sorry

theorem locallyClosedSubscheme_factor_unique
    {X : Scheme.{u}} (Z Z' : LocallyClosedSubscheme X)
    (_h : Z.IsContainedIn Z') :
    ∃! g : Z.scheme ⟶ Z'.scheme, g ≫ Z'.inclusion = Z.inclusion := by
  sorry

/-- A factorization of an immersion through a locally closed subscheme. -/
structure ImmersionLocallyClosedFactorization
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : IsImmersion f) where
  carrier : LocallyClosedSubscheme X
  iso : Y ≅ carrier.scheme
  commutes : iso.hom ≫ carrier.inclusion = f

theorem immersion_factors_through_locallyClosed
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : IsImmersion f) :
    Nonempty (ImmersionLocallyClosedFactorization f hf) := by
  sorry

theorem immersion_locallyClosed_factorization_unique
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : IsImmersion f)
    (a b : ImmersionLocallyClosedFactorization f hf) :
    ∃! e : a.carrier.scheme ≅ b.carrier.scheme,
      e.hom ≫ b.carrier.inclusion = a.carrier.inclusion ∧
        a.iso.hom ≫ e.hom = b.iso.hom := by
  sorry

end Formalization.Books.Schemes.Unit10

end
