import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Formalization.Books.Examples.Unit38.FiniteTypeFlatNotFinitePresentation
import Formalization.Books.SpacesGroupoids.Unit20.Core

/-!
# Examples, Chapter 73: the stack of proper algebraic spaces is not algebraic

The source introduces the stack of flat, proper, finitely presented algebraic
spaces and then gives a K3-surface formal-effectiveness obstruction. Mathlib
and earlier project chapters provide the fppf-sheaf model, fibred-category
interfaces, scheme morphism properties, and the algebraic constructions.
Cohomology, Picard groups of schemes, and deformation theory are recorded
below as explicit source-facing data because this snapshot does not provide
those moduli objects.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open Formalization.Books.Stacks.Unit01
open scoped TensorProduct

universe u

namespace Formalization.Books.Examples.Unit73

/-! ## The stack of finitely presented flat proper algebraic spaces -/

/-- The objects in the fibre over S of the stack from the source. -/
structure FlatProperFinitelyPresentedAlgebraicSpace (S : Scheme.{u}) where
  /-- The fppf sheaf of points of the algebraic space. -/
  space : Formalization.Books.SpacesGroupoids.Unit20.AlgebraicSpace S
  /-- Flatness of the structure morphism. -/
  flat : Prop
  /-- Properness of the structure morphism. -/
  proper : Prop
  /-- Finite presentation of the structure morphism. -/
  finitelyPresented : Prop

/-- The geometric property carried by an object of the section category. -/
def IsFlatProperFinitelyPresented
    {S : Scheme.{u}} (X : FlatProperFinitelyPresentedAlgebraicSpace S) : Prop :=
  X.flat ∧ X.proper ∧ X.finitelyPresented

namespace FlatProperFinitelyPresentedAlgebraicSpace

/-- A morphism in the fibre category over S. -/
structure Hom {S : Scheme.{u}}
    (X Y : FlatProperFinitelyPresentedAlgebraicSpace S) where
  map : X.space ⟶ Y.space

@[ext]
theorem hom_ext {S : Scheme.{u}}
    {X Y : FlatProperFinitelyPresentedAlgebraicSpace S}
    {f g : Hom X Y} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

end FlatProperFinitelyPresentedAlgebraicSpace

instance (S : Scheme.{u}) : Category (FlatProperFinitelyPresentedAlgebraicSpace S) where
  Hom := FlatProperFinitelyPresentedAlgebraicSpace.Hom
  id X := ⟨𝟙 X.space⟩
  comp f g := ⟨f.map ≫ g.map⟩

/-- The category of flat, proper, finitely presented algebraic spaces over S.

The underlying algebraic space is the canonical fppf-sheaf model from the
earlier algebraic-spaces chapter. The geometric properties are carried as the
source predicates because that model does not expose morphism properties for
algebraic spaces. -/
abbrev ProperAlgebraicSpaceSectionCategory (S : Scheme.{u}) :=
  FlatProperFinitelyPresentedAlgebraicSpace S

/-- The section category of p'_{fp, flat, proper}. -/
abbrev properAlgebraicSpaceStackSections (S : Scheme.{u}) :=
  ProperAlgebraicSpaceSectionCategory S

/-- The global fppf fibred-category interface for the stack in the source. -/
structure ProperAlgebraicSpaceStackData where
  fibre : FiberedCategory (Scheme.{u})
  fibre_equivalence : ∀ S : Scheme.{u}, Nonempty
    (Fiber fibre S ≌ ProperAlgebraicSpaceSectionCategory S)
  is_fppf_stack :
    Formalization.Books.SpacesGroupoids.Unit20.StackInGroupoids fibre
      AlgebraicGeometry.Scheme.fppfTopology

/-- Existence of the stack whose sections are flat, proper, finitely presented
algebraic spaces. -/
def ProperAlgebraicSpaceStackIsFppfStack : Prop :=
  Nonempty (ProperAlgebraicSpaceStackData.{u})

theorem proper_algebraic_space_stack_exists :
    ProperAlgebraicSpaceStackIsFppfStack := by
  sorry

/-- A chosen presentation of the stack from the source. -/
noncomputable def properAlgebraicSpaceStack : ProperAlgebraicSpaceStackData.{u} :=
  Classical.choice proper_algebraic_space_stack_exists

theorem proper_algebraic_space_stack_is_fppf_stack :
    Formalization.Books.SpacesGroupoids.Unit20.StackInGroupoids
      properAlgebraicSpaceStack.fibre
      AlgebraicGeometry.Scheme.fppfTopology :=
  properAlgebraicSpaceStack.is_fppf_stack

/-! ## The numerical deformation setup -/

/-- The formal parameter count g squared for a dimension-g abelian variety. -/
def abelianVarietyFormalParameterCount (g : ℕ) : ℕ := g ^ 2

/-- The dimension bound g(g + 1)/2 for an effective formal deformation. -/
def effectiveFormalDeformationDimensionBound (g : ℕ) : ℕ := g * (g + 1) / 2

/-- For dimension at least two, the universal parameter count is larger than
the bound for an effective formal deformation. -/
theorem abelianVarietyFormalParameterCount_exceeds_effectiveBound
    {g : ℕ} (hg : 2 ≤ g) :
    effectiveFormalDeformationDimensionBound g <
      abelianVarietyFormalParameterCount g := by
  sorry

/-! ## The quartic K3 surface -/

/-- The projective 3-space model reused from the earlier examples chapter. -/
abbrev projectiveThreeSpace (k : Type u) [Field k] : Scheme.{u} :=
  Formalization.Books.Examples.Unit38.projectiveSpace k 3

/-- A smooth degree-four surface embedded in projective three-space. -/
structure SmoothQuarticSurface (k : Type u) [Field k] where
  surface : Scheme.{u}
  embedding : surface ⟶ projectiveThreeSpace k
  embedding_is_closed : IsClosedImmersion embedding
  structureMap : surface ⟶ Spec (CommRingCat.of k)
  smooth_over_k : Smooth structureMap
  degree : ℕ
  degree_eq_four : degree = 4

/-- The source footnote's characteristic-zero first-Chern-class interface.

The project does not yet expose Picard groups and Hodge cohomology of
schemes as canonical objects, so this record packages precisely the two
groups and the first-Chern map needed by that footnote. -/
structure SmoothQuarticFirstChernData (k : Type u) [Field k]
    (X : SmoothQuarticSurface k) where
  picardGroup : AddCommGrpCat.{0}
  hodgeH1 : AddCommGrpCat.{0}
  firstChern : (picardGroup : Type) →+ (hodgeH1 : Type)
  injective : Function.Injective firstChern

/-- The characteristic-zero assertion from the source footnote. -/
def CharacteristicZeroQuarticFirstChernInjective (k : Type u) [Field k]
    [CharZero k] : Prop :=
  ∀ (X : SmoothQuarticSurface k),
    Nonempty (SmoothQuarticFirstChernData k X)

theorem characteristic_zero_quartic_first_chern_injective
    (k : Type u) [Field k] [CharZero k] :
    CharacteristicZeroQuarticFirstChernInjective k := by
  sorry

/-- A general-enough smooth quartic whose Picard group is generated by the
hyperplane class. -/
structure GeneralSmoothQuarticSurface (k : Type u) [Field k]
    extends SmoothQuarticSurface k where
  picardGroup : AddCommGrpCat.{0}
  hyperplaneClass : (picardGroup : Type)
  picardEquiv : (picardGroup : Type) ≃+ ℤ
  picardEquiv_hyperplaneClass : picardEquiv hyperplaneClass = 1

/-! ## Cohomology and Picard interfaces for the complex quartic K3 -/

/-- Nondegeneracy of a bilinear pairing represented by a linear map on a
tensor product. -/
def IsNondegeneratePairing {k M N P : Type*} [Field k]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module k M] [Module k N] [Module k P]
    (pairing : M ⊗[k] N →ₗ[k] P) : Prop :=
  (∀ m : M, (∀ n : N, pairing (TensorProduct.tmul k m n) = 0) → m = 0) ∧
    (∀ n : N, (∀ m : M, pairing (TensorProduct.tmul k m n) = 0) → n = 0)

/-- Cohomological data used by the K3 obstruction argument.

The module-category objects model the sheaves, while the cohomology and Ext
groups are explicit vector-space interfaces. The fields record the source
identities for the canonical, two-form, structure, cotangent, and tangent
sheaves; the Ext/tangent comparison; the three tangent dimensions; H1 of the
structure sheaf; coherent-duality nondegeneracy; and first-Chern injectivity. -/
structure ComplexQuarticK3Data (X : GeneralSmoothQuarticSurface ℂ) where
  canonicalSheaf : X.surface.Modules
  twoFormsSheaf : X.surface.Modules
  structureSheaf : X.surface.Modules
  canonical_iso_twoForms : Nonempty (canonicalSheaf ≅ twoFormsSheaf)
  twoForms_iso_structure : Nonempty (twoFormsSheaf ≅ structureSheaf)
  cotangentSheaf : X.surface.Modules
  tangentSheaf : X.surface.Modules
  cotangentComplex_is_differentials : Prop
  tangentCohomology : ℕ → ModuleCat.{0} ℂ
  extCohomology : ℕ → ModuleCat.{0} ℂ
  ext_tangent_iso : ∀ i : ℕ,
    Nonempty (extCohomology i ≅ tangentCohomology i)
  h0_tangent_dimension :
    Module.finrank ℂ (tangentCohomology 0 : Type) = 0
  h1_tangent_dimension :
    Module.finrank ℂ (tangentCohomology 1 : Type) = 20
  h2_tangent_dimension :
    Module.finrank ℂ (tangentCohomology 2 : Type) = 0
  h1_structureSheaf : ModuleCat.{0} ℂ
  h1_structureSheaf_dimension :
    Module.finrank ℂ (h1_structureSheaf : Type) = 0
  h1_cotangent : ModuleCat.{0} ℂ
  h2_structureSheaf : ModuleCat.{0} ℂ
  cupProduct :
    (h1_cotangent : Type) ⊗[ℂ] (tangentCohomology 1 : Type) →ₗ[ℂ]
      (h2_structureSheaf : Type)
  cupProduct_nondegenerate : IsNondegeneratePairing cupProduct
  firstChern : (X.picardGroup : Type) →+ (h1_cotangent : Type)
  /-- The injectivity hypothesis singled out in the source footnote; the
  complex quartic instance used here supplies it as part of its data. -/
  firstChern_injective : Function.Injective firstChern
  liftsToFirstOrder :
    ∀ (_c : (X.picardGroup : Type)),
      (tangentCohomology 1 : Type) → Prop

abbrev tangentCohomologyGroup (D : ComplexQuarticK3Data X) (i : ℕ) :=
  D.tangentCohomology i

abbrev extCohomologyGroup (D : ComplexQuarticK3Data X) (i : ℕ) :=
  D.extCohomology i

/-- The class of O_X(n) represented by the hyperplane class. -/
def twist (X : GeneralSmoothQuarticSurface ℂ) (n : ℕ) :
    (X.picardGroup : Type) := n • X.hyperplaneClass

/-- The nonvanishing Chern-class computation for a positive hyperplane twist. -/
theorem positive_twist_first_chern_nonzero
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    {n : ℕ} (hn : 0 < n) :
    D.firstChern (twist X n) ≠ 0 := by
  sorry

theorem complex_quartic_k3_data_exists (X : GeneralSmoothQuarticSurface ℂ) :
    Nonempty (ComplexQuarticK3Data X) := by
  sorry

theorem exists_general_smooth_quartic_surface_over_complex :
    Nonempty (GeneralSmoothQuarticSurface ℂ) := by
  sorry

/-! ## The universal formal deformation -/

/-- The complete local ring of formal power series in twenty variables. -/
abbrev ComplexFormalDeformationRing := MvPowerSeries (Fin 20) ℂ

/-- The ideal generated by the twenty formal parameters. -/
def complexFormalDeformationIdeal : Ideal ComplexFormalDeformationRing :=
  Ideal.span (Set.range (fun i : Fin 20 => MvPowerSeries.X i))

/-- The complete-local-ring assertion for the formal power-series base. -/
def ComplexFormalDeformationRingIsCompleteLocal : Prop :=
  IsLocalRing ComplexFormalDeformationRing ∧
    IsAdicComplete complexFormalDeformationIdeal ComplexFormalDeformationRing

theorem complexFormalDeformationRing_is_complete_local :
    ComplexFormalDeformationRingIsCompleteLocal := by
  sorry

/-- The base scheme of the formal power-series ring. -/
noncomputable def complexFormalDeformationBase : Scheme :=
  Spec (CommRingCat.of ComplexFormalDeformationRing)

/-- The ring of the (n + 1)st infinitesimal neighbourhood of the closed point. -/
abbrev complexFormalDeformationLevelRing (n : ℕ) :=
  ComplexFormalDeformationRing ⧸ complexFormalDeformationIdeal ^ (n + 1)

/-- The corresponding infinitesimal neighbourhood. -/
noncomputable def complexFormalDeformationLevel (n : ℕ) : Scheme :=
  Spec (CommRingCat.of (complexFormalDeformationLevelRing n))

/-- A compatible formal object of the proper-algebraic-space stack with
special fibre X. -/
structure ProperFormalObject (X : Scheme) where
  level : ∀ n : ℕ,
    FlatProperFinitelyPresentedAlgebraicSpace (complexFormalDeformationLevel n)
  compatible : Prop
  special_fibre_is_X : Prop

/-- An algebraization of a formal object. -/
structure EffectiveRealization {X : Scheme} (ξ : ProperFormalObject X) where
  totalSpace :
    FlatProperFinitelyPresentedAlgebraicSpace complexFormalDeformationBase
  inducedLevel : ∀ n : ℕ,
    FlatProperFinitelyPresentedAlgebraicSpace (complexFormalDeformationLevel n)
  comparison : ∀ n : ℕ, Nonempty (inducedLevel n ≅ ξ.level n)

/-- Formal effectiveness for the stack in this chapter. -/
def IsEffectiveFormalObject {X : Scheme} (ξ : ProperFormalObject X) : Prop :=
  Nonempty (EffectiveRealization ξ)

/-- The formal-effectiveness consequence of algebraicity used in the chapter.
The actual algebraic-stack object is represented by properAlgebraicSpaceStack;
this predicate records the necessary Artin axiom for the K3 formal objects. -/
structure IsAlgebraicStack (stack : ProperAlgebraicSpaceStackData.{u}) : Prop where
  fppf_stack :
    Formalization.Books.SpacesGroupoids.Unit20.StackInGroupoids stack.fibre
      AlgebraicGeometry.Scheme.fppfTopology
  formal_effective :
    ∀ (X : GeneralSmoothQuarticSurface ℂ) (ξ : ProperFormalObject X.surface),
      IsEffectiveFormalObject ξ

/-- The universal formal deformation supplied by the K3 deformation theory. -/
structure UniversalK3Deformation {X : GeneralSmoothQuarticSurface ℂ}
    (D : ComplexQuarticK3Data X) where
  formalObject : ProperFormalObject X.surface
  universal : Prop

theorem universal_k3_deformation_exists {X : GeneralSmoothQuarticSurface ℂ}
    (D : ComplexQuarticK3Data X) :
    Nonempty (UniversalK3Deformation D) := by
  sorry

/-! ## The Picard obstruction in the informal proof -/

/-- The geometric consequences extracted from an effective realization in the
source argument. -/
structure EffectiveRealizationGeometry {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ) where
  separated : Prop
  separated_holds : separated
  affineOpen : Prop
  affineOpen_holds : affineOpen
  special_fibre_smooth : Prop
  special_fibre_smooth_holds : special_fibre_smooth
  smooth : Prop
  smooth_holds : smooth
  regular : Prop
  regular_holds : regular
  complement_effective_cartier : Prop
  complement_effective_cartier_holds : complement_effective_cartier
  generic_fibre_proper_smooth : Prop
  generic_fibre_proper_smooth_holds : generic_fibre_proper_smooth
  grothendieck_existence : Prop
  grothendieck_existence_holds : grothendieck_existence
  picardGroup : AddCommGrpCat.{0}
  complementDivisorClass : (picardGroup : Type)

def IsSeparatedTotalSpace {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r) : Prop :=
  G.separated

def HasAffineOpenTotalSpace {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r) : Prop :=
  G.affineOpen

def IsSmoothTotalSpace {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r) : Prop :=
  G.smooth

def IsRegularTotalSpace {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r) : Prop :=
  G.regular

def ComplementIsEffectiveCartier {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r) : Prop :=
  G.complement_effective_cartier

def GenericFibreIsProperSmooth {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r) : Prop :=
  G.generic_fibre_proper_smooth

def GrothendieckExistenceForPicard {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r) : Prop :=
  G.grothendieck_existence

/-- The Picard class of the line bundle `O_Y(D)` in the source argument. -/
def complementLineBundleClass {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r) : (G.picardGroup : Type) :=
  G.complementDivisorClass

theorem effective_universal_deformation_has_geometry
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    (𝒟 : UniversalK3Deformation D)
    (r : EffectiveRealization 𝒟.formalObject) :
    Nonempty (EffectiveRealizationGeometry r) := by
  sorry

/-- A nonempty affine complement in a proper smooth generic fibre produces a
nonzero divisor line-bundle class. -/
theorem affine_complement_line_bundle_nontrivial
    {X : GeneralSmoothQuarticSurface ℂ} {D : ComplexQuarticK3Data X}
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r)
    (hsep : IsSeparatedTotalSpace G)
    (haff : HasAffineOpenTotalSpace G)
    (hsmooth : IsSmoothTotalSpace G)
    (hregular : IsRegularTotalSpace G)
    (hcartier : ComplementIsEffectiveCartier G)
    (hgeneric : GenericFibreIsProperSmooth G) :
    complementLineBundleClass G ≠ 0 := by
  sorry

/-- The restriction map from the Picard group of an algebraization to that of
the special fibre. The last field records that a line bundle on the total
space lifts along every first-order direction of the universal deformation. -/
structure PicardRestrictionData {X : GeneralSmoothQuarticSurface ℂ}
    (D : ComplexQuarticK3Data X)
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r) where
  restriction : (G.picardGroup : Type) →+ (X.picardGroup : Type)
  injective : Function.Injective restriction
  restriction_lifts : ∀ (c : (G.picardGroup : Type))
    (v : (D.tangentCohomology 1 : Type)),
      D.liftsToFirstOrder (restriction c) v

theorem picard_restriction_injective_of_h1_zero
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r)
    (hH1 : Module.finrank ℂ (D.h1_structureSheaf : Type) = 0)
    (hGE : GrothendieckExistenceForPicard G) :
    Nonempty (PicardRestrictionData D G) := by
  sorry

/-- The cup product with the first Chern class at a first-order deformation. -/
def CupProductAt {X : GeneralSmoothQuarticSurface ℂ}
    (D : ComplexQuarticK3Data X) (c : (X.picardGroup : Type))
    (v : (D.tangentCohomology 1 : Type)) :
    (D.h2_structureSheaf : Type) :=
  D.cupProduct (TensorProduct.tmul ℂ (D.firstChern c) v)

/-- A line bundle class does not lift along the specified first-order
deformation. -/
def NoFirstOrderLineBundleLift {X : GeneralSmoothQuarticSurface ℂ}
    (D : ComplexQuarticK3Data X) (c : (X.picardGroup : Type))
    (v : (D.tangentCohomology 1 : Type)) : Prop :=
  ¬ D.liftsToFirstOrder c v

theorem exists_first_order_deformation_with_nonzero_cup_product
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    (c : (X.picardGroup : Type)) (hc : D.firstChern c ≠ 0) :
    ∃ v : (D.tangentCohomology 1 : Type), CupProductAt D c v ≠ 0 := by
  sorry

theorem line_bundle_lifts_iff_cup_product_eq_zero
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    (c : (X.picardGroup : Type)) (v : (D.tangentCohomology 1 : Type)) :
    D.liftsToFirstOrder c v ↔ CupProductAt D c v = 0 := by
  sorry

/-- Inverse line bundles preserve the first-order lifting predicate. -/
theorem line_bundle_lift_neg
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    (c : (X.picardGroup : Type)) (v : (D.tangentCohomology 1 : Type)) :
    D.liftsToFirstOrder c v ↔ D.liftsToFirstOrder (-c) v := by
  sorry

theorem positive_twist_has_no_first_order_lift
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    {n : ℕ} (hn : 0 < n) :
    ∃ v : (D.tangentCohomology 1 : Type),
      NoFirstOrderLineBundleLift D (twist X n) v := by
  sorry

theorem effective_picard_group_is_trivial
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    {ξ : ProperFormalObject X.surface} {r : EffectiveRealization ξ}
    (G : EffectiveRealizationGeometry r)
    (ρ : PicardRestrictionData D G)
    (hNoLift : ∀ n : ℕ, 0 < n →
      ∃ v : (D.tangentCohomology 1 : Type),
        NoFirstOrderLineBundleLift D (twist X n) v) :
    Subsingleton (G.picardGroup : Type) := by
  sorry

/-! ## Non-effectivity and the chapter theorem -/

theorem universal_k3_deformation_not_effective
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    (𝒟 : UniversalK3Deformation D) :
    ¬ IsEffectiveFormalObject 𝒟.formalObject := by
  intro hξ
  obtain ⟨r⟩ := hξ
  obtain ⟨G⟩ := effective_universal_deformation_has_geometry D 𝒟 r
  obtain ⟨ρ⟩ := picard_restriction_injective_of_h1_zero D G
    D.h1_structureSheaf_dimension
      (show GrothendieckExistenceForPicard G from
        G.grothendieck_existence_holds)
  have hNoLift : ∀ n : ℕ, 0 < n →
      ∃ v : (D.tangentCohomology 1 : Type),
        NoFirstOrderLineBundleLift D (twist X n) v := by
    intro n hn
    exact positive_twist_has_no_first_order_lift D hn
  have htrivial : Subsingleton (G.picardGroup : Type) :=
    effective_picard_group_is_trivial D G ρ hNoLift
  have hnonzero := affine_complement_line_bundle_nontrivial (D := D) G
    (show IsSeparatedTotalSpace G from G.separated_holds)
    (show HasAffineOpenTotalSpace G from G.affineOpen_holds)
    (show IsSmoothTotalSpace G from G.smooth_holds)
    (show IsRegularTotalSpace G from G.regular_holds)
    (show ComplementIsEffectiveCartier G from
      G.complement_effective_cartier_holds)
    (show GenericFibreIsProperSmooth G from
      G.generic_fibre_proper_smooth_holds)
  exact hnonzero (htrivial.allEq _ _)

/-- The stack of finitely presented flat proper algebraic spaces is not an
algebraic stack. Algebraicity would force formal effectiveness by Artin's
axioms, while the universal quartic K3 deformation is not effective. -/
theorem proper_algebraic_space_stack_not_algebraic :
    ¬ IsAlgebraicStack properAlgebraicSpaceStack := by
  intro hAlgebraic
  obtain ⟨X⟩ := exists_general_smooth_quartic_surface_over_complex
  obtain ⟨D⟩ := complex_quartic_k3_data_exists X
  obtain ⟨𝒟⟩ := universal_k3_deformation_exists D
  exact universal_k3_deformation_not_effective D 𝒟
    (hAlgebraic.formal_effective X 𝒟.formalObject)

end Formalization.Books.Examples.Unit73
