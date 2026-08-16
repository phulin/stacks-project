import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPowerSeries.Basic
import Formalization.«Books.SpacesGroupoids».Unit20.Core

/-!
# Examples, Chapter 73: the stack of proper algebraic spaces is not algebraic

The project has a canonical fppf-sheaf model for algebraic spaces over a fixed
scheme, but it does not yet expose the full big stack of algebraic spaces or
the deformation theory of K3 surfaces.  This file therefore uses those
canonical sheaf and categorical objects wherever they are available and gives
explicit source-facing interfaces for the missing deformation, cohomology,
Picard, and formal-effectiveness constructions.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Formalization.«Books.Examples».Unit73

/-! ## The stack of finitely presented flat proper algebraic spaces -/

/-- The objects in the fibre over `S` of the stack from the source. -/
structure FlatProperFinitelyPresentedAlgebraicSpace (S : Scheme.{u}) where
  /-- The fppf sheaf of points of the algebraic space. -/
  space : Formalization.«Books.SpacesGroupoids».Unit20.AlgebraicSpace S
  /-- The assertion that the structure morphism is flat. -/
  flat : Prop
  /-- The assertion that the structure morphism is proper. -/
  proper : Prop
  /-- The assertion that the structure morphism is finitely presented. -/
  finitelyPresented : Prop

namespace FlatProperFinitelyPresentedAlgebraicSpace

/-- A morphism in the fibre category over `S`. -/
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

/-- The category of flat, proper, finitely presented algebraic spaces over `S`.

The underlying sheaf and its morphisms use the fppf-sheaf model from the
earlier algebraic-spaces chapter; the three geometric properties remain the
source-facing predicates carried by each object. -/
abbrev ProperAlgebraicSpaceSectionCategory (S : Scheme.{u}) :=
  FlatProperFinitelyPresentedAlgebraicSpace S

/-- The section family of the stack `p'_{fp, flat, proper}`. -/
abbrev properAlgebraicSpaceStackSections (S : Scheme.{u}) :=
  ProperAlgebraicSpaceSectionCategory S

/-- The stack's fppf-sheaf model of algebraic spaces over a fixed base. -/
def properAlgebraicSpaceStack (S : Scheme.{u}) : Type _ :=
  properAlgebraicSpaceStackSections S

/-- The missing big pseudofunctor interface for the stack in groupoids from the
source.  Its fibre equivalences tie the pseudofunctor to the explicit section
categories above, while the stack field records the fppf descent assertion. -/
structure ProperAlgebraicSpaceStackData where
  fibre : Formalization.«Books.Stacks».Unit01.FiberedCategory.{u, u, u + 1}
    AlgebraicGeometry.Scheme
  fibre_equivalence : ∀ S : Scheme.{u}, Nonempty
    (Formalization.«Books.Stacks».Unit01.Fiber fibre S ≌
      ProperAlgebraicSpaceSectionCategory S)
  is_fppf_stack : Formalization.«Books.SpacesGroupoids».Unit20.StackInGroupoids
    fibre AlgebraicGeometry.Scheme.fppfTopology

/-- The source stack exists with the stated fppf-stack structure. -/
def ProperAlgebraicSpaceStackIsFppfStack : Prop :=
  Nonempty (ProperAlgebraicSpaceStackData.{u})

theorem proper_algebraic_space_stack_is_fppf_stack :
    ProperAlgebraicSpaceStackIsFppfStack := by
  sorry

/-! ## The numerical deformation setup -/

/-- The formal parameter count `g²` for a dimension-`g` abelian variety. -/
def abelianVarietyFormalParameterCount (g : ℕ) : ℕ := g ^ 2

/-- The dimension bound `g(g + 1)/2` for an effective formal deformation. -/
def effectiveFormalDeformationDimensionBound (g : ℕ) : ℕ := g * (g + 1) / 2

theorem abelianVarietyFormalParameterCount_exceeds_effectiveBound
    {g : ℕ} (hg : 2 ≤ g) :
    effectiveFormalDeformationDimensionBound g <
      abelianVarietyFormalParameterCount g := by
  sorry

/-- Mathlib's projective spectrum model of `\mathbf P^3_k`. -/
noncomputable def projectiveThreeSpace (k : Type u) [Field k] : Scheme.{u} :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin 4) (R := k)
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)

/-- A smooth degree-four surface embedded in projective three-space. -/
structure SmoothQuarticSurface (k : Type u) [Field k] where
  surface : Scheme.{u}
  ambient : Scheme.{u}
  ambient_identification : Nonempty (ambient ≅ projectiveThreeSpace k)
  embedding : surface ⟶ ambient
  embedding_is_closed : AlgebraicGeometry.IsClosedImmersion embedding
  structureMap : surface ⟶ Spec (CommRingCat.of k)
  smooth_over_k : AlgebraicGeometry.Smooth structureMap
  degree : ℕ
  degree_eq_four : degree = 4

/-! The generic Picard-rank-one hypothesis used later in the argument. -/

/-- A smooth quartic surface satisfying the source's ``general enough''
Picard-group condition.  The Picard group is represented by the project
Picard-group object interface because Mathlib has no scheme Picard functor. -/
structure GeneralSmoothQuarticSurface (k : Type u) [Field k]
    extends SmoothQuarticSurface k where
  picardGroup : AddCommGrpCat.{0}
  picard_is_integer : Nonempty ((picardGroup : Type) ≃+ ℤ)

/-! ## Cohomology and Picard interfaces for the complex quartic K3 -/

/-- Nondegeneracy of a bilinear pairing represented by a linear map on a
tensor product. -/
def IsNondegeneratePairing {k M N P : Type*} [Field k]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module k M] [Module k N] [Module k P]
    (pairing : M ⊗[k] N →ₗ[k] P) : Prop :=
  (∀ m : M, (∀ n : N, pairing (TensorProduct.tmul k m n) = 0) → m = 0) ∧
    (∀ n : N, (∀ m : M, pairing (TensorProduct.tmul k m n) = 0) → n = 0)

/-- The cohomological and Picard data used by the K3 obstruction argument.

The sheaves are genuine objects of Mathlib's scheme-module category.  The
cohomology groups, Ext groups, cup product, and Picard group are the explicit
interfaces required by this source section. -/
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
  firstChern_injective : Function.Injective firstChern
  twist : ℕ → (X.picardGroup : Type)
  twist_c1_nonzero : ∀ n : ℕ, 0 < n → firstChern (twist n) ≠ 0
  liftsToFirstOrder :
    ∀ _ : (X.picardGroup : Type), (tangentCohomology 1 : Type) → Prop

abbrev tangentCohomologyGroup (D : ComplexQuarticK3Data X) (i : ℕ) :=
  D.tangentCohomology i

abbrev extCohomologyGroup (D : ComplexQuarticK3Data X) (i : ℕ) :=
  D.extCohomology i

theorem complex_quartic_k3_data_exists (X : GeneralSmoothQuarticSurface ℂ) :
    Nonempty (ComplexQuarticK3Data X) := by
  sorry

theorem exists_general_smooth_quartic_surface_over_complex :
    Nonempty (GeneralSmoothQuarticSurface ℂ) := by
  sorry

/-! ## The universal formal deformation -/

/-- The complete local ring `\mathbf C[[x₁, ..., x₂₀]]`. -/
abbrev ComplexFormalDeformationRing := MvPowerSeries (Fin 20) ℂ

/-- The ideal generated by the twenty formal parameters. -/
def complexFormalDeformationIdeal : Ideal ComplexFormalDeformationRing :=
  Ideal.span (Set.range (fun i : Fin 20 => MvPowerSeries.X i))

/-- The base `\operatorname{Spec}(\mathbf C[[x₁, ..., x₂₀]])`. -/
noncomputable def complexFormalDeformationBase : Scheme :=
  Spec (CommRingCat.of ComplexFormalDeformationRing)

/-- The ring of the `(n + 1)`st infinitesimal neighbourhood of the closed
point of the formal deformation base. -/
abbrev complexFormalDeformationLevelRing (n : ℕ) :=
  ComplexFormalDeformationRing ⧸ complexFormalDeformationIdeal ^ (n + 1)

/-- The corresponding infinitesimal neighbourhood. -/
noncomputable def complexFormalDeformationLevel (n : ℕ) : Scheme :=
  Spec (CommRingCat.of (complexFormalDeformationLevelRing n))

/-- A compatible formal object of the proper-algebraic-space stack with
special fibre `X`. -/
structure ProperFormalObject (X : Scheme) where
  level : ∀ n : ℕ,
    FlatProperFinitelyPresentedAlgebraicSpace (complexFormalDeformationLevel n)
  compatible : Prop
  special_fibre_is_X : Prop

/-- An algebraization of a formal object.  The comparison fields express that
the algebraic family recovers every infinitesimal level. -/
structure EffectiveRealization {X : Scheme} (ξ : ProperFormalObject X) where
  totalSpace :
    FlatProperFinitelyPresentedAlgebraicSpace complexFormalDeformationBase
  inducedLevel : ∀ n : ℕ,
    FlatProperFinitelyPresentedAlgebraicSpace (complexFormalDeformationLevel n)
  comparison : ∀ n : ℕ, Nonempty (inducedLevel n ≅ ξ.level n)
  separated : Prop
  affineOpen : Prop
  special_fibre_smooth : Prop
  smooth : Prop
  regular : Prop
  complement_effective_cartier : Prop
  generic_fibre_proper_smooth : Prop
  grothendieck_existence : Prop
  picardGroup : AddCommGrpCat.{0}
  complementDivisorClass : (picardGroup : Type)

/-- Formal effectiveness for the stack in this chapter. -/
def IsEffectiveFormalObject {X : Scheme} (ξ : ProperFormalObject X) : Prop :=
  Nonempty (EffectiveRealization ξ)

/-- The Artin-axiom necessary condition used to test algebraicity here. -/
def IsAlgebraicStack : Prop :=
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

def IsSeparatedTotalSpace {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ) : Prop :=
  r.separated

def HasAffineOpenTotalSpace {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ) : Prop :=
  r.affineOpen

def IsSmoothTotalSpace {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ) : Prop :=
  r.smooth

def IsRegularTotalSpace {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ) : Prop :=
  r.regular

def ComplementIsEffectiveCartier {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ) : Prop :=
  r.complement_effective_cartier

def GenericFibreIsProperSmooth {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ) : Prop :=
  r.generic_fibre_proper_smooth

def GrothendieckExistenceForPicard {X : GeneralSmoothQuarticSurface ℂ}
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ) : Prop :=
  r.grothendieck_existence

theorem effective_universal_deformation_has_geometry
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    (𝒟 : UniversalK3Deformation D)
    (r : EffectiveRealization 𝒟.formalObject) :
    IsSeparatedTotalSpace r ∧
      HasAffineOpenTotalSpace r ∧
      IsSmoothTotalSpace r ∧
      IsRegularTotalSpace r ∧
      ComplementIsEffectiveCartier r ∧
      GenericFibreIsProperSmooth r ∧
      GrothendieckExistenceForPicard r := by
  sorry

def PicardGroupTrivial (P : AddCommGrpCat.{0}) : Prop :=
  Subsingleton (P : Type)

theorem affine_complement_line_bundle_nontrivial
    {X : GeneralSmoothQuarticSurface ℂ} {D : ComplexQuarticK3Data X}
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ)
    (hsep : IsSeparatedTotalSpace r)
    (haff : HasAffineOpenTotalSpace r)
    (hsmooth : IsSmoothTotalSpace r)
    (hregular : IsRegularTotalSpace r)
    (hcartier : ComplementIsEffectiveCartier r)
    (hgeneric : GenericFibreIsProperSmooth r) :
    r.complementDivisorClass ≠ 0 := by
  sorry

/-- The restriction map from the Picard group of an algebraization to that of
the special fibre. -/
structure PicardRestrictionData {X : GeneralSmoothQuarticSurface ℂ}
    (D : ComplexQuarticK3Data X)
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ) where
  restriction : (r.picardGroup : Type) →+ (X.picardGroup : Type)
  injective : Function.Injective restriction

theorem picard_restriction_injective_of_h1_zero
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ)
    (hH1 : Module.finrank ℂ (D.h1_structureSheaf : Type) = 0)
    (hGE : GrothendieckExistenceForPicard r) :
    Nonempty (PicardRestrictionData D r) := by
  sorry

def CupProductAt {X : GeneralSmoothQuarticSurface ℂ}
    (D : ComplexQuarticK3Data X) (c : (X.picardGroup : Type))
    (v : (D.tangentCohomology 1 : Type)) :
    (D.h2_structureSheaf : Type) :=
  D.cupProduct (TensorProduct.tmul ℂ (D.firstChern c) v)

def NoFirstOrderLineBundleLift {X : GeneralSmoothQuarticSurface ℂ}
    (D : ComplexQuarticK3Data X) (c : (X.picardGroup : Type)) : Prop :=
  ∀ v : (D.tangentCohomology 1 : Type), ¬ D.liftsToFirstOrder c v

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

theorem positive_twist_has_no_first_order_lift
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    {n : ℕ} (hn : 0 < n) :
    NoFirstOrderLineBundleLift D (D.twist n) := by
  sorry

theorem effective_picard_group_is_trivial
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    {ξ : ProperFormalObject X.surface} (r : EffectiveRealization ξ)
    (ρ : PicardRestrictionData D r)
    (hNoLift : ∀ n : ℕ, 0 < n → NoFirstOrderLineBundleLift D (D.twist n)) :
    PicardGroupTrivial r.picardGroup := by
  sorry

/-! ## Non-effectivity and the chapter theorem -/

theorem universal_k3_deformation_not_effective
    {X : GeneralSmoothQuarticSurface ℂ} (D : ComplexQuarticK3Data X)
    (𝒟 : UniversalK3Deformation D) :
    ¬ IsEffectiveFormalObject 𝒟.formalObject := by
  sorry

/-- The stack of finitely presented flat proper algebraic spaces is not an
algebraic stack.  Algebraicity is tested by the formal-effectiveness
condition supplied by Artin's axioms. -/
theorem proper_algebraic_space_stack_not_algebraic :
    ¬ IsAlgebraicStack := by
  intro hAlgebraic
  obtain ⟨X⟩ := exists_general_smooth_quartic_surface_over_complex
  obtain ⟨D⟩ := complex_quartic_k3_data_exists X
  obtain ⟨𝒟⟩ := universal_k3_deformation_exists D
  exact universal_k3_deformation_not_effective D 𝒟
    (hAlgebraic X 𝒟.formalObject)

end Formalization.«Books.Examples».Unit73
