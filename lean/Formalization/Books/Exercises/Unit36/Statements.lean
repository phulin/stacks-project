import Formalization.Books.Exercises.Unit36.Core

/-!
# Exercises, Chapter 36: Quasi-coherent Sheaves

The declarations follow the source order.  Proposition-valued exercises are
statement interfaces and are intentionally left for the proving stage.
-/

namespace Formalization.Books.Exercises.Unit36

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

/-! ## Definition `definition-quasi-coherent` and its affine-cover remark -/

/-- Quasi-coherence is Mathlib's canonical `M.IsQuasicoherent` predicate on
sheaves of modules; `QuasiCoherentModules X` is its full subcategory. -/
theorem quasi_coherent_module_mem_subcategory_iff {X : Scheme.{u}}
    (M : X.Modules) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) M ↔ M.IsQuasicoherent := by
  rfl

/-- Quasi-coherence can be checked on an affine open covering. -/
theorem isQuasicoherent_iff_of_affine_openCover
    {X : Scheme.{u}} (𝒰 : Scheme.OpenCover X)
    [∀ i, IsAffine (𝒰.X i)] (M : X.Modules) :
    M.IsQuasicoherent ↔
      ∀ i : 𝒰.I₀,
        ((Scheme.Modules.restrictFunctor (𝒰.f i)).obj M).IsQuasicoherent := by
  sorry

/-! ## Definition `definition-specialization` and the two specialization exercises -/

/-- The source definition of specialization is represented by the canonical
closure relation. -/
theorem isSpecialization_iff_mem_closure {X : Type u} [TopologicalSpace X]
    {x x' : X} :
    IsSpecialization x x' ↔ x ∈ closure ({x'} : Set X) := by
  rfl

/-- A quasi-coherent module with a nonzero stalk stays nonzero at every
specialization. -/
theorem quasi_coherent_stalk_nontrivial_of_specialization
    {X : Scheme.{u}} (M : X.Modules) (hM : M.IsQuasicoherent)
    {x x' : X} (hxx' : IsSpecialization x x')
    (hx' : Nontrivial (M.presheaf.stalk x')) :
    Nontrivial (M.presheaf.stalk x) := by
  sorry

/-- There is a sheaf of `𝒪_X`-modules for which nontriviality is lost under
specialization; no quasi-coherence hypothesis is imposed. -/
theorem exists_module_stalk_nontrivial_specialization_zero :
    ∃ (X : Scheme.{u}) (x x' : X) (M : X.Modules),
      IsSpecialization x x' ∧
        Nontrivial (M.presheaf.stalk x') ∧
        ¬ Nontrivial (M.presheaf.stalk x) := by
  sorry

/-! ## Definitions `definition-Noetherian-scheme` and `definition-coherent` -/

/-- Every affine open of a locally Noetherian scheme has Noetherian global
sections. -/
theorem affine_open_isNoetherianRing_of_isLocallyNoetherian
    (X : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsNoetherianRing Γ(X, U) :=
  AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨U, hU⟩

/-- Equivalently, every affine open of a locally Noetherian scheme is the
spectrum of a Noetherian ring. -/
theorem affine_open_is_spectrum_of_isLocallyNoetherian
    (X : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ R : CommRingCat.{u}, IsNoetherianRing R ∧
      Nonempty (U.toScheme ≅ Scheme.Spec.obj (Opposite.op R)) := by
  sorry

/-- Mathlib's `IsNoetherian` is exactly the conjunction of local
Noetherianity and compactness used by the source. -/
theorem isNoetherian_iff_isLocallyNoetherian_and_compactSpace
    (X : Scheme.{u}) :
    AlgebraicGeometry.IsNoetherian X ↔
      AlgebraicGeometry.IsLocallyNoetherian X ∧ CompactSpace X := by
  sorry

/-- The source's coherent sheaf definition is the canonical conjunction of
quasi-coherence and finite type on a locally Noetherian scheme. -/
theorem isCoherent_iff_quasiCoherent_and_finiteType
    {X : Scheme.{u}}
    (M : X.Modules) :
    IsCoherent M ↔ M.IsQuasicoherent ∧ M.IsFiniteType := by
  rfl

/-! ## Exercise `exercise-extend-quasi-coherent` -/

/-- The quotient map used for the closed-subscheme exercise is a closed
immersion. -/
theorem quotientClosedImmersion_isClosedImmersion
    (R : Type u) [CommRing R] (I : Ideal R) :
    AlgebraicGeometry.IsClosedImmersion (quotientClosedImmersion R I) := by
  sorry

/-- A quasi-coherent module on `D(f)` extends to a quasi-coherent module on
`Spec(R)`. -/
theorem exists_quasiCoherent_extension_basicOpen
    (R : Type u) [CommRing R] (f : R)
    (G : (basicOpenScheme R f).Modules) (hG : G.IsQuasicoherent) :
    ∃ F : (affineSpec R).Modules,
      F.IsQuasicoherent ∧
        IsRestrictionOf (basicOpenInclusion R f) G F := by
  sorry

/-- A quasi-coherent module on the affine closed subscheme cut out by `I`
extends as the pullback of a quasi-coherent module on the ambient affine
scheme. -/
theorem exists_quasiCoherent_extension_quotientClosedSubscheme
    (R : Type u) [CommRing R] (I : Ideal R)
    (G : (quotientClosedSubscheme R I).Modules) (hG : G.IsQuasicoherent) :
    ∃ F : (affineSpec R).Modules,
      F.IsQuasicoherent ∧
        IsRestrictionOf (quotientClosedImmersion R I) G F := by
  sorry

/-- Over a Noetherian affine scheme, a coherent module on `D(f)` extends to a
coherent module on the whole scheme. -/
theorem exists_coherent_extension_basicOpen
    (R : Type u) [CommRing R] [IsNoetherianRing R] (f : R)
    (G : (basicOpenScheme R f).Modules)
    (hG : IsCoherent G) :
    ∃ F : (affineSpec R).Modules,
      IsCoherent F ∧ IsRestrictionOf (basicOpenInclusion R f) G F := by
  sorry

/-! ## Remark `remark-extend-off-open` -/

/-- A quasi-coherent module on a quasi-compact immersion extends to the
ambient scheme. -/
theorem exists_quasiCoherent_extension_of_quasiCompact_immersion
    {U X : Scheme.{u}} (i : U ⟶ X)
    [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.QuasiCompact i]
    (G : U.Modules) (hG : G.IsQuasicoherent) :
    ∃ F : X.Modules, F.IsQuasicoherent ∧ IsRestrictionOf i G F := by
  sorry

/-- On a Noetherian scheme, a coherent module on an open subscheme extends to
a coherent module on the ambient scheme. -/
theorem exists_coherent_extension_of_open_immersion
    {U X : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    (i : U ⟶ X) [AlgebraicGeometry.IsOpenImmersion i]
    (G : U.Modules) (hG : IsCoherent G) :
    ∃ F : X.Modules, IsCoherent F ∧ IsRestrictionOf i G F := by
  sorry

end

end Formalization.Books.Exercises.Unit36
