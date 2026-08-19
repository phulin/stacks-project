import Formalization.Books.Descent.Unit19.VariantsOnDescendingProperties

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Formalization.Books.Descent.Unit19

/-! ## Properties local in the fppf topology on the target -/

theorem immersion_isFppfLocalOnTarget :
    IsFppfLocalOnTarget (@IsImmersion) := by sorry

theorem dominant_isFppfLocalOnTarget :
    IsFppfLocalOnTarget (@IsDominant) := by sorry

/-! ## Applications of fpqc descent -/

theorem flat_quasiCompact_surjective_mono_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f]
    [Surjective f] [Mono f] : IsIso f := by
  sorry

theorem universallyInjective_etale_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyInjective f] [Etale f] :
    IsOpenImmersion f := by
  sorry

def GenericPointOfComponent {X : Scheme.{u}} (ξ : X) : Prop :=
  ∃ C : Set X, IsClosed C ∧ IsIrreducible C ∧ C = closure ({ξ} : Set X)

def ResidueFieldEqualAt {X Y : Scheme.{u}} (f : X ⟶ Y) (ξ : X) : Prop :=
  Nonempty (Y.residueField (f ξ) ≃+* X.residueField ξ)

def DistinctImagesOfGenericPoints {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ {ξ ξ' : X}, GenericPointOfComponent ξ → GenericPointOfComponent ξ' →
    ξ ≠ ξ' → f ξ ≠ f ξ'

theorem flat_separated_generic_residue_fields_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsSeparated f]
    (hres : ∀ {ξ : X}, GenericPointOfComponent ξ → ResidueFieldEqualAt f ξ)
    (hdist : DistinctImagesOfGenericPoints f) : UniversallyInjective f := by
  sorry

theorem etale_separated_generic_residue_fields_openImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    (hres : ∀ {ξ : X}, GenericPointOfComponent ξ → ResidueFieldEqualAt f ξ)
    (hdist : DistinctImagesOfGenericPoints f) : IsOpenImmersion f := by
  sorry

/-! Properness of a closed subset over the base.  Mathlib has the morphism
predicate, but not the source's reduced-induced closed-subscheme wrapper. -/

structure ClosedSubset (X : Scheme.{u}) where
  carrier : Set X
  isClosed : IsClosed carrier

def IsProperOver {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : ClosedSubset X) : Prop :=
  ∃ (W : Scheme.{u}) (i : W ⟶ X), IsClosedImmersion i ∧
    Set.range i = Z.carrier ∧ IsProper (i ≫ f)

theorem proper_closed_subset_of_fpqc_local_proper
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : LocallyOfFiniteType f)
    (Z : ClosedSubset X)
    (hcover : ∀ (𝒰 : Cover .fpqc Y) (i : 𝒰.I₀),
      IsProperOver (baseChangeTo f (𝒰.f i))
        ⟨(baseChangeFrom f (𝒰.f i)) ⁻¹' Z.carrier, by sorry⟩) :
    IsProperOver f Z := by
  sorry

/-! Relative ampleness -/

structure RelativeInvertibleModule (X : Scheme.{u}) where
  invertible : Prop
  ampleOver : ∀ {Y : Scheme.{u}} (_f : X ⟶ Y), Prop

def PullbackInvertibleModule {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (L : RelativeInvertibleModule X) :
  RelativeInvertibleModule (baseChange f g) where
  invertible := L.invertible
  ampleOver := fun _ => L.ampleOver f

theorem relativeAmple_isFpqcLocal
    {X S : Scheme.{u}} (f : X ⟶ S) (L : RelativeInvertibleModule X)
    (𝒰 : Cover .fpqc S) :
    L.ampleOver f ↔
      ∀ i, (PullbackInvertibleModule f (𝒰.f i) L).ampleOver
        (baseChangeTo f (𝒰.f i)) := by
  sorry

end Formalization.Books.Descent.Unit19
