import Formalization.Books.Descent.Unit19.Core

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Formalization.Books.Descent.Unit19

/-! ## Germs of schemes -/

/-- Étaleness of a chosen representative of a germ morphism. -/
def germMorphismIsEtale {X Y : SchemeGerm.{u}} (f : SchemeGerm.Hom X Y) : Prop :=
  Etale f.map

/-- Smoothness of a chosen representative of a germ morphism. -/
def germMorphismIsSmooth {X Y : SchemeGerm.{u}} (f : SchemeGerm.Hom X Y) : Prop :=
  Smooth f.map

theorem germMorphismIsEtale_iff {X Y : SchemeGerm.{u}}
    (f : SchemeGerm.Hom X Y) : germMorphismIsEtale f ↔ Etale f.map := Iff.rfl

theorem germMorphismIsSmooth_iff {X Y : SchemeGerm.{u}}
    (f : SchemeGerm.Hom X Y) : germMorphismIsSmooth f ↔ Smooth f.map := Iff.rfl

/-! ## Local properties of germs -/

abbrev GermObjectProperty := ∀ _X : SchemeGerm.{u}, Prop

def IsEtaleLocalObjectProperty (Q : GermObjectProperty) : Prop :=
  ∀ {X Y : SchemeGerm.{u}} (f : SchemeGerm.Hom X Y),
    germMorphismIsEtale f → (Q X ↔ Q Y)

def IsSmoothLocalObjectProperty (Q : GermObjectProperty) : Prop :=
  ∀ {X Y : SchemeGerm.{u}} (f : SchemeGerm.Hom X Y),
    germMorphismIsSmooth f → (Q X ↔ Q Y)

theorem dimension_at_point_is_etale_local
    {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U) :
    Order.coheight u = Order.coheight (f u) := by
  sorry

theorem local_ring_dimension_is_etale_local
    {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U) :
    ringKrullDim (U.presheaf.stalk u) =
      ringKrullDim (V.presheaf.stalk (f u)) := by
  sorry

theorem regular_local_ring_is_etale_local
    {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U) :
    (IsRegularLocalRing (U.presheaf.stalk u) ↔
      IsRegularLocalRing (V.presheaf.stalk (f u))) := by
  sorry

theorem dimension_at_point_property_is_etale_local :
    IsEtaleLocalObjectProperty (fun X =>
      ∃ d : ℕ∞, X.pointDimension = d) := by
  sorry

theorem local_ring_dimension_property_is_etale_local :
    IsEtaleLocalObjectProperty (fun X =>
      ∃ d : WithBot ℕ∞, X.localRingDimension = d) := by
  sorry

theorem regular_local_ring_property_is_etale_local :
    IsEtaleLocalObjectProperty SchemeGerm.IsRegularLocalRingAtGerm := by
  sorry

/-! ## Properties local on the target -/

def IsFlatLocalOnTarget (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnTarget .fpqc P

def IsFppfLocalOnTarget (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnTarget .fppf P

def IsEtaleLocalOnTarget (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnTarget .etale P

def IsSmoothLocalOnTarget (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnTarget .smooth P

def IsSyntomicLocalOnTarget (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnTarget .syntomic P

def IsZariskiLocalOnTarget (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnTarget .zariski P

theorem pullback_property_local_on_target
    (τ : Topology) (P : SchemeMorphismProperty)
    (hP : IsLocalOnTarget τ P) {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hf : P f)
    (hg : coveringMorphismProperty τ g) : P (baseChangeTo f g) := by
  sorry

theorem property_local_on_target_of_open_restriction
    (τ : Topology) (P : SchemeMorphismProperty)
    (hP : IsLocalOnTarget τ P) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hf : P f) (hsub : Set.range f ⊆ (V : Set Y)) :
    P (f ∣_ V) := by
  sorry

/-- The largest target open on which a local property holds. -/
noncomputable def largestOpenOfTarget
    (τ : Topology) (P : SchemeMorphismProperty)
    (_hP : IsLocalOnTarget τ P) {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Opens :=
  sSup {W : Y.Opens | P (f ∣_ W)}

theorem largestOpenOfTarget_is_largest
    (τ : Topology) (P : SchemeMorphismProperty)
    (hP : IsLocalOnTarget τ P) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P (f ∣_ largestOpenOfTarget τ P hP f) ∧
      ∀ W : Y.Opens, P (f ∣_ W) → W ≤ largestOpenOfTarget τ P hP f := by
  sorry

theorem largestOpenOfTarget_image_subset
    (τ : Topology) (P : SchemeMorphismProperty)
    (hP : IsLocalOnTarget τ P) {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hg : coveringMorphismProperty τ g)
    (hbase : P (baseChangeTo f g)) :
    Set.range g ⊆ (largestOpenOfTarget τ P hP f : Set Y) := by
  sorry

theorem largestOpenOfTarget_baseChange
    (τ : Topology) (P : SchemeMorphismProperty)
    (hP : IsLocalOnTarget τ P) {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hg : coveringMorphismProperty τ g) :
    largestOpenOfTarget τ P hP (baseChangeTo f g) =
      g ⁻¹ᵁ largestOpenOfTarget τ P hP f := by
  sorry

theorem largestOpenOfTarget_cover_member
    (τ : Topology) (P : SchemeMorphismProperty)
    (hP : IsLocalOnTarget τ P) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Cover τ Y) (i : 𝒰.I₀) :
    largestOpenOfTarget τ P hP (baseChangeTo f (𝒰.f i)) =
      (𝒰.f i) ⁻¹ᵁ largestOpenOfTarget τ P hP f := by
  sorry

theorem local_on_target_of_affine_criterion
    (τ : Topology) (P : SchemeMorphismProperty)
    (hbase : PreservedByBaseChange (coveringMorphismProperty τ) P)
    (hzariski : IsZariskiLocalOnTarget P)
    (haffine : AffineDescent P τ) : IsLocalOnTarget τ P := by
  exact isLocalOnTarget_of_affine_criterion τ P hbase hzariski haffine

def StandardTargetCoveringMorphism (τ : Topology) : SchemeMorphismProperty :=
  coveringMorphismProperty τ

theorem affine_target_descent_standard_cover
    (P : SchemeMorphismProperty) (τ : Topology) :
    AffineDescent P τ ↔
      ∀ {X' X Y : Scheme.{u}} (a : X' ⟶ X) (f : X ⟶ Y),
        IsAffine X' → IsAffine X → Surjective a →
        StandardTargetCoveringMorphism τ a → P (a ≫ f) → P f := by sorry

/-! ## The source's standard specializations -/

theorem quasiCompact_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@QuasiCompact) := by sorry

theorem quasiSeparated_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@QuasiSeparated) := by sorry

theorem universallyClosed_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@UniversallyClosed) := by sorry

theorem universallyOpen_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@UniversallyOpen) := by sorry

theorem universallySubmersive_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (topologically IsQuotientMap) := by sorry

theorem separated_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsSeparated) := by sorry

theorem surjective_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@Surjective) := by sorry

theorem dominant_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (fun _ _ f => QuasiCompact f ∧ IsDominant f) := by sorry

noncomputable def specMapOfFieldExtension
    {k E : Type u} [Field k] [Field E] [Algebra k E] :
    Spec (.of E) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k E))

noncomputable def baseChangeOfMorphism
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X ⟶ Spec (.of k)) (y : Y ⟶ Spec (.of k))
    (comm : f ≫ y = x) :
    pullback x (specMapOfFieldExtension (k := k) (E := E)) ⟶
      pullback y (specMapOfFieldExtension (k := k) (E := E)) :=
  pullback.lift
    (pullback.fst x (specMapOfFieldExtension (k := k) (E := E)) ≫ f)
    (pullback.snd x (specMapOfFieldExtension (k := k) (E := E)))
    (by
      rw [Category.assoc, comm, pullback.condition])

theorem dominant_over_field_is_baseChange_invariant
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X ⟶ Spec (.of k)) (y : Y ⟶ Spec (.of k))
    (comm : f ≫ y = x) :
    IsDominant f ↔ IsDominant (baseChangeOfMorphism (k := k) (E := E) f x y comm) := by
  sorry

theorem universallyInjective_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@UniversallyInjective) := by sorry

theorem universalHomeomorphism_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (fun _ _ f =>
      UniversallyClosed f ∧ UniversallyOpen f ∧ UniversallyInjective f ∧ Surjective f) := by sorry

theorem locallyOfFiniteType_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@LocallyOfFiniteType) := by sorry

theorem locallyOfFinitePresentation_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@LocallyOfFinitePresentation) := by sorry

theorem finiteType_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (fun _ _ f => QuasiCompact f ∧ LocallyOfFiniteType f) := by sorry

theorem finitePresentation_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (fun _ _ f =>
      QuasiCompact f ∧ QuasiSeparated f ∧ LocallyOfFinitePresentation f) := by sorry

theorem proper_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsProper) := by sorry

theorem flat_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@Flat) := by sorry

theorem openImmersion_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsOpenImmersion) := by sorry

theorem isomorphism_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (MorphismProperty.isomorphisms Scheme) := by sorry

theorem affine_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsAffineHom) := by sorry

theorem closedImmersion_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsClosedImmersion) := by sorry

theorem quasiAffine_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (fun X _ f =>
      Scheme.IsQuasiAffine X ∧ QuasiCompact f ∧ IsSeparated f) := by sorry

theorem quasiCompactImmersion_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (fun _ _ f => QuasiCompact f ∧ IsImmersion f) := by sorry

theorem integral_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsIntegralHom) := by sorry

theorem finite_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsFinite) := by sorry

theorem quasiFinite_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (fun _ _ f => LocallyQuasiFinite f ∧ QuasiCompact f) := by sorry

theorem relativeDimension_isFpqcLocalOnTarget (d : ℕ) :
    IsFlatLocalOnTarget
      (fun _ _ f => IsLocallyOfFiniteTypeOfRelativeDimension d f) := by sorry

theorem syntomic_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsSyntomic) := by sorry

theorem smooth_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@Smooth) := by sorry

theorem unramified_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsUnramified) := by sorry

theorem gUnramified_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsGUnramified) := by sorry

theorem etale_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@Etale) := by sorry

theorem finiteLocallyFree_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (fun _ _ f => IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f) := by sorry

theorem finiteLocallyFree_of_degree_isFpqcLocalOnTarget (d : ℕ) :
    IsFlatLocalOnTarget (fun _ _ f =>
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        ∀ y, Scheme.Hom.finrank f y = d) := by sorry

theorem monomorphism_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (fun _ _ f => Mono f) := by sorry

theorem regularImmersion_isFpqcLocalOnTarget :
    IsFlatLocalOnTarget (@IsKoszulRegularImmersion) ∧
      IsFlatLocalOnTarget (@IsH1RegularImmersion) ∧
      IsFlatLocalOnTarget (@IsQuasiRegularImmersion) := by sorry

end Formalization.Books.Descent.Unit19
