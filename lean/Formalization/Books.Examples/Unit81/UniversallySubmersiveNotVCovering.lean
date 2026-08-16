import Mathlib.Algebra.Ring.Prod
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Maps.Basic

/-!
# Examples, Chapter 81: Universally submersive but not V covering

This file records the valuation-ring example from the source section.  The
finite coproduct of affine schemes is represented by the spectrum of the
product ring, using Mathlib's canonical `coprodSpec` isomorphism.  The
chapter-specific `Submersive` and affine singleton `IsVCovering` predicates
make the two topological claims and the valuative obstruction explicit.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Set
open Topology

namespace Formalization.«Books.Examples».Unit81

/-! ## The valuation ring and its intermediate prime -/

/-- A prime which is neither a minimal prime nor a maximal ideal. -/
def IsIntermediatePrime (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (p : PrimeSpectrum A) : Prop :=
  p.asIdeal ∉ minimalPrimes A ∧ ¬p.asIdeal.IsMaximal

/-- The localization of `A` at the prime represented by `p`. -/
abbrev localizedRing (A : Type u) [CommRing A] (p : PrimeSpectrum A) : Type u :=
  Localization.AtPrime p.asIdeal

/-- The residue ring of the prime represented by `p`. -/
abbrev residueRing (A : Type u) [CommRing A] (p : PrimeSpectrum A) : Type u :=
  A ⧸ p.asIdeal

/-- The affine ring representing the disjoint union of the two spectra. -/
abbrev disjointUnionAffineRing (A : Type u) [CommRing A] (p : PrimeSpectrum A) : Type u :=
  localizedRing A p × residueRing A p

/-- The ring map whose spectrum is the source morphism in the example. -/
noncomputable def disjointUnionAffineRingMap (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) : A →+* disjointUnionAffineRing A p :=
  (algebraMap A (localizedRing A p)).prod (Ideal.Quotient.mk p.asIdeal)

/-- The affine scheme representing `Spec(Aₚ) ⨿ Spec(A/𝔭)`. -/
abbrev disjointUnionAffineScheme (A : Type u) [CommRing A] (p : PrimeSpectrum A) : Scheme :=
  Spec (CommRingCat.of (disjointUnionAffineRing A p))

/-- The morphism `Spec(Aₚ) ⨿ Spec(A/𝔭) ⟶ Spec(A)`, in its affine realization. -/
noncomputable def disjointUnionAffineSchemeMap (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) : disjointUnionAffineScheme A p ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (disjointUnionAffineRingMap A p))

/-- The affine realization used above is canonically the coproduct of the two spectra. -/
noncomputable def disjointUnionAffineSchemeIsoCoproduct (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) :
    Spec (CommRingCat.of (localizedRing A p)) ⨿
        Spec (CommRingCat.of (residueRing A p)) ≅ disjointUnionAffineScheme A p :=
  asIso (AlgebraicGeometry.coprodSpec (localizedRing A p) (residueRing A p))

/-! ## The base change appearing in the proof of universal submersiveness -/

/-- The extension of `𝔭` to `B` along an `A`-algebra structure. -/
def baseChangedIdeal (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) : Ideal B :=
  p.asIdeal.map (algebraMap A B)

/-- The localization of `B` at the image of the complement of `p`. -/
abbrev baseChangedLocalization (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) : Type u :=
  Localization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl)

/-- The quotient of `B` by the extended ideal. -/
abbrev baseChangedQuotient (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) : Type u :=
  B ⧸ baseChangedIdeal A B p

/-- The affine ring representing the base-changed disjoint union. -/
abbrev baseChangedDisjointUnionRing (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (p : PrimeSpectrum A) : Type u :=
  baseChangedLocalization A B p × baseChangedQuotient A B p

/-- The base-changed ring map `B → Bₚ × B/𝔭B`. -/
noncomputable def baseChangedDisjointUnionRingMap (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (p : PrimeSpectrum A) : B →+* baseChangedDisjointUnionRing A B p :=
  (algebraMap B (baseChangedLocalization A B p)).prod
    (Ideal.Quotient.mk (baseChangedIdeal A B p))

/-- The base change of the example morphism along `Spec(B) ⟶ Spec(A)`. -/
noncomputable def baseChangedDisjointUnionSchemeMap (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (p : PrimeSpectrum A) :
    Spec (CommRingCat.of (baseChangedDisjointUnionRing A B p)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (baseChangedDisjointUnionRingMap A B p))

/-- The localization component of the base-changed source. -/
noncomputable def localizationComponent (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (p : PrimeSpectrum A) : Set (Spec (CommRingCat.of B)) :=
  Set.range <| Spec.map (CommRingCat.ofHom (algebraMap B (baseChangedLocalization A B p)))

/-- The quotient component of the base-changed source. -/
noncomputable def quotientComponent (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (p : PrimeSpectrum A) : Set (Spec (CommRingCat.of B)) :=
  Set.range <| Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (baseChangedIdeal A B p)))

/-- The two components cover the base-changed affine scheme. -/
theorem baseChanged_components_cover (A B : Type u) [CommRing A] [IsDomain A]
    [ValuationRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A) :
    localizationComponent A B p ∪ quotientComponent A B p = Set.univ := by
  sorry

/-- The affine realization of the base change is a categorical pullback. -/
theorem baseChangedDisjointUnionSchemeMap_isPullback (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (p : PrimeSpectrum A) :
    ∃ i : Spec (CommRingCat.of (baseChangedDisjointUnionRing A B p)) ⟶
        disjointUnionAffineScheme A p,
      IsPullback (baseChangedDisjointUnionSchemeMap A B p) i
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (disjointUnionAffineSchemeMap A p) := by
  sorry

/-! ## Spectrum images -/

/-- Data witnessing that a subset of an affine spectrum is the image of a spectrum of an algebra. -/
structure SpectrumImageData (B : Type u) [CommRing B]
    (T : Set (Spec (CommRingCat.of B))) where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  [algebraBCarrier : Algebra B carrier]
  image_eq : T = Set.range (Spec.map (CommRingCat.ofHom (algebraMap B carrier)))

/-- A subset of `Spec(B)` which is the image of the spectrum of a `B`-algebra. -/
def IsSpectrumImageOfAlgebra (B : Type u) [CommRing B]
    (T : Set (Spec (CommRingCat.of B))) : Prop :=
  Nonempty (SpectrumImageData B T)

/-! ## Submersiveness and the closed-subset argument -/

/-- A scheme morphism is submersive when its underlying map is a quotient map. -/
def Submersive {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Topology.IsQuotientMap f

/-- Universal submersiveness is the universalization of the quotient-map property. -/
def UniversallySubmersive {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  CategoryTheory.MorphismProperty.universally
    (AlgebraicGeometry.topologically @Topology.IsQuotientMap) f

/-- The universal property unfolds to quotient maps on all scheme-theoretic base changes. -/
theorem universallySubmersive_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    UniversallySubmersive f ↔
      ∀ ⦃X' Y' : Scheme.{u}⦄ (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y)
        (f' : X' ⟶ Y') (_ : IsPullback f' i₁ i₂ f),
        Submersive f' :=
  Iff.rfl

/-- The base-changed morphism is surjective on points. -/
theorem baseChangedDisjointUnionSchemeMap_surjective (A B : Type u) [CommRing A] [IsDomain A]
    [ValuationRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A) :
    Surjective (baseChangedDisjointUnionSchemeMap A B p) := by
  sorry

/-- The two closed pieces in the source proof are images of spectra of `B`-algebras. -/
theorem baseChanged_components_are_spectrum_images (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (p : PrimeSpectrum A) :
    IsSpectrumImageOfAlgebra B (localizationComponent A B p) ∧
      IsSpectrumImageOfAlgebra B (quotientComponent A B p) := by
  sorry

/-- The union of the two closed component intersections is again a spectrum image. -/
theorem baseChanged_subset_isSpectrumImage_of_component_closed
    (A B : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) (T : Set (Spec (CommRingCat.of B)))
    (h₁ : IsClosed (localizationComponent A B p ∩ T))
    (h₂ : IsClosed (quotientComponent A B p ∩ T)) :
    IsSpectrumImageOfAlgebra B T := by
  sorry

/-- A subset which is a spectrum image, stable under specialization, is closed. -/
theorem isClosed_of_spectrumImage_and_stableUnderSpecialization
    (B : Type u) [CommRing B] (T : Set (Spec (CommRingCat.of B)))
    (hT : IsSpectrumImageOfAlgebra B T)
    (hstable : StableUnderSpecialization T) : IsClosed T := by
  sorry

/-- The closedness criterion used after splitting a subset into the two components. -/
theorem baseChanged_subset_isClosed_of_component_closed
    (A B : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) (T : Set (Spec (CommRingCat.of B)))
    (h₁ : IsClosed (localizationComponent A B p ∩ T))
    (h₂ : IsClosed (quotientComponent A B p ∩ T))
    (hstable : StableUnderSpecialization T) : IsClosed T := by
  sorry

/-! ## Valuation-ring specialization interfaces -/

/-- A valuation ring packaged with the instances needed to form its spectrum. -/
structure ValuationRingSpec where
  carrier : Type u
  [commRing : CommRing carrier]
  [domain : IsDomain carrier]
  [valuationRing : ValuationRing carrier]

attribute [instance] ValuationRingSpec.commRing ValuationRingSpec.domain
  ValuationRingSpec.valuationRing

/-- The valuation-ring package associated to a ring already carrying the instances. -/
abbrev valuationRingSpecOf (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    ValuationRingSpec :=
  { carrier := A }

/-- An extension of valuation rings used in the affine valuative criterion. -/
structure ValuationRingExtension (V : ValuationRingSpec.{u}) where
  target : ValuationRingSpec.{u}
  hom : V.carrier →+* target.carrier
  injective : Function.Injective hom
  local_hom : IsLocalHom hom

/-- Data for a valuation ring whose generic and closed points realize a specialization. -/
structure ValuationRingSpecializationData (B : Type u) [CommRing B]
    (x y : Spec (CommRingCat.of B)) where
  source : ValuationRingSpec
  map : Spec (CommRingCat.of source.carrier) ⟶ Spec (CommRingCat.of B)
  eta : Spec (CommRingCat.of source.carrier)
  closed : Spec (CommRingCat.of source.carrier)
  eta_generic : ∀ z, eta ⤳ z
  closed_specializes : ∀ z, z ⤳ closed
  closed_is_closed : IsClosed ({closed} : Set (Spec (CommRingCat.of source.carrier)))
  closed_unique : ∀ z, IsClosed ({z} : Set (Spec (CommRingCat.of source.carrier))) → z = closed
  map_eta : map eta = x
  map_closed : map closed = y

/-- Every specialization in an affine scheme admits the valuation-ring witness used in the source. -/
theorem exists_valuationRing_specialization {B : Type u} [CommRing B]
    {x y : Spec (CommRingCat.of B)} (hxy : x ⤳ y) :
    Nonempty (ValuationRingSpecializationData B x y) := by
  sorry

/-- The composition of a valuation-ring specialization with `Spec(B) ⟶ Spec(A)`. -/
noncomputable def specializationToBaseMap
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {x y : Spec (CommRingCat.of B)}
    (d : ValuationRingSpecializationData B x y) :
    Spec (CommRingCat.of d.source.carrier) ⟶ Spec (CommRingCat.of A) :=
  d.map ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The chosen valuation-ring witness has image the interval between its endpoint images on
`Spec(A)`, as used in the source's specialization argument. -/
theorem exists_valuationRing_specialization_with_base_image
    (A B : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B] [Algebra A B]
    {x y : Spec (CommRingCat.of B)} (hxy : x ⤳ y) :
    ∃ d : ValuationRingSpecializationData B x y,
      Set.range (specializationToBaseMap A B d) =
        {z | specializationToBaseMap A B d d.eta ⤳ z ∧
          z ⤳ specializationToBaseMap A B d d.closed} := by
  sorry

/-- If the middle prime is not in the valuation-ring image, both endpoints stay in one component. -/
theorem specialization_stays_in_one_component
    (A B : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) {x y : Spec (CommRingCat.of B)}
    (d : ValuationRingSpecializationData B x y)
    (hnot : (p : Spec (CommRingCat.of A)) ∉ Set.range (specializationToBaseMap A B d)) :
    (x ∈ localizationComponent A B p ∧ y ∈ localizationComponent A B p) ∨
      (x ∈ quotientComponent A B p ∧ y ∈ quotientComponent A B p) := by
  sorry

/-- Closedness of the two component intersections handles the case without the middle prime. -/
theorem specialization_mem_of_not_in_base_image
    (A B : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) {x y : Spec (CommRingCat.of B)}
    (d : ValuationRingSpecializationData B x y) (T : Set (Spec (CommRingCat.of B)))
    (hx : x ∈ T)
    (h₁ : IsClosed (localizationComponent A B p ∩ T))
    (h₂ : IsClosed (quotientComponent A B p ∩ T))
    (hnot : (p : Spec (CommRingCat.of A)) ∉ Set.range (specializationToBaseMap A B d)) :
    y ∈ T := by
  sorry

/-- Closedness of the two component intersections handles the case through the middle prime. -/
theorem specialization_mem_of_middle_prime_in_base_image
    (A B : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) {x y : Spec (CommRingCat.of B)}
    (d : ValuationRingSpecializationData B x y) (T : Set (Spec (CommRingCat.of B)))
    (hx : x ∈ T)
    (h₁ : IsClosed (localizationComponent A B p ∩ T))
    (h₂ : IsClosed (quotientComponent A B p ∩ T))
    (hmiddle : ∃ r, specializationToBaseMap A B d r = (p : Spec (CommRingCat.of A))) :
    y ∈ T := by
  sorry

/-- In the middle-prime case, the valuation witness supplies the intermediate point and both
component memberships used in the source's specialization argument. -/
theorem specialization_middle_prime_component_bridge
    (A B : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) {x y : Spec (CommRingCat.of B)}
    (d : ValuationRingSpecializationData B x y)
    (hmiddle : ∃ r, specializationToBaseMap A B d r = (p : Spec (CommRingCat.of A))) :
    ∃ r, specializationToBaseMap A B d r = (p : Spec (CommRingCat.of A)) ∧
      x ⤳ d.map r ∧ d.map r ⤳ y ∧
      x ∈ localizationComponent A B p ∧ d.map r ∈ localizationComponent A B p ∧
      d.map r ∈ quotientComponent A B p ∧ y ∈ quotientComponent A B p := by
  sorry

/-! ## The universal submersiveness claim -/

/-- The base-changed morphism is submersive. -/
theorem baseChangedDisjointUnionSchemeMap_submersive (A B : Type u) [CommRing A] [IsDomain A]
    [ValuationRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A) :
    Submersive (baseChangedDisjointUnionSchemeMap A B p) := by
  sorry

/-- The affine morphism in the source is universally submersive. -/
theorem disjointUnionAffineSchemeMap_universallySubmersive
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (p : PrimeSpectrum A) (hp : IsIntermediatePrime A p) :
    UniversallySubmersive (disjointUnionAffineSchemeMap A p) := by
  sorry

/-! ## The V-covering obstruction -/

/-- The affine singleton V-covering condition used in this chapter. -/
def IsVCovering {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∀ (V : ValuationRingSpec)
    (g : Spec (CommRingCat.of V.carrier) ⟶ Spec (CommRingCat.of A)),
    ∃ (e : ValuationRingExtension V)
      (h : Spec (CommRingCat.of e.target.carrier) ⟶ X),
      Spec.map (CommRingCat.ofHom e.hom) ≫ g = h ≫ f

/-- A V-covering supplies the valuation-ring factorization against the identity of the target. -/
theorem IsVCovering.exists_extension_factorization {A : Type u} [CommRing A]
    [IsDomain A] [ValuationRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (hf : IsVCovering f) :
    ∃ (e : ValuationRingExtension (valuationRingSpecOf A))
      (h : Spec (CommRingCat.of e.target.carrier) ⟶ X),
      Spec.map (CommRingCat.ofHom e.hom) = h ≫ f := by
  obtain ⟨e, h, he⟩ := hf (valuationRingSpecOf A) (𝟙 _)
  refine ⟨e, h, ?_⟩
  change Spec.map (CommRingCat.ofHom e.hom) ≫ 𝟙 (Spec (CommRingCat.of A)) = h ≫ f at he
  rw [Category.comp_id] at he
  exact he

/-- The spectrum of a valuation ring is connected. -/
theorem isConnected_spec_of_valuationRing (V : ValuationRingSpec) :
    _root_.IsConnected (Set.univ : Set (Spec (CommRingCat.of V.carrier))) := by
  sorry

/-- A factorization through the two components would disconnect the valuation-ring spectrum. -/
theorem factorization_through_disjoint_union_forces_disconnected
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (p : PrimeSpectrum A) (hp : IsIntermediatePrime A p)
    (e : ValuationRingExtension (valuationRingSpecOf A))
    (h : Spec (CommRingCat.of e.target.carrier) ⟶ disjointUnionAffineScheme A p)
    (commutes : Spec.map (CommRingCat.ofHom e.hom) =
      h ≫ disjointUnionAffineSchemeMap A p) :
    ¬_root_.IsConnected (Set.univ : Set (Spec (CommRingCat.of e.target.carrier))) := by
  sorry

/-- The morphism in the example is not an affine singleton V-covering. -/
theorem disjointUnionAffineSchemeMap_not_isVCovering
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (p : PrimeSpectrum A) (hp : IsIntermediatePrime A p) :
    ¬IsVCovering (disjointUnionAffineSchemeMap A p) := by
  sorry

/-! ## The source's final existence statement -/

/-- Both schemes in the example are affine. -/
theorem disjointUnionAffineSchemeMap_affine
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (p : PrimeSpectrum A) :
    IsAffine (disjointUnionAffineScheme A p) ∧
      IsAffine (Spec (CommRingCat.of A)) := by
  exact ⟨inferInstance, inferInstance⟩

/-- There is an affine universally submersive morphism which is not a V-covering. -/
theorem exists_affine_universallySubmersive_not_isVCovering :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (p : PrimeSpectrum A),
      IsIntermediatePrime A p ∧
        IsAffine (disjointUnionAffineScheme A p) ∧
          IsAffine (Spec (CommRingCat.of A)) ∧
            UniversallySubmersive (disjointUnionAffineSchemeMap A p) ∧
              ¬IsVCovering (disjointUnionAffineSchemeMap A p) := by
  sorry

end Formalization.«Books.Examples».Unit81
