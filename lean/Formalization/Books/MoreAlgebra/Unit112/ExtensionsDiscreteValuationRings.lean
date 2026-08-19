import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RingHom.Smooth

/-!
This file formalizes the definitions and theorem interfaces in More on Algebra,
Chapter 112.  The canonical DVR and ideal-action APIs are used throughout;
the proofs are deferred to the proving stage.
-/

namespace Formalization.Books.MoreAlgebra.Unit112

noncomputable section

universe u v w

/-! ## Extensions of discrete valuation rings -/

/-- A ring map between two DVRs which is injective and local. -/
structure DVRMap (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] where
  hom : A →+* B
  injective : Function.Injective hom
  localHom : IsLocalHom hom

instance DVRMap.isLocalHom {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) : IsLocalHom E.hom := E.localHom

/-- The source's predicate that `A → B` is an extension of DVRs. -/
def IsExtensionOfDiscreteValuationRings {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (f : A →+* B) : Prop := Function.Injective f ∧ IsLocalHom f

/-- The residue field attached to a DVR, using Mathlib's ideal residue field. -/
abbrev DVRResidueField (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] := (IsLocalRing.maximalIdeal A).ResidueField

/-- The ramification index, defined by the defining power equality of maximal ideals.

The default value `0` is only used for a ring map which is not a `DVRMap`; for a
map satisfying the source hypotheses the defining existence and uniqueness
theorem below identifies this value with the usual positive index. -/
noncomputable def ramificationIndex {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) : ℕ := by
  classical
  exact if h : ∃ e : ℕ, 0 < e ∧
      Ideal.map E.hom (IsLocalRing.maximalIdeal A) =
        (IsLocalRing.maximalIdeal B) ^ e then
    Nat.find h
  else 0

/-- The weakly unramified condition is ramification index one. -/
def WeaklyUnramified {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) : Prop := ramificationIndex E = 1

/-- The residue-field homomorphism induced by a local DVR map. -/
noncomputable def residueFieldMap {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) : DVRResidueField A →+* DVRResidueField B := by
  letI : IsLocalHom E.hom := E.localHom
  exact Ideal.ResidueField.map (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal B) E.hom
    (IsLocalRing.maximalIdeal_comap E.hom).symm

/-- The canonical algebra structure on the residue-field extension. -/
@[instance_reducible] noncomputable def residueFieldAlgebra {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) : Algebra (DVRResidueField A) (DVRResidueField B) :=
  (residueFieldMap E).toAlgebra

/-- Finiteness of the residue-field extension. -/
def ResidueFieldExtensionFinite {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) : Prop :=
  letI := residueFieldAlgebra E
  FiniteDimensional (DVRResidueField A) (DVRResidueField B)

/-- The residual degree, with the usual `finrank` convention outside the finite case. -/
noncomputable def residualDegree {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) : ℕ :=
  letI := residueFieldAlgebra E
  Module.finrank (DVRResidueField A) (DVRResidueField B)

/-- Fraction-field data for an extension of DVRs. -/
structure FractionFieldExtension
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    (E : DVRMap A B) where
  fractionRingA : IsFractionRing A K
  fractionRingB : IsFractionRing B L
  map_commutes : ∀ a : A,
    algebraMap B L (E.hom a) = algebraMap K L (algebraMap A K a)

theorem ramificationIndex_spec
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) :
    0 < ramificationIndex E ∧
      Ideal.map E.hom (IsLocalRing.maximalIdeal A) =
        (IsLocalRing.maximalIdeal B) ^ ramificationIndex E := by
  sorry

theorem uniformizer_factorization
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) {πA : A} {πB : B}
    (hπA : Irreducible πA) (hπB : Irreducible πB) :
    ∃ u : Bˣ, E.hom πA = (u : B) * πB ^ ramificationIndex E := by
  sorry

theorem ramificationIndex_unique
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) {e : ℕ} (he : 0 < e)
    (heq : Ideal.map E.hom (IsLocalRing.maximalIdeal A) =
      (IsLocalRing.maximalIdeal B) ^ e) :
    e = ramificationIndex E := by
  sorry

theorem ramification_residue_degree_inequality
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (_F : FractionFieldExtension (K := K) (L := L) E)
    [FiniteDimensional K L] :
    ramificationIndex E * residualDegree E ≤ Module.finrank K L := by
  sorry

theorem residueFieldExtension_finite_of_finite_fraction_extension
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (_F : FractionFieldExtension (K := K) (L := L) E)
    [FiniteDimensional K L] : ResidueFieldExtensionFinite E := by
  sorry

theorem ramificationIndex_tower
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    (E₁ : DVRMap A B) (E₂ : DVRMap B C) :
    ramificationIndex ⟨E₂.hom.comp E₁.hom, E₂.injective.comp E₁.injective,
      inferInstance⟩ = ramificationIndex E₁ * ramificationIndex E₂ := by
  sorry

theorem residualDegree_tower
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    (E₁ : DVRMap A B) (E₂ : DVRMap B C)
    (h₁ : ResidueFieldExtensionFinite E₁)
    (h₂ : ResidueFieldExtensionFinite E₂) :
    residualDegree ⟨E₂.hom.comp E₁.hom, E₂.injective.comp E₁.injective,
      inferInstance⟩ = residualDegree E₁ * residualDegree E₂ := by
  sorry

theorem ramificationIndex_is_p_power_of_purelyInseparable
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (_F : FractionFieldExtension (K := K) (L := L) E)
    [CharP K p] (hp : 0 < p)
    (hPurelyInseparable : IsPurelyInseparable K L) :
    ∃ n : ℕ, ramificationIndex E = p ^ n := by
  sorry

/-! ## Formal smoothness and the three finite-extension predicates -/

theorem formallySmooth_iff_weaklyUnramified_and_residue_separable
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) :
    RingHom.FormallySmooth E.hom ↔
      WeaklyUnramified E ∧
        letI := residueFieldAlgebra E
        Algebra.IsSeparable (DVRResidueField A) (DVRResidueField B) := by
  sorry

/-- A finite separable extension together with its integral closure. -/
structure FiniteSeparableExtensionData
    (A K L : Type*) [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] where
  finite : FiniteDimensional K L
  separable : Algebra.IsSeparable K L
  numberOfPlaces : ℕ
  ramificationIndex : Fin numberOfPlaces → ℕ
  residueDegree : Fin numberOfPlaces → ℕ
  residueCharacteristic : ℕ
  residueFieldSeparable : Fin numberOfPlaces → Prop
  residueFieldTrivial : Fin numberOfPlaces → Prop

def UnramifiedWithRespectTo
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L) : Prop :=
  ∀ i, X.ramificationIndex i = 1 ∧ X.residueFieldSeparable i

def TamelyRamifiedWithRespectTo
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L) : Prop :=
  (∀ i, X.residueFieldSeparable i) ∧
    (X.residueCharacteristic = 0 ∨
      ∀ i, Nat.Coprime (X.ramificationIndex i) X.residueCharacteristic)

def TotallyRamifiedWithRespectTo
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L) : Prop :=
  X.numberOfPlaces = 1 ∧ ∃ i : Fin X.numberOfPlaces, X.residueFieldTrivial i

theorem integralClosure_finite_and_dimension_one
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsDomain A]
    [IsDiscreteValuationRing A] [IsNoetherianRing A]
    (X : FiniteSeparableExtensionData A K L) :
    letI := X.finite
    letI := X.separable
    ∃ hB : IsDedekindDomain (_root_.integralClosure A L),
      letI := hB
      Module.Finite A (_root_.integralClosure A L) ∧
      ∃ (m : Fin X.numberOfPlaces → Ideal (_root_.integralClosure A L)),
        (∀ i, (m i).IsMaximal) ∧
          (∀ q : Ideal (_root_.integralClosure A L), q.IsMaximal → ∃ i, q = m i) := by
  sorry

theorem finite_separable_extension_sum_ramification_residue
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L) :
    letI := X.finite
    letI := X.separable
    (∀ i, 0 < X.ramificationIndex i ∧ 0 < X.residueDegree i) ∧
        Module.finrank K L =
          ∑ i, X.ramificationIndex i * X.residueDegree i := by
  sorry

theorem henselian_integralClosure_has_unique_maximalIdeal
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [HenselianLocalRing A] (X : FiniteSeparableExtensionData A K L) :
    letI := X.finite
    letI := X.separable
    X.numberOfPlaces = 1 := by
  sorry

structure PlaceRestrictionData
    {A K L M : Type*} [CommRing A] [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    (XL : FiniteSeparableExtensionData A K L)
    (XM : FiniteSeparableExtensionData A K M) where
  restriction : Fin XM.numberOfPlaces → Fin XL.numberOfPlaces
  surjective : Function.Surjective restriction
  ramification_factor : ∀ i, ∃ d : ℕ,
    XM.ramificationIndex i = XL.ramificationIndex (restriction i) * d
  residue_separability_descends : ∀ i,
    XM.residueFieldSeparable i → XL.residueFieldSeparable (restriction i)

theorem unramified_permanence_subextension
    {A K L M : Type*} [CommRing A] [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    (XL : FiniteSeparableExtensionData A K L)
    (XM : FiniteSeparableExtensionData A K M)
    (R : PlaceRestrictionData XL XM)
    (hM : UnramifiedWithRespectTo XM) :
    UnramifiedWithRespectTo XL := by
  sorry

def HasUnramifiedGaloisClosure
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L) : Prop :=
  ∃ (M : Type*) (hM : Field M) (hKM : Algebra K M)
    (hKMfin : FiniteDimensional K M) (hGalois : IsGalois K M)
    (hLM : Algebra L M),
    letI := hM
    letI := hKM
    letI := hKMfin
    letI := hGalois
    letI := hLM
    ∃ (hAM : Algebra A M),
      letI := hAM
      ∃ (Y : FiniteSeparableExtensionData A K M)
        (j : L →ₐ[K] M) (R : PlaceRestrictionData X Y),
        Function.Injective j ∧ Function.Surjective R.restriction ∧
          UnramifiedWithRespectTo Y

theorem unramified_galois_closure
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L)
    (hL : UnramifiedWithRespectTo X) :
    HasUnramifiedGaloisClosure X := by
  sorry

def HasUnramifiedCommonCompositum
    {A K L₁ L₂ : Type*} [CommRing A] [Field K] [Field L₁] [Field L₂]
    [Algebra A K] [Algebra A L₁] [Algebra A L₂]
    [Algebra K L₁] [Algebra K L₂]
    (X₁ : FiniteSeparableExtensionData A K L₁)
    (X₂ : FiniteSeparableExtensionData A K L₂) : Prop :=
  ∃ (L : Type*) (hL : Field L) (hKL : Algebra K L),
    letI := hL
    letI := hKL
    UnramifiedWithRespectTo X₁ ∧ UnramifiedWithRespectTo X₂ ∧
    ∃ (hAL : Algebra A L),
      letI := hAL
      ∃ (j₁ : L₁ →ₐ[K] L) (j₂ : L₂ →ₐ[K] L)
        (Y : FiniteSeparableExtensionData A K L),
        Function.Injective j₁ ∧ Function.Injective j₂ ∧
          Algebra.adjoin K (Set.range j₁ ∪ Set.range j₂) = ⊤ ∧
          UnramifiedWithRespectTo Y

theorem unramified_common_compositum
    {A K L₁ L₂ : Type*} [CommRing A] [Field K] [Field L₁] [Field L₂]
    [Algebra A K] [Algebra A L₁] [Algebra A L₂]
    [Algebra K L₁] [Algebra K L₂]
    (X₁ : FiniteSeparableExtensionData A K L₁)
    (X₂ : FiniteSeparableExtensionData A K L₂)
    (h₁ : UnramifiedWithRespectTo X₁)
    (h₂ : UnramifiedWithRespectTo X₂) :
    HasUnramifiedCommonCompositum X₁ X₂ := by
  sorry

structure UnramifiedCompositionData
    {A K L M : Type*} [CommRing A] [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    (XL : FiniteSeparableExtensionData A K L)
    (XML : FiniteSeparableExtensionData L L M)
    (XMK : FiniteSeparableExtensionData A K M) where
  restrictionBase : Fin XMK.numberOfPlaces → Fin XL.numberOfPlaces
  restrictionMiddle : Fin XMK.numberOfPlaces → Fin XML.numberOfPlaces
  ramification_factor : ∀ i, ∃ d : ℕ,
    XMK.ramificationIndex i =
      XL.ramificationIndex (restrictionBase i) * d
  middle_ramification_factor : ∀ i, ∃ d : ℕ,
    XMK.ramificationIndex i =
      XML.ramificationIndex (restrictionMiddle i) * d
  residue_separable : ∀ i, XMK.residueFieldSeparable i

theorem unramified_composition
    {A K L M : Type*} [CommRing A] [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    (XL : FiniteSeparableExtensionData A K L)
    (XML : FiniteSeparableExtensionData L L M)
    (XMK : FiniteSeparableExtensionData A K M)
    (C : UnramifiedCompositionData XL XML XMK)
    (hLK : UnramifiedWithRespectTo XL)
    (hML : UnramifiedWithRespectTo XML) :
    UnramifiedWithRespectTo XMK := by
  sorry


end

end Formalization.Books.MoreAlgebra.Unit112
