import Formalization.Books.MoreAlgebra.Unit112.ExtensionsDiscreteValuationRings
import Formalization.Books.Algebra.Unit162.NagataRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# More on Algebra, Chapter 115: Abhyankar's lemma and tame ramification

This file records the constructions and theorem interfaces in the chapter.
The DVR and finite-extension predicates from Chapter 112 are deliberately
reused; the proofs of the new interfaces are deferred to the proving stage.
-/

namespace Formalization.Books.MoreAlgebra.Unit115

open scoped TensorProduct

noncomputable section

universe u v w

open Formalization.Books.MoreAlgebra.Unit112
open Formalization.Books.Algebra.Unit162

/-! ## The base-change construction -/

/-- The reduced tensor product used for the field `L₁` in the construction.

For commutative rings, quotienting by the radical of the zero ideal is the
canonical reduced quotient. -/
def reducedTensorProduct
    (K : Type u) (L : Type v) (K₁ : Type w)
    [CommRing K] [CommRing L] [CommRing K₁]
    [Algebra K L] [Algebra K K₁] : Type (max v w) :=
  (TensorProduct K L K₁) ⧸ Ideal.radical (⊥ : Ideal (TensorProduct K L K₁))

/-- The integral closure notation used for the rings `A₁` and `B₁`. -/
abbrev integralClosureIn (A : Type u) (R : Type v) [CommRing A] [CommRing R]
    [Algebra A R] : Type v := ↥(_root_.integralClosure A R)

/-- A finite product of Dedekind domains, expressed by its product
decomposition rather than by choosing one component as a representative. -/
def IsFiniteProductOfDedekindDomains
    (R : Type u) [CommRing R] : Prop :=
  ∃ (n : ℕ) (S : Fin n → CommRingCat.{u}),
    Nonempty (R ≃+* (∀ i, (S i : Type u))) ∧
      ∀ i, IsDedekindDomain (S i : Type u)

/-- The objects in Remark `remark-construction`, with the canonical objects
`A₁`, `L₁`, and `B₁` exposed as definitions. -/
structure BaseChangeConstruction
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E) where
  B₁ : Type*
  B₁_commRing : CommRing B₁
  B₁_algebra : Algebra B B₁
  B₁_integral : ∀ x : B₁, IsIntegral B x
  B₁_isFiniteProductOfDedekindDomains :
    IsFiniteProductOfDedekindDomains B₁
  L₁_nonempty_finite_product : Prop
  tensor_localization : Prop
  uniformizer_nonzerodivisor : Prop
  integral_kernel_nilpotent : Prop
  spectrum_B₁_surjective : Prop
  spectrum_tensor_surjective : Prop

attribute [instance] BaseChangeConstruction.B₁_commRing
  BaseChangeConstruction.B₁_algebra

abbrev baseChangeA₁
    (A K₁ : Type*) [CommRing A] [Field K₁] [Algebra A K₁] :=
  integralClosureIn A K₁

abbrev baseChangeL₁
    (K : Type u) (L : Type v) (K₁ : Type w)
    [CommRing K] [CommRing L] [CommRing K₁]
    [Algebra K L] [Algebra K K₁] : Type (max v w) :=
  reducedTensorProduct K L K₁

theorem baseChange_A₁_isDedekindDomain
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A]
    [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E) :
    IsDedekindDomain (baseChangeA₁ A K₁) := by
  sorry

theorem baseChange_spectrum_surjective
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (C : BaseChangeConstruction (K₁ := K₁) E F) :
    IsFiniteProductOfDedekindDomains C.B₁ := by
  exact C.B₁_isFiniteProductOfDedekindDomains

theorem baseChange_tensor_spectrum_surjective
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (C : BaseChangeConstruction (K₁ := K₁) E F) :
    C.spectrum_tensor_surjective := by
  sorry

/-! The following data packages the local DVR diagrams and the assertions
about their places from the construction remark. -/

/-- A DVR map whose source and target rings are carried by the local diagram.
This avoids identifying the different localizations appearing over different
places. -/
structure LocalDVRMap where
  source : Type*
  target : Type*
  sourceCommRing : CommRing source
  targetCommRing : CommRing target
  sourceDomain : IsDomain source
  targetDomain : IsDomain target
  sourceDVR : IsDiscreteValuationRing source
  targetDVR : IsDiscreteValuationRing target
  map : letI := sourceCommRing; letI := targetCommRing
    letI := sourceDomain; letI := targetDomain
    letI := sourceDVR; letI := targetDVR
    DVRMap source target

def LocalDVRMap.formallySmooth (D : LocalDVRMap) : Prop :=
  letI := D.sourceCommRing
  letI := D.targetCommRing
  letI := D.sourceDomain
  letI := D.targetDomain
  letI := D.sourceDVR
  letI := D.targetDVR
  RingHom.FormallySmooth D.map.hom

structure BaseChangePlaceData
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) where
  numberOfPlaces : ℕ
  numberOfPlaces_pos : 0 < numberOfPlaces
  numberOfPlacesAbove : Fin numberOfPlaces → ℕ
  numberOfPlacesAbove_pos : ∀ i, 0 < numberOfPlacesAbove i
  baseRamificationIndex : Fin numberOfPlaces → ℕ
  localExtension : ∀ (i : Fin numberOfPlaces)
    (j : Fin (numberOfPlacesAbove i)),
    LocalDVRMap

def IsHenselianConstruction
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    {E : DVRMap A B} (P : BaseChangePlaceData E) : Prop :=
  P.numberOfPlaces = 1

def IsPurelyInseparableConstruction
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    {E : DVRMap A B} (P : BaseChangePlaceData E) : Prop :=
  P.numberOfPlaces = 1 ∧
    P.numberOfPlacesAbove ⟨0, P.numberOfPlaces_pos⟩ = 1

def IsFiniteSeparableConstruction
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    {E : DVRMap A B} (P : BaseChangePlaceData E) : Prop :=
  P.numberOfPlaces > 0

theorem baseChange_henselian_places
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [HenselianLocalRing A]
    (E : DVRMap A B) (P : BaseChangePlaceData E) :
    P.numberOfPlaces = 1 := by
  sorry

theorem baseChange_henselian_B_places
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [HenselianLocalRing B]
    (E : DVRMap A B) (P : BaseChangePlaceData E) :
    ∀ i, P.numberOfPlacesAbove i = 1 := by
  sorry

theorem baseChange_purelyInseparable_places
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (P : BaseChangePlaceData E)
    {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]
    (hK : IsPurelyInseparable K K₁) :
    P.numberOfPlaces = 1 ∧
      P.numberOfPlacesAbove ⟨0, P.numberOfPlaces_pos⟩ = 1 := by
  sorry

theorem baseChange_finite_separable
    {A B K L K₁ : Type*} [CommRing A] [CommRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁]
    [Algebra.IsSeparable K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (C : BaseChangeConstruction (K₁ := K₁) E F) :
    Module.Finite A (baseChangeA₁ A K₁) ∧ Module.Finite B C.B₁ := by
  sorry

theorem baseChange_A₁_finite_of_nagata
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (hA : IsNagataRing A) :
    Module.Finite A (baseChangeA₁ A K₁) := by
  sorry

theorem baseChange_B₁_finite_of_nagata
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (C : BaseChangeConstruction (K₁ := K₁) E F)
    (hB : IsNagataRing B) :
    Module.Finite B C.B₁ := by
  sorry

/-! ## Pulling a root of a uniformizer -/

/-- The root extension `K[π^(1/n)]`, represented by the canonical adjoin-root
construction over the fraction field. -/
abbrev pullRootField
    (K : Type u) [Field K] (π : K) (n : ℕ) : Type u :=
  AdjoinRoot ((Polynomial.X : Polynomial K) ^ n - Polynomial.C π)

def IsTotallyRamified
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L) : Prop :=
  TotallyRamifiedWithRespectTo X

def IsSubextension
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] : Prop :=
  ∃ f : L →ₐ[K] M, Function.Injective f

theorem pullRoot_uniformizer
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (n : ℕ) (hn : 2 ≤ n)
    (hπ : IsFractionRing A K) :
    ∃ (K₁ : Type*) (hK₁ : Field K₁) (hAK₁ : Algebra A K₁)
      (hKK₁ : Algebra K K₁)
      (hfin : letI := hKK₁; FiniteDimensional K K₁),
      letI := hK₁
      letI := hAK₁
      letI := hKK₁
      letI := hfin
      ∃ θ : K₁, θ ^ n = algebraMap A K₁ π ∧
        Algebra.adjoin K {θ} = ⊤ ∧
        ∃ X : FiniteSeparableExtensionData A K K₁,
          Module.finrank K K₁ = n ∧ IsTotallyRamified X ∧
            ∃ A₁ : Type*,
              ∃ (hA₁ : CommRing A₁),
                letI := hA₁
                Nonempty (A₁ ≃+* integralClosureIn A K₁) := by
  sorry

theorem pullRoot_uniformizer_tame_subextensions
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (n : ℕ) (hn : 2 ≤ n)
    (hπ : IsFractionRing A K)
    (hprime : ∃ p : ℕ, 0 < p ∧ CharP A p ∧ Nat.Coprime n p) :
    ∃ (K₁ : Type*) (hK₁ : Field K₁) (hAK₁ : Algebra A K₁)
      (hKK₁ : Algebra K K₁) (hfin : FiniteDimensional K K₁),
      letI := hK₁
      letI := hAK₁
      letI := hKK₁
      letI := hfin
      ∃ X : FiniteSeparableExtensionData A K K₁,
        TamelyRamifiedWithRespectTo X ∧
          ∀ (M : Type*) (hM : Field M) (hKM : Algebra K M)
            (hAM : Algebra A M),
            letI := hM
            letI := hKM
            letI := hAM
            IsSubextension K M K₁ →
              ∃ d : ℕ, d ∣ n ∧
                ∃ θ : M, θ ^ d = algebraMap A M π ∧
                  Algebra.adjoin K {θ} = ⊤ := by
  sorry

/-! ## Formal smoothness and Abhyankar's lemma -/

def FormallySmoothInAdicTopology
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) : Prop :=
  RingHom.FormallySmooth E.hom

theorem formallySmooth_goes_up
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (P : BaseChangePlaceData E)
    (h : FormallySmoothInAdicTopology E) :
    ∀ i j, (P.localExtension i j).formallySmooth := by
  sorry

theorem abhyankar_lemma
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (P : BaseChangePlaceData E)
    (hchar : ∃ p : ℕ, p = 0 ∨ ∃ hp : 0 < p, CharP A p)
    (hdiv : ∃ i, ramificationIndex E ∣ P.baseRamificationIndex i) :
    ∀ i j, (P.localExtension i j).formallySmooth := by
  sorry

/-! ## Tame composition, subextensions, and characterization -/

structure TameTowerData
    {A K L M : Type*} [CommRing A] [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    (XL : FiniteSeparableExtensionData A K L)
    (XML : FiniteSeparableExtensionData L L M)
    (XMK : FiniteSeparableExtensionData A K M) where
  restrictionBase : Fin XMK.numberOfPlaces → Fin XL.numberOfPlaces
  restrictionMiddle : Fin XMK.numberOfPlaces → Fin XML.numberOfPlaces
  base_ramification_factor : ∀ i, ∃ d : ℕ,
    XMK.ramificationIndex i =
      XL.ramificationIndex (restrictionBase i) * d
  middle_ramification_factor : ∀ i, ∃ d : ℕ,
    XMK.ramificationIndex i =
      XML.ramificationIndex (restrictionMiddle i) * d
  residue_separable : ∀ i, XMK.residueFieldSeparable i

theorem tame_composition
    {A K L M : Type*} [CommRing A] [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    (XL : FiniteSeparableExtensionData A K L)
    (XML : FiniteSeparableExtensionData L L M)
    (XMK : FiniteSeparableExtensionData A K M)
    (C : TameTowerData XL XML XMK)
    (hL : TamelyRamifiedWithRespectTo XL)
    (hML : TamelyRamifiedWithRespectTo XML) :
    TamelyRamifiedWithRespectTo XMK := by
  sorry

theorem tame_subextension
    {A K L M : Type*} [CommRing A] [Field K] [Field L] [Field M]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    (XL : FiniteSeparableExtensionData A K L)
    (XM : FiniteSeparableExtensionData A K M)
    (R : PlaceRestrictionData XL XM)
    (hM : TamelyRamifiedWithRespectTo XM) :
    TamelyRamifiedWithRespectTo XL := by
  sorry

def IsInvertibleInResidueCharacteristic
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L) (n : ℕ) : Prop :=
  0 < n ∧ (X.residueCharacteristic = 0 ∨
    Nat.Coprime n X.residueCharacteristic)

def HasUnramifiedRootCover
    {A : Type u} {K : Type v} {L : Type w} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L) (π : A) (e : ℕ) : Prop :=
  IsInvertibleInResidueCharacteristic X e ∧
    ∃ (K₁ L₁ : Type u) (hK₁ : Field K₁) (hL₁ : Field L₁)
      (hAK₁ : Algebra A K₁) (hKK₁ : Algebra K K₁)
      (hK₁fin : letI := hKK₁; FiniteDimensional K K₁)
      (hKL₁ : Algebra K L₁) (hK₁L₁ : Algebra K₁ L₁)
      (hA₁L₁ : Algebra (integralClosureIn A K₁) L₁),
      letI := hK₁
      letI := hL₁
      letI := hK₁fin
      letI := hAK₁
      letI := hKK₁
      letI := hKL₁
      letI := hK₁L₁
      letI := hA₁L₁
      (∃ θ : K₁, θ ^ e = algebraMap A K₁ π ∧
        Algebra.adjoin K {θ} = ⊤) ∧
      ∃ Y : FiniteSeparableExtensionData (integralClosureIn A K₁) K₁ L₁,
        IsSubextension K L L₁ ∧ UnramifiedWithRespectTo Y

def tameCharacterizationConditions
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L) (π : A) : List Prop :=
  [TamelyRamifiedWithRespectTo X,
    ∃ e : ℕ, HasUnramifiedRootCover X π e,
    ∃ e₀ : ℕ, IsInvertibleInResidueCharacteristic X e₀ ∧
      ∀ d : ℕ, IsInvertibleInResidueCharacteristic X d →
        HasUnramifiedRootCover X π (d * e₀)]

theorem tame_characterization
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L) (π : A) :
    List.TFAE (tameCharacterizationConditions X π) := by
  sorry

/-! ## Permanence of tame ramification -/

def HasTamelyRamifiedGaloisClosure
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
        (j : L →ₐ[K] M),
        Function.Injective j ∧ TamelyRamifiedWithRespectTo Y

def HasTamelyRamifiedCommonCompositum
    {A K L₁ L₂ : Type*} [CommRing A] [Field K] [Field L₁] [Field L₂]
    [Algebra A K] [Algebra A L₁] [Algebra A L₂]
    [Algebra K L₁] [Algebra K L₂]
    (X₁ : FiniteSeparableExtensionData A K L₁)
    (X₂ : FiniteSeparableExtensionData A K L₂) : Prop :=
  ∃ (L : Type*) (hL : Field L) (hKL : Algebra K L),
    letI := hL
    letI := hKL
    ∃ (hAL : Algebra A L),
      letI := hAL
      ∃ (j₁ : L₁ →ₐ[K] L) (j₂ : L₂ →ₐ[K] L)
        (Y : FiniteSeparableExtensionData A K L),
        Function.Injective j₁ ∧ Function.Injective j₂ ∧
          Algebra.adjoin K (Set.range j₁ ∪ Set.range j₂) = ⊤ ∧
          TamelyRamifiedWithRespectTo Y

theorem tame_galois_closure
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (X : FiniteSeparableExtensionData A K L)
    (hX : TamelyRamifiedWithRespectTo X) :
    HasTamelyRamifiedGaloisClosure X := by
  sorry

theorem tame_common_compositum
    {A K L₁ L₂ : Type*} [CommRing A] [Field K] [Field L₁] [Field L₂]
    [Algebra A K] [Algebra A L₁] [Algebra A L₂]
    [Algebra K L₁] [Algebra K L₂]
    (X₁ : FiniteSeparableExtensionData A K L₁)
    (X₂ : FiniteSeparableExtensionData A K L₂)
    (h₁ : TamelyRamifiedWithRespectTo X₁)
    (h₂ : TamelyRamifiedWithRespectTo X₂) :
    HasTamelyRamifiedCommonCompositum X₁ X₂ := by
  sorry

/-! ## Tame ramification after extending the base DVR -/

structure TensorProductFieldFactors
    (K : Type u) (L : Type v) (K₁ : Type w) [Field K] [Field L] [Field K₁]
    [Algebra K L] [Algebra K K₁] where
  numberOfFactors : ℕ
  factor : Fin numberOfFactors → Type (max u (max v w))
  factorField : ∀ i, Field (factor i)
  productPresentation : Prop

structure TameBaseChangeData
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) where
  factors : TensorProductFieldFactors K L K₁
  unramified_case : Prop
  tame_case : Prop
  unramified_factor : Fin factors.numberOfFactors → Prop
  tame_factor : Fin factors.numberOfFactors → Prop

theorem tame_goes_up
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [FiniteDimensional K K₁]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (hsep : Algebra.IsSeparable K K₁)
    (D : TameBaseChangeData (K := K) (L := L) (K₁ := K₁) E) :
    D.factors.numberOfFactors > 0 ∧
      (D.unramified_case → ∀ i, D.unramified_factor i) ∧
      (D.tame_case → ∀ i, D.tame_factor i) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit115
