import Formalization.Books.Algebra.Unit146.LocalHomomorphisms
import Formalization.Books.Algebra.Unit151.UnramifiedRingMaps
import Formalization.Books.MoreAlgebra.Unit107.LocalIrreducibility
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# More on Algebra, Chapter 108: Miscellaneous on branches

This file records the four source lemmas about contractions of ideals,
unramified maps over geometrically unibranch domains, local maps essentially
of finite type, and minimal primes after tensoring strict henselian local
algebras.
-/

namespace Formalization.Books.MoreAlgebra.Unit108

open Formalization.Books.MoreAlgebra.Unit107
open Formalization.Books.Algebra.Unit146
open Formalization.Books.Algebra.Unit151
open Formalization.Books.Algebra.Unit153
open Formalization.Books.Algebra.Unit155
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Generic points -/

/-- The generic point of the spectrum of a domain. -/
def genericPoint (R : Type u) [CommRing R] [IsDomain R] : PrimeSpectrum R :=
  ⟨(⊥ : Ideal R), inferInstance⟩

/-! ## Localizations and fibres -/

/- A localization witness is parameterized by the property of the map before
  localization.  The étale case itself uses the established
  `Formalization.Books.Algebra.Unit146.IsLocalizationOfEtale` declaration
  below. -/
structure LocalizationWitness
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) where
  T : Type u
  [commRingT : CommRing T]
  g : A →+* T
  p : Ideal T
  [primeP : p.IsPrime]
  q : T →+* B
  comp : q.comp g = f
  localization :
    letI : Algebra T B := q.toAlgebra
    IsLocalization.AtPrime B p

/-- A map is a localization at a prime of a map with property `P`. -/
def IsLocalizationOf
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S],
      (R →+* S) → Prop)
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  ∃ W : LocalizationWitness f,
    letI : CommRing W.T := W.commRingT
    P W.g

/-- The localization forms occurring in alternatives (2), (3), and (4) of
the source lemma. -/
def IsLocalizationOfUnramified
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∃ W : LocalizationWitness f,
    letI : CommRing W.T := W.commRingT
    letI : Algebra A W.T := W.g.toAlgebra
    Algebra.Unramified A W.T

abbrev IsLocalizationOfQuasiFinite
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  IsLocalizationOf
    (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) =>
      RingHom.QuasiFinite g) f

abbrev IsLocalizationOfIntegral
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  IsLocalizationOf
    (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) =>
      RingHom.IsIntegral g) f

/-- There are no nontrivial specializations between points in a fibre of a
map of spectra. -/
def NoNontrivialSpecializationsInFibres
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ p q : PrimeSpectrum B,
    PrimeSpectrum.comap f p = PrimeSpectrum.comap f q →
      p ≤ q → p = q

/-! ## The contraction lemma -/

/-- Under any of the seven hypotheses in the source, every nonzero ideal of
`B` has nonzero contraction to `A`.  The contraction is the precise Lean
form of the source's `A ∩ J`. -/
theorem ideal_comap_ne_bot_of_branch_hypothesis
    {A B : Type u} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] (f : A →+* B)
    (h : Formalization.Books.Algebra.Unit146.IsLocalizationOfEtale f ∨
      (RingHom.Flat f ∧ IsLocalizationOfUnramified f) ∨
      (RingHom.Flat f ∧ IsLocalizationOfQuasiFinite f) ∨
      (RingHom.Flat f ∧ IsLocalizationOfIntegral f) ∨
      (RingHom.Flat f ∧ NoNontrivialSpecializationsInFibres f) ∨
      (PrimeSpectrum.comap f
          (genericPoint B) =
          genericPoint A ∧
        NoNontrivialSpecializationsInFibres f) ∨
      ∃! p : PrimeSpectrum B,
        PrimeSpectrum.comap f p =
          genericPoint A) :
    ∀ J : Ideal B, J ≠ ⊥ → Ideal.comap f J ≠ ⊥ := by
  sorry

/-! ## Unramified extensions over a geometrically unibranch domain -/

/-- The map on localizations at a pair of primes over one another. -/
noncomputable def localizedAtPrimeMap
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap f q = p) :
    Localization.AtPrime p.asIdeal →+*
      Localization.AtPrime q.asIdeal :=
  Localization.localRingHom p.asIdeal q.asIdeal f (by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq).symm)

/-- The map from `A` to the principal localization `B_g` induced by `f`. -/
noncomputable def localizationAwayMap
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (g : B) : A →+* Localization.Away g := by
  exact (algebraMap B (Localization.Away g)).comp f

/-- If an unramified map is injective after localizing at a prime of a
geometrically unibranch domain, a principal localization of the target is
étale over the original domain. -/
theorem exists_localization_away_etale_of_unramified_at_prime
    {A B : Type u} [CommRing A] [CommRing B]
    [IsDomain A]
    (f : A →+* B) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap f q = p)
    (hA_unibranch :
      IsGeometricallyUnibranch (Localization.AtPrime p.asIdeal))
    (h_unramified :
      letI : Algebra A B := f.toAlgebra
      Formalization.Books.Algebra.Unit151.UnramifiedAt A B q)
    (h_injective :
      Function.Injective (localizedAtPrimeMap f p q hq)) :
    ∃ g : B, g ∉ q.asIdeal ∧
      letI : Algebra A (Localization.Away g) :=
        (localizationAwayMap f g).toAlgebra
      Algebra.Etale A (Localization.Away g) := by
  sorry

/-! ## Local maps essentially of finite type -/

/-- The separability condition on the residue-field extension induced by a
local ring homomorphism. -/
def ResidueFieldExtensionIsSeparable
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] : Prop :=
  letI : Algebra (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B) :=
    (IsLocalRing.ResidueField.map f).toAlgebra
  Algebra.IsSeparable (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B)

/-- An injective local map essentially of finite type between geometrically
unibranch local domains is a localization of an étale ring map when it maps
the maximal ideal onto the maximal ideal and induces a separable residue-field
extension. -/
theorem isLocalizationOfEtale_of_injective_local_essFiniteType
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsDomain A]
    (hA_unibranch : IsGeometricallyUnibranch A)
    (f : A →+* B) (hf : IsLocalHom f)
    (h_injective : Function.Injective f)
    (h_essFiniteType : RingHom.EssFiniteType f)
    (h_maximalIdeal :
      Ideal.map f (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal B)
    (h_separable :
      letI : IsLocalHom f := hf
      ResidueFieldExtensionIsSeparable f) :
    Formalization.Books.Algebra.Unit146.IsLocalizationOfEtale f := by
  sorry

/-! ## Minimal primes after tensoring strict henselian local algebras -/

/-- The ideal denoted
`\mathfrak m_A \otimes_k B + A \otimes_k \mathfrak m_B` in the source. -/
def tensorMaximalIdeal
    (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra k A] [Algebra k B] : Ideal (A ⊗[k] B) :=
  Ideal.map
      (Algebra.TensorProduct.includeLeftRingHom :
        A →+* (A ⊗[k] B)) (IsLocalRing.maximalIdeal A) ⊔
    Ideal.map
      (Algebra.TensorProduct.includeRight.toRingHom :
        B →+* (A ⊗[k] B)) (IsLocalRing.maximalIdeal B)

/-- The minimal primes of the strict henselization at the tensor-product
maximal ideal correspond to pairs of minimal primes of the two factors. -/
theorem minimalPrimes_strictHenselization_tensor
    (k A B : Type u) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B]
    [StrictlyHenselianLocalRing A] [StrictlyHenselianLocalRing B]
    (hA_residue :
      Nonempty (IsLocalRing.ResidueField A ≃+* k))
    (hB_residue :
      Nonempty (IsLocalRing.ResidueField B ≃+* k))
    (p : PrimeSpectrum (A ⊗[k] B))
    (hp : p.asIdeal = tensorMaximalIdeal k A B)
    (C : Type u) [CommRing C] [IsLocalRing C]
    (c : Localization.AtPrime p.asIdeal →+* C)
    (hc : IsStrictHenselization (Localization.AtPrime p.asIdeal) C c) :
    Nonempty
      (MinimalPrimeSpectrum C ≃
        MinimalPrimeSpectrum A × MinimalPrimeSpectrum B) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit108
