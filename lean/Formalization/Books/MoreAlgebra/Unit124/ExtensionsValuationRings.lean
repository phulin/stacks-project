import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit50.ValuationRings
import Formalization.Books.Algebra.Unit155.Henselization
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Etale

/-!
This file formalizes the definitions and theorem interfaces in More on Algebra,
Chapter 124.  Valuation rings are Mathlib's `ValuationRing`s.  The value-group
index is represented by a finite set of representatives for the quotient of
nonzero elements by multiplication by a unit and an element of the base ring;
this avoids choosing noncanonical presentations of the value groups.
-/

namespace Formalization.Books.MoreAlgebra.Unit124

noncomputable section

universe u v

/-! ## Extensions of valuation rings -/

/- The general extension notion in the source is the same injective-local map
   pattern used for DVRs in Chapter 112, but with `ValuationRing` in place of
   `IsDiscreteValuationRing`. -/

/-- An injective local ring map between two valuation rings. -/
structure ValuationRingExtension (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B] where
  hom : A →+* B
  injective : Function.Injective hom
  localHom : IsLocalHom hom

instance ValuationRingExtension.isLocalHom
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    (E : ValuationRingExtension A B) : IsLocalHom E.hom := E.localHom

/-- The residue field attached to a valuation ring. -/
abbrev ResidueField (A : Type*) [CommRing A] [IsDomain A]
    [ValuationRing A] := (IsLocalRing.maximalIdeal A).ResidueField

/-- The residue-field map induced by a local extension of valuation rings. -/
noncomputable def residueFieldMap
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    (E : ValuationRingExtension A B) : ResidueField A →+* ResidueField B := by
  letI : IsLocalHom E.hom := E.localHom
  exact Ideal.ResidueField.map (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal B) E.hom
    (IsLocalRing.maximalIdeal_comap E.hom).symm

/-- The induced algebra structure on the residue-field extension. -/
@[instance_reducible] noncomputable def residueFieldAlgebra
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    (E : ValuationRingExtension A B) : Algebra (ResidueField A) (ResidueField B) :=
  (residueFieldMap E).toAlgebra

/-- Finiteness of the residue-field extension. -/
def ResidueFieldExtensionFinite
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    (E : ValuationRingExtension A B) : Prop :=
  letI := residueFieldAlgebra E
  FiniteDimensional (ResidueField A) (ResidueField B)

/-- The residual degree, with Mathlib's `finrank` convention in the infinite case. -/
noncomputable def residualDegree
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    (E : ValuationRingExtension A B) : ℕ :=
  letI := residueFieldAlgebra E
  Module.finrank (ResidueField A) (ResidueField B)

/-- A unit-factorization form of equality of the value groups.

For valuation rings, every nonzero element of `B` has the same value as an
element of `A` exactly when it is a unit times the image of that element. -/
def ValueGroupMapInjective
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  ∀ {a b : A}, a ≠ 0 → b ≠ 0 →
    (∃ u : Bˣ, f a = (u : B) * f b) →
      ∃ u : Aˣ, a = (u : A) * b

/-- Equality of the value groups is represented by injectivity together with
the unit-factorization surjectivity criterion. -/
def WeaklyUnramified
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  ValueGroupMapInjective f ∧
    ∀ b : B, b ≠ 0 →
      ∃ a : A, a ≠ 0 ∧ ∃ u : Bˣ, b = (u : B) * f a

/-- The value-group map attached to an extension is injective. -/
theorem valueGroup_injective
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    (E : ValuationRingExtension A B) :
    ValueGroupMapInjective E.hom := by
  sorry

/-- The finite-coset condition expressing finite index of value groups. -/
def ValueGroupCosetCover
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    (E : ValuationRingExtension A B) (n : ℕ) (r : Fin n → B) : Prop :=
  ∀ b : B, b ≠ 0 →
    ∃ i : Fin n, ∃ a : A, a ≠ 0 ∧ ∃ u : Bˣ,
      b = (u : B) * E.hom a * r i

/-- The value-group index, using the least cardinality of a coset cover. -/
noncomputable def valueGroupIndex
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    (E : ValuationRingExtension A B) : ℕ :=
  by
    classical
    exact if h : ∃ n : ℕ, ∃ r : Fin n → B, ValueGroupCosetCover E n r then
      Nat.find h
    else 0

/-- Finiteness of the index of the value group of the base in the extension. -/
def ValueGroupIndexFinite
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    (E : ValuationRingExtension A B) : Prop :=
  ∃ n : ℕ, ∃ r : Fin n → B, ValueGroupCosetCover E n r

/-- Fraction-field data compatible with an extension of valuation rings. -/
structure FractionFieldExtension
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    (E : ValuationRingExtension A B) where
  fractionRingA : IsFractionRing A K
  fractionRingB : IsFractionRing B L
  map_commutes : ∀ a : A,
    algebraMap B L (E.hom a) = algebraMap K L (algebraMap A K a)

/-- The source's extension conclusion without requiring target valuation-ring
instances to be available while a theorem is constructing them. -/
def IsValuationRingExtensionHom
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  Function.Injective f ∧ IsLocalHom f

/-! ## The finite-extension inequality -/

/-- A finite fraction-field extension has finite residue and value-group degrees,
and their product is bounded by the field degree. -/
theorem inequality_general
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [IsDomain A] [IsDomain B]
    [ValuationRing A] [ValuationRing B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    (E : ValuationRingExtension A B)
    (_F : FractionFieldExtension (K := K) (L := L) E)
    [FiniteDimensional K L] :
    ResidueFieldExtensionFinite E ∧
      ValueGroupIndexFinite E ∧
        valueGroupIndex E * residualDegree E ≤ Module.finrank K L := by
  sorry

/-! ## Purely inseparable extensions -/

/-- The integral closure in a purely inseparable field extension is again a
valuation ring, has the larger field as fraction field, and is a local
injective extension of the base. -/
theorem purelyInseparable_integralClosure
    {A K L : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsFractionRing A K]
    (hPurelyInseparable : IsPurelyInseparable K L) :
    let B := _root_.integralClosure A L
    ∃ hB : IsDomain B,
      @ValuationRing B _ hB ∧
        IsFractionRing B L ∧
          IsValuationRingExtensionHom (algebraMap A B) := by
  sorry

/-! ## Normal domains and roots -/

/-- The map on localizations at a prime and a prime above it. -/
noncomputable def localPrimeMap
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap f q = p) :
    Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
  Localization.localRingHom p.asIdeal q.asIdeal f (by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq).symm)

/-- Under the weak-unramification hypothesis in codimension one, an nth root
in a flat local extension of normal Noetherian domains descends up to a unit. -/
theorem extension_normal_domains_and_roots
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : Formalization.Books.Algebra.Unit37.IsNormalDomain A)
    (hB : Formalization.Books.Algebra.Unit37.IsNormalDomain B)
    (f : A →+* B) [IsLocalHom f] (hflat : RingHom.Flat f)
    (x : A) (y : B) (n : ℕ) (hn : 1 < n) (w : Bˣ)
    (hfactor : f x = (w : B) * y ^ n)
    (hweak : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 →
      ∃ q : PrimeSpectrum B, q.asIdeal.height = 1 ∧
        ∃ hq : PrimeSpectrum.comap f q = p,
        WeaklyUnramified (localPrimeMap f p q hq)) :
    ∃ g : A, ∃ u : Aˣ, x = (u : A) * g ^ n := by
  sorry

/-! ## Etale extensions -/

/-- The map from a ring to the localization of the target at a prime. -/
noncomputable def mapToLocalization
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (q : Ideal B) [q.IsPrime] : A →+* Localization.AtPrime q :=
  (algebraMap B (Localization.AtPrime q)).comp f

/-- An etale algebra over a valuation ring, localized at a prime over the
maximal ideal, is a weakly unramified valuation-ring extension. -/
theorem etale_extension_valuationRing
    {A B : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] (f : A →+* B) (hf : RingHom.Etale f)
    (m : Ideal B) [m.IsPrime]
    (hm : m.comap f = IsLocalRing.maximalIdeal A) :
    ∃ hB : IsDomain (Localization.AtPrime m),
      @ValuationRing (Localization.AtPrime m) _ hB ∧
        IsValuationRingExtensionHom (mapToLocalization f m) ∧
          WeaklyUnramified (mapToLocalization f m) := by
  sorry

/-! ## Henselization -/

/-- Henselization and strict henselization data carry the two ring maps used
in the source's chain `A ⊂ Aʰ ⊂ Aˢʰ`. -/
theorem henselization_valuationRing
    {A K : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    (D : Formalization.Books.Algebra.Unit155.StrictHenselizationData A K) :
    letI : CommRing D.henselization := D.commRingHenselization
    letI : IsLocalRing D.henselization := D.localRingHenselization
    letI : CommRing D.strictHenselization := D.commRingStrictHenselization
    letI : IsLocalRing D.strictHenselization := D.localRingStrictHenselization
    ∃ hH : IsDomain D.henselization,
      ∃ hS : IsDomain D.strictHenselization,
        @ValuationRing D.henselization _ hH ∧
          @ValuationRing D.strictHenselization _ hS ∧
            IsValuationRingExtensionHom D.henselizationMap ∧
              WeaklyUnramified D.henselizationMap ∧
                IsValuationRingExtensionHom D.mapFromHenselization ∧
                  WeaklyUnramified D.mapFromHenselization ∧
                    IsValuationRingExtensionHom D.strictMap ∧
                      WeaklyUnramified D.strictMap := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit124
