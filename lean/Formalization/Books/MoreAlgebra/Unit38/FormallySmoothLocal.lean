import Formalization.Books.MoreAlgebra.Unit37.FormallySmooth
import Formalization.Books.Algebra.Unit141.SmoothRingMapsNoetherian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# More Algebra, Chapter 38: Formally smooth maps of local rings

This file records the local lifting criterion and the local algebra consequences
from the chapter section.  Adic formal smoothness is the canonical predicate
from Chapter 37; local rings, residue fields, small extensions, smoothness at a
prime, regular local rings, and multivariable power series use the existing
project and Mathlib interfaces.
-/

namespace Formalization.Books.MoreAlgebra.Unit38

open Formalization.Books.MoreAlgebra.Unit37

noncomputable section

universe u v

/-! ## The local lifting tests -/

/-- The square-zero lifting test in the local category used in the first
condition of the chapter's local criterion.

The explicit `IsLocalHom` hypotheses make the solid diagram of local ring
homomorphisms visible, while the local instances make the canonical residue
field map available. -/
def LocalSquareZeroLifting
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : Prop :=
  ∀ {A : Type (max u v)} [CommRing A] [IsLocalRing A]
    (J : Ideal A),
    J ^ 2 = ⊥ →
      (∃ n : ℕ, 0 < n ∧ (IsLocalRing.maximalIdeal A) ^ n = ⊥) →
      [IsLocalRing (A ⧸ J)] →
      IsLocalHom (Ideal.Quotient.mk J) →
      ∀ (g : R →+* A) (ψ : S →+* (A ⧸ J)),
        (hg : IsLocalHom g) →
          (hψ : IsLocalHom ψ) →
            letI : IsLocalHom g := hg
            letI : IsLocalHom ψ := hψ
            Function.Bijective (IsLocalRing.ResidueField.map ψ) →
              ψ.comp f = (Ideal.Quotient.mk J).comp g →
                ∃ lift : S →+* A,
                  IsLocalHom lift ∧
                    (Ideal.Quotient.mk J).comp lift = ψ ∧
                      lift.comp f = g

/-- The small-extension restriction of the local square-zero lifting test.

`IsSmallExtension` is reused from the earlier Algebra formalization, where it
is the source's local Artinian length-one kernel condition. -/
def LocalSmallExtensionLifting
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : Prop :=
  ∀ {A : Type (max u v)} [CommRing A] [IsLocalRing A]
    (J : Ideal A),
    J ^ 2 = ⊥ →
      (∃ n : ℕ, 0 < n ∧ (IsLocalRing.maximalIdeal A) ^ n = ⊥) →
      [IsLocalRing (A ⧸ J)] →
      Formalization.Books.Algebra.Unit141.IsSmallExtension
        (Ideal.Quotient.mk J) →
      IsLocalHom (Ideal.Quotient.mk J) →
      ∀ (g : R →+* A) (ψ : S →+* (A ⧸ J)),
        (hg : IsLocalHom g) →
          (hψ : IsLocalHom ψ) →
            letI : IsLocalHom g := hg
            letI : IsLocalHom ψ := hψ
            Function.Bijective (IsLocalRing.ResidueField.map ψ) →
              ψ.comp f = (Ideal.Quotient.mk J).comp g →
                ∃ lift : S →+* A,
                  IsLocalHom lift ∧
                    (Ideal.Quotient.mk J).comp lift = ψ ∧
                      lift.comp f = g

/-- Formal smoothness in the adic topologies of local rings is equivalent to
the square-zero local lifting test. -/
theorem formallySmoothForLocalRing_iff_localSquareZeroLifting
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    FormallySmoothForIdeals f
        (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) ↔
      LocalSquareZeroLifting f := by
  sorry

/-- For a Noetherian local target, the square-zero test may be restricted to
small extensions. -/
theorem formallySmoothForLocalRing_iff_localSmallExtensionLifting
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    FormallySmoothForIdeals f
        (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) ↔
      LocalSmallExtensionLifting f := by
  sorry

/-! ## Formal smoothness and regular local rings -/

/-- A formally smooth Noetherian local algebra over a field is regular. -/
theorem isRegularLocalRing_of_formallySmooth_field_localAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]
    (hformal :
      FormallySmoothForIdeal (algebraMap k A)
        (IsLocalRing.maximalIdeal A)) :
    IsRegularLocalRing A := by
  sorry

/-- A separable residue-field extension admits a coefficient-field section in
a complete local algebra. -/
theorem exists_residueField_section_of_separable
    (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Algebra.IsSeparable k (IsLocalRing.ResidueField A)] :
    ∃ e : IsLocalRing.ResidueField A →ₐ[k] A,
      (IsLocalRing.residue A).comp e.toRingHom = RingHom.id _ := by
  sorry

/-- A complete regular local algebra with separable residue field is a
multivariable power-series ring over its residue field, as a `k`-algebra.

The coefficient-field algebra structure on the power-series ring is made
explicit because its coefficients are the residue field rather than `k`. -/
theorem exists_algEquiv_mvPowerSeries_residueField
    (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Algebra.IsSeparable k (IsLocalRing.ResidueField A)] :
    ∃ d : ℕ,
      letI : Algebra k
          (MvPowerSeries (Fin d) (IsLocalRing.ResidueField A)) :=
        ((algebraMap (IsLocalRing.ResidueField A)
          (MvPowerSeries (Fin d) (IsLocalRing.ResidueField A))).comp
          (algebraMap k (IsLocalRing.ResidueField A))).toAlgebra
      Nonempty
        (A ≃ₐ[k] MvPowerSeries (Fin d) (IsLocalRing.ResidueField A)) := by
  sorry

/-- Conversely, a regular local algebra with separable residue-field
extension is formally smooth in the maximal-ideal-adic topology. -/
theorem formallySmooth_field_localAlgebra_of_isRegularLocalRing
    (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [IsRegularLocalRing A]
    [Algebra.IsSeparable k (IsLocalRing.ResidueField A)] :
    FormallySmoothForIdeal (algebraMap k A)
      (IsLocalRing.maximalIdeal A) := by
  sorry

/-! ## Finite type maps -/

/-- For a finite-type map from a Noetherian ring, smoothness at a prime is
equivalent to formal smoothness of the corresponding local map in the
maximal-ideal-adic topology. -/
theorem smoothAt_iff_localized_formallySmooth
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A]
    (f : A →+* B) (hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hpq : p.asIdeal = q.asIdeal.comap f) :
    letI : Algebra A B := f.toAlgebra
    Formalization.Books.Algebra.Unit137.IsSmoothAt A B q ↔
      FormallySmoothForIdeals
        (Localization.localRingHom p.asIdeal q.asIdeal f hpq)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) := by
  sorry

/- The proof of the regularity criterion constructs compatible continuous
`k`-algebra maps into successive power-series quotients.  They need not be
`K`-algebra maps for the residue field `K`; this is a warning about the
construction, not an additional hypothesis or conclusion. -/

end

end Formalization.Books.MoreAlgebra.Unit38
