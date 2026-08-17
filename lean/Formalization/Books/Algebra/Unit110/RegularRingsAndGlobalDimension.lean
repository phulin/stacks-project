import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit106.RegularLocalRings
import Formalization.Books.Algebra.Unit109.FiniteGlobalDimension

/-!
# Commutative Algebra, Chapter 110: Regular rings and global dimension

The chapter's projective dimensions and global dimensions use the canonical
interfaces from Chapter 109.  Finite free resolutions are represented by the
source-facing finite-free resolution predicate from that chapter, while local
regularity is Mathlib's `IsRegularLocalRing`.
-/

namespace Formalization.Books.Algebra.Unit110

open CategoryTheory
open Formalization.Books.Algebra.Unit109
open Formalization.Books.Algebra.Unit72
open IsLocalRing

universe u

noncomputable section

/-! ## Regular local rings and finite global dimension -/

/- The displayed resolution
   `0 → F_(d-e) → ... → F₀ → M → 0` is the finite prefix encoded by
   `HasFiniteFreeResolutionWithFiniteTermsLE`. -/

/-- A finite module of depth `e` over a regular local ring of dimension `d`
has a finite free resolution of length at most `d - e`. -/
theorem regular_local_finite_free_resolution
    {R M : Type u} [CommRing R] [IsRegularLocalRing R]
    [AddCommGroup M] [Module R M]
    [Module.Finite R M] (d e : ℕ)
    (hdim : ringKrullDim R = d)
    (hdepth : localDepth R M = (e : ℕ∞)) :
    HasFiniteFreeResolutionWithFiniteTermsLE (ModuleCat.of R M) (d - e) := by
  sorry

/-- A regular local ring of dimension `d` has global dimension at most `d`. -/
theorem regular_local_global_dimension_le
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hdim : ringKrullDim R = d) :
    HasGlobalDimensionLE R d := by
  sorry

/-- Over a Noetherian ring, a global-dimension bound can be checked at the
maximal localizations. -/
theorem finite_global_dimension_iff_localizations
    {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    HasGlobalDimensionLE R n ↔
      ∀ m : MaximalSpectrum R,
        HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) n := by
  sorry

/-! ## The residue field and dimension bounds -/

/-- The projective dimension of the residue field is at least the dimension of
the cotangent space.  The inequality is written in the canonical extended
natural-number-valued projective-dimension type. -/
theorem residue_field_projective_dimension_ge_cotangentSpace_finrank
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤
      CategoryTheory.projectiveDimension
        (ModuleCat.of R (ResidueField R)) := by
  sorry

/-- If the residue field has projective dimension exactly `n`, then the ring
dimension is at least `n`. -/
theorem ringKrullDim_ge_residue_field_projective_dimension
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ)
    (hκ : HasProjectiveDimensionExactly
      (ModuleCat.of R (ResidueField R)) n) :
    ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R := by
  sorry

/-- For a Noetherian local ring, finite projective dimension of the residue
field, finite global dimension, and regularity are equivalent.  In this case
the three numerical invariants in the source agree. -/
theorem residue_field_finite_projective_dimension_iff_finite_global_dimension_iff_regular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    List.TFAE
      [ HasFiniteProjectiveDimension (ModuleCat.of R (ResidueField R)),
        HasFiniteGlobalDimension R,
        IsRegularLocalRing R ] ∧
      (HasFiniteProjectiveDimension (ModuleCat.of R (ResidueField R)) →
        globalDimension R = ringKrullDim R ∧
          ringKrullDim R = Module.finrank (ResidueField R) (CotangentSpace R)) := by
  sorry

/-- A Noetherian local ring is regular exactly when it has finite global
dimension; then all of its prime localizations are regular local rings. -/
theorem regular_local_iff_finite_global_dimension
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    (IsRegularLocalRing R ↔ HasFiniteGlobalDimension R) ∧
      (HasFiniteGlobalDimension R →
        ∀ p : PrimeSpectrum R,
          IsRegularLocalRing (Localization.AtPrime p.asIdeal)) := by
  sorry

/-! ## Regular rings -/

/-- A Noetherian ring is regular when all of its prime localizations are
regular local rings. -/
def IsRegularRing (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ p : PrimeSpectrum R,
    IsRegularLocalRing (Localization.AtPrime p.asIdeal)

/-- Regularity can be checked at maximal ideals. -/
theorem isRegularRing_iff_forall_maximal
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsRegularRing R ↔
      ∀ m : MaximalSpectrum R,
        IsRegularLocalRing (Localization.AtPrime m.asIdeal) := by
  sorry

/-- The warning in the source is an existence assertion: regular Noetherian
rings need not have finite global dimension, because they may have infinite
Krull dimension. -/
theorem exists_regular_noetherian_ring_not_finite_global_dimension
    : ∃ (R : Type u) (_ : CommRing R) (_ : IsNoetherianRing R),
        IsRegularRing R ∧
          ¬ HasFiniteGlobalDimension R ∧
            ¬ ∃ n : ℕ,
              ringKrullDim R ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
  sorry

/-! ## Finite-dimensional regular rings -/

/- The source leaves `n` implicit in this lemma.  It is made an explicit
   parameter here so that the exact global dimension and exact Krull dimension
   in the first two alternatives have a single common value. -/

/-- For a Noetherian ring, having exact global dimension `n` is equivalent to
being regular of exact dimension `n`, and to the corresponding maximal- or
prime-local conditions. -/
theorem finite_global_dimension_iff_regular_finite_dimension
    {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    List.TFAE
      [ globalDimension R = ((n : ℕ∞) : WithBot ℕ∞),
        IsRegularRing R ∧
          ringKrullDim R = ((n : ℕ∞) : WithBot ℕ∞),
        (∀ m : MaximalSpectrum R,
            IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
              ringKrullDim (Localization.AtPrime m.asIdeal) ≤
                ((n : ℕ∞) : WithBot ℕ∞)) ∧
          ∃ m : MaximalSpectrum R,
            ringKrullDim (Localization.AtPrime m.asIdeal) =
              ((n : ℕ∞) : WithBot ℕ∞),
        (∀ p : PrimeSpectrum R,
            IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
              ringKrullDim (Localization.AtPrime p.asIdeal) ≤
                ((n : ℕ∞) : WithBot ℕ∞)) ∧
          ∃ p : PrimeSpectrum R,
            ringKrullDim (Localization.AtPrime p.asIdeal) =
              ((n : ℕ∞) : WithBot ℕ∞) ] := by
  sorry

/-! ## Flat local descent -/

/-- Regularity descends along a flat local homomorphism of Noetherian local
rings. -/
theorem isRegularLocalRing_of_flat_localHom_of_regular
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f]
    (hflat : RingHom.Flat f) (hS : IsRegularLocalRing S) :
    IsRegularLocalRing R := by
  sorry

end

end Formalization.Books.Algebra.Unit110
