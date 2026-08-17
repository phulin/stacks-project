import Formalization.Books.Algebra.Unit17.Spectrum
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Commutative Algebra, Chapter 29: Images of ring maps of finite presentation

The source's constructible sets and quasi-compact maps use Mathlib's canonical
`Topology.IsConstructible`, `IsRetrocompact`, `IsCompact`, and `IsSpectralMap`
predicates.  The finite-union normal form is represented by
`PrimeSpectrum.ConstructibleSetData`; the source's basic pieces are precisely
the `BasicConstructibleSetData.toSet` pieces.  Localization and quotient
spectrum maps use the canonical maps from Chapter 17.
-/

namespace Formalization.Books.Algebra.Unit29

open Set
open _root_.Topology
open scoped TensorProduct

universe u

/-! ## Quasi-compact opens and constructible sets -/

/-
For an open subset of an affine spectrum, the four conditions in the source
are stated together.  `IsCompact` is the set-level quasi-compactness predicate.
-/
theorem isRetrocompact_iff_isCompact_iff_finite_union_basicOpen_iff_exists_fg_ideal
    {R : Type u} [CommRing R] {U : Set (PrimeSpectrum R)} (hU : IsOpen U) :
    IsRetrocompact U ↔
      IsCompact U ∧
        (∃ s : Finset R,
          U = ⋃ f ∈ s, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) ∧
          ∃ I : Ideal R, I.FG ∧
            (PrimeSpectrum.zeroLocus (I : Set R))ᶜ = U := by
  sorry

/-
Mathlib's `IsSpectralMap` is the canonical Lean interface for a continuous
quasi-compact map between spectral spaces: it includes continuity and compact
preimages of compact opens.  The second conjunct is the source's inverse-image
assertion for constructible sets.
-/
theorem affine_map_quasiCompact_and_constructible_preimage
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    IsSpectralMap (PrimeSpectrum.comap φ) ∧
      ∀ E : Set (PrimeSpectrum R), IsConstructible E →
        IsConstructible (PrimeSpectrum.comap φ ⁻¹' E) := by
  sorry

/-!
The source's finite union of sets `D(f) ∩ V(g₁, ..., gₘ)` is exactly
`PrimeSpectrum.ConstructibleSetData.toSet`.  We expose the equivalent
source-facing orientation of Mathlib's canonical equivalence, without defining
a parallel constructible-set data type.
-/
theorem isConstructible_iff_exists_constructibleSetData
    {R : Type u} [CommRing R] {T : Set (PrimeSpectrum R)} :
    IsConstructible T ↔
      ∃ S : PrimeSpectrum.ConstructibleSetData R, S.toSet = T := by
  exact PrimeSpectrum.exists_constructibleSetData_iff.symm

/-! ## Constructible sets as images -/

theorem exists_finitePresentation_ringHom_of_isConstructible
    {R : Type u} [CommRing R] {T : Set (PrimeSpectrum R)}
    (hT : IsConstructible T) :
    ∃ (S : Type u) (_ : CommRing S) (φ : R →+* S),
      RingHom.FinitePresentation φ ∧
        Set.range (PrimeSpectrum.comap φ) = T := by
  sorry

theorem isConstructible_image_of_localization
    {R : Type u} [CommRing R] (f : R)
    {E : Set (PrimeSpectrum (Localization.Away f))}
    (hE : IsConstructible E) :
    IsConstructible
      (PrimeSpectrum.comap (algebraMap R (Localization.Away f)) '' E) := by
  sorry

theorem isConstructible_image_of_fg_quotient
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    {E : Set (PrimeSpectrum (R ⧸ I))} (hE : IsConstructible E) :
    IsConstructible (PrimeSpectrum.comap (Ideal.Quotient.mk I) '' E) := by
  sorry

/-! ## The affine line -/

theorem polynomial_spectrum_comap_isOpen_and_standardOpen_image_isCompactOpen
    {R : Type u} [CommRing R] :
    IsOpenMap (PrimeSpectrum.comap (Polynomial.C : R →+* Polynomial R)) ∧
      ∀ f : Polynomial R,
        IsCompact
            (PrimeSpectrum.comap (Polynomial.C : R →+* Polynomial R) ''
              (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial R)))) ∧
          IsOpen
            (PrimeSpectrum.comap (Polynomial.C : R →+* Polynomial R) ''
              (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial R)))) := by
  sorry

/-! ## Characteristic polynomials and the affine-line special case -/

/-
The finite-free hypothesis in the source is represented by Mathlib's canonical
`Module.Free` and `Module.Finite` typeclasses.  `Algebra.lmul R A f` is the
source's multiplication map, and membership of all coefficients below the
finite rank is the source's `V(r₀, ..., rₙ₋₁)` condition.
-/
theorem characteristic_polynomial_prime
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A] (f : A) (p : PrimeSpectrum R) :
    IsNilpotent (algebraMap A (A ⊗[R] p.asIdeal.ResidueField) f) ↔
      ∀ i < Module.finrank R A,
        (Algebra.lmul R A f).charpoly.coeff i ∈ p.asIdeal := by
  exact isNilpotent_tensor_residueField_iff f p.asIdeal

theorem exists_fin_union_basicOpen_image_of_isUnit_leadingCoeff
    {R : Type u} [CommRing R] (f g : Polynomial R)
    (hg : IsUnit g.leadingCoeff) :
    ∃ n : ℕ, ∃ r : Fin n → R,
      PrimeSpectrum.comap (Polynomial.C : R →+* Polynomial R) ''
          ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial R))) ∩
            PrimeSpectrum.zeroLocus ({g} : Set (Polynomial R))) =
        ⋃ i, (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum R)) := by
  sorry

/-! ## Chevalley's theorem -/

theorem isConstructible_image_of_finitePresentation
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.FinitePresentation φ)
    {E : Set (PrimeSpectrum S)} (hE : IsConstructible E) :
    IsConstructible (PrimeSpectrum.comap φ '' E) := by
  exact PrimeSpectrum.isConstructible_comap_image hφ hE

/-
The source's warning that an affine open need not be a standard open is already
represented by the distinction between arbitrary open subsets and the basic
opens in Mathlib.  The displayed partitions, polynomial coefficient formulas,
and induction reductions in the proof narration are consequences of the
canonical spectrum, localization, quotient, polynomial, and constructible-set
APIs above; they do not introduce additional source-level definitions.
-/

end Formalization.Books.Algebra.Unit29
