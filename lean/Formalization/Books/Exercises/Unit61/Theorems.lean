import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.Topology.Constructible

import Formalization.Books.Exercises.Unit61.Definitions

/-!
# Exercises, Chapter 61: Theorems

The named theorems in the source are recorded through Mathlib's Chevalley,
Nullstellensatz, Krull-dimension, Noether-normalization, and regular-local
interfaces.
-/

namespace Formalization.Books.Exercises.Unit61

open Set Topology IsLocalRing

universe u v

noncomputable section

/-! ## Images of constructible sets -/

/-- The image of a constructible set under the map on spectra of a finitely
presented ring homomorphism is constructible. -/
theorem image_of_constructible_under_finite_presentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FinitePresentation)
    {s : Set (PrimeSpectrum S)} (hs : Topology.IsConstructible s) :
    Topology.IsConstructible (PrimeSpectrum.comap f '' s) := by
  exact PrimeSpectrum.isConstructible_comap_image hf hs

/-! ## Hilbert's Nullstellensatz -/

/-- Hilbert's Nullstellensatz identifies the vanishing ideal of the zero locus
with the radical of the original ideal. -/
theorem hilbert_nullstellensatz
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed K] {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus K I) = I.radical := by
  exact MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I

/-! ## Dimension of finite-type algebras over fields -/

/-- The dimension of a polynomial algebra in finitely many variables over a
field is the number of variables.  This is the standard dimension theorem
underlying the finite-type case. -/
theorem finite_type_field_polynomial_dimension
    (k : Type u) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- A nontrivial finite-type algebra over a field has finite Krull dimension. -/
theorem finite_type_field_algebra_dimension_lt_top
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A < ⊤ := by
  sorry

/-! ## Noether normalization -/

/-- Noether normalization gives a finite injective algebra map from a
polynomial algebra over the base field. -/
theorem noether_normalization_finite_injective
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n, ∃ g : MvPolynomial (Fin n) k →ₐ[k] A,
      Function.Injective g ∧ g.Finite := by
  exact exists_finite_inj_algHom_of_fg k A

/-! ## Regular local rings -/

/-- A Noetherian local ring is regular exactly when the dimension of its
cotangent space over its residue field equals its Krull dimension. -/
theorem regular_local_ring_iff_cotangent_space_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
        ringKrullDim R := by
  exact IsRegularLocalRing.iff_finrank_cotangentSpace R

end

end Formalization.Books.Exercises.Unit61
