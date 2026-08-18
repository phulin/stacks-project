import Mathlib.Topology.Sober

import Formalization.Books.Exercises.Unit06.Basics

/-!
# Exercises, Chapter 6: Irreducible subsets and generic points

The source definitions are represented by Mathlib's canonical
`IsIrreducible`, `IsGenericPoint`, `IrreducibleSpace`, and `QuasiSober`
interfaces.  The spectrum statements use the corresponding canonical
vanishing-ideal and sobriety theorems.
-/

noncomputable section

universe u

open Set Topology

namespace Formalization.Books.Exercises.Unit06

/-! ## Irreducibility of spectra -/

/-- `Spec(A)` is irreducible exactly when its nilradical is prime. -/
theorem spectrum_irreducible_iff_nilradical_prime {A : Type u} [CommRing A] :
    IrreducibleSpace (PrimeSpectrum A) ↔ (nilradical A).IsPrime := by
  exact PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical

/-- In the irreducible case the nilradical is the unique minimal prime. -/
theorem nilradical_unique_minimal_prime {A : Type u} [CommRing A]
    (h : (nilradical A).IsPrime) :
    nilradical A ∈ minimalPrimes A ∧
      ∀ p : Ideal A, p ∈ minimalPrimes A → p = nilradical A := by
  rw [minimalPrimes_eq_minimals]
  constructor
  · change Minimal Ideal.IsPrime (nilradical A)
    exact ⟨h, fun q hq _ => @nilradical_le_prime A _ q hq⟩
  · intro p hp
    change Minimal Ideal.IsPrime p at hp
    exact (hp.eq_of_le h (@nilradical_le_prime A _ p hp.1)).symm

/-- Irreducibility is unchanged on passing to the closure. -/
theorem irreducible_iff_closure_irreducible {X : Type u} [TopologicalSpace X]
    (T : Set X) :
    IsIrreducible T ↔ IsIrreducible (closure T) := by
  exact isIrreducible_iff_closure.symm

/-! ## Irreducible closed subsets -/

/-- The irreducible closed subsets of an affine spectrum are exactly the
vanishing sets of prime ideals. -/
theorem closed_irreducible_iff_prime_zeroLocus {A : Type u} [CommRing A]
    {T : Set (PrimeSpectrum A)} :
    IsClosed T ∧ IsIrreducible T ↔
      ∃ p : Ideal A, p.IsPrime ∧
        T = PrimeSpectrum.zeroLocus (p : Set A) := by
  constructor
  · rintro ⟨hclosed, hirr⟩
    obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal T).mp hclosed
    refine ⟨I.radical, (PrimeSpectrum.isIrreducible_zeroLocus_iff I).mp (hI ▸ hirr), ?_⟩
    rw [PrimeSpectrum.zeroLocus_radical]
    exact hI
  · rintro ⟨p, hp, rfl⟩
    exact ⟨PrimeSpectrum.isClosed_zeroLocus _, by
      rw [PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical p hp.isRadical]
      exact hp⟩

/-! ## Generic points and sobriety -/

/-- A `T₀` space has at most one generic point for an irreducible closed set. -/
theorem generic_point_unique_in_t0 {X : Type u} [TopologicalSpace X] [T0Space X]
    {T : Set X} (_hT : IsIrreducible T) (_hclosed : IsClosed T)
    {x y : X} (hx : IsGenericPoint x T) (hy : IsGenericPoint y T) :
    x = y := by
  exact hx.eq hy

/-- Every irreducible closed subset of an affine spectrum has a generic point. -/
theorem spectrum_irreducible_closed_has_generic_point {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) (hT : IsIrreducible T) (hclosed : IsClosed T) :
    ∃ x, IsGenericPoint x T := by
  exact QuasiSober.sober hT hclosed

/-- The canonical bijection between points and irreducible closed subsets of
an affine spectrum. -/
noncomputable def spectrum_points_irreducible_closed_equiv {A : Type u} [CommRing A] :
    PrimeSpectrum A ≃o
      (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ :=
  PrimeSpectrum.pointsEquivIrreducibleCloseds A

/-- The underlying set map sends a prime to the closure of its singleton. -/
theorem spectrum_point_closure_bijective {A : Type u} [CommRing A] :
    Function.Bijective
      (fun p : PrimeSpectrum A =>
        (⟨closure ({p} : Set (PrimeSpectrum A)),
          isIrreducible_singleton.closure, isClosed_closure⟩ :
          TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A))) := by
  exact (PrimeSpectrum.pointsEquivIrreducibleCloseds A).toEquiv.bijective

/-! ## A non-generic irreducible subset of `Spec(ℤ)` -/

/-- The closed points of `Spec(ℤ)`, viewed as a subset of its spectrum. -/
def integerClosedPoints : Set (PrimeSpectrum ℤ) :=
  {p | p.asIdeal ≠ (⊥ : Ideal ℤ)}

/-- The closed-point subset of `Spec(ℤ)` is irreducible but has no generic
point in the subspace. -/
theorem integer_closed_points_irreducible_no_generic :
    IsIrreducible integerClosedPoints ∧
      ¬ ∃ x, IsGenericPoint x integerClosedPoints := by
  sorry

end Formalization.Books.Exercises.Unit06
