import Formalization.Books.Topology.Unit08.IrreducibleComponents
import Formalization.Books.Topology.Unit22.ProfiniteSpaces
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 26: Irreducible components of spectra

The canonical Mathlib notions `PrimeSpectrum.zeroLocus`, `IsIrreducible`,
`irreducibleComponents`, and `IsProfiniteSpace` are used for the statements in
this chapter.  The unfinished ninth item in the final source list is not
translated into a mathematical proposition below.
-/

namespace Formalization.Books.Algebra.Unit26

open Set _root_.Topology

universe u

/-! ## Irreducible components of spectra -/

section Irreducible

variable {R : Type u} [CommRing R]

/-! ### Closure of a prime and irreducible closed subsets -/

/-- The closure of a point of the prime spectrum is its vanishing locus. -/
theorem closure_singleton_prime (p : PrimeSpectrum R) :
    closure ({p} : Set (PrimeSpectrum R)) =
      PrimeSpectrum.zeroLocus (p.asIdeal : Set R) :=
  PrimeSpectrum.closure_singleton p

/-- The irreducible closed subsets of a prime spectrum are the vanishing
loci of prime ideals. -/
theorem isClosed_and_isIrreducible_iff_zeroLocus_prime
    (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ∧ IsIrreducible Z ↔
      ∃ p : PrimeSpectrum R,
        Z = PrimeSpectrum.zeroLocus (p.asIdeal : Set R) := by
  constructor
  · rintro ⟨hZclosed, hZirreducible⟩
    let P : Ideal R := PrimeSpectrum.vanishingIdeal Z
    have hPprime : P.IsPrime :=
      (PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime).mp hZirreducible
    refine ⟨⟨P, hPprime⟩, ?_⟩
    exact hZclosed.closure_eq.symm.trans
      (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Z).symm
  · rintro ⟨p, rfl⟩
    refine ⟨PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
    rw [← PrimeSpectrum.closure_singleton p]
    exact isIrreducible_singleton.closure

/-- The irreducible components of a prime spectrum are exactly the vanishing
loci of its minimal prime ideals. -/
theorem zeroLocus_minimalPrimes_eq_irreducibleComponents :
    PrimeSpectrum.zeroLocus ∘ (↑) '' minimalPrimes R =
      irreducibleComponents (PrimeSpectrum R) := by
  exact PrimeSpectrum.zeroLocus_minimalPrimes R

/-! The source's accompanying generic-point assertion. -/

/-- Every irreducible closed subset of a prime spectrum has a unique generic
point. -/
theorem irreducibleClosed_existsUnique_genericPoint :
    ∀ Z : Set (PrimeSpectrum R), IsIrreducible Z → IsClosed Z →
      ∃! p : PrimeSpectrum R, IsGenericPoint p Z := by
  exact
    (Formalization.Books.Topology.Unit08.quasiSober_and_t0_iff_unique_genericPoint
      (X := PrimeSpectrum R)).mp ⟨inferInstance, inferInstance⟩

/- The source's sober-space assertion is represented by Mathlib's canonical
`QuasiSober` and `T0Space` pair. -/
theorem primeSpectrum_is_sober :
    QuasiSober (PrimeSpectrum R) ∧ T0Space (PrimeSpectrum R) := by
  exact ⟨inferInstance, inferInstance⟩

/-! ### Spectrality -/

/-- The spectrum of a commutative ring is a spectral space. -/
theorem primeSpectrum_is_spectral : SpectralSpace (PrimeSpectrum R) := by
  infer_instance

/-! ### Components through a point -/

/-- Irreducible closed subsets through a prime correspond to primes of the
localization at that prime. -/
theorem irreducibleClosedSets_through_prime_correspond_localization
    (p : PrimeSpectrum R) :
    Nonempty
      ({Z : Set (PrimeSpectrum R) // IsClosed Z ∧ IsIrreducible Z ∧ p ∈ Z} ≃
        PrimeSpectrum (Localization.AtPrime p.asIdeal)) := by
  let e : Set.Iic p ≃
      {Z : Set (PrimeSpectrum R) // IsClosed Z ∧ IsIrreducible Z ∧ p ∈ Z} :=
    { toFun := fun q =>
        ⟨PrimeSpectrum.zeroLocus (q.1.asIdeal : Set R),
          PrimeSpectrum.isClosed_zeroLocus _,
          by
            rw [← PrimeSpectrum.closure_singleton q.1]
            exact isIrreducible_singleton.closure,
          (PrimeSpectrum.mem_zeroLocus p _).2 q.2⟩
      invFun := fun Z =>
        ⟨⟨PrimeSpectrum.vanishingIdeal Z.1,
            (PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp Z.2.2.1)⟩,
          (PrimeSpectrum.mem_zeroLocus p _).1 <|
            (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Z.1).symm ▸ by
              rw [Z.2.1.closure_eq]
              exact Z.2.2.2⟩
      left_inv := fun q => by
        apply Subtype.ext
        apply PrimeSpectrum.ext
        dsimp
        change PrimeSpectrum.vanishingIdeal
            (PrimeSpectrum.zeroLocus (q.1.asIdeal : Set R)) = q.1.asIdeal
        rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
        exact q.1.2.radical
      right_inv := fun Z => by
        apply Subtype.ext
        exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Z.1).trans
          Z.2.1.closure_eq }
  exact ⟨e.symm.trans (IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.asIdeal) p.asIdeal).symm⟩

/-- Irreducible components through a prime correspond to minimal primes of the
localization at that prime. -/
theorem irreducibleComponents_through_prime_correspond_minimalPrimes_localization
    (p : PrimeSpectrum R) :
    Nonempty
      ({C : Set (PrimeSpectrum R) //
          C ∈ irreducibleComponents (PrimeSpectrum R) ∧ p ∈ C} ≃
        {q : PrimeSpectrum (Localization.AtPrime p.asIdeal) //
          q.asIdeal ∈ minimalPrimes (Localization.AtPrime p.asIdeal)}) := by
  let e :
      {C : Set (PrimeSpectrum R) //
          C ∈ irreducibleComponents (PrimeSpectrum R) ∧ p ∈ C} ≃
        {q : Set.Iic p // q.1.asIdeal ∈ minimalPrimes R} :=
    { toFun := fun C =>
        ⟨⟨⟨PrimeSpectrum.vanishingIdeal C.1,
              PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp C.2.1.1⟩,
            (PrimeSpectrum.mem_zeroLocus p _).1 <|
              (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure C.1).symm ▸ by
                rw [(Formalization.Books.Topology.Unit08.irreducibleComponent_isClosed C.2.1).closure_eq]
                exact C.2.2⟩,
          (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes).2 <|
            (Formalization.Books.Topology.Unit08.irreducibleComponent_isClosed C.2.1).closure_eq ▸ C.2.1⟩
      invFun := fun q =>
        ⟨PrimeSpectrum.zeroLocus (q.1.1.asIdeal : Set R),
          (PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents).2 <| by
            rw [q.1.1.2.radical]
            exact q.2,
          (PrimeSpectrum.mem_zeroLocus p _).2 q.1.2⟩
      left_inv := fun C => by
        apply Subtype.ext
        exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure C.1).trans
          (Formalization.Books.Topology.Unit08.irreducibleComponent_isClosed C.2.1).closure_eq
      right_inv := fun q => by
        apply Subtype.ext
        apply PrimeSpectrum.ext
        dsimp
        rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
        exact q.1.1.2.radical }
  let o := IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.asIdeal) p.asIdeal
  let m :
      {q : Set.Iic p // q.1.asIdeal ∈ minimalPrimes R} ≃
        {q : PrimeSpectrum (Localization.AtPrime p.asIdeal) //
          q.asIdeal ∈ minimalPrimes (Localization.AtPrime p.asIdeal)} :=
    { toFun := fun q =>
        ⟨o.symm q.1, by
          have h := IsLocalization.minimalPrimes_map p.asIdeal.primeCompl
            (Localization.AtPrime p.asIdeal) (⊥ : Ideal R)
          simpa [o] using (show q.1.asIdeal ∈ minimalPrimes R from q.2)⟩
      invFun := fun q =>
        ⟨o q.1, by
          have h := IsLocalization.minimalPrimes_map p.asIdeal.primeCompl
            (Localization.AtPrime p.asIdeal) (⊥ : Ideal R)
          simpa [o] using (show q.1.asIdeal ∈ minimalPrimes R from ?_)⟩
      left_inv := fun q => by simp [o]
      right_inv := fun q => by simp [o] }
  exact ⟨e.trans m⟩

/-! ### A standard open avoiding a minimal prime -/

/-- A quasi-compact open avoiding a minimal prime is disjoint from a standard
open containing that minimal prime. -/
theorem exists_basicOpen_disjoint_of_minimalPrime
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    {W : Set (PrimeSpectrum R)} (hWopen : IsOpen W) (hWcompact : IsCompact W)
    (hpW : p ∉ W) :
    ∃ f : R, f ∉ p.asIdeal ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩ W = ∅ := by
  sorry

/-! ### Rings with no nontrivial prime inclusions -/

/-- The eight substantive conditions listed in the source are equivalent for
the spectrum of a commutative ring. -/
theorem isProfinite_TFAE_primeSpectrum_separation_conditions :
    List.TFAE
      [Formalization.Books.Topology.Unit22.IsProfiniteSpace (PrimeSpectrum R),
        T2Space (PrimeSpectrum R),
        TotallyDisconnectedSpace (PrimeSpectrum R),
        (∀ U : Set (PrimeSpectrum R), IsOpen U → IsCompact U → IsClosed U),
        (∀ p q : Ideal R, p.IsPrime → q.IsPrime → p ≤ q → p = q),
        (∀ p : Ideal R, p.IsPrime → p.IsMaximal),
        (∀ p : Ideal R, p.IsPrime → p ∈ minimalPrimes R),
        (∀ f : R, IsClosed (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)))] := by
  sorry

end Irreducible

end Formalization.Books.Algebra.Unit26
