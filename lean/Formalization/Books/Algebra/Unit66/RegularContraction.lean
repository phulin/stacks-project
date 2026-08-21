import Formalization.Books.Algebra.Unit66.WeaklyAssociatedPrimes

namespace Formalization.Books.Algebra.Unit66

open Set

set_option linter.style.haveILetI false

/-- A weakly associated prime contracts when every element outside the
extended prime acts regularly. -/
theorem weaklyAssociatedPrime_contract_of_regular
    {R B X : Type*} [CommRing R] [CommRing B]
    [AddCommGroup X] [Module B X] (f : R →+* B)
    (q : PrimeSpectrum B) (p : PrimeSpectrum R)
    (hpq : PrimeSpectrum.comap f q = p)
    (hq : q ∈ weaklyAssociatedPrimes B X)
    (hreg : ∀ b : B, b ∉ p.asIdeal.map f → IsSMulRegular X b) :
    letI : Module R X := Module.compHom X f
    p ∈ weaklyAssociatedPrimes R X := by
  letI : Module R X := Module.compHom X f
  rcases hq with ⟨z, hz⟩
  let IR : Ideal R := (⊥ : Submodule R X).colon ({z} : Set X)
  let IB : Ideal B := (⊥ : Submodule B X).colon ({z} : Set X)
  have hcomap : q.asIdeal.comap f = p.asIdeal := by
    simpa only [PrimeSpectrum.comap_asIdeal] using
      congrArg (fun x : PrimeSpectrum R => x.asIdeal) hpq
  have hIRle : IR ≤ p.asIdeal := by
    intro r hr
    have hrB : f r ∈ q.asIdeal := by
      apply hz.1.2
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      change r • z = 0
      simpa [IR, Submodule.mem_colon_singleton, Submodule.mem_bot] using hr
    have : r ∈ q.asIdeal.comap f := hrB
    rw [hcomap] at this
    exact this
  have hpRad : p.asIdeal ≤ IR.radical := by
    intro r hr
    have hrq : f r ∈ q.asIdeal := by
      have hr' : r ∈ q.asIdeal.comap f := by
        rw [hcomap]
        exact hr
      exact hr'
    let A := Localization.AtPrime (R := B) q.asIdeal
    have hradloc :
        (IB.map (algebraMap B A)).radical =
          q.asIdeal.map (algebraMap B A) := by
      exact IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
        (R := B) (A := A) q.asIdeal IB (by simpa [IB] using hz)
    have hmul (x : B) (hx : x ∈ q.asIdeal) :
        ∃ n : ℕ, ∃ g : B, g ∉ q.asIdeal ∧ g * x ^ n ∈ IB := by
      have hxloc : algebraMap B A x ∈
          (IB.map (algebraMap B A)).radical := by
        rw [hradloc]
        exact Ideal.mem_map_of_mem (algebraMap B A) hx
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hxloc
      have hpowloc : algebraMap B A (x ^ n) ∈
          IB.map (algebraMap B A) := by
        simpa only [map_pow] using hn
      obtain ⟨g, hg, hgmul⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff
          q.asIdeal.primeCompl A IB (x ^ n)).mp hpowloc
      exact ⟨n, g, by simpa using hg, hgmul⟩
    obtain ⟨n, g, hgq, hgr⟩ := hmul (f r) hrq
    have hgr0 : (g * (f r) ^ n) • z = 0 := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hgr
      exact hgr
    have hpow : (f r) ^ n • z = 0 := by
      have hmaple : p.asIdeal.map f ≤ q.asIdeal := by
        rw [Ideal.map_le_iff_le_comap, hcomap]
      have hgmap : g ∉ p.asIdeal.map f := by
        intro hg
        exact hgq (hmaple hg)
      exact (hreg g hgmap).right_eq_zero_of_smul (by
        simpa [mul_smul] using hgr0)
    have hpowR : r ^ n • z = 0 := by
      change f (r ^ n) • z = 0
      simpa only [map_pow] using hpow
    exact Ideal.mem_radical_iff.mpr ⟨n, by
      simpa [IR, Submodule.mem_colon_singleton, Submodule.mem_bot] using hpowR⟩
  have hrad : IR.radical = p.asIdeal := le_antisymm
    ((Ideal.IsPrime.radical_le_iff p.2).mpr hIRle) hpRad
  refine ⟨z, ⟨⟨p.2, hIRle⟩, ?_⟩⟩
  intro P hP hPle
  rw [← hrad]
  exact (Ideal.IsPrime.radical_le_iff hP.1).mpr (by simpa [IR] using hP.2)

end Formalization.Books.Algebra.Unit66
