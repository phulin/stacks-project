import Formalization.Books.Algebra.Unit66.PureTransLocalization

namespace Formalization.Books.Algebra.Unit66
open Set

/-- Local regularity turns a minimal annihilator upstairs into the radical
annihilator of the closed point after localization. -/
theorem maximalIdeal_le_radical_annihilator_of_regular
    {R B A C X Z : Type*}
    [CommRing R] [CommRing B] [CommRing A] [CommRing C]
    (p : PrimeSpectrum R)
    [IsLocalRing A] [Algebra R A] [IsLocalization.AtPrime A p.asIdeal]
    [AddCommGroup X] [Module B X]
    [AddCommGroup Z] [Module C Z] [Module A Z] [Algebra A C]
    [IsScalarTower A C Z]
    (f : R →+* B) (g : B →+* C)
    (q : PrimeSpectrum B)
    (hpq : PrimeSpectrum.comap f q = p)
    (z : X)
    (hz : q.asIdeal ∈
      ((⊥ : Submodule B X).colon ({z} : Set X)).minimalPrimes)
    (ψ : X →+ Z) (zA : Z) (hψz : ψ z = zA)
    (hψsmul : ∀ (b : B) (x : X), ψ (b • x) = g b • ψ x)
    (hginc : ∀ r : R, g (f r) = algebraMap A C (algebraMap R A r))
    (hreg : ∀ b : B, b ∉ p.asIdeal.map f → IsSMulRegular Z (g b)) :
    IsLocalRing.maximalIdeal A ≤
      ((⊥ : Submodule A Z).colon ({zA} : Set Z)).radical := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal A,
    Ideal.map_le_iff_le_comap]
  intro r hr
  have hcomap : q.asIdeal.comap f = p.asIdeal := by
    simpa only [PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal hpq
  have hrq : f r ∈ q.asIdeal := by
    apply (show r ∈ q.asIdeal.comap f by rw [hcomap]; exact hr)
  let IB : Ideal B := (⊥ : Submodule B X).colon ({z} : Set X)
  let Lq := Localization.AtPrime (R := B) q.asIdeal
  have hradloc :
      (IB.map (algebraMap B Lq)).radical =
        q.asIdeal.map (algebraMap B Lq) := by
    exact IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      (R := B) (A := Lq) q.asIdeal IB (by simpa [IB] using hz)
  have hxloc : algebraMap B Lq (f r) ∈
      (IB.map (algebraMap B Lq)).radical := by
    rw [hradloc]
    exact Ideal.mem_map_of_mem _ hrq
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hxloc
  have hpowloc : algebraMap B Lq ((f r) ^ n) ∈
      IB.map (algebraMap B Lq) := by
    simpa only [map_pow] using hn
  obtain ⟨b, hbq, hbmul⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      q.asIdeal.primeCompl Lq IB ((f r) ^ n)).mp hpowloc
  have hbzero : (b * (f r) ^ n) • z = 0 := by
    simpa [IB, Submodule.mem_colon_singleton, Submodule.mem_bot] using hbmul
  have hbnot : b ∉ p.asIdeal.map f := by
    intro hb
    have hmaple : p.asIdeal.map f ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap, hcomap]
    exact hbq (hmaple hb)
  have hmapped := congrArg ψ hbzero
  rw [map_zero, hψsmul, map_mul, map_pow, hginc, mul_smul, hψz] at hmapped
  rw [← map_pow] at hmapped
  have hinner : algebraMap A C ((algebraMap R A r) ^ n) • zA =
      (algebraMap R A r) ^ n • zA :=
    IsScalarTower.algebraMap_smul C _ _
  have hlocalzero : g b • ((algebraMap R A r) ^ n • zA) = 0 := by
    rw [← hinner]
    simpa only [map_zero] using hmapped
  have hpowzero : (algebraMap R A r) ^ n • zA = 0 :=
    (hreg b hbnot).right_eq_zero_of_smul hlocalzero
  exact Ideal.mem_radical_iff.mpr ⟨n, by
    simpa [Submodule.mem_colon_singleton, Submodule.mem_bot] using hpowzero⟩

end Formalization.Books.Algebra.Unit66
