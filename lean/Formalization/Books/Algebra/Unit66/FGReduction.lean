import Formalization.Books.Algebra.Unit66.IntermediateDescent

namespace Formalization.Books.Algebra.Unit66

open Set
open scoped TensorProduct

noncomputable section

/-- A weakly associated prime after arbitrary field extension is already
defined over a finitely generated intermediate coefficient field. -/
theorem exists_weaklyAssociatedPrime_over_fg_intermediateField
    {k K R M : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [AddCommGroup M] [Module R M]
    (q : PrimeSpectrum (R ⊗[k] K)) (p : PrimeSpectrum R)
    (hpq : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] K) q = p)
    (hq : q ∈ weaklyAssociatedPrimes (R ⊗[k] K)
      (TensorProduct R (R ⊗[k] K) M)) :
    ∃ L : IntermediateField k K, L.FG ∧
      ∃ qL : PrimeSpectrum (R ⊗[k] L),
        PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] L) qL = p ∧
        qL ∈ weaklyAssociatedPrimes (R ⊗[k] L)
          (TensorProduct R (R ⊗[k] L) M) := by
  obtain ⟨z, hz⟩ := hq
  obtain ⟨L, hLfg, zL, hzmap⟩ :=
    exists_fg_intermediateField_module_preimage z
  let f := Algebra.TensorProduct.map (AlgHom.id k R) L.val
  let qL : PrimeSpectrum (R ⊗[k] L) := PrimeSpectrum.comap f.toRingHom q
  have hqL : qL ∈ weaklyAssociatedPrimes (R ⊗[k] L)
      (TensorProduct R (R ⊗[k] L) M) :=
    weaklyAssociatedPrime_contract_intermediate_preimage L q z zL hzmap hz
  refine ⟨L, hLfg, qL, ?_, hqL⟩
  change (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] L) ∘
        PrimeSpectrum.comap f.toRingHom) q = p
  rw [← PrimeSpectrum.comap_comp]
  have hmaps : f.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] L) =
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] K) := by
    ext r
    simp [f]
  rw [hmaps]
  exact hpq

end
end Formalization.Books.Algebra.Unit66
