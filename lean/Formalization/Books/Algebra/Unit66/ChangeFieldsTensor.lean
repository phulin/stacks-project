import Formalization.Books.Algebra.Unit66.FGReduction
import Formalization.Books.Algebra.Unit66.PureTransDescent

namespace Formalization.Books.Algebra.Unit66
open Set
open scoped TensorProduct
noncomputable section

set_option linter.style.haveILetI false

/-- The standard tensor-product form of change-of-coefficient-fields
descent for weakly associated primes. -/
theorem weaklyAssociatedPrimes_change_fields_tensor
    {k K R M : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [AddCommGroup M] [Module R M]
    (q : PrimeSpectrum (R ⊗[k] K)) (p : PrimeSpectrum R)
    (hpq : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] K) q = p)
    (hq : q ∈ weaklyAssociatedPrimes (R ⊗[k] K)
      (TensorProduct R (R ⊗[k] K) M)) :
    p ∈ weaklyAssociatedPrimes R M := by
  obtain ⟨L, hLfg, qL, hqLmap, hqL⟩ :=
    exists_weaklyAssociatedPrime_over_fg_intermediateField q p hpq hq
  have htopfg : (⊤ : IntermediateField k L).FG := by
    exact IntermediateField.fg_top_iff.mpr
      (IntermediateField.essFiniteType_iff.mpr hLfg)
  obtain ⟨s, hsfin, hs, hfinite⟩ :=
    exists_finite_transcendenceBasis_of_fg htopfg
  have hrange : Set.range ((↑) : s → L) = s := Subtype.range_val
  let F : IntermediateField k L :=
    IntermediateField.adjoin k (Set.range ((↑) : s → L))
  have hF : F = IntermediateField.adjoin k s := by simp [F, hrange]
  letI : Module.Finite F L := hF.symm ▸ hfinite
  let f := Algebra.TensorProduct.map (AlgHom.id k R) F.val
  letI : Module (R ⊗[k] F) (TensorProduct R (R ⊗[k] L) M) :=
    Module.compHom _ f.toRingHom
  obtain ⟨qF, hqFmap, hqF⟩ :=
    exists_weaklyAssociatedPrime_over_finite_intermediateField
      F qL p hqLmap hqL
  have hqFstd : qF ∈ weaklyAssociatedPrimes (R ⊗[k] F)
      (TensorProduct R (R ⊗[k] F) M) := by
    exact weaklyAssociatedPrimes_descend_finite_intermediateField_module
      (k := k) (F := F) (K := L) (R := R) (M := M) qF hqF
  have hs' : AlgebraicIndependent k ((↑) : s → L) := hs.1
  exact weaklyAssociatedPrimes_change_fields_pureTrans hs' qF p hqFmap hqFstd

end
end Formalization.Books.Algebra.Unit66
