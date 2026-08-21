import Formalization.Books.Algebra.Unit66.PureTransDomain

namespace Formalization.Books.Algebra.Unit66
open Set
open scoped TensorProduct
noncomputable section

set_option linter.style.haveILetI false

/-- Weak association descends through a purely transcendental coefficient
field extension. -/
theorem weaklyAssociatedPrimes_change_fields_pureTrans
    {k K R M ι : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [AddCommGroup M] [Module R M]
    {x : ι → K} (hx : AlgebraicIndependent k x)
    (q : PrimeSpectrum (R ⊗[k] IntermediateField.adjoin k (Set.range x)))
    (p : PrimeSpectrum R)
    (hpq : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom :
        R →+* R ⊗[k] IntermediateField.adjoin k (Set.range x)) q = p)
    (hq : q ∈ weaklyAssociatedPrimes
      (R ⊗[k] IntermediateField.adjoin k (Set.range x))
      (TensorProduct R
        (R ⊗[k] IntermediateField.adjoin k (Set.range x)) M)) :
    p ∈ weaklyAssociatedPrimes R M := by
  let F := IntermediateField.adjoin k (Set.range x)
  have hdomBase : IsDomain ((R ⧸ p.asIdeal) ⊗[k] F) :=
    isDomain_tensorProduct_adjoin_of_algebraicIndependent_of_domain hx
  let A := Localization.AtPrime p.asIdeal
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  have hdomLocal : IsDomain
      (((Localization.AtPrime p.asIdeal) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) ⊗[k] F) :=
    isDomain_tensorProduct_adjoin_of_algebraicIndependent
      (k := k) (κ := A ⧸ IsLocalRing.maximalIdeal A) (K := K) hx
  have hpTensor : p ∈ weaklyAssociatedPrimes R (TensorProduct R (R ⊗[k] F) M) :=
    weaklyAssociatedPrime_tensor_change_fields_of_local_domain p hdomBase hdomLocal
      q (by simpa [F] using hpq) (by simpa [F] using hq)
  let b := Module.Free.chooseBasis k F
  let eB : (R ⊗[k] F) ≃ₗ[R]
      ((Module.Free.ChooseBasisIndex k F) →₀ R) :=
    Algebra.TensorProduct.equivFinsuppOfBasis R b
  let eP : TensorProduct R (R ⊗[k] F) M ≃ₗ[R]
      TensorProduct R ((Module.Free.ChooseBasisIndex k F) →₀ R) M :=
    LinearEquiv.rTensor M eB
  let eF : TensorProduct R ((Module.Free.ChooseBasisIndex k F) →₀ R) M ≃ₗ[R]
      ((Module.Free.ChooseBasisIndex k F) →₀ M) :=
    TensorProduct.equivFinsuppOfBasisLeft
      (Finsupp.basisSingleOne
        (R := R) (ι := Module.Free.ChooseBasisIndex k F))
  have hpFinsupp : p ∈ weaklyAssociatedPrimes R
      ((Module.Free.ChooseBasisIndex k F) →₀ M) :=
    (weaklyAssociatedPrimes_linearEquiv (eP.trans eF) p).1 hpTensor
  exact weaklyAssociatedPrimes_finsupp p hpFinsupp

end
end Formalization.Books.Algebra.Unit66
