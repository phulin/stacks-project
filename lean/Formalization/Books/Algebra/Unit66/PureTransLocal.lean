import Formalization.Books.Algebra.Unit66.RegularContraction
import Formalization.Books.Algebra.Unit66.LocalRegularity

namespace Formalization.Books.Algebra.Unit66

open Set
open scoped TensorProduct

set_option linter.style.haveILetI false

/-- Change of coefficient field at a local ring, provided the residue-field
tensor product is a domain. -/
theorem weaklyAssociatedPrimes_change_fields_local_of_domain
    {k F R M : Type*} [Field k] [Field F] [Algebra k F]
    [CommRing R] [IsLocalRing R] [Algebra k R]
    [AddCommGroup M] [Module R M]
    (hdom : IsDomain ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[k] F))
    (q : PrimeSpectrum (R ⊗[k] F))
    (hqmap : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] F) q =
        IsLocalRing.closedPoint R)
    (hq : q ∈ weaklyAssociatedPrimes (R ⊗[k] F)
      (TensorProduct R (R ⊗[k] F) M)) :
    IsLocalRing.closedPoint R ∈ weaklyAssociatedPrimes R M := by
  let B := R ⊗[k] F
  have hpTensor :
      (letI : Module R (TensorProduct R B M) :=
        Module.compHom _
          (Algebra.TensorProduct.includeLeftRingHom : R →+* B)
       IsLocalRing.closedPoint R ∈
        weaklyAssociatedPrimes R (TensorProduct R B M)) := by
    apply weaklyAssociatedPrime_contract_of_regular
      (Algebra.TensorProduct.includeLeftRingHom : R →+* B)
      q (IsLocalRing.closedPoint R) (by simpa [B] using hqmap) (by simpa [B] using hq)
    intro f hf
    apply pureTrans_local_regular hdom f
    simpa [IsLocalRing.closedPoint, B] using hf
  let b := Module.Free.chooseBasis k F
  let eB : B ≃ₗ[R] ((Module.Free.ChooseBasisIndex k F) →₀ R) :=
    Algebra.TensorProduct.equivFinsuppOfBasis R b
  let eCan : TensorProduct R B M ≃+
      TensorProduct R ((Module.Free.ChooseBasisIndex k F) →₀ R) M :=
    (LinearEquiv.rTensor M eB).toAddEquiv
  letI : Module R (TensorProduct R B M) :=
    Module.compHom _
      (Algebra.TensorProduct.includeLeftRingHom : R →+* B)
  let ePstd : TensorProduct R B M ≃ₗ[R]
      TensorProduct R ((Module.Free.ChooseBasisIndex k F) →₀ R) M :=
    { eCan with
      map_smul' := by
        intro r z
        change eCan
            ((Algebra.TensorProduct.includeLeftRingHom : R →+* B) r • z) =
          r • eCan z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a m =>
            simp only [eCan, TensorProduct.smul_tmul']
            have hr :
                (Algebra.TensorProduct.includeLeftRingHom : R →+* B) r • a = r • a := by
              rw [smul_eq_mul, Algebra.smul_def]
              rfl
            rw [hr]
            change (eB (r • a)) ⊗ₜ[R] m = r • ((eB a) ⊗ₜ[R] m)
            rw [eB.map_smul]
            exact (TensorProduct.smul_tmul' (R := R) (R' := R)
              r (eB a) m).symm
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }
  let eF : TensorProduct R ((Module.Free.ChooseBasisIndex k F) →₀ R) M ≃ₗ[R]
      ((Module.Free.ChooseBasisIndex k F) →₀ M) :=
    TensorProduct.equivFinsuppOfBasisLeft
      (Finsupp.basisSingleOne
        (R := R) (ι := Module.Free.ChooseBasisIndex k F))
  let eall : TensorProduct R B M ≃ₗ[R]
      ((Module.Free.ChooseBasisIndex k F) →₀ M) := ePstd.trans eF
  have hpFinsupp : IsLocalRing.closedPoint R ∈ weaklyAssociatedPrimes R
      ((Module.Free.ChooseBasisIndex k F) →₀ M) :=
    (weaklyAssociatedPrimes_linearEquiv eall _).1 hpTensor
  exact weaklyAssociatedPrimes_finsupp _ hpFinsupp

end Formalization.Books.Algebra.Unit66
