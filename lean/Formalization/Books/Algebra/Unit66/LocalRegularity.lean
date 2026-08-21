import Formalization.Books.Algebra.Unit66.PureTranscendental
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.TensorProduct.Free

namespace Formalization.Books.Algebra.Unit66

open Set
open scoped TensorProduct

noncomputable section

theorem pureTrans_local_regular
    {k F R M : Type*} [Field k] [Field F] [Algebra k F]
    [CommRing R] [IsLocalRing R] [Algebra k R]
    [AddCommGroup M] [Module R M]
    (hdom : IsDomain ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[k] F))
    (f : R ⊗[k] F)
    (hf : f ∉ (IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] F)) :
    IsSMulRegular (TensorProduct R (R ⊗[k] F) M) f := by
  classical
  let B := R ⊗[k] F
  let κ := R ⧸ IsLocalRing.maximalIdeal R
  let C := κ ⊗[k] F
  let bF := Module.Free.chooseBasis k F
  let bB := Algebra.TensorProduct.basis R bF
  let eB : TensorProduct R B M ≃ₗ[R]
      ((Module.Free.ChooseBasisIndex k F) →₀ M) :=
    TensorProduct.equivFinsuppOfBasisLeft bB
  intro x y hxy
  let z := x - y
  have hz : f • z = 0 := by
    change f • x = f • y at hxy
    change f • (x - y) = 0
    rw [smul_sub, hxy, sub_self]
  let w := eB z
  let N : Submodule R M :=
    Submodule.span R (w '' (w.support : Set _))
  let liftN (m : M) : N :=
    if hm : m ∈ N then ⟨m, hm⟩ else 0
  let wN : (Module.Free.ChooseBasisIndex k F) →₀ N :=
    w.mapRange liftN (by simp [liftN])
  let eBN : TensorProduct R B N ≃ₗ[R]
      ((Module.Free.ChooseBasisIndex k F) →₀ N) :=
    TensorProduct.equivFinsuppOfBasisLeft bB
  let zN : TensorProduct R B N := eBN.symm wN
  have hcomm (x : TensorProduct R B N) :
      eB (N.subtype.lTensor B x) =
        Finsupp.mapRange.linearMap N.subtype (eBN x) := by
    induction x with
    | zero => simp
    | tmul b n =>
        ext i
        simp [eB, eBN, bB]
    | add x y hx hy =>
        rw [map_add, map_add, map_add, hx, hy]
        exact ((Finsupp.mapRange.linearMap N.subtype).map_add _ _).symm
  have hwN : Finsupp.mapRange.linearMap N.subtype wN = w := by
    ext i
    have hwi : w i ∈ N := by
      by_cases hi : i ∈ w.support
      · exact Submodule.subset_span ⟨i, hi, rfl⟩
      · simp [Finsupp.notMem_support_iff.mp hi]
    simp [wN, liftN, hwi]
  have hzN : N.subtype.lTensor B zN = z := by
    apply eB.injective
    rw [hcomm]
    change Finsupp.mapRange.linearMap N.subtype (eBN (eBN.symm wN)) = w
    rw [eBN.apply_symm_apply]
    exact hwN
  have hincl : Function.Injective (N.subtype.lTensor B) :=
    fun x y hxy => by
      apply eBN.injective
      apply Finsupp.ext
      intro i
      apply Subtype.ext
      have h := congrArg eB hxy
      rw [hcomm, hcomm] at h
      exact congrArg (fun v => v i) h
  have hsmul (t : TensorProduct R B N) :
      N.subtype.lTensor B (f • t) = f • (N.subtype.lTensor B t) := by
    induction t with
    | zero => simp
    | tmul b n => simp [TensorProduct.smul_tmul']
    | add a b ha hb => simp [smul_add, ha, hb]
  have hzNzero : f • zN = 0 := by
    apply hincl
    rw [map_zero]
    rw [hsmul, hzN, hz]
  let qR : R →+* κ := Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
  let gAlg : B →ₐ[k] C := Algebra.TensorProduct.map
    (Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal R)) (AlgHom.id k F)
  let Q := N ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R N))
  let gSemi : B →ₛₗ[qR] C :=
    { toFun := gAlg
      map_add' := gAlg.map_add
      map_smul' := by
        intro r b
        induction b using TensorProduct.induction_on with
        | zero => simp
        | tmul a x =>
            change gAlg (r • a ⊗ₜ[k] x) = qR r • gAlg (a ⊗ₜ[k] x)
            simp only [gAlg]
            change (Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal R)) (r * a) ⊗ₜ[k]
                (AlgHom.id k F) x =
              qR r • ((Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal R)) a ⊗ₜ[k]
                (AlgHom.id k F) x)
            rw [TensorProduct.smul_tmul']
            simp [qR]
        | add x y hx hy => simp [smul_add, hx, hy] }
  have hQ : Module.IsTorsionBySet R Q (IsLocalRing.maximalIdeal R) := by
    rw [Module.isTorsionBySet_quotient_iff]
    intro n r hr
    exact Submodule.smul_mem_smul hr trivial
  letI : Field κ := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  letI : Module κ Q := hQ.module
  let qSemi : N →ₛₗ[qR] Q :=
    { toFun := Submodule.Quotient.mk
      map_add' := by intro a b; rfl
      map_smul' := by
        intro r n
        change Submodule.Quotient.mk (r • n) = qR r • Submodule.Quotient.mk n
        rw [hQ.mk_smul]
        rfl }
  let phi : TensorProduct R B N →ₛₗ[qR] TensorProduct κ C Q :=
    TensorProduct.map gSemi qSemi
  let eQuot := Algebra.TensorProduct.quotientTensorEquiv
    (R := k) k F R (IsLocalRing.maximalIdeal R)
  have heQuot (b : B) : eQuot (gAlg b) =
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map
          (Algebra.TensorProduct.includeLeftRingHom : R →+* B)) b := by
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        change eQuot
            ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) a) ⊗ₜ[k] x) =
          Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal R).map
              (Algebra.TensorProduct.includeLeftRingHom : R →+* B)) (a ⊗ₜ[k] x)
        rfl
    | add x y hx hy => simp [hx, hy]
  have hgf : gAlg f ≠ 0 := by
    intro hzero
    apply hf
    rw [← Submodule.Quotient.mk_eq_zero]
    calc
      Submodule.Quotient.mk f = eQuot (gAlg f) := (heQuot f).symm
      _ = 0 := by simp [hzero]
  have hphi_smul (b : B) (t : TensorProduct R B N) :
      phi (b • t) = gAlg b • phi t := by
    induction t with
    | zero => simp
    | tmul c n =>
        simp [phi, gSemi, qSemi, TensorProduct.smul_tmul']
    | add x y hx hy => simp [smul_add, hx, hy]
  letI : IsDomain C := hdom
  let bQ := Module.Free.chooseBasis κ Q
  let eCQ : TensorProduct κ C Q ≃ₗ[κ]
      ((Module.Free.ChooseBasisIndex κ Q) →₀ C) :=
    TensorProduct.equivFinsuppOfBasisRight bQ
  have heCQ_smul (c : C) (t : TensorProduct κ C Q) :
      eCQ (c • t) = c • eCQ t := by
    induction t with
    | zero => simp
    | tmul a q =>
        rw [TensorProduct.smul_tmul']
        ext i
        simp only [eCQ, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
          Finsupp.smul_apply]
        change (bQ.repr q) i • (c * a) = c * ((bQ.repr q) i • a)
        exact (Algebra.mul_smul_comm ((bQ.repr q) i) c a).symm
    | add x y hx hy => simp [smul_add, hx, hy]
  have hphi_zero : phi zN = 0 := by
    have hmapped := congrArg phi hzNzero
    rw [map_zero, hphi_smul] at hmapped
    apply eCQ.injective
    apply Finsupp.ext
    intro i
    simp only [map_zero, Finsupp.zero_apply]
    have hi := congrArg (fun v => eCQ v i) hmapped
    rw [heCQ_smul, map_zero, Finsupp.smul_apply] at hi
    have hi' : gAlg f * (eCQ (phi zN)) i = 0 := by
      simpa [smul_eq_mul] using hi
    exact (mul_eq_zero.mp hi').resolve_left hgf
  let bC := Algebra.TensorProduct.basis κ bF
  let eCN : TensorProduct κ C Q ≃ₗ[κ]
      ((Module.Free.ChooseBasisIndex k F) →₀ Q) :=
    TensorProduct.equivFinsuppOfBasisLeft bC
  have hrepr (b : B) (i : Module.Free.ChooseBasisIndex k F) :
      (bC.repr (gAlg b)) i = qR ((bB.repr b) i) := by
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        have hg : gAlg (a ⊗ₜ[k] x) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) a ⊗ₜ[k] x := rfl
        rw [hg]
        simp [bC, bB, qR]
        left
        exact ((Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal R)).commutes _).symm
    | add x y hx hy => simp [hx, hy]
  have hphi_comm (t : TensorProduct R B N) :
      eCN (phi t) = Finsupp.mapRange.linearMap qSemi (eBN t) := by
    induction t with
    | zero => simp
    | tmul b n =>
        ext i
        simp only [eCN, eBN, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
          phi, TensorProduct.map_tmul, gSemi, qSemi,
          Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
        change (bC.repr (gAlg b)) i • qSemi n =
          qSemi ((bB.repr b) i • n)
        rw [hrepr]
        exact (qSemi.map_smulₛₗ (bB.repr b i) n).symm
    | add x y hx hy =>
        rw [map_add, map_add, map_add, hx, hy]
        exact ((Finsupp.mapRange.linearMap qSemi).map_add _ _).symm
  have hwQ : Finsupp.mapRange.linearMap qSemi wN = 0 := by
    rw [← eBN.apply_symm_apply wN, ← hphi_comm]
    simp [zN, hphi_zero]
  have hcoeff (i : Module.Free.ChooseBasisIndex k F) :
      w i ∈ IsLocalRing.maximalIdeal R • N := by
    have hwi : w i ∈ N := by
      by_cases hi : i ∈ w.support
      · exact Submodule.subset_span ⟨i, hi, rfl⟩
      · simp [Finsupp.notMem_support_iff.mp hi]
    have hkernel : wN i ∈
        IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change qSemi (wN i) = 0
      have hi := congrArg (fun v => v i) hwQ
      simpa using hi
    have himage : N.subtype (wN i) ∈
        IsLocalRing.maximalIdeal R • N := by
      exact Submodule.smul_induction_on hkernel
        (fun r hr n _ => by
          change r • (n : M) ∈ IsLocalRing.maximalIdeal R • N
          exact Submodule.smul_mem_smul hr n.property)
        (fun _ _ ha hb => add_mem ha hb)
    simpa [wN, liftN, hwi] using himage
  have hwzero : w = 0 :=
    finsupp_eq_zero_of_coeff_mem_maximalIdeal_smul_span w hcoeff
  have hz0 : z = 0 := by
    apply eB.injective
    simpa [w] using hwzero
  exact sub_eq_zero.mp (by simpa [z] using hz0)

end

end Formalization.Books.Algebra.Unit66
