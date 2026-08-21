import Formalization.Books.Algebra.Unit66.LocalizedRadical

namespace Formalization.Books.Algebra.Unit66

open Set
open scoped TensorProduct
noncomputable section

set_option linter.style.haveILetI false

/-- The contraction is weakly associated to the tensor module when the
relevant global and local residue tensors are domains. -/
theorem weaklyAssociatedPrime_tensor_change_fields_of_local_domain
    {k F R M : Type*} [Field k] [Field F] [Algebra k F]
    [CommRing R] [Algebra k R] [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R)
    (hdomBase : IsDomain ((R ⧸ p.asIdeal) ⊗[k] F))
    (hdom : IsDomain
      (((Localization.AtPrime p.asIdeal) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) ⊗[k] F))
    (q : PrimeSpectrum (R ⊗[k] F))
    (hpq : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] F) q = p)
    (hq : q ∈ weaklyAssociatedPrimes (R ⊗[k] F)
      (TensorProduct R (R ⊗[k] F) M)) :
    p ∈ weaklyAssociatedPrimes R (TensorProduct R (R ⊗[k] F) M) := by
  let S := p.asIdeal.primeCompl
  let A := Localization S
  let B := R ⊗[k] F
  let C := A ⊗[k] F
  let X := TensorProduct R B M
  let Mp := LocalizedModule S M
  let g := Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom k R A) (AlgHom.id k F)
  letI : Algebra B C := g.toRingHom.toAlgebra
  letI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap R A r ⊗ₜ[k] (1 : F) = g (r ⊗ₜ[k] (1 : F))
    simp [g])
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B S) C := by
    apply IsLocalization.tensorProduct_tensorProduct k F S A
    ext x
    simp [g, RingHom.algebraMap_toAlgebra]
  let gR : B →ₗ[R] C :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro r b
        induction b using TensorProduct.induction_on with
        | zero => simp
        | tmul a x =>
            change g ((r * a) ⊗ₜ[k] x) = r • ((algebraMap R A a) ⊗ₜ[k] x)
            rw [Algebra.TensorProduct.map_tmul, map_mul]
            simpa [Algebra.smul_def] using
              (TensorProduct.smul_tmul' (R := k) (R' := A)
                (algebraMap R A r) (algebraMap R A a) x).symm
        | add x y hx hy => simp [smul_add, hx, hy] }
  have hgR : IsLocalizedModule S gR := by
    rw [isLocalizedModule_iff_isBaseChange S A]
    exact (Algebra.isPushout_of_isLocalization (A := A) S B C).symm.out
  letI : IsLocalizedModule S gR := hgR
  let phi : X →ₗ[R] TensorProduct R C M := gR.rTensor M
  haveI hphi : IsLocalizedModule S phi := by
    exact IsLocalizedModule.rTensor R S gR
  let eMp : Mp ≃ₗ[A] TensorProduct R A M :=
    LocalizedModule.equivTensorProduct S M
  letI : Algebra A C := Algebra.TensorProduct.leftAlgebra
  letI : IsScalarTower A C C := by infer_instance
  let eCongr : TensorProduct A C Mp ≃ₗ[C]
      TensorProduct A C (TensorProduct R A M) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) eMp
  let eCancel : TensorProduct A C (TensorProduct R A M) ≃ₗ[C]
      TensorProduct R C M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A C C M
  let e : TensorProduct A C Mp ≃ₗ[C] TensorProduct R C M := eCongr.trans eCancel
  have hphi_smul (b : B) (x : X) : phi (b • x) = g b • phi x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
        change g (b * c) ⊗ₜ[R] m = g b • (g c ⊗ₜ[R] m)
        rw [map_mul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => simp [smul_add, hx, hy]
  have hnotmax (b : B)
      (hb : b ∉ p.asIdeal.map
        (Algebra.TensorProduct.includeLeftRingHom : R →+* B)) :
      g b ∉ (IsLocalRing.maximalIdeal A).map
        (Algebra.TensorProduct.includeLeftRingHom : A →+* C) := by
    exact pureTrans_tensorMap_notMem_local_max p hdomBase b hb
  rcases hq with ⟨z, hz⟩
  let eLoc : LocalizedModule S X ≃ₗ[A] TensorProduct R C M :=
    (IsLocalizedModule.iso S phi).extendScalarsOfIsLocalization S A
  let d : LocalizedModule S X ≃ₗ[A] TensorProduct A C Mp :=
    eLoc.trans (e.symm.restrictScalars A)
  let zLoc : LocalizedModule S X := eLoc.symm (phi z)
  let zA : TensorProduct A C Mp := e.symm (phi z)
  have hdz : d zLoc = zA := by simp [d, zLoc, zA, eLoc]
  have hzAne : zA ≠ 0 := by
    intro hz0
    have hphiz : phi z = 0 := by
      apply e.symm.injective
      simpa [zA] using hz0
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff S phi).mp hphiz
    have hsmap :
        (Algebra.TensorProduct.includeLeftRingHom : R →+* B) s ∈ q.asIdeal := by
      apply hz.le
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact (IsScalarTower.algebraMap_smul B (s : R) z).trans (by
        simpa only [Submonoid.smul_def] using hs)
    have hscomap : (s : R) ∈ q.asIdeal.comap
        (Algebra.TensorProduct.includeLeftRingHom : R →+* B) := hsmap
    have hcomap : q.asIdeal.comap
        (Algebra.TensorProduct.includeLeftRingHom : R →+* B) = p.asIdeal := by
      simpa only [PrimeSpectrum.comap_asIdeal] using
        congrArg PrimeSpectrum.asIdeal hpq
    rw [hcomap] at hscomap
    exact s.2 hscomap
  apply ((weaklyAssociated_local (M := X) p).out 0 2).mpr
  change ∃ zLoc : LocalizedModule S X,
    (((⊥ : Submodule A (LocalizedModule S X)).colon ({zLoc} : Set _)).radical =
      (IsLocalRing.closedPoint A).asIdeal)
  refine ⟨zLoc, ?_⟩
  let J : Ideal A :=
    (⊥ : Submodule A (TensorProduct A C Mp)).colon ({zA} : Set _)
  have hcolon :
      (⊥ : Submodule A (LocalizedModule S X)).colon ({zLoc} : Set _) = J := by
    ext a
    simp only [J, Submodule.mem_colon_singleton, Submodule.mem_bot]
    constructor
    · intro ha
      calc
        a • zA = a • d zLoc := by rw [hdz]
        _ = d (a • zLoc) := (d.map_smul a zLoc).symm
        _ = 0 := by rw [ha, map_zero]
    · intro ha
      apply d.injective
      rw [d.map_smul, hdz, ha, map_zero]
  rw [hcolon]
  have hJle : J ≤ IsLocalRing.maximalIdeal A := by
    apply IsLocalRing.le_maximalIdeal
    intro htop
    have : zA = 0 := by
      have hzmem : zA ∈ (⊥ : Submodule A (TensorProduct A C Mp)) :=
        (Submodule.colon_eq_top_iff_subset ({zA} : Set _)).mp htop (by simp)
      simpa using hzmem
    exact hzAne this
  have hmaxrad : IsLocalRing.maximalIdeal A ≤ J.radical := by
    let psi : X →+ TensorProduct A C Mp :=
      { toFun := fun x => e.symm (phi x)
        map_zero' := by simp
        map_add' := by intro x y; simp }
    apply maximalIdeal_le_radical_annihilator_of_regular p
      (Algebra.TensorProduct.includeLeftRingHom : R →+* B) g.toRingHom q hpq z hz
      psi zA
    · rfl
    · exact fun b x => by
        change e.symm (phi (b • x)) = g b • e.symm (phi x)
        rw [hphi_smul, e.symm.map_smul]
    · intro r
      change (algebraMap R A r) ⊗ₜ[k] (1 : F) =
        (algebraMap R A r) ⊗ₜ[k] (1 : F)
      rfl
    · intro b hb
      exact pureTrans_local_regular (k := k) (F := F) (R := A) (M := Mp)
        hdom (g b) (hnotmax b hb)
  exact le_antisymm
    ((Ideal.IsPrime.radical_le_iff
      (IsLocalRing.maximalIdeal.isMaximal A).isPrime).mpr hJle) hmaxrad

end
end Formalization.Books.Algebra.Unit66
