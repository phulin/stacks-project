import Formalization.Books.Algebra.Unit20.Nakayama
import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.Algebra.Unit99.CriteriaForFlatness
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.Ideal.Finsupp

/-!
# Commutative Algebra, Chapter 101: Flatness criteria over Artinian rings

The statements in this section use Mathlib's canonical flat, free, projective,
basis, quotient-module, residue-field, localization, and ring-hom flatness
interfaces.  Tor is the canonical construction recorded in Chapter 75.

The short exact sequences and tensor-product maps displayed inside the source
proofs are proof scaffolding for the theorem interfaces below, so they are not
duplicated as unreferenced declarations.
-/

namespace Formalization.Books.Algebra.Unit101

open CategoryTheory
open CategoryTheory.Limits
open Function
open scoped TensorProduct

noncomputable section

universe u

/-! ## Nilpotent local criteria -/

/-- An Artinian local ring has a nilpotent maximal ideal. -/
theorem artinian_local_maximalIdeal_isNilpotent
    {R : Type u} [CommRing R] [IsArtinianRing R] [IsLocalRing R] :
    IsNilpotent (IsLocalRing.maximalIdeal R) :=
  (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance

/- The ideal used in the preparation lemma is the contraction of the extension
   of `I ^ 2` along the given ring map. -/
def prepareIdeal {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') (I : Ideal R) : Ideal R :=
  Ideal.comap φ (Ideal.map φ (I ^ 2))

/- Mathlib packages a basis as a structure and does not take its vector
   family as a type parameter.  This predicate records the source's phrase
   that a specified family forms a basis. -/
def IsBasisFamily {R M A : Type u} [Semiring R] [AddCommMonoid M]
    [Module R M] (x : A → M) : Prop :=
  ∃ b : Module.Basis A R M, (b : A → M) = x

private noncomputable def quotTensorEquivQuotSMulAlg
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I]
      (M ⧸ (I • (⊤ : Submodule R M))) := by
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  let f : ((R ⧸ I) ⊗[R] M) →ₗ[R ⧸ I]
      (M ⧸ (I • (⊤ : Submodule R M))) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro a z
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z w hz hw => simp [map_add, hz, hw, smul_add]
        | tmul r' m =>
            obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r'
            change e ((Ideal.Quotient.mk I r * Ideal.Quotient.mk I r') ⊗ₜ[R] m) =
              Ideal.Quotient.mk I r • e ((Ideal.Quotient.mk I r') ⊗ₜ[R] m)
            have hmul : Ideal.Quotient.mk I r * Ideal.Quotient.mk I r' =
                Ideal.Quotient.mk I (r * r') := by simp
            calc
              e ((Ideal.Quotient.mk I r * Ideal.Quotient.mk I r') ⊗ₜ[R] m) =
                  e (Ideal.Quotient.mk I (r * r') ⊗ₜ[R] m) := by
                    exact congrArg (fun z => e (z ⊗ₜ[R] m)) hmul
              _ = Submodule.Quotient.mk ((r * r') • m) := by
                    exact TensorProduct.quotTensorEquivQuotSMul_mk_tmul I
                      (r * r') m
              _ = Ideal.Quotient.mk I (r * r') • Submodule.Quotient.mk m := by
                    exact (Module.Quotient.mk_smul_mk (R := R) (M := M)
                      (I := I) (r * r') m).symm
              _ = Ideal.Quotient.mk I r •
                    e (Ideal.Quotient.mk I r' ⊗ₜ[R] m) := by
                    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
                    rw [← Module.Quotient.mk_smul_mk (R := R) (M := M)
                      (I := I) r' m]
                    rw [smul_smul, hmul] }
  exact LinearEquiv.ofBijective f
    ⟨fun x y h => e.injective h, fun y => ⟨e.symm y, by simp [f, e]⟩⟩

private theorem square_zero_flatness_of_base_change
    {R R' M : Type u} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] (φ : R →+* R') (hφ : Function.Injective φ)
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hbase :
      letI : Algebra R R' := φ.toAlgebra
      Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat R M := by
  let _ : Algebra R R' := φ.toAlgebra
  let I' : Ideal R' := Ideal.map φ I
  have hI' : I' ^ 2 = ⊥ := by
    dsimp [I']
    rw [← Ideal.map_pow, hI]
    simp
  have hI'tors : Module.IsTorsionBySet R' (I' : Type u) (I' : Set R') := by
    rw [Module.isTorsionBySet_iff_subset_annihilator]
    rintro r hr
    apply Module.mem_annihilator.mpr
    intro x
    apply Subtype.ext
    have hprod : r * (x : R') ∈ I' ^ 2 := by
      simpa [pow_two] using (Ideal.mul_mem_mul hr x.property)
    rw [hI'] at hprod
    simpa [smul_eq_mul] using hprod
  let _ : Module (R' ⧸ I') (I' : Type u) := hI'tors.module
  have hItors : Module.IsTorsionBySet R (I : Type u) (I : Set R) := by
    rw [Module.isTorsionBySet_iff_subset_annihilator]
    rintro r hr
    apply Module.mem_annihilator.mpr
    intro x
    apply Subtype.ext
    have hprod : r * (x : R) ∈ I ^ 2 := by
      simpa [pow_two] using (Ideal.mul_mem_mul hr x.property)
    rw [hI] at hprod
    simpa [smul_eq_mul] using hprod
  let _ : Module (R ⧸ I) (I : Type u) := hItors.module
  let φbar : R ⧸ I →+* R' ⧸ I' :=
    Ideal.quotientMap I' φ Ideal.le_comap_map
  let _ : Module (R ⧸ I) (I' : Type u) := Module.compHom I' φbar
  let fI : (I : Type u) →ₗ[R ⧸ I] (I' : Type u) :=
    { toFun := fun x => ⟨φ (x : R), Ideal.mem_map_of_mem φ x.property⟩
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by
        rintro ⟨r⟩ x
        apply Subtype.ext
        change φ (r • (x : R)) = φ r • φ (x : R)
        simp }
  have hfI : Function.Injective fI := by
    intro x y hxy
    apply Subtype.ext
    apply hφ
    exact congrArg Subtype.val hxy
  have htensor : Function.Injective
      (fI.rTensor (M ⧸ (I • (⊤ : Submodule R M)))) :=
    Module.Flat.rTensor_preserves_injective_linearMap fI hfI
  let Mbar := M ⧸ (I • (⊤ : Submodule R M))
  let eQ := quotTensorEquivQuotSMulAlg (R := R) (M := M) I
  let _ : IsScalarTower R (R ⧸ I) (I' : Type u) :=
    ⟨by
      intro r a x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      apply Subtype.ext
      change φ (r * a) * (x : R') = φ r * (φ a * (x : R'))
      simp [mul_assoc]⟩
  let eI : (I : Type u) ⊗[R ⧸ I] Mbar ≃ₗ[R ⧸ I]
      (I : Type u) ⊗[R] M :=
    eQ.symm.lTensor (I : Type u) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I)
        (R ⧸ I) (I : Type u) M
  let eI' : (I' : Type u) ⊗[R ⧸ I] Mbar ≃ₗ[R ⧸ I]
      (I' : Type u) ⊗[R] M :=
    eQ.symm.lTensor (I' : Type u) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I)
        (R ⧸ I) (I' : Type u) M
  let eBase : (I' : Type u) ⊗[R'] (R' ⊗[R] M) ≃ₗ[R']
      (I' : Type u) ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R'
      (I' : Type u) M
  let H : (I : Type u) ⊗[R] M →ₗ[R]
      (I' : Type u) ⊗[R'] (R' ⊗[R] M) :=
    (eBase.symm.toLinearMap.restrictScalars R).comp
      ((eI'.toLinearMap.restrictScalars R).comp
        (((fI.rTensor Mbar).restrictScalars R).comp
          (eI.symm.toLinearMap.restrictScalars R)))
  have hH : Function.Injective H := by
    intro x y hxy
    have hxy' :
        (eI'.toLinearMap.restrictScalars R)
            ((fI.rTensor Mbar).restrictScalars R
              ((eI.symm.toLinearMap.restrictScalars R) x)) =
          (eI'.toLinearMap.restrictScalars R)
            ((fI.rTensor Mbar).restrictScalars R
              ((eI.symm.toLinearMap.restrictScalars R) y)) := by
      apply eBase.symm.injective
      simpa [H] using hxy
    have hxy'' :
        (fI.rTensor Mbar).restrictScalars R
            ((eI.symm.toLinearMap.restrictScalars R) x) =
          (fI.rTensor Mbar).restrictScalars R
            ((eI.symm.toLinearMap.restrictScalars R) y) :=
      eI'.injective hxy'
    have hxy''' :
        (eI.symm.toLinearMap.restrictScalars R) x =
          (eI.symm.toLinearMap.restrictScalars R) y :=
      htensor hxy''
    apply eI.symm.injective
    exact hxy'''
  have htargetR : Function.Injective
      (I'.subtype.rTensor (R' ⊗[R] M)) :=
    (Module.Flat.iff_rTensor_injective'.mp hbase I')
  let g' : (I' : Type u) ⊗[R'] (R' ⊗[R] M) →ₗ[R]
      (R' ⊗[R] M) :=
    ((TensorProduct.lid R' (R' ⊗[R] M)).toLinearMap.comp
      (I'.subtype.rTensor (R' ⊗[R] M))).restrictScalars R
  have hg' : Function.Injective g' := by
    exact (TensorProduct.lid R' (R' ⊗[R] M)).injective.comp htargetR
  let g : (I : Type u) ⊗[R] M →ₗ[R] M :=
    (TensorProduct.lid R M).toLinearMap.comp (I.subtype.rTensor M)
  let iM : M →ₗ[R] (R' ⊗[R] M) := TensorProduct.mk R R' M 1
  have hcomm : g'.comp H = iM.comp g := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [g, g', iM]
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul a m =>
        simp [H, eI, eI', eBase, g, g', iM, Mbar, eQ,
          TensorProduct.AlgebraTensorModule.cancelBaseChange]
        change φ (a : R) • (1 : R') ⊗ₜ[R] m =
          (a : R) • (1 : R') ⊗ₜ[R] m
        congr 1
  have hg : Function.Injective g := by
    intro x y hxy
    apply hH
    apply hg'
    have hxy' : (iM.comp g) x = (iM.comp g) y := by
      simp only [LinearMap.comp_apply, hxy]
    change (g'.comp H) x = (g'.comp H) y
    rw [hcomm]
    exact hxy'
  let Amap :=
    Formalization.Books.Algebra.Unit75.idealTensorActionMap I
      (ModuleCat.of R M)
  have hAmap : Function.Injective Amap := by
    have hEq : Amap = g := by
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp [Amap, g]
      | add x y hx hy => simp [Amap, g, hx, hy]
      | tmul a m =>
          change (a : R) • m = (a : R) • m
          rfl
    rw [hEq]
    exact hg
  let _ : Subsingleton (LinearMap.ker Amap) :=
    ⟨fun x y => Subtype.ext (hAmap (by
      exact x.property.trans y.property.symm))⟩
  have hkernel : IsZero
      (Formalization.Books.Algebra.Unit75.idealTensorActionKernel I
        (ModuleCat.of R M)) := by
    change IsZero (ModuleCat.of R (LinearMap.ker Amap))
    apply ModuleCat.isZero_of_subsingleton
  obtain ⟨eTor⟩ :=
    Formalization.Books.Algebra.Unit75.tor_one_ideal_quotient_kernel
      (ModuleCat.of R M) I
  have hTor0 : IsZero
      (Formalization.Books.Algebra.Unit75.Tor (R := R)
        (ModuleCat.of R M) (ModuleCat.of R (R ⧸ I)) 1) :=
    (Iso.isZero_iff eTor).2 hkernel
  have hTor : IsZero
      (Formalization.Books.Algebra.Unit75.Tor (R := R)
        (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 1) :=
    (Iso.isZero_iff
      (Formalization.Books.Algebra.Unit75.torLeftRightIso
        (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 1)).2 hTor0
  exact (Formalization.Books.Algebra.Unit99.what_does_it_mean I hflat hTor).2.2
    ⟨2, hI⟩

private theorem basis_family_lift_of_flat_of_isNilpotent
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : IsNilpotent I) (hflat : Module.Flat R M)
    (x : A → M)
    (hbasis : IsBasisFamily
      (R := R ⧸ I) (M := M ⧸ (I • (⊤ : Submodule R M)))
      (fun a => (I • (⊤ : Submodule R M)).mkQ (x a))) :
    IsBasisFamily (R := R) (M := M) x := by
  classical
  let IM : Submodule R M := I • (⊤ : Submodule R M)
  let ψ : (A →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
  rcases hbasis with ⟨b, hb⟩
  have hspan : Submodule.span R
      (Set.range (fun a => IM.mkQ (x a))) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I)
      Ideal.Quotient.mk_surjective, ← hb]
    simp
  have hspanx : Submodule.span R (Set.range x) = ⊤ := by
    exact Formalization.Books.Algebra.Unit20.nakayama_part_twelve I x hspan hI
  have hsurj : Function.Surjective ψ := by
    rw [span_range_eq_top_iff_surjective_finsuppLinearCombination R] at hspanx
    exact hspanx
  let _ : Module.Flat R M := hflat
  have hkerI : ∀ z : A →₀ R, ψ z = 0 →
      z ∈ I • (⊤ : Submodule R (A →₀ R)) := by
    intro z hz
    let zbar : A →₀ (R ⧸ I) :=
      Finsupp.mapRange (Ideal.Quotient.mk I) (by simp) z
    have hzbar : Finsupp.linearCombination (R ⧸ I)
        (fun a => IM.mkQ (x a)) zbar = 0 := by
      have hz' : IM.mkQ (ψ z) = 0 := by simp [hz]
      calc
        Finsupp.linearCombination (R ⧸ I)
            (fun a => IM.mkQ (x a)) zbar = IM.mkQ (ψ z) := by
          dsimp [zbar, ψ]
          refine Finsupp.induction_linear z (by simp)
            (fun f g hf hg => ?_) (fun a c => ?_)
          · rw [Finsupp.mapRange_add']
            rw [map_add, hf, hg]
            simp
          · simp
        _ = 0 := hz'
    have hzbar' : Finsupp.linearCombination (R ⧸ I)
        (b : A → M ⧸ IM) zbar = 0 := by
      simpa [hb] using hzbar
    have hzbar0 : zbar = 0 :=
      b.linearIndependent.finsuppLinearCombination_injective hzbar'
    have hcoeff : ∀ a, z a ∈ I := by
      intro a
      have ha := congrArg (fun w : A →₀ (R ⧸ I) => w a) hzbar0
      have ha' : Ideal.Quotient.mk I (z a) = 0 := by
        simpa [zbar] using ha
      exact Ideal.Quotient.eq_zero_iff_mem.mp ha'
    rw [← Finsupp.sum_single z]
    apply Submodule.sum_mem
    intro a ha
    simpa [Finsupp.smul_single] using
      (Submodule.smul_mem_smul (hcoeff a)
        (show (Finsupp.single a (1 : R) : A →₀ R) ∈
          (⊤ : Submodule R (A →₀ R)) from Submodule.mem_top))
  have hker_pow : ∀ n : ℕ,
      LinearMap.ker ψ ≤ I ^ n • (⊤ : Submodule R (A →₀ R)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro z hz
        have hzI := hkerI z hz
        have hz' : z ∈ LinearMap.ker ψ ⊓
            (I • (⊤ : Submodule R (A →₀ R))) := ⟨hz, hzI⟩
        rw [LinearMap.ker_inf_smul_top_eq_smul_of_flat I ψ hsurj] at hz'
        have hle : I • LinearMap.ker ψ ≤
            I ^ (n + 1) • (⊤ : Submodule R (A →₀ R)) := by
          apply Submodule.smul_le.2
          intro r hr y hy
          have hy' := ih hy
          have hsmul : r • y ∈ I •
              (I ^ n • (⊤ : Submodule R (A →₀ R))) :=
            Submodule.smul_mem_smul hr hy'
          simpa [pow_succ, mul_comm, mul_smul] using hsmul
        exact hle hz'
  obtain ⟨n, hn⟩ := hI
  have hker : LinearMap.ker ψ = ⊥ := by
    apply le_antisymm
    · intro z hz
      have hz' := hker_pow n hz
      rw [hn] at hz'
      simpa using hz'
    · exact bot_le
  have hli : LinearIndependent R x := by
    rw [linearIndependent_iff_injective_finsuppLinearCombination]
    exact LinearMap.ker_eq_bot.mp hker
  exact ⟨Module.Basis.mk hli hspanx.ge, Module.Basis.coe_mk hli hspanx.ge⟩

private theorem basis_family_descend_of_basis
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (x : A → M)
    (hbasis : IsBasisFamily (R := R) (M := M) x) :
    IsBasisFamily
      (R := R ⧸ I) (M := M ⧸ (I • (⊤ : Submodule R M)))
      (fun a => (I • (⊤ : Submodule R M)).mkQ (x a)) := by
  classical
  let IM : Submodule R M := I • (⊤ : Submodule R M)
  let ψ : (A →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
  rcases hbasis with ⟨b, hb⟩
  have hψbij : Function.Bijective ψ := by
    rw [show ψ = b.repr.symm by
      ext z
      simp [ψ, ← hb]]
    exact b.repr.symm.bijective
  let e : (A →₀ R) ≃ₗ[R] M := LinearEquiv.ofBijective ψ hψbij
  have hinv : IM.map e.symm.toLinearMap ≤
      I • (⊤ : Submodule R (A →₀ R)) := by
    apply Submodule.map_le_iff_le_comap.mpr
    intro m hm
    refine Submodule.smul_induction_on hm
      (fun r hr y _ => ?_) (fun y z hy hz => ?_)
    · change e.symm (r • y) ∈ I • (⊤ : Submodule R (A →₀ R))
      rw [map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · change e.symm (y + z) ∈ I • (⊤ : Submodule R (A →₀ R))
      rw [map_add]
      exact (I • (⊤ : Submodule R (A →₀ R))).add_mem hy hz
  have hformula (z : A →₀ R) :
      Finsupp.linearCombination (R ⧸ I)
        (fun a => IM.mkQ (x a))
        (Finsupp.mapRange (Ideal.Quotient.mk I) (by simp) z) =
        IM.mkQ (ψ z) := by
    dsimp [ψ]
    refine Finsupp.induction_linear z (by simp)
      (fun f g hf hg => ?_) (fun a c => ?_)
    · rw [Finsupp.mapRange_add']
      rw [map_add, hf, hg]
      simp
    · simp
  have hli : LinearIndependent (R ⧸ I)
      (fun a => IM.mkQ (x a)) := by
    rw [linearIndependent_iff_injective_finsuppLinearCombination]
    intro zbar₁ zbar₂ h
    let zd := zbar₁ - zbar₂
    obtain ⟨z, hz⟩ := Finsupp.mapRange_surjective
      (Ideal.Quotient.mk I) (by simp) Ideal.Quotient.mk_surjective zd
    have hz0 : Finsupp.linearCombination (R ⧸ I)
        (fun a => IM.mkQ (x a)) zd = 0 := by
      rw [map_sub]
      apply sub_eq_zero.mpr
      simpa [IM] using h
    have hmk : IM.mkQ (ψ z) = 0 := by
      calc
        IM.mkQ (ψ z) = Finsupp.linearCombination (R ⧸ I)
            (fun a => IM.mkQ (x a))
            (Finsupp.mapRange (Ideal.Quotient.mk I) (by simp) z) :=
          (hformula z).symm
        _ = Finsupp.linearCombination (R ⧸ I)
            (fun a => IM.mkQ (x a)) zd := by rw [hz]
        _ = 0 := hz0
    have hmem : ψ z ∈ IM :=
      (Submodule.Quotient.mk_eq_zero IM).mp hmk
    have hzmem : z ∈ I • (⊤ : Submodule R (A →₀ R)) := by
      have hzmap : z ∈ IM.map e.symm.toLinearMap := by
        refine ⟨ψ z, hmem, ?_⟩
        simp [e]
      simpa [e] using hinv hzmap
    have hIF_eq : I • (⊤ : Submodule R (A →₀ R)) =
        Finsupp.submodule (fun _ : A => (I : Submodule R R)) := by
      have hItop : I • (⊤ : Submodule R R) = I := by
        apply le_antisymm
        · apply Submodule.smul_le.2
          intro r hr s hs
          change r * s ∈ I
          simpa [mul_comm] using I.mul_mem_left s hr
        · intro r hr
          simpa using Submodule.smul_mem_smul hr
            (show (1 : R) ∈ (⊤ : Submodule R R) from Submodule.mem_top)
      calc
        I • (⊤ : Submodule R (A →₀ R)) =
            I • Finsupp.submodule (fun _ : A => (⊤ : Submodule R R)) := by
              rw [Finsupp.submodule_top]
        _ = Finsupp.submodule
            (fun _ : A => I • (⊤ : Submodule R R)) :=
          (Finsupp.submodule_smul R A
            (fun _ : A => (⊤ : Submodule R R)) I).symm
        _ = Finsupp.submodule (fun _ : A => (I : Submodule R R)) := by
          rw [hItop]
    have hzcoeff : ∀ a, z a ∈ I := by
      rw [hIF_eq] at hzmem
      exact hzmem
    have hzzero : Finsupp.mapRange (Ideal.Quotient.mk I)
        (by simp) z = 0 := by
      ext a
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hzcoeff a)
    have hzd : zd = 0 := by simpa [hz] using hzzero
    exact sub_eq_zero.mp hzd
  have hspan : Submodule.span (R ⧸ I)
      (Set.range (fun a => IM.mkQ (x a))) = ⊤ := by
    have hmap : (Submodule.span R (Set.range x)).map IM.mkQ = ⊤ := by
      rw [← hb, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
    rw [Submodule.map_span] at hmap
    have himage : IM.mkQ '' Set.range x =
        Set.range (fun a => IM.mkQ (x a)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨x a, ⟨a, rfl⟩, rfl⟩
    have hspanR : Submodule.span R
        (Set.range (fun a => IM.mkQ (x a))) = ⊤ := by
      simpa [himage] using hmap
    rw [← Submodule.restrictScalars_eq_top_iff R,
      Submodule.restrictScalars_span R (R ⧸ I)
        Ideal.Quotient.mk_surjective, hspanR]
  exact ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk hli hspan.ge⟩

private theorem basis_family_iff_of_flat_of_isNilpotent
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : IsNilpotent I) (hflat : Module.Flat R M)
    (x : A → M) :
    IsBasisFamily
      (R := R ⧸ I) (M := M ⧸ (I • (⊤ : Submodule R M)))
      (fun a => (I • (⊤ : Submodule R M)).mkQ (x a)) ↔
      IsBasisFamily (R := R) (M := M) x := by
  constructor
  · exact basis_family_lift_of_flat_of_isNilpotent I hI hflat x
  · exact basis_family_descend_of_basis I x

/- The source's residue vectors are the images under the canonical quotient
   map of the maximal-ideal multiple of the module. -/
theorem local_artinian_basis_when_flat
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsLocalRing R] (hmax : IsNilpotent (IsLocalRing.maximalIdeal R))
    (hflat : Module.Flat R M) (x : A → M) :
    IsBasisFamily
        (R := R ⧸ IsLocalRing.maximalIdeal R)
        (M := M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)))
        (fun a =>
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ (x a)) ↔
      IsBasisFamily (R := R) (M := M) x := by
  exact basis_family_iff_of_flat_of_isNilpotent
    (IsLocalRing.maximalIdeal R) hmax hflat x

theorem local_artinian_characterize_flat
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsLocalRing R]
    (hmax : IsNilpotent (IsLocalRing.maximalIdeal R)) :
    List.TFAE [Module.Flat R M, Module.Free R M, Module.Projective R M] := by
  tfae_have 1 → 2 := by
    intro hflat
    let k := R ⧸ IsLocalRing.maximalIdeal R
    let Q := M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
    let _ : Field k := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    let A' := Module.Basis.ofVectorSpaceIndex k Q
    let b : Module.Basis A' k Q := Module.Basis.ofVectorSpace k Q
    let y : A' → M := fun a =>
      Classical.choose (Submodule.mkQ_surjective
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) (b a))
    have hy (a : A') :
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ (y a) = b a := by
      exact Classical.choose_spec (Submodule.mkQ_surjective
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) (b a))
    have hbq : IsBasisFamily
        (R := R ⧸ IsLocalRing.maximalIdeal R)
        (M := M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)))
        (fun a =>
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ (y a)) := by
      refine ⟨b, ?_⟩
      funext a
      exact (hy a).symm
    rcases (local_artinian_basis_when_flat hmax hflat y).mp hbq with ⟨bM, hbM⟩
    exact Module.Free.of_basis bM
  tfae_have 2 → 3 := by
    intro hfree
    let _ : Module.Free R M := hfree
    exact Module.Projective.of_free
  tfae_have 3 → 1 := by
    intro hprojective
    let _ : Module.Projective R M := hprojective
    exact Module.Flat.of_projective
  tfae_finish

theorem lift_basis
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : IsNilpotent I) (x : A → M)
    (hbasis :
      IsBasisFamily
        (R := R ⧸ I) (M := M ⧸ (I • (⊤ : Submodule R M)))
        (fun a => (I • (⊤ : Submodule R M)).mkQ (x a)))
    (hTor : IsZero
      (Formalization.Books.Algebra.Unit75.Tor
        (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 1)) :
    IsBasisFamily (R := R) (M := M) x := by
  rcases hbasis with ⟨b, hb⟩
  have hflatbar : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))) := by
    let _ : Module.Free (R ⧸ I)
        (M ⧸ (I • (⊤ : Submodule R M))) := Module.Free.of_basis b
    exact Module.Flat.of_free
  obtain ⟨n, hn⟩ := hI
  have hflat : Module.Flat R M :=
    (Formalization.Books.Algebra.Unit99.what_does_it_mean
      I hflatbar hTor).2.2 ⟨n, by simpa using hn⟩
  exact basis_family_lift_of_flat_of_isNilpotent I ⟨n, hn⟩ hflat x
    ⟨b, hb⟩

private noncomputable opaque cancel_base_change
    {R A B M N : Type u} [CommSemiring R] [CommSemiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [AddCommMonoid M] [Module R M]
    [Module A M] [Module B M] [IsScalarTower R A M]
    [IsScalarTower R B M] [SMulCommClass A B M] [AddCommMonoid N]
    [Module R N] [Algebra A B] [IsScalarTower A B M] :
    M ⊗[A] (A ⊗[R] N) ≃ₗ[B] M ⊗[R] N :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R A B M N

private theorem prepare_lift_flatness_c_phase
    {R A C T M Mbar : Type u} [CommRing R] [CommRing A] [CommRing C]
    [CommRing T] [AddCommGroup M] [AddCommGroup Mbar] [Module R M]
    [Module R Mbar] [Module A Mbar] [Algebra R A] [Algebra R C]
    [Algebra R T] [Algebra A C] [IsScalarTower R A C]
    (eM : A ⊗[R] M ≃ₗ[A] Mbar) (eRing : C ≃+* T)
    (hcomp : ∀ r : R, eRing ((algebraMap R C) r) = algebraMap R T r)
    (hTflat : Module.Flat T (T ⊗[R] M)) :
    Module.Flat C (C ⊗[A] Mbar) := by
  let _ : Algebra C T := eRing.toRingHom.toAlgebra
  let _ : IsScalarTower R C T :=
    IsScalarTower.of_algebraMap_eq (fun r => (hcomp r).symm)
  let eRingLin : C ≃ₗ[C] T :=
    { eRing.toAddEquiv with
      map_smul' := by
        intro c x
        change eRing (c * x) = eRing c * eRing x
        exact eRing.map_mul c x }
  let _ : SMul C (T ⊗[R] M) :=
    ⟨fun c x => eRing c • x⟩
  let _ : Module C (T ⊗[R] M) :=
    Module.compHom (T ⊗[R] M) eRing.toRingHom
  have hTowerCT : IsScalarTower C T (T ⊗[R] M) :=
    ⟨by
      intro c t x
      change (eRing c * t) • x = eRing c • (t • x)
      rw [mul_smul]⟩
  have hCT : Module.Flat C T := by
    exact Module.Flat.of_linearEquiv eRingLin.symm
  have hCflatT : Module.Flat C (T ⊗[R] M) := by
    let _ : Module.Flat C T := hCT
    let _ : Module.Flat T (T ⊗[R] M) := hTflat
    exact @Module.Flat.trans C T (T ⊗[R] M)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance hTowerCT hCT hTflat
  let _ : IsScalarTower C T (T ⊗[R] M) := hTowerCT
  let eCM : C ⊗[R] M ≃ₗ[C] T ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.congr eRingLin
      (LinearEquiv.refl R M)
  have hCflatM : Module.Flat C (C ⊗[R] M) :=
    (Module.Flat.equiv_iff eCM).mpr hCflatT
  let _ : IsScalarTower R C C :=
    IsScalarTower.of_algebraMap_smul (fun r c => by
      simp [Algebra.smul_def])
  let _ : IsScalarTower A C C :=
    IsScalarTower.of_algebraMap_smul (fun a c => by
      simp [Algebra.smul_def])
  let _ : SMulCommClass A C C :=
    ⟨fun a c x => by
      simp [Algebra.smul_def, mul_assoc, mul_comm]⟩
  let eC : C ⊗[A] Mbar ≃ₗ[C] C ⊗[R] M :=
    LinearEquiv.baseChange A C Mbar (A ⊗[R] M) eM.symm ≪≫ₗ
      cancel_base_change (R := R) (A := A) (B := C) (M := C) (N := M)
  exact (Module.Flat.equiv_iff eC).mpr hCflatM

private theorem prepare_lift_flatness_tail
    {R R' M : Type u} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] (φ : R →+* R') (I J : Ideal R)
    (hJ : J = prepareIdeal φ I)
    (φbar : (R ⧸ J) →+*
      (R' ⧸ Ideal.map φ (I ^ 2)))
    (hφbar : Function.Injective φbar)
    (eM : (R ⧸ J) ⊗[R] M ≃ₗ[R ⧸ J]
      (M ⧸ (J • (⊤ : Submodule R M))))
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hbaseS' : letI : Algebra (R ⧸ J) (R' ⧸ Ideal.map φ (I ^ 2)) :=
        φbar.toAlgebra
      Module.Flat (R' ⧸ Ideal.map φ (I ^ 2))
      ((R' ⧸ Ideal.map φ (I ^ 2)) ⊗[R ⧸ J]
        (M ⧸ (J • (⊤ : Submodule R M))))) :
    Module.Flat (R ⧸ J)
      (M ⧸ (J • (⊤ : Submodule R M))) := by
  let _ : Algebra R R' := φ.toAlgebra
  let K : Ideal R' := Ideal.map φ (I ^ 2)
  let A := R ⧸ J
  let S := R' ⧸ K
  let Mbar := M ⧸ (J • (⊤ : Submodule R M))
  let _ : Algebra A S := φbar.toAlgebra
  let Ibar : Ideal A := Ideal.map (Ideal.Quotient.mk J) I
  have hIbar : Ibar ^ 2 = ⊥ := by
    dsimp [Ibar]
    rw [← Ideal.map_pow]
    apply le_antisymm
    · exact (Ideal.map_mk_eq_bot_of_le (I := I ^ 2) (J := J) (by
        change I ^ 2 ≤ J
        rw [hJ]
        exact Ideal.le_comap_map)).le
    · exact bot_le
  let B := R ⧸ I
  let Mfiber := M ⧸ (I • (⊤ : Submodule R M))
  let L : Ideal B := Ideal.map (Ideal.Quotient.mk I) J
  let T := B ⧸ L
  let qT : R →+* T :=
    (Ideal.Quotient.mk L).comp (Ideal.Quotient.mk I)
  let _ : SMul B T := ⟨fun b t => (Ideal.Quotient.mk L b) * t⟩
  let _ : SMul R T := ⟨fun r t => qT r * t⟩
  let _ : Algebra B T := (Ideal.Quotient.mk L).toAlgebra
  let _ : Module B T := Module.compHom T (Ideal.Quotient.mk L)
  let _ : Algebra R T := qT.toAlgebra
  let _ : Module R T := Module.compHom T qT
  have hcompT (r : R) :
      (algebraMap B T) ((algebraMap R B) r) = (algebraMap R T) r := by
    change (Ideal.Quotient.mk L) (Ideal.Quotient.mk I r) = qT r
    rfl
  let _ : IsScalarTower R B T :=
    IsScalarTower.of_algebraMap_smul (fun r t => by
      change (algebraMap B T) ((algebraMap R B) r) * t = qT r * t
      rw [hcompT]
      change qT r * t = qT r * t
      rfl)
  let _ : IsScalarTower R T T :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let _ : IsScalarTower B T T :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let _ : SMulCommClass B T T :=
    ⟨fun b t x => by
      change (algebraMap B T b) * (t * x) = t * ((algebraMap B T b) * x)
      simp [mul_assoc, mul_comm]⟩
  let qI : B ⊗[R] M ≃ₗ[B] Mfiber :=
    quotTensorEquivQuotSMulAlg (R := R) (M := M) I
  let eT : T ⊗[B] Mfiber ≃ₗ[T] T ⊗[R] M :=
    LinearEquiv.baseChange B T Mfiber (B ⊗[R] M) qI.symm ≪≫ₗ
      cancel_base_change (R := R) (A := B) (B := T) (M := T) (N := M)
  have hbaseT : Module.Flat T (T ⊗[B] Mfiber) := by
    let _ : Module.Flat B Mfiber := hflat
    infer_instance
  have hTflat : Module.Flat T (T ⊗[R] M) :=
    (Module.Flat.equiv_iff eT).mp hbaseT
  let C := A ⧸ Ibar
  let qC : R →+* C :=
    (Ideal.Quotient.mk Ibar).comp (Ideal.Quotient.mk J)
  let _ : SMul A C :=
    ⟨fun a c => (Ideal.Quotient.mk Ibar a) * c⟩
  let _ : SMul R C := ⟨fun r c => qC r * c⟩
  let _ : Algebra A C := (Ideal.Quotient.mk Ibar).toAlgebra
  let _ : Module A C := Module.compHom C (Ideal.Quotient.mk Ibar)
  let _ : Algebra R C := qC.toAlgebra
  let _ : Module R C := Module.compHom C qC
  have hcompC (r : R) :
      (algebraMap A C) ((algebraMap R A) r) = (algebraMap R C) r := by
    change (Ideal.Quotient.mk Ibar) (Ideal.Quotient.mk J r) = qC r
    rfl
  let _ : IsScalarTower R A C :=
    IsScalarTower.of_algebraMap_eq (fun r => (hcompC r).symm)
  let eRing : C ≃+* T := DoubleQuot.quotQuotEquivComm J I
  let _ : Algebra C T := eRing.toRingHom.toAlgebra
  have hcompCT (r : R) :
      (algebraMap C T) ((algebraMap R C) r) = (algebraMap R T) r := by
    change eRing (qC r) = qT r
    change DoubleQuot.quotQuotEquivComm J I
        (Ideal.Quotient.mk Ibar (Ideal.Quotient.mk J r)) =
      Ideal.Quotient.mk L (Ideal.Quotient.mk I r)
    exact DoubleQuot.quotQuotEquivComm_quotQuotMk J I r
  let _ : IsScalarTower R C T :=
    IsScalarTower.of_algebraMap_eq (fun r => (hcompCT r).symm)
  have hCflatMbar : Module.Flat C (C ⊗[A] Mbar) := by
    apply prepare_lift_flatness_c_phase eM eRing
    · intro r
      exact hcompCT r
    · exact hTflat
  let eFiber : C ⊗[A] Mbar ≃ₗ[C]
      (Mbar ⧸ (Ibar • (⊤ : Submodule A Mbar))) :=
    quotTensorEquivQuotSMulAlg (R := A) (M := Mbar) Ibar
  have hflatFiber : Module.Flat C
      (Mbar ⧸ (Ibar • (⊤ : Submodule A Mbar))) :=
    (Module.Flat.equiv_iff eFiber).mp hCflatMbar
  exact square_zero_flatness_of_base_change φbar hφbar Ibar hIbar
    hflatFiber hbaseS'

theorem prepare_lift_flatness
    {R R' M : Type u} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] (φ : R →+* R') (I : Ideal R)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hbase :
      letI : Algebra R R' := φ.toAlgebra
      Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat (R ⧸ prepareIdeal φ I)
      (M ⧸ (prepareIdeal φ I • (⊤ : Submodule R M))) := by
  let _ : Algebra R R' := φ.toAlgebra
  let J : Ideal R := prepareIdeal φ I
  let K : Ideal R' := Ideal.map φ (I ^ 2)
  let A := R ⧸ J
  let S := R' ⧸ K
  let φbar : A →+* S :=
    Ideal.quotientMap K φ (by
      change Ideal.comap φ (Ideal.map φ (I ^ 2)) ≤
        Ideal.comap φ (Ideal.map φ (I ^ 2))
      exact le_rfl)
  have hφbar : Function.Injective φbar := by
    apply Ideal.quotientMap_injective'
    change Ideal.comap φ (Ideal.map φ (I ^ 2)) ≤
      Ideal.comap φ (Ideal.map φ (I ^ 2))
    exact le_rfl
  let _ : Algebra A S := φbar.toAlgebra
  have hcomp (r : R) :
      (algebraMap A S) ((algebraMap R A) r) = (algebraMap R S) r := by
    change φbar (Ideal.Quotient.mk J r) = Ideal.Quotient.mk K (φ r)
    rfl
  let _ : IsScalarTower R A S :=
    ⟨by
      intro r a s
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      simp only [Algebra.smul_def, map_mul, mul_assoc]
      rw [hcomp]⟩
  let Ibar : Ideal A := Ideal.map (Ideal.Quotient.mk J) I
  have hIbar : Ibar ^ 2 = ⊥ := by
    dsimp [Ibar]
    rw [← Ideal.map_pow]
    apply le_antisymm
    · exact (Ideal.map_mk_eq_bot_of_le (I := I ^ 2) (J := J) (by
        change I ^ 2 ≤ Ideal.comap φ (Ideal.map φ (I ^ 2))
        exact Ideal.le_comap_map)).le
    · exact bot_le
  let Mbar := M ⧸ (J • (⊤ : Submodule R M))
  let eM : A ⊗[R] M ≃ₗ[A] Mbar :=
    quotTensorEquivQuotSMulAlg (R := R) (M := M) J
  let eS : S ⊗[A] Mbar ≃ₗ[S] S ⊗[R] M :=
    LinearEquiv.baseChange A S Mbar (A ⊗[R] M) eM.symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R A S S M
  let eS' : S ⊗[R'] (R' ⊗[R] M) ≃ₗ[S] S ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R R' S S M
  have hbaseS : Module.Flat S (S ⊗[R'] (R' ⊗[R] M)) := by
    infer_instance
  have hbaseS' : Module.Flat S (S ⊗[A] Mbar) := by
    exact (Module.Flat.equiv_iff eS).2 ((Module.Flat.equiv_iff eS').mp hbaseS)
  exact prepare_lift_flatness_tail φ I J rfl φbar hφbar eM hflat hbaseS'

theorem lift_flatness
    {R R' M : Type u} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] (φ : R →+* R') (I : Ideal R)
    (hI : IsNilpotent I) (hφ : Injective φ)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hbase :
      letI : Algebra R R' := φ.toAlgebra
      Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat R M := by
  let J : ℕ → Ideal R := fun n =>
    Nat.rec I (fun _ Jn => prepareIdeal φ Jn) n
  have hflatJ : ∀ n : ℕ,
      let Jn : Ideal R := J n
      letI : Module (R ⧸ Jn) (M ⧸ (Jn • (⊤ : Submodule R M))) :=
        Submodule.Quotient.module _
      Module.Flat (R ⧸ Jn) (M ⧸ (Jn • (⊤ : Submodule R M))) := by
    intro n
    induction n with
    | zero => simpa [J] using hflat
    | succ n ih =>
        simpa [J] using prepare_lift_flatness (R := R) (R' := R')
          (M := M) φ (J n) ih hbase
  have hmapJ : ∀ n : ℕ,
      Ideal.map φ (J n) ≤ (Ideal.map φ I) ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp [J]
    | succ n ih =>
        change Ideal.map φ (prepareIdeal φ (J n)) ≤
          (Ideal.map φ I) ^ (2 ^ (n + 1))
        calc
          Ideal.map φ (prepareIdeal φ (J n)) ≤
              Ideal.map φ ((J n) ^ 2) := by
            exact Ideal.map_comap_le
          _ = (Ideal.map φ (J n)) ^ 2 := by
            rw [Ideal.map_pow]
          _ ≤ ((Ideal.map φ I) ^ (2 ^ n)) ^ 2 :=
            Ideal.mul_mono ih ih
          _ = (Ideal.map φ I) ^ (2 ^ (n + 1)) := by
            rw [← pow_mul, pow_succ]
            simp [Nat.mul_comm]
  obtain ⟨n, hn⟩ := hI
  have hpow : n ≤ 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
          _ ≤ 2 ^ n + 2 ^ n := by
            exact Nat.add_le_add_left (Nat.one_le_pow (by omega)) _
          _ = 2 ^ (n + 1) := by simp [pow_succ, mul_two]
  have hmapI : (Ideal.map φ I) ^ n = ⊥ := by
    rw [← Ideal.map_pow, hn]
    simp
  have hmapJn : Ideal.map φ (J n) = ⊥ := by
    apply le_antisymm
    · exact (hmapJ n).trans ((Ideal.pow_le_pow_right hpow).trans_eq hmapI)
    · exact bot_le
  have hJn : J n = ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hφ).mp hmapJn
  have hJn_sq : (J n) ^ 2 = ⊥ := by simp [hJn]
  exact square_zero_flatness_of_base_change φ hφ (J n) hJn_sq
    (hflatJ n) hbase
/-
  let J : ℕ → Ideal R := fun n =>
    Nat.rec I (fun _ Jn => prepareIdeal φ Jn) n
  have hflatJ : ∀ n : ℕ,
      let Jn : Ideal R := J n
      letI : Module (R ⧸ Jn) (M ⧸ (Jn • (⊤ : Submodule R M))) :=
        Submodule.Quotient.module _
      Module.Flat (R ⧸ Jn) (M ⧸ (Jn • (⊤ : Submodule R M))) := by
    intro n
    induction n with
    | zero => simpa [J] using hflat
    | succ n ih =>
        simpa [J] using prepare_lift_flatness (R := R) (R' := R')
          (M := M) φ (J n) ih hbase
  have hmapJ : ∀ n : ℕ,
      Ideal.map φ (J n) ≤ (Ideal.map φ I) ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp [J]
    | succ n ih =>
        change Ideal.map φ (prepareIdeal φ (J n)) ≤
          (Ideal.map φ I) ^ (2 ^ (n + 1))
        calc
          Ideal.map φ (prepareIdeal φ (J n)) ≤
              Ideal.map φ ((J n) ^ 2) := by
            exact Ideal.map_comap_le
          _ = (Ideal.map φ (J n)) ^ 2 := by
            rw [Ideal.map_pow]
          _ ≤ ((Ideal.map φ I) ^ (2 ^ n)) ^ 2 :=
            Ideal.mul_mono ih ih
          _ = (Ideal.map φ I) ^ (2 ^ (n + 1)) := by
            rw [← pow_mul, pow_succ]
            simp [Nat.mul_comm]
  obtain ⟨n, hn⟩ := hI
  have hpow : n ≤ 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
          _ ≤ 2 ^ n + 2 ^ n := by
            exact Nat.add_le_add_left (Nat.one_le_pow (by omega)) _
          _ = 2 ^ (n + 1) := by simp [pow_succ, mul_two]
  have hmapI : (Ideal.map φ I) ^ n = ⊥ := by
    rw [← Ideal.map_pow, hn]
    simp
  have hmapJn : Ideal.map φ (J n) = ⊥ := by
    apply le_antisymm
    · exact (hmapJ n).trans ((Ideal.pow_le_pow_right hpow).trans_eq hmapI)
    · exact bot_le
  have hJn : J n = ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hφ).mp hmapJn
  have hJn_sq : (J n) ^ 2 = ⊥ := by simp [hJn]
  exact square_zero_flatness_of_base_change φ hφ (J n) hJn_sq
    (hflatJ n) hbase

-/
theorem artinian_variant_local_criterion_flatness
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    Module.Flat R M ↔
      Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) ∧
        IsZero
          (Formalization.Books.Algebra.Unit75.Tor
            (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 1) := by
  constructor
  · intro hflat
    let _ : Algebra R (R ⧸ I) := (Ideal.Quotient.mk I).toAlgebra
    let eQ := quotTensorEquivQuotSMulAlg (R := R) (M := M) I
    have hflatQ : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
      Formalization.Books.Algebra.Unit39.flat_base_change hflat
    have hflatbar : Module.Flat (R ⧸ I)
        (M ⧸ (I • (⊤ : Submodule R M))) :=
      (Module.Flat.equiv_iff eQ).mp hflatQ
    have hcrit : Module.Flat R M ↔
        Formalization.Books.Algebra.Unit75.TorFunctorZero
          (ModuleCat.of R M) 1 :=
      (Formalization.Books.Algebra.Unit75.flat_iff_tor_criteria
        (ModuleCat.of R M)).out 0 2
    have hTor' : IsZero
        (Formalization.Books.Algebra.Unit75.Tor
          (ModuleCat.of R M) (ModuleCat.of R (R ⧸ I)) 1) :=
      hcrit.mp hflat (ModuleCat.of R (R ⧸ I))
    have hTor : IsZero
        (Formalization.Books.Algebra.Unit75.Tor
          (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 1) :=
      (Iso.isZero_iff
        (Formalization.Books.Algebra.Unit75.torLeftRightIso
          (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 1)).2 hTor'
    exact ⟨hflatbar, hTor⟩
  · rintro ⟨hflatbar, hTor⟩
    obtain ⟨n, hn⟩ := artinian_local_maximalIdeal_isNilpotent (R := R)
    apply (Formalization.Books.Algebra.Unit99.what_does_it_mean
      I hflatbar hTor).2.2
    refine ⟨n, ?_⟩
    apply le_antisymm
    · exact (Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hI) n).trans
        (by simpa using hn)
    · exact bot_le

theorem descent_flatness_injective_map_artinian_rings
    {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [IsArtinianRing R] (φ : R →+* S) (hφ : Injective φ)
    (hflat :
      letI : Algebra R S := φ.toAlgebra
      Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := by
  let J : Ideal R := Ring.jacobson R
  have hJ : IsNilpotent J := by
    simpa [J, Ideal.jacobson_bot] using
      (IsArtinianRing.isNilpotent_jacobson_bot (R := R))
  have hflatbar : Module.Flat (R ⧸ J)
      (M ⧸ (J • (⊤ : Submodule R M))) := by
    let _ : IsSemisimpleRing (R ⧸ J) := inferInstance
    let _ : Module.Projective (R ⧸ J)
        (M ⧸ (J • (⊤ : Submodule R M))) :=
      Module.projective_of_isSemisimpleRing (R ⧸ J)
        (M ⧸ (J • (⊤ : Submodule R M)))
    exact Module.Flat.of_projective
  exact lift_flatness φ J hJ hφ hflatbar hflat
/-
  let J : Ideal R := Ring.jacobson R
  have hJ : IsNilpotent J := by
    simpa [Ideal.jacobson_bot] using
      (IsArtinianRing.isNilpotent_jacobson_bot (R := R))
  have hflatbar : Module.Flat (R ⧸ J)
      (M ⧸ (J • (⊤ : Submodule R M))) := by
    let _ : IsSemisimpleRing (R ⧸ J) := inferInstance
    let _ : Module.Projective (R ⧸ J)
        (M ⧸ (J • (⊤ : Submodule R M))) :=
      Module.projective_of_isSemisimpleRing (R ⧸ J)
        (M ⧸ (J • (⊤ : Submodule R M)))
    exact Module.Flat.of_projective
  exact lift_flatness φ J hJ hφ hflatbar hflat

 -/
/- The condition in the fibre criterion is the source's assertion that the
   fibre of `M` at `q` is nonzero, with the `S`-action restricted from `S'`. -/
def nontrivialFibreAt
    {S S' M : Type u} [CommRing S] [CommRing S'] [AddCommGroup M]
    [Module S' M] (g : S →+* S') (q : PrimeSpectrum S) : Prop :=
  letI : Module S M := Module.compHom M g
  Nontrivial (M ⊗[S] q.asIdeal.ResidueField)

/- This is the nilpotent fibre criterion.  The comparison warning in the
   source points to the Noetherian, finitely presented, and locally nilpotent
   fibre criteria formalized in the preceding chapter. -/
theorem criterion_flatness_fibre_nilpotent
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    [AddCommGroup M] [Module S' M]
    (f : R →+* S) (g : S →+* S') (h : R →+* S')
    (comm : g.comp f = h) (I : Ideal R) (hI : IsNilpotent I)
    (hflat_fibre :
      letI : Module S M := Module.compHom M g
      Module.Flat (S ⧸ (I.map f))
        (M ⧸ ((I.map f) • (⊤ : Submodule S M))))
    (hflat_base :
      letI : Module R M := Module.compHom M h
      Module.Flat R M) :
    (letI : Module S M := Module.compHom M g
     Module.Flat S M) ∧
      ∀ q : PrimeSpectrum S,
        nontrivialFibreAt (M := M) g q →
          RingHom.Flat
            ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f) := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Module S M := Module.compHom M g
  let _ : Module R M := Module.compHom M h
  have hcomm (r : R) : g (f r) = h r := by
    exact congrArg (fun k : R →+* S' => k r) comm
  let _ : IsScalarTower R S M :=
    IsScalarTower.of_algebraMap_smul (fun r m => by
      change g (f r) • m = h r • m
      rw [hcomm])
  let J : Ideal S := Ideal.map f I
  have hmem (a : I) : f (a : R) ∈ J := by
    change f (a : R) ∈ Ideal.map f I
    exact Ideal.mem_map_of_mem f a.property
  have hmem_mul (r : R) (a : I) : f (r * (a : R)) ∈ J := by
    change f (r * (a : R)) ∈ Ideal.map f I
    exact Ideal.mem_map_of_mem f (I.mul_mem_left r a.property)
  change Module.Flat (S ⧸ J) (M ⧸ (J • (⊤ : Submodule S M))) at hflat_fibre
  change Module.Flat R M at hflat_base
  have hJ : IsNilpotent J := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow, hn]
    simp
  let AmapI := Formalization.Books.Algebra.Unit75.idealTensorActionMap I
      (ModuleCat.of R M)
  let gI : TensorProduct R (I : Type u) M →ₗ[R] M :=
    (TensorProduct.lid R M).toLinearMap.comp (I.subtype.rTensor M)
  have hIinj : Function.Injective (I.subtype.rTensor M) :=
    (Module.Flat.iff_rTensor_injective'.mp hflat_base I)
  have hgI : Function.Injective gI :=
    (TensorProduct.lid R M).injective.comp hIinj
  have hAmapI : Function.Injective AmapI := by
    have hEq : AmapI = gI := by
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp [AmapI, gI]
      | add x y hx hy => simp [AmapI, gI, hx, hy]
      | tmul a m => rfl
    rw [hEq]
    exact hgI
  let T := TensorProduct S (J : Type u) M
  let _ : Module R T := Module.compHom T f
  have hsc (r s : R) (x : T) : r • s • x = s • r • x := by
    rw [smul_smul, smul_smul, mul_comm]
  let _ : Module R (M →ₗ[R] T) :=
    { smul := fun r k =>
        { toFun := fun m => r • k m
          map_add' := by intro x y; simp [smul_add]
          map_smul' := by
            intro s x
            change r • k (s • x) = s • r • k x
            rw [k.map_smul]
            exact hsc r s (k x) }
      one_smul := by
        intro k
        ext x
        change (1 : R) • k x = k x
        exact one_smul R (k x)
      mul_smul := by
        intro r s k
        ext x
        change (r * s) • k x = r • s • k x
        rw [smul_smul]
      smul_add := by
        intro r k l
        ext x
        change r • (k x + l x) = r • k x + r • l x
        rw [smul_add]
      smul_zero := by
        intro r
        ext x
        change r • (0 : T) = 0
        exact smul_zero r
      add_smul := by
        intro r s k
        ext x
        change (r + s) • k x = r • k x + s • k x
        exact add_smul r s (k x)
      zero_smul := by
        intro k
        ext x
        change (0 : R) • k x = 0
        exact zero_smul R (k x) }
  let K : TensorProduct R (I : Type u) M →ₗ[R] T :=
    TensorProduct.lift (R := R) (R₂ := R) (σ₁₂ := RingHom.id R)
      (M := (I : Type u)) (N := M) (P₂ := T)
      { toFun := fun a =>
          { toFun := fun m =>
              TensorProduct.tmul S
                (⟨f (a : R), hmem a⟩ : J) m
            map_add' := by
              intro m n
              rw [TensorProduct.tmul_add]
            map_smul' := by
              intro r m
              change TensorProduct.tmul S
                  (⟨f (a : R), hmem a⟩ : J)
                  (h r • m) =
                TensorProduct.tmul S
                  (f r • (⟨f (a : R), hmem a⟩ : J)) m
              rw [← hcomm r]
              change TensorProduct.tmul S
                  (⟨f (a : R), hmem a⟩ : J)
                  ((f r) • m) =
                TensorProduct.tmul S
                  ((f r) • (⟨f (a : R), hmem a⟩ : J)) m
              exact TensorProduct.tmul_smul (f r)
                (⟨f (a : R), hmem a⟩ : J) m }
        map_add' := by
          intro a b
          ext m
          have hab : (⟨f (a + b), hmem (a + b)⟩ : J) =
              (⟨f a, hmem a⟩ : J) + ⟨f b, hmem b⟩ := by
            apply Subtype.ext
            simp
          rw [hab, add_tmul]
        map_smul' := by
          intro r a
          ext m
          have hmul : (⟨f (r * (a : R)), hmem_mul r a⟩ : J) =
              (f r) • (⟨f (a : R), hmem a⟩ : J) := by
            apply Subtype.ext
            simp [smul_eq_mul]
          rw [hmul, TensorProduct.smul_tmul] }
  have hKsurj : Function.Surjective K := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [K]⟩
    | add x y hx hy =>
        obtain ⟨x', hx'⟩ := hx
        obtain ⟨y', hy'⟩ := hy
        refine ⟨x' + y', ?_⟩
        simp [map_add, hx', hy']
    | tmul a m =>
        have hspan : ∀ (a : S) (ha : a ∈ J), ∀ m : M,
            ∃ u : TensorProduct R (I : Type u) M,
              TensorProduct.tmul S (⟨a, ha⟩ : J) m = K u := by
          intro a ha
          change a ∈ Submodule.span S (f '' (I : Set R)) at ha
          refine Submodule.span_induction
            (p := fun a ha => ∀ m : M,
              ∃ u : TensorProduct R (I : Type u) M,
                TensorProduct.tmul S (⟨a, ha⟩ : J) m = K u) ?_ ?_ ?_ ?_ ha
          · intro a ha m
            rcases ha with ⟨b, hb, rfl⟩
            exact ⟨TensorProduct.tmul R (⟨b, hb⟩ : I) m, by simp [K]⟩
          · intro m
            exact ⟨0, by rw [TensorProduct.zero_tmul, map_zero]⟩
          · intro x y _ _ hx hy m
            obtain ⟨u, hu⟩ := hx m
            obtain ⟨v, hv⟩ := hy m
            exact ⟨u + v, by
              rw [TensorProduct.add_tmul, map_add, hu, hv]⟩
          · intro s x _ hx m
            obtain ⟨u, hu⟩ := hx (s • m)
            refine ⟨u, ?_⟩
            change TensorProduct.tmul S (s • x) m = K u
            exact (TensorProduct.tmul_smul (R := S) s (x : J) m).symm.trans hu
        obtain ⟨u, hu⟩ := hspan (a : S) a.property m
        exact ⟨u, hu.symm⟩
  letI : IsScalarTower R S T :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : LinearMap.CompatibleSMul T M R S :=
    ⟨fun F r x => by
      rw [← IsScalarTower.algebraMap_smul S r x,
        ← IsScalarTower.algebraMap_smul S r (F x), F.map_smul]⟩
  let AmapJ := Formalization.Books.Algebra.Unit75.idealTensorActionMap J
      (ModuleCat.of S M)
  have hKaction :
      (AmapJ.restrictScalars R).comp K = AmapI := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [AmapI, AmapJ, K]
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul a m =>
        simp [AmapI, AmapJ, K, hcomm]
  have hAmapJ : Function.Injective AmapJ := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := hKsurj x
    obtain ⟨y', rfl⟩ := hKsurj y
    have hxy' := hxy
    change (AmapJ.restrictScalars R) (K x') =
      (AmapJ.restrictScalars R) (K y') at hxy'
    rw [hKaction, hKaction]
    have hxyI : x' = y' := hAmapI hxy'
    simpa [hxyI]
  have hTorJ0 : IsZero
      (Formalization.Books.Algebra.Unit75.Tor
        (ModuleCat.of S M) (ModuleCat.of S (S ⧸ J)) 1) := by
    obtain ⟨eTor⟩ :=
      Formalization.Books.Algebra.Unit75.tor_one_ideal_quotient_kernel
        (ModuleCat.of S M) J
    let _ : Subsingleton (LinearMap.ker AmapJ) :=
      ⟨fun x y => Subtype.ext (hAmapJ (x.property.trans y.property.symm))⟩
    have hkernel : IsZero
        (Formalization.Books.Algebra.Unit75.idealTensorActionKernel J
          (ModuleCat.of S M)) := by
      change IsZero (ModuleCat.of S (LinearMap.ker AmapJ))
      apply ModuleCat.isZero_of_subsingleton
    exact (Iso.isZero_iff eTor).2 hkernel
  have hTorJ : IsZero
      (Formalization.Books.Algebra.Unit75.Tor
        (ModuleCat.of S (S ⧸ J)) (ModuleCat.of S M) 1) :=
    (Iso.isZero_iff
      (Formalization.Books.Algebra.Unit75.torLeftRightIso
        (ModuleCat.of S (S ⧸ J)) (ModuleCat.of S M) 1)).2 hTorJ0
  have hflatS : Module.Flat S M :=
    (Formalization.Books.Algebra.Unit99.what_does_it_mean
      J hflat_fibre hTorJ).2.2 hJ
  constructor
  · exact hflatS
  · intro q hq
    let Tq := Localization.AtPrime q.asIdeal
    let Mq := LocalizedModule q.asIdeal.primeCompl M
    let Kq := q.asIdeal.ResidueField
    change Nontrivial (M ⊗[S] Kq) at hq
    letI : Algebra R Tq := ((algebraMap S Tq).comp f).toAlgebra
    letI : IsScalarTower R S Tq :=
      IsScalarTower.of_algebraMap_eq' (R := R) (S := S) (A := Tq) (by
        ext r
        rfl)
    letI : Module R Mq := Module.compHom Mq (algebraMap R Tq)
    letI : IsScalarTower R Tq Mq :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    have hflatRq : Module.Flat R Mq := by
      rw [Module.Flat.iff_lTensor_injectiveₛ]
      simp_rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := S)]
      intro P _ _ N
      let gLoc : M →ₗ[S] Mq := LocalizedModule.mkLinearMap
        q.asIdeal.primeCompl M
      have hF : Function.Injective
          (TensorProduct.AlgebraTensorModule.lTensor S M N.subtype) :=
        (Module.Flat.iff_lTensor_injectiveₛ.mp hflat_base) N
      have hmap := IsLocalizedModule.map_injective
        (S := q.asIdeal.primeCompl)
        (f := TensorProduct.AlgebraTensorModule.rTensor R N gLoc)
        (g := TensorProduct.AlgebraTensorModule.rTensor R P gLoc)
        (TensorProduct.AlgebraTensorModule.lTensor S M N.subtype) hF
      simpa [IsLocalizedModule.map_lTensor] using hmap
    have hflatT : Module.Flat Tq Mq := by
      change Module.Flat (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M)
      infer_instance
    have hfiber : Nontrivial (Kq ⊗[Tq] Mq) := by
      let eLoc : Mq ≃ₗ[Tq] Tq ⊗[S] M :=
        LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M
      let e1 := TensorProduct.congr (LinearEquiv.refl Tq Kq) eLoc
      let e2 :=
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          S Tq Kq Kq M).restrictScalars Tq
      let e : Kq ⊗[Tq] Mq ≃ₗ[Tq] Kq ⊗[S] M := e1 ≪≫ₗ e2
      letI : Nontrivial (Kq ⊗[S] M) :=
        (TensorProduct.comm S Kq M).toEquiv.nontrivial
      exact e.toEquiv.symm.nontrivial
    have hfaithful : Module.FaithfullyFlat Tq Mq := by
      apply (Module.FaithfullyFlat.iff_flat_and_proper_ideal Tq Mq).2
      refine ⟨hflatT, ?_⟩
      intro L hL htop
      let m := IsLocalRing.maximalIdeal Tq
      have hm_top : m • (⊤ : Submodule Tq Mq) = ⊤ := by
        apply top_unique
        calc
          (⊤ : Submodule Tq Mq) = L • ⊤ := htop.symm
          _ ≤ m • ⊤ :=
            Submodule.smul_mono (IsLocalRing.le_maximalIdeal hL) le_rfl
      have hzero : ∀ z : Kq ⊗[Tq] Mq, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp [hx, hy]
        | tmul k x =>
            have hx : x ∈ m • (⊤ : Submodule Tq Mq) := by
              rw [hm_top]
              exact Submodule.mem_top
            refine Submodule.smul_induction_on hx ?_ ?_
            · intro r hr y _
              rw [← TensorProduct.tmul_smul]
              simp [IsLocalRing.ResidueField.algebraMap_eq,
                IsLocalRing.residue_eq_zero_iff, hr]
            · intro y z hy hz
              simp [TensorProduct.tmul_add, hy, hz]
      letI : Subsingleton (Kq ⊗[Tq] Mq) :=
        ⟨fun x y => by rw [hzero x, hzero y]⟩
      exact not_subsingleton _ hfiber
    have hflat : Module.Flat R Tq :=
      Formalization.Books.Algebra.Unit39.flat_permanence hflatRq hfaithful
    change RingHom.Flat ((algebraMap S Tq).comp f)
    exact (Formalization.Books.Algebra.Unit39.ringHom_flat_iff_module_flat
      ((algebraMap S Tq).comp f)).2 hflat
/-
  letI : Algebra R S := f.toAlgebra
  letI : Module S M := Module.compHom M g
  letI : Module R M := Module.compHom M h
  have hcomm (r : R) : g (f r) = h r := by
    exact congrArg (fun k : R →+* S' => k r) comm
  letI : IsScalarTower R S M :=
    IsScalarTower.of_algebraMap_smul (fun r m => by
      change g (f r) • m = h r • m
      rw [hcomm])
  let J : Ideal S := Ideal.map f I
  change Module.Flat (S ⧸ J) (M ⧸ (J • (⊤ : Submodule S M))) at hflat_fibre
  change Module.Flat R M at hflat_base
  have hJ : IsNilpotent J := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow, hn]
    simp
  let AmapI := Formalization.Books.Algebra.Unit75.idealTensorActionMap I
      (ModuleCat.of R M)
  let gI : TensorProduct R (I : Type u) M →ₗ[R] M :=
    (TensorProduct.lid R M).toLinearMap.comp (I.subtype.rTensor M)
  have hIinj : Function.Injective (I.subtype.rTensor M) :=
    (Module.Flat.iff_rTensor_injective'.mp hflat_base I)
  have hgI : Function.Injective gI :=
    (TensorProduct.lid R M).injective.comp hIinj
  have hAmapI : Function.Injective AmapI := by
    have hEq : AmapI = gI := by
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp [AmapI, gI]
      | add x y hx hy => simp [AmapI, gI, hx, hy]
      | tmul a m => rfl
    rw [hEq]
    exact hgI
  let T := TensorProduct S (J : Type u) M
  letI : Module R T := Module.compHom T f
  have hsc (r s : R) (x : T) : r • s • x = s • r • x := by
    rw [smul_smul, smul_smul, mul_comm]
  letI : Module R (M →ₗ[R] T) :=
    { smul := fun r k =>
        { toFun := fun m => r • k m
          map_add' := by intro x y; simp [smul_add]
          map_smul' := by
            intro s x
            change r • k (s • x) = s • r • k x
            rw [k.map_smul]
            exact hsc r s (k x) }
      one_smul := by
        intro k
        ext x
        change (1 : R) • k x = k x
        exact one_smul R (k x)
      mul_smul := by
        intro r s k
        ext x
        change (r * s) • k x = r • s • k x
        rw [smul_smul]
      smul_add := by
        intro r k l
        ext x
        change r • (k x + l x) = r • k x + r • l x
        rw [smul_add]
      smul_zero := by
        intro r
        ext x
        change r • (0 : T) = 0
        exact smul_zero r
      add_smul := by
        intro r s k
        ext x
        change (r + s) • k x = r • k x + s • k x
        exact add_smul r s (k x)
      zero_smul := by
        intro k
        ext x
        change (0 : R) • k x = 0
        exact zero_smul R (k x) }
  let K : TensorProduct R (I : Type u) M →ₗ[R] T :=
    TensorProduct.lift (R := R) (R₂ := R) (σ₁₂ := RingHom.id R)
      (M := (I : Type u)) (N := M) (P₂ := T)
      { toFun := fun a =>
          { toFun := fun m =>
              TensorProduct.tmul S
                (⟨f (a : R), Ideal.mem_map_of_mem f a.property⟩ : J) m
            map_add' := by
              intro m n
              rw [TensorProduct.tmul_add]
            map_smul' := by
              intro r m
              change TensorProduct.tmul S
                  (⟨f (a : R), Ideal.mem_map_of_mem f a.property⟩ : J)
                  (h r • m) =
                TensorProduct.tmul S
                  (f r • (⟨f (a : R), Ideal.mem_map_of_mem f a.property⟩ : J)) m
              rw [← hcomm r]
              change TensorProduct.tmul S
                  (⟨f (a : R), Ideal.mem_map_of_mem f a.property⟩ : J)
                  ((f r) • m) =
                TensorProduct.tmul S
                  ((f r) • (⟨f (a : R), Ideal.mem_map_of_mem f a.property⟩ : J)) m
              exact TensorProduct.tmul_smul (f r)
                (⟨f (a : R), Ideal.mem_map_of_mem f a.property⟩ : J) m }
        map_add' := by
          intro a b
          ext m
          change TensorProduct.tmul S
              (⟨f (a + b),
                Ideal.mem_map_of_mem f (I.add_mem a.2 b.2)⟩ : J) m =
            TensorProduct.tmul S
              (⟨f a, Ideal.mem_map_of_mem f a.property⟩ : J) m +
              TensorProduct.tmul S
                (⟨f b, Ideal.mem_map_of_mem f b.property⟩ : J) m
          rw [map_add, add_tmul]
        map_smul' := by
          intro r a
          ext m
          change TensorProduct.tmul S
              (⟨f (r * (a : R)),
                Ideal.mem_map_of_mem f (I.mul_mem_left r a.2)⟩ : J) m =
            (f r) • TensorProduct.tmul S
              (⟨f (a : R), Ideal.mem_map_of_mem f a.property⟩ : J) m
          rw [map_mul, TensorProduct.smul_tmul]
          rfl }
  have hKsurj : Function.Surjective K := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [K]⟩
    | add x y hx hy =>
        obtain ⟨x', hx'⟩ := hx
        obtain ⟨y', hy'⟩ := hy
        refine ⟨x' + y', ?_⟩
        simp [map_add, hx', hy']
    | tmul a m =>
        have hspan : ∀ (a : S) (ha : a ∈ J), ∀ m : M,
            ∃ u : TensorProduct R (I : Type u) M,
              TensorProduct.tmul S (⟨a, ha⟩ : J) m = K u := by
          intro a ha
          change a ∈ Submodule.span S (f '' (I : Set R)) at ha
          refine Submodule.span_induction
            (p := fun a ha => ∀ m : M,
              ∃ u : TensorProduct R (I : Type u) M,
                TensorProduct.tmul S (⟨a, ha⟩ : J) m = K u) ?_ ?_ ?_ ?_ ha
          · intro a ha m
            rcases ha with ⟨b, hb, rfl⟩
            exact ⟨TensorProduct.tmul R (⟨b, hb⟩ : I) m, by simp [K]⟩
          · intro m
            exact ⟨0, by rw [TensorProduct.zero_tmul, map_zero]⟩
          · intro x y _ _ hx hy m
            obtain ⟨u, hu⟩ := hx m
            obtain ⟨v, hv⟩ := hy m
            exact ⟨u + v, by
              rw [TensorProduct.add_tmul, map_add, hu, hv]⟩
          · intro s x _ hx m
            obtain ⟨u, hu⟩ := hx (s • m)
            refine ⟨u, ?_⟩
            change TensorProduct.tmul S (s • x) m = K u
            exact (TensorProduct.tmul_smul (R := S) s (x : J) m).symm.trans hu
        obtain ⟨u, hu⟩ := hspan (a : S) a.property m
        exact ⟨u, hu.symm⟩
  letI : IsScalarTower R S T :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : LinearMap.CompatibleSMul T M R S :=
    ⟨fun F r x => by
      rw [← IsScalarTower.algebraMap_smul S r x,
        ← IsScalarTower.algebraMap_smul S r (F x), F.map_smul]⟩
  let AmapJ := Formalization.Books.Algebra.Unit75.idealTensorActionMap J
      (ModuleCat.of S M)
  have hKaction :
      (AmapJ.restrictScalars R).comp K = AmapI := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [AmapI, AmapJ, K]
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul a m =>
        simp [AmapI, AmapJ, K, hcomm]
  have hAmapJ : Function.Injective AmapJ := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := hKsurj x
    obtain ⟨y', rfl⟩ := hKsurj y
    have hxy' := hxy
    change (AmapJ.restrictScalars R) (K x') =
      (AmapJ.restrictScalars R) (K y') at hxy'
    rw [hKaction, hKaction]
    have hxyI : x' = y' := hAmapI hxy'
    simpa [hxyI]
  have hTorJ0 : IsZero
      (Formalization.Books.Algebra.Unit75.Tor
        (ModuleCat.of S M) (ModuleCat.of S (S ⧸ J)) 1) := by
    obtain ⟨eTor⟩ :=
      Formalization.Books.Algebra.Unit75.tor_one_ideal_quotient_kernel
        (ModuleCat.of S M) J
    let _ : Subsingleton (LinearMap.ker AmapJ) :=
      ⟨fun x y => Subtype.ext (hAmapJ (x.property.trans y.property.symm))⟩
    have hkernel : IsZero
        (Formalization.Books.Algebra.Unit75.idealTensorActionKernel J
          (ModuleCat.of S M)) := by
      change IsZero (ModuleCat.of S (LinearMap.ker AmapJ))
      apply ModuleCat.isZero_of_subsingleton
    exact (Iso.isZero_iff eTor).2 hkernel
  have hTorJ : IsZero
      (Formalization.Books.Algebra.Unit75.Tor
        (ModuleCat.of S (S ⧸ J)) (ModuleCat.of S M) 1) :=
    (Iso.isZero_iff
      (Formalization.Books.Algebra.Unit75.torLeftRightIso
        (ModuleCat.of S (S ⧸ J)) (ModuleCat.of S M) 1)).2 hTorJ0
  have hflatS : Module.Flat S M :=
    (Formalization.Books.Algebra.Unit99.what_does_it_mean
      J hflat_fibre hTorJ).2.2 hJ
  constructor
  · exact hflatS
  · intro q hq
    let Tq := Localization.AtPrime q.asIdeal
    let Mq := LocalizedModule q.asIdeal.primeCompl M
    let Kq := q.asIdeal.ResidueField
    change Nontrivial (M ⊗[S] Kq) at hq
    letI : Algebra R Tq := ((algebraMap S Tq).comp f).toAlgebra
    letI : IsScalarTower R S Tq :=
      IsScalarTower.of_algebraMap_eq' (R := R) (S := S) (A := Tq) (by
        ext r
        rfl)
    letI : Module R Mq := Module.compHom Mq (algebraMap R Tq)
    letI : IsScalarTower R Tq Mq :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    have hflatRq : Module.Flat R Mq := by
      rw [Module.Flat.iff_lTensor_injectiveₛ]
      simp_rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := S)]
      intro P _ _ N
      let gLoc : M →ₗ[S] Mq := LocalizedModule.mkLinearMap
        q.asIdeal.primeCompl M
      have hF : Function.Injective
          (TensorProduct.AlgebraTensorModule.lTensor S M N.subtype) :=
        (Module.Flat.iff_lTensor_injectiveₛ.mp hflat_base) N
      have hmap := IsLocalizedModule.map_injective
        (S := q.asIdeal.primeCompl)
        (f := TensorProduct.AlgebraTensorModule.rTensor R N gLoc)
        (g := TensorProduct.AlgebraTensorModule.rTensor R P gLoc)
        (TensorProduct.AlgebraTensorModule.lTensor S M N.subtype) hF
      simpa [IsLocalizedModule.map_lTensor] using hmap
    have hflatT : Module.Flat Tq Mq := by
      change Module.Flat (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M)
      infer_instance
    have hfiber : Nontrivial (Kq ⊗[Tq] Mq) := by
      let eLoc : Mq ≃ₗ[Tq] Tq ⊗[S] M :=
        LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M
      let e1 := TensorProduct.congr (LinearEquiv.refl Tq Kq) eLoc
      let e2 :=
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          S Tq Kq Kq M).restrictScalars Tq
      let e : Kq ⊗[Tq] Mq ≃ₗ[Tq] Kq ⊗[S] M := e1 ≪≫ₗ e2
      letI : Nontrivial (Kq ⊗[S] M) :=
        (TensorProduct.comm S Kq M).toEquiv.nontrivial
      exact e.toEquiv.symm.nontrivial
    have hfaithful : Module.FaithfullyFlat Tq Mq := by
      apply (Module.FaithfullyFlat.iff_flat_and_proper_ideal Tq Mq).2
      refine ⟨hflatT, ?_⟩
      intro L hL htop
      let m := IsLocalRing.maximalIdeal Tq
      have hm_top : m • (⊤ : Submodule Tq Mq) = ⊤ := by
        apply top_unique
        calc
          (⊤ : Submodule Tq Mq) = L • ⊤ := htop.symm
          _ ≤ m • ⊤ :=
            Submodule.smul_mono (IsLocalRing.le_maximalIdeal hL) le_rfl
      have hzero : ∀ z : Kq ⊗[Tq] Mq, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp [hx, hy]
        | tmul k x =>
            have hx : x ∈ m • (⊤ : Submodule Tq Mq) := by
              rw [hm_top]
              exact Submodule.mem_top
            refine Submodule.smul_induction_on hx ?_ ?_
            · intro r hr y _
              rw [← TensorProduct.tmul_smul]
              simp [IsLocalRing.ResidueField.algebraMap_eq,
                IsLocalRing.residue_eq_zero_iff, hr]
            · intro y z hy hz
              simp [TensorProduct.tmul_add, hy, hz]
      letI : Subsingleton (Kq ⊗[Tq] Mq) :=
        ⟨fun x y => by rw [hzero x, hzero y]⟩
      exact not_subsingleton _ hfiber
    have hflat : Module.Flat R Tq :=
      Formalization.Books.Algebra.Unit39.flat_permanence hflatRq hfaithful
    change RingHom.Flat ((algebraMap S Tq).comp f)
    exact (Formalization.Books.Algebra.Unit39.ringHom_flat_iff_module_flat
      ((algebraMap S Tq).comp f)).2 hflat

 -/
end

end Formalization.Books.Algebra.Unit101
