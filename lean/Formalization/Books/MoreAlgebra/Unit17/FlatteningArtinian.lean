import Formalization.Books.MoreAlgebra.Unit16.FlatteningStratification
import Formalization.Books.Algebra.Unit101.FlatnessCriteriaArtinian
import Mathlib.RingTheory.Ideal.Maps

/-!
# More on Algebra, Chapter 17: Flattening over an Artinian ring

The source's quotient `M / IM` is represented by the canonical quotient module
`M ⧸ (I • ⊤)`, and the condition `φ(I) = 0` is represented by
`I.map φ = ⊥`.
-/

namespace Formalization.Books.MoreAlgebra.Unit17

universe uR uS uM

open scoped TensorProduct

noncomputable section

/-! ## Flattening over an Artinian ring -/

/- The opening discussion is accounted for by the stronger result below for
   every Artinian ring and every module.  The final scheme-theoretic
   consequence, concerning a base that is the spectrum of an Artinian local
   ring, is a roadmap to the later flattening-stratification sections rather
   than a separate algebraic declaration in this section. -/

/-- The ideals whose quotient makes `M` flat over the corresponding quotient
ring. -/
def flatQuotientIdeals
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] : Set (Ideal R) :=
  {I | Module.Flat (R ⧸ I)
    (M ⧸ (I • (⊤ : Submodule R M)))}

/-- The least ideal in `flatQuotientIdeals`, once existence is known. -/
def flatteningIdeal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] : Ideal R :=
  sInf (flatQuotientIdeals (R := R) (M := M))

/-- A base change of `M` along `φ` is flat over its target ring. -/
def IsFlatAfterBaseChange
    {R R' M : Type*} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] (φ : R →+* R') : Prop :=
  letI : Algebra R R' := φ.toAlgebra
  Module.Flat R' (R' ⊗[R] M)

/- The proof of the source lemma uses the preceding intersection lemma to show
   that the relevant set of ideals is closed under intersections, together
   with the Artinian minimum principle. -/

/-- Over an Artinian ring, there is a smallest ideal whose quotient makes the
module flat over the quotient ring. -/
theorem exists_isLeast_flatQuotientIdeal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] :
    ∃ I : Ideal R, IsLeast (flatQuotientIdeals (R := R) (M := M)) I := by
  have htop : flatQuotientIdeals (R := R) (M := M) (⊤ : Ideal R) := by
    dsimp [flatQuotientIdeals]
    let _ : Subsingleton (R ⧸ (⊤ : Ideal R)) := inferInstance
    let _ : Subsingleton
        (M ⧸ ((⊤ : Ideal R) • (⊤ : Submodule R M))) := by
      rw [show (⊤ : Ideal R) • (⊤ : Submodule R M) = ⊤ by simp]
      infer_instance
    exact Module.Flat.of_free
  obtain ⟨I, hImem, hImin⟩ :=
    IsArtinian.set_has_minimal
      (a := flatQuotientIdeals (R := R) (M := M)) ⟨⊤, htop⟩
  refine ⟨I, hImem, ?_⟩
  intro J hJ
  have hInfmem : flatQuotientIdeals (R := R) (M := M) (J ⊓ I) :=
    Formalization.Books.MoreAlgebra.Unit16.flat_quotient_inf_of_flat_quotients
      J I hJ hImem
  have hle : I ≤ (J ⊓ I : Ideal R) := by
    by_cases h : I ≤ (J ⊓ I : Ideal R)
    · exact h
    · have hne : (J ⊓ I : Ideal R) ≠ I := by
        intro heq
        apply h
        rw [heq]
      exact False.elim
        (hImin (J ⊓ I) hInfmem (lt_of_le_of_ne inf_le_right hne))
  exact le_trans hle (inf_le_left : J ⊓ I ≤ J)

/-- The canonical infimum construction is the smallest flatness ideal over an
Artinian ring. -/
theorem flatteningIdeal_isLeast
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] :
    IsLeast (flatQuotientIdeals (R := R) (M := M))
      (flatteningIdeal (R := R) (M := M)) := by
  obtain ⟨I, hI⟩ := exists_isLeast_flatQuotientIdeal (R := R) (M := M)
  have hle : I ≤ flatteningIdeal (R := R) (M := M) := by
    apply le_sInf
    intro J hJ
    exact hI.2 hJ
  have hge : flatteningIdeal (R := R) (M := M) ≤ I := by
    dsimp [flatteningIdeal]
    exact sInf_le hI.1
  have heq : flatteningIdeal (R := R) (M := M) = I :=
    le_antisymm hge hle
  simpa only [heq] using hI

private def tensor_lid_of_algebraMap_surjective
    {R A N : Type*} [CommSemiring R] [CommSemiring A]
    [AddCommMonoid N] [Algebra R A] [Module R N] [Module A N]
    [IsScalarTower R A N] [SMulCommClass R A N]
    (hsurj : Function.Surjective (algebraMap R A)) :
    A ⊗[R] N ≃ₗ[A] N := by
  let f : A →ₗ[A] N →ₗ[R] N :=
    { toFun := fun a =>
        { toFun := fun n => a • n
          map_add' := fun _ _ => smul_add _ _ _
          map_smul' := fun r n => (smul_comm r a n).symm }
      map_add' := fun a b => by
        ext n
        exact add_smul a b n
      map_smul' := fun a b => by
        ext n
        exact mul_smul a b n }
  let g : N →ₗ[A] A ⊗[R] N :=
    { toFun := fun n => 1 ⊗ₜ[R] n
      map_add' := fun _ _ => by rw [TensorProduct.tmul_add]
      map_smul' := fun a n => by
        obtain ⟨r, rfl⟩ := hsurj a
        simp [← TensorProduct.tmul_smul] }
  refine LinearEquiv.ofLinear (TensorProduct.AlgebraTensorModule.lift f) g ?_ ?_
  · apply LinearMap.ext
    intro n
    simp [f, g]
  · apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [f, g]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a n =>
      change g (a • n) = a ⊗ₜ[R] n
      rw [g.map_smul]
      change a • ((1 : A) ⊗ₜ[R] n) = a ⊗ₜ[R] n
      rw [TensorProduct.smul_tmul']
      simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, mul_one]

private theorem descent_flatness_injective_map_artinian_rings
    {R : Type uR} {S : Type uS} {M : Type uM}
    [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] (φ : R →+* S) (hφ : Function.Injective φ)
    (hflat :
      letI : Algebra R S := φ.toAlgebra
      Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := by
  let _ : Algebra R S := φ.toAlgebra
  let eR : ULift.{max uR (max uS uM)} R ≃+* R := ULift.ringEquiv
  let eS : ULift.{max uR (max uS uM)} S ≃+* S := ULift.ringEquiv
  let φU : ULift.{max uR (max uS uM)} R →+*
      ULift.{max uR (max uS uM)} S :=
    eS.symm.toRingHom.comp (φ.comp eR.toRingHom)
  have hφU : Function.Injective φU := by
    dsimp [φU]
    exact eS.symm.injective.comp (hφ.comp eR.injective)
  let _ : IsArtinianRing (ULift.{max uR (max uS uM)} R) :=
    eR.symm.isArtinianRing
  let eUL :
      ULift.{max uR (max uS uM)} (S ⊗[R] M) ≃ₗ[ULift.{max uR (max uS uM)} S]
        (ULift.{max uR (max uS uM)} S) ⊗[ULift.{max uR (max uS uM)} R]
          (ULift.{max uR (max uS uM)} M) :=
    TensorProduct.AlgebraTensorModule.uliftEquiv
      R (ULift.{max uR (max uS uM)} S) S M
  have hflatUL :
      Module.Flat (ULift.{max uR (max uS uM)} S)
        (ULift.{max uR (max uS uM)} (S ⊗[R] M)) := by
    apply (Module.Flat.ulift_left_iff).2
    exact (Module.Flat.ulift_right_iff).2 hflat
  have hflatU :
      Module.Flat (ULift.{max uR (max uS uM)} S)
        ((ULift.{max uR (max uS uM)} S) ⊗[ULift.{max uR (max uS uM)} R]
          (ULift.{max uR (max uS uM)} M)) := by
    let _ : Module.Flat (ULift.{max uR (max uS uM)} S)
        (ULift.{max uR (max uS uM)} (S ⊗[R] M)) := hflatUL
    exact Module.Flat.of_linearEquiv eUL.symm
  have hdescU :
      Module.Flat (ULift.{max uR (max uS uM)} R)
        (ULift.{max uR (max uS uM)} M) := by
    refine Formalization.Books.Algebra.Unit101.descent_flatness_injective_map_artinian_rings
      (R := ULift.{max uR (max uS uM)} R)
      (S := ULift.{max uR (max uS uM)} S)
      (M := ULift.{max uR (max uS uM)} M) φU hφU ?_
    exact hflatU
  exact (Module.Flat.ulift_right_iff).mp ((Module.Flat.ulift_left_iff).mp hdescU)

/- The forward implication in the source is flatness after base change; the
   reverse implication uses the kernel quotient and the Artinian descent
   theorem `descent_flatness_injective_map_artinian_rings`. -/

/-- The smallest flatness ideal is characterized by the universal property of
the flattening over every ring map out of the Artinian base. -/
theorem flatteningIdeal_universal_property
    {R R' M : Type*} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] [IsArtinianRing R]
    (I : Ideal R)
    (hI : IsLeast (flatQuotientIdeals (R := R) (M := M)) I)
    (φ : R →+* R') :
    IsFlatAfterBaseChange (M := M) φ ↔ I.map φ = ⊥ := by
  constructor
  · intro hflat
    let _ : Algebra R R' := φ.toAlgebra
    dsimp [IsFlatAfterBaseChange] at hflat
    let J : Ideal R := RingHom.ker φ
    let ψ : R ⧸ J →+* R' := RingHom.kerLift φ
    let _ : Algebra (R ⧸ J) R' := ψ.toAlgebra
    let _ : IsScalarTower R (R ⧸ J) R' :=
      IsScalarTower.of_algebraMap_eq (fun r => by
        change φ r = ψ (Ideal.Quotient.mk J r)
        rfl)
    have hψ : Function.Injective ψ := by
      exact RingHom.kerLift_injective φ
    have hJmap : J.map φ = ⊥ := by
      apply (Ideal.map_eq_bot_iff_le_ker φ).2
      change RingHom.ker φ ≤ RingHom.ker φ
      exact le_rfl
    have hsmul :
        J.map φ • (⊤ : Submodule R' (R' ⊗[R] M)) = ⊥ := by
      rw [hJmap]
      simp
    let _ : IsScalarTower R (R ⧸ J)
        (M ⧸ (J • (⊤ : Submodule R M))) :=
      (Module.isTorsionBySet_quotient_ideal_smul M J).isScalarTower
    let _ : IsScalarTower R (R ⧸ J) (R ⧸ J) :=
      inferInstance
    have hsurjJ : Function.Surjective (algebraMap R (R ⧸ J)) := by
      simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := J))
    let elid :
        (R ⧸ J) ⊗[R] (M ⧸ (J • (⊤ : Submodule R M))) ≃ₗ[R ⧸ J]
          (M ⧸ (J • (⊤ : Submodule R M))) :=
      tensor_lid_of_algebraMap_surjective hsurjJ
    let ebase :
        (R' ⊗[R] M) ≃ₗ[R'] R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M))) :=
      (Submodule.quotEquivOfEqBot
        (M := R' ⊗[R] M)
        (p := J.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M))) hsmul).symm ≪≫ₗ
        TensorProduct.tensorQuotMapSMulEquivTensorQuot M R' J
    let e :
        (R' ⊗[R ⧸ J] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R'] R' ⊗[R] M :=
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) elid.symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ J) R' R'
        (M ⧸ (J • (⊤ : Submodule R M))) ≪≫ₗ ebase.symm
    have _ : Module.Flat R' (R' ⊗[R] M) := hflat
    have hflatquot :
        Module.Flat (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))) := by
      refine descent_flatness_injective_map_artinian_rings
        (R := R ⧸ J) (S := R')
        (M := M ⧸ (J • (⊤ : Submodule R M))) ψ hψ ?_
      exact Module.Flat.of_linearEquiv e
    exact (Ideal.map_eq_bot_iff_le_ker φ).2 (hI.2 hflatquot)
  · intro hmap
    let _ : Algebra R R' := φ.toAlgebra
    dsimp [IsFlatAfterBaseChange]
    have hleker : I ≤ RingHom.ker φ :=
      (Ideal.map_eq_bot_iff_le_ker φ).mp hmap
    let ψ : R ⧸ I →+* R' :=
      Ideal.Quotient.lift I φ (fun a ha => hleker ha)
    let _ : Algebra (R ⧸ I) R' := ψ.toAlgebra
    let _ : IsScalarTower R (R ⧸ I) R' :=
      IsScalarTower.of_algebraMap_eq (fun r => by
        change φ r = ψ (Ideal.Quotient.mk I r)
        rfl)
    have _ : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := hI.1
    have hsmul :
        I.map φ • (⊤ : Submodule R' (R' ⊗[R] M)) = ⊥ := by
      rw [hmap]
      simp
    let _ : IsScalarTower R (R ⧸ I)
        (M ⧸ (I • (⊤ : Submodule R M))) :=
      (Module.isTorsionBySet_quotient_ideal_smul M I).isScalarTower
    let _ : IsScalarTower R (R ⧸ I) (R ⧸ I) :=
      inferInstance
    have hsurjI : Function.Surjective (algebraMap R (R ⧸ I)) := by
      simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I))
    let elid :
        (R ⧸ I) ⊗[R] (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I]
          (M ⧸ (I • (⊤ : Submodule R M))) :=
      tensor_lid_of_algebraMap_surjective hsurjI
    let ebase :
        (R' ⊗[R] M) ≃ₗ[R'] R' ⊗[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
      (Submodule.quotEquivOfEqBot
        (M := R' ⊗[R] M)
        (p := I.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M))) hsmul).symm ≪≫ₗ
        TensorProduct.tensorQuotMapSMulEquivTensorQuot M R' I
    let e :
        (R' ⊗[R ⧸ I] (M ⧸ (I • (⊤ : Submodule R M)))) ≃ₗ[R'] R' ⊗[R] M :=
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) elid.symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) R' R'
        (M ⧸ (I • (⊤ : Submodule R M))) ≪≫ₗ ebase.symm
    exact Module.Flat.of_linearEquiv e.symm

end

end Formalization.Books.MoreAlgebra.Unit17
