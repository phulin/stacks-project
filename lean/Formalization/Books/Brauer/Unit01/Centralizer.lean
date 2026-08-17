import Formalization.Books.Brauer.Unit01.SkolemNoether
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

/-!
# The centralizer theorem

The canonical `Subalgebra.centralizer` is used throughout.  A small
source-facing predicate packages the textbook notion of a maximal
commutative subalgebra.
-/

namespace Formalization.Books.Brauer

open scoped TensorProduct

/-- A commutative subalgebra maximal among commutative subalgebras. -/
def IsMaximalCommutativeSubalgebra (k A : Type*) [CommSemiring k]
    [Semiring A] [Algebra k A] (S : Subalgebra k A) : Prop :=
  (∀ x y : S, Commute (x : A) (y : A)) ∧
    ∀ T : Subalgebra k A,
      (∀ x y : T, Commute (x : A) (y : A)) → S ≤ T → T = S

private theorem smulCommClass_of_algebra (k D M : Type*) [Field k] [Ring D]
    [Algebra k D] [AddCommGroup M] [Module D M] [Module k M]
    [IsScalarTower k D M] : SMulCommClass D k M := by
  constructor
  intro d r m
  calc
    d • (r • m) = d • ((algebraMap k D r) • m) := by
      rw [IsScalarTower.algebraMap_smul]
    _ = (d * algebraMap k D r) • m := (mul_smul _ _ _).symm
    _ = (algebraMap k D r * d) • m := by rw [Algebra.commutes]
    _ = (algebraMap k D r) • (d • m) := mul_smul _ _ _
    _ = r • (d • m) := IsScalarTower.algebraMap_smul D r (d • m)

private theorem finrank_end_fin (k D M : Type*) (n : ℕ) [Field k] [Ring D]
    [Algebra k D] [AddCommGroup M] [Module D M] [Module k M]
    [SMulCommClass D k M] [IsScalarTower k D M] :
    Module.finrank k (Module.End D (Fin n → M)) =
      n ^ 2 * Module.finrank k (Module.End D M) := by
  calc
    Module.finrank k (Module.End D (Fin n → M)) =
        Module.finrank k (Matrix (Fin n) (Fin n) (Module.End D M)) :=
      (endVecAlgEquivMatrixEnd (R := k) (A := D) (ι := Fin n) (M := M)).toLinearEquiv.finrank_eq
    _ = n ^ 2 * Module.finrank k (Module.End D M) := by
      simp [Module.finrank_matrix, pow_two]

private theorem finrank_end_linearEquiv (k D M N : Type*) [Field k] [Ring D]
    [Algebra k D] [AddCommGroup M] [Module D M] [Module k M]
    [SMulCommClass D k M] [IsScalarTower k D M] [AddCommGroup N]
    [Module D N] [Module k N] [SMulCommClass D k N]
    [IsScalarTower k D N] (e : M ≃ₗ[D] N) :
    Module.finrank k (Module.End D M) = Module.finrank k (Module.End D N) := by
  exact (e.conjAlgEquiv k).toLinearEquiv.finrank_eq

theorem centralizer_theorem (k A : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]
    (B : Subalgebra k A) [IsSimpleRing B] :
    let C := Subalgebra.centralizer k (B : Set A)
    IsSimpleRing C ∧
        Module.finrank k A = Module.finrank k B * Module.finrank k C ∧
        Subalgebra.centralizer k (C : Set A) = B := by
  classical
  dsimp
  have core : ∀ (B' : Subalgebra k A), IsSimpleRing B' →
      IsSimpleRing (Subalgebra.centralizer k (B' : Set A)) ∧
        Module.finrank k A = Module.finrank k B' *
          Module.finrank k (Subalgebra.centralizer k (B' : Set A)) := by
    intro B' hB'
    letI : IsSimpleRing B' := hB'
    let C' : Subalgebra k A := Subalgebra.centralizer k (B' : Set A)
    change IsSimpleRing C' ∧
      Module.finrank k A = Module.finrank k B' * Module.finrank k C'
    obtain ⟨M, hM⟩ := finite_algebra_has_simple_submodule k A
    letI : IsSimpleModule A M := hM
    letI : Nontrivial M := IsSimpleModule.nontrivial A M
    letI : Module.Finite k M :=
      simple_module_over_finite_algebra_is_finite_dimensional k A M
    let L := Module.End A M
    letI : FiniteDimensional k L :=
      (simple_module_center_and_dimension k A M).2.1
    let eCenter : Subalgebra.center k A ≃ₐ[k] Subalgebra.center k L :=
      Classical.choice (simple_module_center_and_dimension k A M).1
    letI : Algebra.IsCentral k L := by
      constructor
      intro z hz
      let z' : Subalgebra.center k A := eCenter.symm ⟨z, hz⟩
      obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out z'.property)
      refine ⟨r, ?_⟩
      let za : Subalgebra.center k A := ⟨algebraMap k A r, by
        simpa [hr] using z'.property⟩
      have hz' : z' = za := by
        apply Subtype.ext
        exact hr.symm
      have hz'' := congrArg (fun w : Subalgebra.center k A => (eCenter w : L)) hz'
      have hza : (eCenter za : L) = algebraMap k L r := by
        simpa [za] using eCenter.commutes r
      calc
        algebraMap k L r = (eCenter za : L) := hza.symm
        _ = (eCenter z' : L) := hz''.symm
        _ = z := by simp [z']
    let module_B : Module B' M := Module.compHom M B'.val.toRingHom
    let tower_B : @IsScalarTower k B' M _
        module_B.toDistribMulAction.toSMul _ := by
      letI : Module B' M := module_B
      exact IsScalarTower.of_algebraMap_smul (R := k) (A := B') (M := M)
        (fun r m => by
          change B'.val (algebraMap k B' r) • m = r • m
          rw [B'.val.commutes]
          exact IsScalarTower.algebraMap_smul A r m)
    let tower_L : IsScalarTower k L M := Module.End.apply_isScalarTower
    let comm_B_L : @SMulCommClass B' L M
        module_B.toDistribMulAction.toSMul _ := by
      letI : Module B' M := module_B
      exact ⟨by
        intro b l m
        change (b : A) • (l • m) = l • ((b : A) • m)
        exact (l.map_smul (b : A) m).symm⟩
    let D := (B' ⊗[k] L)
    let module_D : Module D M := by
      letI : Module B' M := module_B
      letI : IsScalarTower k B' M := tower_B
      letI : IsScalarTower k L M := tower_L
      letI : SMulCommClass B' L M := comm_B_L
      exact TensorProduct.Algebra.module
    let tower_D : @IsScalarTower k D M _
        module_D.toDistribMulAction.toSMul _ := by
      letI : Module B' M := module_B
      letI : IsScalarTower k B' M := tower_B
      letI : IsScalarTower k L M := tower_L
      letI : SMulCommClass B' L M := comm_B_L
      letI : Module D M := module_D
      exact IsScalarTower.of_algebraMap_smul (R := k) (A := D) (M := M)
        (fun r m => by
          change (algebraMap k (B' ⊗[k] L) r) • m = r • m
          rw [Algebra.TensorProduct.algebraMap_apply' (R := k) (A := B')
            (B := L) r]
          rw [TensorProduct.Algebra.smul_def]
          change (1 : B') • ((algebraMap k L r) • m) = r • m
          rw [one_smul]
          exact IsScalarTower.algebraMap_smul L r m)
    let finite_D : @Module.Finite D M _ _ module_D := by
      letI : Module D M := module_D
      letI : IsScalarTower k D M := tower_D
      exact Module.Finite.of_restrictScalars_finite k D M
    letI : IsSimpleRing D := tensor_product_simple_of_simple_algebras k B' L
    letI : FiniteDimensional k D := inferInstance
    letI : Module D M := module_D
    letI : IsScalarTower k D M := tower_D
    letI : Module.Finite D M := finite_D
    let E := Module.End D M
    let comm_A_L : @SMulCommClass A L M _ _ :=
      ⟨fun a l m => (l.map_smul a m).symm⟩
    letI : SMulCommClass A L M := comm_A_L
    let rho : A →ₐ[k] Module.End L M :=
      { toRingHom := Module.toModuleEnd L (S := A) M
        commutes' := by
          intro r
          ext m
          rw [Module.algebraMap_end_apply]
          exact congrArg Subtype.val (IsScalarTower.algebraMap_smul A r m) }
    have hAnn : Module.annihilator A M = ⊥ := by
      have h := (isSimpleRing_iff_isTwoSided_imp.mp (inferInstance : IsSimpleRing A)).2
        (Module.annihilator A M) inferInstance
      exact h.resolve_right (by
        intro htop
        exact (not_subsingleton M)
          (Module.annihilator_eq_top_iff.mp htop))
    letI : FaithfulSMul A M := Module.annihilator_eq_bot.mp hAnn
    have hrho : Function.Injective rho := by
      intro a b h
      apply (Module.toModuleEnd L (S := A) M).injective
      simpa [rho] using h
    obtain ⟨eA⟩ := simple_module_double_commutant k A M
    let alpha : A →ₐ[k] A := eA.symm.toAlgHom.comp rho
    have halpha_injective : Function.Injective alpha := eA.symm.injective.comp hrho
    have halpha_surjective : Function.Surjective alpha :=
      LinearMap.surjective_of_injective (f := alpha.toLinearMap) halpha_injective
    let alphaE : A ≃ₐ[k] A := AlgEquiv.ofBijective alpha
      ⟨halpha_injective, halpha_surjective⟩
    have hrho_surjective : Function.Surjective rho := by
      intro z
      obtain ⟨a, ha⟩ := alphaE.surjective (eA.symm z)
      refine ⟨a, ?_⟩
      apply eA.symm.injective
      change alpha a = eA.symm z at ha
      simpa [alpha] using ha
    let rhoE : A ≃ₐ[k] Module.End L M := AlgEquiv.ofBijective rho
      ⟨hrho, hrho_surjective⟩
    let e_toEnd : E →ₐ[k] Module.End L M :=
      { toRingHom :=
          { toFun := fun u =>
              { toFun := u
                map_add' := u.map_add
                map_smul' := by
                  intro l m
                  letI : Module B' M := module_B
                  letI : IsScalarTower k B' M := tower_B
                  letI : IsScalarTower k L M := tower_L
                  letI : SMulCommClass B' L M := comm_B_L
                  have hs : ((1 : B') ⊗ₜ[k] l) • m = l • m := by
                    change (1 : B') • (l • m) = l • m
                    simp
                  have h := u.map_smul ((1 : B') ⊗ₜ[k] l) m
                  have ht : ((1 : B') ⊗ₜ[k] l) • u m = l • u m := by
                    change (1 : B') • (l • u m) = l • u m
                    simp
                  rw [hs, ht] at h
                  exact h }
            map_one' := by
              ext m
              rfl
            map_mul' := by
              intro u v
              ext m
              rfl
            map_zero' := by
              ext m
              rfl
            map_add' := by
              intro u v
              ext m
              rfl }
        commutes' := by
          intro r
          ext m
          rw [Module.algebraMap_end_apply]
          rfl }
    let e_toA : E →ₐ[k] A := rhoE.symm.toAlgHom.comp e_toEnd
    have hmem : ∀ u : E, e_toA u ∈ C' := by
      intro u
      rw [Subalgebra.mem_centralizer_iff]
      intro b hb
      apply rhoE.injective
      rw [map_mul, map_mul]
      simp [e_toA, rhoE]
      change rho (b : A) * e_toEnd u = e_toEnd u * rho (b : A)
      ext m
      letI : Module B' M := module_B
      letI : IsScalarTower k B' M := tower_B
      letI : IsScalarTower k L M := tower_L
      letI : SMulCommClass B' L M := comm_B_L
      have hs : ((⟨b, hb⟩ : B') ⊗ₜ[k] (1 : L)) • m = (b : A) • m := by
        change (b : A) • ((1 : L) • m) = (b : A) • m
        simp
      have h := u.map_smul ((⟨b, hb⟩ : B') ⊗ₜ[k] (1 : L)) m
      have ht : ((⟨b, hb⟩ : B') ⊗ₜ[k] (1 : L)) • u m = (b : A) • u m := by
        change (b : A) • ((1 : L) • u m) = (b : A) • u m
        simp
      rw [hs, ht] at h
      have hv := congrArg Subtype.val h.symm
      simpa [Module.End.mul_eq_comp, rho, e_toEnd] using hv
    have he_toEnd_inj : Function.Injective e_toEnd := by
      intro u v huv
      apply LinearMap.ext
      intro m
      have h := congrArg (fun z : Module.End L M => z m) huv
      simpa [e_toEnd] using h
    let e_toC : E →ₐ[k] C' := e_toA.codRestrict C' (fun u => hmem u)
    have he_toC_inj : Function.Injective e_toC := by
      intro u v huv
      apply he_toEnd_inj
      have h := congrArg Subtype.val huv
      have h' := congrArg rhoE h
      simpa [e_toC, e_toA] using h'
    have he_toC_surj : Function.Surjective e_toC := by
      intro z
      let u_z : M →ₗ[D] M :=
        { toFun := rho (z : A)
          map_add' := by
            intro x y
            exact (rho (z : A)).map_add x y
          map_smul' := by
            intro d m
            letI : Module B' M := module_B
            letI : IsScalarTower k B' M := tower_B
            letI : IsScalarTower k L M := tower_L
            letI : SMulCommClass B' L M := comm_B_L
            induction d using TensorProduct.induction_on with
            | zero =>
                rw [zero_smul (M₀ := D) (A := M) m]
                change (rho (z : A)) 0 = (0 : D) • (rho (z : A)) m
                have hz : (0 : D) • (rho (z : A)) m = 0 :=
                  zero_smul (M₀ := D) (A := M) ((rho (z : A)) m)
                exact (rho (z : A)).map_zero.trans hz.symm
            | add d₁ d₂ h₁ h₂ =>
                simp only [map_add, h₁, h₂, add_smul, RingHom.id_apply]
            | tmul b l =>
                have hcomm : (b : A) * (z : A) = (z : A) * (b : A) :=
                  (Subalgebra.mem_centralizer_iff k).mp z.property (b : A) b.property
                change (z : A) • ((b : A) • (l • m)) =
                  (b : A) • (l • ((z : A) • m))
                calc
                  (z : A) • ((b : A) • (l • m)) =
                      ((z : A) * (b : A)) • (l • m) :=
                    (smul_assoc (z : A) (b : A) (l • m)).symm
                  _ = ((b : A) * (z : A)) • (l • m) := by rw [hcomm]
                  _ = (b : A) • ((z : A) • (l • m)) := mul_smul _ _ _
                  _ = (b : A) • (l • ((z : A) • m)) := by
                    congr 1
                    exact (l.map_smul (z : A) m).symm }
      let u : E := u_z
      refine ⟨u, ?_⟩
      apply Subtype.ext
      change rhoE.symm (rho (z : A)) = (z : A)
      exact rhoE.symm_apply_apply (z : A)
    let eEC : E ≃ₐ[k] C' := AlgEquiv.ofBijective e_toC
      ⟨he_toC_inj, he_toC_surj⟩
    obtain ⟨n, hn, K, hK, hKalg, hKfinite, ⟨eMatrix⟩, _⟩ :=
      finite_module_end_is_matrix_and_double_commutant k D M
    letI : NeZero n := hn
    letI : DivisionRing K := hK
    letI : Algebra k K := hKalg
    letI : FiniteDimensional k K := hKfinite
    have hEsimple : IsSimpleRing E := by
      exact IsSimpleRing.of_ringEquiv eMatrix.toRingEquiv.symm inferInstance
    obtain ⟨S, hS⟩ := finite_algebra_has_simple_submodule k D
    letI : IsSimpleModule D S := hS
    letI : Nontrivial S := IsSimpleModule.nontrivial D S
    letI : Module.Finite k S :=
      simple_module_over_finite_algebra_is_finite_dimensional k D S
    obtain ⟨nM, ⟨eM⟩⟩ := finite_module_is_direct_sum_of_simple k D M S
    have hnM : nM ≠ 0 := by
      intro hn
      subst nM
      have hnontriv : Nontrivial (Fin 0 → S) := eM.injective.nontrivial
      exact (not_nontrivial (Fin 0 → S)) hnontriv
    let comm_D_k_M : SMulCommClass D k M :=
      smulCommClass_of_algebra k D M
    letI : SMulCommClass D k M := comm_D_k_M
    let comm_D_k_S : SMulCommClass D k S :=
      smulCommClass_of_algebra k D S
    letI : SMulCommClass D k S := comm_D_k_S
    let comm_D_k_pi : SMulCommClass D k (Fin nM → S) := by
      constructor
      intro d r v
      funext i
      exact comm_D_k_S.smul_comm d r (v i)
    letI : SMulCommClass D k (Fin nM → S) := comm_D_k_pi
    let eMk := eM.restrictScalars k
    have hMdim : Module.finrank k M = nM * Module.finrank k S := by
      calc
        Module.finrank k M = Module.finrank k (Fin nM → S) :=
          eMk.finrank_eq
        _ = nM * Module.finrank k S := by
          simp [Module.finrank_pi_fintype]
    have hEdim : Module.finrank k E = nM ^ 2 *
        Module.finrank k (Module.End D S) := by
      calc
        Module.finrank k E = Module.finrank k (Module.End D (Fin nM → S)) := by
          change Module.finrank k (Module.End D M) =
            Module.finrank k (Module.End D (Fin nM → S))
          exact finrank_end_linearEquiv k D M (Fin nM → S) eM
        _ = nM ^ 2 * Module.finrank k (Module.End D S) := by
          exact finrank_end_fin k D S nM
    have hDdim : Module.finrank k D = Module.finrank k B' * Module.finrank k L := by
      simp [D, Module.finrank_tensorProduct]
    have hSdim : Module.finrank k D * Module.finrank k (Module.End D S) =
        Module.finrank k S ^ 2 := by
      exact (simple_module_center_and_dimension k D S).2.2
    have hAdim : Module.finrank k A * Module.finrank k L =
        Module.finrank k M ^ 2 :=
      (simple_module_center_and_dimension k A M).2.2
    have hAL : Module.finrank k A * Module.finrank k L =
        (Module.finrank k B' * Module.finrank k E) * Module.finrank k L := by
      calc
        Module.finrank k A * Module.finrank k L = Module.finrank k M ^ 2 := hAdim
        _ = (nM * Module.finrank k S) ^ 2 := by rw [hMdim]
        _ = nM ^ 2 * (Module.finrank k S ^ 2) := by ring
        _ = nM ^ 2 * (Module.finrank k D *
            Module.finrank k (Module.End D S)) := by
          rw [hSdim]
        _ = (nM ^ 2 * Module.finrank k (Module.End D S)) *
            Module.finrank k D := by ring
        _ = Module.finrank k E * Module.finrank k D := by rw [hEdim]
        _ = Module.finrank k E *
            (Module.finrank k B' * Module.finrank k L) := by rw [hDdim]
        _ = (Module.finrank k B' * Module.finrank k E) *
            Module.finrank k L := by ring
    have hdim : Module.finrank k A = Module.finrank k B' *
        Module.finrank k E :=
      Nat.mul_right_cancel (Module.finrank_pos (R := k) (M := L)) hAL
    have hdimC : Module.finrank k A = Module.finrank k B' * Module.finrank k C' := by
      rw [← eEC.toLinearEquiv.finrank_eq]
      exact hdim
    have hCsimple : IsSimpleRing C' :=
      IsSimpleRing.of_ringEquiv eEC.symm.toRingEquiv hEsimple
    exact ⟨hCsimple, hdimC⟩
  sorry

theorem central_simple_tensor_decomposition (k A : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [IsSimpleRing A] (B : Subalgebra k A)
    [IsSimpleRing B] [Algebra.IsCentral k B] :
    let C := Subalgebra.centralizer k (B : Set A)
    IsSimpleRing C ∧ Algebra.IsCentral k C ∧
      Nonempty (B ⊗[k] C ≃ₐ[k] A) := by
  sorry

theorem self_centralizing_subfield_tfae (k A K : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Algebra.IsCentral k A]
    [IsSimpleRing A] [Field K] [Algebra k K] [FiniteDimensional k K]
    (f : K →ₐ[k] A) (hf : Function.Injective f) :
    List.TFAE
      [Module.finrank k A = Module.finrank k K ^ 2,
        Subalgebra.centralizer k (Set.range f) = AlgHom.range f,
        IsMaximalCommutativeSubalgebra k A (AlgHom.range f)] := by
  sorry

theorem maximal_subfield_dimension_square (k A K : Type*) [Field k]
    [DivisionRing A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [Field K] [Algebra k K]
    [FiniteDimensional k K] (f : K →ₐ[k] A) (hf : Function.Injective f)
    (hmax : IsMaximalCommutativeSubalgebra k A (AlgHom.range f)) :
    Module.finrank k A = Module.finrank k K ^ 2 := by
  exact ((self_centralizing_subfield_tfae k A K f hf).out 2 0).mp hmax

end Formalization.Books.Brauer
