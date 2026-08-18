import Formalization.Books.Brauer.Unit06.Foundation
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

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

private theorem finrank_end_finrank_of_linearEquiv (k D M N : Type*) (n : ℕ)
    [Field k] [Ring D] [Algebra k D] [AddCommGroup M] [Module D M] [Module k M]
    [SMulCommClass D k M] [IsScalarTower k D M] [AddCommGroup N]
    [Module D N] [Module k N] [SMulCommClass D k N] [IsScalarTower k D N]
    (e : M ≃ₗ[D] (Fin n → N)) :
    Module.finrank k (Module.End D M) = n ^ 2 * Module.finrank k (Module.End D N) := by
  calc
    Module.finrank k (Module.End D M) =
        Module.finrank k (Module.End D (Fin n → N)) := by
      exact (e.conjAlgEquiv k).toLinearEquiv.finrank_eq
    _ = n ^ 2 * Module.finrank k (Module.End D N) := finrank_end_fin k D N n

private theorem finrank_fin_pi (k M : Type*) (n : ℕ) [Field k]
    [AddCommGroup M] [Module k M] [Module.Free k M] [Module.Finite k M] :
    Module.finrank k (Fin n → M) = n * Module.finrank k M := by
  rw [Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

private theorem finrank_eq_mul_finrank_of_linearEquiv (k M N : Type*) (n : ℕ) [Field k]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [Module.Free k N] [Module.Finite k N] (e : M ≃ₗ[k] (Fin n → N)) :
    Module.finrank k M = n * Module.finrank k N := by
  calc
    Module.finrank k M = Module.finrank k (Fin n → N) := e.finrank_eq
    _ = n * Module.finrank k N := finrank_fin_pi k N n

private theorem simple_module_dimension_formula (k A M : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
    [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Module.finrank k A * Module.finrank k (Module.End A M) =
      Module.finrank k M ^ 2 := by
  exact (simple_module_center_and_dimension k A M).2.2

private theorem centralizer_core_dimension (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Algebra.IsCentral k A]
    [IsSimpleRing A] (B' : Subalgebra k A) [IsSimpleRing B']
    (C' D M : Type*) [Ring C'] [Algebra k C'] [Ring D] [Algebra k D]
    [IsSimpleRing D] [FiniteDimensional k D] [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] [Module k M]
    [IsScalarTower k A M] [Module D M] [IsScalarTower k D M]
    [Module.Finite k M] [Module.Finite D M] [Nontrivial M]
    (eEC : Module.End D M ≃ₐ[k] C')
    (hDdim : Module.finrank k D = Module.finrank k B' *
      Module.finrank k (Module.End A M)) :
    IsSimpleRing C' ∧ Module.finrank k A = Module.finrank k B' *
      Module.finrank k C' := by
  obtain ⟨n, hn, K, hK, hKalg, hKfinite, ⟨eMatrix⟩, _⟩ :=
    finite_module_end_is_matrix_and_double_commutant k D M
  let : NeZero n := hn
  let : DivisionRing K := hK
  let : Algebra k K := hKalg
  let : FiniteDimensional k K := hKfinite
  have hEsimple : IsSimpleRing (Module.End D M) := by
    exact IsSimpleRing.of_ringEquiv eMatrix.toRingEquiv.symm inferInstance
  obtain ⟨S, hS⟩ := finite_algebra_has_simple_submodule k D
  let : IsSimpleModule D S := hS
  let : Nontrivial S := IsSimpleModule.nontrivial D S
  let : Module.Finite k S :=
    simple_module_over_finite_algebra_is_finite_dimensional k D S
  obtain ⟨nM, ⟨eM⟩⟩ := finite_module_is_direct_sum_of_simple k D M S
  have hEdim : Module.finrank k (Module.End D M) = nM ^ 2 *
      Module.finrank k (Module.End D S) := by
    let comm_D_k_M' : SMulCommClass D k M :=
      smulCommClass_of_algebra k D M
    let : SMulCommClass D k M := comm_D_k_M'
    let comm_D_k_S' : SMulCommClass D k S :=
      smulCommClass_of_algebra k D S
    let : SMulCommClass D k S := comm_D_k_S'
    exact @finrank_end_finrank_of_linearEquiv k D M S nM
      _ _ _ _ inferInstance _ comm_D_k_M' inferInstance _ _ _ comm_D_k_S' _ eM
  have hnM : nM ≠ 0 := by
    intro hnM0
    subst nM
    have hnontriv : Nontrivial (Fin 0 → S) := eM.injective.nontrivial
    exact (not_nontrivial (Fin 0 → S)) hnontriv
  let : Module.Free k S := Module.Free.of_divisionRing k S
  let eMk := eM.restrictScalars k
  have hMdim : Module.finrank k M = nM * Module.finrank k S := by
    exact finrank_eq_mul_finrank_of_linearEquiv k M S nM eMk
  have hSdim : Module.finrank k D * Module.finrank k (Module.End D S) =
      Module.finrank k S ^ 2 := by
    exact simple_module_dimension_formula k D S
  have hAdim : Module.finrank k A * Module.finrank k (Module.End A M) =
      Module.finrank k M ^ 2 :=
    simple_module_dimension_formula k A M
  have hAL : Module.finrank k A * Module.finrank k (Module.End A M) =
      (Module.finrank k B' * Module.finrank k (Module.End D M)) *
        Module.finrank k (Module.End A M) := by
    calc
      Module.finrank k A * Module.finrank k (Module.End A M) =
          Module.finrank k M ^ 2 := hAdim
      _ = (nM * Module.finrank k S) ^ 2 := by rw [hMdim]
      _ = nM ^ 2 * (Module.finrank k S ^ 2) := by ring
      _ = nM ^ 2 * (Module.finrank k D *
          Module.finrank k (Module.End D S)) := by rw [hSdim]
      _ = (nM ^ 2 * Module.finrank k (Module.End D S)) *
          Module.finrank k D := by ring
      _ = Module.finrank k (Module.End D M) * Module.finrank k D := by
        rw [hEdim]
      _ = Module.finrank k (Module.End D M) *
          (Module.finrank k B' * Module.finrank k (Module.End A M)) := by
        rw [hDdim]
      _ = (Module.finrank k B' * Module.finrank k (Module.End D M)) *
          Module.finrank k (Module.End A M) := by ring
  have hdim : Module.finrank k A = Module.finrank k B' *
      Module.finrank k (Module.End D M) :=
    Nat.mul_right_cancel (Module.finrank_pos (R := k)
      (M := Module.End A M)) hAL
  have hdimC : Module.finrank k A = Module.finrank k B' * Module.finrank k C' := by
    rw [← eEC.toLinearEquiv.finrank_eq]
    exact hdim
  have hCsimple : IsSimpleRing C' :=
    IsSimpleRing.of_ringEquiv eEC.toRingEquiv hEsimple
  exact ⟨hCsimple, hdimC⟩

private theorem centralizer_core (k A : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A] :
    ∀ (B' : Subalgebra k A), IsSimpleRing B' →
      IsSimpleRing (Subalgebra.centralizer k (B' : Set A)) ∧
        Module.finrank k A = Module.finrank k B' *
          Module.finrank k (Subalgebra.centralizer k (B' : Set A)) := by
    classical
    intro B' hB'
    let : IsSimpleRing B' := hB'
    let C' : Subalgebra k A := Subalgebra.centralizer k (B' : Set A)
    change IsSimpleRing C' ∧
      Module.finrank k A = Module.finrank k B' * Module.finrank k C'
    obtain ⟨M, hM⟩ := finite_algebra_has_simple_submodule k A
    let : IsSimpleModule A M := hM
    let : Nontrivial M := IsSimpleModule.nontrivial A M
    let : Module.Finite k M :=
      simple_module_over_finite_algebra_is_finite_dimensional k A M
    let L := Module.End A M
    let : FiniteDimensional k L :=
      (simple_module_center_and_dimension k A M).2.1
    let eCenter : Subalgebra.center k A ≃ₐ[k] Subalgebra.center k L :=
      Classical.choice (simple_module_center_and_dimension k A M).1
    let : Algebra.IsCentral k L := by
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
        simp [za]
      calc
        algebraMap k L r = (eCenter za : L) := hza.symm
        _ = (eCenter z' : L) := hz''.symm
        _ = z := by simp [z']
    let module_B : Module B' M := Module.compHom M B'.val.toRingHom
    let tower_B : @IsScalarTower k B' M _
        module_B.toDistribMulAction.toSMul _ := by
      let : Module B' M := module_B
      exact IsScalarTower.of_algebraMap_smul (R := k) (A := B') (M := M)
        (fun r m => by
          change B'.val (algebraMap k B' r) • m = r • m
          rw [B'.val.commutes]
          exact IsScalarTower.algebraMap_smul A r m)
    let tower_L : IsScalarTower k L M := Module.End.apply_isScalarTower
    let comm_B_L : @SMulCommClass B' L M
        module_B.toDistribMulAction.toSMul _ := by
      let : Module B' M := module_B
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
      let : Module B' M := module_B
      let : IsScalarTower k B' M := tower_B
      let : IsScalarTower k L M := tower_L
      let : SMulCommClass B' L M := comm_B_L
      let : Module D M := module_D
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
      let : Module D M := module_D
      let : IsScalarTower k D M := tower_D
      exact Module.Finite.of_restrictScalars_finite k D M
    let : IsSimpleRing D := tensor_product_simple_of_simple_algebras k B' L
    let : FiniteDimensional k D := inferInstance
    let : Module D M := module_D
    let : IsScalarTower k D M := tower_D
    let : Module.Finite D M := finite_D
    let E := Module.End D M
    let comm_A_L : @SMulCommClass A L M _ _ :=
      ⟨fun a l m => (l.map_smul a m).symm⟩
    let : SMulCommClass A L M := comm_A_L
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
    let : FaithfulSMul A M := Module.annihilator_eq_bot.mp hAnn
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
                  let : Module B' M := module_B
                  let : IsScalarTower k B' M := tower_B
                  let : IsScalarTower k L M := tower_L
                  let : SMulCommClass B' L M := comm_B_L
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
      let : Module B' M := module_B
      let : IsScalarTower k B' M := tower_B
      let : IsScalarTower k L M := tower_L
      let : SMulCommClass B' L M := comm_B_L
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
            let : Module B' M := module_B
            let : IsScalarTower k B' M := tower_B
            let : IsScalarTower k L M := tower_L
            let : SMulCommClass B' L M := comm_B_L
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
    have hDdim : Module.finrank k D = Module.finrank k B' * Module.finrank k L := by
      change Module.finrank k (B' ⊗[k] L) =
        Module.finrank k B' * Module.finrank k L
      rw [Module.finrank_tensorProduct]
    exact centralizer_core_dimension k A B' C' D M eEC hDdim

theorem centralizer_theorem (k A : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]
    (B : Subalgebra k A) [IsSimpleRing B] :
    let C := Subalgebra.centralizer k (B : Set A)
    IsSimpleRing C ∧
        Module.finrank k A = Module.finrank k B * Module.finrank k C ∧
        Subalgebra.centralizer k (C : Set A) = B := by
  classical
  dsimp
  have hB := centralizer_core k A B (inferInstance : IsSimpleRing B)
  have hC := centralizer_core k A (Subalgebra.centralizer k (B : Set A)) hB.1
  refine ⟨hB.1, hB.2, ?_⟩
  have h_eq : B = Subalgebra.centralizer k
      (Subalgebra.centralizer k (B : Set A) : Set A) := by
    apply Subalgebra.eq_of_le_of_finrank_eq
    · rw [Subalgebra.le_centralizer_iff]
    · apply Nat.mul_right_cancel
        (Module.finrank_pos (R := k)
          (M := Subalgebra.centralizer k (B : Set A)))
      calc
        Module.finrank k B * Module.finrank k (Subalgebra.centralizer k (B : Set A)) =
            Module.finrank k A := hB.2.symm
        _ = Module.finrank k (Subalgebra.centralizer k (B : Set A)) *
            Module.finrank k (Subalgebra.centralizer k
              (Subalgebra.centralizer k (B : Set A) : Set A)) := hC.2
        _ = Module.finrank k (Subalgebra.centralizer k
              (Subalgebra.centralizer k (B : Set A) : Set A)) *
            Module.finrank k (Subalgebra.centralizer k (B : Set A)) := Nat.mul_comm _ _
  exact h_eq.symm

theorem central_simple_tensor_decomposition (k A : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [IsSimpleRing A] (B : Subalgebra k A)
    [IsSimpleRing B] [Algebra.IsCentral k B] :
    let C := Subalgebra.centralizer k (B : Set A)
    IsSimpleRing C ∧ Algebra.IsCentral k C ∧
      Nonempty (B ⊗[k] C ≃ₐ[k] A) := by
  classical
  dsimp
  let C : Subalgebra k A := Subalgebra.centralizer k (B : Set A)
  have hct := centralizer_theorem k A B
  dsimp at hct
  have hCsimple : IsSimpleRing C := by
    simpa [C] using hct.1
  have hdim : Module.finrank k A = Module.finrank k B * Module.finrank k C := by
    simpa [C] using hct.2.1
  have hdouble : Subalgebra.centralizer k (C : Set A) = B := by
    simpa [C] using hct.2.2
  have hCcentral : Algebra.IsCentral k C := by
    constructor
    intro x hx
    have hxCcentral : (x : A) ∈ Subalgebra.centralizer k (C : Set A) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro y hy
      have hxy := Subalgebra.mem_center_iff.mp hx (⟨y, hy⟩ : C)
      exact congrArg Subtype.val hxy
    have hxB : (x : A) ∈ B := by
      rw [← hdouble]
      exact hxCcentral
    let xB : B := ⟨x, hxB⟩
    have hxBcenter : xB ∈ Subalgebra.center k B := by
      rw [Subalgebra.mem_center_iff]
      intro y
      apply Subtype.ext
      exact x.property y y.property
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hxBcenter)
    refine ⟨r, ?_⟩
    apply Subtype.ext
    have hr' := congrArg Subtype.val hr
    simpa [xB] using hr'
  let : IsSimpleRing C := hCsimple
  let : Algebra.IsCentral k C := hCcentral
  let : IsSimpleRing (B ⊗[k] C) :=
    tensor_product_simple_of_simple_algebras k B C
  let f : B ⊗[k] C →ₐ[k] A :=
    Algebra.TensorProduct.lift B.val C.val (by
      intro b c
      exact c.property b b.property)
  have hfin : Module.finrank k (B ⊗[k] C) = Module.finrank k A := by
    rw [Module.finrank_tensorProduct]
    exact hdim.symm
  have hf : Function.Injective f := RingHom.injective f.toRingHom
  have hfs : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hf
  exact ⟨hCsimple, hCcentral, ⟨AlgEquiv.ofBijective f ⟨hf, hfs⟩⟩⟩

theorem self_centralizing_subfield_tfae (k A K : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Algebra.IsCentral k A]
    [IsSimpleRing A] [Field K] [Algebra k K] [FiniteDimensional k K]
    (f : K →ₐ[k] A) (hf : Function.Injective f) :
    List.TFAE
      [Module.finrank k A = Module.finrank k K ^ 2,
        Subalgebra.centralizer k (Set.range f) = AlgHom.range f,
        IsMaximalCommutativeSubalgebra k A (AlgHom.range f)] := by
  classical
  let S : Subalgebra k A := AlgHom.range f
  let C : Subalgebra k A := Subalgebra.centralizer k (S : Set A)
  change List.TFAE
    [Module.finrank k A = Module.finrank k K ^ 2,
      C = S, IsMaximalCommutativeSubalgebra k A S]
  let eK : K ≃ₐ[k] S := AlgEquiv.ofInjective f hf
  have hSdim : Module.finrank k S = Module.finrank k K :=
    eK.toLinearEquiv.finrank_eq.symm
  have : IsSimpleRing S :=
    IsSimpleRing.of_ringEquiv eK.toRingEquiv inferInstance
  have hScomm : ∀ x y : S, (x : A) * (y : A) = (y : A) * (x : A) := by
    intro x y
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    rw [← ha, ← hb]
    calc
      f a * f b = f (a * b) := (f.map_mul a b).symm
      _ = f (b * a) := congrArg f (mul_comm _ _)
      _ = f b * f a := f.map_mul b a
  have hSleC : S ≤ C := by
    intro x hx
    change x ∈ Subalgebra.centralizer k (S : Set A)
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    exact hScomm ⟨y, hy⟩ ⟨x, hx⟩
  have hct := centralizer_theorem k A S
  dsimp at hct
  have hCdim : Module.finrank k A = Module.finrank k S * Module.finrank k C := by
    simpa [C] using hct.2.1
  have hdouble : Subalgebra.centralizer k (C : Set A) = S := by
    simpa [C] using hct.2.2
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hdim
      have hdimC : Module.finrank k C = Module.finrank k S := by
        apply Nat.mul_right_cancel (Module.finrank_pos (R := k) (M := S))
        calc
          Module.finrank k C * Module.finrank k S =
              Module.finrank k S * Module.finrank k C := Nat.mul_comm _ _
          _ = Module.finrank k A := hCdim.symm
          _ = Module.finrank k K ^ 2 := hdim
          _ = Module.finrank k S ^ 2 := by rw [hSdim]
          _ = Module.finrank k S * Module.finrank k S := by simp [pow_two]
      have hSC : S = C :=
        Subalgebra.eq_of_le_of_finrank_eq hSleC hdimC.symm
      exact hSC.symm
    · intro hCS
      calc
        Module.finrank k A = Module.finrank k S * Module.finrank k C := hCdim
        _ = Module.finrank k S ^ 2 := by rw [hCS]; simp [pow_two]
        _ = Module.finrank k K ^ 2 := by rw [hSdim]
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hCS
      constructor
      · intro x y
        exact hScomm x y
      · intro T hTcomm hST
        have hTC : T ≤ C := by
          intro x hx
          change x ∈ Subalgebra.centralizer k (S : Set A)
          rw [Subalgebra.mem_centralizer_iff]
          intro s hs
          exact (hTcomm ⟨x, hx⟩ ⟨s, hST hs⟩).symm
        have hTS : T ≤ S := by
          intro x hx
          have hxC : x ∈ C := hTC hx
          rw [hCS] at hxC
          exact hxC
        exact le_antisymm hTS hST
    · intro hmax
      have hC_le_S : C ≤ S := by
        intro x hx
        have hxC : ∀ a ∈ (S : Set A), a * x = x * a := by
          exact (Subalgebra.mem_centralizer_iff k).mp hx
        let T : Subalgebra k A := Algebra.adjoin k ((S : Set A) ∪ {x})
        have hgens : ∀ a ∈ ((S : Set A) ∪ {x}),
            ∀ b ∈ ((S : Set A) ∪ {x}), a * b = b * a := by
          intro a ha b hb
          rcases ha with haS | haX
          · rcases hb with hbS | hbX
            · exact hScomm ⟨a, haS⟩ ⟨b, hbS⟩
            · have hb' : b = x := by
                simpa only [Set.mem_singleton_iff] using hbX
              subst b
              exact hxC a haS
          · have ha' : a = x := by
              simpa only [Set.mem_singleton_iff] using haX
            subst a
            rcases hb with hbS | hbX
            · exact (hxC b hbS).symm
            · have hb' : b = x := by
                simpa only [Set.mem_singleton_iff] using hbX
              subst b
              rfl
        have : IsMulCommutative T :=
          Algebra.isMulCommutative_adjoin k hgens
        have hTcomm : ∀ u v : T, Commute (u : A) (v : A) := by
          intro u v
          change (u : A) * (v : A) = (v : A) * (u : A)
          exact congrArg Subtype.val (mul_comm' u v)
        have hST : S ≤ T := by
          intro s hs
          exact Algebra.subset_adjoin (Set.mem_union_left _ hs)
        have hTS : T = S := hmax.2 T hTcomm hST
        have hxT : x ∈ T :=
          Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton x))
        rw [hTS] at hxT
        exact hxT
      exact le_antisymm hC_le_S hSleC
  tfae_finish

theorem maximal_subfield_dimension_square (k A K : Type*) [Field k]
    [DivisionRing A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [Field K] [Algebra k K]
    [FiniteDimensional k K] (f : K →ₐ[k] A) (hf : Function.Injective f)
    (hmax : IsMaximalCommutativeSubalgebra k A (AlgHom.range f)) :
    Module.finrank k A = Module.finrank k K ^ 2 := by
  exact ((self_centralizing_subfield_tfae k A K f hf).out 2 0).mp hmax

end Formalization.Books.Brauer
