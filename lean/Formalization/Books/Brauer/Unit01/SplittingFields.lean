import Formalization.Books.Brauer.Unit01.Centralizer
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.JacobsonNoether
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Splitting fields

The right-hand tensor-product algebra is installed locally by the splitting
predicates, following Mathlib's convention that this structure is not a
global instance because the left and right actions can otherwise be
ambiguous.
-/

namespace Formalization.Books.Brauer

open scoped TensorProduct

universe u_k u_A u_K

/-- `k'` splits `A` in the specified matrix degree. -/
def SplitsInDegree (k A k' : Type*) [Field k] [Ring A] [Algebra k A]
    [Field k'] [Algebra k k'] (d : ℕ) : Prop :=
  letI : Algebra k' (A ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  Nonempty ((A ⊗[k] k') ≃ₐ[k'] Matrix (Fin d) (Fin d) k')

/-- A field extension splits an algebra when it splits it in some matrix degree. -/
def Splits (k A k' : Type*) [Field k] [Ring A] [Algebra k A]
    [Field k'] [Algebra k k'] : Prop :=
  ∃ d : ℕ, SplitsInDegree k A k' d

theorem splits_iff_exists_matrix_degree (k A k' : Type*) [Field k] [Ring A]
    [Algebra k A] [Field k'] [Algebra k k'] :
    Splits k A k' ↔ ∃ d : ℕ, SplitsInDegree k A k' d := by
  rfl

theorem splits_iff_base_change_class_eq_one (k k' : Type*) [Field k]
    [Field k'] [Algebra k k'] (A : CSA k) :
    Splits k A.carrier k' ↔
      ∃ B : CSA k',
        IsBaseChangeRepresentative k k' A B ∧ brauerClass k' B = 1 := by
  constructor
  · rintro ⟨d, hsplit⟩
    let _ : Algebra k' (A.carrier ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    dsimp [SplitsInDegree] at hsplit
    obtain ⟨e⟩ := hsplit
    have hd0 : d ≠ 0 := by
      intro hd
      subst d
      have hzero : (0 : A.carrier ⊗[k] k') = 1 := by
        exact e.injective (Subsingleton.elim _ _)
      exact zero_ne_one hzero
    let _ : NeZero d := ⟨hd0⟩
    let B : CSA k' := { AlgCat.of k' (Matrix (Fin d) (Fin d) k') with }
    have hbase : IsBaseChangeRepresentative k k' A B := by
      dsimp [IsBaseChangeRepresentative, B]
      exact ⟨e⟩
    have hB : IsBrauerEquivalent B (scalarCSA k') := by
      refine ⟨1, d, one_ne_zero, hd0, ?_⟩
      change Nonempty
        (Matrix (Fin 1) (Fin 1) (Matrix (Fin d) (Fin d) k') ≃ₐ[k']
          Matrix (Fin d) (Fin d) k')
      let f : Matrix (Fin 1) (Fin 1) (Matrix (Fin d) (Fin d) k') →ₐ[k']
          Matrix (Fin d) (Fin d) k' :=
        { toFun := fun M => M 0 0
          map_one' := by simp
          map_mul' := by
            intro M N
            simp [Matrix.mul_apply]
          map_zero' := by simp
          map_add' := by
            intro M N
            rfl
          commutes' := by
            intro r
            apply Matrix.ext
            intro i j
            rw [Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
            simp only [if_true]
            rw [Matrix.algebraMap_matrix_apply] }
      have hf : Function.Bijective f := by
        constructor
        · intro M N h
          change M 0 0 = N 0 0 at h
          apply Matrix.ext
          intro i j
          simpa [Subsingleton.elim i (0 : Fin 1),
            Subsingleton.elim j (0 : Fin 1)] using h
        · intro M
          refine ⟨fun _ _ => M, ?_⟩
          rfl
      exact ⟨AlgEquiv.ofBijective f hf⟩
    refine ⟨B, hbase, ?_⟩
    calc
      brauerClass k' B = brauerClass k' (scalarCSA k') := Quotient.sound hB
      _ = 1 := by
        simpa only [brauerGroupCommGroup] using
          (Classical.choose_spec (brauer_group_is_abelian k')).1
  · rintro ⟨B, hbase, hclass⟩
    let _ : Algebra k' (A.carrier ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    have hscalar : brauerClass k' (scalarCSA k') = 1 := by
      simpa only [brauerGroupCommGroup] using
        (Classical.choose_spec (brauer_group_is_abelian k')).1
    have hBE : IsBrauerEquivalent B (scalarCSA k') :=
      Quotient.exact (hclass.trans hscalar.symm)
    obtain ⟨p, q, hp, hq, ⟨hE⟩⟩ := hBE
    dsimp [IsBaseChangeRepresentative] at hbase
    obtain ⟨eBase⟩ := hbase
    obtain ⟨n, hn, D, hD, hDalg, hDfinite, ⟨eB⟩⟩ :=
      wedderburn_artin_finite k' B.carrier
    let _ : NeZero n := hn
    let _ : Algebra.IsCentral k' B.carrier := B.isCentral
    let _ : Algebra.IsCentral k' D :=
      { out := by
          intro x hx
          have hxcomm : ∀ y : D, Commute x y := by
            intro y
            exact (Subalgebra.mem_center_iff.mp hx y).symm
          have hxmat : Matrix.scalar (Fin n) x ∈ Set.center
              (Matrix (Fin n) (Fin n) D) := by
            rw [Semigroup.mem_center_iff]
            intro M
            exact (Matrix.scalar_commute x hxcomm M).eq.symm
          obtain ⟨a, ha⟩ := eB.surjective (Matrix.scalar (Fin n) x)
          have hacenter : a ∈ Subalgebra.center k' B.carrier := by
            rw [Subalgebra.mem_center_iff]
            intro b
            have h := (Semigroup.mem_center_iff.mp hxmat) (eB b)
            have h' := congrArg eB.symm h
            rw [← ha] at h'
            simpa using h'
          obtain ⟨r, hr⟩ :=
            Algebra.mem_bot.mp (‹Algebra.IsCentral k' B.carrier›.out hacenter)
          apply Algebra.mem_bot.mpr
          refine ⟨r, ?_⟩
          apply (Matrix.scalar_inj (n := Fin n)).mp
          calc
            Matrix.scalar (Fin n) (algebraMap k' D r) =
                algebraMap k' (Matrix (Fin n) (Fin n) D) r := by rfl
            _ = eB (algebraMap k' B.carrier r) := by simp
            _ = eB a := by rw [hr]
            _ = Matrix.scalar (Fin n) x := ha }
    let eleft : Matrix (Fin p) (Fin p) B.carrier ≃ₐ[k']
        Matrix (Fin (n * p)) (Fin (n * p)) D :=
      ((eB.mapMatrix).trans (matrixEquivTensor (Fin p) k'
        (Matrix (Fin n) (Fin n) D))).trans
        (((Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin p) k' k' D k').trans
          (Algebra.TensorProduct.rid k' k' D).mapMatrix).trans
          (Matrix.reindexAlgEquiv k' D finProdFinEquiv))
    have hmatrix : Nonempty
        (Matrix (Fin (n * p)) (Fin (n * p)) D ≃ₐ[k']
          Matrix (Fin q) (Fin q) k') :=
      ⟨eleft.symm.trans hE⟩
    obtain ⟨eD⟩ := (matrix_division_similarity_iff k' D k').mp
      ⟨n * p, q, Nat.mul_ne_zero hn.out hp, hq, hmatrix⟩
    refine ⟨n, ?_⟩
    dsimp [SplitsInDegree]
    exact ⟨eBase.trans (eB.trans eD.mapMatrix)⟩

private def splittingTensorCSA (k : Type*) [Field k] (A B : CSA k) : CSA k :=
  let h := tensor_product_finite_central_simple k A.carrier B.carrier
  { AlgCat.of k (A.carrier ⊗[k] B.carrier) with
    isCentral := h.2.1
    isSimple := h.2.2
    fin_dim := h.1 }

private noncomputable def splittingMatrixOneAlgEquiv (k R : Type*) [Field k]
    [Ring R] [Algebra k R] :
    Matrix (Fin 1) (Fin 1) R ≃ₐ[k] R := by
  let f : Matrix (Fin 1) (Fin 1) R →ₐ[k] R :=
    { toFun := fun M => M 0 0
      map_one' := by simp
      map_mul' := by
        intro M N
        simp [Matrix.mul_apply]
      map_zero' := by simp
      map_add' := by
        intro M N
        rfl
      commutes' := by
        intro r
        rw [Matrix.algebraMap_matrix_apply]
        simp }
  apply AlgEquiv.ofBijective f
  constructor
  · intro M N h
    change M 0 0 = N 0 0 at h
    apply Matrix.ext
    intro i j
    simpa [Subsingleton.elim i (0 : Fin 1),
      Subsingleton.elim j (0 : Fin 1)] using h
  · intro M
    refine ⟨fun _ _ => M, ?_⟩
    rfl

private def splittingMatrixTensorEquiv (k X Y : Type*) [CommSemiring k]
    [Semiring X] [Algebra k X] [Semiring Y] [Algebra k Y] (n : ℕ) :
    Matrix (Fin n) (Fin n) (X ⊗[k] Y) ≃ₐ[k]
      Matrix (Fin n) (Fin n) X ⊗[k] Y :=
  ((Algebra.TensorProduct.comm k X Y).mapMatrix).trans
    (((Algebra.TensorProduct.congr (AlgEquiv.refl : Y ≃ₐ[k] Y)
        (matrixEquivTensor (Fin n) k X)).trans
      ((Algebra.TensorProduct.assoc k k k Y X
          (Matrix (Fin n) (Fin n) k)).symm.trans
        (matrixEquivTensor (Fin n) k (Y ⊗[k] X)).symm)).symm.trans
      (Algebra.TensorProduct.comm k Y (Matrix (Fin n) (Fin n) X)))

private theorem splittingTensorSimilarityLeft (k : Type*) [Field k]
    (A A' B : CSA k) (h : IsBrauerEquivalent A A') :
    IsBrauerEquivalent (splittingTensorCSA k A B)
      (splittingTensorCSA k A' B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ?_⟩
  let e' := Algebra.TensorProduct.congr e
    (AlgEquiv.refl : B.carrier ≃ₐ[k] B.carrier)
  change Nonempty
    (Matrix (Fin n) (Fin n) (A.carrier ⊗[k] B.carrier) ≃ₐ[k]
      Matrix (Fin m) (Fin m) (A'.carrier ⊗[k] B.carrier))
  exact ⟨(splittingMatrixTensorEquiv k A.carrier B.carrier n).trans
    (e'.trans (splittingMatrixTensorEquiv k A'.carrier B.carrier m).symm)⟩

private theorem splittingTensorSimilarityRight (k : Type*) [Field k]
    (A B B' : CSA k) (h : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (splittingTensorCSA k A B)
      (splittingTensorCSA k A B') := by
  have hleft : IsBrauerEquivalent (splittingTensorCSA k B A)
      (splittingTensorCSA k B' A) :=
    splittingTensorSimilarityLeft k B B' A h
  obtain ⟨n, m, hn, hm, ⟨eleft⟩⟩ := hleft
  refine ⟨n, m, hn, hm, ?_⟩
  let commAB : A.carrier ⊗[k] B.carrier ≃ₐ[k]
      B.carrier ⊗[k] A.carrier :=
    Algebra.TensorProduct.comm k A.carrier B.carrier
  let commAB' : A.carrier ⊗[k] B'.carrier ≃ₐ[k]
      B'.carrier ⊗[k] A.carrier :=
    Algebra.TensorProduct.comm k A.carrier B'.carrier
  exact ⟨(commAB.mapMatrix).trans
    (eleft.trans (commAB'.mapMatrix).symm)⟩

private theorem splittingTensorSimilarityComm (k : Type*) [Field k]
    (A B : CSA k) :
    IsBrauerEquivalent (splittingTensorCSA k A B)
      (splittingTensorCSA k B A) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] B.carrier) ≃ₐ[k]
      Matrix (Fin 1) (Fin 1) (B.carrier ⊗[k] A.carrier))
  let uA : Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] B.carrier) ≃ₐ[k]
      A.carrier ⊗[k] B.carrier := splittingMatrixOneAlgEquiv k _
  let uB : Matrix (Fin 1) (Fin 1) (B.carrier ⊗[k] A.carrier) ≃ₐ[k]
      B.carrier ⊗[k] A.carrier := splittingMatrixOneAlgEquiv k _
  exact ⟨uA.trans
    ((Algebra.TensorProduct.comm k A.carrier B.carrier).trans uB.symm)⟩

private theorem splittingOppositeSimilarity (k : Type*) [Field k]
    (A B : CSA k) (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (oppositeCSA k A) (oppositeCSA k B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ?_⟩
  change Nonempty
    (Matrix (Fin n) (Fin n) A.carrierᵐᵒᵖ ≃ₐ[k]
      Matrix (Fin m) (Fin m) B.carrierᵐᵒᵖ)
  let mopA : Matrix (Fin n) (Fin n) A.carrierᵐᵒᵖ ≃ₐ[k]
      (Matrix (Fin n) (Fin n) A.carrier)ᵐᵒᵖ := AlgEquiv.mopMatrix
  let mopB : Matrix (Fin m) (Fin m) B.carrierᵐᵒᵖ ≃ₐ[k]
      (Matrix (Fin m) (Fin m) B.carrier)ᵐᵒᵖ := AlgEquiv.mopMatrix
  exact ⟨mopA.trans ((AlgEquiv.op e).trans mopB.symm)⟩

private theorem splittingTensorSimilarityScalarLeft (k : Type*) [Field k]
    (A : CSA k) :
    IsBrauerEquivalent (splittingTensorCSA k (scalarCSA k) A) A := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (k ⊗[k] A.carrier) ≃ₐ[k]
      Matrix (Fin 1) (Fin 1) A.carrier)
  exact ⟨(Algebra.TensorProduct.lid k A.carrier).mapMatrix⟩

private theorem splittingTensorSimilarityScalarRight (k : Type*) [Field k]
    (A : CSA k) :
    IsBrauerEquivalent (splittingTensorCSA k A (scalarCSA k)) A := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] k) ≃ₐ[k]
      Matrix (Fin 1) (Fin 1) A.carrier)
  exact ⟨(Algebra.TensorProduct.rid k k A.carrier).mapMatrix⟩

private theorem splittingTensorSimilarityAssoc (k : Type*) [Field k]
    (A B C : CSA k) :
    IsBrauerEquivalent (splittingTensorCSA k (splittingTensorCSA k A B) C)
      (splittingTensorCSA k A (splittingTensorCSA k B C)) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) ((A.carrier ⊗[k] B.carrier) ⊗[k] C.carrier) ≃ₐ[k]
      Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] (B.carrier ⊗[k] C.carrier)))
  exact ⟨(Algebra.TensorProduct.assoc k k k A.carrier B.carrier C.carrier).mapMatrix⟩

private theorem splittingTensorSimilarityInverseLeft (k : Type*) [Field k]
    (A : CSA k) :
    IsBrauerEquivalent (splittingTensorCSA k A (oppositeCSA k A))
      (scalarCSA k) := by
  have hd : Module.finrank k A.carrier ≠ 0 :=
    Nat.ne_of_gt (Module.finrank_pos (R := k) (M := A.carrier))
  obtain ⟨e⟩ := inverse_of_finite_central_simple k A.carrier
  refine ⟨1, Module.finrank k A.carrier, one_ne_zero, hd, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] A.carrierᵐᵒᵖ) ≃ₐ[k]
      Matrix (Fin (Module.finrank k A.carrier))
        (Fin (Module.finrank k A.carrier)) k)
  exact ⟨(splittingMatrixOneAlgEquiv k _).trans e⟩

private theorem splittingTensorSimilarityInverseRight (k : Type*) [Field k]
    (A : CSA k) :
    IsBrauerEquivalent (splittingTensorCSA k (oppositeCSA k A) A)
      (scalarCSA k) :=
  IsBrauerEquivalent.trans (splittingTensorSimilarityComm k (oppositeCSA k A) A)
    (splittingTensorSimilarityInverseLeft k A)

private theorem splittingTensorSplitOppositeSimilarity (k : Type*) [Field k]
    [Field k'] [Algebra k k'] (A B : CSA k) (d : ℕ) (hd : d ≠ 0)
    (e : Nonempty ((A.carrier ⊗[k] B.carrier) ≃ₐ[k]
      Matrix (Fin d) (Fin d) k)) :
    IsBrauerEquivalent A (oppositeCSA k B) := by
  have hsplit : IsBrauerEquivalent (splittingTensorCSA k A B)
      (scalarCSA k) := by
    obtain ⟨e⟩ := e
    refine ⟨1, d, one_ne_zero, hd, ?_⟩
    change Nonempty
      (Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] B.carrier) ≃ₐ[k]
        Matrix (Fin d) (Fin d) k)
    exact ⟨(splittingMatrixOneAlgEquiv k _).trans e⟩
  have hleft : IsBrauerEquivalent
      (splittingTensorCSA k (oppositeCSA k A)
        (splittingTensorCSA k A B)) (oppositeCSA k A) :=
    (splittingTensorSimilarityRight k (oppositeCSA k A)
      (splittingTensorCSA k A B) (scalarCSA k) hsplit).trans
      (splittingTensorSimilarityScalarRight k (oppositeCSA k A))
  have hright : IsBrauerEquivalent
      (splittingTensorCSA k (oppositeCSA k A)
        (splittingTensorCSA k A B)) B := by
    exact (splittingTensorSimilarityAssoc k (oppositeCSA k A) A B).symm.trans
      ((splittingTensorSimilarityLeft k
        (splittingTensorCSA k (oppositeCSA k A) A)
        (splittingTensorCSA k A (oppositeCSA k A)) B
        (splittingTensorSimilarityComm k (oppositeCSA k A) A)).trans
        ((splittingTensorSimilarityLeft k
          (splittingTensorCSA k A (oppositeCSA k A)) (scalarCSA k) B
          (splittingTensorSimilarityInverseLeft k A)).trans
          (splittingTensorSimilarityScalarLeft k B)))
  have hOpp : IsBrauerEquivalent
      (oppositeCSA k (oppositeCSA k A)) (oppositeCSA k B) :=
    splittingOppositeSimilarity k (oppositeCSA k A) B (hleft.symm.trans hright)
  have hOpOp : IsBrauerEquivalent A (oppositeCSA k (oppositeCSA k A)) := by
    refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
    change Nonempty
      (Matrix (Fin 1) (Fin 1) A.carrier ≃ₐ[k]
        Matrix (Fin 1) (Fin 1) (A.carrierᵐᵒᵖ)ᵐᵒᵖ)
    let eop : Matrix (Fin 1) (Fin 1) A.carrier ≃ₐ[k]
        Matrix (Fin 1) (Fin 1) (A.carrierᵐᵒᵖ)ᵐᵒᵖ :=
      (AlgEquiv.opOp k A.carrier).mapMatrix
    exact ⟨eop⟩
  exact hOpOp.trans hOpp

theorem splitting_iff_similar_embedded_subfield (k k' : Type*) [Field k]
    [Field k'] [Algebra k k'] [FiniteDimensional k k'] (A : CSA k) :
    Splits k A.carrier k' ↔
    ∃ B : CSA k, IsBrauerEquivalent A B ∧
        ∃ f : k' →ₐ[k] B.carrier,
          Function.Injective f ∧
            Module.finrank k B.carrier = Module.finrank k k' ^ 2 := by
  constructor
  · rintro ⟨d, hsplit⟩
    letI : Algebra k' (A.carrier ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    dsimp [SplitsInDegree] at hsplit
    obtain ⟨e⟩ := hsplit
    have hd0 : d ≠ 0 := by
      intro hd
      subst d
      have hzero : (0 : A.carrier ⊗[k] k') = 1 := by
        exact e.injective (Subsingleton.elim _ _)
      exact zero_ne_one hzero
    let V := Fin d → k'
    let moduleE : Module (A.carrier ⊗[k] k') V :=
      Module.compHom V e.toRingHom
    letI : IsScalarTower k k' k' := by
      exact IsScalarTower.of_algebraMap_smul (by
        intro r c
        simp [Algebra.smul_def])
    letI : IsScalarTower k k' V := by
      infer_instance
    let towerE : @IsScalarTower k (A.carrier ⊗[k] k') V _
        moduleE.toDistribMulAction.toSMul _ := by
      letI : Module (A.carrier ⊗[k] k') V := moduleE
      exact IsScalarTower.of_algebraMap_smul (by
        intro r v
        change e (algebraMap k (A.carrier ⊗[k] k') r) • v = r • v
        rw [Algebra.TensorProduct.algebraMap_apply']
        change e (algebraMap k' (A.carrier ⊗[k] k')
          (algebraMap k k' r)) • v = r • v
        rw [e.commutes]
        simpa [Algebra.smul_def] using
          (IsScalarTower.algebraMap_smul k' r v))
    let iA : A.carrier →ₐ[k] A.carrier ⊗[k] k' :=
      Algebra.TensorProduct.includeLeft
    let moduleA : Module A.carrier V :=
      Module.compHom V iA.toRingHom
    let towerA : @IsScalarTower k A.carrier V _
        moduleA.toDistribMulAction.toSMul _ := by
      letI : Module (A.carrier ⊗[k] k') V := moduleE
      letI : Module A.carrier V := moduleA
      letI : IsScalarTower k (A.carrier ⊗[k] k') V := towerE
      exact IsScalarTower.of_algebraMap_smul (by
        intro r v
        change (algebraMap k A.carrier r) • v = r • v
        exact IsScalarTower.algebraMap_smul (A.carrier ⊗[k] k') r v)
    let commA : @SMulCommClass A.carrier k V
        moduleA.toDistribMulAction.toSMul _ := by
      letI : Module A.carrier V := moduleA
      letI : IsScalarTower k A.carrier V := towerA
      exact ⟨by
        intro a r v
        change a • (r • v) = r • (a • v)
        rw [← IsScalarTower.algebraMap_smul A.carrier r v,
          ← IsScalarTower.algebraMap_smul A.carrier r (a • v)]
        rw [← mul_smul, ← mul_smul, Algebra.commutes]⟩
    letI : IsScalarTower k k V := by
      exact IsScalarTower.of_algebraMap_smul (by
        intro r v
        simp [Algebra.smul_def])
    let rho : A.carrier →ₐ[k] Module.End k V :=
      { toRingHom := @Module.toModuleEnd k A.carrier V _ _ _ _ _ commA
        commutes' := by
          intro r
          apply LinearMap.ext
          intro v
          change (algebraMap k A.carrier r) • v = r • v
          exact IsScalarTower.algebraMap_smul A.carrier r v }
    letI : NeZero d := ⟨hd0⟩
    letI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd0⟩⟩
    letI : Nontrivial V := inferInstance
    letI : Module.Finite k V := Module.Finite.trans k' V
    letI : Module.Free k V := Module.Free.of_divisionRing k V
    let b := Module.Free.chooseBasis k V
    let R := Module.End k V
    letI : IsSimpleRing R :=
      IsSimpleRing.of_ringEquiv (algEquivMatrix b).toRingEquiv.symm inferInstance
    letI : Algebra.IsCentral k R := inferInstance
    have hrho : Function.Injective rho := by
      intro x y hxy
      have hxy' : ∀ v : V, x • v = y • v := by
        intro v
        exact congrArg (fun f : Module.End k V => f v) hxy
      have hxy'' : ∀ v : V, e (iA x) • v = e (iA y) • v := by
        intro v
        exact hxy' v
      have heq : e (iA x) = e (iA y) := by
        apply Matrix.ext_of_mulVec_single
        intro j
        exact hxy'' (Pi.single j 1)
      apply iA.injective
      apply e.injective
      exact heq
    let S : Subalgebra k R := AlgHom.range rho
    let eS : A.carrier ≃ₐ[k] S := AlgEquiv.ofInjective rho hrho
    letI : IsSimpleRing S :=
      IsSimpleRing.of_ringEquiv eS.toRingEquiv inferInstance
    letI : Algebra.IsCentral k S := by
      refine { out := ?_ }
      intro z hz
      obtain ⟨a, rfl⟩ := eS.surjective z
      have ha : a ∈ Subalgebra.center k A.carrier := by
        rw [Subalgebra.mem_center_iff]
        intro b
        have hcomm := (Subalgebra.mem_center_iff.mp hz) (eS b)
        apply eS.injective
        simpa only [map_mul] using hcomm
      obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (A.isCentral.out ha)
      apply Algebra.mem_bot.mpr
      refine ⟨r, ?_⟩
      calc
        algebraMap k S r = eS (algebraMap k A.carrier r) := by simp
        _ = eS a := by rw [hr]
    let C : Subalgebra k R := Subalgebra.centralizer k (S : Set R)
    have hdec := central_simple_tensor_decomposition k R S
    let commK : @SMulCommClass k' k V _ _ := by
      exact ⟨by
        intro c r v
        change c • (r • v) = r • (c • v)
        rw [← IsScalarTower.algebraMap_smul k' r v,
          ← IsScalarTower.algebraMap_smul k' r (c • v)]
        rw [← mul_smul, ← mul_smul, Algebra.commutes]⟩
    let scalar : k' →ₐ[k] R :=
      { toRingHom := @Module.toModuleEnd k k' V _ _ _ _ _ commK
        commutes' := by
          intro r
          apply LinearMap.ext
          intro v
          change (algebraMap k k' r) • v = r • v
          exact IsScalarTower.algebraMap_smul k' r v }
    have hscalar_mem : ∀ c : k', scalar c ∈ C := by
      intro c
      rw [Subalgebra.mem_centralizer_iff]
      intro z hz
      obtain ⟨a, rfl⟩ := hz
      apply LinearMap.ext
      intro v
      change (iA a) • (c • v) = c • ((iA a) • v)
      have hc : ∀ w : V,
          (algebraMap k' (A.carrier ⊗[k] k') c) • w = c • w := by
        intro w
        change e (algebraMap k' (A.carrier ⊗[k] k') c) • w = c • w
        rw [e.commutes]
        simp
      rw [← hc v, ← hc (iA a • v)]
      change iA a • ((algebraMap k' (A.carrier ⊗[k] k') c) • v) =
        (algebraMap k' (A.carrier ⊗[k] k') c) • (iA a • v)
      rw [← mul_smul, ← mul_smul]
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      change ((a ⊗ₜ[k] (1 : k')) * (1 ⊗ₜ[k] c)) • v =
        ((1 ⊗ₜ[k] c) * (a ⊗ₜ[k] (1 : k'))) • v
      rw [Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp [mul_comm]
    sorry
  · sorry

theorem maximal_subfield_splits (k K k' : Type*) [Field k]
    [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (f : k' →ₐ[k] K) (hf : Function.Injective f)
    (hmax : IsMaximalCommutativeSubalgebra k K (AlgHom.range f)) :
    Splits k K k' := by
  let B : CSA k := { AlgCat.of k K with }
  have hdim : Module.finrank k K = Module.finrank k k' ^ 2 :=
    maximal_subfield_dimension_square k K k' f hf hmax
  have hsplit : Splits k B.carrier k' := by
    apply (splitting_iff_similar_embedded_subfield k k' B).2
    refine ⟨B, IsBrauerEquivalent.refl B, f, hf, ?_⟩
    simpa [B] using hdim
  simpa [B] using hsplit

private theorem splitting_iff_similar_embedded_subfield_same_universe
    (k : Type u_k) (k' : Type*) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (A : CSA.{u_k, u_K} k) :
    Splits k A.carrier k' →
      ∃ B : CSA.{u_k, u_K} k, IsBrauerEquivalent A B ∧
        ∃ f : k' →ₐ[k] B.carrier,
          Function.Injective f ∧
            Module.finrank k B.carrier = Module.finrank k k' ^ 2 := by
  intro h
  exact (splitting_iff_similar_embedded_subfield k k' A).mp h

theorem splitting_field_degree_dvd (k K k' : Type*) [Field k]
    [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (d : ℕ)
    (hd : Module.finrank k K = d ^ 2) (h : Splits k K k') :
    d ∣ Module.finrank k k' := by
  let A0 : CSA k := { AlgCat.of k K with }
  have hsplit : Splits k A0.carrier k' := by
    simpa [A0] using h
  obtain ⟨B, hAB, _f, _hf, hBdim⟩ :=
    splitting_iff_similar_embedded_subfield_same_universe k k' A0 hsplit
  obtain ⟨p, q, hp, hq, ⟨hE⟩⟩ := hAB
  obtain ⟨n, hn, D, hD, hDalg, hDfinite, ⟨eB⟩⟩ :=
    @wedderburn_artin_finite k B.carrier _ _ _ _ _
  let _ : NeZero n := hn
  let _ : Algebra.IsCentral k B.carrier := B.isCentral
  let _ : Algebra.IsCentral k D :=
    { out := by
        intro x hx
        have hxcomm : ∀ y : D, Commute x y := by
          intro y
          exact (Subalgebra.mem_center_iff.mp hx y).symm
        have hxmat : Matrix.scalar (Fin n) x ∈ Set.center
            (Matrix (Fin n) (Fin n) D) := by
          rw [Semigroup.mem_center_iff]
          intro M
          exact (Matrix.scalar_commute x hxcomm M).eq.symm
        obtain ⟨a, ha⟩ := eB.surjective (Matrix.scalar (Fin n) x)
        have hacenter : a ∈ Subalgebra.center k B.carrier := by
          rw [Subalgebra.mem_center_iff]
          intro b
          have h := (Semigroup.mem_center_iff.mp hxmat) (eB b)
          have h' := congrArg eB.symm h
          rw [← ha] at h'
          simpa using h'
        obtain ⟨r, hr⟩ :=
          Algebra.mem_bot.mp (‹Algebra.IsCentral k B.carrier›.out hacenter)
        apply Algebra.mem_bot.mpr
        refine ⟨r, ?_⟩
        apply (Matrix.scalar_inj (n := Fin n)).mp
        calc
          Matrix.scalar (Fin n) (algebraMap k D r) =
              algebraMap k (Matrix (Fin n) (Fin n) D) r := by rfl
          _ = eB (algebraMap k B.carrier r) := by simp
          _ = eB a := by rw [hr]
          _ = Matrix.scalar (Fin n) x := ha }
  let eleft : Matrix (Fin q) (Fin q) B.carrier ≃ₐ[k]
      Matrix (Fin (n * q)) (Fin (n * q)) D :=
    ((eB.mapMatrix).trans (matrixEquivTensor (Fin q) k
      (Matrix (Fin n) (Fin n) D))).trans
      (((Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin q) k k D k).trans
        (Algebra.TensorProduct.rid k k D).mapMatrix).trans
        (Matrix.reindexAlgEquiv k D finProdFinEquiv))
  have hmatrix : Nonempty
      (Matrix (Fin p) (Fin p) K ≃ₐ[k]
        Matrix (Fin (n * q)) (Fin (n * q)) D) :=
    ⟨hE.trans eleft⟩
  obtain ⟨eKD⟩ := (matrix_division_similarity_iff k K D).mp
    ⟨p, n * q, hp, Nat.mul_ne_zero hn.out hq, hmatrix⟩
  have hfinD : Module.finrank k D = Module.finrank k K :=
    eKD.toLinearEquiv.finrank_eq.symm
  have hdimB : Module.finrank k B.carrier =
      n ^ 2 * Module.finrank k K := by
    calc
      Module.finrank k B.carrier =
          Module.finrank k (Matrix (Fin n) (Fin n) D) :=
        eB.toLinearEquiv.finrank_eq
      _ = n ^ 2 * Module.finrank k D := by
        simp [Module.finrank_matrix, pow_two]
      _ = n ^ 2 * Module.finrank k K := by rw [hfinD]
  have hsq : Module.finrank k k' ^ 2 = (n * d) ^ 2 := by
    calc
      Module.finrank k k' ^ 2 = Module.finrank k B.carrier := hBdim.symm
      _ = n ^ 2 * Module.finrank k K := hdimB
      _ = n ^ 2 * d ^ 2 := by rw [hd]
      _ = (n * d) ^ 2 := by
        simp [pow_two, Nat.mul_left_comm, Nat.mul_comm]
  have hdegree : Module.finrank k k' = n * d :=
    Nat.pow_left_injective (n := 2) (by decide) hsq
  refine ⟨n, ?_⟩
  simpa [Nat.mul_comm] using hdegree

/-- A separable maximal subfield of a finite central division algebra. -/
structure SeparableMaximalSubfield (k : Type u_k) (K : Type u_K)
    [Field k] [DivisionRing K]
    [Algebra k K] where
  carrier : Type u_K
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [finite : FiniteDimensional k carrier]
  embedding : carrier →ₐ[k] K
  injective : Function.Injective embedding
  maximal : IsMaximalCommutativeSubalgebra k K (AlgHom.range embedding)
  [separable : Algebra.IsSeparable k carrier]

theorem exists_separable_maximal_subfield (k K : Type*) [Field k]
    [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] :
    Nonempty (SeparableMaximalSubfield k K) := by
  sorry

/-- A finite separable extension which splits a given algebra. -/
structure FiniteSeparableSplittingField (k : Type u_k) (A : Type u_A) [Field k] [Ring A]
    [Algebra k A] where
  carrier : Type u_k
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [finite : FiniteDimensional k carrier]
  [separable : Algebra.IsSeparable k carrier]
  degree : ℕ
  degree_pos : 0 < degree
  splitting : SplitsInDegree k A carrier degree

theorem brauer_class_has_finite_separable_splitting_field (k : Type*)
    [Field k] :
    ∀ A : CSA k, Nonempty (FiniteSeparableSplittingField k A.carrier) := by
  sorry

/-- A finite Galois splitting field, packaged with its typeclass data. -/
structure FiniteGaloisSplittingField (k : Type u_k) (A : Type u_A) [Field k] [Ring A]
    [Algebra k A] where
  carrier : Type u_k
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [finite : FiniteDimensional k carrier]
  [galois : IsGalois k carrier]
  degree : ℕ
  degree_pos : 0 < degree
  splitting : SplitsInDegree k A carrier degree

/-- A Wedderburn presentation by a matrix algebra over a finite central skew field. -/
structure MatrixDivisionPresentation (k : Type u_k) (A : Type u_A) [Field k] [Ring A]
    [Algebra k A] where
  degree : ℕ
  degree_pos : 0 < degree
  division : Type u_A
  [divisionRing : DivisionRing division]
  [algebra : Algebra k division]
  [finite : FiniteDimensional k division]
  [central : Algebra.IsCentral k division]
  equivalence : Nonempty
    (A ≃ₐ[k] Matrix (Fin degree) (Fin degree) division)

theorem finite_central_simple_tfae (k A : Type*) [Field k] [Ring A]
    [Algebra k A] :
    List.TFAE
      [FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A,
        FiniteDimensional k A ∧
          Subalgebra.center k A = ⊥ ∧ IsSimpleRing A,
        ∃ d : ℕ, 0 < d ∧ SplitsInDegree k A (AlgebraicClosure k) d,
        ∃ d : ℕ, 0 < d ∧ SplitsInDegree k A (SeparableClosure k) d,
        Nonempty (FiniteGaloisSplittingField k A),
        Nonempty (MatrixDivisionPresentation k A)] := by
  sorry

theorem finite_central_simple_degree_is_unique (k A : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [IsSimpleRing A] :
    ∃! d : ℕ, 0 < d ∧ SplitsInDegree k A (AlgebraicClosure k) d := by
  let K := AlgebraicClosure k
  let _ : Algebra K (A ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  have hbase := base_change_finite_central_simple k A K
  let _ : FiniteDimensional K (A ⊗[k] K) := hbase.1
  let _ : Algebra.IsCentral K (A ⊗[k] K) := hbase.2.1
  let _ : IsSimpleRing (A ⊗[k] K) := hbase.2.2
  obtain ⟨d, hd, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K (A ⊗[k] K)
  have hbase_finrank : Module.finrank K (A ⊗[k] K) = Module.finrank k A := by
    calc
      Module.finrank K (A ⊗[k] K) = Module.finrank K (K ⊗[k] A) :=
        (Algebra.TensorProduct.commRight k K A).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k A := by rw [Module.finrank_baseChange]
  have hdegree : 0 < d := Nat.pos_iff_ne_zero.mpr hd.out
  refine ⟨d, ⟨hdegree, ?_⟩, ?_⟩
  · exact ⟨e⟩
  · intro d' hd'
    rcases hd' with ⟨hdegree', hsplit⟩
    dsimp [SplitsInDegree] at hsplit
    obtain ⟨e'⟩ := hsplit
    have hdsq : d' ^ 2 = Module.finrank k A := by
      calc
        d' ^ 2 = Module.finrank K (Matrix (Fin d') (Fin d') K) := by
          simp [Module.finrank_matrix, pow_two]
        _ = Module.finrank K (A ⊗[k] K) := e'.toLinearEquiv.finrank_eq.symm
        _ = Module.finrank k A := hbase_finrank
    have hdsq0 : d ^ 2 = Module.finrank k A := by
      calc
        d ^ 2 = Module.finrank K (Matrix (Fin d) (Fin d) K) := by
          simp [Module.finrank_matrix, pow_two]
        _ = Module.finrank K (A ⊗[k] K) := e.toLinearEquiv.finrank_eq.symm
        _ = Module.finrank k A := hbase_finrank
    exact Nat.pow_left_injective (n := 2) (by decide) (hdsq.trans hdsq0.symm)

end Formalization.Books.Brauer
