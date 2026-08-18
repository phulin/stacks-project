import Formalization.Books.Brauer.Unit07.Foundation
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.JacobsonNoether
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
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
open scoped IsMulCommutative

#check IntermediateField.val
#check IntermediateField.adjoin

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
    (A B : CSA k) (d : ℕ) (hd : d ≠ 0)
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

private theorem splitting_of_embedded_subfield_of_finrank
    (k K k' : Type*) [Field k] [Ring K] [Algebra k K] [IsSimpleRing K]
    [FiniteDimensional k K] [Algebra.IsCentral k K]
    [Field k'] [Algebra k k'] [FiniteDimensional k k']
    (f : k' →ₐ[k] K) (hf : Function.Injective f)
    (hdim : Module.finrank k K = Module.finrank k k' ^ 2) :
    Splits k K k' := by
  letI moduleK : Module k' K :=
    { smul := fun c x => x * f c
      one_smul := by
        intro x
        change x * f 1 = x
        simp
      mul_smul := by
        intro c d x
        change x * f (c * d) = (x * f d) * f c
        calc
          x * f (c * d) = x * f (d * c) := by rw [mul_comm c d]
          _ = x * (f d * f c) := by rw [map_mul]
          _ = (x * f d) * f c := by
            rw [mul_assoc]
      smul_zero := by
        intro c
        exact zero_mul (f c)
      smul_add := by
        intro c x y
        change (x + y) * f c = x * f c + y * f c
        exact add_mul x y (f c)
      add_smul := by
        intro c d x
        change x * f (c + d) = x * f c + x * f d
        rw [map_add, mul_add]
      zero_smul := by
        intro x
        change x * f 0 = 0
        simp }
  let towerK : IsScalarTower k k' K := by
    refine ⟨?_⟩
    intro r c x
    change x * f (r • c) = r • (x * f c)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, f.commutes]
    calc
      x * ((algebraMap k K) r * f c) = (x * (algebraMap k K r)) * f c := by
        rw [← mul_assoc]
      _ = ((algebraMap k K) r * x) * f c := by
        rw [(Algebra.commutes r x).symm]
      _ = (algebraMap k K) r * (x * f c) := by
        rw [mul_assoc]
  let : IsScalarTower k k' K := towerK
  let : Module.Finite k' K :=
    Module.Finite.of_restrictScalars_finite k k' K
  let commKK : SMulCommClass k' k' K := by
    exact ⟨by
      intro c d x
      change (x * f d) * f c = (x * f c) * f d
      calc
        (x * f d) * f c = x * (f d * f c) := by rw [mul_assoc]
        _ = x * (f c * f d) := by
          rw [← map_mul, ← map_mul, mul_comm c d]
        _ = (x * f c) * f d := by rw [mul_assoc]⟩
  let commK : SMulCommClass K k' K := by
    exact ⟨by
      intro a c x
      change a * (x * f c) = (a * x) * f c
      simp [mul_assoc]⟩
  let left : K →ₐ[k] Module.End k' K :=
    { toRingHom := @Module.toModuleEnd k' K K _ _ _ _ _ commK
      commutes' := by
        intro r
        apply LinearMap.ext
        intro x
        dsimp only [Module.toModuleEnd, DistribSMul.toLinearMap]
        rw [Module.algebraMap_end_apply]
        change (algebraMap k K r) * x = r • x
        simp [Algebra.smul_def] }
  let scalar : k' →ₐ[k'] Module.End k' K :=
    { toRingHom := @Module.toModuleEnd k' k' K _ _ _ _ _ commKK
      commutes' := by
        intro c
        ext x
        change c • x = c • x
        rfl }
  let hcomm : ∀ c a, Commute (scalar c) (left a) := by
    intro c a
    apply LinearMap.ext
    intro x
    change c • (a • x) = a • (c • x)
    change (a * x) * f c = a * (x * f c)
    rw [mul_assoc]
  let eLift : (k' ⊗[k] K) →ₐ[k'] Module.End k' K :=
    Algebra.TensorProduct.lift scalar left hcomm
  let _ : Algebra k' (K ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  let e : (K ⊗[k] k') →ₐ[k'] Module.End k' K :=
    { toRingHom := eLift.toRingHom.comp
        (Algebra.TensorProduct.comm k K k').toRingHom
      commutes' := by
        intro c
        rw [Algebra.TensorProduct.right_algebraMap_apply]
        change eLift (Algebra.TensorProduct.comm k K k'
          (1 ⊗ₜ[k] c)) = algebraMap k' (Module.End k' K) c
        rw [Algebra.TensorProduct.comm_tmul]
        simpa [eLift] using scalar.commutes c }
  let : IsSimpleRing (K ⊗[k] k') :=
    tensor_product_simple_of_simple_algebras_left k K k'
  have heinj : Function.Injective e := RingHom.injective e.toRingHom
  have hfinK : Module.finrank k' K = Module.finrank k k' := by
    apply Nat.mul_left_cancel (Module.finrank_pos (R := k) (M := k'))
    calc
      Module.finrank k k' * Module.finrank k' K = Module.finrank k K :=
        Module.finrank_mul_finrank k k' K
      _ = Module.finrank k k' ^ 2 := hdim
      _ = Module.finrank k k' * Module.finrank k k' := by
        rw [pow_two]
  have hfin : Module.finrank k (K ⊗[k] k') =
      Module.finrank k (Module.End k' K) := by
    calc
      Module.finrank k (K ⊗[k] k') =
          Module.finrank k K * Module.finrank k k' := by
        rw [Module.finrank_tensorProduct]
      _ = Module.finrank k' K * Module.finrank k K := by
        rw [hfinK, Nat.mul_comm]
      _ = Module.finrank k (Module.End k' K) := by
        symm
        rw [Module.finrank_linearMap]
  let eK := (e.restrictScalars k).toLinearMap
  have hesurjK : Function.Surjective eK := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp
    intro x y hxy
    apply heinj
    simpa [eK] using hxy
  have hesurj : Function.Surjective e.toLinearMap := by
    intro y
    obtain ⟨x, hxy⟩ := hesurjK y
    exact ⟨x, by simpa [eK] using hxy⟩
  let ee : (K ⊗[k] k') ≃ₐ[k'] Module.End k' K :=
    AlgEquiv.ofBijective e ⟨heinj, hesurj⟩
  let b := Module.Free.chooseBasis k' K
  let m := Fintype.card (Module.Free.ChooseBasisIndex k' K)
  let emat : (K ⊗[k] k') ≃ₐ[k'] Matrix (Fin m) (Fin m) k' :=
    (ee.trans (algEquivMatrix b)).trans
      (Matrix.reindexAlgEquiv k' k'
        (Fintype.equivFin (Module.Free.ChooseBasisIndex k' K)))
  refine ⟨m, ?_⟩
  dsimp [SplitsInDegree]
  exact ⟨emat⟩

private def matrixTensorEquivForSplitting (k X Y : Type*) [CommSemiring k]
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

private theorem base_change_matrix_similarity_for_splitting (k k' : Type*) [Field k]
    [Field k'] [Algebra k k'] (A A' : CSA k) (h : IsBrauerEquivalent A A') :
    let _ : Algebra k' (A.carrier ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    let _ : Algebra k' (A'.carrier ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    ∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧
      Nonempty
        (Matrix (Fin n) (Fin n) (A.carrier ⊗[k] k') ≃ₐ[k']
          Matrix (Fin m) (Fin m) (A'.carrier ⊗[k] k')) := by
  dsimp
  let _ : Algebra k' (A.carrier ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  let _ : Algebra k' (A'.carrier ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ?_⟩
  let e' := Algebra.TensorProduct.congr e
    (AlgEquiv.refl : k' ≃ₐ[k] k')
  let gk : Matrix (Fin n) (Fin n) (A.carrier ⊗[k] k') ≃ₐ[k]
      Matrix (Fin m) (Fin m) (A'.carrier ⊗[k] k') :=
    (matrixTensorEquivForSplitting k A.carrier k' n).trans
      (e'.trans (matrixTensorEquivForSplitting k A'.carrier k' m).symm)
  let g : Matrix (Fin n) (Fin n) (A.carrier ⊗[k] k') ≃ₐ[k']
      Matrix (Fin m) (Fin m) (A'.carrier ⊗[k] k') :=
    AlgEquiv.ofBijective
      { toFun := gk
        map_one' := gk.map_one
        map_mul' := gk.map_mul
        map_zero' := gk.map_zero
        map_add' := gk.map_add
        commutes' := by
          intro r
          have hmtA :
              matrixTensorEquivForSplitting k A.carrier k' n
                  (Matrix.scalar (Fin n) ((1 : A.carrier) ⊗ₜ[k] r)) =
                (1 : Matrix (Fin n) (Fin n) A.carrier) ⊗ₜ[k] r := by
            let q : k' ⊗[k] Matrix (Fin n) (Fin n) A.carrier ≃ₐ[k]
                Matrix (Fin n) (Fin n) (k' ⊗[k] A.carrier) :=
              (Algebra.TensorProduct.congr (AlgEquiv.refl : k' ≃ₐ[k] k')
                (matrixEquivTensor (Fin n) k A.carrier)).trans
                ((Algebra.TensorProduct.assoc k k k k' A.carrier
                    (Matrix (Fin n) (Fin n) k)).symm.trans
                  (matrixEquivTensor (Fin n) k (k' ⊗[k] A.carrier)).symm)
            have hq :
                q ((r : k') ⊗ₜ[k]
                  (1 : Matrix (Fin n) (Fin n) A.carrier)) =
                  Matrix.scalar (Fin n) ((r : k') ⊗ₜ[k] (1 : A.carrier)) := by
              change (matrixEquivTensor (Fin n) k (k' ⊗[k] A.carrier)).symm
                  ((Algebra.TensorProduct.assoc k k k k' A.carrier
                      (Matrix (Fin n) (Fin n) k)).symm
                    (r ⊗ₜ[k]
                      matrixEquivTensor (Fin n) k A.carrier
                        (1 : Matrix (Fin n) (Fin n) A.carrier))) =
                Matrix.scalar (Fin n) ((r : k') ⊗ₜ[k] (1 : A.carrier))
              have hone :
                  matrixEquivTensor (Fin n) k A.carrier
                      (1 : Matrix (Fin n) (Fin n) A.carrier) =
                    (1 : A.carrier) ⊗ₜ[k]
                      (1 : Matrix (Fin n) (Fin n) k) := by
                simpa [Algebra.TensorProduct.one_def] using
                  (matrixEquivTensor (Fin n) k A.carrier).map_one
              rw [hone]
              simp only [Algebra.TensorProduct.assoc_symm_tmul,
                matrixEquivTensor_apply_symm]
              apply Matrix.ext
              intro i j
              by_cases hij : i = j <;>
                simp [Matrix.map, Matrix.diagonal, Matrix.one_apply, hij]
            have hscalar :
                Matrix.scalar (Fin n) ((1 : A.carrier) ⊗ₜ[k] r) =
                  (Algebra.TensorProduct.includeRight :
                    k' →ₐ[k] A.carrier ⊗[k] k').mapMatrix
                    (Matrix.scalar (Fin n) r) := by
              apply Matrix.ext
              intro i j
              by_cases hij : i = j <;> simp [hij]
            rw [hscalar]
            change (Algebra.TensorProduct.comm k k'
                (Matrix (Fin n) (Fin n) A.carrier))
              (q.symm
                ((Algebra.TensorProduct.comm k A.carrier k').mapMatrix
                  ((Algebra.TensorProduct.includeRight :
                    k' →ₐ[k] A.carrier ⊗[k] k').mapMatrix
                    (Matrix.scalar (Fin n) r)))) =
              (1 : Matrix (Fin n) (Fin n) A.carrier) ⊗ₜ[k] r
            have hfirst :
                (Algebra.TensorProduct.comm k A.carrier k').mapMatrix
                    ((Algebra.TensorProduct.includeRight :
                      k' →ₐ[k] A.carrier ⊗[k] k').mapMatrix
                      (Matrix.scalar (Fin n) r)) =
                  Matrix.scalar (Fin n) ((r : k') ⊗ₜ[k] (1 : A.carrier)) := by
              apply Matrix.ext
              intro i j
              by_cases hij : i = j <;> simp [hij]
            rw [hfirst]
            have hq' :
                q.symm (Matrix.scalar (Fin n)
                  ((r : k') ⊗ₜ[k] (1 : A.carrier))) =
                  (r : k') ⊗ₜ[k] (1 : Matrix (Fin n) (Fin n) A.carrier) := by
              apply q.injective
              simp [hq]
            rw [hq']
            simp [Algebra.TensorProduct.comm_tmul]
          have hmtA' :
              matrixTensorEquivForSplitting k A'.carrier k' m
                  (Matrix.scalar (Fin m) ((1 : A'.carrier) ⊗ₜ[k] r)) =
                (1 : Matrix (Fin m) (Fin m) A'.carrier) ⊗ₜ[k] r := by
            let q : k' ⊗[k] Matrix (Fin m) (Fin m) A'.carrier ≃ₐ[k]
                Matrix (Fin m) (Fin m) (k' ⊗[k] A'.carrier) :=
              (Algebra.TensorProduct.congr (AlgEquiv.refl : k' ≃ₐ[k] k')
                (matrixEquivTensor (Fin m) k A'.carrier)).trans
                ((Algebra.TensorProduct.assoc k k k k' A'.carrier
                    (Matrix (Fin m) (Fin m) k)).symm.trans
                  (matrixEquivTensor (Fin m) k (k' ⊗[k] A'.carrier)).symm)
            have hq :
                q ((r : k') ⊗ₜ[k]
                  (1 : Matrix (Fin m) (Fin m) A'.carrier)) =
                  Matrix.scalar (Fin m) ((r : k') ⊗ₜ[k] (1 : A'.carrier)) := by
              change (matrixEquivTensor (Fin m) k (k' ⊗[k] A'.carrier)).symm
                  ((Algebra.TensorProduct.assoc k k k k' A'.carrier
                      (Matrix (Fin m) (Fin m) k)).symm
                    (r ⊗ₜ[k]
                      matrixEquivTensor (Fin m) k A'.carrier
                        (1 : Matrix (Fin m) (Fin m) A'.carrier))) =
                Matrix.scalar (Fin m) ((r : k') ⊗ₜ[k] (1 : A'.carrier))
              have hone :
                  matrixEquivTensor (Fin m) k A'.carrier
                      (1 : Matrix (Fin m) (Fin m) A'.carrier) =
                    (1 : A'.carrier) ⊗ₜ[k]
                      (1 : Matrix (Fin m) (Fin m) k) := by
                simpa [Algebra.TensorProduct.one_def] using
                  (matrixEquivTensor (Fin m) k A'.carrier).map_one
              rw [hone]
              simp only [Algebra.TensorProduct.assoc_symm_tmul,
                matrixEquivTensor_apply_symm]
              apply Matrix.ext
              intro i j
              by_cases hij : i = j <;>
                simp [Matrix.map, Matrix.diagonal, Matrix.one_apply, hij]
            have hscalar :
                Matrix.scalar (Fin m) ((1 : A'.carrier) ⊗ₜ[k] r) =
                  (Algebra.TensorProduct.includeRight :
                    k' →ₐ[k] A'.carrier ⊗[k] k').mapMatrix
                    (Matrix.scalar (Fin m) r) := by
              apply Matrix.ext
              intro i j
              by_cases hij : i = j <;> simp [hij]
            rw [hscalar]
            change (Algebra.TensorProduct.comm k k'
                (Matrix (Fin m) (Fin m) A'.carrier))
              (q.symm
                ((Algebra.TensorProduct.comm k A'.carrier k').mapMatrix
                  ((Algebra.TensorProduct.includeRight :
                    k' →ₐ[k] A'.carrier ⊗[k] k').mapMatrix
                    (Matrix.scalar (Fin m) r)))) =
              (1 : Matrix (Fin m) (Fin m) A'.carrier) ⊗ₜ[k] r
            have hfirst :
                (Algebra.TensorProduct.comm k A'.carrier k').mapMatrix
                    ((Algebra.TensorProduct.includeRight :
                      k' →ₐ[k] A'.carrier ⊗[k] k').mapMatrix
                      (Matrix.scalar (Fin m) r)) =
                  Matrix.scalar (Fin m) ((r : k') ⊗ₜ[k] (1 : A'.carrier)) := by
              apply Matrix.ext
              intro i j
              by_cases hij : i = j <;> simp [hij]
            rw [hfirst]
            have hq' :
                q.symm (Matrix.scalar (Fin m)
                  ((r : k') ⊗ₜ[k] (1 : A'.carrier))) =
                  (r : k') ⊗ₜ[k] (1 : Matrix (Fin m) (Fin m) A'.carrier) := by
              apply q.injective
              simp [hq]
            rw [hq']
            simp [Algebra.TensorProduct.comm_tmul]
          change gk (Matrix.scalar (Fin n) ((1 : A.carrier) ⊗ₜ[k] r)) =
            Matrix.scalar (Fin m) ((1 : A'.carrier) ⊗ₜ[k] r)
          change (matrixTensorEquivForSplitting k A'.carrier k' m).symm
            (e' (matrixTensorEquivForSplitting k A.carrier k' n
              (Matrix.scalar (Fin n) ((1 : A.carrier) ⊗ₜ[k] r)))) =
            Matrix.scalar (Fin m) ((1 : A'.carrier) ⊗ₜ[k] r)
          rw [hmtA]
          have he' :
              e' ((1 : Matrix (Fin n) (Fin n) A.carrier) ⊗ₜ[k] r) =
                (1 : Matrix (Fin m) (Fin m) A'.carrier) ⊗ₜ[k] r := by
            simp [e']
          rw [he', ← hmtA']
          exact (matrixTensorEquivForSplitting k A'.carrier k' m).symm_apply_apply _
        }
      gk.bijective
  exact ⟨g⟩

theorem splitting_iff_similar_embedded_subfield
    (k : Type u_k) (k' : Type u_K) [Field k]
    [Field k'] [Algebra k k'] [FiniteDimensional k k']
    (A : CSA.{u_k, u_A} k) :
    Splits k A.carrier k' ↔
    ∃ B : CSA.{u_k, u_K} k, IsBrauerEquivalent A B ∧
        ∃ f : k' →ₐ[k] B.carrier,
          Function.Injective f ∧
            Module.finrank k B.carrier = Module.finrank k k' ^ 2 := by
  constructor
  · rintro ⟨d, hsplit⟩
    let : Algebra k' (A.carrier ⊗[k] k') :=
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
    let : IsScalarTower k k' k' := by
      exact IsScalarTower.of_algebraMap_smul (by
        intro r c
        simp [Algebra.smul_def])
    let : IsScalarTower k k' V := by
      infer_instance
    let towerE : @IsScalarTower k (A.carrier ⊗[k] k') V _
        moduleE.toDistribMulAction.toSMul _ := by
      let : Module (A.carrier ⊗[k] k') V := moduleE
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
      let : Module (A.carrier ⊗[k] k') V := moduleE
      let : Module A.carrier V := moduleA
      let : IsScalarTower k (A.carrier ⊗[k] k') V := towerE
      exact IsScalarTower.of_algebraMap_smul (by
        intro r v
        change (algebraMap k A.carrier r) • v = r • v
        exact IsScalarTower.algebraMap_smul (A.carrier ⊗[k] k') r v)
    let commA : @SMulCommClass A.carrier k V
        moduleA.toDistribMulAction.toSMul _ := by
      let : Module A.carrier V := moduleA
      let : IsScalarTower k A.carrier V := towerA
      exact ⟨by
        intro a r v
        change a • (r • v) = r • (a • v)
        rw [← IsScalarTower.algebraMap_smul A.carrier r v,
          ← IsScalarTower.algebraMap_smul A.carrier r (a • v)]
        rw [← mul_smul, ← mul_smul, Algebra.commutes]⟩
    let : IsScalarTower k k V := by
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
    let : NeZero d := ⟨hd0⟩
    let : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd0⟩⟩
    let : Nontrivial V := inferInstance
    let : Module.Finite k V := Module.Finite.trans k' V
    let : Module.Free k V := Module.Free.of_divisionRing k V
    let b := Module.Free.chooseBasis k V
    let R := Module.End k V
    let : IsSimpleRing R :=
      IsSimpleRing.of_ringEquiv (algEquivMatrix b).toRingEquiv.symm inferInstance
    let : Algebra.IsCentral k R := inferInstance
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
    let : IsSimpleRing S :=
      IsSimpleRing.of_ringEquiv eS.toRingEquiv inferInstance
    let : Algebra.IsCentral k S := by
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
    let : FaithfulSMul k' V := inferInstance
    have hscalar : Function.Injective scalar := by
      intro x y hxy
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro v
      exact congrArg (fun f : Module.End k V => f v) hxy
    let scalarC : k' →ₐ[k] C := scalar.codRestrict C hscalar_mem
    have hscalarC : Function.Injective scalarC := by
      intro x y hxy
      apply hscalar
      exact congrArg Subtype.val hxy
    let : IsSimpleRing C := by
      simpa [C] using hdec.1
    let : Algebra.IsCentral k C := by
      simpa [C] using hdec.2.1
    let Bc : CSA k := { AlgCat.of k C with }
    let B : CSA k := oppositeCSA k Bc
    have hcommScalar : ∀ x y : k', Commute (scalarC x) (scalarC y) := by
      intro x y
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      change x • (y • v) = y • (x • v)
      rw [← mul_smul, ← mul_smul, mul_comm]
    let f : k' →ₐ[k] B.carrier := scalarC.toOpposite hcommScalar
    have hf : Function.Injective f := by
      intro x y hxy
      apply hscalarC
      apply Subtype.ext
      change scalarC.toOpposite hcommScalar x =
        scalarC.toOpposite hcommScalar y at hxy
      have hxy'' := congrArg MulOpposite.unop hxy
      exact congrArg Subtype.val hxy''
    obtain ⟨eSC⟩ := hdec.2.2
    let : Module.Free k C := Module.Free.of_divisionRing k C
    let m := Fintype.card (Module.Free.ChooseBasisIndex k V)
    let eR : R ≃ₐ[k] Matrix (Fin m) (Fin m) k :=
      (algEquivMatrix b).trans
        (Matrix.reindexAlgEquiv k k
          (Fintype.equivFin (Module.Free.ChooseBasisIndex k V)))
    let eTensor : A.carrier ⊗[k] C ≃ₐ[k] S ⊗[k] C :=
      Algebra.TensorProduct.congr eS (AlgEquiv.refl : C ≃ₐ[k] C)
    have hm0 : m ≠ 0 := Fintype.card_ne_zero
    have hAB : IsBrauerEquivalent A B := by
      change IsBrauerEquivalent A (oppositeCSA k Bc)
      apply splittingTensorSplitOppositeSimilarity k A Bc m hm0
      change Nonempty
        ((A.carrier ⊗[k] Bc.carrier) ≃ₐ[k]
          Matrix (Fin m) (Fin m) k)
      exact ⟨eTensor.trans (eSC.trans eR)⟩
    have hbase_finrank : Module.finrank k' (A.carrier ⊗[k] k') =
        Module.finrank k A.carrier := by
      calc
        Module.finrank k' (A.carrier ⊗[k] k') =
            Module.finrank k' (k' ⊗[k] A.carrier) :=
          (Algebra.TensorProduct.commRight k k' A.carrier).toLinearEquiv.finrank_eq.symm
        _ = Module.finrank k A.carrier := by rw [Module.finrank_baseChange]
    have hAdim : Module.finrank k A.carrier = d ^ 2 := by
      calc
        Module.finrank k A.carrier =
            Module.finrank k' (A.carrier ⊗[k] k') := hbase_finrank.symm
        _ = Module.finrank k' (Matrix (Fin d) (Fin d) k') :=
          e.toLinearEquiv.finrank_eq
        _ = d ^ 2 := by simp [Module.finrank_matrix, pow_two]
    have hVdim : Module.finrank k V = d * Module.finrank k k' := by
      change Module.finrank k (Fin d → k') = _
      rw [Module.finrank_pi_fintype]
      simp
    have hRdim : Module.finrank k R = Module.finrank k V ^ 2 := by
      change Module.finrank k (V →ₗ[k] V) = _
      rw [Module.finrank_linearMap]
      simp [pow_two]
    have hSdim : Module.finrank k S = Module.finrank k A.carrier :=
      eS.toLinearEquiv.finrank_eq.symm
    have hdimRC : Module.finrank k R =
        Module.finrank k S * Module.finrank k C := by
      let : Module.Free k S := Module.Free.of_divisionRing k S
      calc
        Module.finrank k R = Module.finrank k (S ⊗[k] C) :=
          eSC.toLinearEquiv.finrank_eq.symm
        _ = Module.finrank k S * Module.finrank k C :=
          Module.finrank_tensorProduct
    have hCdim : Module.finrank k C = Module.finrank k k' ^ 2 := by
      apply Nat.mul_right_cancel (pow_pos (Nat.pos_of_ne_zero hd0) 2)
      calc
        Module.finrank k C * d ^ 2 = d ^ 2 * Module.finrank k C :=
          Nat.mul_comm _ _
        _ = Module.finrank k A.carrier * Module.finrank k C := by rw [hAdim]
        _ = Module.finrank k S * Module.finrank k C := by rw [hSdim]
        _ = Module.finrank k R := hdimRC.symm
        _ = Module.finrank k V ^ 2 := hRdim
        _ = (d * Module.finrank k k') ^ 2 := by rw [hVdim]
        _ = Module.finrank k k' ^ 2 * d ^ 2 := by
          simp [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hBdim : Module.finrank k B.carrier = Module.finrank k k' ^ 2 := by
      change Module.finrank k Cᵐᵒᵖ = _
      calc
        Module.finrank k Cᵐᵒᵖ = Module.finrank k C :=
          (MulOpposite.opLinearEquiv k (M := C)).finrank_eq.symm
        _ = _ := hCdim
    exact ⟨B, hAB, f, hf, hBdim⟩
  · rintro ⟨B, hAB, f, hf, hBdim⟩
    have hsplitB : Splits k B.carrier k' :=
      splitting_of_embedded_subfield_of_finrank k B.carrier k' f hf hBdim
    obtain ⟨d, hsplitB⟩ := hsplitB
    let _ : Algebra k' (B.carrier ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    dsimp [SplitsInDegree] at hsplitB
    obtain ⟨eB⟩ := hsplitB
    have hd0 : d ≠ 0 := by
      intro hd
      subst d
      have hzero : (0 : B.carrier ⊗[k] k') = 1 := by
        exact eB.injective (Subsingleton.elim _ _)
      exact zero_ne_one hzero
    obtain ⟨n, m, hn, hm, ⟨eAB⟩⟩ :=
      base_change_matrix_similarity_for_splitting k k' A B hAB
    let eBmat : Matrix (Fin m) (Fin m) (B.carrier ⊗[k] k') ≃ₐ[k']
        Matrix (Fin (m * d)) (Fin (m * d)) k' :=
      let ecomm : Matrix (Fin d) (Fin d) k' ⊗[k']
          Matrix (Fin m) (Fin m) k' ≃ₐ[k']
            Matrix (Fin m) (Fin m) k' ⊗[k'] Matrix (Fin d) (Fin d) k' :=
        Algebra.TensorProduct.comm k'
          (Matrix (Fin d) (Fin d) k') (Matrix (Fin m) (Fin m) k')
      let ekron : Matrix (Fin m) (Fin m) k' ⊗[k']
          Matrix (Fin d) (Fin d) k' ≃ₐ[k']
            Matrix (Fin (m * d)) (Fin (m * d)) k' :=
        (Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin d) k' k' k' k').trans
          (Algebra.TensorProduct.rid k' k' k').mapMatrix |>.trans
            (Matrix.reindexAlgEquiv k' k' finProdFinEquiv)
      ((eB.mapMatrix).trans (matrixEquivTensor (Fin m) k'
        (Matrix (Fin d) (Fin d) k'))).trans (ecomm.trans ekron)
    let _ : Algebra k' (A.carrier ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    let hC := base_change_finite_central_simple k A.carrier k'
    let C : CSA k' :=
      { AlgCat.of k' (A.carrier ⊗[k] k') with
        isCentral := hC.2.1
        isSimple := hC.2.2
        fin_dim := hC.1 }
    let _ : Algebra.IsCentral k' (ULift.{u_A} k') :=
      { out := by
          intro x hx
          refine ⟨x.down, ?_⟩
          cases x
          rfl }
    let scalarLift : CSA.{u_K, max u_A u_K} k' :=
      { AlgCat.of k' (ULift.{u_A} k') with }
    let eLift : Matrix (Fin (m * d)) (Fin (m * d)) k' ≃ₐ[k']
        Matrix (Fin (m * d)) (Fin (m * d)) (ULift.{u_A} k') :=
      (ULift.algEquiv (R := k') (A := k')).symm.mapMatrix
    have hrel : IsBrauerEquivalent C scalarLift := by
      refine ⟨n, m * d, hn, Nat.mul_ne_zero hm hd0, ?_⟩
      change Nonempty
        (Matrix (Fin n) (Fin n) (A.carrier ⊗[k] k') ≃ₐ[k']
          Matrix (Fin (m * d)) (Fin (m * d)) (ULift.{u_A} k'))
      exact ⟨eAB.trans (eBmat.trans eLift)⟩
    obtain ⟨p, q, hp, hq, ⟨hE⟩⟩ := hrel
    let _ : IsSimpleRing C.carrier := C.isSimple
    let _ : FiniteDimensional k' C.carrier := C.fin_dim
    obtain ⟨s, hs, D, hD, hDalg, hDfinite, ⟨e⟩⟩ :=
      wedderburn_artin_finite k' C.carrier
    let _ : NeZero s := hs
    let _ : Algebra.IsCentral k' C.carrier := C.isCentral
    let _ : Algebra.IsCentral k' D :=
      { out := by
          intro x hx
          have hxcomm : ∀ y : D, Commute x y := by
            intro y
            exact (Subalgebra.mem_center_iff.mp hx y).symm
          have hxmat : Matrix.scalar (Fin s) x ∈ Set.center
              (Matrix (Fin s) (Fin s) D) := by
            rw [Semigroup.mem_center_iff]
            intro M
            exact (Matrix.scalar_commute x hxcomm M).eq.symm
          obtain ⟨a, ha⟩ := e.surjective (Matrix.scalar (Fin s) x)
          have hacenter : a ∈ Subalgebra.center k' C.carrier := by
            rw [Subalgebra.mem_center_iff]
            intro b
            have h := (Semigroup.mem_center_iff.mp hxmat) (e b)
            have h' := congrArg e.symm h
            rw [← ha] at h'
            simpa using h'
          obtain ⟨r, hr⟩ :=
            Algebra.mem_bot.mp (‹Algebra.IsCentral k' C.carrier›.out hacenter)
          apply Algebra.mem_bot.mpr
          refine ⟨r, ?_⟩
          apply (Matrix.scalar_inj (n := Fin s)).mp
          calc
            Matrix.scalar (Fin s) (algebraMap k' D r) =
                algebraMap k' (Matrix (Fin s) (Fin s) D) r := by rfl
            _ = e (algebraMap k' C.carrier r) := by simp
            _ = e a := by rw [hr]
            _ = Matrix.scalar (Fin s) x := ha }
    let eleft : Matrix (Fin p) (Fin p) C.carrier ≃ₐ[k']
        Matrix (Fin (s * p)) (Fin (s * p)) D :=
      ((e.mapMatrix).trans (matrixEquivTensor (Fin p) k'
        (Matrix (Fin s) (Fin s) D))).trans
        (((Matrix.kroneckerTMulAlgEquiv (Fin s) (Fin p) k' k' D k').trans
          (Algebra.TensorProduct.rid k' k' D).mapMatrix).trans
          (Matrix.reindexAlgEquiv k' D finProdFinEquiv))
    have hmatrix : Nonempty
        (Matrix (Fin (s * p)) (Fin (s * p)) D ≃ₐ[k']
          Matrix (Fin q) (Fin q) (ULift.{u_A} k')) := by
      exact ⟨eleft.symm.trans hE⟩
    obtain ⟨eD⟩ := (matrix_division_similarity_iff k' D
      (ULift.{u_A} k')).mp
      ⟨s * p, q, Nat.mul_ne_zero hs.out hp, hq, hmatrix⟩
    let eDK : D ≃ₐ[k'] k' :=
      eD.trans (ULift.algEquiv (R := k') (A := k'))
    let eC : C.carrier ≃ₐ[k'] Matrix (Fin s) (Fin s) k' :=
      e.trans eDK.mapMatrix
    refine ⟨s, ?_⟩
    dsimp [SplitsInDegree]
    exact ⟨eC⟩

theorem maximal_subfield_splits (k K k' : Type*) [Field k]
    [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (f : k' →ₐ[k] K) (hf : Function.Injective f)
    (hmax : IsMaximalCommutativeSubalgebra k K (AlgHom.range f)) :
    Splits k K k' := by
  exact splitting_of_embedded_subfield_of_finrank k K k' f hf
    (maximal_subfield_dimension_square k K k' f hf hmax)

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
    (splitting_iff_similar_embedded_subfield k k' A0).mp hsplit
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

private structure CentralizerDivisionPackage (k : Type u_k) (L : Type u_K) (K : Type u_A)
    [Field k] [Field L]
    [DivisionRing K] [Algebra k L] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] (f : L →ₐ[k] K) where
  carrier : Type u_A
  [divisionRing : DivisionRing carrier]
  [baseAlgebra : Algebra k carrier]
  [algebra : Algebra L carrier]
  [tower : IsScalarTower k L carrier]
  [finite : FiniteDimensional L carrier]
  [central : Algebra.IsCentral L carrier]
  embedding : carrier →ₐ[k] K
  injective : Function.Injective embedding
  embedding_as : ∀ x : L, embedding (algebraMap L carrier x) = f x
  dimension : Module.finrank k K = Module.finrank k L * Module.finrank k carrier

private theorem centralizer_division_package (k : Type u_k) (L : Type u_K) (K : Type u_A)
    [Field k] [Field L]
    [DivisionRing K] [Algebra k L] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] [FiniteDimensional k L]
    (f : L →ₐ[k] K) (hf : Function.Injective f) :
    Nonempty (CentralizerDivisionPackage k L K f) := by
  classical
  let S : Subalgebra k K := AlgHom.range f
  let eS : L ≃ₐ[k] S := AlgEquiv.ofInjective f hf
  letI : IsSimpleRing S := IsSimpleRing.of_ringEquiv eS.toRingEquiv inferInstance
  let C : Subalgebra k K := Subalgebra.centralizer k (S : Set K)
  have hct := centralizer_theorem k K S
  dsimp [C] at hct ⊢
  have hdouble : Subalgebra.centralizer k (C : Set K) = S := hct.2.2
  have hfC : ∀ x : L, f x ∈ C := by
    intro x
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    obtain ⟨y, rfl⟩ := hy
    calc
      f y * f x = f (y * x) := (map_mul f y x).symm
      _ = f (x * y) := congrArg f (mul_comm y x)
      _ = f x * f y := map_mul f x y
  let i : L →ₐ[k] C := f.codRestrict C hfC
  letI : Algebra L C := i.toRingHom.toAlgebra' (by
    intro x y
    have hy := y.property
    rw [Subalgebra.mem_centralizer_iff] at hy
    apply Subtype.ext
    change f x * (y : K) = (y : K) * f x
    exact hy (f x) ⟨x, rfl⟩)
  letI : IsScalarTower k L C := IsScalarTower.of_algebraMap_eq (by
    intro x
    apply Subtype.ext
    change algebraMap k K x = f (algebraMap k L x)
    exact (f.commutes x).symm)
  letI : DivisionRing C := DivisionRing.ofIsUnitOrEqZero (by
    intro x
    by_cases hx : (x : K) = 0
    · exact Or.inr (Subtype.ext hx)
    · left
      have hinv : (x : K)⁻¹ ∈ C := by
        rw [Subalgebra.mem_centralizer_iff]
        intro y hy
        have hxy : (x : K) * y = y * (x : K) :=
          ((Subalgebra.mem_centralizer_iff k).mp x.property y hy).symm
        apply (mul_left_cancel₀ hx)
        calc
          (x : K) * (y * (x : K)⁻¹) = ((x : K) * y) * (x : K)⁻¹ := by
            rw [mul_assoc]
          _ = (y * (x : K)) * (x : K)⁻¹ := by rw [hxy]
          _ = y * ((x : K) * (x : K)⁻¹) := by rw [mul_assoc]
          _ = y := by rw [mul_inv_cancel₀ hx, mul_one]
          _ = (x : K) * ((x : K)⁻¹ * y) := by
            rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
      let u : Cˣ :=
        { val := x
          inv := ⟨(x : K)⁻¹, hinv⟩
          val_inv := by
            apply Subtype.ext
            exact mul_inv_cancel₀ hx
          inv_val := by
            apply Subtype.ext
            exact inv_mul_cancel₀ hx }
      exact ⟨u, rfl⟩)
  letI : FiniteDimensional k C := inferInstance
  letI : Module.Finite L C := Module.Finite.of_restrictScalars_finite k L C
  letI : FiniteDimensional L C := inferInstance
  have hcentral : Algebra.IsCentral L C := by
    constructor
    intro x hx
    have hxCcentral : (x : K) ∈ Subalgebra.centralizer k (C : Set K) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro y hy
      have hxy := Subalgebra.mem_center_iff.mp hx (⟨y, hy⟩ : C)
      exact congrArg Subtype.val hxy
    have hxS : (x : K) ∈ S := by
      rw [← hdouble]
      exact hxCcentral
    obtain ⟨r, hr⟩ := hxS
    refine ⟨r, ?_⟩
    apply Subtype.ext
    change f r = (x : K)
    exact hr
  have result : CentralizerDivisionPackage k L K f := by
    refine ⟨C, ?_, ?_, ?_, ?_⟩
    · exact C.val
    · exact Subtype.val_injective
    · intro x
      rfl
    · calc
        Module.finrank k K = Module.finrank k S * Module.finrank k C := hct.2.1
        _ = Module.finrank k L * Module.finrank k C := by
          rw [eS.toLinearEquiv.finrank_eq]
  exact ⟨result⟩

private theorem exists_separable_maximal_subfield_same_universe (k K : Type u_K)
    [Field k] [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] :
    Nonempty (SeparableMaximalSubfield k K) := by
  classical
  let f : K →ₐ[k] K := AlgHom.id k K
  by_cases htrivial : (⊥ : Subalgebra k K) = ⊤
  · letI : IsMulCommutative K := ⟨⟨fun x y => by
      have hxbot : x ∈ (⊥ : Subalgebra k K) := by
        rw [htrivial]
        exact trivial
      have hybot : y ∈ (⊥ : Subalgebra k K) := by
        rw [htrivial]
        exact trivial
      obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hxbot
      obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hybot
      calc
        x * y = algebraMap k K a * algebraMap k K b := by rw [ha, hb]
        _ = algebraMap k K (a * b) := (map_mul (algebraMap k K) a b).symm
        _ = algebraMap k K (b * a) := congrArg (algebraMap k K) (mul_comm a b)
        _ = algebraMap k K b * algebraMap k K a := map_mul (algebraMap k K) b a
        _ = y * x := by rw [← hb, ← ha]⟩⟩
    letI : CommRing K := inferInstance
    letI : Field K := Field.ofIsUnitOrEqZero (by
      intro x
      by_cases hx : x = 0
      · exact Or.inr hx
      · exact Or.inl (isUnit_iff_ne_zero.mpr hx))
    letI : Algebra.IsSeparable k K := by
      constructor
      intro x
      have hxbot : x ∈ (⊥ : Subalgebra k K) := by
        rw [htrivial]
        exact trivial
      obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hxbot
      rw [← hr]
      exact isSeparable_algebraMap r
    have hf : Function.Injective f := by
      intro x y hxy
      exact hxy
    have hrange : AlgHom.range f = ⊤ := by
      apply le_antisymm le_top
      rw [← htrivial]
      exact bot_le
    have hmax : IsMaximalCommutativeSubalgebra k K (AlgHom.range f) := by
      rw [hrange]
      constructor
      · intro x y
        have hxbot : (x : K) ∈ (⊥ : Subalgebra k K) := by
          rw [htrivial]
          exact x.property
        have hybot : (y : K) ∈ (⊥ : Subalgebra k K) := by
          rw [htrivial]
          exact y.property
        obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hxbot
        obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hybot
        change (x : K) * (y : K) = (y : K) * (x : K)
        calc
          (x : K) * (y : K) = algebraMap k K a * algebraMap k K b := by
            rw [ha, hb]
          _ = algebraMap k K (a * b) := (map_mul (algebraMap k K) a b).symm
          _ = algebraMap k K (b * a) := congrArg (algebraMap k K) (mul_comm a b)
          _ = algebraMap k K b * algebraMap k K a := map_mul (algebraMap k K) b a
          _ = (y : K) * (x : K) := by rw [← hb, ← ha]
      · intro T _ hle
        exact le_antisymm le_top hle
    let result : SeparableMaximalSubfield k K := ⟨K, f, hf, hmax⟩
    exact ⟨result⟩
  · obtain ⟨x, hx, hxsep⟩ :=
      JacobsonNoether.exists_separable_and_not_isCentral' (L := k) (D := K) htrivial
    let L : Subalgebra k K := Algebra.adjoin k ({x} : Set K)
    letI : IsMulCommutative L := by
      dsimp [L]
      infer_instance
    let hring : Ring L := inferInstance
    letI : Ring L := hring
    let hcomm : CommRing L := { hring with
      mul_comm := fun a b => mul_comm a b }
    letI : CommRing L := hcomm
    letI : IsDomain L := by infer_instance
    let hfield : IsField L := IsField.of_isDomain_of_finite k L
    letI : Field L := Field.ofIsUnitOrEqZero (by
      intro a
      by_cases ha : a = 0
      · exact Or.inr ha
      · obtain ⟨b, hb⟩ := hfield.mul_inv_cancel ha
        exact Or.inl ((isUnit_iff_exists_inv).2 ⟨b, hb⟩))
    let fL : L →ₐ[k] K := L.val
    letI : Algebra.IsSeparable k L := by
      constructor
      intro y
      have hsepK : ∀ z : K, ∀ hz : z ∈ L,
          IsSeparable k (⟨z, hz⟩ : L) := by
        intro z hz
        change z ∈ Algebra.adjoin k ({x} : Set K) at hz
        induction hz using Algebra.adjoin_induction with
        | mem z hz =>
            rcases Set.mem_singleton_iff.mp hz with rfl
            apply (isSeparable_map_iff L.val Subtype.val_injective).mp
            change IsSeparable k z
            exact hxsep
        | algebraMap r =>
            exact isSeparable_algebraMap r
        | add z w hz hw hz' hw' =>
            convert Field.isSeparable_add (F := k) (E := L) hz' hw' using 1 <;> rfl
        | mul z w hz hw hz' hw' =>
            convert Field.isSeparable_mul (F := k) (E := L) hz' hw' using 1 <;> rfl
      exact hsepK (y : K) y.property
    have hfL : Function.Injective fL := Subtype.val_injective
    obtain ⟨pkg⟩ := centralizer_division_package k L K fL hfL
    let C := pkg.carrier
    letI : DivisionRing C := pkg.divisionRing
    letI : Algebra k C := pkg.baseAlgebra
    letI : Algebra L C := pkg.algebra
    letI : IsScalarTower k L C := pkg.tower
    letI : FiniteDimensional L C := pkg.finite
    letI : Algebra.IsCentral L C := pkg.central
    have hLne : L ≠ (⊥ : Subalgebra k K) := by
      intro hLbot
      apply hx
      have hxL : x ∈ L := Algebra.subset_adjoin (Set.mem_singleton x)
      rw [hLbot] at hxL
      exact hxL
    have hLdim_ne : Module.finrank k L ≠ 1 := by
      intro hLdim
      apply hLne
      exact Subalgebra.eq_bot_of_finrank_one hLdim
    have hLpos : 0 < Module.finrank k L := Module.finrank_pos
    have hLgt : 1 < Module.finrank k L := by omega
    have hCpos : 0 < Module.finrank L C := Module.finrank_pos
    have hfirst : Module.finrank L C < Module.finrank k L * Module.finrank L C := by
      simpa using Nat.mul_lt_mul_of_pos_right hLgt hCpos
    have hsecond : Module.finrank k L * Module.finrank L C <
        Module.finrank k L * (Module.finrank k L * Module.finrank L C) := by
      exact Nat.mul_lt_mul_of_pos_left hfirst hLpos
    have hlt : Module.finrank L C < Module.finrank k K := by
      calc
        Module.finrank L C < Module.finrank k L * Module.finrank L C := hfirst
        _ < Module.finrank k L * (Module.finrank k L * Module.finrank L C) := hsecond
        _ = Module.finrank k L * Module.finrank k C := by
          rw [Module.finrank_mul_finrank k L C]
        _ = Module.finrank k K := by simpa [C] using pkg.dimension.symm
    obtain ⟨q⟩ := exists_separable_maximal_subfield_same_universe (k := L) (K := C)
    let M := q.carrier
    letI : Field M := q.field
    letI : Algebra L M := q.algebra
    letI : FiniteDimensional L M := q.finite
    letI : Algebra.IsSeparable L M := q.separable
    letI : Algebra k M :=
      RingHom.toAlgebra ((algebraMap L M).comp (algebraMap k L))
    letI : IsScalarTower k L M := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional k M := FiniteDimensional.trans k L M
    letI : Algebra.IsSeparable k M := Algebra.IsSeparable.trans k L M
    let g : M →ₐ[k] K := pkg.embedding.comp (q.embedding.restrictScalars k)
    have hg : Function.Injective g := pkg.injective.comp q.injective
    have hdimC : Module.finrank L C = Module.finrank L M ^ 2 :=
      maximal_subfield_dimension_square L C M q.embedding q.injective q.maximal
    have hdimM : Module.finrank k M = Module.finrank k L * Module.finrank L M :=
      Module.finrank_mul_finrank k L M |>.symm
    have hdimK : Module.finrank k K = Module.finrank k M ^ 2 := by
      calc
        Module.finrank k K = Module.finrank k L * Module.finrank k C := pkg.dimension
        _ = Module.finrank k L * (Module.finrank k L * Module.finrank L C) := by
          rw [Module.finrank_mul_finrank k L C]
        _ = Module.finrank k L * (Module.finrank k L * (Module.finrank L M ^ 2)) := by
          rw [hdimC]
        _ = (Module.finrank k L * Module.finrank L M) ^ 2 := by
          simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = Module.finrank k M ^ 2 := by rw [hdimM]
    have hmax : IsMaximalCommutativeSubalgebra k K (AlgHom.range g) :=
      ((self_centralizing_subfield_tfae k K M g hg).out 0 2).mp hdimK
    let result : SeparableMaximalSubfield k K := ⟨M, g, hg, hmax⟩
    exact ⟨result⟩
  termination_by Module.finrank k K
  decreasing_by exact hlt

theorem exists_separable_maximal_subfield (k K : Type*) [Field k]
    [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] :
    Nonempty (SeparableMaximalSubfield k K) := by
  classical
  let f : K →ₐ[k] K := AlgHom.id k K
  by_cases htrivial : (⊥ : Subalgebra k K) = ⊤
  · letI : IsMulCommutative K := ⟨⟨fun x y => by
      have hxbot : x ∈ (⊥ : Subalgebra k K) := by
        rw [htrivial]
        exact trivial
      have hybot : y ∈ (⊥ : Subalgebra k K) := by
        rw [htrivial]
        exact trivial
      obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hxbot
      obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hybot
      calc
        x * y = algebraMap k K a * algebraMap k K b := by rw [ha, hb]
        _ = algebraMap k K (a * b) := (map_mul (algebraMap k K) a b).symm
        _ = algebraMap k K (b * a) := congrArg (algebraMap k K) (mul_comm a b)
        _ = algebraMap k K b * algebraMap k K a := map_mul (algebraMap k K) b a
        _ = y * x := by rw [← hb, ← ha]⟩⟩
    letI : CommRing K := inferInstance
    letI : Field K := Field.ofIsUnitOrEqZero (by
      intro x
      by_cases hx : x = 0
      · exact Or.inr hx
      · exact Or.inl (isUnit_iff_ne_zero.mpr hx))
    letI : Algebra.IsSeparable k K := by
      constructor
      intro x
      have hxbot : x ∈ (⊥ : Subalgebra k K) := by
        rw [htrivial]
        exact trivial
      obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hxbot
      rw [← hr]
      exact isSeparable_algebraMap r
    have hf : Function.Injective f := by
      intro x y hxy
      exact hxy
    have hrange : AlgHom.range f = ⊤ := by
      apply le_antisymm le_top
      rw [← htrivial]
      exact bot_le
    have hmax : IsMaximalCommutativeSubalgebra k K (AlgHom.range f) := by
      rw [hrange]
      constructor
      · intro x y
        have hxbot : (x : K) ∈ (⊥ : Subalgebra k K) := by
          rw [htrivial]
          exact x.property
        have hybot : (y : K) ∈ (⊥ : Subalgebra k K) := by
          rw [htrivial]
          exact y.property
        obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hxbot
        obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hybot
        change (x : K) * (y : K) = (y : K) * (x : K)
        calc
          (x : K) * (y : K) = algebraMap k K a * algebraMap k K b := by
            rw [ha, hb]
          _ = algebraMap k K (a * b) := (map_mul (algebraMap k K) a b).symm
          _ = algebraMap k K (b * a) := congrArg (algebraMap k K) (mul_comm a b)
          _ = algebraMap k K b * algebraMap k K a := map_mul (algebraMap k K) b a
          _ = (y : K) * (x : K) := by rw [← hb, ← ha]
      · intro T _ hle
        exact le_antisymm le_top hle
    let result : SeparableMaximalSubfield k K := ⟨K, f, hf, hmax⟩
    exact ⟨result⟩
  · obtain ⟨x, hx, hxsep⟩ :=
      JacobsonNoether.exists_separable_and_not_isCentral' (L := k) (D := K) htrivial
    let L : Subalgebra k K := Algebra.adjoin k ({x} : Set K)
    letI : IsMulCommutative L := by
      dsimp [L]
      infer_instance
    let hring : Ring L := inferInstance
    letI : Ring L := hring
    let hcomm : CommRing L := { hring with
      mul_comm := fun a b => mul_comm a b }
    letI : CommRing L := hcomm
    letI : IsDomain L := by infer_instance
    let hfield : IsField L := IsField.of_isDomain_of_finite k L
    letI : Field L := Field.ofIsUnitOrEqZero (by
      intro a
      by_cases ha : a = 0
      · exact Or.inr ha
      · obtain ⟨b, hb⟩ := hfield.mul_inv_cancel ha
        exact Or.inl ((isUnit_iff_exists_inv).2 ⟨b, hb⟩))
    let fL : L →ₐ[k] K := L.val
    letI : Algebra.IsSeparable k L := by
      constructor
      intro y
      have hsepK : ∀ z : K, ∀ hz : z ∈ L,
          IsSeparable k (⟨z, hz⟩ : L) := by
        intro z hz
        change z ∈ Algebra.adjoin k ({x} : Set K) at hz
        induction hz using Algebra.adjoin_induction with
        | mem z hz =>
            rcases Set.mem_singleton_iff.mp hz with rfl
            apply (isSeparable_map_iff L.val Subtype.val_injective).mp
            change IsSeparable k z
            exact hxsep
        | algebraMap r =>
            exact isSeparable_algebraMap r
        | add z w hz hw hz' hw' =>
            convert Field.isSeparable_add (F := k) (E := L) hz' hw' using 1 <;> rfl
        | mul z w hz hw hz' hw' =>
            convert Field.isSeparable_mul (F := k) (E := L) hz' hw' using 1 <;> rfl
      exact hsepK (y : K) y.property
    have hfL : Function.Injective fL := Subtype.val_injective
    obtain ⟨pkg⟩ := centralizer_division_package k L K fL hfL
    let C := pkg.carrier
    letI : DivisionRing C := pkg.divisionRing
    letI : Algebra k C := pkg.baseAlgebra
    letI : Algebra L C := pkg.algebra
    letI : IsScalarTower k L C := pkg.tower
    letI : FiniteDimensional L C := pkg.finite
    letI : Algebra.IsCentral L C := pkg.central
    have hLne : L ≠ (⊥ : Subalgebra k K) := by
      intro hLbot
      apply hx
      have hxL : x ∈ L := Algebra.subset_adjoin (Set.mem_singleton x)
      rw [hLbot] at hxL
      exact hxL
    have hLdim_ne : Module.finrank k L ≠ 1 := by
      intro hLdim
      apply hLne
      exact Subalgebra.eq_bot_of_finrank_one hLdim
    have hLpos : 0 < Module.finrank k L := Module.finrank_pos
    have hLgt : 1 < Module.finrank k L := by omega
    have hCpos : 0 < Module.finrank L C := Module.finrank_pos
    have hfirst : Module.finrank L C < Module.finrank k L * Module.finrank L C := by
      simpa using Nat.mul_lt_mul_of_pos_right hLgt hCpos
    have hsecond : Module.finrank k L * Module.finrank L C <
        Module.finrank k L * (Module.finrank k L * Module.finrank L C) := by
      exact Nat.mul_lt_mul_of_pos_left hfirst hLpos
    have hlt : Module.finrank L C < Module.finrank k K := by
      calc
        Module.finrank L C < Module.finrank k L * Module.finrank L C := hfirst
        _ < Module.finrank k L * (Module.finrank k L * Module.finrank L C) := hsecond
        _ = Module.finrank k L * Module.finrank k C := by
          rw [Module.finrank_mul_finrank k L C]
        _ = Module.finrank k K := by simpa [C] using pkg.dimension.symm
    obtain ⟨q⟩ := exists_separable_maximal_subfield_same_universe (k := L) (K := C)
    let M := q.carrier
    letI : Field M := q.field
    letI : Algebra L M := q.algebra
    letI : FiniteDimensional L M := q.finite
    letI : Algebra.IsSeparable L M := q.separable
    letI : Algebra k M :=
      RingHom.toAlgebra ((algebraMap L M).comp (algebraMap k L))
    letI : IsScalarTower k L M := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional k M := FiniteDimensional.trans k L M
    letI : Algebra.IsSeparable k M := Algebra.IsSeparable.trans k L M
    let g : M →ₐ[k] K := pkg.embedding.comp (q.embedding.restrictScalars k)
    have hg : Function.Injective g := pkg.injective.comp q.injective
    have hdimC : Module.finrank L C = Module.finrank L M ^ 2 :=
      maximal_subfield_dimension_square L C M q.embedding q.injective q.maximal
    have hdimM : Module.finrank k M = Module.finrank k L * Module.finrank L M :=
      Module.finrank_mul_finrank k L M |>.symm
    have hdimK : Module.finrank k K = Module.finrank k M ^ 2 := by
      calc
        Module.finrank k K = Module.finrank k L * Module.finrank k C := pkg.dimension
        _ = Module.finrank k L * (Module.finrank k L * Module.finrank L C) := by
          rw [Module.finrank_mul_finrank k L C]
        _ = Module.finrank k L * (Module.finrank k L * (Module.finrank L M ^ 2)) := by
          rw [hdimC]
        _ = (Module.finrank k L * Module.finrank L M) ^ 2 := by
          simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = Module.finrank k M ^ 2 := by rw [hdimM]
    have hmax : IsMaximalCommutativeSubalgebra k K (AlgHom.range g) :=
      ((self_centralizing_subfield_tfae k K M g hg).out 0 2).mp hdimK
    let result : SeparableMaximalSubfield k K := ⟨M, g, hg, hmax⟩
    exact ⟨result⟩
/-- A finite separable extension which splits a given algebra. -/
structure FiniteSeparableSplittingField (k : Type u_k) (A : Type u_A) [Field k] [Ring A]
    [Algebra k A] where
  carrier : Type*
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [finite : FiniteDimensional k carrier]
  [separable : Algebra.IsSeparable k carrier]
  degree : ℕ
  degree_pos : 0 < degree
  splitting : SplitsInDegree k A carrier degree

theorem brauer_class_has_finite_separable_splitting_field (k : Type*)
    [Field k] :
    ∀ A : CSA k, Nonempty (FiniteSeparableSplittingField k A.carrier) := by sorry
/-
  intro A
  obtain ⟨rep⟩ := wedderburn_artin_finite_central_division_representative k A
  letI : DivisionRing rep.division.carrier := rep.division.divisionRing
  letI : Algebra k rep.division.carrier := rep.division.algebra
  letI : FiniteDimensional k rep.division.carrier := rep.division.finite
  letI : Algebra.IsCentral k rep.division.carrier := rep.division.central
  obtain ⟨smf⟩ := exists_separable_maximal_subfield k rep.division.carrier
  letI : Field smf.carrier := smf.field
  letI : Algebra k smf.carrier := smf.algebra
  letI : FiniteDimensional k smf.carrier := smf.finite
  letI : Algebra.IsSeparable k smf.carrier := smf.separable
  let B : CSA k := rep.division.toCSA k
  have hsim : IsBrauerEquivalent A B := by
    refine ⟨1, rep.degree, one_ne_zero, Nat.ne_of_gt rep.degree_pos, ?_⟩
    change Nonempty
      (Matrix (Fin 1) (Fin 1) A.carrier ≃ₐ[k]
        Matrix (Fin rep.degree) (Fin rep.degree) rep.division.carrier)
    obtain ⟨e⟩ := rep.equivalence
    exact ⟨(splittingMatrixOneAlgEquiv k A.carrier).trans e⟩
  have hsplit : Splits k A.carrier smf.carrier := by
    apply (splitting_iff_similar_embedded_subfield k smf.carrier A).2
    refine ⟨B, hsim, smf.embedding, smf.injective, ?_⟩
    exact maximal_subfield_dimension_square k rep.division.carrier smf.carrier
      smf.embedding smf.injective smf.maximal
  obtain ⟨d, hd⟩ := hsplit
  have hdpos : 0 < d := by
    let _ : Algebra smf.carrier (A.carrier ⊗[k] smf.carrier) :=
      Algebra.TensorProduct.rightAlgebra
    dsimp [SplitsInDegree] at hd
    obtain ⟨e⟩ := hd
    have hdne : d ≠ 0 := by
      intro hd0
      subst d
      have hzero : (0 : A.carrier ⊗[k] smf.carrier) = 1 := by
        exact e.injective (Subsingleton.elim _ _)
      exact zero_ne_one hzero
    exact Nat.pos_of_ne_zero hdne
  refine ⟨{
    carrier := smf.carrier
    degree := d
    degree_pos := hdpos
    splitting := hd }⟩

 -/
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
