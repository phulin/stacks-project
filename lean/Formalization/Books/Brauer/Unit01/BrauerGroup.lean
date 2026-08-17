import Formalization.Books.Brauer.Unit01.AlgebraLemmas
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# The Brauer group of a field

Mathlib already supplies the canonical `CSA`, similarity relation, setoid, and
quotient used here.  This file adds the source-facing interfaces for the
group, base-change, division-representative, and dimension assertions.
-/

namespace Formalization.Books.Brauer

open scoped TensorProduct

universe u_k u_A u_E

/-- The similarity class of a finite central simple algebra. -/
def brauerClass (k : Type*) [Field k] (A : CSA k) : BrauerGroup k :=
  Quotient.mk (Brauer.CSA_Setoid k) A

/- The scalar algebra is the identity representative in the source's
   tensor-product construction. -/
def scalarCSA (k : Type*) [Field k] : CSA k :=
  { AlgCat.of k k with }

/- The opposite algebra is the source's representative for the inverse
   similarity class. -/
def oppositeCSA (k : Type*) [Field k] (A : CSA k) : CSA k :=
  { AlgCat.of k (A.carrierᵐᵒᵖ) with }

/- The canonical right-hand tensor algebra is local in Mathlib, so this
   relation packages the source's base-change representative without
   introducing a competing algebra structure. -/
def IsBaseChangeRepresentative (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] (A : CSA k) (B : CSA k') : Prop :=
  letI : Algebra k' (A.carrier ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  Nonempty ((A.carrier ⊗[k] k') ≃ₐ[k'] B.carrier)

theorem similarity_is_equivalence (k : Type*) [Field k] :
    Equivalence (@IsBrauerEquivalent k _) :=
  IsBrauerEquivalent.is_eqv

theorem similarity_has_unique_division_representative (k : Type u_k) [Field k]
    (A : CSA.{u_k, u_A} k) :
      ∃ D : CSA.{u_k, u_A} k,
        Nonempty (DivisionRing D.carrier) ∧
          IsBrauerEquivalent A D ∧
            ∀ E : CSA.{u_k, u_E} k, Nonempty (DivisionRing E.carrier) →
            IsBrauerEquivalent A E →
                Nonempty (D.carrier ≃ₐ[k] E.carrier) := by
  sorry

private theorem matrix_standard_module_end_alg (k K : Type*) [Field k]
    [DivisionRing K] [Algebra k K] (n : ℕ) [NeZero n] :
    Nonempty
      (Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) ≃ₐ[k] Kᵐᵒᵖ) := by
  classical
  let e := ModuleCat.matrixEquivalence K (i := Classical.arbitrary (Fin n))
  let f : Module.End K K →+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
    { toFun := fun x => (e.functor.map (ModuleCat.ofHom x)).hom
      map_zero' := by
        ext
        rfl
      map_add' := by
        intro x y
        ext v
        rfl
      map_one' := by
        rfl
      map_mul' := by
        intro x y
        rfl }
  let ef : Module.End K K ≃+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
    RingEquiv.ofBijective f (by
      constructor
      · intro x y h
        have h' : e.functor.map (ModuleCat.ofHom x) =
            e.functor.map (ModuleCat.ofHom y) := by
          apply ModuleCat.hom_ext
          exact h
        have hxy := e.functor.map_injective h'
        exact congrArg ModuleCat.Hom.hom hxy
      · intro y
        obtain ⟨x, hx⟩ := e.functor.map_surjective
          (ModuleCat.ofHom (X := e.functor.obj (ModuleCat.of K K))
            (Y := e.functor.obj (ModuleCat.of K K)) y)
        refine ⟨x.hom, ?_⟩
        have hx' : x = ModuleCat.ofHom x.hom := by
          apply ModuleCat.hom_ext
          rfl
        rw [hx'] at hx
        have hxy := congrArg ModuleCat.Hom.hom hx
        change (e.functor.map (ModuleCat.ofHom x.hom)).hom = y at hxy
        exact hxy)
  have hcomm : ∀ r : k,
      ef (algebraMap k (Module.End K K) r) = algebraMap k
        (Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) r := by
    intro r
    ext v i
    change (e.functor.map (ModuleCat.ofHom (algebraMap k (Module.End K K) r))).hom v i = _
    simp [e, ModuleCat.matrixEquivalence, ModuleCat.toMatrixModCat,
      ModuleCat.toMatrixModCat_map]
    change (r • (1 : Module.End K K)) (v i) = _
    simp [Algebra.smul_def]
  refine ⟨((AlgEquiv.moduleEndSelf k : Kᵐᵒᵖ ≃ₐ[k] Module.End K K).trans
    (AlgEquiv.ofRingEquiv (f := ef) hcomm)).symm⟩

theorem matrix_division_similarity_iff (k K K' : Type*) [Field k]
    [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsCentral k K] [DivisionRing K'] [Algebra k K']
    [FiniteDimensional k K'] [Algebra.IsCentral k K'] :
    (∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧
      Nonempty (Matrix (Fin n) (Fin n) K ≃ₐ[k]
        Matrix (Fin m) (Fin m) K')) ↔
      Nonempty (K ≃ₐ[k] K') := by
  constructor
  · rintro ⟨n, m, hn, hm, ⟨E⟩⟩
    let R := Matrix (Fin n) (Fin n) K
    let R' := Matrix (Fin m) (Fin m) K'
    letI : NeZero n := ⟨hn⟩
    letI : NeZero m := ⟨hm⟩
    letI : IsSimpleRing R := inferInstance
    letI : RingHomInvPair E.toRingEquiv.toRingHom E.toRingEquiv.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv E.toRingEquiv
    letI : RingHomInvPair E.toRingEquiv.symm.toRingHom E.toRingEquiv.toRingHom :=
      RingHomInvPair.symm E.toRingEquiv.toRingHom E.toRingEquiv.symm.toRingHom
    let V := Fin n → K
    let W := Fin m → K'
    letI : Module R W := Module.compHom W E.toRingEquiv.toRingHom
    letI : IsScalarTower k R W :=
      IsScalarTower.of_algebraMap_smul fun r w => by
        change E (algebraMap k R r) • w = r • w
        rw [E.commutes]
        exact IsScalarTower.algebraMap_smul R' r w
    let l : W ≃ₛₗ[E.toRingEquiv.toRingHom] W :=
      { Equiv.refl W with
        map_add' := by intro x y; rfl
        map_smul' := by intro r x; rfl }
    have hsimpleW : IsSimpleModule R W := by
      exact (LinearMap.isSimpleModule_iff_of_bijective
        (R := R) (S := R') (M := W) (N := W)
        (σ := E.toRingEquiv.toRingHom) l.toLinearMap l.bijective).mpr
        (matrix_standard_module_is_simple K' m)
    letI : IsSimpleModule R V := matrix_standard_module_is_simple K n
    letI : IsSimpleModule R W := hsimpleW
    obtain ⟨v⟩ := finite_simple_algebra_unique_simple_modules k R V W
    obtain ⟨eK⟩ := matrix_standard_module_end_alg k K n
    obtain ⟨eK'⟩ := matrix_standard_module_end_alg k K' m
    let q : Module.End R W ≃ₐ[k] Module.End R' W :=
      AlgEquiv.ofRingEquiv (f := l.conjRingEquiv) (by
        intro r
        ext v i
        simp [LinearEquiv.conjRingEquiv, LinearEquiv.arrowCongrAddEquiv, l,
          Algebra.algebraMap_eq_smul_one]
        change (r • (1 : Module.End R W)) v i = (r • v) i
        simp)
    exact ⟨(eK.symm.trans ((v.conjAlgEquiv k).trans (q.trans eK'))).unop⟩
  · rintro ⟨e⟩
    exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

theorem brauer_group_is_abelian (k : Type*) [Field k] :
    ∃ G : CommGroup (BrauerGroup k),
      letI : CommGroup (BrauerGroup k) := G
      brauerClass k (scalarCSA k) = 1 ∧
        (∀ A B : CSA k, ∃ C : CSA k,
          brauerClass k A * brauerClass k B = brauerClass k C ∧
            Nonempty ((A.carrier ⊗[k] B.carrier) ≃ₐ[k] C.carrier)) ∧
          ∀ A : CSA k,
            brauerClass k A * brauerClass k (oppositeCSA k A) = 1 := by
  sorry

/- Make the existence result available to the later interfaces as the
   chapter's chosen group structure on the quotient. -/
noncomputable instance brauerGroupCommGroup (k : Type*) [Field k] :
    CommGroup (BrauerGroup k) :=
  Classical.choose (brauer_group_is_abelian k)

theorem brauer_group_tensor_operation_interface (k : Type*) [Field k] :
    ∀ A B : CSA k, ∃ C : CSA k,
      brauerClass k A * brauerClass k B = brauerClass k C ∧
        Nonempty ((A.carrier ⊗[k] B.carrier) ≃ₐ[k] C.carrier) := by
  intro A B
  simpa only [brauerGroupCommGroup] using
    (Classical.choose_spec (brauer_group_is_abelian k)).2.1 A B

theorem brauer_group_base_change_interface (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] :
    ∃ f : BrauerGroup k →* BrauerGroup k',
      ∀ A : CSA k, ∃ B : CSA k',
        f (brauerClass k A) = brauerClass k' B ∧
          IsBaseChangeRepresentative k k' A B := by
  sorry

theorem brauer_group_zero_iff (k : Type*) [Field k] :
    (∀ x : BrauerGroup k, x = 1) ↔
      (∀ (K : Type*) [DivisionRing K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsCentral k K],
        Nonempty (K ≃ₐ[k] k)) := by
  sorry

theorem brauer_group_algebraically_closed (k : Type*) [Field k]
    [IsAlgClosed k] :
    ∀ x : BrauerGroup k, x = 1 := by
  intro x
  refine Quotient.inductionOn x ?_
  intro A
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k A.carrier
  have hA : IsBrauerEquivalent A (scalarCSA k) := by
    refine ⟨n, n * n, hn.out, Nat.mul_ne_zero hn.out hn.out, ?_⟩
    let e1 : Matrix (Fin n) (Fin n) A.carrier ≃ₐ[k]
        Matrix (Fin n) (Fin n) (Matrix (Fin n) (Fin n) k) := e.mapMatrix
    let e2 : Matrix (Fin n) (Fin n) (Matrix (Fin n) (Fin n) k) ≃ₐ[k]
      Matrix (Fin n) (Fin n) k ⊗[k] Matrix (Fin n) (Fin n) k :=
      matrixEquivTensor (Fin n) k (Matrix (Fin n) (Fin n) k)
    let e3 : Matrix (Fin n) (Fin n) k ⊗[k] Matrix (Fin n) (Fin n) k ≃ₐ[k]
      Matrix (Fin n × Fin n) (Fin n × Fin n) k :=
      Matrix.kroneckerAlgEquiv (Fin n) (Fin n) k
    exact ⟨e1.trans (e2.trans (e3.trans
      (Matrix.reindexAlgEquiv k k finProdFinEquiv)))⟩
  calc
    brauerClass k A = brauerClass k (scalarCSA k) := Quotient.sound hA
    _ = 1 := by
      simpa only [brauerGroupCommGroup] using
        (Classical.choose_spec (brauer_group_is_abelian k)).1

theorem finite_central_simple_dimension_square (k A : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [IsSimpleRing A] :
    ∃ d : ℕ, Module.finrank k A = d ^ 2 := by
  let K := AlgebraicClosure k
  letI : Algebra K (A ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  have hbase := base_change_finite_central_simple k A K
  letI : FiniteDimensional K (A ⊗[k] K) := hbase.1
  letI : Algebra.IsCentral K (A ⊗[k] K) := hbase.2.1
  letI : IsSimpleRing (A ⊗[k] K) := hbase.2.2
  obtain ⟨d, hd, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K (A ⊗[k] K)
  refine ⟨d, ?_⟩
  have hcomm : Module.finrank K (K ⊗[k] A) = Module.finrank k A := by
    rw [Module.finrank_baseChange]
  have hswap : Module.finrank K (K ⊗[k] A) = Module.finrank K (A ⊗[k] K) :=
    (Algebra.TensorProduct.commRight k K A).toLinearEquiv.finrank_eq
  calc
    Module.finrank k A = Module.finrank K (K ⊗[k] A) := hcomm.symm
    _ = Module.finrank K (A ⊗[k] K) := hswap
    _ = Module.finrank K (Matrix (Fin d) (Fin d) K) := e.toLinearEquiv.finrank_eq
    _ = d ^ 2 := by simp [Module.finrank_matrix, pow_two]

end Formalization.Books.Brauer
