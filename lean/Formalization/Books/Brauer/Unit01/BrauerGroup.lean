import Formalization.Books.Brauer.Unit01.AlgebraLemmas
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.RingTheory.Finiteness.Small

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

private theorem matrix_standard_module_end_alg_for_unique (k K : Type*) [Field k]
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
    simp [e, ModuleCat.matrixEquivalence, ModuleCat.toMatrixModCat]
    change (r • (1 : Module.End K K)) (v i) = _
    simp [Algebra.smul_def]
  refine ⟨((AlgEquiv.moduleEndSelf k : Kᵐᵒᵖ ≃ₐ[k] Module.End K K).trans
    (AlgEquiv.ofRingEquiv (f := ef) hcomm)).symm⟩

private theorem matrix_division_similarity_iff_for_unique (k K K' : Type*) [Field k]
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
    let _ : NeZero n := ⟨hn⟩
    let _ : NeZero m := ⟨hm⟩
    let _ : IsSimpleRing R := inferInstance
    let _ : RingHomInvPair E.toRingEquiv.toRingHom E.toRingEquiv.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv E.toRingEquiv
    let _ : RingHomInvPair E.toRingEquiv.symm.toRingHom E.toRingEquiv.toRingHom :=
      RingHomInvPair.symm E.toRingEquiv.toRingHom E.toRingEquiv.symm.toRingHom
    let V := Fin n → K
    let W := Fin m → K'
    let _ : Module R W := Module.compHom W E.toRingEquiv.toRingHom
    let _ : IsScalarTower k R W :=
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
    let _ : IsSimpleModule R V := matrix_standard_module_is_simple K n
    let _ : IsSimpleModule R W := hsimpleW
    obtain ⟨v⟩ := finite_simple_algebra_unique_simple_modules k R V W
    obtain ⟨eK⟩ := matrix_standard_module_end_alg_for_unique k K n
    obtain ⟨eK'⟩ := matrix_standard_module_end_alg_for_unique k K' m
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

theorem similarity_has_unique_division_representative (k : Type u_k) [Field k]
    (A : CSA.{u_k, u_A} k) :
      ∃ D : CSA.{u_k, u_A} k,
        (∀ x : D.carrier, IsUnit x ∨ x = 0) ∧
          IsBrauerEquivalent A D ∧
            ∀ E : CSA.{u_k, u_E} k,
            (∀ x : E.carrier, IsUnit x ∨ x = 0) →
            IsBrauerEquivalent A E →
                Nonempty (D.carrier ≃ₐ[k] E.carrier) := by
  classical
  obtain ⟨n, hn, D, hD, hDalg, hDfinite, ⟨e⟩⟩ :=
    wedderburn_artin_finite k A.carrier
  let _ : NeZero n := hn
  let _ : Algebra.IsCentral k A.carrier := A.isCentral
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
        obtain ⟨a, ha⟩ := e.surjective (Matrix.scalar (Fin n) x)
        have hacenter : a ∈ Subalgebra.center k A.carrier := by
          rw [Subalgebra.mem_center_iff]
          intro b
          have h := (Semigroup.mem_center_iff.mp hxmat) (e b)
          have h' := congrArg e.symm h
          rw [← ha] at h'
          simpa using h'
        obtain ⟨r, hr⟩ :=
          Algebra.mem_bot.mp (‹Algebra.IsCentral k A.carrier›.out hacenter)
        apply Algebra.mem_bot.mpr
        refine ⟨r, ?_⟩
        apply (Matrix.scalar_inj (n := Fin n)).mp
        calc
          Matrix.scalar (Fin n) (algebraMap k D r) =
              algebraMap k (Matrix (Fin n) (Fin n) D) r := by rfl
          _ = e (algebraMap k A.carrier r) := by simp
          _ = e a := by rw [hr]
          _ = Matrix.scalar (Fin n) x := ha }
  let D' : CSA.{u_k, u_A} k := { AlgCat.of k D with }
  have hAD : IsBrauerEquivalent A D' := by
    refine ⟨1, n, one_ne_zero, hn.out, ?_⟩
    let f : Matrix (Fin 1) (Fin 1) A.carrier →ₐ[k] A.carrier :=
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
    exact ⟨(AlgEquiv.ofBijective f hf).trans e⟩
  refine ⟨D', ?_, hAD, ?_⟩
  · intro x
    by_cases hx : (x : D) = 0
    · exact Or.inr hx
    · exact Or.inl (isUnit_iff_ne_zero.mpr hx)
  · intro E hE hAE
    let _ : DivisionRing E.carrier := DivisionRing.ofIsUnitOrEqZero hE
    have hDE : IsBrauerEquivalent D' E :=
      IsBrauerEquivalent.trans (IsBrauerEquivalent.symm hAD) hAE
    obtain ⟨eDE⟩ := (matrix_division_similarity_iff_for_unique k D E.carrier).mp hDE
    exact ⟨eDE⟩

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
    simp [e, ModuleCat.matrixEquivalence, ModuleCat.toMatrixModCat]
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
    let _ : NeZero n := ⟨hn⟩
    let _ : NeZero m := ⟨hm⟩
    let _ : IsSimpleRing R := inferInstance
    let _ : RingHomInvPair E.toRingEquiv.toRingHom E.toRingEquiv.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv E.toRingEquiv
    let _ : RingHomInvPair E.toRingEquiv.symm.toRingHom E.toRingEquiv.toRingHom :=
      RingHomInvPair.symm E.toRingEquiv.toRingHom E.toRingEquiv.symm.toRingHom
    let V := Fin n → K
    let W := Fin m → K'
    let _ : Module R W := Module.compHom W E.toRingEquiv.toRingHom
    let _ : IsScalarTower k R W :=
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
    let _ : IsSimpleModule R V := matrix_standard_module_is_simple K n
    let _ : IsSimpleModule R W := hsimpleW
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

private def tensorCSA (k : Type*) [Field k] (A B : CSA k) : CSA k :=
  let h := tensor_product_finite_central_simple k A.carrier B.carrier
  { AlgCat.of k (A.carrier ⊗[k] B.carrier) with
    isCentral := h.2.1
    isSimple := h.2.2
    fin_dim := h.1 }

private noncomputable def matrixOneAlgEquiv (k R : Type*) [Field k] [Ring R] [Algebra k R] :
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

private def matrixTensorEquiv (k X Y : Type*) [CommSemiring k]
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

private theorem tensor_similarity_left (k : Type*) [Field k]
    (A A' B : CSA k) (h : IsBrauerEquivalent A A') :
    IsBrauerEquivalent (tensorCSA k A B) (tensorCSA k A' B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ?_⟩
  let e' := Algebra.TensorProduct.congr e (AlgEquiv.refl : B.carrier ≃ₐ[k] B.carrier)
  change Nonempty
    (Matrix (Fin n) (Fin n) (A.carrier ⊗[k] B.carrier) ≃ₐ[k]
      Matrix (Fin m) (Fin m) (A'.carrier ⊗[k] B.carrier))
  exact ⟨(matrixTensorEquiv k A.carrier B.carrier n).trans
    (e'.trans (matrixTensorEquiv k A'.carrier B.carrier m).symm)⟩

private theorem tensor_similarity_right (k : Type*) [Field k]
    (A B B' : CSA k) (h : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (tensorCSA k A B) (tensorCSA k A B') := by
  have hleft : IsBrauerEquivalent (tensorCSA k B A) (tensorCSA k B' A) :=
    tensor_similarity_left k B B' A h
  obtain ⟨n, m, hn, hm, ⟨eleft⟩⟩ := hleft
  refine ⟨n, m, hn, hm, ?_⟩
  let commAB : A.carrier ⊗[k] B.carrier ≃ₐ[k] B.carrier ⊗[k] A.carrier :=
    Algebra.TensorProduct.comm k A.carrier B.carrier
  let commAB' : A.carrier ⊗[k] B'.carrier ≃ₐ[k] B'.carrier ⊗[k] A.carrier :=
    Algebra.TensorProduct.comm k A.carrier B'.carrier
  exact ⟨(commAB.mapMatrix).trans
    (eleft.trans (commAB'.mapMatrix).symm)⟩

private theorem tensor_similarity_comm (k : Type*) [Field k]
    (A B : CSA k) :
    IsBrauerEquivalent (tensorCSA k A B) (tensorCSA k B A) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] B.carrier) ≃ₐ[k]
      Matrix (Fin 1) (Fin 1) (B.carrier ⊗[k] A.carrier))
  let uA : Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] B.carrier) ≃ₐ[k]
      A.carrier ⊗[k] B.carrier := matrixOneAlgEquiv k _
  let uB : Matrix (Fin 1) (Fin 1) (B.carrier ⊗[k] A.carrier) ≃ₐ[k]
      B.carrier ⊗[k] A.carrier := matrixOneAlgEquiv k _
  exact ⟨uA.trans
    ((Algebra.TensorProduct.comm k A.carrier B.carrier).trans uB.symm)⟩

private theorem opposite_similarity (k : Type*) [Field k]
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

private theorem tensor_similarity_scalar_left (k : Type*) [Field k]
    (A : CSA k) :
    IsBrauerEquivalent (tensorCSA k (scalarCSA k) A) A := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (k ⊗[k] A.carrier) ≃ₐ[k]
      Matrix (Fin 1) (Fin 1) A.carrier)
  exact ⟨(Algebra.TensorProduct.lid k A.carrier).mapMatrix⟩

private theorem tensor_similarity_scalar_right (k : Type*) [Field k]
    (A : CSA k) :
    IsBrauerEquivalent (tensorCSA k A (scalarCSA k)) A := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] k) ≃ₐ[k]
      Matrix (Fin 1) (Fin 1) A.carrier)
  exact ⟨(Algebra.TensorProduct.rid k k A.carrier).mapMatrix⟩

private theorem tensor_similarity_assoc (k : Type*) [Field k]
    (A B C : CSA k) :
    IsBrauerEquivalent (tensorCSA k (tensorCSA k A B) C)
      (tensorCSA k A (tensorCSA k B C)) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) ((A.carrier ⊗[k] B.carrier) ⊗[k] C.carrier) ≃ₐ[k]
      Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] (B.carrier ⊗[k] C.carrier)))
  exact ⟨(Algebra.TensorProduct.assoc k k k A.carrier B.carrier C.carrier).mapMatrix⟩

private theorem tensor_similarity_inverse_left (k : Type*) [Field k]
    (A : CSA k) :
    IsBrauerEquivalent (tensorCSA k A (oppositeCSA k A)) (scalarCSA k) := by
  have hd : Module.finrank k A.carrier ≠ 0 :=
    Nat.ne_of_gt (Module.finrank_pos (R := k) (M := A.carrier))
  obtain ⟨e⟩ := inverse_of_finite_central_simple k A.carrier
  refine ⟨1, Module.finrank k A.carrier, one_ne_zero, hd, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] A.carrierᵐᵒᵖ) ≃ₐ[k]
      Matrix (Fin (Module.finrank k A.carrier))
        (Fin (Module.finrank k A.carrier)) k)
  exact ⟨(matrixOneAlgEquiv k _).trans e⟩

private theorem tensor_similarity_inverse_right (k : Type*) [Field k]
    (A : CSA k) :
    IsBrauerEquivalent (tensorCSA k (oppositeCSA k A) A) (scalarCSA k) :=
  IsBrauerEquivalent.trans (tensor_similarity_comm k (oppositeCSA k A) A)
    (tensor_similarity_inverse_left k A)

private def baseChangeCSA (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] (A : CSA k) : CSA k' :=
  let _ : Algebra k' (A.carrier ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  let h := base_change_finite_central_simple k A.carrier k'
  { AlgCat.of k' (A.carrier ⊗[k] k') with
    isCentral := h.2.1
    isSimple := h.2.2
    fin_dim := h.1 }

private theorem base_change_similarity (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] (A A' : CSA k) (h : IsBrauerEquivalent A A') :
    IsBrauerEquivalent (baseChangeCSA k k' A) (baseChangeCSA k k' A') := by
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
    (matrixTensorEquiv k A.carrier k' n).trans
      (e'.trans (matrixTensorEquiv k A'.carrier k' m).symm)
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
              matrixTensorEquiv k A.carrier k' n
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
              matrixTensorEquiv k A'.carrier k' m
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
          change (matrixTensorEquiv k A'.carrier k' m).symm
            (e' ((matrixTensorEquiv k A.carrier k' n)
              (Matrix.scalar (Fin n) ((1 : A.carrier) ⊗ₜ[k] r)))) =
            Matrix.scalar (Fin m) ((1 : A'.carrier) ⊗ₜ[k] r)
          rw [hmtA]
          have he' :
              e' ((1 : Matrix (Fin n) (Fin n) A.carrier) ⊗ₜ[k] r) =
                (1 : Matrix (Fin m) (Fin m) A'.carrier) ⊗ₜ[k] r := by
            simp [e']
          rw [he', ← hmtA']
          exact (matrixTensorEquiv k A'.carrier k' m).symm_apply_apply _
        }
      gk.bijective
  exact ⟨g⟩

theorem brauer_group_is_abelian (k : Type*) [Field k] :
    ∃ G : CommGroup (BrauerGroup k),
      letI : CommGroup (BrauerGroup k) := G
      brauerClass k (scalarCSA k) = 1 ∧
        (∀ A B : CSA k, ∃ C : CSA k,
          brauerClass k A * brauerClass k B = brauerClass k C ∧
            Nonempty ((A.carrier ⊗[k] B.carrier) ≃ₐ[k] C.carrier)) ∧
          ∀ A : CSA k,
            brauerClass k A * brauerClass k (oppositeCSA k A) = 1 := by
  classical
  let mul : BrauerGroup k → BrauerGroup k → BrauerGroup k := fun x y =>
    Quotient.liftOn₂ x y
      (fun A B => brauerClass k (tensorCSA k A B))
      (by
        intro A B A' B' hAA' hBB'
        apply Quotient.sound
        exact IsBrauerEquivalent.trans
          (tensor_similarity_left k A A' B hAA')
          (tensor_similarity_right k A' B B' hBB'))
  let inv : BrauerGroup k → BrauerGroup k := fun x =>
    Quotient.liftOn x
      (fun A => brauerClass k (oppositeCSA k A))
      (by
        intro A B h
        apply Quotient.sound
        exact opposite_similarity k A B h)
  let G : CommGroup (BrauerGroup k) :=
    { mul := mul
      one := brauerClass k (scalarCSA k)
      inv := inv
      mul_assoc := by
        intro x y z
        refine Quotient.inductionOn x ?_
        intro A
        refine Quotient.inductionOn y ?_
        intro B
        refine Quotient.inductionOn z ?_
        intro C
        change brauerClass k (tensorCSA k (tensorCSA k A B) C) =
          brauerClass k (tensorCSA k A (tensorCSA k B C))
        exact Quotient.sound (tensor_similarity_assoc k A B C)
      one_mul := by
        intro x
        refine Quotient.inductionOn x ?_
        intro A
        change brauerClass k (tensorCSA k (scalarCSA k) A) = brauerClass k A
        exact Quotient.sound (tensor_similarity_scalar_left k A)
      mul_one := by
        intro x
        refine Quotient.inductionOn x ?_
        intro A
        change brauerClass k (tensorCSA k A (scalarCSA k)) = brauerClass k A
        exact Quotient.sound (tensor_similarity_scalar_right k A)
      inv_mul_cancel := by
        intro x
        refine Quotient.inductionOn x ?_
        intro A
        change brauerClass k (tensorCSA k (oppositeCSA k A) A) =
          brauerClass k (scalarCSA k)
        exact Quotient.sound (tensor_similarity_inverse_right k A)
      mul_comm := by
        intro x y
        refine Quotient.inductionOn x ?_
        intro A
        refine Quotient.inductionOn y ?_
        intro B
        change brauerClass k (tensorCSA k A B) =
          brauerClass k (tensorCSA k B A)
        exact Quotient.sound (tensor_similarity_comm k A B) }
  refine ⟨G, ?_⟩
  let : CommGroup (BrauerGroup k) := G
  refine ⟨rfl, ?_, ?_⟩
  · intro A B
    refine ⟨tensorCSA k A B, ?_, ?_⟩
    · rfl
    · exact ⟨AlgEquiv.refl⟩
  · intro A
    change brauerClass k (tensorCSA k A (oppositeCSA k A)) =
      brauerClass k (scalarCSA k)
    exact Quotient.sound (tensor_similarity_inverse_left k A)

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

private theorem base_change_tensor_equiv (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] (A B : CSA k) :
    let _ : Algebra k' (A.carrier ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    let _ : Algebra k' (B.carrier ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    let _ : Algebra k' ((A.carrier ⊗[k] B.carrier) ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    Nonempty
      (((A.carrier ⊗[k] B.carrier) ⊗[k] k') ≃ₐ[k']
        ((A.carrier ⊗[k] k') ⊗[k'] (B.carrier ⊗[k] k'))) := by
  dsimp
  let _ : Algebra k' (A.carrier ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  let _ : Algebra k' (B.carrier ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  let _ : Algebra k' ((A.carrier ⊗[k] B.carrier) ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  let e₁ :
      ((A.carrier ⊗[k] k') ⊗[k'] (B.carrier ⊗[k] k')) ≃ₐ[k']
        ((A.carrier ⊗[k] k') ⊗[k'] (k' ⊗[k] B.carrier)) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl)
      (Algebra.TensorProduct.commRight k k' B.carrier).symm
  let e₂ :
      ((A.carrier ⊗[k] k') ⊗[k'] (k' ⊗[k] B.carrier)) ≃ₐ[k']
        ((A.carrier ⊗[k] k') ⊗[k] B.carrier) :=
    Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'
        (A.carrier ⊗[k] k') B.carrier)
      (by
        intro a₁ a₂ r₁ r₂
        induction r₁ using TensorProduct.induction_on with
        | zero => simp
        | tmul r₁ b₁ =>
            induction r₂ using TensorProduct.induction_on with
            | zero => simp
            | tmul r₂ b₂ =>
                have hcent (r : k') (x y : A.carrier ⊗[k] k') :
                    algebraMap k' (A.carrier ⊗[k] k') r * (x * y) =
                      x * (algebraMap k' (A.carrier ⊗[k] k') r * y) := by
                  rw [← Algebra.smul_def r (x * y),
                    ← Algebra.smul_def r y]
                  exact (mul_smul_comm r x y).symm
                simp [TensorProduct.AlgebraTensorModule.cancelBaseChange,
                  Algebra.smul_def, mul_assoc]
                rw [hcent r₂ a₁ a₂]
            | add r₂ s₂ hr₂ hs₂ =>
                simp only [mul_add, TensorProduct.tmul_add, map_add, hr₂, hs₂]
        | add r₁ s₁ hr₁ hs₁ =>
            simp only [add_mul, TensorProduct.tmul_add, map_add, hr₁, hs₁])
      (by
        simp [TensorProduct.AlgebraTensorModule.cancelBaseChange,
          Algebra.TensorProduct.one_def])
  let e₃k :
      ((A.carrier ⊗[k] k') ⊗[k] B.carrier) ≃ₐ[k]
        ((A.carrier ⊗[k] B.carrier) ⊗[k] k') :=
    (Algebra.TensorProduct.assoc k k k A.carrier k' B.carrier).trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl)
        (Algebra.TensorProduct.comm k k' B.carrier)).trans
        (Algebra.TensorProduct.assoc k k k A.carrier B.carrier k').symm)
  let e₃ :
      ((A.carrier ⊗[k] k') ⊗[k] B.carrier) ≃ₐ[k']
        ((A.carrier ⊗[k] B.carrier) ⊗[k] k') :=
    AlgEquiv.ofBijective
      { toFun := e₃k
        map_one' := e₃k.map_one
        map_mul' := e₃k.map_mul
        map_zero' := e₃k.map_zero
        map_add' := e₃k.map_add
        commutes' := by
          intro r
          simp [e₃k, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.right_algebraMap_apply,
            Algebra.TensorProduct.assoc_tmul,
            Algebra.TensorProduct.comm_tmul,
            Algebra.TensorProduct.one_def] }
      e₃k.bijective
  exact ⟨(e₁.trans (e₂.trans e₃)).symm⟩

private theorem brauerClass_tensor_eq_mul (k : Type u_k) [Field k]
    (A B : CSA.{u_k, u_k} k) :
    brauerClass k (tensorCSA k A B) =
      brauerClass k A * brauerClass k B := by
  obtain ⟨C, hC, ⟨e⟩⟩ := brauer_group_tensor_operation_interface k A B
  have hsim : IsBrauerEquivalent (tensorCSA k A B) C := by
    refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
    change Nonempty
      (Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] B.carrier) ≃ₐ[k]
        Matrix (Fin 1) (Fin 1) C.carrier)
    exact ⟨(matrixOneAlgEquiv k _).trans
      (e.trans (matrixOneAlgEquiv k _).symm)⟩
  exact (Quotient.sound hsim).trans hC.symm

private noncomputable def shrunkBaseChangeCSA (k : Type u_k) (k' : Type u_A)
    [Field k] [Field k'] [Algebra k k']
    (A : CSA.{u_k, u_k} k) : CSA.{u_A, u_A} k' := by
  let _ : Algebra k' (A.carrier ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  let C := baseChangeCSA k k' A
  let : Algebra.IsCentral k' (A.carrier ⊗[k] k') := C.isCentral
  let : IsSimpleRing (A.carrier ⊗[k] k') := C.isSimple
  let : FiniteDimensional k' (A.carrier ⊗[k] k') := C.fin_dim
  let : Small.{u_A} (A.carrier ⊗[k] k') :=
    Module.Finite.small k' (A.carrier ⊗[k] k')
  let e : Shrink.{u_A} (A.carrier ⊗[k] k') ≃ (A.carrier ⊗[k] k') :=
    (equivShrink (A.carrier ⊗[k] k')).symm
  let : Ring (Shrink.{u_A} (A.carrier ⊗[k] k')) := Equiv.ring e
  let : Algebra k' (Shrink.{u_A} (A.carrier ⊗[k] k')) := Equiv.algebra k' e
  let ealg : Shrink.{u_A} (A.carrier ⊗[k] k') ≃ₐ[k']
      (A.carrier ⊗[k] k') := Equiv.algEquiv k' e
  exact
    { AlgCat.of k' (Shrink.{u_A} (A.carrier ⊗[k] k')) with
      isCentral := by
        refine ⟨?_⟩
        intro x hx
        obtain ⟨r, hr⟩ := C.isCentral.out
          ((MulEquivClass.apply_mem_center_iff ealg).mpr hx)
        refine ⟨r, ?_⟩
        apply ealg.injective
        dsimp [C, baseChangeCSA] at hr
        calc
          ealg (algebraMap k' (Shrink.{u_A} (A.carrier ⊗[k] k')) r) =
              algebraMap k' (A.carrier ⊗[k] k') r := ealg.commutes r
          _ = (Algebra.ofId k' (A.carrier ⊗[k] k')).toRingHom r := by
            simp [Algebra.ofId]
          _ = ealg x := hr
      isSimple := IsSimpleRing.of_ringEquiv ealg.symm.toRingEquiv
        (inferInstance : IsSimpleRing (A.carrier ⊗[k] k'))
      fin_dim := ealg.symm.toLinearEquiv.finiteDimensional }

private theorem shrunk_base_change_equiv (k : Type u_k) (k' : Type u_A)
    [Field k] [Field k'] [Algebra k k']
    (A : CSA.{u_k, u_k} k) :
    let _ : Algebra k' (A.carrier ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    Nonempty
      ((A.carrier ⊗[k] k') ≃ₐ[k'] (shrunkBaseChangeCSA k k' A).carrier) := by
  let _ : Algebra k' (A.carrier ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  dsimp [shrunkBaseChangeCSA]
  let C := baseChangeCSA k k' A
  let : Algebra.IsCentral k' (A.carrier ⊗[k] k') := C.isCentral
  let : IsSimpleRing (A.carrier ⊗[k] k') := C.isSimple
  let : FiniteDimensional k' (A.carrier ⊗[k] k') := C.fin_dim
  let : Small.{u_A} (A.carrier ⊗[k] k') :=
    Module.Finite.small k' (A.carrier ⊗[k] k')
  let e : Shrink.{u_A} (A.carrier ⊗[k] k') ≃ (A.carrier ⊗[k] k') :=
    (equivShrink (A.carrier ⊗[k] k')).symm
  let : Ring (Shrink.{u_A} (A.carrier ⊗[k] k')) := Equiv.ring e
  let : Algebra k' (Shrink.{u_A} (A.carrier ⊗[k] k')) := Equiv.algebra k' e
  let ealg : Shrink.{u_A} (A.carrier ⊗[k] k') ≃ₐ[k']
      (A.carrier ⊗[k] k') := Equiv.algEquiv k' e
  exact ⟨ealg.symm⟩

private theorem base_change_to_shrunk_similarity
    (k : Type u_k) (k' : Type u_A) [Field k] [Field k'] [Algebra k k']
    (A : CSA.{u_k, u_k} k) :
    IsBrauerEquivalent (baseChangeCSA k k' A)
      (shrunkBaseChangeCSA k k' A) := by
  let _ : Algebra k' (A.carrier ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra
  obtain ⟨e⟩ := shrunk_base_change_equiv k k' A
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (A.carrier ⊗[k] k') ≃ₐ[k']
      Matrix (Fin 1) (Fin 1) (shrunkBaseChangeCSA k k' A).carrier)
  exact ⟨(matrixOneAlgEquiv k' _).trans
    (e.trans (matrixOneAlgEquiv k' _).symm)⟩

private theorem brauer_quotient_sound_low (k : Type u_k) [Field k]
    (A B : CSA.{u_k, u_k} k) (h : IsBrauerEquivalent A B) :
    brauerClass k A = brauerClass k B := by
  exact Quotient.sound h

theorem brauer_group_base_change_interface (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] :
    ∃ f : BrauerGroup k →* BrauerGroup k',
      ∀ A : CSA k, ∃ B : CSA k',
        f (brauerClass k A) = brauerClass k' B ∧
          IsBaseChangeRepresentative k k' A B := by
  classical
  let _ : CommGroup (BrauerGroup k) := brauerGroupCommGroup k
  let _ : CommGroup (BrauerGroup k') := brauerGroupCommGroup k'
  let f₀ : BrauerGroup k → BrauerGroup k' :=
    Quotient.lift (fun A => brauerClass k'
        (shrunkBaseChangeCSA k k' A))
      (by
        intro A A' h
        change (⟦shrunkBaseChangeCSA k k' A⟧ : BrauerGroup k') =
          ⟦shrunkBaseChangeCSA k k' A'⟧
        have hsim : IsBrauerEquivalent
            (shrunkBaseChangeCSA k k' A)
            (shrunkBaseChangeCSA k k' A') :=
          IsBrauerEquivalent.trans
            (IsBrauerEquivalent.trans
              (base_change_to_shrunk_similarity k k' A).symm
              (base_change_similarity k k' A A' h))
            (base_change_to_shrunk_similarity k k' A')
        exact brauer_quotient_sound_low k'
          (shrunkBaseChangeCSA k k' A) (shrunkBaseChangeCSA k k' A') hsim)
  have hscalar : IsBrauerEquivalent
      (baseChangeCSA k k' (scalarCSA k)) (scalarCSA k') := by
    let _ : Algebra k' (k ⊗[k] k') :=
      Algebra.TensorProduct.rightAlgebra
    let eScalarK : k ⊗[k] k' ≃ₐ[k] k' :=
      Algebra.TensorProduct.lid k k'
    let eScalar : k ⊗[k] k' ≃ₐ[k'] k' :=
      AlgEquiv.ofBijective
        { toFun := eScalarK
          map_one' := eScalarK.map_one
          map_mul' := eScalarK.map_mul
          map_zero' := eScalarK.map_zero
          map_add' := eScalarK.map_add
          commutes' := by
            intro r
            simp [eScalarK, Algebra.TensorProduct.right_algebraMap_apply] }
        eScalarK.bijective
    refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
    change Nonempty
      (Matrix (Fin 1) (Fin 1) (k ⊗[k] k') ≃ₐ[k']
        Matrix (Fin 1) (Fin 1) k')
    exact ⟨(matrixOneAlgEquiv k' _).trans
      (eScalar.trans (matrixOneAlgEquiv k' _).symm)⟩
  have hscalarShrunk : IsBrauerEquivalent
      (shrunkBaseChangeCSA k k' (scalarCSA k)) (scalarCSA k') := by
    exact IsBrauerEquivalent.trans
      (base_change_to_shrunk_similarity k k' (scalarCSA k)).symm
      hscalar
  let f : BrauerGroup k →* BrauerGroup k' :=
    { toFun := f₀
      map_one' := by
        have hone : (1 : BrauerGroup k) = brauerClass k (scalarCSA k) := by
          symm
          simpa only [brauerGroupCommGroup] using
            (Classical.choose_spec (brauer_group_is_abelian k)).1
        rw [hone]
        dsimp [f₀]
        change brauerClass k' (shrunkBaseChangeCSA k k' (scalarCSA k)) = 1
        calc
          brauerClass k' (shrunkBaseChangeCSA k k' (scalarCSA k)) =
              brauerClass k' (scalarCSA k') := Quotient.sound hscalarShrunk
          _ = 1 := by
            simpa only [brauerGroupCommGroup] using
              (Classical.choose_spec (brauer_group_is_abelian k')).1
      map_mul' := by
        intro x y
        refine Quotient.inductionOn x ?_
        intro A
        refine Quotient.inductionOn y ?_
        intro B
        dsimp [f₀]
        have hprod :
            brauerClass k A * brauerClass k B =
              brauerClass k (tensorCSA k A B) :=
          (brauerClass_tensor_eq_mul k A B).symm
        have hprodRaw :
            (⟦A⟧ : BrauerGroup k) * ⟦B⟧ =
              ⟦tensorCSA k A B⟧ := by
          simpa only [brauerClass] using hprod
        rw [hprodRaw]
        change brauerClass k' (shrunkBaseChangeCSA k k'
            (tensorCSA k A B)) =
          brauerClass k' (shrunkBaseChangeCSA k k' A) *
            brauerClass k' (shrunkBaseChangeCSA k k' B)
        rw [← brauerClass_tensor_eq_mul k'
          (shrunkBaseChangeCSA k k' A) (shrunkBaseChangeCSA k k' B)]
        apply Quotient.sound
        refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
        let _ : Algebra k' (A.carrier ⊗[k] k') :=
          Algebra.TensorProduct.rightAlgebra
        let _ : Algebra k' (B.carrier ⊗[k] k') :=
          Algebra.TensorProduct.rightAlgebra
        let _ : Algebra k' ((A.carrier ⊗[k] B.carrier) ⊗[k] k') :=
          Algebra.TensorProduct.rightAlgebra
        let _ : Algebra k' ((tensorCSA k A B).carrier ⊗[k] k') :=
          Algebra.TensorProduct.rightAlgebra
        obtain ⟨eAB⟩ := shrunk_base_change_equiv k k'
          (tensorCSA k A B)
        obtain ⟨eBase⟩ := base_change_tensor_equiv k k' A B
        obtain ⟨eA⟩ := shrunk_base_change_equiv k k' A
        obtain ⟨eB⟩ := shrunk_base_change_equiv k k' B
        let eFactors :
            (A.carrier ⊗[k] k') ⊗[k'] (B.carrier ⊗[k] k') ≃ₐ[k']
              (shrunkBaseChangeCSA k k' A).carrier ⊗[k']
                (shrunkBaseChangeCSA k k' B).carrier :=
          Algebra.TensorProduct.congr eA eB
        let eTotal :
            (shrunkBaseChangeCSA k k' (tensorCSA k A B)).carrier ≃ₐ[k']
              (shrunkBaseChangeCSA k k' A).carrier ⊗[k']
                (shrunkBaseChangeCSA k k' B).carrier :=
          eAB.symm.trans (eBase.trans eFactors)
        change Nonempty
          (Matrix (Fin 1) (Fin 1)
              (shrunkBaseChangeCSA k k' (tensorCSA k A B)).carrier ≃ₐ[k']
            Matrix (Fin 1) (Fin 1)
              ((shrunkBaseChangeCSA k k' A).carrier ⊗[k']
                (shrunkBaseChangeCSA k k' B).carrier))
        exact ⟨(matrixOneAlgEquiv k' _).trans
          (eTotal.trans (matrixOneAlgEquiv k' _).symm)⟩ }
  refine ⟨f, ?_⟩
  intro A
  let B : CSA k' := shrunkBaseChangeCSA k k' A
  refine ⟨B, ?_, ?_⟩
  · change brauerClass k' (shrunkBaseChangeCSA k k' A) =
      brauerClass k' (shrunkBaseChangeCSA k k' A)
    rfl
  · dsimp [IsBaseChangeRepresentative, B]
    exact shrunk_base_change_equiv k k' A

theorem brauer_group_zero_iff (k : Type u_k) [Field k] :
    (∀ x : BrauerGroup.{u_k, u_k} k, x = 1) ↔
      (∀ (K : Type u_k) [DivisionRing K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsCentral k K],
        Nonempty (K ≃ₐ[k] k)) := by
  classical
  have hscalar : brauerClass k (scalarCSA k) = 1 := by
    simpa only [brauerGroupCommGroup] using
      (Classical.choose_spec (brauer_group_is_abelian k)).1
  constructor
  · intro h K instK instAlg instFin instCentral
    let A : CSA.{u_k, u_k} k := { AlgCat.of k K with }
    have hclass : brauerClass k A = brauerClass k (scalarCSA k) :=
      (h (brauerClass k A)).trans hscalar.symm
    have hsim : IsBrauerEquivalent A (scalarCSA k) :=
      Quotient.exact hclass
    obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := hsim
    change Nonempty (K ≃ₐ[k] k)
    exact (matrix_division_similarity_iff k K k).mp
      ⟨n, m, hn, hm, ⟨e⟩⟩
  · intro h x
    refine Quotient.inductionOn x ?_
    intro A
    obtain ⟨D, hD, hAD, _hunique⟩ :=
      @similarity_has_unique_division_representative.{u_k, u_k, u_k} k _ A
    let _ : DivisionRing D.carrier := DivisionRing.ofIsUnitOrEqZero hD
    obtain ⟨eD⟩ := h D.carrier
    have hDscalar : IsBrauerEquivalent D (scalarCSA k) := by
      refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
      change Nonempty
        (Matrix (Fin 1) (Fin 1) D.carrier ≃ₐ[k]
          Matrix (Fin 1) (Fin 1) k)
      exact ⟨eD.mapMatrix⟩
    calc
      brauerClass k A = brauerClass k D := Quotient.sound hAD
      _ = brauerClass k (scalarCSA k) := Quotient.sound hDscalar
      _ = 1 := hscalar

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
  let _ : Algebra K (A ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  have hbase := base_change_finite_central_simple k A K
  let _ : FiniteDimensional K (A ⊗[k] K) := hbase.1
  let _ : Algebra.IsCentral K (A ⊗[k] K) := hbase.2.1
  let _ : IsSimpleRing (A ⊗[k] K) := hbase.2.2
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
