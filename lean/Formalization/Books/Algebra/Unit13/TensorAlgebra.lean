import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.AlgCat.FilteredColimits
import Mathlib.Algebra.Category.AlgCat.TensorAlgebra
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.RingTheory.TensorProduct.Maps
import Formalization.Books.Algebra.Unit12.TensorProducts

/-!
# Commutative Algebra, Chapter 13: Tensor algebra

The chapter uses Mathlib's canonical tensor, exterior, and symmetric algebra
constructions.  The lower-case declarations below are book-facing interfaces;
the underlying objects and their universal properties remain Mathlib's.
-/

namespace Formalization.Books.Algebra.Unit13

attribute [local instance] RestrictScalars.moduleOrig

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit09
open scoped DirectSum TensorProduct

universe u v uR uM₂ uM₁ uM

noncomputable section

/-! ## Tensor, exterior, and symmetric algebras -/

/-- The `n`th tensor power appearing in the direct-sum grading of a tensor algebra. -/
abbrev tensorPower (R M : Type*) (n : ℕ) [CommRing R] [AddCommGroup M] [Module R M] :=
  TensorPower R n M

/-- The `n`th symmetric power, represented by Mathlib's symmetric tensor power. -/
abbrev symmetricPower (R : Type u) (M : Type v) (n : ℕ)
    [CommRing R] [AddCommGroup M] [Module R M] :=
  SymmetricPower R (ULift.{u} (Fin n)) M

/-- The `n`th exterior power, represented by the homogeneous component of the exterior algebra. -/
abbrev exteriorPower (R M : Type*) (n : ℕ) [CommRing R] [AddCommGroup M] [Module R M] :=
  ⋀[R]^n M

/-- The tensor algebra of an `R`-module. -/
abbrev tensorAlgebra (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :=
  TensorAlgebra R M

/-- The exterior algebra of an `R`-module. -/
abbrev exteriorAlgebra (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :=
  ExteriorAlgebra R M

/-- The symmetric algebra of an `R`-module. -/
abbrev symmetricAlgebra (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :=
  SymmetricAlgebra R M

/-- The direct-sum presentation of the tensor algebra by its tensor powers. -/
noncomputable def tensorAlgebraDirectSumEquiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    tensorAlgebra R M ≃ₐ[R] ⨁ n : ℕ, tensorPower R M n :=
  TensorAlgebra.equivDirectSum

/-- The degree-zero tensor power is canonically the coefficient ring. -/
def tensorPowerZeroEquiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    tensorPower R M 0 ≃ₗ[R] R :=
  (TensorPower.algebraMap₀ (R := R) (M := M)).symm

/-- The first tensor power is canonically the original module. -/
def tensorPowerOneEquiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    tensorPower R M 1 ≃ₗ[R] M :=
  PiTensorProduct.subsingletonEquiv (0 : Fin 1)

/-- Multiplication in the tensor algebra concatenates pure tensors. -/
theorem tensorAlgebra_pure_tensor_mul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n m : ℕ} (x : Fin n → M) (y : Fin m → M) :
    TensorAlgebra.tprod R M n x * TensorAlgebra.tprod R M m y =
      TensorAlgebra.tprod R M (n + m) (Fin.append x y) := by
  rw [← TensorPower.toTensorAlgebra_tprod, ← TensorPower.toTensorAlgebra_tprod,
    ← TensorPower.toTensorAlgebra_gMul, TensorPower.tprod_mul_tprod,
    TensorPower.toTensorAlgebra_tprod]

/-- The canonical tensor-to-exterior algebra map records the quotient relation. -/
def tensorAlgebraToExterior
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    tensorAlgebra R M →ₐ[R] exteriorAlgebra R M :=
  TensorAlgebra.toExterior

@[simp]
theorem tensorAlgebraToExterior_ι
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (m : M) :
    tensorAlgebraToExterior (R := R) (M := M) (TensorAlgebra.ι R m) =
      ExteriorAlgebra.ι R m := by
  exact TensorAlgebra.toExterior_ι m

/-- The defining square-zero relation in the exterior algebra. -/
theorem exterior_generator_square_zero
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (m : M) :
    ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R m = 0 := by
  exact ExteriorAlgebra.ι_sq_zero m

/-- Pure exterior tensors are alternating; repeated entries give zero. -/
theorem exterior_pure_tensor_eq_zero_of_repeated
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} {x : Fin n → M} (i j : Fin n) (hij : i ≠ j) (h : x i = x j) :
    ExteriorAlgebra.ιMulti R n x = 0 := by
  exact AlternatingMap.map_eq_zero_of_eq (ExteriorAlgebra.ιMulti R n) x h hij

/-- Pure exterior tensors span their homogeneous exterior power. -/
theorem exterior_pure_tensor_span
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ) :
    Submodule.span R (Set.range (exteriorPower.ιMulti R n)) =
      (⊤ : Submodule R (exteriorPower R M n)) := by
  exact exteriorPower.ιMulti_span R n M

/-- Degree-one generators anticommute in the exterior algebra. -/
theorem exterior_generator_swap
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x y : M) :
    ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y =
      -ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R x := by
  simp [eq_neg_iff_add_eq_zero, ExteriorAlgebra.ι_add_mul_swap]

/-- Pure symmetric tensors span their symmetric power. -/
theorem symmetric_pure_tensor_span
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ) :
    Submodule.span R
        (Set.range
          (SymmetricPower.tprod R (ι := ULift.{u} (Fin n)) (M := M))) =
      (⊤ : Submodule R (symmetricPower R M n)) := by
  exact SymmetricPower.span_tprod_eq_top R (ULift.{u} (Fin n)) M

/-- Permuting the entries of a pure symmetric tensor does not change it. -/
@[simp]
theorem symmetric_pure_tensor_perm
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (σ : Equiv.Perm (ULift.{u} (Fin n)))
    (x : ULift.{u} (Fin n) → M) :
    SymmetricPower.tprod R (fun i => x (σ i)) =
      SymmetricPower.tprod R x := by
  exact SymmetricPower.tprod_equiv σ x

/-! ## Finite free examples and freeness -/

/-- A finite free basis gives the standard exterior-algebra basis indexed by subsets. -/
theorem finite_free_exterior_algebra_basis
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [LinearOrder ι] (b : Module.Basis ι R M) :
    Nonempty (Module.Basis (Finset ι) R (exteriorAlgebra R M)) := by
  exact ⟨b.ExteriorAlgebra⟩

/-- A finite free basis identifies the symmetric algebra with a polynomial algebra. -/
theorem finite_free_symmetric_algebra_polynomial
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) :
    Nonempty (symmetricAlgebra R M ≃ₐ[R] MvPolynomial ι R) := by
  exact ⟨SymmetricAlgebra.equivMvPolynomial b⟩

private noncomputable def symmetricPowerOrbitSet (J I : Type*) [DecidableEq J] :
    Setoid (J → I) where
  r p q := ∃ e : Equiv.Perm J, q = fun j => p (e j)
  iseqv := {
    refl := fun p => ⟨Equiv.refl _, rfl⟩
    symm := by
      rintro p q ⟨e, rfl⟩
      exact ⟨e.symm, by ext j; simp⟩
    trans := by
      rintro p q r ⟨e, rfl⟩ ⟨f, rfl⟩
      exact ⟨f.trans e, by ext j; rfl⟩ }

private noncomputable def symmetricPowerCollapse
    (R J I : Type*) [CommRing R] [DecidableEq J]
    (q : (J → I) → Quotient (symmetricPowerOrbitSet J I)) :
    ((J → I) →₀ R) →ₗ[R] (Quotient (symmetricPowerOrbitSet J I) →₀ R) :=
  Finsupp.lsum R (fun p => Finsupp.lsingle (q p))

/-- The symmetric and exterior powers of a free module are free. -/
theorem free_symmetric_and_exterior_power
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] (n : ℕ) :
    Module.Free R (symmetricPower R M n) ∧ Module.Free R (exteriorPower R M n) := by
  constructor
  · classical
    let J := ULift (Fin n)
    let ⟨I, b⟩ := Module.Free.exists_basis R M
    let S := symmetricPowerOrbitSet J I
    let q : (J → I) → Quotient S := Quotient.mk'
    let C : (⨂[R] _ : J, M) →ₗ[R] (Quotient S →₀ R) :=
      (symmetricPowerCollapse R J I q).comp
        (Basis.piTensorProduct (fun _ : J => b)).repr.toLinearMap
    have hC (e : Equiv.Perm J) :
        C.comp (PiTensorProduct.reindex R (fun _ : J => M) e).toLinearMap = C := by
      apply (Basis.piTensorProduct (fun _ : J => b)).ext
      intro p
      simp only [C, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Basis.piTensorProduct_apply]
      rw [PiTensorProduct.reindex_tprod,
        ← Basis.piTensorProduct_apply, ← Basis.piTensorProduct_apply,
        Module.Basis.repr_self, Module.Basis.repr_self]
      simp only [symmetricPowerCollapse, Finsupp.lsum_single, q]
      simp only [Finsupp.lsingle_apply]
      apply congrArg (fun z : Quotient S => Finsupp.single z (1 : R))
      apply Quotient.sound
      exact ⟨e, by ext i; simp⟩

    have hrel : addConGen (SymmetricPower.Rel R J M) ≤
        AddCon.ker C.toAddMonoidHom := by
      apply AddCon.addConGen_le.2
      intro x y hxy
      cases hxy with
      | perm e f =>
        have he := LinearMap.congr_fun (hC e.symm) (PiTensorProduct.tprod R f)
        change C (PiTensorProduct.reindex R (fun _ : J => M) e.symm
          (PiTensorProduct.tprod R f)) = C (PiTensorProduct.tprod R f) at he
        rw [PiTensorProduct.reindex_tprod] at he
        change C (PiTensorProduct.tprod R f) =
          C (PiTensorProduct.tprod R (fun i => f (e i)))
        exact he.symm

    let D : SymmetricPower R J M →ₗ[R] (Quotient S →₀ R) :=
      { toFun := AddCon.lift (addConGen (SymmetricPower.Rel R J M))
          C.toAddMonoidHom hrel
        map_add' := by
          intro x y
          exact map_add _ _ _
        map_smul' := by
          intro r x
          refine AddCon.induction_on x ?_
          intro t
          change C (r • t) = r • C t
          exact C.map_smul r t }

    have hD (t : (⨂[R] _ : J, M)) :
        D (SymmetricPower.mk R J M t) = C t := by
      change AddCon.lift (addConGen (SymmetricPower.Rel R J M))
        C.toAddMonoidHom hrel (AddCon.mk' _ t) = C t
      exact AddCon.lift_coe hrel t

    let v : Quotient S → SymmetricPower R J M := fun z =>
      SymmetricPower.tprod R (fun j => b (Quotient.out z j))

    have hv (z : Quotient S) : D (v z) = Finsupp.single z (1 : R) := by
      change D (SymmetricPower.mk R J M
        (PiTensorProduct.tprod R (fun j => b (Quotient.out z j)))) = _
      rw [hD]
      simp only [C, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← Basis.piTensorProduct_apply, Module.Basis.repr_self]
      simp only [symmetricPowerCollapse, Finsupp.lsum_single, q]
      simp only [Finsupp.lsingle_apply]
      congr 1
      exact Quotient.out_eq z

    have hli : LinearIndependent R v := by
      apply LinearIndependent.of_comp D
      rw [show D ∘ v = (fun z => Finsupp.single z (1 : R)) by
        funext z; exact hv z]
      exact
        (Finsupp.basisSingleOne (R := R) (ι := Quotient S)).linearIndependent

    have hspanT : Submodule.span R (Set.range (fun p : J → I =>
        PiTensorProduct.tprod R (fun j => b (p j)))) = ⊤ := by
      apply PiTensorProduct.submodule_span_eq_top
      intro j
      exact b.span_eq

    have hspanBasis : Submodule.span R (Set.range (fun p : J → I =>
        SymmetricPower.tprod R (fun j => b (p j)))) = ⊤ := by
      rw [SymmetricPower.tprod, LinearMap.coe_compMultilinearMap]
      change Submodule.span R (Set.range ((SymmetricPower.mk R J M) ∘
        (fun p : J → I => PiTensorProduct.tprod R (fun j => b (p j))))) = ⊤
      rw [Set.range_comp, Submodule.span_image, hspanT, Submodule.map_top,
        SymmetricPower.range_mk]

    have hspan : ⊤ ≤ Submodule.span R (Set.range v) := by
      rw [← hspanBasis]
      apply Submodule.span_mono
      rintro _ ⟨p, rfl⟩
      refine ⟨q p, ?_⟩
      unfold v
      have hq : S (Quotient.out (q p)) p := by
        dsimp [q]
        exact Quotient.mk_out p
      rcases hq with ⟨e, he⟩
      have hfirst : SymmetricPower.tprod R (fun j => b (p j)) =
          SymmetricPower.tprod R (fun j => b (Quotient.out (q p) (e j))) := by
        congr 1
        funext j
        exact congrArg (fun k : J → I => b (k j)) he
      have ht : SymmetricPower.tprod R (fun j => b (p j)) =
          SymmetricPower.tprod R (fun j => b (Quotient.out (q p) j)) := by
        rw [hfirst]
        exact SymmetricPower.tprod_equiv e
          (fun j => b (Quotient.out (q p) j))
      exact ht.symm

    exact Module.Free.of_basis (Module.Basis.mk hli hspan)
  · infer_instance

/-! ## Presentations by relations -/

/-! The maps below separate the quotient functoriality from the relation
insertion appearing in the presentation lemma. -/

/-- The map on symmetric powers induced by a quotient map of modules. -/
def symmetricPowerQuotientMap
    {R : Type uR} {M₁ : Type uM₁} {M : Type uM} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M]
    [Module R M₁] [Module R M] (n : ℕ) (g : M₁ →ₗ[R] M) :
    symmetricPower R M₁ n →ₗ[R] symmetricPower R M n := by
  let C : (⨂[R] _ : ULift.{uR} (Fin n), M₁) →ₗ[R]
      symmetricPower R M n :=
    (SymmetricPower.mk R (ULift.{uR} (Fin n)) M).comp
      (PiTensorProduct.map (fun _ : ULift.{uR} (Fin n) => g))
  have hC : addConGen (SymmetricPower.Rel R (ULift.{uR} (Fin n)) M₁) ≤
      AddCon.ker C.toAddMonoidHom := by
    apply AddCon.addConGen_le.2
    intro x y hxy
    cases hxy with
    | perm e f =>
        change C (PiTensorProduct.tprod R f) =
          C (PiTensorProduct.tprod R (fun i => f (e i)))
        dsimp [C]
        rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
        exact (SymmetricPower.tprod_equiv (R := R) (M := M) e
          (fun i => g (f i))).symm
  exact
    { toFun := AddCon.lift
        (addConGen (SymmetricPower.Rel R (ULift.{uR} (Fin n)) M₁))
        C.toAddMonoidHom hC
      map_add' := by intro x y; exact map_add _ _ _
      map_smul' := by
        intro r x
        refine AddCon.induction_on x ?_
        intro t
        change C (r • t) = r • C t
        exact C.map_smul r t }

@[simp]
theorem symmetricPowerQuotientMap_tprod
    {R : Type uR} {M₁ : Type uM₁} {M : Type uM} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M]
    [Module R M₁] [Module R M] (n : ℕ) (g : M₁ →ₗ[R] M)
    (x : ULift.{uR} (Fin n) → M₁) :
      symmetricPowerQuotientMap n g (SymmetricPower.tprod R x) =
      SymmetricPower.tprod R (fun i => g (x i)) := by
  let C : (⨂[R] _ : ULift.{uR} (Fin n), M₁) →ₗ[R]
      symmetricPower R M n :=
    (SymmetricPower.mk R (ULift.{uR} (Fin n)) M).comp
      (PiTensorProduct.map (fun _ : ULift.{uR} (Fin n) => g))
  have hC : addConGen (SymmetricPower.Rel R (ULift.{uR} (Fin n)) M₁) ≤
      AddCon.ker C.toAddMonoidHom := by
    apply AddCon.addConGen_le.2
    intro x y hxy
    cases hxy with
    | perm e f =>
        change C (PiTensorProduct.tprod R f) =
          C (PiTensorProduct.tprod R (fun i => f (e i)))
        dsimp [C]
        rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
        exact (SymmetricPower.tprod_equiv (R := R) (M := M) e
          (fun i => g (f i))).symm
  change AddCon.lift (addConGen (SymmetricPower.Rel R (ULift.{uR} (Fin n)) M₁))
      C.toAddMonoidHom hC
      (AddCon.mk' _ (PiTensorProduct.tprod R x)) = _
  calc
    ((addConGen (SymmetricPower.Rel R (ULift.{uR} (Fin n)) M₁)).lift
        C.toAddMonoidHom hC)
        (AddCon.mk' _ (PiTensorProduct.tprod R x)) = C (PiTensorProduct.tprod R x) :=
      AddCon.lift_coe hC _
    _ = _ := by
      dsimp [C]
      rw [PiTensorProduct.map_tprod]
      rfl

/-- The map on exterior powers induced by a quotient map of modules. -/
def exteriorPowerQuotientMap
    {R : Type uR} {M₁ : Type uM₁} {M : Type uM} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M]
    [Module R M₁] [Module R M] (n : ℕ) (g : M₁ →ₗ[R] M) :
    exteriorPower R M₁ n →ₗ[R] exteriorPower R M n :=
  exteriorPower.map n g

@[simp]
theorem exteriorPowerQuotientMap_ιMulti
    {R : Type uR} {M₁ : Type uM₁} {M : Type uM} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M]
    [Module R M₁] [Module R M] (n : ℕ) (g : M₁ →ₗ[R] M)
    (x : Fin n → M₁) :
    exteriorPowerQuotientMap n g (exteriorPower.ιMulti R n x) =
      exteriorPower.ιMulti R n (fun i => g (x i)) := by
  exact exteriorPower.map_apply_ιMulti g x

/-- The symmetric relation-insertion map in the quotient presentation.

The quotient lift is made explicit: the multilinear map inserts `f z` in
one slot, while `AddCon.lift` descends it through the symmetric relations. -/
noncomputable def symmetricPowerRelationMap
    {R : Type uR} {M₂ : Type uM₂} {M₁ : Type uM₁} [CommRing R]
    [AddCommGroup M₂] [AddCommGroup M₁]
    [Module R M₂] [Module R M₁]
    (f : M₂ →ₗ[R] M₁) {n : ℕ} (hn : 0 < n) :
    TensorProduct R M₂ (symmetricPower R M₁ (n - 1)) →ₗ[R]
      symmetricPower R M₁ n := by
  classical
  let h₁ : 1 + (n - 1) = n := Nat.add_sub_of_le (Nat.succ_le_iff.2 hn)
  let σ : ULift.{uR} (Fin n) ≃
      ULift.{uR} (Fin 1) ⊕ ULift.{uR} (Fin (n - 1)) :=
    ((Equiv.ulift : ULift.{uR} (Fin n) ≃ Fin n).trans (finCongr h₁.symm)).trans
      (finSumFinEquiv.symm.trans
        (Equiv.sumCongr (Equiv.ulift.symm) (Equiv.ulift.symm)))
  let F : MultilinearMap R
      (fun _ : ULift.{uR} (Fin 1) ⊕ ULift.{uR} (Fin (n - 1)) => M₁)
      (symmetricPower R M₁ n) :=
    (SymmetricPower.tprod R).domDomCongr σ
  let H : M₁ →ₗ[R]
      MultilinearMap R (fun _ : ULift.{uR} (Fin (n - 1)) => M₁)
        (symmetricPower R M₁ n) :=
    (MultilinearMap.ofSubsingletonₗ R R M₁
      (MultilinearMap R (fun _ : ULift.{uR} (Fin (n - 1)) => M₁)
        (symmetricPower R M₁ n)) (ULift.up 0)).symm F.currySum
  let C : M₂ →ₗ[R]
      (⨂[R] _ : ULift.{uR} (Fin (n - 1)), M₁) →ₗ[R]
        symmetricPower R M₁ n :=
    { toFun := fun z => PiTensorProduct.lift (H (f z))
      map_add' := by
        intro x y
        change PiTensorProduct.lift (H (f (x + y))) =
          PiTensorProduct.lift (H (f x)) + PiTensorProduct.lift (H (f y))
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro v
        change (PiTensorProduct.lift (H (f (x + y))))
            (PiTensorProduct.tprod R v) =
          ((PiTensorProduct.lift (H (f x)) + PiTensorProduct.lift (H (f y)))
            (PiTensorProduct.tprod R v))
        rw [LinearMap.add_apply, PiTensorProduct.lift.tprod,
          PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
        change H (f (x + y)) v = H (f x) v + H (f y) v
        rw [f.map_add, H.map_add]
        simp
      map_smul' := by
        intro r x
        change PiTensorProduct.lift (H (f (r • x))) =
          r • PiTensorProduct.lift (H (f x))
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro v
        change (PiTensorProduct.lift (H (f (r • x))))
            (PiTensorProduct.tprod R v) =
          ((r • PiTensorProduct.lift (H (f x))) (PiTensorProduct.tprod R v))
        rw [LinearMap.smul_apply, PiTensorProduct.lift.tprod,
          PiTensorProduct.lift.tprod]
        change H (f (r • x)) v = r • H (f x) v
        rw [f.map_smul, H.map_smul]
        simp }
  let hC (z : M₂) :
      addConGen (SymmetricPower.Rel R (ULift.{uR} (Fin (n - 1))) M₁) ≤
        AddCon.ker (C z).toAddMonoidHom := by
    apply AddCon.addConGen_le.2
    intro x y hxy
    cases hxy with
    | perm e q =>
        change C z (PiTensorProduct.tprod R q) =
          C z (PiTensorProduct.tprod R (fun i => q (e i)))
        change (PiTensorProduct.lift (H (f z))) (PiTensorProduct.tprod R q) =
          (PiTensorProduct.lift (H (f z)))
            (PiTensorProduct.tprod R (fun i => q (e i)))
        rw [PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
        change H (f z) q = H (f z) (fun i => q (e i))
        simp [H, F]
        let e' : (ULift.{uR} (Fin 1) ⊕ ULift.{uR} (Fin (n - 1))) ≃
            (ULift.{uR} (Fin 1) ⊕ ULift.{uR} (Fin (n - 1))) :=
          Equiv.sumCongr (Equiv.refl _) e
        let p := σ.trans (e'.trans σ.symm)
        have hp := SymmetricPower.tprod_equiv (R := R) (M := M₁) p
          (fun i => Sum.elim (fun _ => f z) q (σ i))
        have hfun :
            (fun i => Sum.elim (fun _ => f z) q (σ (p i))) =
              (fun i => Sum.elim (fun _ => f z) (fun i => q (e i)) (σ i)) := by
          funext i
          cases hσ : σ i with
          | inl a => simp [p, e', Equiv.trans_apply, hσ]
          | inr b => simp [p, e', Equiv.trans_apply, hσ]
        simpa only [hfun] using hp.symm
  let B : M₂ →ₗ[R]
      symmetricPower R M₁ (n - 1) →ₗ[R] symmetricPower R M₁ n :=
    { toFun := fun z =>
        { toFun := AddCon.lift
            (addConGen (SymmetricPower.Rel R (ULift.{uR} (Fin (n - 1))) M₁))
            (C z).toAddMonoidHom (hC z)
          map_add' := by intro x y; exact map_add _ _ _
          map_smul' := by
            intro r x
            refine AddCon.induction_on x ?_
            intro t
            change C z (r • t) = r • C z t
            exact (C z).map_smul r t }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        refine AddCon.induction_on z ?_
        intro t
        change C (x + y) t = C x t + C y t
        simp [C]
      map_smul' := by
        intro r x
        apply LinearMap.ext
        intro z
        refine AddCon.induction_on z ?_
        intro t
        change C (r • x) t = r • C x t
        simp [C] }
  exact TensorProduct.lift B

/-- Exterior relation insertion is multiplication by the degree-one class
corresponding to `f z`, followed by the tensor-product universal map. -/
noncomputable def exteriorPowerRelationMap
    {R : Type uR} {M₂ : Type uM₂} {M₁ : Type uM₁} [CommRing R]
    [AddCommGroup M₂] [AddCommGroup M₁]
    [Module R M₂] [Module R M₁]
    (f : M₂ →ₗ[R] M₁) {n : ℕ} (hn : 0 < n) :
    TensorProduct R M₂ (exteriorPower R M₁ (n - 1)) →ₗ[R]
      exteriorPower R M₁ n := by
  let h₁ : 1 + (n - 1) = n := Nat.add_sub_of_le (Nat.succ_le_iff.2 hn)
  let leftMul : M₁ →ₗ[R]
      exteriorPower R M₁ (n - 1) →ₗ[R] exteriorPower R M₁ n :=
    { toFun := fun x =>
        let hx : exteriorPower R M₁ 1 := (exteriorPower.oneEquiv R M₁).symm x
        { toFun := fun y =>
            ⟨(hx : ExteriorAlgebra R M₁) * (y : ExteriorAlgebra R M₁), by
              simpa [h₁] using
                (SetLike.mul_mem_graded
                  (A := fun i : ℕ => exteriorPower R M₁ i)
                  hx.property y.property)⟩
          map_add' := by
            intro y z
            apply Subtype.ext
            simp [mul_add]
          map_smul' := by
            intro r y
            apply Subtype.ext
            change (hx : ExteriorAlgebra R M₁) * (r • (y : ExteriorAlgebra R M₁)) =
              r • ((hx : ExteriorAlgebra R M₁) * (y : ExteriorAlgebra R M₁))
            rw [Algebra.smul_def, Algebra.smul_def]
            calc
              (hx : ExteriorAlgebra R M₁) *
                    (algebraMap R (ExteriorAlgebra R M₁) r * (y : ExteriorAlgebra R M₁)) =
                  ((hx : ExteriorAlgebra R M₁) *
                    algebraMap R (ExteriorAlgebra R M₁) r) *
                    (y : ExteriorAlgebra R M₁) := (mul_assoc _ _ _).symm
              _ = (algebraMap R (ExteriorAlgebra R M₁) r *
                    (hx : ExteriorAlgebra R M₁)) *
                    (y : ExteriorAlgebra R M₁) := by rw [Algebra.commutes]
              _ = algebraMap R (ExteriorAlgebra R M₁) r *
                    ((hx : ExteriorAlgebra R M₁) * (y : ExteriorAlgebra R M₁)) :=
                mul_assoc _ _ _ }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        apply Subtype.ext
        simp [Algebra.smul_def, add_mul]
      map_smul' := by
        intro r x
        apply LinearMap.ext
        intro z
        apply Subtype.ext
        simp [Algebra.smul_def, mul_assoc] }
  exact TensorProduct.lift (leftMul.comp f)

/-- Focused image-equals-kernel interface for the symmetric presentation. -/
theorem symmetricPower_relation_range_eq_kernel
    {R M₂ M₁ M : Type*} [CommRing R]
    [AddCommGroup M₂] [AddCommGroup M₁] [AddCommGroup M]
    [Module R M₂] [Module R M₁] [Module R M]
    (f : M₂ →ₗ[R] M₁) (g : M₁ →ₗ[R] M)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {n : ℕ} (hn : 0 < n) :
    LinearMap.range (symmetricPowerRelationMap f hn) =
      LinearMap.ker (symmetricPowerQuotientMap n g) := by
  sorry

/-- Focused image-equals-kernel interface for the exterior presentation. -/
theorem exteriorPower_relation_range_eq_kernel
    {R M₂ M₁ M : Type*} [CommRing R]
    [AddCommGroup M₂] [AddCommGroup M₁] [AddCommGroup M]
    [Module R M₂] [Module R M₁] [Module R M]
    (f : M₂ →ₗ[R] M₁) (g : M₁ →ₗ[R] M)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {n : ℕ} (hn : 0 < n) :
    LinearMap.range (exteriorPowerRelationMap f hn) =
      LinearMap.ker (exteriorPowerQuotientMap n g) := by
  sorry

/-- The right-exact sequences for symmetric and exterior powers of a quotient. -/
theorem presentation_symmetric_exterior_power
    {R M₂ M₁ M : Type*} [CommRing R]
    [AddCommGroup M₂] [AddCommGroup M₁] [AddCommGroup M]
    [Module R M₂] [Module R M₁] [Module R M]
    (f : M₂ →ₗ[R] M₁) (g : M₁ →ₗ[R] M)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {n : ℕ} (hn : 0 < n) :
    (∃ a : TensorProduct R M₂ (symmetricPower R M₁ (n - 1)) →ₗ[R]
        symmetricPower R M₁ n,
      ∃ b : symmetricPower R M₁ n →ₗ[R] symmetricPower R M n,
        Function.Exact a b ∧ Function.Surjective b ∧
          (∀ x,
            b (SymmetricPower.tprod R x) =
              SymmetricPower.tprod R (fun i => g (x i)))) ∧
    (∃ a : TensorProduct R M₂ (exteriorPower R M₁ (n - 1)) →ₗ[R]
        exteriorPower R M₁ n,
      ∃ b : exteriorPower R M₁ n →ₗ[R] exteriorPower R M n,
        Function.Exact a b ∧ Function.Surjective b ∧
          (∀ x,
            b (exteriorPower.ιMulti R n x) =
              exteriorPower.ιMulti R n (fun i => g (x i)))) := by
  constructor
  · refine ⟨symmetricPowerRelationMap f hn, symmetricPowerQuotientMap n g, ?_, ?_, ?_⟩
    · rw [LinearMap.exact_iff]
      exact (symmetricPower_relation_range_eq_kernel f g hfg hg hn).symm
    · rw [← LinearMap.range_eq_top]
      apply top_unique
      rw [← symmetric_pure_tensor_span n]
      apply Submodule.span_le.2
      rintro _ ⟨x, rfl⟩
      choose y hy using fun i : ULift (Fin n) => hg (x i)
      refine ⟨SymmetricPower.tprod R y, ?_⟩
      rw [symmetricPowerQuotientMap_tprod]
      congr
      funext i
      exact hy i
    · intro x
      exact symmetricPowerQuotientMap_tprod n g x
  · refine ⟨exteriorPowerRelationMap f hn, exteriorPowerQuotientMap n g, ?_, ?_, ?_⟩
    · rw [LinearMap.exact_iff]
      exact (exteriorPower_relation_range_eq_kernel f g hfg hg hn).symm
    · rw [← LinearMap.range_eq_top]
      apply top_unique
      rw [← exterior_pure_tensor_span n]
      apply Submodule.span_le.2
      rintro _ ⟨x, rfl⟩
      choose y hy using fun i : Fin n => hg (x i)
      refine ⟨exteriorPower.ιMulti R n y, ?_⟩
      rw [exteriorPowerQuotientMap_ιMulti]
      congr
      funext i
      exact hy i
    · intro x
      exact exteriorPowerQuotientMap_ιMulti n g x
/-
  classical
  let C : (⨂[R] _ : ULift.{_} (Fin n), M₁) →ₗ[R] symmetricPower R M n :=
    (SymmetricPower.mk R (ULift.{_} (Fin n)) M).comp
      (PiTensorProduct.map (fun _ : ULift.{_} (Fin n) => g))
  have hC : addConGen (SymmetricPower.Rel R (ULift.{_} (Fin n)) M₁) ≤
      AddCon.ker C.toAddMonoidHom := by
    apply AddCon.addConGen_le.2
    intro x y hxy
    cases hxy with
    | perm e f =>
        change C (PiTensorProduct.tprod R f) =
          C (PiTensorProduct.tprod R (fun i => f (e i)))
        dsimp [C]
        rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
        exact (SymmetricPower.tprod_equiv (R := R) (M := M) e
          (fun i => g (f i))).symm
  let bₛ : symmetricPower R M₁ n →ₗ[R] symmetricPower R M n :=
    { toFun := AddCon.lift (addConGen (SymmetricPower.Rel R (ULift.{_} (Fin n)) M₁))
        C.toAddMonoidHom hC
      map_add' := by intro x y; exact map_add _ _ _
      map_smul' := by
        intro r x
        refine AddCon.induction_on x ?_
        intro t
        change C (r • t) = r • C t
        exact C.map_smul r t }
  have hbₛ_tprod (x : ULift (Fin n) → M₁) :
      bₛ (SymmetricPower.tprod R x) =
        SymmetricPower.tprod R (fun i => g (x i)) := by
    change AddCon.lift (addConGen (SymmetricPower.Rel R (ULift.{_} (Fin n)) M₁))
      C.toAddMonoidHom hC (↑(PiTensorProduct.tprod R x)) = _
    rw [AddCon.lift_coe]
    change C (PiTensorProduct.tprod R x) = _
    simp only [C, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      SymmetricPower.mk, SymmetricPower.tprod]
    rfl
  have hbₛ_surj : Function.Surjective bₛ := by
    rw [← LinearMap.range_eq_top]
    apply top_unique
    rw [← symmetric_pure_tensor_span n]
    apply Submodule.span_le.2
    rintro _ ⟨x, rfl⟩
    choose y hy using fun i : ULift (Fin n) => hg (x i)
    refine ⟨SymmetricPower.tprod R y, ?_⟩
    rw [hbₛ_tprod]
    congr 1
    funext i
    exact hy i
  have h₁ : 1 + (n - 1) = n := Nat.add_sub_of_le (Nat.succ_le_iff.2 hn)
  let σₛ : ULift.{_} (Fin n) ≃
      ULift.{_} (Fin 1) ⊕ ULift.{_} (Fin (n - 1)) :=
    ((Equiv.ulift : ULift.{_} (Fin n) ≃ Fin n).trans (finCongr h₁.symm)).trans
      (finSumFinEquiv.symm.trans
        (Equiv.sumCongr (Equiv.ulift.symm) (Equiv.ulift.symm)))
  let Fₛ : MultilinearMap R
      (fun _ : ULift.{_} (Fin 1) ⊕ ULift.{_} (Fin (n - 1)) => M₁)
      (symmetricPower R M₁ n) :=
    (SymmetricPower.tprod R).domDomCongr σₛ
  let Hₛ : M₁ →ₗ[R]
      MultilinearMap R (fun _ : ULift.{_} (Fin (n - 1)) => M₁)
        (symmetricPower R M₁ n) :=
    (MultilinearMap.ofSubsingletonₗ R R M₁
      (MultilinearMap R (fun _ : ULift.{_} (Fin (n - 1)) => M₁)
        (symmetricPower R M₁ n)) (ULift.up 0)).symm Fₛ.currySum
  let Aₛ : M₂ →ₗ[R]
      (symmetricPower R M₁ (n - 1) →ₗ[R] symmetricPower R M₁ n) :=
    { toFun := fun z =>
        { toFun := PiTensorProduct.lift (Hₛ (f z))
          map_add' := by
            intro x y
            apply PiTensorProduct.ext
            apply MultilinearMap.ext
            intro v
            simp [Hₛ]
          map_smul' := by
            intro r x
            apply PiTensorProduct.ext
            apply MultilinearMap.ext
            intro v
            simp [Hₛ] }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro v
        simp [Hₛ]
      map_smul' := by
        intro r x
        apply LinearMap.ext
        intro z
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro v
        simp [Hₛ] }
  let aₛ : TensorProduct R M₂ (symmetricPower R M₁ (n - 1)) →ₗ[R]
      symmetricPower R M₁ n := TensorProduct.lift Aₛ
  refine ?_ 

/-- Indices for the two distinguished slots in the generator-and-relation presentation. -/
 -/
def positionPairs (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The direct-sum domain of the exterior relation presentation. -/
abbrev exteriorRelationDomain (R M I : Type*) (n : ℕ)
    [CommRing R] [AddCommGroup M] [Module R M] :=
    (⨁ _q : positionPairs n × I × I, tensorPower R M (n - 2)) ×
      (⨁ _q : positionPairs n × I, tensorPower R M (n - 2))

/-- The direct-sum domain of the symmetric relation presentation. -/
abbrev symmetricRelationDomain (R M I : Type*) (n : ℕ)
    [CommRing R] [AddCommGroup M] [Module R M] :=
    ⨁ _q : positionPairs n × I × I, tensorPower R M (n - 2)

/-
/-
/-- The canonical tensor-to-exterior-power map after restricting scalars. -/
noncomputable def wedgeTensorPowerMap
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] (n : ℕ) :
    letI : Module B (RestrictScalars A B M) := RestrictScalars.moduleOrig A B M
    letI : Module A (RestrictScalars A B M) :=
      RestrictScalars.module (R := A) (S := B) (M := M)
    letI : Module A (exteriorPower B M n) :=
      Module.restrictScalars A B (exteriorPower B M n)
    letI : ∀ i : Fin n, AddCommMonoid (RestrictScalars A B M) := fun _ => inferInstance
    letI : ∀ i : Fin n, Module A (RestrictScalars A B M) :=
      fun _ => RestrictScalars.module (R := A) (S := B) (M := M)
    letI : AddCommMonoid (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) :=
      PiTensorProduct.instAddCommMonoid (fun _ : Fin n => RestrictScalars A B M)
    letI : Module A (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) :=
      @PiTensorProduct.instModule (Fin n) A inferInstance
        (fun _ : Fin n => RestrictScalars A B M) (fun _ => inferInstance) (fun _ => inferInstance)
    @tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M) →ₗ[A]
      exteriorPower B M n := by
  letI : Module B (RestrictScalars A B M) := RestrictScalars.moduleOrig A B M
  letI : Module A (RestrictScalars A B M) :=
    RestrictScalars.module (R := A) (S := B) (M := M)
  letI : Module A M := Module.restrictScalars A B M
  letI : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
  letI : Module A (exteriorPower B M n) :=
    Module.restrictScalars A B (exteriorPower B M n)
  letI : Module B (exteriorPower B M n) := inferInstance
  letI : MulAction B (exteriorPower B M n) := inferInstance
  letI : IsScalarTower A B (exteriorPower B M n) :=
    IsScalarTower.restrictScalars A B (exteriorPower B M n)
  letI : ∀ i : Fin n, Module B M := fun _ => inferInstance
  letI : ∀ i : Fin n, Module A M := fun _ => Module.restrictScalars A B M
  letI : ∀ i : Fin n, IsScalarTower A B M :=
    fun _ => IsScalarTower.restrictScalars A B M
  letI : ∀ i : Fin n, Module B (RestrictScalars A B M) :=
    fun _ => RestrictScalars.moduleOrig A B M
  letI : ∀ i : Fin n, AddCommMonoid (RestrictScalars A B M) := fun _ => inferInstance
  letI : ∀ i : Fin n, AddCommGroup (RestrictScalars A B M) := fun _ => inferInstance
  letI : ∀ i : Fin n, Module A (RestrictScalars A B M) :=
    fun _ => RestrictScalars.module (R := A) (S := B) (M := M)
  letI : AddCommMonoid (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
    (RestrictScalars.module A B M)) :=
    PiTensorProduct.instAddCommMonoid (fun _ : Fin n => RestrictScalars A B M)
  letI : Module A (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
    (RestrictScalars.module A B M)) :=
    @PiTensorProduct.instModule (Fin n) A inferInstance
      (fun _ : Fin n => RestrictScalars A B M) (fun _ => inferInstance) (fun _ => inferInstance)
  letI : ∀ i : Fin n, IsScalarTower A B (RestrictScalars A B M) :=
    fun _ => inferInstance
  exact PiTensorProduct.lift
    ((exteriorPower.ιMulti B n).toMultilinearMap.restrictScalars (R := A) (A := B))

@[simp]
theorem wedgeTensorPowerMap_tprod
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] (n : ℕ) (x : Fin n → M) :
    letI : Module B (RestrictScalars A B M) := RestrictScalars.moduleOrig A B M
    letI : Module A (RestrictScalars A B M) :=
      RestrictScalars.module (R := A) (S := B) (M := M)
    letI : Module A (exteriorPower B M n) :=
      Module.restrictScalars A B (exteriorPower B M n)
    letI : IsScalarTower A B (exteriorPower B M n) :=
      IsScalarTower.restrictScalars A B (exteriorPower B M n)
    letI : ∀ i : Fin n, Module B (RestrictScalars A B M) :=
      fun _ => RestrictScalars.moduleOrig A B M
    letI : ∀ i : Fin n, AddCommMonoid (RestrictScalars A B M) := fun _ => inferInstance
    letI : ∀ i : Fin n, Module A (RestrictScalars A B M) :=
      fun _ => RestrictScalars.module (R := A) (S := B) (M := M)
    letI : AddCommMonoid (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) :=
      PiTensorProduct.instAddCommMonoid (fun _ : Fin n => RestrictScalars A B M)
    letI : Module A (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) :=
      @PiTensorProduct.instModule (Fin n) A inferInstance
        (fun _ : Fin n => RestrictScalars A B M) (fun _ => inferInstance) (fun _ => inferInstance)
    wedgeTensorPowerMap (A := A) (B := B) (M := M) n
        (PiTensorProduct.tprod A (fun i => (x i : RestrictScalars A B M))) =
      (exteriorPower.ιMulti B n) x := by
  exact
    letI : Module B (RestrictScalars A B M) := RestrictScalars.moduleOrig A B M
    letI : Module A (RestrictScalars A B M) :=
      RestrictScalars.module (R := A) (S := B) (M := M)
    letI : Module A (exteriorPower B M n) :=
      Module.restrictScalars A B (exteriorPower B M n)
    letI : IsScalarTower A B (exteriorPower B M n) :=
      IsScalarTower.restrictScalars A B (exteriorPower B M n)
    letI : ∀ i : Fin n, Module B (RestrictScalars A B M) :=
      fun _ => RestrictScalars.moduleOrig A B M
    letI : ∀ i : Fin n, AddCommMonoid (RestrictScalars A B M) := fun _ => inferInstance
    letI : ∀ i : Fin n, Module A (RestrictScalars A B M) :=
      fun _ => RestrictScalars.module (R := A) (S := B) (M := M)
    letI : AddCommMonoid (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) :=
      PiTensorProduct.instAddCommMonoid (fun _ : Fin n => RestrictScalars A B M)
    letI : Module A (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) :=
      @PiTensorProduct.instModule (Fin n) A inferInstance
        (fun _ : Fin n => RestrictScalars A B M) (fun _ => inferInstance) (fun _ => inferInstance)
    letI : ∀ i : Fin n, IsScalarTower A B (RestrictScalars A B M) :=
      fun _ => inferInstance
    PiTensorProduct.lift.tprod _

-/

/-- The generators used in the kernel presentation of the exterior power. -/
def wedgeKernelGenerators
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] (n : ℕ) :
    letI : Module B (RestrictScalars A B M) := RestrictScalars.moduleOrig A B M
    letI : Module A (RestrictScalars A B M) :=
      RestrictScalars.module (R := A) (S := B) (M := M)
    letI : ∀ i : Fin n, AddCommMonoid (RestrictScalars A B M) := fun _ => inferInstance
    letI : ∀ i : Fin n, Module A (RestrictScalars A B M) :=
      fun _ => RestrictScalars.module (R := A) (S := B) (M := M)
    letI : AddCommMonoid (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) :=
      PiTensorProduct.instAddCommMonoid (fun _ : Fin n => RestrictScalars A B M)
    letI : Module A (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) :=
      @PiTensorProduct.instModule (Fin n) A inferInstance
        (fun _ : Fin n => RestrictScalars A B M) (fun _ => inferInstance) (fun _ => inferInstance)
    Set (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) := by
  letI : Module B (RestrictScalars A B M) := RestrictScalars.moduleOrig A B M
  letI : Module A (RestrictScalars A B M) :=
    RestrictScalars.module (R := A) (S := B) (M := M)
  letI : ∀ i : Fin n, AddCommMonoid (RestrictScalars A B M) := fun _ => inferInstance
  letI : ∀ i : Fin n, AddCommGroup (RestrictScalars A B M) := fun _ => inferInstance
  letI : ∀ i : Fin n, Module A (RestrictScalars A B M) :=
    fun _ => RestrictScalars.module (R := A) (S := B) (M := M)
  letI : AddCommMonoid (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
    (RestrictScalars.module A B M)) :=
    PiTensorProduct.instAddCommMonoid (fun _ : Fin n => RestrictScalars A B M)
  letI : Module A (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
    (RestrictScalars.module A B M)) :=
    @PiTensorProduct.instModule (Fin n) A inferInstance
      (fun _ : Fin n => RestrictScalars A B M) (fun _ => inferInstance) (fun _ => inferInstance)
  exact {z | ∃ (x : Fin n → RestrictScalars A B M) (i j : Fin n), i ≠ j ∧ x i = x j ∧
      z = PiTensorProduct.tprod A x} ∪
    {z | ∃ (x : Fin n → RestrictScalars A B M) (i j : Fin n) (b : B), i ≠ j ∧
      z = PiTensorProduct.tprod A (Function.update x i (b • x i)) -
        PiTensorProduct.tprod A (Function.update x j (b • x j))}

/-- The kernel of the tensor-to-exterior-power map is generated by alternating and scalar-moving
relations. -/
theorem wedgeTensorPowerMap_ker_span
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] (n : ℕ) (hn : 1 < n) :
    letI : Module B (RestrictScalars A B M) := RestrictScalars.moduleOrig A B M
    letI : Module A (RestrictScalars A B M) :=
      RestrictScalars.module (R := A) (S := B) (M := M)
    letI : Module A (exteriorPower B M n) :=
      Module.restrictScalars A B (exteriorPower B M n)
    letI : IsScalarTower A B (exteriorPower B M n) :=
      IsScalarTower.restrictScalars A B (exteriorPower B M n)
    letI : ∀ i : Fin n, Module B (RestrictScalars A B M) :=
      fun _ => RestrictScalars.moduleOrig A B M
    letI : ∀ i : Fin n, AddCommMonoid (RestrictScalars A B M) := fun _ => inferInstance
    letI : ∀ i : Fin n, Module A (RestrictScalars A B M) :=
      fun _ => RestrictScalars.module (R := A) (S := B) (M := M)
    letI : AddCommMonoid (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) :=
      PiTensorProduct.instAddCommMonoid (fun _ : Fin n => RestrictScalars A B M)
    letI : Module A (@tensorPower A (RestrictScalars A B M) n inferInstance inferInstance
      (RestrictScalars.module A B M)) :=
      @PiTensorProduct.instModule (Fin n) A inferInstance
        (fun _ : Fin n => RestrictScalars A B M) (fun _ => inferInstance) (fun _ => inferInstance)
    LinearMap.ker (wedgeTensorPowerMap (A := A) (B := B) (M := M) n) =
      Submodule.span A (wedgeKernelGenerators (A := A) (B := B) (M := M) n) := by
  sorry

-/

/-
/-- The canonical tensor-to-exterior-power map after restricting scalars. -/
noncomputable def wedgeTensorPowerMap
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] (n : ℕ) :
    letI : Module A (exteriorPower B M n) :=
      Module.restrictScalars A B (exteriorPower B M n)
    tensorPower A M n →ₗ[A] exteriorPower B M n := by
  letI : Module A (exteriorPower B M n) :=
    Module.restrictScalars A B (exteriorPower B M n)
  letI : ∀ i : Fin n, AddCommMonoid M := fun _ => inferInstance
  letI : ∀ i : Fin n, Module A M := fun _ => inferInstance
  letI : ∀ i : Fin n, Module B M := fun _ => inferInstance
  letI : ∀ i : Fin n, IsScalarTower A B M := fun _ => inferInstance
  letI : IsScalarTower A B (exteriorPower B M n) :=
    ⟨fun r s x => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  exact PiTensorProduct.lift
    ((exteriorPower.ιMulti B n).toMultilinearMap.restrictScalars (R := A) (A := B))

@[simp]
theorem wedgeTensorPowerMap_tprod
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (n : ℕ) (x : Fin n → M) :
    letI : Module A (exteriorPower B M n) :=
      Module.restrictScalars A B (exteriorPower B M n)
    wedgeTensorPowerMap (A := A) (B := B) (M := M) n
        (PiTensorProduct.tprod A x) =
      (exteriorPower.ιMulti B n) x := by
  exact
    letI : Module A (exteriorPower B M n) :=
      Module.restrictScalars A B (exteriorPower B M n)
    PiTensorProduct.lift.tprod _

/-- The generators used in the kernel presentation of the exterior power. -/
def wedgeKernelGenerators
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] (n : ℕ) :
    Set (tensorPower A M n) := by
  letI : ∀ i : Fin n, AddCommGroup M := fun _ => inferInstance
  letI : ∀ i : Fin n, Module A M := fun _ => inferInstance
  exact {z | ∃ (x : Fin n → M) (i j : Fin n), i ≠ j ∧ x i = x j ∧
      z = PiTensorProduct.tprod A x} ∪
    {z | ∃ (x : Fin n → M) (i j : Fin n) (b : B), i ≠ j ∧
      z = PiTensorProduct.tprod A (Function.update x i (b • x i)) -
        PiTensorProduct.tprod A (Function.update x j (b • x j))}

/-- The kernel of the tensor-to-exterior-power map is generated by alternating and scalar-moving
relations. -/
theorem wedgeTensorPowerMap_ker_span
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (n : ℕ) (hn : 1 < n) :
    letI : Module A (exteriorPower B M n) :=
      Module.restrictScalars A B (exteriorPower B M n)
    LinearMap.ker (wedgeTensorPowerMap (A := A) (B := B) (M := M) n) =
      Submodule.span A (wedgeKernelGenerators (A := A) (B := B) (M := M) n) := by
  sorry

-/

/-! ## Colimits -/

/-- The algebra map induced by a linear map of modules. -/
def tensorAlgebraMap
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    tensorAlgebra R M →ₐ[R] tensorAlgebra R N :=
  TensorAlgebra.lift R ((TensorAlgebra.ι R).comp f)

/-- The exterior-algebra map induced by a linear map of modules. -/
def exteriorAlgebraMap
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    exteriorAlgebra R M →ₐ[R] exteriorAlgebra R N :=
  ExteriorAlgebra.map f

/-- The symmetric-algebra map induced by a linear map of modules. -/
def symmetricAlgebraMap
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    symmetricAlgebra R M →ₐ[R] symmetricAlgebra R N :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f)

theorem tensorAlgebraMap_id
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    tensorAlgebraMap (LinearMap.id : M →ₗ[R] M) =
      AlgHom.id R (tensorAlgebra R M) := by
  apply TensorAlgebra.hom_ext
  simp [tensorAlgebraMap]

theorem tensorAlgebraMap_comp
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    tensorAlgebraMap (g.comp f) =
      (tensorAlgebraMap g).comp (tensorAlgebraMap f) := by
  apply TensorAlgebra.hom_ext
  simp only [tensorAlgebraMap, AlgHom.comp_toLinearMap]
  conv_rhs =>
    rw [LinearMap.comp_assoc, TensorAlgebra.ι_comp_lift, ← LinearMap.comp_assoc,
      TensorAlgebra.ι_comp_lift]
  rw [TensorAlgebra.ι_comp_lift]
  rw [← LinearMap.comp_assoc]

theorem exteriorAlgebraMap_id
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    exteriorAlgebraMap (LinearMap.id : M →ₗ[R] M) =
      AlgHom.id R (exteriorAlgebra R M) := by
  exact ExteriorAlgebra.map_id

theorem exteriorAlgebraMap_comp
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    exteriorAlgebraMap (g.comp f) =
      (exteriorAlgebraMap g).comp (exteriorAlgebraMap f) := by
  exact (ExteriorAlgebra.map_comp_map f g).symm

theorem symmetricAlgebraMap_id
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    symmetricAlgebraMap (LinearMap.id : M →ₗ[R] M) =
      AlgHom.id R (symmetricAlgebra R M) := by
  apply SymmetricAlgebra.algHom_ext
  simp [symmetricAlgebraMap]

theorem symmetricAlgebraMap_comp
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    symmetricAlgebraMap (g.comp f) =
      (symmetricAlgebraMap g).comp (symmetricAlgebraMap f) := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  simp [symmetricAlgebraMap]

/-- Tensor algebras as a functor on the category of `R`-modules. -/
def tensorAlgebraFunctor (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (tensorAlgebra R M)
  map f := ModuleCat.ofHom (tensorAlgebraMap f.hom).toLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    simpa using congrArg (fun h => h.toLinearMap)
      (tensorAlgebraMap_id (R := R) (M := X))
  map_comp f g := by
    apply ModuleCat.hom_ext
    simpa using congrArg (fun h => h.toLinearMap)
      (tensorAlgebraMap_comp f.hom g.hom)

/-- Exterior algebras as a functor on the category of `R`-modules. -/
def exteriorAlgebraFunctor (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (exteriorAlgebra R M)
  map f := ModuleCat.ofHom (exteriorAlgebraMap f.hom).toLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    simpa using congrArg (fun h => h.toLinearMap)
      (exteriorAlgebraMap_id (R := R) (M := X))
  map_comp f g := by
    apply ModuleCat.hom_ext
    simpa using congrArg (fun h => h.toLinearMap)
      (exteriorAlgebraMap_comp f.hom g.hom)

/-- Symmetric algebras as a functor on the category of `R`-modules. -/
def symmetricAlgebraFunctor (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (symmetricAlgebra R M)
  map f := ModuleCat.ofHom (symmetricAlgebraMap f.hom).toLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    simpa using congrArg (fun h => h.toLinearMap)
      (symmetricAlgebraMap_id (R := R) (M := X))
  map_comp f g := by
    apply ModuleCat.hom_ext
    simpa using congrArg (fun h => h.toLinearMap)
      (symmetricAlgebraMap_comp f.hom g.hom)

/-- Tensor, exterior, and symmetric algebras commute with filtered colimits. -/
theorem algebra_colimit_iso
    {R : Type u} [CommRing R] {I : Type u} [Preorder I] [IsFiltered I]
    (M : I ⥤ ModuleCat.{u} R) :
    Nonempty (colimit (M ⋙ tensorAlgebraFunctor R) ≅
        (tensorAlgebraFunctor R).obj (colimit M)) ∧
      Nonempty (colimit (M ⋙ exteriorAlgebraFunctor R) ≅
        (exteriorAlgebraFunctor R).obj (colimit M)) ∧
      Nonempty (colimit (M ⋙ symmetricAlgebraFunctor R) ≅
        (symmetricAlgebraFunctor R).obj (colimit M)) := by
  let : PreservesFilteredColimits (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) :=
    { preserves_filtered_colimits := fun J =>
        { preservesColimit := fun {F} =>
            { preserves := fun {c} hc =>
                ⟨by
                  apply isColimitOfReflects (forget₂ (ModuleCat R) AddCommGrpCat)
                  change IsColimit
                    ((forget₂ (AlgCat R) RingCat ⋙
                      forget₂ RingCat AddCommGrpCat).mapCocone c)
                  exact isColimitOfPreserves
                    (forget₂ (AlgCat R) RingCat ⋙ forget₂ RingCat AddCommGrpCat) hc⟩ } } }
  let : PreservesColimitsOfSize (AlgCat.tensorAlgebra R) :=
    (AlgCat.tensorAlgebraAdj R).leftAdjoint_preservesColimits
  constructor
  · exact ⟨(preservesColimitIso
      (AlgCat.tensorAlgebra R ⋙ forget₂ (AlgCat R) (ModuleCat R)) M).symm⟩
  · constructor
    · let exteriorAlgCat : ModuleCat.{u} R ⥤ AlgCat.{u} R :=
        { obj := fun X => AlgCat.of R (exteriorAlgebra R X)
          map := fun f => AlgCat.ofHom (exteriorAlgebraMap f.hom)
          map_id := fun X => by
            apply AlgCat.hom_ext
            simpa using (exteriorAlgebraMap_id (R := R) (M := (X : Type u)))
          map_comp := fun f g => by
            apply AlgCat.hom_ext
            simpa using (exteriorAlgebraMap_comp f.hom g.hom) }
      let A := M ⋙ exteriorAlgCat
      let C : AlgCat.{u} R := colimit A
      let moduleHomOfLinear {X Y : ModuleCat R} (f : X →ₗ[R] Y) : X ⟶ Y :=
        ModuleCat.homMk (AddCommGrpCat.ofHom f.toAddMonoidHom) (by
          intro r
          ext x
          simp [ModuleCat.smul])
      let genCocone : Cocone M :=
        { pt := (forget₂ (AlgCat R) (ModuleCat R)).obj C
          ι :=
            { app := fun i => moduleHomOfLinear
                ((colimit.ι A i).hom.toLinearMap.comp (ExteriorAlgebra.ι R))
              naturality := fun i j f => by
                apply ModuleCat.hom_ext
                dsimp [moduleHomOfLinear]
                change (colimit.ι A j).hom.toLinearMap.comp
                    ((ExteriorAlgebra.ι R).comp (M.map f).hom) =
                  (colimit.ι A i).hom.toLinearMap.comp (ExteriorAlgebra.ι R)
                have hnat := (colimit.cocone A).w f
                have hnat' := congrArg (fun k => k.hom.toLinearMap) hnat
                dsimp [A, exteriorAlgCat] at hnat'
                change
                  ((colimit.ι A j).hom.comp (ExteriorAlgebra.map (M.map f).hom)).toLinearMap =
                    (colimit.ι A i).hom.toLinearMap at hnat'
                have hnat'' := congrArg (fun k => k.comp (ExteriorAlgebra.ι R)) hnat'
                rw [AlgHom.comp_toLinearMap, LinearMap.comp_assoc,
                  ExteriorAlgebra.map_comp_ι] at hnat''
                simpa [A, exteriorAlgCat, exteriorAlgebraMap,
                  LinearMap.comp_assoc] using hnat'' } }
      let h : colimit M ⟶ (forget₂ (AlgCat R) (ModuleCat R)).obj C :=
        colimit.desc M genCocone
      let hC : ((colimit M : ModuleCat R) : Type u) →ₗ[R] (C : Type u) := h.hom
      have hsq : ∀ x : ((colimit M : ModuleCat.{u} R) : Type u),
          hC x * hC x = 0 := by
        intro x
        obtain ⟨i, m, hm⟩ :=
          Types.jointly_surjective_of_isColimit
            (isColimitOfPreserves (forget (ModuleCat R)) (colimit.isColimit M)) x
        rw [← hm]
        simp [h, hC, genCocone, moduleHomOfLinear]
        change (colimit.ι A i).hom (ExteriorAlgebra.ι R m) *
          (colimit.ι A i).hom (ExteriorAlgebra.ι R m) = 0
        calc
          _ = (colimit.ι A i).hom
              (ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R m) :=
            ((colimit.ι A i).hom.map_mul _ _).symm
          _ = (colimit.ι A i).hom 0 := by rw [ExteriorAlgebra.ι_sq_zero]
          _ = 0 := map_zero _
      let g : exteriorAlgebra R ((colimit M : ModuleCat R) : Type u) →ₐ[R] C :=
        ExteriorAlgebra.lift R ⟨hC, hsq⟩
      let targetCocone := exteriorAlgCat.mapCocone (colimit.cocone M)
      let f : colimit A ⟶ targetCocone.pt := colimit.desc A targetCocone
      have hgen' :
          moduleHomOfLinear (f.hom.toLinearMap.comp h.hom) =
            moduleHomOfLinear
              (X := colimit M)
              (Y := (forget₂ (AlgCat R) (ModuleCat R)).obj targetCocone.pt)
              (ExteriorAlgebra.ι R :
                ((colimit M : ModuleCat R) : Type u) →ₗ[R] (targetCocone.pt : Type u)) := by
        apply colimit.hom_ext
        intro i
        have hcomp :
            moduleHomOfLinear (f.hom.toLinearMap.comp h.hom) =
              h ≫ (forget₂ (AlgCat R) (ModuleCat R)).map f := by
          apply ModuleCat.hom_ext
          rfl
        rw [hcomp, ← Category.assoc, colimit.ι_desc]
        have hf := colimit.ι_desc targetCocone i
        have hfi :
            moduleHomOfLinear
                ((colimit.ι A i).hom.toLinearMap.comp (ExteriorAlgebra.ι R)) ≫
              (forget₂ (AlgCat R) (ModuleCat R)).map f =
              moduleHomOfLinear
                ((targetCocone.ι.app i).hom.toLinearMap.comp (ExteriorAlgebra.ι R)) := by
          apply ModuleCat.hom_ext
          change (f.hom.toLinearMap.comp
              ((colimit.ι A i).hom.toLinearMap.comp (ExteriorAlgebra.ι R))) =
            (targetCocone.ι.app i).hom.toLinearMap.comp (ExteriorAlgebra.ι R)
          have hfc := congrArg (fun k => k.hom.toLinearMap) hf
          change
            ((f.hom.comp (colimit.ι A i).hom).toLinearMap) =
              (targetCocone.ι.app i).hom.toLinearMap at hfc
          rw [AlgHom.comp_toLinearMap] at hfc
          have hfc' := congrArg (fun k => k.comp (ExteriorAlgebra.ι R)) hfc
          simpa [LinearMap.comp_assoc] using hfc'
        rw [hfi]
        apply ModuleCat.hom_ext
        change (targetCocone.ι.app i).hom.toLinearMap.comp (ExteriorAlgebra.ι R) =
          (ExteriorAlgebra.ι R).comp (colimit.ι M i).hom
        simp [targetCocone, exteriorAlgCat, exteriorAlgebraMap,
          ExteriorAlgebra.map_comp_ι]
      have hgen : f.hom.toLinearMap.comp h.hom = ExteriorAlgebra.ι R :=
        congrArg ModuleCat.Hom.hom hgen'
      have h₁ : f.hom.comp g =
          AlgHom.id R (exteriorAlgebra R ((colimit M : ModuleCat R) : Type u)) := by
        apply ExteriorAlgebra.hom_ext
        simpa [g, LinearMap.comp_assoc] using hgen
      have h₂ : g.comp f.hom = AlgHom.id R C := by
        have h₂' :
            (AlgCat.ofHom (g.comp f.hom) : C ⟶ C) =
              AlgCat.ofHom (AlgHom.id R C) := by
          apply colimit.hom_ext
          intro i
          apply AlgCat.hom_ext
          apply ExteriorAlgebra.hom_ext
          ext m
          change g (f.hom ((colimit.ι A i).hom (ExteriorAlgebra.ι R m))) =
            (colimit.ι A i).hom (ExteriorAlgebra.ι R m)
          have hf := colimit.ι_desc targetCocone i
          have hf' := congrArg (fun k => k.hom) hf
          dsimp [A] at hf'
          change f.hom.comp (colimit.ι A i).hom = (targetCocone.ι.app i).hom at hf'
          have hf_m := congrArg (fun k => k (ExteriorAlgebra.ι R m)) hf'
          change g ((f.hom.comp (colimit.ι A i).hom) (ExteriorAlgebra.ι R m)) =
            (colimit.ι A i).hom (ExteriorAlgebra.ι R m)
          rw [hf_m]
          simp [g, targetCocone, exteriorAlgCat, exteriorAlgebraMap]
          have hi := colimit.ι_desc genCocone i
          have hi' := congrArg (fun k => k.hom) hi
          change h.hom.comp (colimit.ι M i).hom = (genCocone.ι.app i).hom at hi'
          have hi_m := congrArg (fun k => k m) hi'
          have hi_m' := hi_m
          change hC ((colimit.ι M i).hom m) =
            (colimit.ι A i).hom (ExteriorAlgebra.ι R m) at hi_m'
          rw [ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.lift_ι_apply]
          exact hi_m'
        exact congrArg AlgCat.Hom.hom h₂'
      let eAlg : C ≃ₐ[R] exteriorAlgebra R ((colimit M : ModuleCat R) : Type u) :=
        AlgEquiv.ofAlgHom f.hom g h₁ h₂
      exact ⟨(preservesColimitIso
          (forget₂ (AlgCat R) (ModuleCat R)) A).symm ≪≫ eAlg.toLinearEquiv.toModuleIso⟩
    · let symmetricAlgCat : ModuleCat.{u} R ⥤ AlgCat.{u} R :=
        { obj := fun X => AlgCat.of R (symmetricAlgebra R X)
          map := fun f => AlgCat.ofHom (symmetricAlgebraMap f.hom)
          map_id := fun X => by
            apply AlgCat.hom_ext
            simpa using (symmetricAlgebraMap_id (R := R) (M := (X : Type u)))
          map_comp := fun f g => by
            apply AlgCat.hom_ext
            simpa using (symmetricAlgebraMap_comp f.hom g.hom) }
      let A := M ⋙ symmetricAlgCat
      let C : AlgCat.{u} R := colimit A
      let moduleHomOfLinear {X Y : ModuleCat R} (f : X →ₗ[R] Y) : X ⟶ Y :=
        ModuleCat.homMk (AddCommGrpCat.ofHom f.toAddMonoidHom) (by
          intro r
          ext x
          simp [ModuleCat.smul])
      let genCocone : Cocone M :=
        { pt := (forget₂ (AlgCat R) (ModuleCat R)).obj C
          ι :=
            { app := fun i => moduleHomOfLinear
                ((colimit.ι A i).hom.toLinearMap.comp
                  (SymmetricAlgebra.ι R (M.obj i)))
              naturality := fun i j f => by
                apply ModuleCat.hom_ext
                dsimp [moduleHomOfLinear]
                change (colimit.ι A j).hom.toLinearMap.comp
                    ((SymmetricAlgebra.ι R (M.obj j)).comp (M.map f).hom) =
                  (colimit.ι A i).hom.toLinearMap.comp
                    (SymmetricAlgebra.ι R (M.obj i))
                have hnat := (colimit.cocone A).w f
                have hnat' := congrArg (fun k => k.hom.toLinearMap) hnat
                dsimp [A, symmetricAlgCat] at hnat'
                change
                  ((colimit.ι A j).hom.comp (symmetricAlgebraMap (M.map f).hom)).toLinearMap =
                    (colimit.ι A i).hom.toLinearMap at hnat'
                have hnat'' :=
                  congrArg (fun k => k.comp (SymmetricAlgebra.ι R (M.obj i))) hnat'
                rw [AlgHom.comp_toLinearMap] at hnat''
                have hmapι :
                    (symmetricAlgebraMap (M.map f).hom).toLinearMap.comp
                        (SymmetricAlgebra.ι R (M.obj i)) =
                      (SymmetricAlgebra.ι R (M.obj j)).comp (M.map f).hom := by
                  apply LinearMap.ext
                  intro x
                  simp [symmetricAlgebraMap]
                rw [LinearMap.comp_assoc, hmapι] at hnat''
                exact hnat'' } }
      let h : colimit M ⟶ (forget₂ (AlgCat R) (ModuleCat R)).obj C :=
        colimit.desc M genCocone
      let hC : ((colimit M : ModuleCat R) : Type u) →ₗ[R] (C : Type u) := h.hom
      have hcomm : ∀ x y : (C : Type u), x * y = y * x := by
        intro x y
        obtain ⟨i, xi, hxi⟩ :=
          Types.jointly_surjective_of_isColimit
            (isColimitOfPreserves (forget (AlgCat R)) (colimit.isColimit A)) x
        obtain ⟨j, yj, hyj⟩ :=
          Types.jointly_surjective_of_isColimit
            (isColimitOfPreserves (forget (AlgCat R)) (colimit.isColimit A)) y
        rw [← hxi, ← hyj]
        let k := IsFiltered.max i j
        let fi := IsFiltered.leftToMax i j
        let fj := IsFiltered.rightToMax i j
        change (colimit.ι A i).hom xi * (colimit.ι A j).hom yj =
          (colimit.ι A j).hom yj * (colimit.ι A i).hom xi
        rw [← colimit.w_apply A fi xi, ← colimit.w_apply A fj yj]
        calc
          (colimit.ι A k).hom (A.map fi xi) *
              (colimit.ι A k).hom (A.map fj yj) =
              (colimit.ι A k).hom (A.map fi xi * A.map fj yj) :=
            ((colimit.ι A k).hom.map_mul _ _).symm
          _ = (colimit.ι A k).hom (A.map fj yj * A.map fi xi) := by
            let xk : symmetricAlgebra R (M.obj k) :=
              symmetricAlgebraMap (M.map fi).hom xi
            let yk : symmetricAlgebra R (M.obj k) :=
              symmetricAlgebraMap (M.map fj).hom yj
            have hmul :
                xk * yk = yk * xk := mul_comm xk yk
            simpa [A, symmetricAlgCat, xk, yk] using
              congrArg (colimit.ι A k).hom hmul
          _ = (colimit.ι A k).hom (A.map fj yj) *
              (colimit.ι A k).hom (A.map fi xi) :=
            (colimit.ι A k).hom.map_mul _ _
      let : CommRing (C : Type u) :=
        { (inferInstance : Ring (C : Type u)) with mul_comm := hcomm }
      let g : symmetricAlgebra R ((colimit M : ModuleCat R) : Type u) →ₐ[R] C :=
        SymmetricAlgebra.lift (R := R) (A := (C : Type u)) hC
      let targetCocone := symmetricAlgCat.mapCocone (colimit.cocone M)
      let f : colimit A ⟶ targetCocone.pt := colimit.desc A targetCocone
      have hgen' :
          moduleHomOfLinear (f.hom.toLinearMap.comp h.hom) =
            moduleHomOfLinear
              (X := colimit M)
              (Y := (forget₂ (AlgCat R) (ModuleCat R)).obj targetCocone.pt)
              (SymmetricAlgebra.ι R ((colimit M : ModuleCat R) : Type u) :
                ((colimit M : ModuleCat R) : Type u) →ₗ[R] (targetCocone.pt : Type u)) := by
        apply colimit.hom_ext
        intro i
        have hcomp :
            moduleHomOfLinear (f.hom.toLinearMap.comp h.hom) =
              h ≫ (forget₂ (AlgCat R) (ModuleCat R)).map f := by
          apply ModuleCat.hom_ext
          rfl
        rw [hcomp, ← Category.assoc, colimit.ι_desc]
        have hf := colimit.ι_desc targetCocone i
        have hfi :
            moduleHomOfLinear
                ((colimit.ι A i).hom.toLinearMap.comp
                  (SymmetricAlgebra.ι R (M.obj i))) ≫
              (forget₂ (AlgCat R) (ModuleCat R)).map f =
              moduleHomOfLinear
                ((targetCocone.ι.app i).hom.toLinearMap.comp
                  (SymmetricAlgebra.ι R (M.obj i))) := by
          apply ModuleCat.hom_ext
          change (f.hom.toLinearMap.comp
              ((colimit.ι A i).hom.toLinearMap.comp
                (SymmetricAlgebra.ι R (M.obj i)))) =
            (targetCocone.ι.app i).hom.toLinearMap.comp
              (SymmetricAlgebra.ι R (M.obj i))
          have hfc := congrArg (fun k => k.hom.toLinearMap) hf
          change
            ((f.hom.comp (colimit.ι A i).hom).toLinearMap) =
              (targetCocone.ι.app i).hom.toLinearMap at hfc
          rw [AlgHom.comp_toLinearMap] at hfc
          have hfc' := congrArg
            (fun k => k.comp (SymmetricAlgebra.ι R (M.obj i))) hfc
          simpa [LinearMap.comp_assoc] using hfc'
        rw [hfi]
        apply ModuleCat.hom_ext
        change (targetCocone.ι.app i).hom.toLinearMap.comp
              (SymmetricAlgebra.ι R (M.obj i)) =
            (SymmetricAlgebra.ι R ((colimit M : ModuleCat R) : Type u)).comp
              (colimit.ι M i).hom
        simp [targetCocone, symmetricAlgCat, symmetricAlgebraMap]
        exact
          SymmetricAlgebra.lift_comp_ι
            ((SymmetricAlgebra.ι R ((colimit M : ModuleCat R) : Type u)).comp
              (colimit.ι M i).hom)
      have hgen : f.hom.toLinearMap.comp h.hom =
          SymmetricAlgebra.ι R ((colimit M : ModuleCat R) : Type u) :=
        congrArg ModuleCat.Hom.hom hgen'
      have h₁ : f.hom.comp g =
          AlgHom.id R (symmetricAlgebra R ((colimit M : ModuleCat R) : Type u)) := by
        refine SymmetricAlgebra.algHom_ext (F := f.hom.comp g)
          (G := AlgHom.id R _) ?_
        apply LinearMap.ext
        intro m
        simpa [g, LinearMap.comp_apply] using LinearMap.congr_fun hgen m
      have h₂ : g.comp f.hom = AlgHom.id R C := by
        have h₂' :
            (AlgCat.ofHom (g.comp f.hom) : C ⟶ C) =
              AlgCat.ofHom (AlgHom.id R C) := by
          apply colimit.hom_ext
          intro i
          apply AlgCat.hom_ext
          change (g.comp f.hom).comp (colimit.ι A i).hom =
            (AlgHom.id R C).comp (colimit.ι A i).hom
          apply SymmetricAlgebra.algHom_ext
          ext m
          change g (f.hom ((colimit.ι A i).hom
              (SymmetricAlgebra.ι R (M.obj i) m))) =
            (colimit.ι A i).hom (SymmetricAlgebra.ι R (M.obj i) m)
          have hf := colimit.ι_desc targetCocone i
          have hf' := congrArg (fun k => k.hom) hf
          dsimp [A] at hf'
          change f.hom.comp (colimit.ι A i).hom =
            (targetCocone.ι.app i).hom at hf'
          have hf_m := congrArg
            (fun k => k (SymmetricAlgebra.ι R (M.obj i) m)) hf'
          change g ((f.hom.comp (colimit.ι A i).hom)
              (SymmetricAlgebra.ι R (M.obj i) m)) =
            (colimit.ι A i).hom (SymmetricAlgebra.ι R (M.obj i) m)
          rw [hf_m]
          simp [g, targetCocone, symmetricAlgCat, symmetricAlgebraMap]
          have hi := colimit.ι_desc genCocone i
          have hi' := congrArg (fun k => k.hom) hi
          change h.hom.comp (colimit.ι M i).hom =
            (genCocone.ι.app i).hom at hi'
          have hi_m := congrArg (fun k => k m) hi'
          have hi_m' := hi_m
          change hC ((colimit.ι M i).hom m) =
            (colimit.ι A i).hom (SymmetricAlgebra.ι R (M.obj i) m) at hi_m'
          rw [SymmetricAlgebra.lift_ι_apply]
          change (SymmetricAlgebra.lift hC)
              (SymmetricAlgebra.ι R ((colimit M : ModuleCat R) : Type u)
                ((colimit.ι M i).hom m)) =
            (colimit.ι A i).hom (SymmetricAlgebra.ι R (M.obj i) m)
          rw [SymmetricAlgebra.lift_ι_apply]
          exact hi_m'
        exact congrArg AlgCat.Hom.hom h₂'
      let eAlg : C ≃ₐ[R] symmetricAlgebra R ((colimit M : ModuleCat R) : Type u) :=
        AlgEquiv.ofAlgHom f.hom g h₁ h₂
      exact ⟨(preservesColimitIso
          (forget₂ (AlgCat R) (ModuleCat R)) A).symm ≪≫ eAlg.toLinearEquiv.toModuleIso⟩

/-! ## Localization -/

/-- Scalar extension of an `R`-algebra to the localization of `R`, used for the source's
notation `S⁻¹A` when `A` is not commutative. -/
abbrev localizedAlgebra
    {R A : Type*} [CommRing R] [Semiring A] [Algebra R A]
    (S : Submonoid R) :=
  localization S ⊗[R] A

/-- Localization commutes with tensor, exterior, and symmetric algebra formation. -/
theorem algebra_localization_iso
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) :
    Nonempty (localizedAlgebra (A := tensorAlgebra R M) S ≃ₐ[localization S]
        tensorAlgebra (localization S) (localizedModule S M)) ∧
      Nonempty (localizedAlgebra (A := exteriorAlgebra R M) S ≃ₐ[localization S]
        exteriorAlgebra (localization S) (localizedModule S M)) ∧
      Nonempty (localizedAlgebra (A := symmetricAlgebra R M) S ≃ₐ[localization S]
        symmetricAlgebra (localization S) (localizedModule S M)) := by
  constructor
  · let e := Formalization.Books.Algebra.Unit12.tensorProductLocalizationModuleEquiv S
      (M := M)
    let fgen : M →ₗ[R] tensorAlgebra (localization S) (localizedModule S M) :=
      (TensorAlgebra.ι (localization S)).restrictScalars R |>.comp
        (localizedModuleMap S M)
    let fR : tensorAlgebra R M →ₐ[R] tensorAlgebra (localization S) (localizedModule S M) :=
      TensorAlgebra.lift R fgen
    let f : localizedAlgebra (A := tensorAlgebra R M) S →ₐ[localization S]
        tensorAlgebra (localization S) (localizedModule S M) :=
      AlgHom.liftEquiv R (localization S) (tensorAlgebra R M)
        (tensorAlgebra (localization S) (localizedModule S M)) fR
    let ggen : localizedModule S M →ₗ[localization S]
        localizedAlgebra (A := tensorAlgebra R M) S :=
      (LinearMap.baseChange (localization S) (TensorAlgebra.ι R)).comp e.symm.toLinearMap
    let g : tensorAlgebra (localization S) (localizedModule S M) →ₐ[localization S]
        localizedAlgebra (A := tensorAlgebra R M) S :=
      TensorAlgebra.lift (localization S) ggen
    have he (m : M) (s : S) :
        e.symm (localizedModuleFraction S m s) =
          (Localization.mk 1 s ⊗ₜ[R] m) := by
      apply e.injective
      simp [e]
    have hgen : f.toLinearMap.comp ggen = TensorAlgebra.ι (localization S) := by
      apply LinearMap.ext
      intro x
      induction x using LocalizedModule.induction_on with
      | _ m s =>
        dsimp [ggen]
        rw [show e.symm (LocalizedModule.mk m s) =
          (Localization.mk 1 s ⊗ₜ[R] m) by simpa [localizedModuleFraction] using he m s]
        simp [f, fR, fgen]
        rw [← (TensorAlgebra.ι (localization S)).map_smul]
        apply congrArg (TensorAlgebra.ι (localization S))
        change Localization.mk 1 s • localizedModuleFraction S m 1 =
          localizedModuleFraction S m s
        simpa [localizationFraction] using
          (localizedModuleFraction_smul S 1 m s 1)
    have h₁ : f.comp g = AlgHom.id (localization S)
        (tensorAlgebra (localization S) (localizedModule S M)) := by
      apply TensorAlgebra.hom_ext
      simpa [g, LinearMap.comp_assoc] using hgen
    have hmap : (ggen.restrictScalars R).comp (localizedModuleMap S M) =
        (((Algebra.TensorProduct.includeRight :
          tensorAlgebra R M →ₐ[R] localizedAlgebra (A := tensorAlgebra R M) S).toLinearMap).comp
          (TensorAlgebra.ι R)) := by
      apply LinearMap.ext
      intro m
      dsimp [ggen]
      rw [show e.symm (localizedModuleMap S M m) =
        (Localization.mk 1 (1 : S) ⊗ₜ[R] m) by
          rw [localizedModuleMap_apply]
          exact he m 1]
      simp [LinearMap.baseChange_tmul]
      rw [Localization.mk_one_eq_algebraMap, map_one]
    have h₂ : g.comp f = AlgHom.id (localization S)
        (localizedAlgebra (A := tensorAlgebra R M) S) := by
      apply Algebra.TensorProduct.ext_ring
      apply TensorAlgebra.hom_ext
      ext m
      simp [f, fR, fgen, g, Algebra.TensorProduct.includeRight]
      simpa using LinearMap.congr_fun hmap m
    exact ⟨AlgEquiv.ofAlgHom f g h₁ h₂⟩
  · constructor
    · let e := Formalization.Books.Algebra.Unit12.tensorProductLocalizationModuleEquiv S
        (M := M)
      let fgen : M →ₗ[R] exteriorAlgebra (localization S) (localizedModule S M) :=
        (ExteriorAlgebra.ι (localization S)).restrictScalars R |>.comp
          (localizedModuleMap S M)
      let fR : exteriorAlgebra R M →ₐ[R]
          exteriorAlgebra (localization S) (localizedModule S M) :=
        ExteriorAlgebra.lift R ⟨fgen, by
          intro m
          simp [fgen]⟩
      let f : localizedAlgebra (A := exteriorAlgebra R M) S →ₐ[localization S]
          exteriorAlgebra (localization S) (localizedModule S M) :=
        AlgHom.liftEquiv R (localization S) (exteriorAlgebra R M)
          (exteriorAlgebra (localization S) (localizedModule S M)) fR
      let ggen : localizedModule S M →ₗ[localization S]
          localizedAlgebra (A := exteriorAlgebra R M) S :=
        (LinearMap.baseChange (localization S) (ExteriorAlgebra.ι R)).comp e.symm.toLinearMap
      have he (m : M) (s : S) :
          e.symm (localizedModuleFraction S m s) =
            (Localization.mk 1 s ⊗ₜ[R] m) := by
        apply e.injective
        simp [e]
      let g : exteriorAlgebra (localization S) (localizedModule S M) →ₐ[localization S]
          localizedAlgebra (A := exteriorAlgebra R M) S :=
        ExteriorAlgebra.lift (localization S) ⟨ggen, by
          intro x
          induction x using LocalizedModule.induction_on with
          | _ m s =>
            dsimp [ggen]
            rw [show e.symm (LocalizedModule.mk m s) =
              (Localization.mk 1 s ⊗ₜ[R] m) by
                simpa [localizedModuleFraction] using he m s]
            simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]⟩
      have hgen : f.toLinearMap.comp ggen = ExteriorAlgebra.ι (localization S) := by
        apply LinearMap.ext
        intro x
        induction x using LocalizedModule.induction_on with
        | _ m s =>
          dsimp [ggen]
          rw [show e.symm (LocalizedModule.mk m s) =
            (Localization.mk 1 s ⊗ₜ[R] m) by
              simpa [localizedModuleFraction] using he m s]
          simp [f, fR, fgen]
          rw [← (ExteriorAlgebra.ι (localization S)).map_smul]
          apply congrArg (ExteriorAlgebra.ι (localization S))
          change Localization.mk 1 s • localizedModuleFraction S m 1 =
            localizedModuleFraction S m s
          simpa [localizationFraction] using
            (localizedModuleFraction_smul S 1 m s 1)
      have h₁ : f.comp g = AlgHom.id (localization S)
          (exteriorAlgebra (localization S) (localizedModule S M)) := by
        apply ExteriorAlgebra.hom_ext
        simpa [g, LinearMap.comp_assoc] using hgen
      have hmap : (ggen.restrictScalars R).comp (localizedModuleMap S M) =
          (((Algebra.TensorProduct.includeRight :
            exteriorAlgebra R M →ₐ[R]
              localizedAlgebra (A := exteriorAlgebra R M) S).toLinearMap).comp
            (ExteriorAlgebra.ι R)) := by
        apply LinearMap.ext
        intro m
        dsimp [ggen]
        rw [show e.symm (localizedModuleMap S M m) =
          (Localization.mk 1 (1 : S) ⊗ₜ[R] m) by
            rw [localizedModuleMap_apply]
            exact he m 1]
        simp [LinearMap.baseChange_tmul]
        rw [Localization.mk_one_eq_algebraMap, map_one]
      have h₂ : g.comp f = AlgHom.id (localization S)
          (localizedAlgebra (A := exteriorAlgebra R M) S) := by
        apply Algebra.TensorProduct.ext_ring
        apply ExteriorAlgebra.hom_ext
        ext m
        simp [f, fR, fgen, g, Algebra.TensorProduct.includeRight]
        simpa using LinearMap.congr_fun hmap m
      exact ⟨AlgEquiv.ofAlgHom f g h₁ h₂⟩
    · let e := Formalization.Books.Algebra.Unit12.tensorProductLocalizationModuleEquiv S
        (M := M)
      let fgen : M →ₗ[R] symmetricAlgebra (localization S) (localizedModule S M) :=
        (SymmetricAlgebra.ι (localization S) (localizedModule S M)).restrictScalars R |>.comp
          (localizedModuleMap S M)
      let fR : symmetricAlgebra R M →ₐ[R]
          symmetricAlgebra (localization S) (localizedModule S M) :=
        SymmetricAlgebra.lift fgen
      let f : localizedAlgebra (A := symmetricAlgebra R M) S →ₐ[localization S]
          symmetricAlgebra (localization S) (localizedModule S M) :=
        AlgHom.liftEquiv R (localization S) (symmetricAlgebra R M)
          (symmetricAlgebra (localization S) (localizedModule S M)) fR
      let ggen : localizedModule S M →ₗ[localization S]
          localizedAlgebra (A := symmetricAlgebra R M) S :=
        (LinearMap.baseChange (localization S) (SymmetricAlgebra.ι R M)).comp e.symm.toLinearMap
      have he (m : M) (s : S) :
          e.symm (localizedModuleFraction S m s) =
            (Localization.mk 1 s ⊗ₜ[R] m) := by
        apply e.injective
        simp [e]
      let g : symmetricAlgebra (localization S) (localizedModule S M) →ₐ[localization S]
          localizedAlgebra (A := symmetricAlgebra R M) S :=
        SymmetricAlgebra.lift ggen
      have hgen : f.toLinearMap.comp ggen =
          SymmetricAlgebra.ι (localization S) (localizedModule S M) := by
        apply LinearMap.ext
        intro x
        induction x using LocalizedModule.induction_on with
        | _ m s =>
          dsimp [ggen]
          rw [show e.symm (LocalizedModule.mk m s) =
            (Localization.mk 1 s ⊗ₜ[R] m) by
              simpa [localizedModuleFraction] using he m s]
          simp [f, fR, fgen]
          rw [← (SymmetricAlgebra.ι (localization S) (localizedModule S M)).map_smul]
          apply congrArg (SymmetricAlgebra.ι (localization S) (localizedModule S M))
          change Localization.mk 1 s • localizedModuleFraction S m 1 =
            localizedModuleFraction S m s
          simpa [localizationFraction] using
            (localizedModuleFraction_smul S 1 m s 1)
      have h₁ : f.comp g = AlgHom.id (localization S)
          (symmetricAlgebra (localization S) (localizedModule S M)) := by
        apply SymmetricAlgebra.algHom_ext
        apply LinearMap.ext
        intro m
        simpa [g, LinearMap.comp_apply] using LinearMap.congr_fun hgen m
      have hmap : (ggen.restrictScalars R).comp (localizedModuleMap S M) =
          (((Algebra.TensorProduct.includeRight :
            symmetricAlgebra R M →ₐ[R]
              localizedAlgebra (A := symmetricAlgebra R M) S).toLinearMap).comp
            (SymmetricAlgebra.ι R M)) := by
        apply LinearMap.ext
        intro m
        dsimp [ggen]
        rw [show e.symm (localizedModuleMap S M m) =
          (Localization.mk 1 (1 : S) ⊗ₜ[R] m) by
            rw [localizedModuleMap_apply]
            exact he m 1]
        simp [LinearMap.baseChange_tmul]
        rw [Localization.mk_one_eq_algebraMap, map_one]
      have h₂ : g.comp f = AlgHom.id (localization S)
          (localizedAlgebra (A := symmetricAlgebra R M) S) := by
        apply Algebra.TensorProduct.ext_ring
        apply SymmetricAlgebra.algHom_ext
        ext m
        simp [f, fR, fgen, g, Algebra.TensorProduct.includeRight]
        simpa using LinearMap.congr_fun hmap m
      exact ⟨AlgEquiv.ofAlgHom f g h₁ h₂⟩

end
end Formalization.Books.Algebra.Unit13
