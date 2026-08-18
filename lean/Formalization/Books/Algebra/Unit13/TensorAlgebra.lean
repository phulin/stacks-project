import Mathlib.Algebra.Category.ModuleCat.Colimits
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

universe u v

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
  simpa [eq_neg_iff_add_eq_zero] using ExteriorAlgebra.ι_add_mul_swap x y

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
      simp only [C, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Basis.piTensorProduct_apply]
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
        Function.Exact a b ∧ Function.Surjective b) ∧
    (∃ a : TensorProduct R M₂ (exteriorPower R M₁ (n - 1)) →ₗ[R]
        exteriorPower R M₁ n,
      ∃ b : exteriorPower R M₁ n →ₗ[R] exteriorPower R M n,
        Function.Exact a b ∧ Function.Surjective b) := by
  sorry

/-- Indices for the two distinguished slots in the generator-and-relation presentation. -/
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
  sorry

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
  sorry

end
end Formalization.Books.Algebra.Unit13
