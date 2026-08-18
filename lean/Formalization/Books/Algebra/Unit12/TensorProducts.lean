import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Finite
import Formalization.Books.Algebra.Unit09.Localization

/-!
# Commutative Algebra, Chapter 12: Tensor products

The binary tensor product is Mathlib's `TensorProduct`, and the finite
multilinear tensor product is Mathlib's `PiTensorProduct`.  The declarations
below expose the book-facing interfaces while keeping the canonical
constructions and categorical APIs as the underlying objects.
-/

namespace Formalization.Books.Algebra.Unit12

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit09
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Bilinear maps and the binary tensor product -/

/-- An `R`-bilinear map, represented by the canonical curried linear-map type. -/
abbrev BilinearMap (R M N P : Type*) [CommRing R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P] :=
  M →ₗ[R] N →ₗ[R] P

/-- The canonical bilinear map into `M ⊗[R] N`. -/
def tensorProductCanonicalMap {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] :
    BilinearMap R M N (TensorProduct R M N) :=
  TensorProduct.mk R M N

/-- The lifting and uniqueness part of the tensor-product universal property. -/
theorem tensorProduct_lift_unique {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : BilinearMap R M N P) :
    ∃! F : TensorProduct R M N →ₗ[R] P,
      ∀ m n, F (m ⊗ₜ[R] n) = f m n := by
  refine ⟨TensorProduct.lift f, ?_, ?_⟩
  · intro m n
    rfl
  · intro F hF
    exact TensorProduct.lift.unique hF

theorem tensorProduct_isTensorProduct {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] :
    IsTensorProduct (tensorProductCanonicalMap (R := R) (M := M) (N := N)) := by
  exact TensorProduct.isTensorProduct R M N

/- The source's quotient construction is represented by Mathlib's tensor
   product; the following exact theorem records its generation assertion. -/
theorem tensorProduct_pure_tensors_span {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] :
    Submodule.span R
        {t : TensorProduct R M N | ∃ m n, m ⊗ₜ[R] n = t} = ⊤ := by
  exact TensorProduct.span_tmul_eq_top R M N

/-- Two tensor-product universal maps are uniquely isomorphic. -/
theorem tensorProduct_universal_unique {R M N T T' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup T] [AddCommGroup T']
    [Module R M] [Module R N] [Module R T] [Module R T']
    (g : BilinearMap R M N T) (g' : BilinearMap R M N T')
    (hg : IsTensorProduct g) (hg' : IsTensorProduct g') :
    ∃! e : T ≃ₗ[R] T', ∀ m n, e (g m n) = g' m n := by
  let e : T ≃ₗ[R] T' := hg.equiv.symm.trans hg'.equiv
  have he : ∀ m n, e (g m n) = g' m n := by
    intro m n
    apply hg'.equiv.symm.injective
    simp [e, hg.equiv_symm_apply, hg'.equiv_symm_apply]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply LinearEquiv.ext
  intro t
  refine hg.inductionOn t ?_ ?_ ?_
  · simp
  · intro m n
    rw [he' m n, he m n]
  · intro x y hx hy
    simp [hx, hy]

/-! ## Symmetries, products, units, and multilinear tensor products -/

/-- The flip isomorphism `M ⊗ N ≅ N ⊗ M`. -/
def tensorProductFlip {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] :
    TensorProduct R M N ≃ₗ[R] TensorProduct R N M :=
  TensorProduct.comm R M N

@[simp] theorem tensorProductFlip_tmul {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (m : M) (n : N) :
    tensorProductFlip (R := R) (M := M) (N := N) (m ⊗ₜ[R] n) = n ⊗ₜ[R] m := by
  rfl

/- In `ModuleCat`, the binary biproduct has underlying module `M × N`; this
   is the canonical Mathlib representative of the displayed `M ⊕ N`. -/
def tensorProductBiproduct {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] :
    TensorProduct R (M × N) P ≃ₗ[R]
      (TensorProduct R M P) × (TensorProduct R N P) :=
  TensorProduct.prodLeft R R M N P

@[simp] theorem tensorProductBiproduct_tmul {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (m : M) (n : N) (p : P) :
    tensorProductBiproduct (R := R) (M := M) (N := N) (P := P)
        ((m, n) ⊗ₜ[R] p) = (m ⊗ₜ[R] p, n ⊗ₜ[R] p) := by
  rfl

/-- The unit isomorphism `R ⊗[R] M ≅ M`. -/
def tensorProductUnit {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] :
    TensorProduct R R M ≃ₗ[R] M :=
  TensorProduct.lid R M

@[simp] theorem tensorProductUnit_tmul {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (r : R) (m : M) :
    tensorProductUnit (R := R) (M := M) (r ⊗ₜ[R] m) = r • m := by
  rfl

/-- Mathlib's multilinear tensor product for a finite family of modules. -/
abbrev multilinearTensorProduct {R : Type u} [CommRing R] {r : ℕ}
    (M : Fin r → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    Type (max u v) :=
  PiTensorProduct R M

/-- The universal multilinear map into the multilinear tensor product. -/
def multilinearTensorProductMap {R : Type u} [CommRing R] {r : ℕ}
    (M : Fin r → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    MultilinearMap R M (multilinearTensorProduct (R := R) M) :=
  PiTensorProduct.tprod R

/-- The universal property of a multilinear tensor product. -/
def IsMultilinearTensorProduct {R : Type u} [CommRing R] {r : ℕ}
    (M : Fin r → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (T : Type w) [AddCommGroup T] [Module R T]
    (g : MultilinearMap R M T) : Prop :=
  Function.Bijective (PiTensorProduct.lift g)

theorem multilinearTensorProduct_isUniversal {R : Type u} [CommRing R] {r : ℕ}
    (M : Fin r → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    IsMultilinearTensorProduct M
      (multilinearTensorProduct (R := R) M)
      (multilinearTensorProductMap (R := R) M) := by
  change Function.Bijective (PiTensorProduct.lift (PiTensorProduct.tprod R))
  rw [PiTensorProduct.lift_tprod]
  exact Function.bijective_id

theorem multilinearTensorProduct_pure_tensors_span {R : Type u} [CommRing R]
    {r : ℕ} (M : Fin r → Type v) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] :
    Submodule.span R
        (Set.range (multilinearTensorProductMap (R := R) M)) = ⊤ :=
  PiTensorProduct.span_tprod_eq_top (R := R) (s := M)

theorem multilinearTensorProduct_universal_unique {R : Type u} [CommRing R]
    {r : ℕ} (M : Fin r → Type v) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] {T T' : Type*} [AddCommGroup T] [AddCommGroup T']
    [Module R T] [Module R T'] (g : MultilinearMap R M T)
    (g' : MultilinearMap R M T')
    (hg : IsMultilinearTensorProduct M T g)
    (hg' : IsMultilinearTensorProduct M T' g') :
    ∃! e : T ≃ₗ[R] T', ∀ x, e (g x) = g' x := by
  let e₁ : multilinearTensorProduct (R := R) M ≃ₗ[R] T :=
    LinearEquiv.ofBijective (PiTensorProduct.lift g) hg
  let e₂ : multilinearTensorProduct (R := R) M ≃ₗ[R] T' :=
    LinearEquiv.ofBijective (PiTensorProduct.lift g') hg'
  have he₁ : e₁.toLinearMap = PiTensorProduct.lift g := by
    rfl
  have he₂ : e₂.toLinearMap = PiTensorProduct.lift g' := by
    rfl
  have hx : ∀ x, e₁.symm (g x) = PiTensorProduct.tprod R x := by
    intro x
    apply e₁.injective
    rw [e₁.apply_symm_apply]
    change g x = e₁.toLinearMap (PiTensorProduct.tprod R x)
    rw [he₁]
    exact (PiTensorProduct.lift.tprod (φ := g) x).symm
  have hx' : ∀ x, e₂ (PiTensorProduct.tprod R x) = g' x := by
    intro x
    change e₂.toLinearMap (PiTensorProduct.tprod R x) = g' x
    rw [he₂]
    exact PiTensorProduct.lift.tprod (φ := g') x
  let e : T ≃ₗ[R] T' := e₁.symm.trans e₂
  have he : ∀ x, e (g x) = g' x := by
    intro x
    change e₂ (e₁.symm (g x)) = g' x
    rw [hx x, hx' x]
  refine ⟨e, he, ?_⟩
  intro e' he'
  have hcomp : e'.toLinearMap.comp e₁.toLinearMap = e₂.toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change e' (e₁.toLinearMap (PiTensorProduct.tprod R x)) =
      e₂.toLinearMap (PiTensorProduct.tprod R x)
    rw [he₁, he₂, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    exact he' x
  apply LinearEquiv.ext
  intro t
  obtain ⟨z, rfl⟩ := e₁.surjective t
  change e' (e₁ z) = e₂ (e₁.symm (e₁ z))
  rw [e₁.symm_apply_apply]
  exact DFunLike.congr_fun hcomp z

/-- The canonical associator for three binary tensor products. -/
def tensorProductAssociator {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] :
    TensorProduct R (TensorProduct R M N) P ≃ₗ[R]
      TensorProduct R M (TensorProduct R N P) :=
  TensorProduct.assoc R M N P

@[simp] theorem tensorProductAssociator_tmul {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (m : M) (n : N) (p : P) :
    tensorProductAssociator (R := R) (M := M) (N := N) (P := P)
        ((m ⊗ₜ[R] n) ⊗ₜ[R] p) = m ⊗ₜ[R] (n ⊗ₜ[R] p) := by
  rfl

/-! ## Bimodules and the Hom adjunction -/

/-- Two commuting module actions, the commutative-ring form of a bimodule. -/
def IsBimodule (A B N : Type*) [CommRing A] [CommRing B]
    [AddCommGroup N] [Module A N] [Module B N] : Prop :=
  SMulCommClass A B N

/-- The right-action notation for a bimodule, expressed using the left action of `B`. -/
def bimoduleRightAction {A B N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module A N] [Module B N] : N → B → N :=
  fun n b => b • n

theorem bimodule_right_action_commutes {A B N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module A N] [Module B N]
    (hN : IsBimodule A B N) (a : A) (b : B) (n : N) :
    bimoduleRightAction (A := A) (B := B) (N := N) (a • n) b =
      a • bimoduleRightAction (A := A) (B := B) (N := N) n b := by
  exact (hN.smul_comm a b n).symm

/- The action on a tensor product in which the `B`-action is on the right
   factor is obtained by flipping, transporting the `B`-module structure, and
   flipping back.  This is the canonical construction needed for the
   bimodule lemma and has no extra mathematical hypotheses. -/
@[instance_reducible] noncomputable def tensorProductBModule
    (A B X Y : Type*) [CommRing A] [CommRing B]
    [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] [Module B Y]
    [SMulCommClass A B Y] : Module B (TensorProduct A X Y) :=
  (TensorProduct.comm A X Y).toAddEquiv.module B

/- These interfaces express that the transported action commutes with the
   original `A`-action.  They are useful named facts for the two nested
   tensor products and are proved in the later proof stage. -/
theorem tensorProductBModule_smulCommClass
    (A B X Y : Type*) [CommRing A] [CommRing B]
    [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] [Module B Y]
    [SMulCommClass A B Y] :
    letI : Module B (TensorProduct A X Y) :=
      tensorProductBModule A B X Y
    SMulCommClass A B (TensorProduct A X Y) := by
  let : Module B (TensorProduct A X Y) := tensorProductBModule A B X Y
  refine ⟨?_⟩
  intro a b z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    change
      a • (TensorProduct.comm A X Y).symm
          (b • (TensorProduct.comm A X Y) (x ⊗ₜ[A] y)) =
        (TensorProduct.comm A X Y).symm
          (b • (TensorProduct.comm A X Y) (a • x ⊗ₜ[A] y))
    apply (TensorProduct.comm A X Y).injective
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    simp only [TensorProduct.comm_tmul, TensorProduct.smul_tmul']
    rw [smul_comm]
  · intro x y hx hy
    simp [smul_add, hx, hy]

theorem tensorProductBModule_smulCommClass_symm
    (A B X Y : Type*) [CommRing A] [CommRing B]
    [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] [Module B Y]
    [SMulCommClass A B Y] :
    letI : Module B (TensorProduct A X Y) :=
      tensorProductBModule A B X Y
    SMulCommClass B A (TensorProduct A X Y) := by
  let : Module B (TensorProduct A X Y) := tensorProductBModule A B X Y
  let : SMulCommClass A B (TensorProduct A X Y) :=
    tensorProductBModule_smulCommClass A B X Y
  exact SMulCommClass.symm A B (TensorProduct A X Y)

/- The tensor-with-bimodule assertion uses the induced actions above. -/
theorem tensor_with_bimodule {A B M N P : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module A M] [Module A N] [Module B N] [Module B P]
    (hN : IsBimodule A B N) :
    letI : SMulCommClass A B N := hN
    letI : SMulCommClass B A N := SMulCommClass.symm A B N
    letI : Module B (TensorProduct A M N) :=
      tensorProductBModule A B M N
    letI : SMulCommClass A B (TensorProduct A M N) :=
      tensorProductBModule_smulCommClass A B M N
    letI : SMulCommClass B A (TensorProduct A M N) :=
      tensorProductBModule_smulCommClass_symm A B M N
    letI : SMulCommClass A B (TensorProduct B N P) := inferInstance
    letI : Module B (TensorProduct A M (TensorProduct B N P)) :=
      tensorProductBModule A B M (TensorProduct B N P)
    letI : SMulCommClass A B (TensorProduct A M (TensorProduct B N P)) :=
      tensorProductBModule_smulCommClass A B M (TensorProduct B N P)
    IsBimodule A B ((TensorProduct A M N) ⊗[B] P) ∧
      IsBimodule A B (TensorProduct A M (TensorProduct B N P)) ∧
      Nonempty
        {e : (TensorProduct A M N) ⊗[B] P ≃ₗ[A]
            TensorProduct A M (TensorProduct B N P) //
          ∀ (b : B) (z : (TensorProduct A M N) ⊗[B] P),
            e (b • z) = b • e z} := by
  let : SMulCommClass A B N := hN
  let : SMulCommClass B A N := SMulCommClass.symm A B N
  let : Module B (TensorProduct A M N) := tensorProductBModule A B M N
  let : SMulCommClass A B (TensorProduct A M N) :=
    tensorProductBModule_smulCommClass A B M N
  let : SMulCommClass B A (TensorProduct A M N) :=
    tensorProductBModule_smulCommClass_symm A B M N
  let : SMulCommClass A B (TensorProduct B N P) := inferInstance
  let : Module B (TensorProduct A M (TensorProduct B N P)) :=
    tensorProductBModule A B M (TensorProduct B N P)
  let : SMulCommClass A B (TensorProduct A M (TensorProduct B N P)) :=
    tensorProductBModule_smulCommClass A B M (TensorProduct B N P)
  let j (p : P) : N →ₗ[A] TensorProduct B N P :=
    { toFun := fun n => n ⊗ₜ[B] p
      map_add' := by intro n n'; exact TensorProduct.add_tmul _ _ _
      map_smul' := by intro a n; rfl }
  let inner (p : P) : TensorProduct A M N →ₗ[A]
      TensorProduct A M (TensorProduct B N P) :=
    TensorProduct.map (LinearMap.id : M →ₗ[A] M) (j p)
  let : SMulCommClass B A (TensorProduct A M (TensorProduct B N P)) :=
    tensorProductBModule_smulCommClass_symm A B M (TensorProduct B N P)
  let Fbil : (TensorProduct A M N) →ₗ[B] P →ₗ[B]
      TensorProduct A M (TensorProduct B N P) :=
    LinearMap.mk₂' B B (fun x p => inner p x)
      (by intro x y p; simp [inner])
      (by
        intro b x p
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp [inner]
        · intro m n
          simp only [inner, TensorProduct.map_tmul]
          change m ⊗ₜ[A] ((b • n) ⊗ₜ[B] p) =
            m ⊗ₜ[A] (b • (n ⊗ₜ[B] p))
          rfl
        · intro x y hx hy
          simp [inner, hx, hy])
      (by
        intro x p q
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp [inner]
        · intro m n
          change m ⊗ₜ[A] (n ⊗ₜ[B] (p + q)) =
            m ⊗ₜ[A] (n ⊗ₜ[B] p) + m ⊗ₜ[A] (n ⊗ₜ[B] q)
          rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
        · intro z z' hz hz'
          simp only [inner, map_add, hz, hz']
          abel)
      (by
        intro b x p
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp [inner]
        · intro m n
          simp only [inner, TensorProduct.map_tmul]
          change m ⊗ₜ[A] (n ⊗ₜ[B] (b • p)) =
            m ⊗ₜ[A] (b • (n ⊗ₜ[B] p))
          rw [TensorProduct.tmul_smul]
        · intro x y hx hy
          simp [inner, hx, hy])
  let F_B : (TensorProduct A M N) ⊗[B] P →ₗ[B]
      TensorProduct A M (TensorProduct B N P) := TensorProduct.lift Fbil
  let F : (TensorProduct A M N) ⊗[B] P →ₗ[A]
      TensorProduct A M (TensorProduct B N P) :=
    { F_B with
      map_smul' := by
        intro a z
        refine TensorProduct.induction_on z ?_ ?_ ?_
        · simp [F_B]
        · intro x p
          change inner p (a • x) = a • inner p x
          exact (inner p).map_smul a x
        · intro x y hx hy
          rw [smul_add]
          change F_B (a • x + a • y) = a • F_B (x + y)
          simp only [F_B.map_add, smul_add]
          have hx' : F_B (a • x) = a • F_B x := by exact hx
          have hy' : F_B (a • y) = a • F_B y := by exact hy
          rw [hx', hy'] }
  let k₀ (m : M) : N →ₗ[B] TensorProduct A M N :=
    { toFun := fun n => m ⊗ₜ[A] n
      map_add' := by intro n n'; exact TensorProduct.tmul_add _ _ _
      map_smul' := by
        intro b n
        change m ⊗ₜ[A] (b • n) = b • (m ⊗ₜ[A] n)
        rfl }
  let outer (m : M) : TensorProduct B N P →ₗ[B]
      ((TensorProduct A M N) ⊗[B] P) :=
    TensorProduct.map (k₀ m) (LinearMap.id : P →ₗ[B] P)
  let k (m : M) : TensorProduct B N P →ₗ[A]
      ((TensorProduct A M N) ⊗[B] P) :=
    { outer m with
      map_smul' := by
        intro a z
        refine TensorProduct.induction_on z ?_ ?_ ?_
        · simp [outer]
        · intro n p
          change ((m ⊗ₜ[A] (a • n)) ⊗ₜ[B] p) =
            a • ((m ⊗ₜ[A] n) ⊗ₜ[B] p)
          rw [TensorProduct.tmul_smul]
          rfl
        · intro z z' hz hz'
          rw [smul_add]
          change outer m (a • z + a • z') = a • outer m (z + z')
          simp only [(outer m).map_add, smul_add]
          have hz'': outer m (a • z) = a • outer m z := by exact hz
          have hz''': outer m (a • z') = a • outer m z' := by exact hz'
          rw [hz'', hz'''] }
  let Gbil : M →ₗ[A] (TensorProduct B N P) →ₗ[A]
      ((TensorProduct A M N) ⊗[B] P) :=
    LinearMap.mk₂' A A (fun m z => k m z)
      (by
        intro m m' z
        refine TensorProduct.induction_on z ?_ ?_ ?_
        · simp [k, outer]
        · intro n p
          change ((m + m') ⊗ₜ[A] n) ⊗ₜ[B] p =
            (m ⊗ₜ[A] n) ⊗ₜ[B] p + (m' ⊗ₜ[A] n) ⊗ₜ[B] p
          rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
        · intro z z' hz hz'
          simp only [k, map_add, hz, hz']
          abel)
      (by
        intro a m z
        refine TensorProduct.induction_on z ?_ ?_ ?_
        · simp [k]
        · intro n p
          change ((a • m) ⊗ₜ[A] n) ⊗ₜ[B] p =
            a • ((m ⊗ₜ[A] n) ⊗ₜ[B] p)
          rfl
        · intro z z' hz hz'
          rw [map_add, map_add, hz, hz', smul_add])
      (by intro m z z'; exact (k m).map_add z z')
      (by intro a m z; exact (k m).map_smul a z)
  let G : TensorProduct A M (TensorProduct B N P) →ₗ[A]
      ((TensorProduct A M N) ⊗[B] P) := TensorProduct.lift Gbil
  have hGF : ∀ z, G (F z) = z := by
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [F, G]
    · intro x p
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp [F, G]
      · intro m n
        change G (m ⊗ₜ[A] (n ⊗ₜ[B] p)) =
          (m ⊗ₜ[A] n) ⊗ₜ[B] p
        rfl
      · intro x y hx hy
        rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
    · intro z z' hz hz'
      rw [map_add, map_add, hz, hz']
  have hFG : ∀ z, F (G z) = z := by
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [F, G]
    · intro m z
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp [F, G]
      · intro n p
        change F ((m ⊗ₜ[A] n) ⊗ₜ[B] p) =
          m ⊗ₜ[A] (n ⊗ₜ[B] p)
        rfl
      · intro z z' hz hz'
        rw [TensorProduct.tmul_add, map_add, map_add, hz, hz']
    · intro z z' hz hz'
      rw [map_add, map_add, hz, hz']
  have hX : IsBimodule A B ((TensorProduct A M N) ⊗[B] P) := by
    change SMulCommClass A B ((TensorProduct A M N) ⊗[B] P)
    infer_instance
  have hY : IsBimodule A B (TensorProduct A M (TensorProduct B N P)) := by
    change SMulCommClass A B (TensorProduct A M (TensorProduct B N P))
    exact tensorProductBModule_smulCommClass A B M (TensorProduct B N P)
  have hFB : ∀ (b : B) (z : (TensorProduct A M N) ⊗[B] P),
      F (b • z) = b • F z := by
    intro b z
    exact F_B.map_smul b z
  let e : (TensorProduct A M N) ⊗[B] P ≃ₗ[A]
      TensorProduct A M (TensorProduct B N P) :=
    LinearEquiv.ofLinear F G ?_ ?_
  refine ⟨hX, hY, ⟨⟨e, ?_⟩⟩⟩
  · intro b z
    exact hFB b z
  · apply LinearMap.ext
    intro z
    exact hFG z
  · apply LinearMap.ext
    intro z
    exact hGF z

/-- The tensor/Hom adjunction for modules. -/
noncomputable def tensorHomEquiv {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] :
    (TensorProduct R M N →ₗ[R] P) ≃ₗ[R]
      (M →ₗ[R] N →ₗ[R] P) :=
  (TensorProduct.lift.equiv (RingHom.id R) M N P).symm

@[simp] theorem tensorHomEquiv_apply_tmul {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (F : TensorProduct R M N →ₗ[R] P) (m : M) (n : N) :
    tensorHomEquiv (R := R) (M := M) (N := N) (P := P) F m n =
      F (m ⊗ₜ[R] n) := by
  rfl

/-! ## Colimits and exactness -/

/-- The colimit diagram obtained by tensoring a module-valued diagram on the right. -/
abbrev tensorProductColimitDiagram {R : Type u} [CommRing R]
    {I : Type u} [Preorder I] (M : I ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) : I ⥤ ModuleCat.{u} R :=
  M ⋙ MonoidalCategory.tensorRight N

/-- Tensoring with a fixed module commutes with colimits in `ModuleCat`. -/
noncomputable def tensorProductColimitIso {R : Type u} [CommRing R]
    {I : Type u} [Preorder I] (M : I ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) :
    colimit (tensorProductColimitDiagram M N) ≅
      (MonoidalCategory.tensorRight N).obj (colimit M) :=
  (preservesColimitIso (MonoidalCategory.tensorRight N) M).symm

/-- The canonical map from a stage tensor product to the tensor product of the colimit. -/
def tensorProductColimitStageMap {R : Type u} [CommRing R]
    {I : Type u} [Preorder I] (M : I ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) (i : I) :
    (tensorProductColimitDiagram M N).obj i ⟶
      (MonoidalCategory.tensorRight N).obj (colimit M) :=
  (MonoidalCategory.tensorRight N).map (colimit.ι M i)

theorem tensorProductColimitIso_stage {R : Type u} [CommRing R]
    {I : Type u} [Preorder I] (M : I ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) (i : I) :
    colimit.ι (tensorProductColimitDiagram M N) i ≫
        (tensorProductColimitIso M N).hom =
      tensorProductColimitStageMap M N i := by
  exact ι_preservesColimitIso_inv (MonoidalCategory.tensorRight N) M i

/-- Tensoring an exact right-exact sequence remains exact and surjective. -/
theorem tensorProduct_right_exact {R M₁ M₂ M₃ N : Type*} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup N]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (LinearMap.rTensor N f) (LinearMap.rTensor N g) ∧
      Function.Surjective (LinearMap.rTensor N g) := by
  exact ⟨rTensor_exact N hfg hg, LinearMap.rTensor_surjective N hg⟩

/-- A map ending in zero is represented by exactness together with surjectivity. -/
theorem tensorProduct_right_exact_sequence {R M₁ M₂ M₃ N : Type*} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup N]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (LinearMap.rTensor N f) (LinearMap.rTensor N g) ∧
      Function.Surjective (LinearMap.rTensor N g) :=
  tensorProduct_right_exact f g hfg hg

/- The following explicit example records the source's failure of left
   exactness; the displayed calculation is the pure-tensor form of the
   vanishing induced map. -/
def integerDoubling : ℤ →ₗ[ℤ] ℤ :=
  (LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight 2

theorem integerDoubling_injective : Function.Injective integerDoubling := by
  intro x y hxy
  apply mul_right_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
  exact hxy

theorem integer_tensor_zmod_two_nontrivial :
    Nontrivial (TensorProduct ℤ ℤ (ZMod 2)) := by
  exact (TensorProduct.lid ℤ (ZMod 2)).surjective.nontrivial

theorem integerDoubling_rTensor_zmod_two_zero :
    LinearMap.rTensor (ZMod 2) integerDoubling = 0 := by
  ext x
  change LinearMap.rTensor (ZMod 2) integerDoubling (1 ⊗ₜ[ℤ] x) = 0
  simp only [LinearMap.rTensor_tmul]
  change (2 * 1 : ℤ) ⊗ₜ[ℤ] x = 0
  rw [mul_one]
  calc
    (2 : ℤ) ⊗ₜ[ℤ] x = (2 : ℤ) • ((1 : ℤ) ⊗ₜ[ℤ] x) :=
      TensorProduct.tmul_eq_smul_one_tmul 2 x
    _ = (1 : ℤ) ⊗ₜ[ℤ] ((2 : ℤ) • x) := by
      rw [← TensorProduct.tmul_smul]
    _ = 0 := by
      have hx : (2 : ℤ) • x = 0 := by
        rw [← Int.cast_smul_eq_zsmul (ZMod 2)]
        simpa using (ZModModule.char_nsmul_eq_zero 2 x)
      rw [hx]
      simp

theorem integerDoubling_rTensor_zmod_two_not_injective :
    ¬Function.Injective (LinearMap.rTensor (ZMod 2) integerDoubling) := by
  rw [integerDoubling_rTensor_zmod_two_zero]
  intro h
  let : Nontrivial (TensorProduct ℤ ℤ (ZMod 2)) :=
    integer_tensor_zmod_two_nontrivial
  obtain ⟨x, hx⟩ := exists_ne (0 : TensorProduct ℤ ℤ (ZMod 2))
  exact hx (h (by simp))

theorem integerDoubling_rTensor_zmod_two_pure_zero (x : ℤ) (y : ZMod 2) :
    LinearMap.rTensor (ZMod 2) integerDoubling (x ⊗ₜ[ℤ] y) = 0 := by
  rw [integerDoubling_rTensor_zmod_two_zero]
  rfl

theorem flatModule_preserves_exact {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] [Module.Flat R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : Function.Exact f g) :
    Function.Exact (LinearMap.rTensor P f) (LinearMap.rTensor P g) := by
  exact Module.Flat.rTensor_exact P hfg

/-! ## Finiteness and localization -/

theorem tensorProduct_finite {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.Finite R (TensorProduct R M N) := by
  infer_instance

theorem tensorProduct_finitePresentation {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N] :
    Module.FinitePresentation R (TensorProduct R M N) := by
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  let : Module.FinitePresentation R ((Fin n → R) ⊗[R] N) := by
    apply Module.FinitePresentation.of_equiv
      ((TensorProduct.piLeft R N (fun _ : Fin n => R) ≪≫ₗ
        LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R N)).symm)
  let : Module.Finite R ((Fin m → R) ⊗[R] N) :=
    tensorProduct_finite
  apply Module.finitePresentation_of_surjective (LinearMap.rTensor N f)
    (LinearMap.rTensor_surjective N hf)
  have hfg' : Function.Exact (LinearMap.rTensor N g) (LinearMap.rTensor N f) :=
    rTensor_exact N hfg hf
  rw [LinearMap.exact_iff] at hfg'
  rw [hfg']
  exact Submodule.fg_range _

/-- The canonical localization/module-tensor equivalence. -/
noncomputable def tensorProductLocalizationModuleEquiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) :
    localization S ⊗[R] M ≃ₗ[localization S] localizedModule S M :=
  (LocalizedModule.equivTensorProduct S M).symm

@[simp] theorem tensorProductLocalizationModuleEquiv_tmul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) (a : R) (m : M) (s : S) :
    tensorProductLocalizationModuleEquiv S
        (Localization.mk a s ⊗ₜ[R] m) =
      a • localizedModuleFraction S m s := by
  exact LocalizedModule.equivTensorProduct_symm_apply_tmul S m a s

/-- The canonical localization equivalence for a tensor product of two modules. -/
noncomputable def tensorProductLocalizationEquiv
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (S : Submonoid R) :
    localizedModule S M ⊗[localization S] localizedModule S N ≃ₗ[localization S]
      localizedModule S (TensorProduct R M N) :=
  (TensorProduct.congr
      (LocalizedModule.equivTensorProduct (R := R) S M)
      (LocalizedModule.equivTensorProduct (R := R) S N)) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.distribBaseChange R (localization S) M N).symm ≪≫ₗ
      (LocalizedModule.equivTensorProduct (R := R) S (TensorProduct R M N)).symm

@[simp] theorem tensorProductLocalizationEquiv_tmul
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (S : Submonoid R) (m : M) (n : N) (s t : S) :
    tensorProductLocalizationEquiv S
        (localizedModuleFraction S m s ⊗ₜ[localization S]
          localizedModuleFraction S n t) =
      localizedModuleFraction S (m ⊗ₜ[R] n) (s * t) := by
  simp [tensorProductLocalizationEquiv, localizedModuleFraction]
  rw [Localization.mk_eq_mk']
  rw [← IsLocalization.mk'_mul]
  simp only [one_mul]
  rw [← Localization.mk_eq_mk']
  simp

end
end Formalization.Books.Algebra.Unit12
