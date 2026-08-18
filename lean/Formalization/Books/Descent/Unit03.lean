import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Descent, Chapter 3: Descent for modules -/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct

namespace Formalization.Books.Descent.Unit03

universe u v w

/-! ## Relative tensor powers -/

/-- The `(n + 1)`-fold tensor product of `A` over `R`. -/
abbrev relativeTensorProduct (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) : Type u := ⨂[R] _ : Fin (n + 1), A

/-- The `n`-fold tensor power used for the module in degree `n`. -/
abbrev relativeTensorPower (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) : Type u := ⨂[R] _ : Fin n, A

/-- The Amitsur cosimplicial algebra, realized by Mathlib's Čech conerve.

The chosen wide pushouts in `CommRingCat` are the tensor powers of `A` over `R`;
the comparison with the indexed tensor-product presentation is recorded below. -/
def relativeTensorCosimplicialAlgebra (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] : CosimplicialObject CommRingCat :=
  (Arrow.mk (CommRingCat.ofHom (algebraMap R A))).cechConerve

/-- The transition map of the Amitsur cosimplicial algebra in its canonical
Čech-conerve presentation.  This is the construction used for arbitrary
simplex maps; the indexed pure-tensor formula below is a presentation theorem. -/
def relativeTensorCosimplicialAlgebraMap (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    (relativeTensorCosimplicialAlgebra R A).obj (SimplexCategory.mk n) ⟶
      (relativeTensorCosimplicialAlgebra R A).obj (SimplexCategory.mk m) :=
  (relativeTensorCosimplicialAlgebra R A).map φ

def relativeTensorCosimplicialAlgebraFace (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) (i : Fin (n + 2)) :
    (relativeTensorCosimplicialAlgebra R A).obj (SimplexCategory.mk n) ⟶
      (relativeTensorCosimplicialAlgebra R A).obj (SimplexCategory.mk (n + 1)) :=
  relativeTensorCosimplicialAlgebraMap R A (SimplexCategory.δ i)

def relativeTensorCosimplicialAlgebraDegeneracy (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) (i : Fin (n + 1)) :
    (relativeTensorCosimplicialAlgebra R A).obj (SimplexCategory.mk (n + 1)) ⟶
      (relativeTensorCosimplicialAlgebra R A).obj (SimplexCategory.mk n) :=
  relativeTensorCosimplicialAlgebraMap R A (SimplexCategory.σ i)

theorem relativeTensorCosimplicialAlgebra_degree (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    Nonempty ((relativeTensorCosimplicialAlgebra R A).obj (SimplexCategory.mk n) ≅
      CommRingCat.of (relativeTensorProduct R A n)) := by
  sorry

/-- The tensor-power map attached to a simplex map, in the source's pure-tensor
presentation.  The empty products in the formula are the units of `A`. -/
theorem relativeTensorMap_exists (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] {n m : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    ∃ g : relativeTensorProduct R A n →ₐ[R] relativeTensorProduct R A m,
      ∀ x : Fin (n + 1) → A,
        g (PiTensorProduct.tprod R x) =
          PiTensorProduct.tprod R (fun j : Fin (m + 1) ↦
            Finset.prod (Finset.filter (fun i : Fin (n + 1) ↦ φ.toOrderHom i = j)
              Finset.univ) x) := by
  sorry

noncomputable def relativeTensorMap (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] {n m : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    relativeTensorProduct R A n →ₐ[R] relativeTensorProduct R A m :=
  Classical.choose (relativeTensorMap_exists R A φ)

/-- The coface maps in the Amitsur cosimplicial algebra. -/
noncomputable def relativeTensorFace (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) (i : Fin (n + 2)) :
    relativeTensorProduct R A n →+* relativeTensorProduct R A (n + 1) :=
  relativeTensorMap R A (SimplexCategory.δ i)

/-- The codegeneracy maps in the Amitsur cosimplicial algebra. -/
noncomputable def relativeTensorDegeneracy (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) (i : Fin (n + 1)) :
    relativeTensorProduct R A (n + 1) →+* relativeTensorProduct R A n :=
  relativeTensorMap R A (SimplexCategory.σ i)

theorem relativeTensorMap_pure (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] {n m : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (x : Fin (n + 1) → A) :
    relativeTensorMap R A φ (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun j : Fin (m + 1) ↦
        Finset.prod (Finset.filter (fun i : Fin (n + 1) ↦ φ.toOrderHom i = j)
          Finset.univ) x) := by
  exact Classical.choose_spec (relativeTensorMap_exists R A φ) x

theorem relativeTensorFace_zero_pure (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (x : Fin 1 → A) :
    relativeTensorFace R A 0 0 (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun j : Fin 2 => if j = 0 then 1 else x 0) := by
  sorry

theorem relativeTensorFace_one_pure (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (x : Fin 1 → A) :
    relativeTensorFace R A 0 1 (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun j : Fin 2 => if j = 0 then x 0 else 1) := by
  sorry

theorem relativeTensorDegeneracy_zero_pure (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (x : Fin 2 → A) :
    relativeTensorDegeneracy R A 0 0 (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun _ : Fin 1 => x 0 * x 1) := by
  sorry

/- The general `relativeTensorMap_pure` statement above is the
source-faithful formulation for arbitrary simplex maps.  These named
specializations record the remaining low-degree maps displayed in the
source, so the first part of the Amitsur diagram is available without
unfolding the simplex maps. -/

theorem relativeTensorFace_two_zero_pure (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (x : Fin 2 → A) :
    relativeTensorFace R A 1 0 (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun j : Fin 3 ↦
        if j = 0 then 1 else if j = 1 then x 0 else x 1) := by
  sorry

theorem relativeTensorFace_two_one_pure (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (x : Fin 2 → A) :
    relativeTensorFace R A 1 1 (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun j : Fin 3 ↦
        if j = 0 then x 0 else if j = 1 then 1 else x 1) := by
  sorry

theorem relativeTensorFace_two_two_pure (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (x : Fin 2 → A) :
    relativeTensorFace R A 1 2 (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun j : Fin 3 ↦
        if j = 0 then x 0 else if j = 1 then x 1 else 1) := by
  sorry

theorem relativeTensorDegeneracy_one_zero_pure (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (x : Fin 3 → A) :
    relativeTensorDegeneracy R A 1 0 (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun j : Fin 2 ↦
        if j = 0 then x 0 * x 1 else x 2) := by
  sorry

theorem relativeTensorDegeneracy_one_one_pure (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (x : Fin 3 → A) :
    relativeTensorDegeneracy R A 1 1 (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun j : Fin 2 ↦
        if j = 0 then x 0 else x 1 * x 2) := by
  sorry

/-! ## Modules over the Amitsur terms -/

/-- The degree-`n` module obtained by tensoring an `R`-module with the
`(n + 1)`-fold Amitsur tensor power. -/
abbrev relativeTensorModule (R A M : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] (n : ℕ) : Type u :=
  TensorProduct R (relativeTensorProduct R A n) M

/- The degreewise term of the extended complex specializes to the
corresponding Amitsur algebra when the coefficient module is the base ring. -/
def relativeTensorModuleBaseRingEquiv (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) :
    relativeTensorModule R A R n ≃ₗ[R] relativeTensorProduct R A n :=
  TensorProduct.rid R (relativeTensorProduct R A n)

@[simp]
theorem relativeTensorModuleBaseRingEquiv_tmul (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] (n : ℕ)
    (x : relativeTensorProduct R A n) (r : R) :
    relativeTensorModuleBaseRingEquiv R A n (x ⊗ₜ[R] r) = r • x := by
  rfl

/- The transition map on the displayed tensor-product module presentation.
This is the tensor product of the Amitsur ring map with the identity on `M`;
the corresponding semilinear form is recorded below. -/
def relativeTensorModuleMap (R A M : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M]
    {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    relativeTensorModule R A M n →ₗ[R] relativeTensorModule R A M m :=
  TensorProduct.map (σ₁₂ := RingHom.id R)
    (relativeTensorMap R A φ).toLinearMap
    (LinearMap.id : M →ₗ[R] M)

theorem relativeTensorModuleMap_smul (R A M : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M]
    {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (a : relativeTensorProduct R A n) (x : relativeTensorModule R A M n) :
    relativeTensorModuleMap R A M φ (a • x) =
      relativeTensorMap R A φ a • relativeTensorModuleMap R A M φ x := by
  sorry

/- The degreewise module map is semilinear for the corresponding Amitsur
ring map.  Its additive function is the canonical tensor-product map; the
scalar-compatibility field is the usual module-over-the-degree-ring fact. -/
noncomputable def relativeTensorModuleMapSemilinear (R A M : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    relativeTensorModule R A M n →ₛₗ[(relativeTensorMap R A φ).toRingHom]
      relativeTensorModule R A M m :=
  { toFun := relativeTensorModuleMap R A M φ
    map_add' := by intros; simp
    map_smul' := relativeTensorModuleMap_smul R A M φ }

theorem relativeTensorModuleMap_tmul (R A M : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M]
    {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (a : relativeTensorProduct R A n) (m' : M) :
    relativeTensorModuleMap R A M φ (a ⊗ₜ[R] m') =
      relativeTensorMap R A φ a ⊗ₜ[R] m' := by
  rfl

theorem relativeTensorModuleMapSemilinear_tmul (R A M : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (a : relativeTensorProduct R A n) (m' : M) :
    relativeTensorModuleMapSemilinear R A M φ (a ⊗ₜ[R] m') =
      relativeTensorMap R A φ a ⊗ₜ[R] m' := by
  rfl

def relativeTensorModuleFace (R A M : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] (n : ℕ) (i : Fin (n + 2)) :
    relativeTensorModule R A M n →ₗ[R] relativeTensorModule R A M (n + 1) :=
  relativeTensorModuleMap R A M (SimplexCategory.δ i)

def relativeTensorModuleDegeneracy (R A M : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] (n : ℕ) (i : Fin (n + 1)) :
    relativeTensorModule R A M (n + 1) →ₗ[R] relativeTensorModule R A M n :=
  relativeTensorModuleMap R A M (SimplexCategory.σ i)

noncomputable def relativeTensorCosimplicialModule (R A M : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M] :
    CosimplicialObject (ModuleCat R) where
  obj n := ModuleCat.of R (relativeTensorModule R A M n.len)
  map φ := ModuleCat.ofHom (relativeTensorModuleMap R A M φ)
  map_id := by sorry
  map_comp := by sorry

theorem relativeTensorCosimplicialModule_exists (R A M : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M] :
    Nonempty (CosimplicialObject.{u, u + 1} (ModuleCat R)) :=
  ⟨relativeTensorCosimplicialModule R A M⟩

/- The presentation condition records that the chosen cosimplicial module is
the one obtained by tensoring the Amitsur algebra object with `M`, including
its transition maps. -/
def RelativeTensorCosimplicialModulePresentation (R A M : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    (X : CosimplicialObject (ModuleCat R)) : Prop :=
  ∃ e : ∀ n : ℕ,
      X.obj (SimplexCategory.mk n) ≅
        ModuleCat.of R (relativeTensorModule R A M n),
    ∀ {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m),
      (e n).inv ≫ X.map φ ≫ (e m).hom =
        ModuleCat.ofHom (relativeTensorModuleMap R A M φ)

theorem relativeTensorCosimplicialModule_presentation (R A M : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M] :
    RelativeTensorCosimplicialModulePresentation R A M
      (relativeTensorCosimplicialModule R A M) := by
  sorry

theorem relativeTensorCosimplicialModule_degree (R A M : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    (n : ℕ) :
    Nonempty ((relativeTensorCosimplicialModule R A M).obj (SimplexCategory.mk n) ≅
      ModuleCat.of R (relativeTensorModule R A M n)) :=
  ⟨by simpa [relativeTensorCosimplicialModule] using
      (Iso.refl (ModuleCat.of R (relativeTensorModule R A M n)))⟩

/-! ## Descent data and their morphisms -/

section DescentData

variable {R A N N' : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

/- The source's `τ` maps are the canonical simplex maps supplied by
Mathlib.  Naming them here keeps the tensor-position notation visible in
the chapter interface. -/

def descentVertexSimplexMap (n : ℕ) (i : Fin (n + 1)) :
    SimplexCategory.mk 0 ⟶ SimplexCategory.mk n :=
  SimplexCategory.const _ _ i

def descentEdgeSimplexMap {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    SimplexCategory.mk 1 ⟶ SimplexCategory.mk n :=
  SimplexCategory.mkOfLe i j h

/-- The two tensor-factor actions on `N ⊗[R] A`, and the corresponding actions
on `A ⊗[R] N`, written without introducing an ambiguous global bimodule instance. -/
def descentComparisonCompatible
    (φ : TensorProduct R N A ≃ₗ[R] TensorProduct R A N) : Prop :=
  (∀ a x, φ (TensorProduct.map (Algebra.lsmul (A := A) R R N a)
      (LinearMap.id : A →ₗ[R] A) x) =
    TensorProduct.map (Algebra.lsmul (A := A) R R A a)
      (LinearMap.id : N →ₗ[R] N) (φ x)) ∧
  (∀ a x, φ (TensorProduct.map (LinearMap.id : N →ₗ[R] N)
      (Algebra.lsmul (A := A) R R A a) x) =
    TensorProduct.map (LinearMap.id : A →ₗ[R] A)
      (Algebra.lsmul (A := A) R R N a) (φ x))

/-- The first map in the cocycle diagram. -/
def descentPhi01
    (φ : TensorProduct R N A ≃ₗ[R] TensorProduct R A N) :
    TensorProduct R (TensorProduct R N A) A ≃ₗ[R]
      TensorProduct R A (TensorProduct R N A) :=
  (TensorProduct.congr φ (LinearEquiv.refl R A)).trans
    (TensorProduct.assoc R A N A)

/-- The second map in the cocycle diagram. -/
def descentPhi12
    (φ : TensorProduct R N A ≃ₗ[R] TensorProduct R A N) :
    TensorProduct R A (TensorProduct R N A) ≃ₗ[R]
      TensorProduct R A (TensorProduct R A N) :=
  TensorProduct.congr (LinearEquiv.refl R A) φ

/-- The direct map from the first to the third tensor position. -/
def descentPhi02
    (φ : TensorProduct R N A ≃ₗ[R] TensorProduct R A N) :
    TensorProduct R (TensorProduct R N A) A ≃ₗ[R]
      TensorProduct R A (TensorProduct R A N) :=
  (((((TensorProduct.assoc R N A A).trans
      (TensorProduct.congr (LinearEquiv.refl R N) (TensorProduct.comm R A A))).trans
        (TensorProduct.assoc R N A A).symm).trans
          (TensorProduct.congr φ (LinearEquiv.refl R A))).trans
            (TensorProduct.assoc R A N A)).trans
              (TensorProduct.congr (LinearEquiv.refl R A) (TensorProduct.comm R N A))

/-- The cocycle condition for a comparison isomorphism. -/
def descentCocycle
    (φ : TensorProduct R N A ≃ₗ[R] TensorProduct R A N) : Prop :=
  (descentPhi01 φ).trans (descentPhi12 φ) = descentPhi02 φ

/-- A descent datum `(N, φ)` for the algebra `A` over `R`. -/
structure DescentDatum where
  comparison : TensorProduct R N A ≃ₗ[R] TensorProduct R A N
  comparison_compatible : descentComparisonCompatible comparison
  cocycle : descentCocycle comparison

/-- Compatibility of an `A`-linear map with the two descent comparisons. -/
def descentMorphismCompatibility
    (D : DescentDatum (R := R) (A := A) (N := N))
    (D' : DescentDatum (R := R) (A := A) (N := N'))
    (f : N →ₗ[A] N') : Prop :=
  D'.comparison.toLinearMap.comp
      (TensorProduct.map (R := R) (f.restrictScalars R)
        (LinearMap.id : A →ₗ[R] A)) =
    (TensorProduct.map (R := R) (LinearMap.id : A →ₗ[R] A)
      (f.restrictScalars R)).comp
      D.comparison.toLinearMap

/-- A morphism of descent data. -/
structure DescentDatumHom
    (D : DescentDatum (R := R) (A := A) (N := N))
    (D' : DescentDatum (R := R) (A := A) (N := N')) where
  hom : N →ₗ[A] N'
  commutes : descentMorphismCompatibility D D' hom

end DescentData

/-! ## The modules in each cosimplicial degree -/

section Terms

variable {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- The tensor product of `n` copies of `A`, written recursively so that it
can be used as the tail of the literal source presentation. -/
def descentAllTensorModule (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) : ModuleCat R :=
  ModuleCat.of R (relativeTensorPower R A n)

/-- `N_{n,i}`, with `N` literally in position `i` and `A` in all other
positions. -/
def descentTermModule (R A N : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] :
    (n : ℕ) → Fin (n + 1) → ModuleCat R
  | 0, _ => ModuleCat.of R N
  | n + 1, ⟨0, _⟩ =>
      ModuleCat.of R (TensorProduct R N (descentAllTensorModule R A n))
  | n + 1, ⟨i + 1, hi⟩ =>
      ModuleCat.of R (TensorProduct R A
        (descentTermModule R A N n ⟨i, Nat.lt_of_succ_lt_succ hi⟩))

abbrev descentTerm (R A N : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (n : ℕ) (i : Fin (n + 1)) : Type u :=
  descentTermModule R A N n i

/- The source regards `N_{n,i}` as a module over the full Amitsur ring in
degree `n`.  The recursive carrier above is retained as the convenient
`R`-module presentation; this instance supplies the degree-ring action needed
for its semilinear transition maps. -/
theorem descentTermModuleOver_exists (n : ℕ) (i : Fin (n + 1)) :
    Nonempty (Module (relativeTensorProduct R A n) (descentTerm R A N n i)) := by
  sorry

noncomputable instance descentTermModuleOver (n : ℕ) (i : Fin (n + 1)) :
    Module (relativeTensorProduct R A n) (descentTerm R A N n i) :=
  Classical.choice (descentTermModuleOver_exists (R := R) (A := A) (N := N) n i)

/-- The degree-zero normal form is canonically the original module. -/
def descentTermZeroEquiv (R A N : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (i : Fin 1) : descentTerm R A N 0 i ≃ₗ[R] N :=
  LinearEquiv.refl R N

def descentUnitTensorPlaced (R A N : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] :
    ∀ (n : ℕ) (i : Fin (n + 1)), N → descentTerm R A N n i
  | 0, _, x => x
  | n + 1, ⟨0, _⟩, x =>
      TensorProduct.mk R N (relativeTensorPower R A n) x 1
  | n + 1, ⟨i + 1, hi⟩, x =>
      TensorProduct.mk R A (descentTerm R A N n ⟨i, Nat.lt_of_succ_lt_succ hi⟩) 1
        (descentUnitTensorPlaced R A N n ⟨i, Nat.lt_of_succ_lt_succ hi⟩ x)

theorem descentTransportMap_exists {n : ℕ} {i j : Fin (n + 1)}
    (D : DescentDatum (R := R) (A := A) (N := N)) (h : i ≤ j) :
    Nonempty (descentTerm R A N n i ≃ₗ[R] descentTerm R A N n j) := by
  sorry

noncomputable def descentTransportMap {n : ℕ} {i j : Fin (n + 1)}
    (D : DescentDatum (R := R) (A := A) (N := N)) (h : i ≤ j) :
    descentTerm R A N n i ≃ₗ[R] descentTerm R A N n j :=
  Classical.choice (descentTransportMap_exists D h)

theorem descentTransportMapOver_exists {n : ℕ} {i j : Fin (n + 1)}
    (D : DescentDatum (R := R) (A := A) (N := N)) (h : i ≤ j) :
    Nonempty (descentTerm R A N n i ≃ₗ[relativeTensorProduct R A n]
      descentTerm R A N n j) := by
  sorry

noncomputable def descentTransportMapOver {n : ℕ} {i j : Fin (n + 1)}
    (D : DescentDatum (R := R) (A := A) (N := N)) (h : i ≤ j) :
    descentTerm R A N n i ≃ₗ[relativeTensorProduct R A n]
      descentTerm R A N n j :=
  Classical.choice (descentTransportMapOver_exists D h)

theorem descentTransportMapOver_refl {n : ℕ} (D : DescentDatum (R := R) (A := A) (N := N))
    (i : Fin (n + 1)) :
    descentTransportMapOver D (le_refl i) =
      LinearEquiv.refl (relativeTensorProduct R A n)
        (descentTerm R A N n i) := by
  sorry

theorem descentTransportMap_unit {n : ℕ} {i j : Fin (n + 1)}
    (D : DescentDatum (R := R) (A := A) (N := N)) (h : i ≤ j) (x : N) :
    descentTransportMap D h (descentUnitTensorPlaced R A N n i x) =
      descentUnitTensorPlaced R A N n j x := by
  sorry

/-- The pure tensor with `x` in position `i` and units elsewhere. -/
def descentUnitTensor {n : ℕ} (i : Fin (n + 1)) (x : N) : descentTerm R A N n i :=
  descentUnitTensorPlaced R A N n i x

theorem descentReindexMap_exists {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1)) :
    Nonempty (descentTerm R A N n i →ₗ[R]
      descentTerm R A N m (β.toOrderHom i)) := by
  sorry

noncomputable def descentReindexMap {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1)) :
    descentTerm R A N n i →ₗ[R]
      descentTerm R A N m (β.toOrderHom i) :=
  Classical.choice (descentReindexMap_exists D β i)

/- The source's `N_{β,i}` is semilinear for the Amitsur ring map.  This is the
exact interface; the preceding `R`-linear map is its underlying shadow. -/
theorem descentReindexMap_semilinear_exists {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1)) :
    Nonempty (descentTerm R A N n i →ₛₗ[(relativeTensorMap R A β).toRingHom]
      descentTerm R A N m (β.toOrderHom i)) := by
  sorry

noncomputable def descentReindexMapSemilinear {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1)) :
    descentTerm R A N n i →ₛₗ[(relativeTensorMap R A β).toRingHom]
      descentTerm R A N m (β.toOrderHom i) :=
  Classical.choice (descentReindexMap_semilinear_exists D β i)

/- The transition map on the normal form `N_{n,n}` is obtained by first
reindexing the distinguished factor and then transporting it to the last
position. -/
noncomputable def descentCosimplicialModuleMap {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    descentTerm R A N n ⟨n, Nat.lt_succ_self n⟩ →ₗ[R]
      descentTerm R A N m ⟨m, Nat.lt_succ_self m⟩ :=
  (descentTransportMap D (Fin.le_last _)).toLinearMap.comp
    (descentReindexMap D β ⟨n, Nat.lt_succ_self n⟩)

/- The first displayed module maps in the source, in the recursive tensor
presentation of `descentTerm`, are made explicit here.  The general
construction above is the usable interface for arbitrary simplex maps. -/

theorem descentCosimplicialModuleMap_face_zero (D : DescentDatum (R := R) (A := A) (N := N))
    (n : N) :
    descentCosimplicialModuleMap D
        (SimplexCategory.δ 0 : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1) n =
      TensorProduct.mk R A N 1 n := by
  sorry

theorem descentCosimplicialModuleMap_face_one (D : DescentDatum (R := R) (A := A) (N := N))
    (n : N) :
    descentCosimplicialModuleMap D
        (SimplexCategory.δ 1 : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1) n =
      D.comparison (TensorProduct.mk R N A n 1) := by
  sorry

theorem descentCosimplicialModuleMap_degeneracy_zero
    (D : DescentDatum (R := R) (A := A) (N := N)) (a : A) (n : N) :
    descentCosimplicialModuleMap D
        (SimplexCategory.σ 0 : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 0)
        (TensorProduct.mk R A N a n) = a • n := by
  sorry

theorem descentCosimplicialModuleMap_face_two_zero
    (D : DescentDatum (R := R) (A := A) (N := N)) (a : A) (n : N) :
    descentCosimplicialModuleMap D
        (SimplexCategory.δ 0 : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2)
        (TensorProduct.mk R A N a n) =
      TensorProduct.mk R A (TensorProduct R A N) 1
        (TensorProduct.mk R A N a n) := by
  sorry

theorem descentCosimplicialModuleMap_face_two_one
    (D : DescentDatum (R := R) (A := A) (N := N)) (a : A) (n : N) :
    descentCosimplicialModuleMap D
        (SimplexCategory.δ 1 : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2)
        (TensorProduct.mk R A N a n) =
      TensorProduct.mk R A (TensorProduct R A N) a
        (TensorProduct.mk R A N 1 n) := by
  sorry

theorem descentCosimplicialModuleMap_face_two_two
    (D : DescentDatum (R := R) (A := A) (N := N)) (a : A) (n : N) :
    descentCosimplicialModuleMap D
        (SimplexCategory.δ 2 : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2)
        (TensorProduct.mk R A N a n) =
      TensorProduct.map (LinearMap.id : A →ₗ[R] A)
        D.comparison.toLinearMap
        (TensorProduct.mk R A (TensorProduct R N A) a
          (TensorProduct.mk R N A n 1)) := by
  sorry

theorem descentCosimplicialModuleMap_degeneracy_one_zero
    (D : DescentDatum (R := R) (A := A) (N := N)) (a₀ a₁ : A) (n : N) :
    descentCosimplicialModuleMap D
        (SimplexCategory.σ 0 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 1)
        (TensorProduct.mk R A (TensorProduct R A N) a₀
          (TensorProduct.mk R A N a₁ n)) =
      TensorProduct.mk R A N (a₀ * a₁) n := by
  sorry

theorem descentCosimplicialModuleMap_degeneracy_one_one
    (D : DescentDatum (R := R) (A := A) (N := N)) (a₀ a₁ : A) (n : N) :
    descentCosimplicialModuleMap D
        (SimplexCategory.σ 1 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 1)
        (TensorProduct.mk R A (TensorProduct R A N) a₀
          (TensorProduct.mk R A N a₁ n)) =
      TensorProduct.mk R A N a₀ (a₁ • n) := by
  sorry

theorem descentCosimplicialModuleMap_semilinear_exists {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    Nonempty (descentTerm R A N n ⟨n, Nat.lt_succ_self n⟩ →ₛₗ[(relativeTensorMap R A β).toRingHom]
      descentTerm R A N m ⟨m, Nat.lt_succ_self m⟩) := by
  sorry

/- The source's cosimplicial transition is the semilinear map above; its
underlying `R`-linear map is the presentation used by the categorical object. -/
noncomputable def descentCosimplicialModuleMapSemilinear {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    descentTerm R A N n ⟨n, Nat.lt_succ_self n⟩ →ₛₗ[(relativeTensorMap R A β).toRingHom]
      descentTerm R A N m ⟨m, Nat.lt_succ_self m⟩ :=
  Classical.choice (descentCosimplicialModuleMap_semilinear_exists D β)

theorem descentReindexMapSemilinear_apply {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1))
    (x : descentTerm R A N n i) :
    descentReindexMapSemilinear D β i x = descentReindexMap D β i x := by
  sorry

theorem descentCosimplicialModuleMapSemilinear_apply {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (x : descentTerm R A N n ⟨n, Nat.lt_succ_self n⟩) :
    descentCosimplicialModuleMapSemilinear D β x =
      descentCosimplicialModuleMap D β x := by
  sorry

theorem descentReindexMap_unit {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1)) (x : N) :
    descentReindexMap D β i (descentUnitTensor i x) =
      descentUnitTensor (β.toOrderHom i) x := by
  sorry

theorem descentReindexMapSemilinear_unit {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1)) (x : N) :
    descentReindexMapSemilinear D β i (descentUnitTensor i x) =
      descentUnitTensor (β.toOrderHom i) x := by
  sorry

noncomputable def descentCosimplicialModule
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    CosimplicialObject (ModuleCat R) where
  obj n := ModuleCat.of R (descentTerm R A N n.len
    ⟨n.len, Nat.lt_succ_self n.len⟩)
  map β := ModuleCat.ofHom (descentCosimplicialModuleMap D β)
  map_id := by sorry
  map_comp := by sorry

theorem descentCosimplicialModule_exists
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    Nonempty (CosimplicialObject.{u, u + 1} (ModuleCat R)) :=
  ⟨descentCosimplicialModule D⟩

theorem descentCosimplicialModule_degree
    (D : DescentDatum (R := R) (A := A) (N := N)) (n : ℕ) :
    Nonempty ((descentCosimplicialModule D).obj (SimplexCategory.mk n) ≅
      descentTermModule R A N n ⟨n, Nat.lt_succ_self n⟩) := by
  exact ⟨by simpa [descentCosimplicialModule] using
    (Iso.refl (descentTermModule R A N n ⟨n, Nat.lt_succ_self n⟩))⟩

theorem descentCosimplicialModule_functorial
    {N' : Type u} [AddCommGroup N'] [Module R N'] [Module A N']
    [IsScalarTower R A N']
    (D : DescentDatum (R := R) (A := A) (N := N))
    (D' : DescentDatum (R := R) (A := A) (N := N'))
    (f : DescentDatumHom D D') :
    Nonempty (descentCosimplicialModule D ⟶ descentCosimplicialModule D') := by
  sorry

def DescentCosimplicialModulePresentation
    (D : DescentDatum (R := R) (A := A) (N := N))
    (X : CosimplicialObject (ModuleCat R)) : Prop :=
  ∃ e : ∀ n : ℕ,
      X.obj (SimplexCategory.mk n) ≅
        descentTermModule R A N n ⟨n, Nat.lt_succ_self n⟩,
    ∀ {n m : ℕ} (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m),
      (e n).inv ≫ X.map β ≫ (e m).hom =
        ModuleCat.ofHom (descentCosimplicialModuleMap D β)

theorem descentCosimplicialModule_presentation
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    DescentCosimplicialModulePresentation D (descentCosimplicialModule D) := by
  sorry

/- The two low-degree identities used in the source proof of the
cosimplicial construction. -/
theorem descentCosimplicialModule_degeneracy_face_zero
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    (descentCosimplicialModuleMap D
      (SimplexCategory.σ 0 : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 0)).comp
      (descentCosimplicialModuleMap D
        (SimplexCategory.δ 0 : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1)) =
      LinearMap.id := by
  sorry

theorem descentCosimplicialModule_degeneracy_face_one
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    (descentCosimplicialModuleMap D
      (SimplexCategory.σ 0 : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 0)).comp
      (descentCosimplicialModuleMap D
        (SimplexCategory.δ 1 : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1)) =
      LinearMap.id := by
  sorry

end Terms

/-! ## Canonical data and effectivity -/

section Canonical

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- The comparison map for the canonical datum.  We use the commuted normal
form `A ⊗[R] M` for the source's `M ⊗[R] A`; the commutation equivalence is
part of the canonical identification. -/
def canonicalDescentComparison :
    TensorProduct R (TensorProduct R A M) A ≃ₗ[R]
      TensorProduct R A (TensorProduct R A M) :=
  (TensorProduct.assoc R A M A).trans
    (TensorProduct.congr (LinearEquiv.refl R A) (TensorProduct.comm R M A))

theorem canonicalDescentComparison_tmul (a₀ a₁ : A) (m : M) :
    canonicalDescentComparison (R := R) (A := A) (M := M)
        ((a₀ ⊗ₜ[R] m) ⊗ₜ[R] a₁) =
      a₀ ⊗ₜ[R] (a₁ ⊗ₜ[R] m) := by
  rfl

noncomputable def canonicalDescentDatum :
    DescentDatum (R := R) (A := A) (N := TensorProduct R A M) :=
  { comparison := canonicalDescentComparison (R := R) (A := A) (M := M)
    comparison_compatible := by sorry
    cocycle := by sorry }

theorem canonicalDescentDatum_exists :
    ∃ D : DescentDatum (R := R) (A := A) (N := TensorProduct R A M),
      D.comparison = canonicalDescentComparison (R := R) (A := A) (M := M) :=
  ⟨canonicalDescentDatum (R := R) (A := A) (M := M), rfl⟩

theorem canonicalDescentDatum_comparison :
    (canonicalDescentDatum (R := R) (A := A) (M := M)).comparison =
      canonicalDescentComparison (R := R) (A := A) (M := M) :=
  rfl

def DescentDatumIsoCompatibility {N N' : Type*} [AddCommGroup N] [Module R N]
    [Module A N] [IsScalarTower R A N]
    [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
    (D : DescentDatum (R := R) (A := A) (N := N))
    (D' : DescentDatum (R := R) (A := A) (N := N')) (e : N ≃ₗ[A] N') : Prop :=
  descentMorphismCompatibility D D' e

structure DescentDatumIso {N N' : Type*} [AddCommGroup N] [Module R N]
    [Module A N] [IsScalarTower R A N]
    [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
    (D : DescentDatum (R := R) (A := A) (N := N))
    (D' : DescentDatum (R := R) (A := A) (N := N')) where
  hom : N ≃ₗ[A] N'
  commutes : DescentDatumIsoCompatibility D D' hom

/-- Effectivity means isomorphism to the canonical datum obtained by extension
of scalars from an `R`-module. -/
def DescentDatum.IsEffective {N : Type*} [AddCommGroup N] [Module R N]
    [Module A N] [IsScalarTower R A N]
    (D : DescentDatum (R := R) (A := A) (N := N)) : Prop :=
  ∃ (M : Type w) (_ : AddCommGroup M) (_ : Module R M),
    Nonempty (DescentDatumIso (canonicalDescentDatum (R := R) (A := A) (M := M)) D)

end Canonical

/- The following degreewise statement is stated in the fixed universe used by
the concrete cosimplicial-module interface above. -/
theorem canonicalDescentCosimplicialModule_degree (R A M : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] (n : ℕ) :
    Nonempty ((descentCosimplicialModule
      (canonicalDescentDatum (R := R) (A := A) (M := M))).obj
        (SimplexCategory.mk n) ≅
      ModuleCat.of R (relativeTensorModule R A M n)) := by
  sorry

theorem canonicalDescentCosimplicialModule_iso (R A M : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] :
    Nonempty (descentCosimplicialModule
      (canonicalDescentDatum (R := R) (A := A) (M := M)) ≅
      relativeTensorCosimplicialModule R A M) := by
  sorry

/-! ## Complexes, exactness, and effectivity -/

section Complexes

variable {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

def descentCochainDegreeModule
    (_D : DescentDatum (R := R) (A := A) (N := N)) (n : ℕ) : ModuleCat R :=
  match n with
  | 0 => ModuleCat.of R N
  | n + 1 => descentTermModule R A N (n + 1) ⟨n + 1, Nat.lt_succ_self (n + 1)⟩

/-- The first differential in the source's displayed complex. -/
noncomputable def descentFirstMap
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    N →ₗ[R] TensorProduct R A N :=
  TensorProduct.mk R A N 1 -
    D.comparison.toLinearMap.comp ((TensorProduct.mk R N A).flip 1)

def DescentCochainComplexFirstCompatibility
    (D : DescentDatum (R := R) (A := A) (N := N))
    (K : CochainComplex (ModuleCat.{u, u} R) ℕ) : Prop :=
  ∃ (e₀ : K.X 0 ≅ ModuleCat.of R N)
    (e₁ : K.X 1 ≅ ModuleCat.of R (TensorProduct R A N)),
    e₀.inv ≫ K.d 0 1 ≫ e₁.hom = ModuleCat.ofHom (descentFirstMap D)

def DescentCochainComplexShape
    (D : DescentDatum (R := R) (A := A) (N := N))
    (K : CochainComplex (ModuleCat.{u, u} R) ℕ) : Prop :=
  (∀ n : ℕ, Nonempty (K.X n ≅ descentCochainDegreeModule D n)) ∧
    DescentCochainComplexFirstCompatibility D K

/-- The alternating coface complex of the cosimplicial module attached to `D`.

This uses Mathlib's source-faithful alternating-sum construction, so the higher
differentials are actual alternating sums of all cofaces rather than a
choice-backed complex with only its first differential specified. -/
noncomputable def descentCochainComplex
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    CochainComplex (ModuleCat.{u, u} R) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj
    (descentCosimplicialModule D)

theorem descentCochainComplex_shape
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    DescentCochainComplexShape D (descentCochainComplex D) := by
  sorry

theorem descentCochainComplex_first_compatibility
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    DescentCochainComplexFirstCompatibility D (descentCochainComplex D) :=
  (descentCochainComplex_shape D).2

/-- The second differential in the source's displayed complex. -/
noncomputable def descentSecondMap
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    TensorProduct R A N →ₗ[R] TensorProduct R A (TensorProduct R A N) :=
  let first := (TensorProduct.assoc R A A N).toLinearMap.comp
    (TensorProduct.map (TensorProduct.mk R A A 1)
      (LinearMap.id : N →ₗ[R] N))
  let second := (TensorProduct.assoc R A A N).toLinearMap.comp
    (TensorProduct.map ((TensorProduct.mk R A A).flip 1)
      (LinearMap.id : N →ₗ[R] N))
  let third := TensorProduct.map (LinearMap.id : A →ₗ[R] A)
    (D.comparison.toLinearMap.comp ((TensorProduct.mk R N A).flip 1))
  first - second + third

theorem descentSecondMap_on_pure (D : DescentDatum (R := R) (A := A) (N := N)) :
    ∀ a n, descentSecondMap D (TensorProduct.mk R A N a n) =
      TensorProduct.mk R A (TensorProduct R A N) 1
          (TensorProduct.mk R A N a n) -
        TensorProduct.mk R A (TensorProduct R A N) a
          (TensorProduct.mk R A N 1 n) +
        TensorProduct.map (LinearMap.id : A →ₗ[R] A)
          D.comparison.toLinearMap
          (TensorProduct.mk R A (TensorProduct R N A) a
            (TensorProduct.mk R N A n 1)) := by
  sorry

/-- `H⁰(s(N_•)) = {n | 1 ⊗ n = φ(n ⊗ 1)}` as an `R`-submodule. -/
def descentH0 (D : DescentDatum (R := R) (A := A) (N := N)) : Submodule R N :=
  (descentFirstMap D).ker

theorem mem_descentH0_iff (D : DescentDatum (R := R) (A := A) (N := N)) (n : N) :
    n ∈ descentH0 D ↔
      TensorProduct.mk R A N 1 n = D.comparison (TensorProduct.mk R N A n 1) := by
  sorry

theorem descent_complex_first_map (D : DescentDatum (R := R) (A := A) (N := N)) :
    ∀ n : N, descentFirstMap D n =
      TensorProduct.mk R A N 1 n - D.comparison (TensorProduct.mk R N A n 1) := by
  intro n
  rfl

/-- The augmentation in the source's extended complex, in the canonical
`A ⊗[R] M` presentation. -/
def canonicalAugmentationMap (M : Type u) [AddCommGroup M] [Module R M] :
    M →ₗ[R] TensorProduct R A M :=
  TensorProduct.mk R A M 1

theorem canonicalAugmentationMap_apply (M : Type u) [AddCommGroup M] [Module R M]
    (m : M) : canonicalAugmentationMap (R := R) (A := A) M m =
      TensorProduct.mk R A M 1 m := rfl

noncomputable def canonicalDescentZeroIso (M : Type u) [AddCommGroup M] [Module R M] :
    (descentCochainComplex (canonicalDescentDatum (R := R) (A := A) (M := M))).X 0 ≅
      ModuleCat.of R (TensorProduct R A M) :=
  Classical.choice (descentCosimplicialModule_degree
    (canonicalDescentDatum (R := R) (A := A) (M := M)) 0)

noncomputable def canonicalAugmentation (M : Type u) [AddCommGroup M] [Module R M] :
    ModuleCat.of R M ⟶
      (descentCochainComplex (canonicalDescentDatum (R := R) (A := A) (M := M))).X 0 :=
  ModuleCat.ofHom <|
    (canonicalDescentZeroIso (R := R) (A := A) M).inv.hom.comp
      (canonicalAugmentationMap (R := R) (A := A) M)

theorem canonicalAugmentation_exists (M : Type u) [AddCommGroup M] [Module R M] :
    Nonempty (ModuleCat.of R M ⟶
      (descentCochainComplex (canonicalDescentDatum (R := R) (A := A) (M := M))).X 0) :=
  ⟨canonicalAugmentation (R := R) (A := A) M⟩

/-- Exactness of the extended canonical Amitsur complex, including its
augmentation by `M`. -/
def ExtendedDescentComplexExact (A : Type u) [CommRing A] [Algebra R A]
    (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
    Function.Injective (canonicalAugmentation (R := R) (A := A) M).hom ∧
    (∀ x : (descentCochainComplex
        (canonicalDescentDatum (R := R) (A := A) (M := M))).X 0,
      ((descentCochainComplex
        (canonicalDescentDatum (R := R) (A := A) (M := M))).d 0 1).hom x = 0 →
        ∃ m : M, (canonicalAugmentation (R := R) (A := A) M).hom m = x) ∧
    ∀ n : ℕ,
      HomologicalComplex.ExactAt (C := ModuleCat.{u, u} R) (c := ComplexShape.up ℕ)
        (descentCochainComplex
          (canonicalDescentDatum (R := R) (A := A) (M := M))) n

theorem extended_descent_complex_shape (A : Type u) [CommRing A] [Algebra R A]
    (M : Type u) [AddCommGroup M] [Module R M] :
    Nonempty (CochainComplex (ModuleCat.{u, u} R) ℕ) :=
  ⟨descentCochainComplex
    (canonicalDescentDatum (R := R) (A := A) (M := M))⟩

theorem exact_extended_descent_complex_of_section
    (M : Type u) [AddCommGroup M] [Module R M]
    (σ : A →+* R) (hσ : (algebraMap R A).comp σ = RingHom.id A) :
    ExtendedDescentComplexExact (R := R) (A := A) M := by
  sorry

theorem exact_extended_descent_complex_of_faithfullyFlat
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R A] :
    ExtendedDescentComplexExact (R := R) (A := A) M := by
  sorry

noncomputable def descentCanonicalMap
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    TensorProduct R A (descentH0 D) →ₗ[R] N :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun n => a • (n : N)
          map_add' := by
            intro n₁ n₂
            simp
          map_smul' := by
            intro r n
            exact smul_comm a r (n : N) }
      map_add' := by
        intro a₁ a₂
        ext n
        simp [add_smul]
      map_smul' := by
        intro r a
        ext n
        exact smul_assoc r a (n : N) }

theorem descentCanonicalMap_on_pure
    (D : DescentDatum (R := R) (A := A) (N := N)) (a : A)
    (n : descentH0 D) :
    descentCanonicalMap D (a ⊗ₜ[R] n) = a • (n : N) := by
  rfl

/-! The raw tensor model of the base change used in the proof of descent
along a faithfully flat extension.  The associativity and commutativity
equivalences in `TensorProduct` identify this model with the usual
`(R' ⊗[R] N) ⊗[R'] (R' ⊗[R] A)` presentation. -/

abbrev baseChangedAlgebra (R A R' : Type u) [CommRing R] [CommRing A]
    [CommRing R'] [Algebra R A] [Algebra R R'] : Type u :=
  TensorProduct R R' A

abbrev baseChangedModule (R N R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup N] [Module R N] : Type u :=
  TensorProduct R R' N

/-- The specific base-changed comparison `id_{R'} ⊗ φ` in the raw tensor
model. -/
def baseChangedDescentComparison
    {R A N R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [AddCommGroup N] [Module R N]
    [Module A N] [IsScalarTower R A N]
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    TensorProduct R R' (TensorProduct R N A) ≃ₗ[R]
      TensorProduct R R' (TensorProduct R A N) :=
  TensorProduct.congr (LinearEquiv.refl R R') D.comparison

theorem baseChangedDescentComparison_tmul
    {R A N R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [AddCommGroup N] [Module R N]
    [Module A N] [IsScalarTower R A N]
    (D : DescentDatum (R := R) (A := A) (N := N)) (r' : R') (n : N) (a : A) :
    baseChangedDescentComparison D (r' ⊗ₜ[R] (n ⊗ₜ[R] a)) =
      r' ⊗ₜ[R] D.comparison (n ⊗ₜ[R] a) := by
  rfl

def BaseChangedDescentDataEffective
    (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.FaithfullyFlat R R'] : Prop :=
  let A₀ := TensorProduct R R' A
  letI : Algebra R' A₀ := Algebra.TensorProduct.leftAlgebra
  ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra R' A'),
    ∃ _ : A' ≃ₐ[R'] A₀,
      ∀ (N' : Type u) (_ : AddCommGroup N') (_ : Module R' N')
        (_ : Module A' N') (_ : IsScalarTower R' A' N'),
        ∀ D' : DescentDatum (R := R') (A := A') (N := N'),
          DescentDatum.IsEffective.{u, u, u, u} D'

/-- Every descent datum for the base-changed algebra `R' ⊗[R] A` is effective.
This is the hypothesis in the source's faithfully-flat base-change lemma. -/
def BaseChangedAllDescentDataEffective
    (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.FaithfullyFlat R R'] : Prop :=
  let A' := TensorProduct R R' A
  letI : Algebra R' A' := Algebra.TensorProduct.leftAlgebra
  ∀ (N' : Type u) (_ : AddCommGroup N') (_ : Module R' N')
    (_ : Module A' N') (_ : IsScalarTower R' A' N'),
    ∀ D' : DescentDatum (R := R') (A := A') (N := N'),
      DescentDatum.IsEffective.{u, u, u, u} D'

theorem descent_descends_of_baseChange
    {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.FaithfullyFlat R A]
    (D : DescentDatum (R := R) (A := A) (N := N))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    (h : BaseChangedAllDescentDataEffective R A R') : D.IsEffective := by
  sorry

theorem recognize_effective_descent
    (D : DescentDatum (R := R) (A := A) (N := N))
    [Module.FaithfullyFlat R A] :
    D.IsEffective ↔ Function.Bijective (descentCanonicalMap D) := by
  sorry

theorem descent_effective_after_baseChange
    (D : DescentDatum (R := R) (A := A) (N := N))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    (h : BaseChangedDescentDataEffective R A R') : D.IsEffective := by
  sorry

end Complexes

/-! ## Effective descent proposition -/

/-- The Eilenberg--Moore category for the extension/restriction adjunction.
Its coalgebra objects are the canonical categorical form of descent data. -/
abbrev DescentCoalgebraCategory (R A : Type u) [CommRing R] [CommRing A]
    (f : R →+* A) :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).toComonad.Coalgebra

def DescentModulesEquivalence (R A : Type u) [CommRing R] [CommRing A]
    (f : R →+* A) : Prop :=
  Nonempty (ModuleCat.{u, u} R ≌ DescentCoalgebraCategory R A f)

theorem effective_descent_for_modules (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.FaithfullyFlat R A] {N : Type v} [AddCommGroup N]
    [Module R N] [Module A N] [IsScalarTower R A N]
    (D : DescentDatum (R := R) (A := A) (N := N)) : D.IsEffective := by
  sorry

theorem effective_descent_for_modules_category_equivalence (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A] :
    DescentModulesEquivalence R A (algebraMap R A) := by
  sorry

/-- The inverse in the source's equivalence is the degree-zero equalizer. -/
def descentInverseModule {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (D : DescentDatum (R := R) (A := A) (N := N)) : Submodule R N :=
  descentH0 D

def descentInverseModuleObject {R A N : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N]
    (D : DescentDatum (R := R) (A := A) (N := N)) : ModuleCat R :=
  ModuleCat.of R (descentH0 D)

theorem effective_descent_modules_inverse
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] {N : Type u} [AddCommGroup N]
    [Module R N] [Module A N] [IsScalarTower R A N]
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    descentInverseModule D = descentH0 D := rfl

/-- The three clauses of the source's effective-descent proposition.  The
categorical equivalence is expressed using Mathlib's Eilenberg--Moore
category for the extension/restriction comonad, and the inverse is the
degree-zero equalizer. -/
theorem proposition_descent_module (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A] :
    (∀ (N : Type u) (_ : AddCommGroup N) (_ : Module R N) (_ : Module A N)
      (_ : IsScalarTower R A N),
      ∀ D : DescentDatum (R := R) (A := A) (N := N), D.IsEffective) ∧
      DescentModulesEquivalence R A (algebraMap R A) ∧
      (∀ (N : Type u) (_ : AddCommGroup N) (_ : Module R N) (_ : Module A N)
        (_ : IsScalarTower R A N)
        (D : DescentDatum (R := R) (A := A) (N := N)),
        descentInverseModule D = descentH0 D) := by
  sorry

/-! ## Standard covers -/

abbrev standardCoverAlgebra (R : Type u) [CommRing R] {k : ℕ}
    (f : Fin k → R) : Type u := ∀ i, Localization.Away (f i)

def StandardCoverFaithfullyFlat (R : Type u) [CommRing R] {k : ℕ}
    (f : Fin k → R) : Prop :=
  RingHom.FaithfullyFlat (algebraMap R (standardCoverAlgebra R f))

def standardCoverGeneratesUnit (R : Type u) [CommRing R] {k : ℕ}
    (f : Fin k → R) : Prop :=
  Ideal.span (Set.range f) = ⊤

theorem standardCoverAlgebra_faithfullyFlat (R : Type u) [CommRing R]
    {k : ℕ} (f : Fin k → R) (hf : standardCoverGeneratesUnit R f) :
    StandardCoverFaithfullyFlat R f := by
  sorry

theorem standardCover_cosimplicial_degree (R : Type u) [CommRing R]
    {k : ℕ} (f : Fin k → R) (n : ℕ) :
    Nonempty ((relativeTensorCosimplicialAlgebra R (standardCoverAlgebra R f)).obj
      (SimplexCategory.mk n) ≅
      CommRingCat.of (∀ t : Fin (n + 1) → Fin k,
        Localization.Away (∏ j, f (t j)))) := by
  sorry

theorem standardCover_extended_complex_exact (R : Type u) [CommRing R]
    {k : ℕ} (f : Fin k → R) (hf : standardCoverGeneratesUnit R f)
    (M : Type u) [AddCommGroup M] [Module R M] :
    ExtendedDescentComplexExact (R := R)
      (A := standardCoverAlgebra R f) M := by
  sorry

/-! ## The homotopy-equivalent cosimplicial-algebra remark -/

theorem effective_descent_modules_equivalence (R A : Type u)
    [CommRing R] [CommRing A] (f : R →+* A) (hf : f.FaithfullyFlat) :
    DescentModulesEquivalence R A f := by
  sorry

/-- A cosimplicial module over `A` is represented degreewise by modules over
the degreewise rings, with transition maps obtained by extension of scalars. -/
structure CosimplicialModuleData
    (A : CosimplicialObject CommRingCat.{u}) where
  obj : ∀ n : ℕ, ModuleCat (A.obj (SimplexCategory.mk n))
  transition : ∀ {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m),
    (ModuleCat.extendScalars (A.map φ).hom).obj (obj n) ⟶ obj m

def CartesianTransition
    (M : CosimplicialModuleData A) {n m : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) : Prop :=
  IsIso (M.transition φ)

def CartesianCosimplicialModule
    (M : CosimplicialModuleData A) : Prop :=
  ∀ n m (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m),
    CartesianTransition M φ

/-- Morphisms of the degreewise module data used in the cartesian-module
formulation of descent. -/
@[ext]
structure CosimplicialModuleDataHom
    {A : CosimplicialObject CommRingCat.{u}}
    (M N : CosimplicialModuleData A) where
  app : ∀ n : ℕ, M.obj n ⟶ N.obj n
  naturality : ∀ {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m),
    M.transition φ ≫ app m =
      (ModuleCat.extendScalars (A.map φ).hom).map (app n) ≫ N.transition φ

theorem cosimplicialModuleDataHom_comp_naturality
    {A : CosimplicialObject CommRingCat.{u}}
    {M N P : CosimplicialModuleData A}
    (f : CosimplicialModuleDataHom M N)
    (g : CosimplicialModuleDataHom N P)
    {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    M.transition φ ≫ (f.app m ≫ g.app m) =
      (ModuleCat.extendScalars (A.map φ).hom).map (f.app n ≫ g.app n) ≫
        P.transition φ := by
  sorry

instance {A : CosimplicialObject CommRingCat.{u}} :
    Category (CosimplicialModuleData A) where
  Hom M N := CosimplicialModuleDataHom M N
  id M :=
    { app := fun n => 𝟙 (M.obj n)
      naturality := by
        intro n m φ
        simp }
  comp f g :=
    { app := fun n => f.app n ≫ g.app n
      naturality := cosimplicialModuleDataHom_comp_naturality f g }
  id_comp f := by
    apply CosimplicialModuleDataHom.ext
    funext n
    simp
  comp_id f := by
    apply CosimplicialModuleDataHom.ext
    funext n
    simp
  assoc f g h := by
    apply CosimplicialModuleDataHom.ext
    funext n
    simp [Category.assoc]

/-- The category of cartesian degreewise modules over a cosimplicial algebra. -/
def cartesianModuleProperty (A : CosimplicialObject CommRingCat.{u}) :
    ObjectProperty (CosimplicialModuleData A) :=
  fun M => CartesianCosimplicialModule M

abbrev CartesianModuleCategory (A : CosimplicialObject CommRingCat.{u}) :=
  (cartesianModuleProperty A).FullSubcategory

/-! ## Homotopy and the category of abstract descent data -/

/-- A homotopy between maps of cosimplicial objects, obtained from the
standard simplicial homotopy notion across the simplicial/cosimplicial
anti-equivalence. -/
def CosimplicialHomotopy {C : Type v} [Category.{u} C]
    {X Y : CosimplicialObject C} (f g : X ⟶ Y) : Prop :=
  Nonempty (SimplicialObject.Homotopy
    ((cosimplicialSimplicialEquiv C).functor.map f.op)
    ((cosimplicialSimplicialEquiv C).functor.map g.op))

/-- A homotopy equivalence of cosimplicial objects. -/
structure CosimplicialHomotopyEquivalence {C : Type v} [Category.{u} C]
    (X Y : CosimplicialObject C) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  homotopy_hom_inv : CosimplicialHomotopy (hom ≫ inv) (𝟙 X)
  homotopy_inv_hom : CosimplicialHomotopy (inv ≫ hom) (𝟙 Y)

/-- The constant cosimplicial algebra used in the source's homotopy remark. -/
def constantCosimplicialAlgebra (R : Type u) [CommRing R] :
    CosimplicialObject CommRingCat :=
  (Functor.const SimplexCategory).obj (CommRingCat.of R)

theorem relativeTensorCosimplicialAlgebra_homotopy_equivalence_of_section
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (σ : A →+* R) (hσ : (algebraMap R A).comp σ = RingHom.id A) :
    Nonempty (CosimplicialHomotopyEquivalence
      (relativeTensorCosimplicialAlgebra R A)
      (constantCosimplicialAlgebra R)) := by
  sorry

theorem cartesian_modules_homotopy_invariant
    {X Y : CosimplicialObject CommRingCat.{u}}
    (e : CosimplicialHomotopyEquivalence X Y) :
    (∀ M : CosimplicialModuleData X, CartesianCosimplicialModule M →
      ∃ N : CosimplicialModuleData Y, CartesianCosimplicialModule N) ∧
    (∀ N : CosimplicialModuleData Y, CartesianCosimplicialModule N →
      ∃ M : CosimplicialModuleData X, CartesianCosimplicialModule M) := by
  sorry

theorem descent_data_cartesian_equivalence (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] :
    Nonempty (DescentCoalgebraCategory R A (algebraMap R A) ≌
      CartesianModuleCategory (relativeTensorCosimplicialAlgebra R A)) := by
  sorry

theorem cartesian_modules_homotopy_category_equivalence
    {X Y : CosimplicialObject CommRingCat.{u}}
    (e : CosimplicialHomotopyEquivalence X Y) :
    Nonempty (CartesianModuleCategory X ≌ CartesianModuleCategory Y) := by
  sorry

theorem descent_data_category_equivalence (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    : Nonempty (ModuleCat.{u, u} R ≌
      DescentCoalgebraCategory R A (algebraMap R A)) := by
  sorry

end Formalization.Books.Descent.Unit03
