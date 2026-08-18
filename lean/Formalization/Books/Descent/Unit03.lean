import Mathlib.AlgebraicTopology.CechNerve
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
    ∃ g : relativeTensorProduct R A n →+* relativeTensorProduct R A m,
      ∀ x : Fin (n + 1) → A,
        g (PiTensorProduct.tprod R x) =
          PiTensorProduct.tprod R (fun j : Fin (m + 1) ↦
            Finset.prod (Finset.filter (fun i : Fin (n + 1) ↦ φ.toOrderHom i = j)
              Finset.univ) x) := by
  sorry

noncomputable def relativeTensorMap (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] {n m : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    relativeTensorProduct R A n →+* relativeTensorProduct R A m :=
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

/-! ## Descent data and their morphisms -/

section DescentData

variable {R A N N' : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

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

/-- `N_{n,i}`, with `N` in position `i`. -/
/- We use the normal form `N ⊗ A^(⊗n)`; commutativity and associativity
of tensor products identify this with the source's `N_{n,i}` for every slot.
The slot is retained in the interface because the reindexing maps act on it. -/
abbrev descentTerm (R A N : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (n : ℕ) (_i : Fin (n + 1)) : Type u :=
  TensorProduct R N (relativeTensorPower R A n)

abbrev descentTermModule (R A N : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (n : ℕ) (i : Fin (n + 1)) : ModuleCat R :=
  ModuleCat.of R (descentTerm R A N n i)

/-- The degree-zero normal form is canonically the original module. -/
def descentTermZeroEquiv (R A N : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (i : Fin 1) : descentTerm R A N 0 i ≃ₗ[R] N :=
  (TensorProduct.congr (LinearEquiv.refl R N)
    (PiTensorProduct.isEmptyEquiv (Fin 0) (R := R)
      (s := fun _ : Fin 0 => A))).trans (TensorProduct.rid R N)

theorem descentTransportMap_exists {n : ℕ} {i j : Fin (n + 1)}
    (D : DescentDatum (R := R) (A := A) (N := N)) (h : i ≤ j) :
    Nonempty (descentTerm R A N n i ≃ₗ[R] descentTerm R A N n j) := by
  sorry

noncomputable def descentTransportMap {n : ℕ} {i j : Fin (n + 1)}
    (D : DescentDatum (R := R) (A := A) (N := N)) (h : i ≤ j) :
    descentTerm R A N n i ≃ₗ[R] descentTerm R A N n j :=
  Classical.choice (descentTransportMap_exists D h)

/-- The pure tensor with `x` in position `i` and units elsewhere. -/
def descentUnitTensor {n : ℕ} (i : Fin (n + 1)) (x : N) : descentTerm R A N n i :=
  TensorProduct.mk R N (relativeTensorPower R A n) x 1

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

theorem descentReindexMap_unit {n m : ℕ}
    (D : DescentDatum (R := R) (A := A) (N := N))
    (β : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1)) (x : N) :
    descentReindexMap D β i (descentUnitTensor i x) =
      descentUnitTensor (β.toOrderHom i) x := by
  sorry

theorem descentCosimplicialModule_exists
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    Nonempty (CosimplicialObject (ModuleCat R)) := by
  sorry

noncomputable def descentCosimplicialModule
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    CosimplicialObject (ModuleCat R) :=
  Classical.choice (descentCosimplicialModule_exists D)

theorem descentCosimplicialModule_degree
    (D : DescentDatum (R := R) (A := A) (N := N)) (n : ℕ) :
    Nonempty ((descentCosimplicialModule D).obj (SimplexCategory.mk n) ≅
      descentTermModule R A N n ⟨n, Nat.lt_succ_self n⟩) := by
  sorry

theorem descentCosimplicialModule_functorial
    {N' : Type u} [AddCommGroup N'] [Module R N'] [Module A N']
    [IsScalarTower R A N']
    (D : DescentDatum (R := R) (A := A) (N := N))
    (D' : DescentDatum (R := R) (A := A) (N := N'))
    (f : DescentDatumHom D D') :
    Nonempty (descentCosimplicialModule D ⟶ descentCosimplicialModule D') := by
  sorry

end Terms

/-! ## Canonical data and effectivity -/

section Canonical

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/- The comparison map for the canonical datum.  We use the commuted normal
form `A ⊗[R] M` for the source's `M ⊗[R] A`; the resulting datum is canonically
isomorphic to the displayed source convention. -/
def canonicalDescentComparison :
    TensorProduct R (TensorProduct R A M) A ≃ₗ[R]
      TensorProduct R A (TensorProduct R A M) :=
  (TensorProduct.assoc R A M A).trans
    (TensorProduct.congr (LinearEquiv.refl R A) (TensorProduct.comm R M A))

theorem canonicalDescentDatum_exists :
    ∃ D : DescentDatum (R := R) (A := A) (N := TensorProduct R A M),
      D.comparison = canonicalDescentComparison (R := R) (A := A) (M := M) := by
  sorry

noncomputable def canonicalDescentDatum :
  DescentDatum (R := R) (A := A) (N := TensorProduct R A M) :=
  Classical.choose (canonicalDescentDatum_exists (R := R) (A := A) (M := M))

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
      ModuleCat.of R (TensorProduct R M (relativeTensorProduct R A n))) := by
  sorry

/-! ## Complexes, exactness, and effectivity -/

section Complexes

variable {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

def descentCochainDegreeModule
    (D : DescentDatum (R := R) (A := A) (N := N)) (n : ℕ) : ModuleCat R :=
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

theorem descentCochainComplex_shape_exists
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    Nonempty {K : CochainComplex (ModuleCat.{u, u} R) ℕ //
      DescentCochainComplexShape D K} := by
  sorry

noncomputable def descentCochainComplexChoice
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    {K : CochainComplex (ModuleCat.{u, u} R) ℕ //
      DescentCochainComplexShape D K} :=
  Classical.choice (descentCochainComplex_shape_exists D)

noncomputable def descentCochainComplex
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    CochainComplex (ModuleCat.{u, u} R) ℕ :=
  (descentCochainComplexChoice D).1

theorem descentCochainComplex_shape
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    DescentCochainComplexShape D (descentCochainComplex D) :=
  (descentCochainComplexChoice D).2

theorem descentCochainComplex_first_compatibility
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    DescentCochainComplexFirstCompatibility D (descentCochainComplex D) :=
  (descentCochainComplexChoice D).2.2

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
`A ⊗[R] M` normal form. -/
def canonicalAugmentationMap (M : Type u) [AddCommGroup M] [Module R M] :
    M →ₗ[R] TensorProduct R A M :=
  TensorProduct.mk R A M 1

theorem canonicalAugmentationMap_apply (M : Type u) [AddCommGroup M] [Module R M]
    (m : M) : canonicalAugmentationMap (R := R) (A := A) M m =
      TensorProduct.mk R A M 1 m := rfl

theorem canonicalAugmentation_exists (M : Type u) [AddCommGroup M] [Module R M] :
    Nonempty (ModuleCat.of R M ⟶
      (descentCochainComplex (canonicalDescentDatum (R := R) (A := A) (M := M))).X 0) := by
  sorry

noncomputable def canonicalAugmentation (M : Type u) [AddCommGroup M] [Module R M] :
    ModuleCat.of R M ⟶
      (descentCochainComplex (canonicalDescentDatum (R := R) (A := A) (M := M))).X 0 :=
  Classical.choice (canonicalAugmentation_exists (R := R) M)

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

theorem descentCanonicalMap_exists
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    Nonempty (TensorProduct R A (descentH0 D) →ₗ[R] N) := by
  sorry

noncomputable def descentCanonicalMap
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    TensorProduct R A (descentH0 D) →ₗ[R] N :=
  Classical.choice (descentCanonicalMap_exists D)

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

def DescentModulesEquivalence (R A : Type u) [CommRing R] [CommRing A]
    (f : R →+* A) : Prop :=
  Nonempty (ComonadicLeftAdjoint (ModuleCat.extendScalars.{u, u, u} f))

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
  letI := comonadicExtendScalars hf
  exact ⟨inferInstance⟩

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

end Formalization.Books.Descent.Unit03
