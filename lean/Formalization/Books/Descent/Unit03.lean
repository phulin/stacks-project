import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.PiTensorProduct

/-! # Descent, Chapter 3: Descent for modules -/

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct

namespace Formalization.Books.Descent.Unit03

universe u v

/-! ## Relative tensor powers -/

/-- The `(n + 1)`-fold tensor product of `A` over `R`. -/
abbrev relativeTensorProduct (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) : Type u := ⨂[R] _ : Fin (n + 1), A

theorem relativeTensorCosimplicialAlgebra_exists (R A : Type u)
    [CommRing R] [CommRing A] (f : R →+* A) :
    Nonempty (CosimplicialObject CommRingCat) := by sorry

/-- The cosimplicial algebra `(A/R)_•`; its degree `n` is the relative tensor
power above. -/
noncomputable def relativeTensorCosimplicialAlgebra (R A : Type u)
    [CommRing R] [CommRing A] (f : R →+* A) :
    CosimplicialObject CommRingCat :=
  Classical.choice (relativeTensorCosimplicialAlgebra_exists R A f)

theorem relativeTensorCosimplicialAlgebra_degree (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] (f : R →+* A) (n : ℕ) :
    Nonempty ((relativeTensorCosimplicialAlgebra R A f).obj (SimplexCategory.mk n) ≅
      CommRingCat.of (relativeTensorProduct R A n)) := by sorry

/-- The source's formula for the map attached to `[n] → [m]`, including the
empty-product convention. -/
theorem relativeTensorMap_exists (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (f : R →+* A) {n m : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    ∃ g : relativeTensorProduct R A n →+* relativeTensorProduct R A m,
      ∀ x : Fin (n + 1) → A,
        g (PiTensorProduct.tprod R x) =
          PiTensorProduct.tprod R (fun j : Fin (m + 1) ↦
            Finset.prod (Finset.filter (fun i : Fin (n + 1) ↦ φ.toOrderHom i = j)
              Finset.univ) x) := by sorry

noncomputable def relativeTensorMap (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (f : R →+* A) {n m : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    relativeTensorProduct R A n →+* relativeTensorProduct R A m :=
  Classical.choose (relativeTensorMap_exists R A f φ)

theorem relativeTensorMap_pure (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (f : R →+* A) {n m : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (x : Fin (n + 1) → A) :
    relativeTensorMap R A f φ (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun j : Fin (m + 1) ↦
        Finset.prod (Finset.filter (fun i : Fin (n + 1) ↦ φ.toOrderHom i = j)
          Finset.univ) x) := by
  exact Classical.choose_spec (relativeTensorMap_exists R A f φ) x

/-! ## Descent data and their morphisms -/

section DescentData

variable {R A N N' : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

/- The three maps in the cocycle diagram are obtained by tensoring the
comparison with the identity and by re-associating tensor products.  We keep
the source-facing condition as a proposition so later interfaces do not
depend on a choice of parenthesization. -/
def descentCocycle (φ : TensorProduct R N A ≃ₗ[R] TensorProduct R A N) : Prop := by
  sorry

/-- A descent datum `(N, φ)` for `R → A`. -/
structure DescentDatum where
  comparison : TensorProduct R N A ≃ₗ[R] TensorProduct R A N
  cocycle : descentCocycle comparison

def descentMorphismCompatibility (D : DescentDatum (R := R) (A := A) (N := N))
    (D' : DescentDatum (R := R) (A := A) (N := N')) (f : N →ₗ[R] N') : Prop := by
  sorry

/-- A morphism of descent data. -/
structure DescentDatumHom (D : DescentDatum (R := R) (A := A) (N := N))
    (D' : DescentDatum (R := R) (A := A) (N := N')) where
  hom : N →ₗ[R] N'
  commutes : descentMorphismCompatibility D D' hom

end DescentData

/-! ## The modules in each cosimplicial degree -/

section Terms

variable {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- `N_{n,i}`, with `N` in position `i`. -/
abbrev descentTerm (R A N : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (n : ℕ) (i : Fin (n + 1)) : Type u :=
  TensorProduct R N (relativeTensorProduct R A n)

abbrev descentTermModule (R A N : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (n : ℕ) (i : Fin (n + 1)) : ModuleCat R :=
  ModuleCat.of R (descentTerm R A N n i)

theorem descentTransportMap_exists {n : ℕ} {i j : Fin (n + 1)}
    (h : i ≤ j) (φ : TensorProduct R N A ≃ₗ[R] TensorProduct R A N) :
    Nonempty (descentTerm R A N n i ≃ₗ[R] descentTerm R A N n j) := by sorry

noncomputable def descentTransportMap {n : ℕ} {i j : Fin (n + 1)}
    (h : i ≤ j) (φ : TensorProduct R N A ≃ₗ[R] TensorProduct R A N) :
    descentTerm R A N n i ≃ₗ[R] descentTerm R A N n j :=
  Classical.choice (descentTransportMap_exists h φ)

theorem descentCosimplicialModule_exists
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    Nonempty (CosimplicialObject (ModuleCat R)) := by sorry

noncomputable def descentCosimplicialModule
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    CosimplicialObject (ModuleCat R) :=
  Classical.choice (descentCosimplicialModule_exists D)

theorem descentCosimplicialModule_degree
    (D : DescentDatum (R := R) (A := A) (N := N)) (n : ℕ) :
    Nonempty ((descentCosimplicialModule D).obj (SimplexCategory.mk n) ≅
      descentTermModule R A N n ⟨n, Nat.lt_succ_self n⟩) := by sorry

end Terms

/-! ## Canonical data and effectivity -/

section Canonical

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

def canonicalDescentComparison :
    TensorProduct R (TensorProduct R M A) A ≃ₗ[R]
      TensorProduct R A (TensorProduct R M A) :=
  (TensorProduct.congr (TensorProduct.comm R M A) (LinearEquiv.refl R A)).trans
    (TensorProduct.assoc R A M A)

theorem canonicalDescentDatum_exists :
    ∃ D : DescentDatum (R := R) (A := A) (N := TensorProduct R M A),
      D.comparison = canonicalDescentComparison (R := R) (A := A) (M := M) := by sorry

noncomputable def canonicalDescentDatum :
    DescentDatum (R := R) (A := A) (N := TensorProduct R M A) :=
  Classical.choose (canonicalDescentDatum_exists (R := R) (A := A) (M := M))

def DescentDatumIsoCompatibility {N N' : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (D : DescentDatum (R := R) (A := A) (N := N))
    (D' : DescentDatum (R := R) (A := A) (N := N')) (e : N ≃ₗ[R] N') : Prop := by
  sorry

structure DescentDatumIso {N N' : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (D : DescentDatum (R := R) (A := A) (N := N))
    (D' : DescentDatum (R := R) (A := A) (N := N')) where
  hom : N ≃ₗ[R] N'
  commutes : DescentDatumIsoCompatibility D D' hom

def DescentDatum.IsEffective {N : Type*} [AddCommGroup N] [Module R N]
    [Module A N] [IsScalarTower R A N]
    (D : DescentDatum (R := R) (A := A) (N := N)) : Prop :=
  ∃ M : Type*, ∃ (_ : AddCommGroup M) (_ : Module R M),
    ∃ D₀ : DescentDatum (R := R) (A := A) (N := TensorProduct R M A),
    Nonempty (DescentDatumIso D₀ D)

end Canonical

/-! ## Complexes, exactness, and effectivity -/

section Complexes

variable {R A N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

theorem descentCochainComplex_exists
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    Nonempty (CochainComplex (ModuleCat R) ℕ) := by sorry

noncomputable def descentCochainComplex
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    CochainComplex (ModuleCat R) ℕ :=
  Classical.choice (descentCochainComplex_exists D)

/-- The first differential in the source's displayed complex. -/
noncomputable def descentFirstMap
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    N →ₗ[R] TensorProduct R A N := by
  exact TensorProduct.mk R A N 1 -
    D.comparison.toLinearMap.comp ((TensorProduct.mk R N A).flip 1)

/-- The degree-zero equalizer `H⁰(s(N_•)) = {n | 1 ⊗ n = φ(n ⊗ 1)}`. -/
def descentH0 (D : DescentDatum (R := R) (A := A) (N := N)) : Submodule R N := by
  exact (descentFirstMap D).ker

theorem descent_complex_first_map (D : DescentDatum (R := R) (A := A) (N := N)) :
    ∀ n : N, descentFirstMap D n =
      TensorProduct.mk R A N 1 n - D.comparison (TensorProduct.mk R N A n 1) := by sorry

def ExtendedDescentComplexExact
    (D : DescentDatum (R := R) (A := A) (N := N)) : Prop := by
  sorry

def BaseChangedDescentDataEffective
    (D : DescentDatum (R := R) (A := A) (N := N)) (R' : Type*) : Prop := by
  sorry

theorem extended_descent_complex_shape
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    Nonempty (CochainComplex (ModuleCat R) ℕ) :=
  ⟨descentCochainComplex D⟩

theorem exact_extended_descent_complex_of_section
    (D : DescentDatum (R := R) (A := A) (N := N))
    (σ : A →+* R) (hσ : (algebraMap R A).comp σ = RingHom.id A) :
    ExtendedDescentComplexExact D := by sorry

theorem exact_extended_descent_complex_of_faithfullyFlat
    (D : DescentDatum (R := R) (A := A) (N := N))
    [Module.FaithfullyFlat R A] : ExtendedDescentComplexExact D := by sorry

theorem recognize_effective_descent
    (D : DescentDatum (R := R) (A := A) (N := N))
    [Module.FaithfullyFlat R A] :
    D.IsEffective ↔ Nonempty (TensorProduct R A (descentH0 D) ≃ₗ[R] N) := by sorry

theorem descent_effective_after_baseChange
    (D : DescentDatum (R := R) (A := A) (N := N))
    (R' : Type*) [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    (h : BaseChangedDescentDataEffective D R') : D.IsEffective := by sorry

end Complexes

/-! ## Main theorem and remarks -/

theorem effective_descent_for_modules (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.FaithfullyFlat R A] {N : Type v} [AddCommGroup N]
    [Module R N] [Module A N] [IsScalarTower R A N]
    (D : DescentDatum (R := R) (A := A) (N := N)) : D.IsEffective := by sorry

theorem effective_descent_modules_inverse
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] {N : Type v} [AddCommGroup N]
    [Module R N] [Module A N] [IsScalarTower R A N]
    (D : DescentDatum (R := R) (A := A) (N := N)) :
    Nonempty (Submodule R N) := ⟨descentH0 D⟩

/-- The canonical datum on `M ⊗[R] A` has the same associated cosimplicial
module as `(A/R)_• ⊗[R] M`. -/
def CanonicalDescentCosimplicialIdentification (R A M : Type*) : Prop := by
  sorry

theorem canonical_descent_cosimplicial_identification (R A M : Type*) :
    CanonicalDescentCosimplicialIdentification R A M := by sorry

/-- The source's assertion that extension of scalars and the degree-zero
descent module are mutually inverse at the level of categories. -/
def DescentModulesEquivalence (R A : Type u) [CommRing R] [CommRing A]
    (f : R →+* A) : Prop :=
  Nonempty (ComonadicLeftAdjoint (ModuleCat.extendScalars.{u, u, u} f))

theorem effective_descent_modules_equivalence (R A : Type u)
    [CommRing R] [CommRing A] (f : R →+* A) (hf : f.FaithfullyFlat) :
    DescentModulesEquivalence R A f := by
  letI := comonadicExtendScalars hf
  exact ⟨inferInstance⟩

def StandardCoverFaithfullyFlat (R : Type u) [CommRing R] {n : ℕ}
    (f : Fin n → R) : Prop := by
  sorry

def standardCoverAlgebra (R : Type u) [CommRing R] {n : ℕ} (f : Fin n → R) : Type u :=
  ∀ i, Localization.Away (f i)

theorem standardCoverAlgebra_faithfullyFlat (R : Type u) [CommRing R]
    {n : ℕ} (f : Fin n → R) : StandardCoverFaithfullyFlat R f := by sorry

/-- The cartesian condition in the general cosimplicial-algebra remark. -/
def CartesianTransition (A : CosimplicialObject CommRingCat)
    (M : CosimplicialObject (ModuleCat ℤ))
    {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) : Prop := by
  sorry

def CartesianCosimplicialModule (A : CosimplicialObject CommRingCat)
    (M : CosimplicialObject (ModuleCat ℤ)) : Prop :=
  ∀ n m (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m),
    CartesianTransition A M φ

def CartesianDescentSteps (A : CosimplicialObject CommRingCat)
    (M : CosimplicialObject (ModuleCat ℤ)) : Prop := by
  sorry

theorem cartesian_module_descent_steps (A : CosimplicialObject CommRingCat)
    (M : CosimplicialObject (ModuleCat ℤ)) : CartesianDescentSteps A M := by sorry

end Formalization.Books.Descent.Unit03
