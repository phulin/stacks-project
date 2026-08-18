import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Commutative Algebra, Chapter 14: Base change

This file records the base-change constructions and interfaces from the source.
Mathlib's extension-of-scalars model is used for a base-changed module: it is
canonically equivalent to the source's `M ⊗[R] R'` model, while retaining the
canonical `S ⊗[R] R'`-module structure needed for the finiteness statements.
-/

open CategoryTheory
open scoped TensorProduct
open scoped ChangeOfRings

namespace Formalization.Books.Algebra.Unit14

universe u

/-! ## Base change -/

/-- The base-change ring map `R' →+* S ⊗[R] R'` attached to `R →+* S` and
`R →+* R'`.  The algebra structures are the ones induced by the two ring maps. -/
def baseChangeRingMap {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    R' →+* S ⊗[R] R' := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Semiring (S ⊗[R] R') := Algebra.TensorProduct.instSemiring
  letI : Ring (S ⊗[R] R') := Algebra.TensorProduct.instRing
  letI : Algebra (S ⊗[R] R') (S ⊗[R] R') := Algebra.id _
  letI : Module (S ⊗[R] R') (S ⊗[R] R') := Algebra.toModule
  letI : Ring (S ⊗[R] R') := Algebra.TensorProduct.instRing
  exact Algebra.TensorProduct.includeRight.toRingHom

/-- The canonical `S`-algebra map into the base-changed ring. -/
def baseChangeAlgebraMap {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    S →+* S ⊗[R] R' := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom

/-- The canonical extension-of-scalars model for the source's base-changed
`S`-module `M ⊗[R] R'`.  Its underlying tensor product is
`(S ⊗[R] R') ⊗[S] M`, which carries the required base-changed module action. -/
abbrev baseChangeModule {R S R' M : Type*} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (g : R →+* R') :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  ((ModuleCat.extendScalars (baseChangeAlgebraMap f g)).obj (ModuleCat.of S M) : Type _)

/-- The ideal of `MvPolynomial σ A` obtained by extending an ideal of
`MvPolynomial σ R` along the coefficient map `R → A`. -/
noncomputable def baseChangePolynomialIdeal {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (σ : Type*) (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ A) :=
  (I.map (Algebra.TensorProduct.includeRight (A := A) (R := R)).toRingHom).map
    (MvPolynomial.algebraTensorAlgEquiv R A).toAlgHom.toRingHom

/-- The polynomial-quotient form of base change, obtained from Mathlib's
tensor-quotient equivalence and the canonical tensor/polynomial equivalence. -/
noncomputable def polynomialQuotientBaseChangeEquiv {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (σ : Type*) (I : Ideal (MvPolynomial σ R)) :
    A ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[A]
      MvPolynomial σ A ⧸ baseChangePolynomialIdeal (R := R) (A := A) σ I := by
  let e : A ⊗[R] MvPolynomial σ R ≃ₐ[A] MvPolynomial σ A :=
    MvPolynomial.algebraTensorAlgEquiv R A
  let I' : Ideal (A ⊗[R] MvPolynomial σ R) :=
    I.map (Algebra.TensorProduct.includeRight (A := A) (R := R)).toRingHom
  let q := Algebra.TensorProduct.tensorQuotientEquiv (R := R) A
    (MvPolynomial σ R) A I
  let q' := Ideal.quotientEquivAlg I' (baseChangePolynomialIdeal (R := R) (A := A) σ I) e (by
    rfl)
  exact q.trans q'

/-! ## Stability of finiteness -/

/-- Finiteness of modules is preserved by the base-change construction. -/
theorem baseChange_finite_module {R S R' M : Type*} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M] (f : R →+* S) (g : R →+* R')
    [Module.Finite S M] :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Module.Finite (S ⊗[R] R') (baseChangeModule (M := M) f g) := by
  classical
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  let Pobj := (ModuleCat.extendScalars (baseChangeAlgebraMap f g)).obj (ModuleCat.of S M)
  letI : AddCommMonoid (Pobj : Type _) := Pobj.isAddCommGroup.toAddCommMonoid
  letI : Module (S ⊗[R] R') (Pobj : Type _) := Pobj.isModule
  letI : Algebra S (S ⊗[R] R') := (baseChangeAlgebraMap f g).toAlgebra
  have hadd :
      (Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := R')).toAddCommMonoid =
        ((ModuleCat.restrictScalars (baseChangeAlgebraMap f g)).obj
          (ModuleCat.of (S ⊗[R] R') (S ⊗[R] R'))).isAddCommGroup.toAddCommMonoid := by
    apply AddCommMonoid.ext
    rfl
  cases hadd
  have hmod :
      (Algebra.toModule : Module S (S ⊗[R] R')) =
        ((ModuleCat.restrictScalars (baseChangeAlgebraMap f g)).obj
          (ModuleCat.of (S ⊗[R] R') (S ⊗[R] R'))).isModule := by
    apply Module.ext'
    intro a x
    rfl
  cases hmod
  exact Module.Finite.base_change S (S ⊗[R] R') M

/-- Finite presentation of modules is preserved by the base-change
construction. -/
theorem baseChange_finite_presentation_module {R S R' M : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [AddCommGroup M] [Module S M] (f : R →+* S) (g : R →+* R')
    [Module.FinitePresentation S M] :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Module.FinitePresentation (S ⊗[R] R') (baseChangeModule (M := M) f g) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  let Pobj := (ModuleCat.extendScalars (baseChangeAlgebraMap f g)).obj (ModuleCat.of S M)
  letI : AddCommMonoid (Pobj : Type _) := Pobj.isAddCommGroup.toAddCommMonoid
  letI : Module (S ⊗[R] R') (Pobj : Type _) := Pobj.isModule
  letI : Algebra S (S ⊗[R] R') := Algebra.TensorProduct.leftAlgebra
  have hadd :
      (Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := R')).toAddCommMonoid =
        ((ModuleCat.restrictScalars (baseChangeAlgebraMap f g)).obj
          (ModuleCat.of (S ⊗[R] R') (S ⊗[R] R'))).isAddCommGroup.toAddCommMonoid := by
    apply AddCommMonoid.ext
    rfl
  cases hadd
  have hmod :
      (Algebra.toModule : Module S (S ⊗[R] R')) =
        ((ModuleCat.restrictScalars (baseChangeAlgebraMap f g)).obj
          (ModuleCat.of (S ⊗[R] R') (S ⊗[R] R'))).isModule := by
    apply Module.ext'
    intro a x
    rw [Algebra.smul_def]
    have h := ModuleCat.restrictScalars.smul_def'
      (M := ModuleCat.of (S ⊗[R] R') (S ⊗[R] R'))
      (baseChangeAlgebraMap f g) a x
    convert h.symm using 1 <;> rfl
  have hstd : Module.FinitePresentation (S ⊗[R] R')
      (TensorProduct S (S ⊗[R] R') M) := by
    letI : Module (S ⊗[R] R') (TensorProduct S (S ⊗[R] R') M) :=
      TensorProduct.leftModule
    obtain ⟨n, m, f₀, g₀, hf₀, hfg₀⟩ := Module.FinitePresentation.exists_fin' S M
    let e : ((S ⊗[R] R') ⊗[S] (Fin n → S)) ≃ₗ[S ⊗[R] R']
        (Fin n → (S ⊗[R] R')) :=
      TensorProduct.piRight S (S ⊗[R] R') (S ⊗[R] R') (fun _ : Fin n => S) ≪≫ₗ
        LinearEquiv.piCongrRight (fun _ =>
          (Algebra.TensorProduct.rid S (S ⊗[R] R') (S ⊗[R] R')).toLinearEquiv)
    letI : Module.FinitePresentation (S ⊗[R] R')
        ((S ⊗[R] R') ⊗[S] (Fin n → S)) := by
      apply Module.FinitePresentation.of_equiv e.symm
    apply Module.finitePresentation_of_surjective (f₀.baseChange (S ⊗[R] R'))
      (LinearMap.lTensor_surjective (S ⊗[R] R') hf₀)
    have hexact : Function.Exact
        ((LinearMap.ker f₀).subtype.baseChange (S ⊗[R] R'))
        (f₀.baseChange (S ⊗[R] R')) :=
      lTensor_exact (S ⊗[R] R') f₀.exact_subtype_ker_map hf₀
    rw [LinearMap.exact_iff] at hexact
    rw [hexact]
    have hker : Module.Finite S (LinearMap.ker f₀) :=
      .of_fg (Module.FinitePresentation.fg_ker f₀ hf₀)
    exact Submodule.fg_range _
  let U := (ModuleCat.restrictScalars (baseChangeAlgebraMap f g)).obj
    (ModuleCat.of (S ⊗[R] R') (S ⊗[R] R'))
  letI : IsScalarTower S (S ⊗[R] R') (U : Type _) :=
    IsScalarTower.of_compHom S (S ⊗[R] R') (U : Type _)
  let eU : (S ⊗[R] R') ≃ₗ[S ⊗[R] R'] (U : Type _) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  let e : TensorProduct S (S ⊗[R] R') M ≃ₗ[S ⊗[R] R'] (Pobj : Type _) :=
    TensorProduct.AlgebraTensorModule.congr eU (LinearEquiv.refl S M)
  letI : Module.FinitePresentation (S ⊗[R] R')
      (TensorProduct S (S ⊗[R] R') M) := hstd
  exact Module.FinitePresentation.of_equiv e

/-- Finite type of ring maps is preserved by base change. -/
theorem baseChange_finite_type {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : f.FiniteType) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    (baseChangeRingMap f g).FiniteType := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R' (S ⊗[R] R') := (baseChangeRingMap f g).toAlgebra
  letI : Algebra.FiniteType R S := hf
  rw [RingHom.FiniteType]
  exact Algebra.FiniteType.equiv (by infer_instance)
    (Algebra.TensorProduct.commRight R R' S)

/-- Finite presentation of ring maps is preserved by base change. -/
theorem baseChange_finite_presentation {R S R' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] (f : R →+* S) (g : R →+* R') (hf : f.FinitePresentation) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    (baseChangeRingMap f g).FinitePresentation := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R' (S ⊗[R] R') := (baseChangeRingMap f g).toAlgebra
  letI : Algebra.FinitePresentation R S := hf
  rw [RingHom.FinitePresentation]
  exact Algebra.FinitePresentation.equiv (Algebra.TensorProduct.commRight R R' S)

/-! ## Restriction and adjunctions -/

/-- Restriction of scalars is Mathlib's canonical functor. -/
noncomputable abbrev restrictionOfScalars {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat S ⥤ ModuleCat R :=
  ModuleCat.restrictScalars f

@[simp]
theorem restrictionOfScalars_smul {R S M : Type u} [Ring R] [Ring S]
    [AddCommGroup M] [Module S M] (f : R →+* S) (r : R) (m : M) :
    r • (show (restrictionOfScalars f).obj (ModuleCat.of S M) from m) = f r • m :=
  by simpa [restrictionOfScalars] using
    (ModuleCat.restrictScalars.smul_def' (M := ModuleCat.of S M) f r m)

/-- Extension of scalars is left adjoint to restriction of scalars. -/
noncomputable abbrev tensorRestrictionAdjunction {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) :=
  ModuleCat.extendRestrictScalarsAdj f

/-- The source-facing Hom equivalence for extension and restriction of scalars. -/
noncomputable def tensorRestrictionHomEquiv {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (f : R →+* S) :
    ((ModuleCat.extendScalars f).obj (ModuleCat.of R M) ⟶ ModuleCat.of S N) ≃
      (ModuleCat.of R M ⟶ (ModuleCat.restrictScalars f).obj (ModuleCat.of S N)) :=
  (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _

@[simp]
theorem tensorRestrictionHomEquiv_apply {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (f : R →+* S)
    (φ : (ModuleCat.extendScalars f).obj (ModuleCat.of R M) ⟶ ModuleCat.of S N)
    (m : M) :
    tensorRestrictionHomEquiv f φ m = φ ((1 : S) ⊗ₜ[R,f] m) :=
  ModuleCat.extendRestrictScalarsAdj_homEquiv_apply (f := f) φ m

/-- Restriction of scalars is left adjoint to the internal Hom/coextension
functor. -/
noncomputable abbrev restrictionHomAdjunction {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :=
  ModuleCat.restrictCoextendScalarsAdj f

/-- The source-facing Hom equivalence for restriction and coextension of
scalars. -/
noncomputable def restrictionHomEquiv {R S M N : Type u} [Ring R] [Ring S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (f : R →+* S) :
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of S N) ⟶ ModuleCat.of R M) ≃
      (ModuleCat.of S N ⟶ (ModuleCat.coextendScalars f).obj (ModuleCat.of R M)) :=
  (ModuleCat.restrictCoextendScalarsAdj f).homEquiv _ _

/-! ## The tensor/Hom variant -/

/-- The `S`-module structure on `Hom_R(N, P)` used in the mixed-scalar
tensor/Hom statement; scalars act by precomposition on the `S`-module `N`. -/
@[instance_reducible]
def homOfScalarsModule {R S N P : Type u} [CommRing R] [CommRing S]
    [AddCommGroup N] [Module S N] [AddCommGroup P] [Module R P] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    letI : Module R N := Module.compHom N f
    letI : IsScalarTower R S N := SMul.comp.isScalarTower f
    Module S (N →ₗ[R] P) := by
  letI : Algebra R S := f.toAlgebra
  letI : Module R N := Module.compHom N f
  letI : IsScalarTower R S N := SMul.comp.isScalarTower f
  refine
    { smul := fun s φ => φ.comp ((LinearMap.lsmul S N s).restrictScalars R)
      smul_zero := ?_
      smul_add := ?_
      one_smul := ?_
      add_smul := ?_
      zero_smul := ?_
      mul_smul := ?_ }
  · intro s t φ
    ext n
    change φ ((s * t) • n) = φ (t • (s • n))
    simp [smul_smul, mul_comm]
  · intro φ
    ext n
    change φ ((LinearMap.lsmul S N (1 : S)).restrictScalars R n) = φ n
    rw [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, one_smul]
  · intro s
    ext n
    change (0 : P) = 0
    rfl
  · intro s φ ψ
    ext n
    change φ (s • n) + ψ (s • n) = φ (s • n) + ψ (s • n)
    rfl
  · intro s t φ
    ext n
    change φ ((s + t) • n) = φ (s • n) + φ (t • n)
    rw [add_smul, map_add]
  · intro φ
    ext n
    change φ ((0 : S) • n) = 0
    rw [zero_smul, map_zero]

/-- The mixed-scalar tensor/Hom adjunction from the source, expressed using
the restriction and precomposition module structures. -/
theorem homFromTensorProductEquiv_exists {R S M N P : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [AddCommGroup P] [Module R P] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    letI : Module R N := Module.compHom N f
    letI : IsScalarTower R S N := SMul.comp.isScalarTower f
    letI : Module S (N →ₗ[R] P) := homOfScalarsModule f
    Nonempty
      (((ModuleCat.restrictScalars f).obj
        (ModuleCat.of S (TensorProduct S M N)) ⟶ ModuleCat.of R P) ≃
        (ModuleCat.of S M ⟶ ModuleCat.of S (N →ₗ[R] P))) := by
  sorry

/- The source identifies these Hom spaces, so expose the equivalence itself in
   addition to the existence form used to package its proof. -/
noncomputable def homFromTensorProductEquiv {R S M N P : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [AddCommGroup P] [Module R P] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    letI : Module R N := Module.compHom N f
    letI : IsScalarTower R S N := SMul.comp.isScalarTower f
    letI : Module S (N →ₗ[R] P) := homOfScalarsModule f
    (((ModuleCat.restrictScalars f).obj
      (ModuleCat.of S (TensorProduct S M N)) ⟶ ModuleCat.of R P) ≃
      (ModuleCat.of S M ⟶ ModuleCat.of S (N →ₗ[R] P))) :=
  letI : Algebra R S := f.toAlgebra
  letI : Module R N := Module.compHom N f
  letI : IsScalarTower R S N := SMul.comp.isScalarTower f
  letI : Module S (N →ₗ[R] P) := homOfScalarsModule f
  Classical.choice (homFromTensorProductEquiv_exists f)

end Formalization.Books.Algebra.Unit14
