import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
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
  sorry

/-- Finite presentation of modules is preserved by the base-change
construction. -/
theorem baseChange_finite_presentation_module {R S R' M : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [AddCommGroup M] [Module S M] (f : R →+* S) (g : R →+* R')
    [Module.FinitePresentation S M] :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Module.FinitePresentation (S ⊗[R] R') (baseChangeModule (M := M) f g) := by
  sorry

/-- Finite type of ring maps is preserved by base change. -/
theorem baseChange_finite_type {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : f.FiniteType) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    (baseChangeRingMap f g).FiniteType := by
  sorry

/-- Finite presentation of ring maps is preserved by base change. -/
theorem baseChange_finite_presentation {R S R' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] (f : R →+* S) (g : R →+* R') (hf : f.FinitePresentation) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    (baseChangeRingMap f g).FinitePresentation := by
  sorry

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

end Formalization.Books.Algebra.Unit14
