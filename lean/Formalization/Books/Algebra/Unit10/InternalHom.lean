import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.Module
import Formalization.Books.Algebra.Unit09.Localization

/-!
# Commutative Algebra, Chapter 10: Internal Hom

The module of homomorphisms is represented by Mathlib's canonical type
`M →ₗ[R] N`.  The categorical internal-hom functor and the finitely presented
localization equivalence are also taken directly from Mathlib; the declarations
below expose the pointwise formulas and the source-facing exactness statements.
-/

namespace Formalization.Books.Algebra.Unit10

open CategoryTheory
open Formalization.Books.Algebra.Unit09

universe u v w

/-! ## The module of homomorphisms -/

/- The source's `Hom_R(M, N)` is exactly the canonical `R`-module
`M →ₗ[R] N`.  Its `AddCommGroup` and `Module` instances are supplied by
Mathlib, so no parallel homomorphism structure is introduced here. -/

abbrev internalHomModule {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :=
  M →ₗ[R] N

@[simp]
theorem internalHom_add_apply {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ ψ : internalHomModule (R := R) (M := M) (N := N)) (m : M) :
    (φ + ψ) m = φ m + ψ m := by
  rfl

@[simp]
theorem internalHom_smul_apply {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (r : R) (φ : internalHomModule (R := R) (M := M) (N := N)) (m : M) :
    (r • φ) m = r • φ m := by
  rfl

theorem internalHom_smul_apply_eq {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (r : R) (φ : internalHomModule (R := R) (M := M) (N := N)) (m : M) :
    (r • φ) m = φ (r • m) := by
  simp

/-! ## Pre- and post-composition -/

/-- Pre-composition by an `R`-linear map, viewed as an `R`-linear map of
internal hom modules. -/
def internalHomPrecomp {R M M' N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] (a : M →ₗ[R] M') :
    internalHomModule (R := R) (M := M') (N := N) →ₗ[R]
      internalHomModule (R := R) (M := M) (N := N) where
  toFun φ := φ.comp a
  map_add' φ ψ := by
    ext m
    simp
  map_smul' r φ := by
    ext m
    simp

/-- Post-composition by an `R`-linear map, viewed as an `R`-linear map of
internal hom modules. -/
def internalHomPostcomp {R M N N' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (b : N →ₗ[R] N') :
    internalHomModule (R := R) (M := M) (N := N) →ₗ[R]
      internalHomModule (R := R) (M := M) (N := N') where
  toFun φ := b.comp φ
  map_add' φ ψ := by
    ext m
    simp
  map_smul' r φ := by
    ext m
    simp

@[simp]
theorem internalHomPrecomp_apply {R M M' N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] (a : M →ₗ[R] M')
    (φ : internalHomModule (R := R) (M := M') (N := N)) (m : M) :
    internalHomPrecomp a φ m = φ (a m) := by
  rfl

@[simp]
theorem internalHomPostcomp_apply {R M N N' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (b : N →ₗ[R] N')
    (φ : internalHomModule (R := R) (M := M) (N := N)) (m : M) :
    internalHomPostcomp b φ m = b (φ m) := by
  rfl

/-- The square formed by pre- and post-composition in the source commutes. -/
theorem internalHom_precomp_postcomp_commute
    {R M M' N N' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (a : M →ₗ[R] M') (b : N →ₗ[R] N') :
    (internalHomPrecomp (N := N') a).comp (internalHomPostcomp (M := M') b) =
      (internalHomPostcomp (M := M) b).comp (internalHomPrecomp (N := N) a) := by
  ext φ m
  rfl

/-! ## The additive internal-hom functor -/

/-- Mathlib's canonical internal-hom functor
`ModuleCat(R)ᵒᵖ ⥤ ModuleCat(R) ⥤ ModuleCat(R)`. -/
abbrev internalHomFunctor {R : Type u} [CommRing R] :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  MonoidalClosed.internalHom

/- The `ModuleCat` internal hom is additive in the covariant module variable;
the bundled `internalHom` functor records the contravariant and covariant
functoriality of the source's diagram. -/
theorem internalHomFunctor_additive {R : Type u} [CommRing R] :
    Functor.Additive (internalHomFunctor (R := R)) := by
  sorry

theorem internalHomFunctor_obj_additive {R : Type u} [CommRing R]
    (M : (ModuleCat.{u} R)ᵒᵖ) :
    Functor.Additive ((internalHomFunctor (R := R)).obj M) := by
  sorry

/-! ## Exactness and internal hom -/

/- The zero at the right of a sequence of two maps is expressed by
surjectivity of the second map, and the zero at the left by injectivity of the
first map.  `Function.Exact` supplies exactness at the middle term. -/

theorem internalHom_exact_of_right_exact
    {R M₁ M₂ M₃ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    (Function.Exact f g ∧ Function.Surjective g) ↔
      ∀ (N : Type*) [AddCommGroup N] [Module R N],
        Function.Injective (internalHomPrecomp (N := N) g) ∧
          Function.Exact (internalHomPrecomp (N := N) g)
            (internalHomPrecomp (N := N) f) := by
  sorry

theorem internalHom_exact_of_left_exact
    {R M₁ M₂ M₃ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    (Function.Injective f ∧ Function.Exact f g) ↔
      ∀ (N : Type*) [AddCommGroup N] [Module R N],
        Function.Injective (internalHomPostcomp (M := N) f) ∧
          Function.Exact (internalHomPostcomp (M := N) f)
            (internalHomPostcomp (M := N) g) := by
  sorry

/-! ## Localization of internal homs -/

/- The first equality in the source's localization lemma is Mathlib's
`linearEquivMapExtendScalars`, extended to a localization-linear equivalence.
The second equality is Mathlib's canonical identification of maps over
`Localization S` with the same maps after restriction of scalars to `R`. -/

theorem internalHom_localization_finitelyPresented
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    [AddCommGroup N] [Module R N] (S : Submonoid R) :
    Nonempty
        (localizedModule S (internalHomModule (R := R) (M := M) (N := N)) ≃ₗ[localization S]
          (localizedModule S M →ₗ[localization S] localizedModule S N)) ∧
      Nonempty
        ((localizedModule S M →ₗ[localization S] localizedModule S N) ≃ₗ[localization S]
          (localizedModule S M →ₗ[R] localizedModule S N)) := by
  constructor
  · exact ⟨(Module.FinitePresentation.linearEquivMapExtendScalars S).extendScalarsOfIsLocalization
      S (localization S)⟩
  · exact ⟨(LinearMap.extendScalarsOfIsLocalizationEquiv S (localization S)).symm⟩

theorem internalHom_localization_away_finitelyPresented
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    [AddCommGroup N] [Module R N] (f : R) :
    Nonempty
        (localizedModuleAway f (internalHomModule (R := R) (M := M) (N := N)) ≃ₗ[localizationAway f]
          (localizedModuleAway f M →ₗ[localizationAway f] localizedModuleAway f N)) ∧
      Nonempty
        ((localizedModuleAway f M →ₗ[localizationAway f] localizedModuleAway f N) ≃ₗ[localizationAway f]
          (localizedModuleAway f M →ₗ[R] localizedModuleAway f N)) := by
  simpa [localizationAway, localizedModuleAway] using
    internalHom_localization_finitelyPresented (R := R) (M := M) (N := N)
      (Submonoid.powers f : Submonoid R)

end Formalization.Books.Algebra.Unit10
