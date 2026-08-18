import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.LeftExact
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

universe u v w z

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

/- Mathlib's `LinearMap.lcomp` and `LinearMap.llcomp` are the canonical
pre- and post-composition maps on internal hom modules. -/

/-- The source-facing name for Mathlib's canonical pre-composition map. -/
abbrev internalHomPrecomp {R M M' N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] (a : M →ₗ[R] M') :
    internalHomModule (R := R) (M := M') (N := N) →ₗ[R]
      internalHomModule (R := R) (M := M) (N := N) :=
  LinearMap.lcomp R N a

/-- The source-facing name for Mathlib's canonical post-composition map. -/
abbrev internalHomPostcomp {R M N N' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (b : N →ₗ[R] N') :
    internalHomModule (R := R) (M := M) (N := N) →ₗ[R]
      internalHomModule (R := R) (M := M) (N := N') :=
  LinearMap.llcomp (R := R) R M N N'
    (σ₁₂ := RingHom.id R) (σ₁₃ := RingHom.id R) (σ₂₃ := RingHom.id R) b

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
  exact
    { map_add := by
        intro X Y f g
        change MonoidalClosed.pre (f + g).unop = _
        apply NatTrans.ext
        funext Z
        change (MonoidalClosed.pre (f + g).unop).app Z =
          (MonoidalClosed.pre f.unop).app Z + (MonoidalClosed.pre g.unop).app Z
        simp only [ModuleCat.monoidalClosed_pre_app]
        apply ModuleCat.hom_ext
        ext x y
        change (x : (Opposite.unop X ⟶ Z)) ((f + g).unop y) =
          (x : (Opposite.unop X ⟶ Z)) (f.unop y) +
            (x : (Opposite.unop X ⟶ Z)) (g.unop y)
        simp }

theorem internalHomFunctor_obj_additive {R : Type u} [CommRing R]
    (M : (ModuleCat.{u} R)ᵒᵖ) :
    Functor.Additive ((internalHomFunctor (R := R)).obj M) := by
  exact linearCoyoneda_obj_additive (R := R) (C := ModuleCat R) M

/-! ## Exactness and internal hom -/

/- The zero at the right of a sequence of two maps is expressed by
surjectivity of the second map, and the zero at the left by injectivity of the
first map.  `Function.Exact` supplies exactness at the middle term. -/

theorem internalHom_exact_of_right_exact
    {R : Type u} {M₁ : Type v} {M₂ : Type w} {M₃ : Type z} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    (Function.Exact f g ∧ Function.Surjective g) ↔
      ∀ (N : Type (max u (max v (max w z)))) [AddCommGroup N] [Module R N],
        Function.Injective (internalHomPrecomp (N := N) g) ∧
          Function.Exact (internalHomPrecomp (N := N) g)
            (internalHomPrecomp (N := N) f) := by
  constructor
  · rintro ⟨hfg, hg⟩ N _ _
    constructor
    · change Function.Injective (LinearMap.lcomp R N g)
      exact LinearMap.lcomp_injective_of_surjective g hg
    · change Function.Exact (LinearMap.lcomp R N g) (LinearMap.lcomp R N f)
      exact LinearMap.exact_lcomp_of_exact_of_surjective N hfg hg
  · intro h
    have hg : Function.Surjective g := by
      let Q := ULift.{max u (max v w)} (M₃ ⧸ LinearMap.range g)
      let e : Q ≃ₗ[R] (M₃ ⧸ LinearMap.range g) := ULift.moduleEquiv
      let q : M₃ →ₗ[R] Q := e.symm.toLinearMap.comp (LinearMap.range g).mkQ
      have hq : q = 0 := by
        apply (h Q).1
        change q.comp g = (0 : M₂ →ₗ[R] Q)
        apply LinearMap.ext
        intro x
        change e.symm ((LinearMap.range g).mkQ (g x)) = 0
        apply e.injective
        simp
      apply (LinearMap.range_eq_top).mp
      rw [eq_top_iff]
      intro y _hy
      have hmk : (LinearMap.range g).mkQ y = 0 := by
        have hq' := congrArg (fun k => e (k y)) hq
        simpa [q] using hq'
      exact (Submodule.Quotient.mk_eq_zero _).mp hmk
    constructor
    · intro x
      constructor
      · intro hx
        let q : M₂ →ₗ[R] (M₂ ⧸ LinearMap.range f) := (LinearMap.range f).mkQ
        let Q := ULift.{max u (max v z)} (M₂ ⧸ LinearMap.range f)
        let e : Q ≃ₗ[R] (M₂ ⧸ LinearMap.range f) := ULift.moduleEquiv
        let q' : M₂ →ₗ[R] Q := e.symm.toLinearMap.comp q
        have hq' : internalHomPrecomp (N := Q) f q' = 0 := by
          change q'.comp f = (0 : M₁ →ₗ[R] Q)
          apply LinearMap.ext
          intro y
          change e.symm (q (f y)) = 0
          apply e.injective
          simp [q]
        rcases ((h Q).2 q').mp hq' with ⟨φ, hφ⟩
        have hx' := congrArg (fun k => k x) hφ
        have hxq' : q' x = 0 := by
          rw [← hx']
          simp [internalHomPrecomp, hx]
        have hxq : e.symm (q x) = 0 := by
          change q' x = 0
          exact hxq'
        have hqx : q x = 0 := by
          apply e.symm.injective
          rw [map_zero]
          exact hxq
        exact (Submodule.Quotient.mk_eq_zero _).mp hqx
      · rintro ⟨y, rfl⟩
        let Q := ULift.{max u (max v w)} M₃
        let e : Q ≃ₗ[R] M₃ := ULift.moduleEquiv
        let idQ : M₃ →ₗ[R] Q := e.symm.toLinearMap
        have hc := (h Q).2.linearMap_comp_eq_zero
        have hcy := congrArg (fun k => k idQ) hc
        have hcy' := congrArg (fun k => k y) hcy
        apply e.symm.injective
        simpa [internalHomPrecomp, idQ] using hcy'
    · exact hg

theorem internalHom_exact_of_left_exact
    {R : Type u} {M₁ : Type v} {M₂ : Type w} {M₃ : Type z} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    (Function.Injective f ∧ Function.Exact f g) ↔
      ∀ (N : Type (max u (max v (max w z)))) [AddCommGroup N] [Module R N],
        Function.Injective (internalHomPostcomp (M := N) f) ∧
          Function.Exact (internalHomPostcomp (M := N) f)
            (internalHomPostcomp (M := N) g) := by
  constructor
  · rintro ⟨hf, hfg⟩ N _ _
    constructor
    · intro φ ψ hφψ
      ext x
      apply hf
      have hx := congrArg (fun k => k x) hφψ
      simpa [internalHomPostcomp_apply] using hx
    · intro φ
      constructor
      · intro hφ
        have hφ0 : g.comp φ = 0 := by
          ext x
          have hx := congrArg (fun k => k x) hφ
          simpa [internalHomPostcomp_apply] using hx
        let φ' : N →ₗ[R] LinearMap.range f :=
          φ.codRestrict (LinearMap.range f) (fun x => (hfg (φ x)).mp (by
            simpa using congrArg (fun k => k x) hφ0))
        let ψ : N →ₗ[R] M₁ :=
          (LinearEquiv.ofInjective f hf).symm.toLinearMap.comp φ'
        refine ⟨ψ, ?_⟩
        ext x
        have hx := congrArg (fun z : LinearMap.range f => (z : M₂))
          ((LinearEquiv.ofInjective f hf).apply_symm_apply (φ' x))
        change f ((LinearEquiv.ofInjective f hf).symm (φ' x)) =
          (φ' x : M₂) at hx
        change f ((LinearEquiv.ofInjective f hf).symm (φ' x)) =
          (φ' x : M₂)
        exact hx
      · rintro ⟨ψ, rfl⟩
        ext x
        have hx := congrArg (fun k => k (ψ x)) hfg.linearMap_comp_eq_zero
        simpa [internalHomPostcomp_apply] using hx
  · intro h
    have hf : Function.Injective f := by
      intro x y hxy
      let Q := ULift.{max v (max w z)} R
      let e : Q ≃ₗ[R] R := ULift.moduleEquiv
      let φx : Q →ₗ[R] M₁ :=
        (LinearMap.toSpanSingleton R M₁ x).comp e.toLinearMap
      let φy : Q →ₗ[R] M₁ :=
        (LinearMap.toSpanSingleton R M₁ y).comp e.toLinearMap
      have hcomp : internalHomPostcomp (M := Q) f φx =
          internalHomPostcomp (M := Q) f φy := by
        apply LinearMap.ext
        intro r
        simp [φx, φy, hxy]
      have hφ := (h Q).1 hcomp
      have hφ1 := congrArg (fun k => k (e.symm 1)) hφ
      simpa [φx, φy] using hφ1
    constructor
    · exact hf
    · intro y
      constructor
      · intro hy
        let Q := ULift.{max v (max w z)} R
        let e : Q ≃ₗ[R] R := ULift.moduleEquiv
        let φ : Q →ₗ[R] M₂ :=
          (LinearMap.toSpanSingleton R M₂ y).comp e.toLinearMap
        have hφ : internalHomPostcomp (M := Q) g φ = 0 := by
          apply LinearMap.ext
          intro r
          simp [φ, hy]
        rcases ((h Q).2 φ).mp hφ with ⟨ψ, hψ⟩
        refine ⟨ψ (e.symm 1), ?_⟩
        have hψ1 := congrArg (fun k => k (e.symm 1)) hψ
        simpa [internalHomPostcomp, φ] using hψ1
      · rintro ⟨x, rfl⟩
        let Q := ULift.{max u (max w z)} M₁
        let e : Q ≃ₗ[R] M₁ := ULift.moduleEquiv
        let idQ : Q →ₗ[R] M₁ := e.toLinearMap
        have hc := (h Q).2.linearMap_comp_eq_zero
        have hcx := congrArg (fun k => k idQ) hc
        have hcx' := congrArg (fun k => k (e.symm x)) hcx
        simpa [internalHomPostcomp, idQ] using hcx'

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
