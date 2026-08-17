import Formalization.Books.MoreAlgebra.Unit54.InjectiveAbelianGroups
import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# More on Algebra, Chapter 55: Injective modules

This file records the module-theoretic form of the chapter.  The categorical
`Injective` predicate and the exact-sequence interfaces are the canonical APIs
used here; the comments identify the source assertions which are consequences
of those interfaces rather than parallel definitions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit23
open Formalization.Books.Algebra.Unit71
open Formalization.Books.Homology.Unit06
open Formalization.Books.Homology.Unit27

universe u

namespace Formalization.Books.MoreAlgebra.Unit55

/-! The restriction map on homs is the concrete module form of the definition. -/

def moduleHomRestriction {R : Type u} [Ring R] {M M' J : ModuleCat R}
    (f : M ⟶ M') : (M' ⟶ J) → (M ⟶ J) := fun φ => f ≫ φ

theorem moduleHomRestriction_injective {R : Type u} [Ring R]
    {M M' J : ModuleCat R} (f : M ⟶ M') (hf : Mono f) :
    Function.Injective (moduleHomRestriction f (J := J)) := by
  sorry

theorem injective_iff_hom_exact {R : Type u} [Ring R] (J : ModuleCat R) :
    Injective J ↔ IsExact (preadditiveYoneda.obj J) := by
  sorry

theorem injective_iff_moduleHomRestriction_surjective {R : Type u} [Ring R]
    (J : ModuleCat R) :
    Injective J ↔
      ∀ (M M' : ModuleCat R) (f : M ⟶ M'), Mono f →
        Function.Surjective (moduleHomRestriction f (J := J)) := by
  sorry

/-! The extension-class comparison is the source's module `Ext¹` interface.

The compatibility with the long exact sequences and six-term exact sequences
is already expressed by `extCovariantSequence`, `extContravariantSequence`,
`covariantExtSequence`, and `contravariantExtSequence` from the imported
chapters, so no duplicate sequence API is introduced here. -/

theorem moduleExtensionExtIso {R : Type u} [Ring R] (M N : ModuleCat R) :
    Nonempty (Ext M N ≃+ ExtGroup M N 1) := by
  sorry

noncomputable def moduleExtensionExtEquiv {R : Type u} [Ring R]
    (M N : ModuleCat R) : Ext M N ≃+ ExtGroup M N 1 :=
  Classical.choice (moduleExtensionExtIso M N)

theorem injective_iff_ext_one_vanishes {R : Type u} [Ring R] (J : ModuleCat R) :
    Injective J ↔ ∀ (M : ModuleCat R), ∀ e : ExtGroup M J 1, e = 0 := by
  sorry

/-! Baer's criterion, in its ideal-extension form. -/

def HasIdealExtension {R : Type u} [Ring R] (J : ModuleCat R) : Prop :=
  ∀ (I : Ideal R) (f : ModuleCat.of R I ⟶ J),
    ∃ g : ModuleCat.of R R ⟶ J,
      ModuleCat.ofHom I.subtype ≫ g = f

theorem injective_iff_baer_criterion {R : Type u} [Ring R] (J : ModuleCat R) :
    List.TFAE
      [Injective J,
       ∀ (I : Ideal R), ∀ e : ExtGroup (ModuleCat.of R (R ⧸ I)) J 1, e = 0,
       HasIdealExtension J] := by
  sorry

/-! The source's assertion that there are enough injectives is recorded before
the explicit dual construction below. -/

theorem module_category_has_enough_injectives {R : Type u} [Ring R] :
    EnoughInjectives (ModuleCat.{u} R) := by
  sorry

/-! A concrete model of the divisible cogenerator `ℚ / ℤ` used by the source. -/

abbrev RationalModInteger : Type := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

theorem rationalModInteger_injective :
    Injective (AddCommGrpCat.of RationalModInteger) := by
  sorry

/-! The contravariant character dual.  The source states this construction for
arbitrary rings, but precomposition gives a module in the same category here
under `[CommRing R]`; for a general ring it naturally lands in the opposite
module category. -/

abbrev CharacterDual (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Type u := M →+ RationalModInteger

instance characterDualModule (R M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] : Module R (CharacterDual R M) where
  smul r φ :=
    { toFun := fun x => φ (r • x)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp }
  one_smul φ := by
    ext x
    change φ ((1 : R) • x) = φ x
    simp
  mul_smul r s φ := by
    ext x
    change φ ((r * s) • x) = φ (s • (r • x))
    rw [smul_smul, mul_comm]
  smul_zero r := by
    ext x
    change (0 : RationalModInteger) = 0
    rfl
  smul_add r φ ψ := by
    ext x
    change (φ + ψ) (r • x) = φ (r • x) + ψ (r • x)
    rfl
  add_smul r s φ := by
    ext x
    change φ ((r + s) • x) = φ (r • x) + φ (s • x)
    rw [add_smul, map_add]
  zero_smul φ := by
    ext x
    change φ ((0 : R) • x) = 0
    simp

def characterDualMap {R M N : Type u} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    CharacterDual R N →ₗ[R] CharacterDual R M where
  toFun φ := φ.comp f.toAddMonoidHom
  map_add' φ ψ := by
    ext x
    rfl
  map_smul' r φ := by
    ext x
    change (r • φ) (f x) = φ (f (r • x))
    change φ (r • f x) = φ (f (r • x))
    exact congrArg φ (f.map_smul r x).symm

noncomputable def characterDualFunctor (R : Type u) [CommRing R] :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (CharacterDual R (M.unop : Type u))
  map f := ModuleCat.ofHom (characterDualMap f.unop.hom)
  map_id := by
    intro M
    apply ModuleCat.hom_ext
    ext φ x
    rfl
  map_comp := by
    intro X Y Z f g
    apply ModuleCat.hom_ext
    ext φ x
    rfl

/-! The source's free module is the direct sum of one copy of `R` for every
element of the indexing type. -/

abbrev FreeModule (R X : Type u) [Semiring R] : Type u :=
  DirectSum X (fun _ : X => R)

noncomputable def freeModuleMapTo {R M : Type u} [Ring R] [AddCommGroup M]
    [Module R M] : FreeModule R M →ₗ[R] M := by
  classical
  exact DirectSum.toModule R M M
    (fun m => LinearMap.toSpanSingleton R M m)

theorem freeModuleMapTo_surjective {R M : Type u} [Ring R] [AddCommGroup M]
    [Module R M] :
    Function.Surjective (freeModuleMapTo (R := R) (M := M)) := by
  sorry

noncomputable def freeModuleMap {R X Y : Type u} [Ring R]
    [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
    (f : X →ₗ[R] Y) : FreeModule R X →ₗ[R] FreeModule R Y := by
  classical
  exact DirectSum.toModule R X (FreeModule R Y)
    (fun x =>
      LinearMap.toSpanSingleton R (FreeModule R Y)
        ((DirectSum.lof R Y (fun _ : Y => R) (f x)) 1))

/-! The arrow-valued free-module construction from the source definition. -/

noncomputable def freeModuleArrowFunctor (R : Type u) [Ring R] :
    ModuleCat.{u} R ⥤ Arrow (ModuleCat.{u} R) where
  obj M :=
    { left := ModuleCat.of R (FreeModule R (M : Type u))
      right := M
      hom := ModuleCat.ofHom (freeModuleMapTo (R := R) (M := (M : Type u))) }
  map f :=
    { left := ModuleCat.ofHom (freeModuleMap f.hom)
      right := f
      w := by sorry }
  map_id := by sorry
  map_comp := by sorry

theorem characterDualFunctor_exact (R : Type u) [CommRing R] :
    IsExact (characterDualFunctor R) := by
  sorry

def characterDualEvaluation {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] : M →ₗ[R] CharacterDual R (CharacterDual R M) where
  toFun x :=
    { toFun := fun φ => φ x
      map_zero' := by simp
      map_add' := by
        intro φ ψ
        simp }
  map_add' x y := by
    ext φ
    simp
  map_smul' r x := by
    ext φ
    rfl

theorem characterDualEvaluation_injective {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Function.Injective (characterDualEvaluation (R := R) (M := M)) := by
  sorry

abbrev InjectiveEnvelope (R M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] : Type u :=
  CharacterDual R (FreeModule R (CharacterDual R M))

def injectiveEnvelopeMap {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] : M →ₗ[R] InjectiveEnvelope R M :=
  (characterDualMap (freeModuleMapTo (R := R) (M := CharacterDual R M))).comp
    (characterDualEvaluation (R := R) (M := M))

theorem injectiveEnvelopeMap_injective {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Function.Injective (injectiveEnvelopeMap (R := R) (M := M)) := by
  sorry

def injectiveEnvelopeMapOf {R M N : Type u} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    InjectiveEnvelope R M →ₗ[R] InjectiveEnvelope R N :=
  characterDualMap (freeModuleMap (characterDualMap f))

theorem injectiveEnvelope_injective {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] :
    Injective (ModuleCat.of R (InjectiveEnvelope R M)) := by
  sorry

noncomputable def injectiveEnvelopeFunctor (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (InjectiveEnvelope R (M : Type u))
  map f := ModuleCat.ofHom (injectiveEnvelopeMapOf f.hom)
  map_id := by sorry
  map_comp := by sorry

noncomputable def injectiveEmbeddingFunctor (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ Arrow (ModuleCat.{u} R) where
  obj M :=
    { left := M
      right := (injectiveEnvelopeFunctor R).obj M
      hom := ModuleCat.ofHom (injectiveEnvelopeMap (R := R) (M := (M : Type u))) }
  map f :=
    { left := f
      right := (injectiveEnvelopeFunctor R).map f
      w := by sorry }
  map_id := by sorry
  map_comp := by sorry

theorem has_functorial_injective_embeddings (R : Type u) [CommRing R] :
    HasFunctorialInjectiveEmbeddings (C := ModuleCat.{u} R) := by
  refine ⟨injectiveEmbeddingFunctor R, ?_, ?_, ?_⟩
  · sorry
  · intro M
    sorry
  · intro M
    exact injectiveEnvelope_injective (R := R) (M := (M : Type u))

end Formalization.Books.MoreAlgebra.Unit55
