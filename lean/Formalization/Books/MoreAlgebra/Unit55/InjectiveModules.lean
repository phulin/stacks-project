import Formalization.Books.MoreAlgebra.Unit54.InjectiveAbelianGroups
import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.Homology.Unit28.Projectives
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
open Formalization.Books.Homology.Unit28

universe u

namespace Formalization.Books.MoreAlgebra.Unit55

/-! The restriction map on homs is the concrete module form of the definition. -/

def moduleHomRestriction {R : Type u} [Ring R] {M M' J : ModuleCat R}
    (f : M ⟶ M') : (M' ⟶ J) → (M ⟶ J) := fun φ => f ≫ φ

theorem moduleHomRestriction_injective {R : Type u} [Ring R]
    {M M' J : ModuleCat R} (f : M ⟶ M') (hf : Epi f) :
    Function.Injective (moduleHomRestriction f (J := J)) := by
  intro φ ψ h
  exact hf.left_cancellation φ ψ h

theorem injective_iff_hom_exact {R : Type u} [Ring R] (J : ModuleCat R) :
    Injective J ↔ IsExact (preadditiveYoneda.obj J) := by
  constructor
  · intro hJ
    let hP : (preadditiveYoneda.obj J).PreservesEpimorphisms :=
      (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj J).mp hJ
    let : (preadditiveYoneda.obj J).PreservesEpimorphisms := hP
    let : (preadditiveYoneda.obj J).PreservesHomology := by
      apply Functor.preservesHomology_of_preservesEpis_and_kernels
    change PreservesFiniteLimits (preadditiveYoneda.obj J) ∧
      PreservesFiniteColimits (preadditiveYoneda.obj J)
    exact ⟨inferInstance, Functor.preservesFiniteColimits_of_preservesHomology _⟩
  · intro hExact
    change PreservesFiniteLimits (preadditiveYoneda.obj J) ∧
      PreservesFiniteColimits (preadditiveYoneda.obj J) at hExact
    let : PreservesFiniteColimits (preadditiveYoneda.obj J) := hExact.2
    apply (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj J).mpr
    infer_instance

theorem injective_iff_moduleHomRestriction_surjective {R : Type u} [Ring R]
    (J : ModuleCat R) :
    Injective J ↔
      ∀ (M M' : ModuleCat R) (f : M ⟶ M'), Mono f →
        Function.Surjective (moduleHomRestriction f (J := J)) := by
  constructor
  · intro hJ M M' f hf φ
    let : Injective J := hJ
    exact ⟨Injective.factorThru φ f, Injective.comp_factorThru φ f⟩
  · intro hJ
    constructor
    intro M M' φ f hf
    obtain ⟨g, hg⟩ := hJ M M' f hf φ
    exact ⟨g, hg⟩

/-! The extension-class comparison is the source's module `Ext¹` interface.

The compatibility with the long exact sequences and six-term exact sequences
is already expressed by `extCovariantSequence`, `extContravariantSequence`,
`covariantExtSequence`, and `contravariantExtSequence` from the imported
chapters, so no duplicate sequence API is introduced here. -/

private noncomputable def addEquivOfSurjectiveMaps
    {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (f : X →+ Y) (g : X →+ Z) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hker : ∀ x, f x = 0 ↔ g x = 0) :
    Y ≃+ Z := by
  let lift : Y → X := fun y => Classical.choose (hf y)
  have lift_spec (y : Y) : f (lift y) = y := Classical.choose_spec (hf y)
  let φ : Y →+ Z :=
    { toFun := fun y => g (lift y)
      map_zero' := (hker (lift 0)).mp (lift_spec 0)
      map_add' := by
        intro y₁ y₂
        have h : f (lift (y₁ + y₂) - (lift y₁ + lift y₂)) = 0 := by
          simp only [map_sub, map_add, lift_spec, sub_self]
        have h' := (hker (lift (y₁ + y₂) - (lift y₁ + lift y₂))).mp h
        simpa only [map_sub, map_add, sub_eq_zero] using h' }
  apply AddEquiv.ofBijective φ
  constructor
  · intro y₁ y₂ hy
    change g (lift y₁) = g (lift y₂) at hy
    have hgy : g (lift y₁ - lift y₂) = 0 := by
      simpa only [map_sub, sub_eq_zero] using hy
    have hfy := (hker (lift y₁ - lift y₂)).mpr hgy
    simpa only [map_sub, lift_spec, sub_eq_zero] using hfy
  · intro z
    obtain ⟨x, hx⟩ := hg z
    refine ⟨f x, ?_⟩
    change g (lift (f x)) = z
    rw [← hx]
    have h : f (lift (f x) - x) = 0 := by
      simp only [map_sub, lift_spec, sub_self]
    have h' := (hker (lift (f x) - x)).mp h
    simpa only [map_sub, sub_eq_zero] using h'

private def homGroupAddEquiv {R : Type u} [Ring R] (X Y : ModuleCat R) :
    HomGroup X Y ≃+ (X ⟶ Y) where
  toFun x := x.down
  invFun x := ULift.up x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private noncomputable def canonicalContravariantBoundary
    {R : Type u} [Ring R] {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (N : ModuleCat R) :
    HomGroup S.X₁ N →+ ExtGroup S.X₃ N 1 :=
  (hS.extClass.precomp N (by omega)).comp
    (CategoryTheory.Abelian.Ext.addEquiv₀.symm.toAddMonoidHom.comp
      (homGroupAddEquiv S.X₁ N).toAddMonoidHom)

private theorem custom_boundary_exact
    {R : Type u} [Ring R] {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (N : ModuleCat R) :
    Function.Exact (homPrecomposition S.f).hom
      (contravariantBoundary hS N).hom := by
  have h := (contravariant_ext_six_term_exact S hS N).exact 2
  change (ShortComplex.mk (homPrecomposition S.f)
    (contravariantBoundary hS N) _).Exact at h
  rwa [ShortComplex.ab_exact_iff_function_exact] at h

private theorem canonical_boundary_exact
    {R : Type u} [Ring R] {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (N : ModuleCat R) :
    Function.Exact (homPrecomposition S.f).hom
      (canonicalContravariantBoundary hS N) := by
  intro x
  constructor
  · intro hx
    have hx' : hS.extClass.comp
        (CategoryTheory.Abelian.Ext.mk₀ ((homGroupAddEquiv S.X₁ N) x))
          (rfl : 1 + 0 = 1) = 0 := by
      change hS.extClass.comp
        (CategoryTheory.Abelian.Ext.mk₀ ((homGroupAddEquiv S.X₁ N) x))
          (rfl : 1 + 0 = 1) = 0 at hx
      exact hx
    obtain ⟨y, hy⟩ :=
      CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁ hS N
        (CategoryTheory.Abelian.Ext.mk₀ ((homGroupAddEquiv S.X₁ N) x))
          (rfl : 1 + 0 = 1) hx'
    refine ⟨(homGroupAddEquiv S.X₂ N).symm
      (CategoryTheory.Abelian.Ext.addEquiv₀ y), ?_⟩
    apply (homGroupAddEquiv S.X₁ N).injective
    change S.f ≫ CategoryTheory.Abelian.Ext.addEquiv₀ y =
      (homGroupAddEquiv S.X₁ N) x
    apply (CategoryTheory.Abelian.Ext.mk₀_bijective S.X₁ N).injective
    rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply y] at hy
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀] at hy
    exact hy
  · rintro ⟨y, hy⟩
    have hy' := congrArg (homGroupAddEquiv S.X₁ N) hy
    change S.f ≫ (homGroupAddEquiv S.X₂ N) y =
      (homGroupAddEquiv S.X₁ N) x at hy'
    change hS.extClass.comp
      (CategoryTheory.Abelian.Ext.mk₀ ((homGroupAddEquiv S.X₁ N) x))
      (rfl : 1 + 0 = 1) = 0
    rw [← hy']
    change hS.extClass.comp
      (CategoryTheory.Abelian.Ext.mk₀
        (S.f ≫ (homGroupAddEquiv S.X₂ N) y)) (rfl : 1 + 0 = 1) = 0
    rw [← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc
      (CategoryTheory.Abelian.Ext.mk₀ ((homGroupAddEquiv S.X₂ N) y))

private theorem custom_boundary_surjective_of_projective
    {R : Type u} [Ring R] {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (N : ModuleCat R) [Projective S.X₂] :
    Function.Surjective (contravariantBoundary hS N).hom := by
  intro e
  have h := (contravariant_ext_six_term_exact S hS N).exact 3
  change (ShortComplex.mk (contravariantBoundary hS N)
    (extPullbackHom S.g) _).Exact at h
  rw [ShortComplex.ab_exact_iff] at h
  apply h e
  have hp := (projective_characterization S.X₂).out 0 3
  change Projective S.X₂ ↔
    (∀ (A : ModuleCat R), ∀ ξ : Ext S.X₂ A, ξ = 0) at hp
  exact hp.mp (inferInstance : Projective S.X₂) N _

private theorem canonical_boundary_surjective_of_projective
    {R : Type u} [Ring R] {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (N : ModuleCat R) [Projective S.X₂] :
    Function.Surjective (canonicalContravariantBoundary hS N) := by
  intro e
  obtain ⟨x, hx⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃
    hS N e (CategoryTheory.Abelian.Ext.eq_zero_of_projective _) (n₀ := 0) (by omega)
  refine ⟨(homGroupAddEquiv S.X₁ N).symm
    (CategoryTheory.Abelian.Ext.addEquiv₀ x), ?_⟩
  change hS.extClass.comp
    (CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.Abelian.Ext.addEquiv₀ x))
      (rfl : 1 + 0 = 1) = e
  simpa only [CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply] using hx

theorem moduleExtensionExtIso {R : Type u} [Ring R] (M N : ModuleCat R) :
    Nonempty (Ext M N ≃+ ExtGroup M N 1) := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (kernel.ι (Projective.π M)) (Projective.π M)
      (kernel.condition (Projective.π M))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel (Projective.π M) }
  let : Projective S.X₂ := by
    dsimp [S]
    infer_instance
  let d := (contravariantBoundary hS N).hom
  let d' := canonicalContravariantBoundary hS N
  refine ⟨addEquivOfSurjectiveMaps d d'
    (custom_boundary_surjective_of_projective hS N)
    (canonical_boundary_surjective_of_projective hS N) ?_⟩
  intro x
  exact (custom_boundary_exact hS N x).trans
    (canonical_boundary_exact hS N x).symm

noncomputable def moduleExtensionExtEquiv {R : Type u} [Ring R]
    (M N : ModuleCat R) : Ext M N ≃+ ExtGroup M N 1 :=
  Classical.choice (moduleExtensionExtIso M N)

@[simp]
theorem moduleExtensionExtEquiv_zero {R : Type u} [Ring R]
    (M N : ModuleCat R) : moduleExtensionExtEquiv M N 0 = 0 :=
  (moduleExtensionExtEquiv M N).map_zero

theorem injective_iff_ext_one_vanishes {R : Type u} [Ring R] (J : ModuleCat R) :
    Injective J ↔ ∀ (M : ModuleCat R), ∀ e : ExtGroup M J 1, e = 0 := by
  constructor
  · intro hJ M e
    obtain ⟨x, rfl⟩ := (moduleExtensionExtEquiv M J).surjective e
    rw [((injective_iff_characterizations J).mp hJ).2.2 M x,
      moduleExtensionExtEquiv_zero]
  · intro hExt
    apply (injective_iff_moduleHomRestriction_surjective J).mpr
    intro M M' f hf φ
    let : Mono f := hf
    let S : ShortComplex (ModuleCat R) :=
      ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel f }
    let x : HomGroup S.X₁ J := ULift.up (by simpa [S] using φ)
    have hz : (contravariantBoundary hS J).hom x = 0 := by
      apply (moduleExtensionExtEquiv S.X₃ J).injective
      exact (hExt S.X₃ _).trans (moduleExtensionExtEquiv_zero S.X₃ J).symm
    obtain ⟨g, hg⟩ := (custom_boundary_exact hS J x).mp hz
    change HomGroup M' J at g
    change (homPrecomposition f).hom g = ULift.up φ at hg
    exact ⟨g.down, congrArg ULift.down hg⟩

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
