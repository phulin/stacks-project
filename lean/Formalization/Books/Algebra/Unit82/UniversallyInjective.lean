import Formalization.Books.Algebra.Unit10.InternalHom
import Formalization.Books.Algebra.Unit39.FlatModules
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Module

/-!
# Commutative Algebra, Chapter 82: Universally injective module maps

The source's universal injectivity predicate is expressed using Mathlib's
canonical tensor map LinearMap.rTensor.  Short exact sequences are kept at
the level of linear maps, while directed colimits of short exact sequences use
Mathlib's category of short complexes.
-/

namespace Formalization.Books.Algebra.Unit82

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct

universe u v w

noncomputable section

/-! ## Universal injectivity and universal exactness -/

/-- A linear map is universally injective when tensoring it on the right by
every module preserves injectivity. -/
def universallyInjective
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type (max u (max v w))) [AddCommGroup Q] [Module R Q],
    Function.Injective (f.rTensor Q)

/-- A short exact sequence is universally exact when its first map remains
injective after every tensor base change. -/
def universallyExact
    {R : Type u} {M₁ : Type v} {M₂ : Type w} {M₃ : Type*}
    [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) : Prop :=
  Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
    Function.Surjective f₂ ∧ universallyInjective f₁

/-- A directed colimit presentation of a short exact sequence. -/
structure DirectedUniversallyExactColimitPresentation
    {R : Type u} (M₁ M₂ M₃ : Type u) [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) where
  comp_eq_zero : f₂.comp f₁ = 0
  index : Type u
  [indexCategory : Category.{u} index]
  [indexFiltered : IsFiltered index]
  presentation : ColimitPresentation index
    (ShortComplex.moduleCatMk f₁ f₂ comp_eq_zero)

/-- A directed colimit of split exact sequences with finitely presented third
terms. -/
structure DirectedSplitExactColimitPresentation
    {R : Type u} (M₁ M₂ M₃ : Type u) [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    extends DirectedUniversallyExactColimitPresentation M₁ M₂ M₃ f₁ f₂ where
  stage_split : ∀ i, presentation.diag.obj i |>.ShortExact ∧
    Nonempty (presentation.diag.obj i).Splitting
  finitelyPresented : ∀ i,
    Module.FinitePresentation R (presentation.diag.obj i).X₃

/-- A split short exact sequence is universally exact. -/
theorem universallyExact_of_split
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
    (hshort : Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
      Function.Surjective f₂)
    (s : M₂ →ₗ[R] M₁) (hs : s.comp f₁ = LinearMap.id) :
    universallyExact f₁ f₂ := by
  refine ⟨hshort.1, hshort.2.1, hshort.2.2, ?_⟩
  intro Q _ _ x y hxy
  have h := congrArg (fun z => (s.rTensor Q) z) hxy
  simpa [LinearMap.rTensor, TensorProduct.map_map, hs] using h

/-- Directed colimits of universally exact short sequences are universally exact. -/
theorem universallyExact_of_directedColimit
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
    (P : DirectedUniversallyExactColimitPresentation M₁ M₂ M₃ f₁ f₂)
    (hstage : letI : Category.{u} P.index := P.indexCategory
      letI : IsFiltered P.index := P.indexFiltered
      ∀ i, universallyExact (P.presentation.diag.obj i).f.hom
        (P.presentation.diag.obj i).g.hom) :
    universallyExact f₁ f₂ := by
  let : Category.{u} P.index := P.indexCategory
  let : IsFiltered P.index := P.indexFiltered
  have hc₁ : IsColimit ((ShortComplex.π₁ :
      ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapCocone
        P.presentation.cocone) :=
    isColimitOfPreserves
      (ShortComplex.π₁ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R)
      P.presentation.isColimit
  have hc₂ : IsColimit ((ShortComplex.π₂ :
      ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapCocone
        P.presentation.cocone) :=
    isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R)
      P.presentation.isColimit
  have hc₃ : IsColimit ((ShortComplex.π₃ :
      ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapCocone
        P.presentation.cocone) :=
    isColimitOfPreserves
      (ShortComplex.π₃ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R)
      P.presentation.isColimit
  let S : ShortComplex (P.index ⥤ ModuleCat.{u} R) :=
    ShortComplex.mk
      (Functor.whiskerLeft P.presentation.diag ShortComplex.π₁Toπ₂)
      (Functor.whiskerLeft P.presentation.diag ShortComplex.π₂Toπ₃) (by
        rw [← Functor.whiskerLeft_comp,
          ShortComplex.π₁Toπ₂_comp_π₂Toπ₃]
        rfl)
  let hEval : JointlyReflectIsomorphisms
      (fun i : P.index => (evaluation P.index (ModuleCat.{u} R)).obj i) :=
    { isIso := fun f => by
        apply NatIso.isIso_of_isIso_app }
  have hS : S.Exact := by
    apply (hEval.exact_iff S).2
    intro i
    exact ModuleCat.shortComplex_exact _ (hstage i).2.1
  have hexC :
      (ShortComplex.moduleCatMk f₁ f₂ P.comp_eq_zero).Exact := by
    have h := CategoryTheory.Limits.colim.exact_mapShortComplex hS hc₁
      hc₂ hc₃ (ModuleCat.ofHom f₁) (ModuleCat.ofHom f₂)
      (fun i => by
        change (P.presentation.ι.app i).τ₁ ≫ ModuleCat.ofHom f₁ =
          (P.presentation.diag.obj i).f ≫ (P.presentation.ι.app i).τ₂
        exact (P.presentation.ι.app i).comm₁₂)
      (fun i => by
        change (P.presentation.ι.app i).τ₂ ≫ ModuleCat.ofHom f₂ =
          (P.presentation.diag.obj i).g ≫ (P.presentation.ι.app i).τ₃
        exact (P.presentation.ι.app i).comm₂₃)
    change (ShortComplex.moduleCatMk f₁ f₂ P.comp_eq_zero).Exact at h
    exact h
  have hex : Function.Exact f₁ f₂ :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hexC
  let : ∀ i, Mono (S.f.app i) := fun i =>
    (ModuleCat.mono_iff_injective _).mpr (hstage i).1
  let : Mono S.f := NatTrans.mono_of_mono_app S.f
  have hmono : Mono (ModuleCat.ofHom f₁) :=
    CategoryTheory.Limits.colim.map_mono' S.f hc₁ hc₂ (ModuleCat.ofHom f₁)
      (fun i => by
        change (P.presentation.ι.app i).τ₁ ≫ ModuleCat.ofHom f₁ =
          (P.presentation.diag.obj i).f ≫ (P.presentation.ι.app i).τ₂
        exact (P.presentation.ι.app i).comm₁₂)
  let : ∀ i, Epi (S.g.app i) := fun i =>
    (ModuleCat.epi_iff_surjective _).mpr (hstage i).2.2.1
  have hepi : Epi (ModuleCat.ofHom f₂) :=
    CategoryTheory.Limits.colim.map_epi' S.g
      (ShortComplex.π₂.mapCocone P.presentation.cocone) hc₃
      (ModuleCat.ofHom f₂) (fun i => by
        change (P.presentation.ι.app i).τ₂ ≫ ModuleCat.ofHom f₂ =
          (P.presentation.diag.obj i).g ≫ (P.presentation.ι.app i).τ₃
        exact (P.presentation.ι.app i).comm₂₃)
  refine ⟨(ModuleCat.mono_iff_injective _).mp hmono, hex,
    (ModuleCat.epi_iff_surjective _).mp hepi, ?_⟩
  intro Q _ _
  let T : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
    MonoidalCategory.tensorRight (ModuleCat.of R Q)
  let : ∀ i, Mono ((Functor.whiskerRight S.f T).app i) := fun i => by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective ((P.presentation.diag.obj i).f.hom.rTensor Q)
    exact (hstage i).2.2.2 Q
  let : Mono (Functor.whiskerRight S.f T) :=
    NatTrans.mono_of_mono_app (Functor.whiskerRight S.f T)
  let fT : (T.mapCocone (ShortComplex.π₁.mapCocone P.presentation.cocone)).pt ⟶
      (T.mapCocone (ShortComplex.π₂.mapCocone P.presentation.cocone)).pt := by
    exact T.map (ShortComplex.moduleCatMk f₁ f₂ P.comp_eq_zero).f
  have hmonoQ : Mono fT :=
    CategoryTheory.Limits.colim.map_mono'
      (Functor.whiskerRight S.f T)
      (isColimitOfPreserves T hc₁) (isColimitOfPreserves T hc₂)
      fT (fun i => by
        change T.map ((P.presentation.ι.app i).τ₁) ≫
            T.map (ShortComplex.moduleCatMk f₁ f₂ P.comp_eq_zero).f =
          T.map ((P.presentation.diag.obj i).f) ≫ T.map ((P.presentation.ι.app i).τ₂)
        have hcomm := congrArg (fun k => T.map k) (P.presentation.ι.app i).comm₁₂
        dsimp at hcomm ⊢
        simpa only [T.map_comp] using hcomm)
  have hmonoQ' := (ModuleCat.mono_iff_injective fT).mp hmonoQ
  change Function.Injective (f₁.rTensor Q) at hmonoQ'
  exact hmonoQ'

/-- A colimit of split short exact sequences is universally exact. -/
theorem universallyExact_of_directedSplitColimit
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
    (P : DirectedSplitExactColimitPresentation M₁ M₂ M₃ f₁ f₂) :
    universallyExact f₁ f₂ := by
  let : Category.{u} P.index := P.indexCategory
  let : IsFiltered P.index := P.indexFiltered
  apply universallyExact_of_directedColimit P.toDirectedUniversallyExactColimitPresentation
  intro i
  have hsplit := P.stage_split (i := i)
  have hshort := hsplit.1 i
  have hs := hsplit.2
  obtain ⟨s⟩ := hs
  apply universallyExact_of_split
    ⟨hshort.moduleCat_injective_f,
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (P.presentation.diag.obj i)).1 hshort.exact,
      hshort.moduleCat_surjective_g⟩
    s.r.hom
  change s.r.hom.comp (P.presentation.diag.obj i).f.hom = LinearMap.id
  exact congrArg (fun k => k.hom) s.f_r

/-! ## The finite-presentation criteria -/

private theorem universallyExact_factor_finiteFree_aux
    {R : Type u} {M₁ M₂ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    {f₁ : M₁ →ₗ[R] M₂}
    {n m : ℕ}
    (a : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R))
    (u : (Fin n →₀ R) →ₗ[R] M₁)
    (v : (Fin m →₀ R) →ₗ[R] M₂)
    (ha : v.comp a = f₁.comp u) :
    Function.Injective (f₁.rTensor
      ((Fin n →₀ R) ⧸ LinearMap.range
        (Finsupp.linearCombination R (fun j =>
          ∑ i, (a (Finsupp.single i 1)) j •
            (Finsupp.single i (1 : R)))))) →
    ∃ w : (Fin m →₀ R) →ₗ[R] M₁, w.comp a = u := by
  let A : (Fin m →₀ R) →ₗ[R] (Fin n →₀ R) :=
    Finsupp.linearCombination R (fun j =>
      ∑ i, (a (Finsupp.single i 1)) j • Finsupp.single i 1)
  let Q : Type u := (Fin n →₀ R) ⧸ LinearMap.range A
  let q : (Fin n →₀ R) →ₗ[R] Q := Submodule.mkQ _
  let tx : M₁ ⊗[R] Q :=
    ∑ i, u (Finsupp.single i 1) ⊗ₜ[R] q (Finsupp.single i 1)
  have htx : (f₁.rTensor Q) tx = 0 := by
    dsimp [tx]
    simp only [map_sum, LinearMap.rTensor_tmul]
    have ha' (i : Fin n) :
        f₁ (u (Finsupp.single i 1)) = v (a (Finsupp.single i 1)) := by
      simpa [LinearMap.comp_apply] using
        (LinearMap.congr_fun ha (Finsupp.single i 1)).symm
    simp_rw [ha']
    classical
    have ha_basis (i : Fin n) :
        a (Finsupp.single i 1) =
          ∑ j, (a (Finsupp.single i 1)) j • Finsupp.single j 1 := by
      ext j
      simp
    calc
      _ = ∑ i, v (∑ j, (a (Finsupp.single i 1)) j •
          Finsupp.single j 1) ⊗ₜ[R] q (Finsupp.single i 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (fun z => v z ⊗ₜ[R] q (Finsupp.single i 1)) (ha_basis i)
      _ = ∑ i, ∑ j, (a (Finsupp.single i 1)) j •
          (v (Finsupp.single j 1) ⊗ₜ[R] q (Finsupp.single i 1)) := by
        simp_rw [map_sum, TensorProduct.sum_tmul, map_smul, TensorProduct.smul_tmul,
          TensorProduct.tmul_smul]
      _ = ∑ j, ∑ i, (a (Finsupp.single i 1)) j •
          (v (Finsupp.single j 1) ⊗ₜ[R] q (Finsupp.single i 1)) := by
        exact Finset.sum_comm
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        change ∑ i, (a (Finsupp.single i 1)) j •
            (v (Finsupp.single j 1) ⊗ₜ[R] q (Finsupp.single i 1)) = 0
        simp_rw [← TensorProduct.tmul_smul]
        rw [← TensorProduct.tmul_sum]
        simp_rw [← map_smul]
        rw [← map_sum]
        rw [show (∑ i, (a (Finsupp.single i 1)) j • Finsupp.single i 1) =
            A (Finsupp.single j 1) by
              simp [A, Finsupp.linearCombination_single]]
        have hq : q (A (Finsupp.single j 1)) = 0 := by
          apply (Submodule.Quotient.mk_eq_zero (LinearMap.range A)).2
          exact ⟨Finsupp.single j 1, rfl⟩
        simpa [q, Submodule.mkQ_apply] using
          congrArg (fun z => v (Finsupp.single j 1) ⊗ₜ[R] z) hq
  intro hQ
  have htx0 : tx = 0 := hQ htx
  let t0 : M₁ ⊗[R] (Fin n →₀ R) :=
    ∑ i, u (Finsupp.single i 1) ⊗ₜ[R] Finsupp.single i 1
  have ht0 : (LinearMap.lTensor M₁ q) t0 = tx := by
    dsimp [t0, tx]
    simp only [map_sum, LinearMap.lTensor_tmul]
  have ht0zero : (LinearMap.lTensor M₁ q) t0 = 0 := ht0.trans htx0
  have hex : Function.Exact (LinearMap.lTensor M₁ A) (LinearMap.lTensor M₁ q) :=
    _root_.lTensor_exact M₁ A.exact_map_mkQ_range (Submodule.mkQ_surjective _)
  have hrange : t0 ∈ LinearMap.range (LinearMap.lTensor M₁ A) := by
    rw [← hex.linearMap_ker_eq]
    exact ht0zero
  obtain ⟨t, ht⟩ := hrange
  have hcontract (z : M₁ ⊗[R] (Fin m →₀ R))
    (b : (Fin m →₀ R) →ₗ[R] R) :
      TensorProduct.rid R M₁ (LinearMap.lTensor M₁ b z) =
        ∑ j, b (Finsupp.single j 1) •
            TensorProduct.rid R M₁
            (LinearMap.lTensor M₁
              (Finsupp.lapply j : (Fin m →₀ R) →ₗ[R] R) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        simp only [TensorProduct.rid_tmul, LinearMap.lTensor_tmul]
        have hy : y = ∑ j, y j • Finsupp.single j 1 := by
          ext j
          simp
        rw [hy]
        have hb : b (∑ j, y j • Finsupp.single j 1) =
            ∑ j, y j • b (Finsupp.single j 1) := by
          simp only [map_sum, map_smul]
        have hl (j : Fin m) :
            (Finsupp.lapply j : (Fin m →₀ R) →ₗ[R] R)
              (∑ k, y k • Finsupp.single k 1) = y j := by
          change (∑ k, y k • Finsupp.single k 1) j = y j
          simp
        rw [hb]
        simp_rw [hl]
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro j hj
        simp [smul_smul, mul_comm]
    | add x y hx hy =>
        simp only [map_add, hx, hy,
          Finset.sum_add_distrib, smul_add]
  let w : (Fin m →₀ R) →ₗ[R] M₁ :=
    Finsupp.linearCombination R (fun j =>
      TensorProduct.rid R M₁
        (LinearMap.lTensor M₁
          (Finsupp.lapply j : (Fin m →₀ R) →ₗ[R] R) t))
  have hcoord (i : Fin n) : w (a (Finsupp.single i 1)) =
      u (Finsupp.single i 1) := by
    have hc := hcontract t
      ((Finsupp.lapply i : (Fin n →₀ R) →ₗ[R] R).comp A)
    have hleft : TensorProduct.rid R M₁
        (LinearMap.lTensor M₁
          ((Finsupp.lapply i : (Fin n →₀ R) →ₗ[R] R).comp A) t) =
        u (Finsupp.single i 1) := by
      rw [LinearMap.lTensor_comp_apply, ht]
      dsimp [t0]
      simp [Finsupp.single_apply]
    have hcoeff (j : Fin m) :
        ((Finsupp.lapply i : (Fin n →₀ R) →ₗ[R] R).comp A)
            (Finsupp.single j 1) = (a (Finsupp.single i 1)) j := by
      simp [LinearMap.comp_apply, A, Finsupp.linearCombination_single,
        Finsupp.single_apply]
    have ha_exp : a (Finsupp.single i 1) =
        ∑ j, (a (Finsupp.single i 1)) j • Finsupp.single j 1 := by
      ext j
      simp
    calc
      w (a (Finsupp.single i 1)) =
          ∑ j, (a (Finsupp.single i 1)) j •
            TensorProduct.rid R M₁
              (LinearMap.lTensor M₁
                (Finsupp.lapply j : (Fin m →₀ R) →ₗ[R] R) t) := by
        rw [ha_exp]
        simp only [map_sum, map_smul]
        simp [w, Finsupp.linearCombination_single]
      _ = ∑ j, ((Finsupp.lapply i : (Fin n →₀ R) →ₗ[R] R).comp A)
          (Finsupp.single j 1) •
          TensorProduct.rid R M₁
            (LinearMap.lTensor M₁
              (Finsupp.lapply j : (Fin m →₀ R) →ₗ[R] R) t) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoeff]
      _ = TensorProduct.rid R M₁
          (LinearMap.lTensor M₁
            ((Finsupp.lapply i : (Fin n →₀ R) →ₗ[R] R).comp A) t) := hc.symm
      _ = u (Finsupp.single i 1) := hleft
  refine ⟨w, ?_⟩
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext
  intro c
  change w (a (Finsupp.single i c)) = u (Finsupp.single i c)
  rw [← Finsupp.smul_single_one]
  simp only [map_smul]
  rw [hcoord]

private theorem universallyExact_factor_finiteFree
    {R : Type u} {M₁ M₂ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    {f₁ : M₁ →ₗ[R] M₂}
    (h : universallyInjective f₁)
    {n m : ℕ}
    (a : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R))
    (u : (Fin n →₀ R) →ₗ[R] M₁)
    (v : (Fin m →₀ R) →ₗ[R] M₂)
    (ha : v.comp a = f₁.comp u) :
    ∃ w : (Fin m →₀ R) →ₗ[R] M₁, w.comp a = u := by
  apply universallyExact_factor_finiteFree_aux a u v ha
  exact h _

/-- The six equivalent criteria for a short exact sequence to be universally
exact.  Finite free modules are represented by finitely supported functions. -/
theorem universallyExact_criteria
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (hshort : Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
      Function.Surjective f₂) :
    List.TFAE [
      universallyExact f₁ f₂,
      ∀ (Q : Type u) [AddCommGroup Q] [Module R Q]
        [Module.FinitePresentation R Q],
        Function.Injective (f₁.rTensor Q) ∧
          Function.Exact (f₁.rTensor Q) (f₂.rTensor Q) ∧
            Function.Surjective (f₂.rTensor Q),
      ∀ {n m : ℕ} (x : Fin n → M₁) (y : Fin m → M₂)
        (a : Fin n → Fin m → R),
        (∀ i, f₁ (x i) = ∑ j, a i j • y j) →
          ∃ z : Fin m → M₁, ∀ i, x i = ∑ j, a i j • z j,
      ∀ {n m : ℕ}
        (a : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R))
        (u : (Fin n →₀ R) →ₗ[R] M₁)
        (v : (Fin m →₀ R) →ₗ[R] M₂),
        v.comp a = f₁.comp u →
          ∃ w : (Fin m →₀ R) →ₗ[R] M₁, w.comp a = u,
      ∀ (P : Type u) [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P],
        Function.Surjective
          (Formalization.Books.Algebra.Unit10.internalHomPostcomp
            (M := P) f₂),
      Nonempty (DirectedSplitExactColimitPresentation M₁ M₂ M₃ f₁ f₂)] := by
  sorry

/-- If the right term is finitely presented, universal exactness is equivalent
to the existence of a section of the quotient map. -/
theorem universallyExact_iff_split_of_finitePresentation
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    [Module.FinitePresentation R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (hshort : Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
      Function.Surjective f₂) :
    universallyExact f₁ f₂ ↔
      ∃ s : M₃ →ₗ[R] M₂, f₂.comp s = LinearMap.id := by
  constructor
  · intro hu
    have hcrit := universallyExact_criteria f₁ f₂ hshort
    have h5 := hcrit.out 0 4
    obtain ⟨s, hs⟩ := (h5.mp hu) M₃ (LinearMap.id : M₃ →ₗ[R] M₃)
    refine ⟨s, ?_⟩
    ext x
    simpa [Formalization.Books.Algebra.Unit10.internalHomPostcomp_apply] using
      congrArg (fun g => g x) hs
  · rintro ⟨s, hs⟩
    let k : M₂ →ₗ[R] M₂ := LinearMap.id - s.comp f₂
    have hk0 : f₂.comp k = 0 := by
      ext x
      dsimp [k]
      have hx := congrArg (fun g => g (f₂ x)) hs
      have hx' : f₂ (s (f₂ x)) = f₂ x := by
        simpa [LinearMap.comp_apply] using hx
      simp only [map_sub, hx']
      exact sub_self (f₂ x)
    let e : M₁ ≃ₗ[R] LinearMap.range f₁ :=
      LinearEquiv.ofInjective f₁ hshort.1
    have hk_mem (x : M₂) : k x ∈ LinearMap.range f₁ := by
      exact (hshort.2.1 (k x)).mp (congrArg (fun g => g x) hk0)
    let r : M₂ →ₗ[R] M₁ := e.symm.toLinearMap.comp
      (k.codRestrict (LinearMap.range f₁) hk_mem)
    have hfr : f₁.comp r = k := by
      ext x
      change f₁ (e.symm (k.codRestrict (LinearMap.range f₁) hk_mem x)) = k x
      exact congrArg Subtype.val (e.apply_symm_apply _)
    have hkf₁ : k.comp f₁ = f₁ := by
      ext x
      have hx := congrArg (fun g => g x) hshort.2.1.comp_eq_zero
      have hx' : f₂ (f₁ x) = 0 := by simpa [Function.comp_apply] using hx
      simp [k, LinearMap.comp_apply, hx']
    have hrf : r.comp f₁ = LinearMap.id := by
      ext x
      apply hshort.1
      have h₁ := congrArg (fun g => g (f₁ x)) hfr
      have h₂ := congrArg (fun g => g x) hkf₁
      exact h₁.trans h₂
    exact universallyExact_of_split hshort r hrf

/-- Flatness is equivalent to universal exactness of every exact sequence
ending in the module. -/
theorem flat_iff_exact_ending_universallyExact
    {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ {M₁ M₂ : Type u} [AddCommGroup M₁] [Module R M₁]
        [AddCommGroup M₂] [Module R M₂]
        (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M),
        (Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
          Function.Surjective f₂) →
          universallyExact f₁ f₂ := by
  constructor
  · intro hflat M₁ M₂ _ _ _ _ f₁ f₂ hshort
    let : Module.Flat R M := hflat
    refine ⟨hshort.1, hshort.2.1, hshort.2.2, ?_⟩
    intro Q _ _
    have hlinj : Function.Injective (f₁.lTensor Q) :=
      LinearMap.lTensor_injective_of_exact_of_flat f₂ hshort.2.2 f₁ hshort.1
        hshort.2.1 Q
    let e₁ : TensorProduct R M₁ Q ≃ₗ[R] TensorProduct R Q M₁ :=
      TensorProduct.comm R M₁ Q
    let e₂ : TensorProduct R M₂ Q ≃ₗ[R] TensorProduct R Q M₂ :=
      TensorProduct.comm R M₂ Q
    have hcomm : e₂.toLinearMap.comp (f₁.rTensor Q) =
        (f₁.lTensor Q).comp e₁.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      rfl
    intro x y hxy
    apply e₁.injective
    apply hlinj
    have h := congrArg (fun z => e₂ z) hxy
    change e₂ ((f₁.rTensor Q) x) = e₂ ((f₁.rTensor Q) y) at h
    have hx' : e₂ ((f₁.rTensor Q) x) =
        (f₁.lTensor Q) (e₁ x) := by
      simpa [LinearMap.comp_apply] using congrArg (fun g => g x) hcomm
    have hy' : e₂ ((f₁.rTensor Q) y) =
        (f₁.lTensor Q) (e₁ y) := by
      simpa [LinearMap.comp_apply] using congrArg (fun g => g y) hcomm
    rw [hx', hy'] at h
    exact h
  · intro h
    apply Module.Flat.of_forall_exists_factorization
    intro l f x hx
    let S : Submodule R (Fin l →₀ R) := Submodule.span R ({f} : Set (Fin l →₀ R))
    let Q : Type u := (Fin l →₀ R) ⧸ S
    have hfree : Module.FinitePresentation R (Fin l →₀ R) := inferInstance
    let : Module.FinitePresentation R Q :=
      Module.finitePresentation_of_surjective (h := hfree) S.mkQ S.mkQ_surjective
        (by
          rw [Submodule.ker_mkQ]
          dsimp [S]
          exact Submodule.fg_span (Set.finite_singleton f))
    have hS : S ≤ LinearMap.ker x := by
      dsimp [S]
      refine Submodule.span_le.2 ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact LinearMap.mem_ker.mpr hx
    let xbar : Q →ₗ[R] M := S.liftQ x hS
    let N : Type u := M →₀ R
    let q : N →ₗ[R] M := Finsupp.linearCombination R (id : M → M)
    have hq : Function.Surjective q := by
      dsimp [q, N]
      simpa using (Finsupp.linearCombination_id_surjective R M)
    let f₁ : (LinearMap.ker q) →ₗ[R] N := (LinearMap.ker q).subtype
    have hshort : Function.Injective f₁ ∧ Function.Exact f₁ q ∧
        Function.Surjective q := by
      exact ⟨(LinearMap.ker q).injective_subtype,
        LinearMap.exact_subtype_ker_map q, hq⟩
    have hu := @h (LinearMap.ker q) N _ _ _ _ f₁ q hshort
    have hcrit := universallyExact_criteria
      (M₁ := LinearMap.ker q) (M₂ := N) (M₃ := M) f₁ q hshort
    have hpost_all := (hcrit.out 0 4).mp hu
    have hpost : Function.Surjective
        (Formalization.Books.Algebra.Unit10.internalHomPostcomp
          (M := Q) q) :=
      hpost_all Q
    obtain ⟨b, hb⟩ := hpost xbar
    have hb' : q.comp b = xbar := by
      change q.comp b = xbar at hb
      exact hb
    obtain ⟨k, a, y, hba⟩ := Module.Flat.exists_factorization_of_finitePresentation b
    refine ⟨k, a.comp S.mkQ, q.comp y, ?_, ?_⟩
    · calc
        x = xbar.comp S.mkQ := by
          dsimp [xbar]
          exact (S.liftQ_mkQ x hS).symm
        _ = (q.comp b).comp S.mkQ := by rw [hb']
        _ = (q.comp (y.comp a)).comp S.mkQ := by rw [hba]
        _ = (q.comp y).comp (a.comp S.mkQ) := by simp [LinearMap.comp_assoc]
    · have hfQ : S.mkQ f = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        dsimp [S]
        exact Submodule.subset_span (by simp)
      change a (S.mkQ f) = 0
      simpa using congrArg a hfQ

/-! ## Split sequences and examples -/

/-- The standard split short exact sequence with middle term a product. -/
def splitSequenceInjection
    {R : Type u} {M : Type v} [Semiring R]
    [AddCommMonoid M] [Module R M] :
    M →ₗ[R] M × M :=
  LinearMap.inl R M M

/-- The projection in the standard split short exact sequence. -/
def splitSequenceProjection
    {R : Type u} {M : Type v} [Semiring R]
    [AddCommMonoid M] [Module R M] :
    M × M →ₗ[R] M :=
  LinearMap.snd R M M

/-- A split short exact sequence is universally exact. -/
theorem splitSequence_universallyExact
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    universallyExact (splitSequenceInjection (R := R) (M := M))
      (splitSequenceProjection (R := R) (M := M)) := by
  change Function.Injective (splitSequenceInjection (R := R) (M := M)) ∧
    Function.Exact (splitSequenceInjection (R := R) (M := M))
      (splitSequenceProjection (R := R) (M := M)) ∧
    Function.Surjective (splitSequenceProjection (R := R) (M := M)) ∧
    universallyInjective (splitSequenceInjection (R := R) (M := M))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y h
    exact congrArg Prod.fst h
  · intro y
    constructor
    · intro hy
      refine ⟨y.1, ?_⟩
      apply Prod.ext
      · rfl
      · simpa [splitSequenceInjection, splitSequenceProjection] using hy.symm
    · rintro ⟨x, rfl⟩
      rfl
  · intro y
    exact ⟨(0, y), rfl⟩
  · intro Q _ _ x y hxy
    have hcomp : (LinearMap.fst R M M).comp
        (splitSequenceInjection (R := R) (M := M)) = LinearMap.id := by
      ext z
      rfl
    have h := congrArg
      (fun z => (LinearMap.fst R M M).rTensor Q z) hxy
    simpa [LinearMap.rTensor, TensorProduct.map_map, hcomp] using h

/-- A split sequence built from a non-flat module has no flat terms. -/
theorem splitSequence_nonflat
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R M ∧ ¬ Module.Flat R (M × M) ∧ ¬ Module.Flat R M := by
  refine ⟨hM, ?_, hM⟩
  intro hprod
  exact hM (Module.Flat.of_retract (f := hprod)
    (LinearMap.inl R M M) (LinearMap.fst R M M) rfl)

/-- A nonzero torsion module over the integers gives the non-flat split
sequence from the source's second example. -/
theorem splitSequence_nonflat_of_nontrivial_torsion
    {M : Type u} [AddCommGroup M] [Module ℤ M] [Nontrivial M]
    (hM : Submodule.torsion ℤ M = ⊤) :
    ¬ Module.Flat ℤ M ∧ ¬ Module.Flat ℤ (M × M) ∧ ¬ Module.Flat ℤ M := by
  have hM' : ¬ Module.Flat ℤ M := by
    intro hflat
    let : Module.Flat ℤ M := hflat
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    have hxT : x ∈ Submodule.torsion ℤ M := by
      rw [hM]
      simp
    rw [Module.Flat.torsion_eq_bot] at hxT
    exact hx (by simpa using hxT)
  refine ⟨hM', ?_, hM'⟩
  intro hprod
  have hmod : (Prod.instModule : Module ℤ (M × M)) =
      AddCommGroup.toIntModule (M × M) := Subsingleton.elim _ _
  have hprod' : @Module.Flat ℤ (M × M) _ _ Prod.instModule :=
    hmod.symm ▸ hprod
  let : Module ℤ (M × M) := Prod.instModule
  exact hM' (Module.Flat.of_retract (f := hprod')
    (LinearMap.inl ℤ M M) (LinearMap.fst ℤ M M) rfl)

/-! ## Permanence properties -/

/-- In a universally exact sequence, flatness of the middle term implies
flatness of both end terms. -/
theorem flat_ends_of_universallyExact
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (h : universallyExact f₁ f₂) (hflat : Module.Flat R M₂) :
    Module.Flat R M₁ ∧ Module.Flat R M₃ := by
  have hflat₁ : Module.Flat R M₁ := by
    let _ : Module.Flat R M₂ := hflat
    apply (Module.Flat.iff_rTensor_preserves_injective_linearMap).2
    intro N N' _ _ _ _ i hi
    have hiM₂ : Function.Injective (i.rTensor M₂) :=
      Module.Flat.rTensor_preserves_injective_linearMap i hi
    have hfN : Function.Injective (f₁.lTensor N) := by
      rw [LinearMap.lTensor_inj_iff_rTensor_inj]
      exact h.2.2.2 N
    have hcomm :
        (i.rTensor M₂).comp (f₁.lTensor N) =
          (f₁.lTensor N').comp (i.rTensor M₁) := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    apply LinearMap.ker_eq_bot.mp
    rw [eq_bot_iff]
    intro x hx
    change (i.rTensor M₁) x = 0 at hx
    have hfx : (f₁.lTensor N) x = 0 := by
      apply hiM₂
      change ((i.rTensor M₂).comp (f₁.lTensor N)) x = 0
      rw [hcomm, LinearMap.comp_apply, hx]
      simp
    have hx0 : x = 0 := hfN hfx
    simpa using hx0
  have hflat₃ : Module.Flat R M₃ := by
    let _ : Module.Flat R M₁ := hflat₁
    let _ : Module.Flat R M₂ := hflat
    apply (Module.Flat.iff_lTensor_preserves_injective_linearMap).2
    intro N N' _ _ _ _ i hi
    have hiM₂ : Function.Injective (i.lTensor M₂) :=
      Module.Flat.lTensor_preserves_injective_linearMap i hi
    have hfN' : Function.Injective (f₁.rTensor N') := h.2.2.2 N'
    have hrowN' : Function.Exact (f₁.rTensor N') (f₂.rTensor N') := by
      exact (Formalization.Books.Algebra.Unit12.tensorProduct_right_exact
        f₁ f₂ h.2.1 h.2.2.1).1
    have hsurjN : Function.Surjective (f₂.rTensor N) :=
      LinearMap.rTensor_surjective N h.2.2.1
    let Q : Type u := N' ⧸ LinearMap.range i
    let q : N' →ₗ[R] Q := (LinearMap.range i).mkQ
    have hqi : Function.Exact i q := by
      dsimp [q]
      rw [LinearMap.exact_iff, Submodule.ker_mkQ]
    have hv₁ : Function.Exact (i.lTensor M₁) (q.lTensor M₁) :=
      Module.Flat.lTensor_exact M₁ hqi
    have hcomm₂ :
        (f₂.rTensor N').comp (i.lTensor M₂) =
          (i.lTensor M₃).comp (f₂.rTensor N) := by
      rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
    have hcomm₁ :
        (f₁.rTensor N').comp (i.lTensor M₁) =
          (i.lTensor M₂).comp (f₁.rTensor N) := by
      rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
    have hcommq :
        (f₁.rTensor Q).comp (q.lTensor M₁) =
          (q.lTensor M₂).comp (f₁.rTensor N') := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    intro x y hxy
    obtain ⟨x', hx'⟩ := hsurjN x
    obtain ⟨y', hy'⟩ := hsurjN y
    let d := x' - y'
    have hd : (f₂.rTensor N) d = x - y := by
      dsimp [d]
      rw [map_sub, hx', hy']
    have hzero₃ : (i.lTensor M₃) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hzero₂ : (f₂.rTensor N') ((i.lTensor M₂) d) = 0 := by
      calc
        (f₂.rTensor N') ((i.lTensor M₂) d) =
            (i.lTensor M₃) ((f₂.rTensor N) d) := by
          have hc := congrArg (fun k => k d) hcomm₂
          simpa only [LinearMap.comp_apply] using hc
        _ = (i.lTensor M₃) (x - y) := by rw [hd]
        _ = 0 := hzero₃
    obtain ⟨z, hz⟩ := (hrowN' ((i.lTensor M₂) d)).mp hzero₂
    have hqcomp : q.comp i = 0 := by
      ext n
      simpa [LinearMap.comp_apply] using
        congrArg (fun k => k n) hqi.comp_eq_zero
    have hqzero : (q.lTensor M₂) ((i.lTensor M₂) d) = 0 := by
      change ((q.lTensor M₂).comp (i.lTensor M₂)) d = 0
      rw [← LinearMap.lTensor_comp, hqcomp]
      simp
    have hzq : (q.lTensor M₁) z = 0 := by
      have hfQ : Function.Injective (f₁.rTensor Q) := h.2.2.2 Q
      apply hfQ
      change ((f₁.rTensor Q).comp (q.lTensor M₁)) z = 0
      rw [hcommq, LinearMap.comp_apply, hz, hqzero]
    obtain ⟨t, ht⟩ := (hv₁ z).mp hzq
    have hft : (f₁.rTensor N) t = d := by
      apply hiM₂
      have hc := congrArg (fun k => k t) hcomm₁
      simp only [LinearMap.comp_apply] at hc
      calc
        (i.lTensor M₂) ((f₁.rTensor N) t) =
            (f₁.rTensor N') ((i.lTensor M₁) t) := hc.symm
        _ = (f₁.rTensor N') z := by rw [ht]
        _ = (i.lTensor M₂) d := hz
    have hfd : (f₂.rTensor N) ((f₁.rTensor N) t) = 0 := by
      change ((f₂.rTensor N).comp (f₁.rTensor N)) t = 0
      have hcomp : f₂.comp f₁ = 0 := by
        ext m
        simpa [LinearMap.comp_apply] using
          congrArg (fun k => k m) h.2.1.comp_eq_zero
      rw [← LinearMap.rTensor_comp, hcomp]
      simp
    have hd₀ : (f₂.rTensor N) d = 0 := by rw [← hft, hfd]
    have hsub : x - y = 0 := by rw [← hd, hd₀]
    exact sub_eq_zero.mp hsub
  exact ⟨hflat₁, hflat₃⟩

/-- Tensoring a universally injective map by an arbitrary module remains
universally injective. -/
theorem universallyInjective_tensor
    {R : Type u} {M N Q : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] N) (hf : universallyInjective f) :
    universallyInjective (f.rTensor Q) := by
  intro S _ _
  intro x y hxy
  let eM := TensorProduct.assoc R M Q S
  let eN := TensorProduct.assoc R N Q S
  have hcomm : eN.toLinearMap.comp ((f.rTensor Q).rTensor S) =
      (f.rTensor (Q ⊗[R] S)).comp eM.toLinearMap := by
    apply TensorProduct.ext_threefold
    intro m q s
    rfl
  apply eM.injective
  apply hf (Q ⊗[R] S)
  have hxy' := congrArg (fun z => eN z) hxy
  have hx := congrArg (fun k => k x) hcomm
  have hy := congrArg (fun k => k y) hcomm
  simp only [LinearMap.comp_apply] at hx hy
  exact hx.symm.trans (hxy'.trans hy)

/-- A composite of universally injective maps is universally injective. -/
theorem universallyInjective_comp
    {R : Type u} {M N P : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : universallyInjective f) (hg : universallyInjective g) :
    universallyInjective (g.comp f) := by
  intro Q _ _
  intro x y hxy
  apply hf Q
  apply hg Q
  rw [LinearMap.rTensor_comp_apply Q, LinearMap.rTensor_comp_apply Q] at hxy
  exact hxy

/-- If a composite is universally injective, then its first factor is
universally injective. -/
theorem universallyInjective_of_comp
    {R : Type u} {M N P : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hgf : universallyInjective (g.comp f)) :
    universallyInjective f := by
  intro Q _ _
  intro x y hxy
  apply hgf Q
  rw [LinearMap.rTensor_comp_apply Q, LinearMap.rTensor_comp_apply Q]
  exact congrArg (fun z => (g.rTensor Q) z) hxy

/-- Finite products of universally exact sequences are universally exact. -/
theorem universallyExact_prod
    {R : Type u} {M₁ M₂ M₃ N₁ N₂ N₃ : Type v} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃)
    (hf : universallyExact f₁ f₂) (hg : universallyExact g₁ g₂) :
    universallyExact (f₁.prodMap g₁) (f₂.prodMap g₂) := by
  sorry

/-! ## The integer example and direct sums -/

abbrev integerDirectSum : Type := ℕ →₀ ℤ

abbrev integerDirectProduct : Type := ℕ → ℤ

/-- The canonical inclusion of the direct sum into the direct product. -/
def integerDirectSumToProduct : integerDirectSum →ₗ[ℤ] integerDirectProduct where
  toFun x n := x n
  map_add' x y := by
    funext n
    simp
  map_smul' a x := by
    funext n
    simp

/-- The cokernel of the direct-sum inclusion. -/
abbrev integerCokernel : Type :=
  integerDirectProduct ⧸ LinearMap.range integerDirectSumToProduct

/-- The quotient map in the integer example. -/
def integerProductToCokernel : integerDirectProduct →ₗ[ℤ] integerCokernel :=
  (LinearMap.range integerDirectSumToProduct).mkQ

/-- The element represented by the sequence of powers of two. -/
def integerPowerSequence : integerDirectProduct :=
  fun n => (2 : ℤ) ^ (n + 1)

/-- The class of the power sequence in the cokernel. -/
def integerPowerClass : integerCokernel :=
  integerProductToCokernel integerPowerSequence

/-- The direct-sum/direct-product sequence is universally exact. -/
theorem integerDirectSumToProduct_universallyExact :
    universallyExact integerDirectSumToProduct integerProductToCokernel := by
  sorry

/-- All three terms in the integer example are flat. -/
theorem integerDirectSumToProduct_flat_terms :
    Module.Flat ℤ integerDirectSum ∧
      Module.Flat ℤ integerDirectProduct ∧
        Module.Flat ℤ integerCokernel := by
  sorry

/-- The power class is divisible by every positive power of two. -/
theorem integerPowerClass_divisible (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : integerCokernel, (2 : ℤ) ^ n • y = integerPowerClass := by
  sorry

/-- Every section of the quotient map kills the power class. -/
theorem integerPowerClass_killed_by_section
    (s : integerCokernel →ₗ[ℤ] integerDirectProduct)
    (hs : integerProductToCokernel.comp s = LinearMap.id) :
    s integerPowerClass = 0 := by
  sorry

/-- The integer universally exact sequence does not split. -/
theorem integerDirectSumToProduct_not_split :
    ¬ ∃ s : integerCokernel →ₗ[ℤ] integerDirectProduct,
      integerProductToCokernel.comp s = LinearMap.id := by
  sorry

/-- Taking a direct sum with a non-flat split sequence preserves universal
exactness and produces a universally exact nonsplit sequence with no flat term. -/
theorem universallyExact_directSum_with_nonflat_split
    {R : Type u} {M₁ M₂ M₃ M : Type v} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup M] [Module R M]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (h : universallyExact f₁ f₂)
    (hflat₁ : Module.Flat R M₁) (hflat₂ : Module.Flat R M₂)
    (hflat₃ : Module.Flat R M₃) (hM : ¬ Module.Flat R M)
    (hnonsplit : ¬ ∃ s : M₃ →ₗ[R] M₂, f₂.comp s = LinearMap.id) :
    universallyExact
        (f₁.prodMap (splitSequenceInjection (R := R) (M := M)))
        (f₂.prodMap (splitSequenceProjection (R := R) (M := M))) ∧
      (¬ ∃ s : (M₃ × M) →ₗ[R] (M₂ × (M × M)),
        (f₂.prodMap (splitSequenceProjection (R := R) (M := M))).comp s =
          LinearMap.id) ∧
      ¬ Module.Flat R (M₁ × M) ∧
        ¬ Module.Flat R (M₂ × (M × M)) ∧
        ¬ Module.Flat R (M₃ × M) := by
  sorry

/-! ## Universal injectivity over an algebra and at stalks -/

/-- Universal injectivity of a linear map relative to a possibly larger scalar
ring.  The modules carry compatible actions of the base ring and the larger
ring. -/
def universallyInjectiveOver
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M]
    [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (f : M →ₗ[A] N) : Prop :=
  ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
    Function.Injective ((f.restrictScalars R).rTensor Q)

/-- The algebra-specialized form of universal injectivity, with the base-ring
actions obtained by restricting scalars. -/
def universallyInjectiveAsAlgebra
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) : Prop :=
  letI : Module R M := Module.restrictScalars R A M
  letI : Module R N := Module.restrictScalars R A N
  letI : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  letI : IsScalarTower R A N := IsScalarTower.of_compHom R A N
  universallyInjectiveOver (R := R) (A := A) (M := M) (N := N) f

/-- Universal injectivity after localizing at a multiplicative subset. -/
noncomputable def universallyInjectiveLocalizedAsAlgebra
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (S : Submonoid A) (f : M →ₗ[A] N) : Prop :=
  letI : Algebra R (Localization S) :=
    ((algebraMap A (Localization S)).comp (algebraMap R A)).toAlgebra
  universallyInjectiveAsAlgebra
    (R := R) (A := Localization S)
    (LocalizedModule.map S f)

/-- Universal injectivity at a prime of an algebra, viewed over the prime of
the base ring lying below it. -/
noncomputable def universallyInjectiveAtPrimeOver
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (q : Ideal A) [q.IsPrime] (f : M →ₗ[A] N) : Prop :=
  let p := q.comap (algebraMap R A)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  universallyInjectiveAsAlgebra
    (R := Localization.AtPrime p) (A := Localization.AtPrime q)
    (LocalizedModule.map q.primeCompl f)

/-- Universal injectivity can be checked on prime and maximal stalks, either
over the original base ring or over the corresponding localized base ring. -/
theorem universallyInjective_iff_check_stalks
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) :
    (universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
      ∀ (q : Ideal A) [q.IsPrime],
        universallyInjectiveLocalizedAsAlgebra
          (R := R) (A := A) q.primeCompl f) ∧
    (universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
      ∀ (q : Ideal A) [q.IsMaximal],
        universallyInjectiveLocalizedAsAlgebra
          (R := R) (A := A) q.primeCompl f) ∧
    (universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
      ∀ (q : Ideal A) [q.IsPrime],
        universallyInjectiveAtPrimeOver (R := R) (A := A) q f) ∧
    (universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
      ∀ (q : Ideal A) [q.IsMaximal],
        universallyInjectiveAtPrimeOver (R := R) (A := A) q f) := by
  sorry

/-! ## Localization and the finitely generated ideal criterion -/

/-- The ring map induced by localizing an algebra map. -/
noncomputable def localizationRingHom
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) (S' : Submonoid A)
    (hS : ∀ s : R, s ∈ S → algebraMap R A s ∈ S') :
    Localization S →+* Localization S' :=
  IsLocalization.map (Localization S') (algebraMap R A) (fun s hs => hS s hs)

/-- Localization preserves universal injectivity both over the original base
ring and over its localization. -/
theorem universallyInjective_localize
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (S : Submonoid R) (S' : Submonoid A)
    (hS : ∀ s : R, s ∈ S → algebraMap R A s ∈ S')
    (f : M →ₗ[A] N)
    (hf : universallyInjectiveAsAlgebra (R := R) (A := A) f) :
    (letI : Algebra R (Localization S') :=
      ((algebraMap A (Localization S')).comp (algebraMap R A)).toAlgebra
     universallyInjectiveAsAlgebra (R := R) (A := Localization S')
       (LocalizedModule.map S' f)) ∧
    (letI : Algebra (Localization S) (Localization S') :=
      (localizationRingHom S S' hS).toAlgebra
     universallyInjectiveAsAlgebra (R := Localization S)
       (A := Localization S') (LocalizedModule.map S' f)) := by
  sorry

/-- For modules on which the localized target ring already acts, universal
injectivity over the base ring is equivalent to universal injectivity over the
localized base ring. -/
theorem universallyInjective_localize_iff
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) (S' : Submonoid A)
    [AddCommGroup M] [Module A M] [Module (Localization S') M]
    [IsScalarTower A (Localization S') M]
    [AddCommGroup N] [Module A N] [Module (Localization S') N]
    [IsScalarTower A (Localization S') N]
    (hS : ∀ s : R, s ∈ S → algebraMap R A s ∈ S')
    (f : M →ₗ[A] N) :
    universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
      (letI : Algebra (Localization S) (Localization S') :=
        (localizationRingHom S S' hS).toAlgebra
       universallyInjectiveAsAlgebra (R := Localization S)
         (A := Localization S')
         (f.extendScalarsOfIsLocalization S' (Localization S'))) := by
  sorry

/-- The map induced on quotients by a linear map modulo a finitely generated
ideal. -/
def quotientMapByIdeal
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R]
      N ⧸ (I • (⊤ : Submodule R N)) :=
  (I • (⊤ : Submodule R M)).mapQ
    (I • (⊤ : Submodule R N)) f
    (Submodule.smul_top_le_comap_smul_top I f)

/-- Into a flat module, universal injectivity is detected modulo finitely
generated ideals. -/
theorem universallyInjective_into_flat_iff
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hflat : Module.Flat R N) :
    universallyInjective f ↔
      ∀ (I : Ideal R), I.FG →
        Function.Injective (quotientMapByIdeal I f) := by
  sorry

/-! ## Faithfully flat base change -/

/-- Tensoring with a universally injective algebra map reflects injections,
surjections, and bijections of modules. -/
theorem baseChange_reflects_of_universallyInjective_algebraMap
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hA : universallyInjective (Algebra.linearMap R A)) :
    ∀ {M N : Type v} [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
      (Function.Injective (f.rTensor A) → Function.Injective f) ∧
      (Function.Surjective (f.rTensor A) → Function.Surjective f) ∧
      (Function.Bijective (f.rTensor A) → Function.Bijective f) := by
  sorry

/-- A faithfully flat algebra map is universally injective, and contraction
of an extended ideal recovers the original ideal. -/
theorem faithfullyFlat_universallyInjective_and_ideal_comap
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hA : RingHom.FaithfullyFlat (algebraMap R A)) :
    universallyInjective (Algebra.linearMap R A) ∧
      ∀ I : Ideal R,
        (I.map (algebraMap R A)).comap (algebraMap R A) = I := by
  sorry

end

end Formalization.Books.Algebra.Unit82
