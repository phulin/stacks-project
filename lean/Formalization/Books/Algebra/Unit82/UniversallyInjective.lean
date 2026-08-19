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
  intro S _ _ x y hxy
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
  intro Q _ _ x y hxy
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
  intro Q _ _ x y hxy
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply Prod.ext
    · apply hf.1
      simpa using congrArg Prod.fst hxy
    · apply hg.1
      simpa using congrArg Prod.snd hxy
  · intro y
    constructor
    · intro hy
      have hy₁ : f₂ y.1 = 0 := by
        simpa using congrArg Prod.fst hy
      have hy₂ : g₂ y.2 = 0 := by
        simpa using congrArg Prod.snd hy
      obtain ⟨x, hx⟩ := (hf.2.1 y.1).mp hy₁
      obtain ⟨z, hz⟩ := (hg.2.1 y.2).mp hy₂
      exact ⟨(x, z), by simp [hx, hz]⟩
    · rintro ⟨p, hp⟩
      rcases p with ⟨x, z⟩
      have hx : f₂ (f₁ x) = 0 := (hf.2.1 (f₁ x)).mpr ⟨x, rfl⟩
      have hz : g₂ (g₁ z) = 0 := (hg.2.1 (g₁ z)).mpr ⟨z, rfl⟩
      rw [← hp]
      simp [hx, hz]
  · intro y
    obtain ⟨x, hx⟩ := hf.2.2.1 y.1
    obtain ⟨z, hz⟩ := hg.2.2.1 y.2
    exact ⟨(x, z), Prod.ext hx hz⟩
  · intro Q _ _ x y hxy
    let e₁ := TensorProduct.prodLeft R R M₁ N₁ Q
    let e₂ := TensorProduct.prodLeft R R M₂ N₂ Q
    have hcomm : e₂.toLinearMap.comp ((f₁.prodMap g₁).rTensor Q) =
        ((f₁.rTensor Q).prodMap (g₁.rTensor Q)).comp e₁.toLinearMap := by
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.induction_on with
      | zero =>
        change (0, 0) = (0, 0)
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x q => rfl
    apply e₁.injective
    have hxy' := congrArg (fun z => e₂ z) hxy
    have hx := congrArg (fun k => k x) hcomm
    have hy := congrArg (fun k => k y) hcomm
    simp only [LinearMap.comp_apply] at hx hy
    have hxy'' := hx.symm.trans (hxy'.trans hy)
    apply Prod.ext
    · apply hf.2.2.2 Q
      simpa using congrArg Prod.fst hxy''
    · apply hg.2.2.2 Q
      simpa using congrArg Prod.snd hxy''

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
  have hshort :
      Function.Injective integerDirectSumToProduct ∧
        Function.Exact integerDirectSumToProduct integerProductToCokernel ∧
          Function.Surjective integerProductToCokernel := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      ext n
      exact congrFun hxy n
    · dsimp [integerProductToCokernel]
      rw [LinearMap.exact_iff, Submodule.ker_mkQ]
    · exact Submodule.mkQ_surjective _
  have htf : Module.IsTorsionFree ℤ integerCokernel := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro a x hax
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
      (LinearMap.range integerDirectSumToProduct) x
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      have hq : integerProductToCokernel (a • y) = 0 := by
        change a • integerProductToCokernel y = 0
        exact hax
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero
        (LinearMap.range integerDirectSumToProduct)).mp hq
      let z' : integerDirectSum := Finsupp.onFinset z.support y (by
        intro n hn
        by_contra hn'
        have hzn : z n = 0 := by
          by_contra hzn
          exact hn' (Finsupp.mem_support_iff.mpr hzn)
        have hcoord := congrFun hz n
        have hacoord : a * y n = 0 := by
          simpa [integerDirectSumToProduct, Pi.smul_apply, hzn] using hcoord
        exact hn (by exact (mul_eq_zero.mp hacoord).resolve_left ha)
        )
      have hy : integerDirectSumToProduct z' = y := by
        funext n
        simp [integerDirectSumToProduct, z']
      rw [← hy]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z', rfl⟩
  have hflat₃ : Module.Flat ℤ integerCokernel := by
    let _ : Module.IsTorsionFree ℤ integerCokernel := htf
    infer_instance
  refine ⟨hshort.1, hshort.2.1, hshort.2.2, ?_⟩
  intro Q _ _
  let _ : Module.Flat ℤ integerCokernel := hflat₃
  have h := Formalization.Books.Algebra.Unit39.flat_tensor_short_exact
    (N := Q) integerDirectSumToProduct integerProductToCokernel hshort.2.1 hshort.1
      hshort.2.2
  rw [LinearMap.lTensor_inj_iff_rTensor_inj] at h
  exact h.1

/-- All three terms in the integer example are flat. -/
theorem integerDirectSumToProduct_flat_terms :
    Module.Flat ℤ integerDirectSum ∧
      Module.Flat ℤ integerDirectProduct ∧
        Module.Flat ℤ integerCokernel := by
  have hflat₁ : Module.Flat ℤ integerDirectSum := by
    infer_instance
  have hflat₂ : Module.Flat ℤ integerDirectProduct := by
    infer_instance
  have hends := flat_ends_of_universallyExact integerDirectSumToProduct
    integerProductToCokernel integerDirectSumToProduct_universallyExact hflat₂
  exact ⟨hflat₁, hflat₂, hends.2⟩

/-- The power class is divisible by every positive power of two. -/
theorem integerPowerClass_divisible (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : integerCokernel, (2 : ℤ) ^ n • y = integerPowerClass := by
  have _hn0 : n ≠ 0 := Nat.ne_of_gt hn
  let y : integerDirectProduct := fun k => (2 : ℤ) ^ (k + 1 - n)
  let d : integerDirectProduct :=
    integerPowerSequence - (2 : ℤ) ^ n • y
  let z : integerDirectSum := Finsupp.onFinset (Finset.range n) d (by
    intro k hk
    by_contra hk'
    have hkn : n ≤ k := Nat.le_of_not_gt (by simpa using hk')
    have hk1 : n ≤ k + 1 := le_trans hkn (Nat.le_succ k)
    have hdecomp : n + (k + 1 - n) = k + 1 := Nat.add_sub_of_le hk1
    have hd : d k = 0 := by
      simp [d, integerPowerSequence, y, ← pow_add, hdecomp]
    exact hk hd
  )
  have hz : integerDirectSumToProduct z = d := by
    funext k
    simp [z, integerDirectSumToProduct]
  have hzero : integerProductToCokernel d = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact ⟨z, hz⟩
  refine ⟨integerProductToCokernel y, ?_⟩
  have hzero' := hzero
  change (2 : ℤ) ^ n • integerProductToCokernel y =
    integerProductToCokernel integerPowerSequence
  change integerProductToCokernel
      (integerPowerSequence - (2 : ℤ) ^ n • y) = 0 at hzero'
  rw [map_sub] at hzero'
  calc
    (2 : ℤ) ^ n • integerProductToCokernel y =
        integerProductToCokernel ((2 : ℤ) ^ n • y) := by rw [map_smul]
    _ = integerProductToCokernel integerPowerSequence :=
      (sub_eq_zero.mp hzero').symm

/-- Every section of the quotient map kills the power class. -/
theorem integerPowerClass_killed_by_section
    (s : integerCokernel →ₗ[ℤ] integerDirectProduct)
    (hs : integerProductToCokernel.comp s = LinearMap.id) :
    s integerPowerClass = 0 := by
  have _ := hs
  funext k
  by_contra hk
  have htwo : ∀ n : ℕ, n < 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          n + 1 ≤ 2 ^ n := by omega
          _ < 2 ^ (n + 1) := by
            rw [pow_succ]
            have hpos : 0 < 2 ^ n := by positivity
            omega
  let n : ℕ := Int.natAbs (s integerPowerClass k) + 1
  have hn : 1 ≤ n := by
    dsimp [n]
    omega
  obtain ⟨y, hy⟩ := integerPowerClass_divisible n hn
  have hy' := congrArg s hy
  have hcoord := congrFun hy' k
  have hdiv : (2 : ℤ) ^ n ∣ s integerPowerClass k := by
    refine ⟨s y k, ?_⟩
    simpa [Pi.smul_apply] using hcoord.symm
  have hdiv' : 2 ^ n ∣ Int.natAbs (s integerPowerClass k) := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hdiv)
  have hle : 2 ^ n ≤ Int.natAbs (s integerPowerClass k) :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hk) hdiv'
  have hlt : Int.natAbs (s integerPowerClass k) < 2 ^ n := by
    dsimp [n]
    exact Nat.lt_of_lt_of_le (by omega) (htwo _)
  exact (Nat.not_lt_of_ge hle) hlt

/-- The integer universally exact sequence does not split. -/
theorem integerDirectSumToProduct_not_split :
    ¬ ∃ s : integerCokernel →ₗ[ℤ] integerDirectProduct,
      integerProductToCokernel.comp s = LinearMap.id := by
  rintro ⟨s, hs⟩
  have hs0 := integerPowerClass_killed_by_section s hs
  have hclass : integerPowerClass = 0 := by
    have h := congrArg (fun g => g integerPowerClass) hs
    rw [LinearMap.comp_apply, hs0] at h
    simpa using h.symm
  change integerProductToCokernel integerPowerSequence = 0 at hclass
  obtain ⟨z, hz⟩ :=
    (Submodule.Quotient.mk_eq_zero (LinearMap.range integerDirectSumToProduct)).mp
      hclass
  have hcoord (n : ℕ) (hn : n ∉ z.support) :
      (0 : ℤ) = (2 : ℤ) ^ (n + 1) := by
    have hz' := congrFun hz n
    have hz0 : z n = 0 := by
      by_contra hz0
      exact hn (Finsupp.mem_support_iff.mpr hz0)
    simpa [integerDirectSumToProduct, hz0, integerPowerSequence] using hz'.symm
  by_cases hsupport : z.support.Nonempty
  · let n : ℕ := z.support.max' hsupport + 1
    have hn : n ∉ z.support := by
      intro hn
      have hle := Finset.le_max' z.support n hn
      dsimp [n] at hle
      omega
    have h := hcoord n hn
    exact (pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)) h.symm
  · have hzsupport : z.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsupport
    have h := hcoord 0 (by simp [hzsupport])
    norm_num at h

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
  have _ := hflat₁
  have _ := hflat₂
  have _ := hflat₃
  refine ⟨universallyExact_prod f₁ f₂
      (splitSequenceInjection (R := R) (M := M))
      (splitSequenceProjection (R := R) (M := M)) h
      (splitSequence_universallyExact (R := R) (M := M)), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    apply hnonsplit
    let i : M₃ →ₗ[R] M₃ × M := LinearMap.inl R M₃ M
    let p : M₂ × (M × M) →ₗ[R] M₂ := LinearMap.fst R M₂ (M × M)
    refine ⟨(p.comp s).comp i, ?_⟩
    apply LinearMap.ext
    intro x
    have h := congrArg (fun g => g (i x)) hs
    simpa [i, p, LinearMap.comp_apply, splitSequenceProjection] using
      congrArg Prod.fst h
  · intro hprod
    exact hM (Module.Flat.of_retract (f := hprod)
      (LinearMap.inr R M₁ M) (LinearMap.snd R M₁ M) rfl)
  · intro hprod
    have hprod' : Module.Flat R (M × M) :=
      Module.Flat.of_retract (f := hprod)
        (LinearMap.inr R M₂ (M × M)) (LinearMap.snd R M₂ (M × M)) rfl
    exact (splitSequence_nonflat hM).2.1 hprod'
  · intro hprod
    exact hM (Module.Flat.of_retract (f := hprod)
      (LinearMap.inr R M₃ M) (LinearMap.snd R M₃ M) rfl)

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
  let _ : Module R M := Module.restrictScalars R A M
  let _ : Module R N := Module.restrictScalars R A N
  let _ : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let _ : IsScalarTower R A N := IsScalarTower.of_compHom R A N
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
  let _ : Module R M := Module.restrictScalars R A M
  let _ : Module R N := Module.restrictScalars R A N
  let _ : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let _ : IsScalarTower R A N := IsScalarTower.of_compHom R A N
  have hprime :
      universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
        ∀ (q : Ideal A) [q.IsPrime],
          universallyInjectiveLocalizedAsAlgebra
            (R := R) (A := A) q.primeCompl f := by
    constructor
    · intro hf q
      dsimp [universallyInjectiveLocalizedAsAlgebra, universallyInjectiveAsAlgebra,
        universallyInjectiveOver]
      intro _ Q _ _
      let _ : Module R (LocalizedModule q.primeCompl M) :=
        Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl M)
      let _ : Module R (LocalizedModule q.primeCompl N) :=
        Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl N)
      let _ : SMul R (LocalizedModule q.primeCompl M) :=
        (Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl M)).toSMul
      let _ : SMul R (LocalizedModule q.primeCompl N) :=
        (Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl N)).toSMul
      let _ : IsScalarTower R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl M) :=
        IsScalarTower.of_compHom R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl M)
      let _ : IsScalarTower R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl N) :=
        IsScalarTower.of_compHom R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl N)
      let _ : IsScalarTower R A (LocalizedModule q.primeCompl M) := by
        apply IsScalarTower.of_algebraMap_smul
        intro r x
        rw [← IsScalarTower.algebraMap_smul (R := A) (A := Localization q.primeCompl)
          (algebraMap R A r) x]
        change _ = (algebraMap R (Localization q.primeCompl) r) • x
        congr 1
      let _ : IsScalarTower R A (LocalizedModule q.primeCompl N) := by
        apply IsScalarTower.of_algebraMap_smul
        intro r x
        rw [← IsScalarTower.algebraMap_smul (R := A) (A := Localization q.primeCompl)
          (algebraMap R A r) x]
        congr 1
      let F : (M ⊗[R] Q) →ₗ[A] (N ⊗[R] Q) :=
        TensorProduct.AlgebraTensorModule.rTensor R Q f
      have hF : Function.Injective F := by
        change Function.Injective ((f.restrictScalars R).rTensor Q)
        exact hf Q
      let gM : M →ₗ[A] LocalizedModule q.primeCompl M :=
        LocalizedModule.mkLinearMap q.primeCompl M
      let gN : N →ₗ[A] LocalizedModule q.primeCompl N :=
        LocalizedModule.mkLinearMap q.primeCompl N
      let gMQ : M ⊗[R] Q →ₗ[A]
          LocalizedModule q.primeCompl M ⊗[R] Q :=
        TensorProduct.AlgebraTensorModule.rTensor R Q gM
      let gNQ : N ⊗[R] Q →ₗ[A]
          LocalizedModule q.primeCompl N ⊗[R] Q :=
        TensorProduct.AlgebraTensorModule.rTensor R Q gN
      have hmap :
          IsLocalizedModule.map q.primeCompl gMQ gNQ F =
            TensorProduct.AlgebraTensorModule.rTensor R Q
              (LocalizedModule.map q.primeCompl f) := by
        apply IsLocalizedModule.linearMap_ext q.primeCompl gMQ gNQ
        dsimp [gMQ, gNQ, F]
        rw [IsLocalizedModule.map_comp]
        apply LinearMap.ext
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
            have hmk : LocalizedModule.map q.primeCompl f (gM x) = gN (f x) := by
              dsimp [gM, gN, LocalizedModule.mkLinearMap]
              exact LocalizedModule.map_mk q.primeCompl f x 1
            change gN (f x) ⊗ₜ[R] y = LocalizedModule.map q.primeCompl f (gM x) ⊗ₜ[R] y
            rw [hmk]
      change Function.Injective
        (TensorProduct.AlgebraTensorModule.rTensor R Q
          (LocalizedModule.map q.primeCompl f))
      have hinj := IsLocalizedModule.map_injective q.primeCompl gMQ gNQ F hF
      rw [hmap] at hinj
      exact hinj
    · intro h
      dsimp [universallyInjectiveAsAlgebra, universallyInjectiveOver]
      intro Q _ _
      let F : (M ⊗[R] Q) →ₗ[A] (N ⊗[R] Q) :=
        TensorProduct.AlgebraTensorModule.rTensor R Q f
      refine injective_of_isLocalized_maximal
        (Mₚ := fun q _ ↦
          LocalizedModule q.primeCompl M ⊗[R] Q)
        (f := fun q _ ↦
          TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.mkLinearMap q.primeCompl M))
        (Nₚ := fun q _ ↦
          LocalizedModule q.primeCompl N ⊗[R] Q)
        (g := fun q _ ↦
          TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.mkLinearMap q.primeCompl N)) F ?_
      intro q hq
      let mM₀ : Module R (LocalizedModule q.primeCompl M) := inferInstance
      let mN₀ : Module R (LocalizedModule q.primeCompl N) := inferInstance
      let mM₁ : Module R (LocalizedModule q.primeCompl M) :=
        Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl M)
      let mN₁ : Module R (LocalizedModule q.primeCompl N) :=
        Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl N)
      let lF : @LinearMap R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl N) _ _ mM₁ mN₁ :=
        @LinearMap.mk R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl N) _ _ mM₁ mN₁
          { toFun := LocalizedModule.map q.primeCompl f
            map_add' := by intro x y; exact map_add _ _ _ }
          (by
            intro r x
            calc
              LocalizedModule.map q.primeCompl f
                  (@SMul.smul R (LocalizedModule q.primeCompl M) mM₁.toSMul r x) =
                  LocalizedModule.map q.primeCompl f
                    ((algebraMap R (Localization q.primeCompl) r) • x) := by rfl
              _ = (algebraMap R (Localization q.primeCompl) r) •
                  LocalizedModule.map q.primeCompl f x := by
                rw [map_smul]
              _ = @SMul.smul R (LocalizedModule q.primeCompl N) mN₁.toSMul r
                  (LocalizedModule.map q.primeCompl f x) := by rfl)
      let _ : Module R (LocalizedModule q.primeCompl M) := mM₀
      let _ : Module R (LocalizedModule q.primeCompl N) := mN₀
      have hsmulM (r : R) (x : LocalizedModule q.primeCompl M) :
          @SMul.smul R (LocalizedModule q.primeCompl M) mM₀.toSMul r x =
            @SMul.smul R (LocalizedModule q.primeCompl M) mM₁.toSMul r x := by
        calc
          @SMul.smul R (LocalizedModule q.primeCompl M) mM₀.toSMul r x =
              (algebraMap R (Localization q.primeCompl) r) • x := by
            symm
            exact IsScalarTower.algebraMap_smul (R := R)
              (A := Localization q.primeCompl) r x
          _ = @SMul.smul R (LocalizedModule q.primeCompl M) mM₁.toSMul r x := by
            rfl
      have hsmulN (r : R) (x : LocalizedModule q.primeCompl N) :
          @SMul.smul R (LocalizedModule q.primeCompl N) mN₀.toSMul r x =
            @SMul.smul R (LocalizedModule q.primeCompl N) mN₁.toSMul r x := by
        calc
          @SMul.smul R (LocalizedModule q.primeCompl N) mN₀.toSMul r x =
              (algebraMap R (Localization q.primeCompl) r) • x := by
            symm
            exact IsScalarTower.algebraMap_smul (R := R)
              (A := Localization q.primeCompl) r x
          _ = @SMul.smul R (LocalizedModule q.primeCompl N) mN₁.toSMul r x := by
            rfl
      let lM : @LinearMap R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl M) _ _ mM₀ mM₁ :=
        @LinearMap.mk R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl M) _ _ mM₀ mM₁
          { toFun := id
            map_add' := by intro x y; rfl }
          (by intro r x; exact hsmulM r x)
      let lN : @LinearMap R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl N) (LocalizedModule q.primeCompl N) _ _ mN₀ mN₁ :=
        @LinearMap.mk R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl N) (LocalizedModule q.primeCompl N) _ _ mN₀ mN₁
          { toFun := id
            map_add' := by intro x y; rfl }
          (by intro r x; exact hsmulN r x)
      let lMInv : @LinearMap R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl M) _ _ mM₁ mM₀ :=
        @LinearMap.mk R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl M) _ _ mM₁ mM₀
          { toFun := id
            map_add' := by intro x y; rfl }
          (by intro r x; exact (hsmulM r x).symm)
      let lNInv : @LinearMap R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl N) (LocalizedModule q.primeCompl N) _ _ mN₁ mN₀ :=
        @LinearMap.mk R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl N) (LocalizedModule q.primeCompl N) _ _ mN₁ mN₀
          { toFun := id
            map_add' := by intro x y; rfl }
          (by intro r x; exact (hsmulN r x).symm)
      let eMQ := @TensorProduct.map R R _ _ (RingHom.id R)
        (LocalizedModule q.primeCompl M) Q (LocalizedModule q.primeCompl M) Q
        _ _ _ _ mM₀ inferInstance mM₁ inferInstance lM (LinearMap.id : Q →ₗ[R] Q)
      let eNQ := @TensorProduct.map R R _ _ (RingHom.id R)
        (LocalizedModule q.primeCompl N) Q (LocalizedModule q.primeCompl N) Q
        _ _ _ _ mN₀ inferInstance mN₁ inferInstance lN (LinearMap.id : Q →ₗ[R] Q)
      let eMQInv := @TensorProduct.map R R _ _ (RingHom.id R)
        (LocalizedModule q.primeCompl M) Q (LocalizedModule q.primeCompl M) Q
        _ _ _ _ mM₁ inferInstance mM₀ inferInstance lMInv (LinearMap.id : Q →ₗ[R] Q)
      let eNQInv := @TensorProduct.map R R _ _ (RingHom.id R)
        (LocalizedModule q.primeCompl N) Q (LocalizedModule q.primeCompl N) Q
        _ _ _ _ mN₁ inferInstance mN₀ inferInstance lNInv (LinearMap.id : Q →ₗ[R] Q)
      let lFQ := @LinearMap.rTensor R _ Q
        (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl N)
        _ _ _ inferInstance mM₁ mN₁ lF
      have hlM : lMInv.comp lM = LinearMap.id := by
        apply LinearMap.ext
        intro x
        rfl
      have heMQ : Function.Injective eMQ := by
        intro x y hxy
        have hxy' := congrArg eMQInv hxy
        simpa [eMQ, eMQInv, TensorProduct.map_map, hlM] using hxy'
      let gM : M →ₗ[A] LocalizedModule q.primeCompl M :=
        LocalizedModule.mkLinearMap q.primeCompl M
      let gN : N →ₗ[A] LocalizedModule q.primeCompl N :=
        LocalizedModule.mkLinearMap q.primeCompl N
      let gMQ : M ⊗[R] Q →ₗ[A]
          LocalizedModule q.primeCompl M ⊗[R] Q :=
        TensorProduct.AlgebraTensorModule.rTensor R Q gM
      let gNQ : N ⊗[R] Q →ₗ[A]
          LocalizedModule q.primeCompl N ⊗[R] Q :=
        TensorProduct.AlgebraTensorModule.rTensor R Q gN
      have hmap :
          IsLocalizedModule.map q.primeCompl gMQ gNQ F =
            TensorProduct.AlgebraTensorModule.rTensor R Q
              (LocalizedModule.map q.primeCompl f) := by
        apply IsLocalizedModule.linearMap_ext q.primeCompl gMQ gNQ
        dsimp [gMQ, gNQ, F]
        rw [IsLocalizedModule.map_comp]
        apply LinearMap.ext
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
            have hmk : LocalizedModule.map q.primeCompl f (gM x) = gN (f x) := by
              dsimp [gM, gN, LocalizedModule.mkLinearMap]
              exact LocalizedModule.map_mk q.primeCompl f x 1
            change gN (f x) ⊗ₜ[R] y = LocalizedModule.map q.primeCompl f (gM x) ⊗ₜ[R] y
            rw [hmk]
      have hq'_prime := h q
      dsimp [universallyInjectiveLocalizedAsAlgebra, universallyInjectiveAsAlgebra,
        universallyInjectiveOver] at hq'_prime
      have hq''_prime := hq'_prime Q
      have htransport (x : LocalizedModule q.primeCompl M ⊗[R] Q) :
          eNQ ((TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.map q.primeCompl f)) x) =
            lFQ (eMQ x) := by
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y => simp [eMQ, eNQ, lFQ, lF, lM, lN]
      have hqL : Function.Injective lFQ := by
        intro x y hxy
        apply hq''_prime
        calc
          _ = lFQ x := by
            clear hxy
            induction x using TensorProduct.induction_on with
            | zero => simp [lFQ, lF]
            | add x y hx hy => simp only [map_add, hx, hy]
            | tmul x y => simp [lFQ, lF]
          _ = lFQ y := hxy
          _ = _ := by
            clear hxy
            induction y using TensorProduct.induction_on with
            | zero => simp [lFQ, lF]
            | add x y hx hy => simp only [map_add, hx, hy]
            | tmul x y => simp [lFQ, lF]
      have hqF : Function.Injective
          (TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.map q.primeCompl f)) := by
        intro x y hxy
        apply heMQ
        apply hqL
        rw [← htransport x, ← htransport y, hxy]
      rw [hmap]
      exact hqF
  have hmax :
      universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
        ∀ (q : Ideal A) [q.IsMaximal],
          universallyInjectiveLocalizedAsAlgebra
            (R := R) (A := A) q.primeCompl f := by
    constructor
    · intro hf q
      dsimp [universallyInjectiveLocalizedAsAlgebra, universallyInjectiveAsAlgebra,
        universallyInjectiveOver]
      intro _ Q _ _
      let F : (M ⊗[R] Q) →ₗ[A] (N ⊗[R] Q) :=
        TensorProduct.AlgebraTensorModule.rTensor R Q f
      have hF : Function.Injective F := by
        change Function.Injective ((f.restrictScalars R).rTensor Q)
        exact hf Q
      let _ : Module R (LocalizedModule q.primeCompl M) :=
        Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl M)
      let _ : Module R (LocalizedModule q.primeCompl N) :=
        Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl N)
      let _ : SMul R (LocalizedModule q.primeCompl M) :=
        (Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl M)).toSMul
      let _ : SMul R (LocalizedModule q.primeCompl N) :=
        (Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl N)).toSMul
      let _ : IsScalarTower R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl M) :=
        IsScalarTower.of_compHom R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl M)
      let _ : IsScalarTower R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl N) :=
        IsScalarTower.of_compHom R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl N)
      let _ : IsScalarTower R A (LocalizedModule q.primeCompl M) := by
        apply IsScalarTower.of_algebraMap_smul
        intro r x
        rw [← IsScalarTower.algebraMap_smul (R := A) (A := Localization q.primeCompl)
          (algebraMap R A r) x]
        congr 1
      let _ : IsScalarTower R A (LocalizedModule q.primeCompl N) := by
        apply IsScalarTower.of_algebraMap_smul
        intro r x
        rw [← IsScalarTower.algebraMap_smul (R := A) (A := Localization q.primeCompl)
          (algebraMap R A r) x]
        congr 1
      let gM : M →ₗ[A] LocalizedModule q.primeCompl M :=
        LocalizedModule.mkLinearMap q.primeCompl M
      let gN : N →ₗ[A] LocalizedModule q.primeCompl N :=
        LocalizedModule.mkLinearMap q.primeCompl N
      let gMQ : M ⊗[R] Q →ₗ[A]
          LocalizedModule q.primeCompl M ⊗[R] Q :=
        TensorProduct.AlgebraTensorModule.rTensor R Q gM
      let gNQ : N ⊗[R] Q →ₗ[A]
          LocalizedModule q.primeCompl N ⊗[R] Q :=
        TensorProduct.AlgebraTensorModule.rTensor R Q gN
      have hmap :
          IsLocalizedModule.map q.primeCompl gMQ gNQ F =
            TensorProduct.AlgebraTensorModule.rTensor R Q
              (LocalizedModule.map q.primeCompl f) := by
        apply IsLocalizedModule.linearMap_ext q.primeCompl gMQ gNQ
        dsimp [gMQ, gNQ, F]
        rw [IsLocalizedModule.map_comp]
        apply LinearMap.ext
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
            have hmk : LocalizedModule.map q.primeCompl f (gM x) = gN (f x) := by
              dsimp [gM, gN, LocalizedModule.mkLinearMap]
              exact LocalizedModule.map_mk q.primeCompl f x 1
            change gN (f x) ⊗ₜ[R] y = LocalizedModule.map q.primeCompl f (gM x) ⊗ₜ[R] y
            rw [hmk]
      have hmapR :
          (IsLocalizedModule.map q.primeCompl gMQ gNQ F).restrictScalars R =
            LinearMap.rTensor Q
              ((LocalizedModule.map q.primeCompl f).restrictScalars R) := by
        rw [hmap]
        rfl
      have hinj := IsLocalizedModule.map_injective q.primeCompl gMQ gNQ F hF
      have hinjR : Function.Injective
          ((IsLocalizedModule.map q.primeCompl gMQ gNQ F).restrictScalars R) := by
        intro x y hxy
        exact hinj hxy
      rw [hmapR] at hinjR
      exact hinjR
    · intro h
      dsimp [universallyInjectiveAsAlgebra, universallyInjectiveOver]
      intro Q _ _
      let F : (M ⊗[R] Q) →ₗ[A] (N ⊗[R] Q) :=
        TensorProduct.AlgebraTensorModule.rTensor R Q f
      refine injective_of_isLocalized_maximal
        (Mₚ := fun q _ ↦
          LocalizedModule q.primeCompl M ⊗[R] Q)
        (f := fun q _ ↦
          TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.mkLinearMap q.primeCompl M))
        (Nₚ := fun q _ ↦
          LocalizedModule q.primeCompl N ⊗[R] Q)
        (g := fun q _ ↦
          TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.mkLinearMap q.primeCompl N)) F ?_
      intro q hq
      let mM₀ : Module R (LocalizedModule q.primeCompl M) := inferInstance
      let mN₀ : Module R (LocalizedModule q.primeCompl N) := inferInstance
      let mM₁ : Module R (LocalizedModule q.primeCompl M) :=
        Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl M)
      let mN₁ : Module R (LocalizedModule q.primeCompl N) :=
        Module.restrictScalars R (Localization q.primeCompl)
          (LocalizedModule q.primeCompl N)
      let lF : @LinearMap R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl N) _ _ mM₁ mN₁ :=
        @LinearMap.mk R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl N)
          _ _ mM₁ mN₁
          { toFun := LocalizedModule.map q.primeCompl f
            map_add' := by intro x y; exact map_add _ _ _ }
          (by
            intro r x
            calc
              LocalizedModule.map q.primeCompl f
                  (@SMul.smul R (LocalizedModule q.primeCompl M) mM₁.toSMul r x) =
                  LocalizedModule.map q.primeCompl f
                    ((algebraMap R (Localization q.primeCompl) r) • x) := by rfl
              _ = (algebraMap R (Localization q.primeCompl) r) •
                  LocalizedModule.map q.primeCompl f x := by
                rw [map_smul]
              _ = @SMul.smul R (LocalizedModule q.primeCompl N) mN₁.toSMul r
                  (LocalizedModule.map q.primeCompl f x) := by rfl)
      let _ : Module R (LocalizedModule q.primeCompl M) := mM₀
      let _ : Module R (LocalizedModule q.primeCompl N) := mN₀
      have hsmulM (r : R) (x : LocalizedModule q.primeCompl M) :
          @SMul.smul R (LocalizedModule q.primeCompl M) mM₀.toSMul r x =
            @SMul.smul R (LocalizedModule q.primeCompl M) mM₁.toSMul r x := by
        calc
          @SMul.smul R (LocalizedModule q.primeCompl M) mM₀.toSMul r x =
              (algebraMap R (Localization q.primeCompl) r) • x := by
            symm
            exact IsScalarTower.algebraMap_smul (R := R)
              (A := Localization q.primeCompl) r x
          _ = @SMul.smul R (LocalizedModule q.primeCompl M) mM₁.toSMul r x := by
            rfl
      have hsmulN (r : R) (x : LocalizedModule q.primeCompl N) :
          @SMul.smul R (LocalizedModule q.primeCompl N) mN₀.toSMul r x =
            @SMul.smul R (LocalizedModule q.primeCompl N) mN₁.toSMul r x := by
        calc
          @SMul.smul R (LocalizedModule q.primeCompl N) mN₀.toSMul r x =
              (algebraMap R (Localization q.primeCompl) r) • x := by
            symm
            exact IsScalarTower.algebraMap_smul (R := R)
              (A := Localization q.primeCompl) r x
          _ = @SMul.smul R (LocalizedModule q.primeCompl N) mN₁.toSMul r x := by
            rfl
      let lM : @LinearMap R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl M) _ _ mM₀ mM₁ :=
        @LinearMap.mk R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl M)
          _ _ mM₀ mM₁
          { toFun := id
            map_add' := by intro x y; rfl }
          (by intro r x; exact hsmulM r x)
      let lN : @LinearMap R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl N) (LocalizedModule q.primeCompl N) _ _ mN₀ mN₁ :=
        @LinearMap.mk R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl N) (LocalizedModule q.primeCompl N)
          _ _ mN₀ mN₁
          { toFun := id
            map_add' := by intro x y; rfl }
          (by intro r x; exact hsmulN r x)
      let lMInv : @LinearMap R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl M) _ _ mM₁ mM₀ :=
        @LinearMap.mk R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl M)
          _ _ mM₁ mM₀
          { toFun := id
            map_add' := by intro x y; rfl }
          (by intro r x; exact (hsmulM r x).symm)
      let eMQ := @TensorProduct.map R R _ _ (RingHom.id R)
        (LocalizedModule q.primeCompl M) Q (LocalizedModule q.primeCompl M) Q
        _ _ _ _ mM₀ inferInstance mM₁ inferInstance lM (LinearMap.id : Q →ₗ[R] Q)
      let eMQInv := @TensorProduct.map R R _ _ (RingHom.id R)
        (LocalizedModule q.primeCompl M) Q (LocalizedModule q.primeCompl M) Q
        _ _ _ _ mM₁ inferInstance mM₀ inferInstance lMInv (LinearMap.id : Q →ₗ[R] Q)
      let eNQ := @TensorProduct.map R R _ _ (RingHom.id R)
        (LocalizedModule q.primeCompl N) Q (LocalizedModule q.primeCompl N) Q
        _ _ _ _ mN₀ inferInstance mN₁ inferInstance lN (LinearMap.id : Q →ₗ[R] Q)
      let lFQ := @LinearMap.rTensor R _ Q
        (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl N)
        _ _ _ inferInstance mM₁ mN₁ lF
      have hlM : lMInv.comp lM = LinearMap.id := by
        apply LinearMap.ext
        intro x
        rfl
      have heMQ : Function.Injective eMQ := by
        intro x y hxy
        have hxy' := congrArg eMQInv hxy
        simpa [eMQ, eMQInv, TensorProduct.map_map, hlM] using hxy'
      let gM : M →ₗ[A] LocalizedModule q.primeCompl M :=
        LocalizedModule.mkLinearMap q.primeCompl M
      let gN : N →ₗ[A] LocalizedModule q.primeCompl N :=
        LocalizedModule.mkLinearMap q.primeCompl N
      let gMQ : M ⊗[R] Q →ₗ[A]
          LocalizedModule q.primeCompl M ⊗[R] Q :=
        TensorProduct.AlgebraTensorModule.rTensor R Q gM
      let gNQ : N ⊗[R] Q →ₗ[A]
          LocalizedModule q.primeCompl N ⊗[R] Q :=
        TensorProduct.AlgebraTensorModule.rTensor R Q gN
      have hmap :
          IsLocalizedModule.map q.primeCompl gMQ gNQ F =
            TensorProduct.AlgebraTensorModule.rTensor R Q
              (LocalizedModule.map q.primeCompl f) := by
        apply IsLocalizedModule.linearMap_ext q.primeCompl gMQ gNQ
        dsimp [gMQ, gNQ, F]
        rw [IsLocalizedModule.map_comp]
        apply LinearMap.ext
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
            have hmk : LocalizedModule.map q.primeCompl f (gM x) = gN (f x) := by
              dsimp [gM, gN, LocalizedModule.mkLinearMap]
              exact LocalizedModule.map_mk q.primeCompl f x 1
            change gN (f x) ⊗ₜ[R] y = LocalizedModule.map q.primeCompl f (gM x) ⊗ₜ[R] y
            rw [hmk]
      have hq' := h q
      dsimp [universallyInjectiveLocalizedAsAlgebra, universallyInjectiveAsAlgebra,
        universallyInjectiveOver] at hq'
      have hq'' := hq' Q
      have htransport (x : LocalizedModule q.primeCompl M ⊗[R] Q) :
          eNQ ((TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.map q.primeCompl f)) x) =
            lFQ (eMQ x) := by
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y => simp [eMQ, eNQ, lFQ, lF, lM, lN]
      have hqL : Function.Injective lFQ := by
        intro x y hxy
        apply hq''
        calc
          _ = lFQ x := by
            clear hxy
            induction x using TensorProduct.induction_on with
            | zero => simp [lFQ, lF]
            | add x y hx hy => simp only [map_add, hx, hy]
            | tmul x y => simp [lFQ, lF]
          _ = lFQ y := hxy
          _ = _ := by
            clear hxy
            induction y using TensorProduct.induction_on with
            | zero => simp [lFQ, lF]
            | add x y hx hy => simp only [map_add, hx, hy]
            | tmul x y => simp [lFQ, lF]
      have hqF : Function.Injective
          (TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.map q.primeCompl f)) := by
        intro x y hxy
        apply heMQ
        apply hqL
        rw [← htransport x, ← htransport y, hxy]
      rw [hmap]
      exact hqF
  have hlocalize_prime : ∀ (q : Ideal A) [q.IsPrime],
      universallyInjectiveLocalizedAsAlgebra
          (R := R) (A := A) q.primeCompl f ↔
        universallyInjectiveAtPrimeOver (R := R) (A := A) q f := by
    intro q _
    constructor
    · intro hq
      let p : Ideal R := q.comap (algebraMap R A)
      let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
        Localization.AtPrime.algebraOfLiesOver p q
      dsimp [universallyInjectiveAtPrimeOver, universallyInjectiveAsAlgebra,
        universallyInjectiveOver]
      intro Q _ _
      let _ : SMul R (LocalizedModule q.primeCompl M) :=
        (Module.restrictScalars R (Localization.AtPrime q)
          (LocalizedModule q.primeCompl M)).toSMul
      let _ : SMul R (LocalizedModule q.primeCompl N) :=
        (Module.restrictScalars R (Localization.AtPrime q)
          (LocalizedModule q.primeCompl N)).toSMul
      let _ : SMul (Localization.AtPrime p) (LocalizedModule q.primeCompl M) :=
        (Module.restrictScalars (Localization.AtPrime p) (Localization.AtPrime q)
          (LocalizedModule q.primeCompl M)).toSMul
      let _ : SMul (Localization.AtPrime p) (LocalizedModule q.primeCompl N) :=
        (Module.restrictScalars (Localization.AtPrime p) (Localization.AtPrime q)
          (LocalizedModule q.primeCompl N)).toSMul
      let _ : Module R (LocalizedModule q.primeCompl M) :=
        Module.restrictScalars R (Localization.AtPrime q)
          (LocalizedModule q.primeCompl M)
      let _ : Module R (LocalizedModule q.primeCompl N) :=
        Module.restrictScalars R (Localization.AtPrime q)
          (LocalizedModule q.primeCompl N)
      let _ : Module (Localization.AtPrime p) (LocalizedModule q.primeCompl M) :=
        Module.restrictScalars (Localization.AtPrime p) (Localization.AtPrime q)
          (LocalizedModule q.primeCompl M)
      let _ : Module (Localization.AtPrime p) (LocalizedModule q.primeCompl N) :=
        Module.restrictScalars (Localization.AtPrime p) (Localization.AtPrime q)
          (LocalizedModule q.primeCompl N)
      let _ : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q)
          (LocalizedModule q.primeCompl M) :=
        IsScalarTower.of_compHom (Localization.AtPrime p) (Localization.AtPrime q)
          (LocalizedModule q.primeCompl M)
      let _ : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q)
          (LocalizedModule q.primeCompl N) :=
        IsScalarTower.of_compHom (Localization.AtPrime p) (Localization.AtPrime q)
          (LocalizedModule q.primeCompl N)
      let _ : IsScalarTower R (Localization.AtPrime p)
          (LocalizedModule q.primeCompl M) := by
        apply IsScalarTower.of_algebraMap_smul
        intro r x
        rw [← IsScalarTower.algebraMap_smul (R := Localization.AtPrime p)
          (A := Localization.AtPrime q) (algebraMap R (Localization.AtPrime p) r) x]
        change _ = @SMul.smul R (LocalizedModule q.primeCompl M)
          (Module.restrictScalars R (Localization.AtPrime q)
            (LocalizedModule q.primeCompl M)).toSMul r x
        change _ = (algebraMap R (Localization.AtPrime q) r) • x
        rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime p)
          (Localization.AtPrime q)]
        rfl
      let _ : IsScalarTower R (Localization.AtPrime p)
          (LocalizedModule q.primeCompl N) := by
        apply IsScalarTower.of_algebraMap_smul
        intro r x
        rw [← IsScalarTower.algebraMap_smul (R := Localization.AtPrime p)
          (A := Localization.AtPrime q) (algebraMap R (Localization.AtPrime p) r) x]
        change _ = @SMul.smul R (LocalizedModule q.primeCompl N)
          (Module.restrictScalars R (Localization.AtPrime q)
            (LocalizedModule q.primeCompl N)).toSMul r x
        change _ = (algebraMap R (Localization.AtPrime q) r) • x
        rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime p)
          (Localization.AtPrime q)]
        rfl
      let _ : Module R Q := Module.restrictScalars R (Localization.AtPrime p) Q
      let _ : IsScalarTower R (Localization.AtPrime p) Q :=
        IsScalarTower.of_compHom R (Localization.AtPrime p) Q
      have hq' := hq
      dsimp [universallyInjectiveLocalizedAsAlgebra, universallyInjectiveAsAlgebra,
        universallyInjectiveOver] at hq'
      have hq'' := hq' Q
      let e := IsLocalization.moduleTensorEquiv (R := R)
        (A := Localization.AtPrime p) (S := p.primeCompl)
        (M₁ := LocalizedModule q.primeCompl M) (M₂ := Q)
      let eN := IsLocalization.moduleTensorEquiv (R := R)
        (A := Localization.AtPrime p) (S := p.primeCompl)
        (M₁ := LocalizedModule q.primeCompl N) (M₂ := Q)
      let mM₁ : Module R (LocalizedModule q.primeCompl M) :=
        Module.restrictScalars R (Localization.AtPrime q)
          (LocalizedModule q.primeCompl M)
      let mN₁ : Module R (LocalizedModule q.primeCompl N) :=
        Module.restrictScalars R (Localization.AtPrime q)
          (LocalizedModule q.primeCompl N)
      let gR : @LinearMap R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl N)
          _ _ mM₁ mN₁ :=
        @LinearMap.mk R R _ _ (RingHom.id R)
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl N)
          _ _ mM₁ mN₁
          { toFun := LocalizedModule.map q.primeCompl f
            map_add' := by intro x y; exact map_add _ _ _ }
          (by
            intro r x
            calc
              LocalizedModule.map q.primeCompl f
                  (@SMul.smul R (LocalizedModule q.primeCompl M) mM₁.toSMul r x) =
                  LocalizedModule.map q.primeCompl f
                    ((algebraMap R (Localization.AtPrime q) r) • x) := by rfl
              _ = (algebraMap R (Localization.AtPrime q) r) •
                  LocalizedModule.map q.primeCompl f x := by
                rw [map_smul]
              _ = @SMul.smul R (LocalizedModule q.primeCompl N) mN₁.toSMul r
                  (LocalizedModule.map q.primeCompl f x) := by rfl)
      let gP : @LinearMap (Localization.AtPrime p) (Localization.AtPrime p)
          _ _ (RingHom.id (Localization.AtPrime p))
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl N)
          _ _
          (Module.restrictScalars (Localization.AtPrime p) (Localization.AtPrime q)
            (LocalizedModule q.primeCompl M))
          (Module.restrictScalars (Localization.AtPrime p) (Localization.AtPrime q)
            (LocalizedModule q.primeCompl N)) :=
        @LinearMap.mk (Localization.AtPrime p) (Localization.AtPrime p)
          _ _ (RingHom.id (Localization.AtPrime p))
          (LocalizedModule q.primeCompl M) (LocalizedModule q.primeCompl N)
          _ _
          (Module.restrictScalars (Localization.AtPrime p) (Localization.AtPrime q)
            (LocalizedModule q.primeCompl M))
          (Module.restrictScalars (Localization.AtPrime p) (Localization.AtPrime q)
            (LocalizedModule q.primeCompl N))
          { toFun := LocalizedModule.map q.primeCompl f
            map_add' := by intro x y; exact map_add _ _ _ }
          (by
            intro r x
            change LocalizedModule.map q.primeCompl f
                ((algebraMap (Localization.AtPrime p) (Localization.AtPrime q) r) • x) = _
            rw [map_smul]
            rfl)
      have hcomm (z : LocalizedModule q.primeCompl M ⊗[Localization.AtPrime p] Q) :
          eN ((LinearMap.rTensor Q gP) z) =
            (LinearMap.rTensor Q gR) (e z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
            simp only [e, eN, IsLocalization.moduleTensorEquiv,
              TensorProduct.equivOfCompatibleSMul,
              TensorProduct.mapOfCompatibleSMul_tmul,
              LinearMap.rTensor_tmul]
            rfl
      intro x y hxy
      apply e.injective
      apply hq''
      calc
        (LinearMap.rTensor Q gR) (e x) = eN ((LinearMap.rTensor Q gP) x) :=
          (hcomm x).symm
        _ = eN ((LinearMap.rTensor Q gP) y) := congrArg eN hxy
        _ = (LinearMap.rTensor Q gR) (e y) := hcomm y
    · intro hq
      let p : Ideal R := q.comap (algebraMap R A)
      let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
        Localization.AtPrime.algebraOfLiesOver p q
      dsimp [universallyInjectiveLocalizedAsAlgebra, universallyInjectiveAsAlgebra,
        universallyInjectiveOver]
      intro Q _ _
      let X := LocalizedModule q.primeCompl M
      let Y := LocalizedModule q.primeCompl N
      let P := Localization.AtPrime p
      let Qp := LocalizedModule p.primeCompl Q
      let _ : SMul P X :=
        (Module.restrictScalars P (Localization.AtPrime q) X).toSMul
      let _ : SMul P Y :=
        (Module.restrictScalars P (Localization.AtPrime q) Y).toSMul
      let _ : Module P X :=
        Module.restrictScalars P (Localization.AtPrime q) X
      let _ : Module P Y :=
        Module.restrictScalars P (Localization.AtPrime q) Y
      let _ : IsScalarTower P (Localization.AtPrime q) X :=
        IsScalarTower.of_compHom P (Localization.AtPrime q) X
      let _ : IsScalarTower P (Localization.AtPrime q) Y :=
        IsScalarTower.of_compHom P (Localization.AtPrime q) Y
      let _ : SMul R X :=
        (Module.restrictScalars R (Localization.AtPrime q) X).toSMul
      let _ : SMul R Y :=
        (Module.restrictScalars R (Localization.AtPrime q) Y).toSMul
      let _ : Module R X := Module.restrictScalars R (Localization.AtPrime q) X
      let _ : Module R Y := Module.restrictScalars R (Localization.AtPrime q) Y
      let _ : IsScalarTower R P X := by
        apply IsScalarTower.of_algebraMap_smul
        intro r x
        rw [← IsScalarTower.algebraMap_smul (R := P)
          (A := Localization.AtPrime q) (algebraMap R P r) x]
        change _ = @SMul.smul R X
          (Module.restrictScalars R (Localization.AtPrime q) X).toSMul r x
        change _ = (algebraMap R (Localization.AtPrime q) r) • x
        rw [IsScalarTower.algebraMap_eq R P (Localization.AtPrime q)]
        rfl
      let _ : IsScalarTower R P Y := by
        apply IsScalarTower.of_algebraMap_smul
        intro r y
        rw [← IsScalarTower.algebraMap_smul (R := P)
          (A := Localization.AtPrime q) (algebraMap R P r) y]
        change _ = @SMul.smul R Y
          (Module.restrictScalars R (Localization.AtPrime q) Y).toSMul r y
        change _ = (algebraMap R (Localization.AtPrime q) r) • y
        rw [IsScalarTower.algebraMap_eq R P (Localization.AtPrime q)]
        rfl
      let eX₀ := IsLocalization.moduleTensorEquiv (R := R)
        (A := Localization p.primeCompl) (S := p.primeCompl)
        (M₁ := X) (M₂ := Qp)
      let eY₀ := IsLocalization.moduleTensorEquiv (R := R)
        (A := Localization p.primeCompl) (S := p.primeCompl)
        (M₁ := Y) (M₂ := Qp)
      let lQ : Q →ₗ[R] Qp := LocalizedModule.mkLinearMap p.primeCompl Q
      let eX : X ⊗[R] Q →ₗ[R] X ⊗[Localization p.primeCompl] Qp :=
        (eX₀.symm.restrictScalars R).toLinearMap.comp
          (TensorProduct.map (LinearMap.id : X →ₗ[R] X) lQ)
      let eY : Y ⊗[R] Q →ₗ[R] Y ⊗[Localization p.primeCompl] Qp :=
        (eY₀.symm.restrictScalars R).toLinearMap.comp
          (TensorProduct.map (LinearMap.id : Y →ₗ[R] Y) lQ)
      let _ : Module P (X ⊗[R] Q) := TensorProduct.leftModule
      let _ : Module P (Y ⊗[R] Q) := TensorProduct.leftModule
      let _ : IsScalarTower R P (X ⊗[R] Q) := by
        apply IsScalarTower.of_algebraMap_smul
        intro r z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z w hz hw => simp only [smul_add, hz, hw]
        | tmul x y =>
            change (algebraMap R P r • x) ⊗ₜ[R] y = (r • x) ⊗ₜ[R] y
            rw [IsScalarTower.algebraMap_smul (R := R) (A := P) r x]
      let _ : IsScalarTower R P (Y ⊗[R] Q) := by
        apply IsScalarTower.of_algebraMap_smul
        intro r z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z w hz hw => simp only [smul_add, hz, hw]
        | tmul x y =>
            change (algebraMap R P r • x) ⊗ₜ[R] y = (r • x) ⊗ₜ[R] y
            rw [IsScalarTower.algebraMap_smul (R := R) (A := P) r x]
      let _ : IsLocalizedModule p.primeCompl
          (LinearMap.id : X →ₗ[R] X) :=
        isLocalizedModule_id p.primeCompl X P
      let _ : IsLocalizedModule p.primeCompl
          (LinearMap.id : Y →ₗ[R] Y) :=
        isLocalizedModule_id p.primeCompl Y P
      have hmapX : IsLocalizedModule p.primeCompl
          (TensorProduct.map (LinearMap.id : X →ₗ[R] X) lQ) := inferInstance
      have hmapY : IsLocalizedModule p.primeCompl
          (TensorProduct.map (LinearMap.id : Y →ₗ[R] Y) lQ) := inferInstance
      have hmapXinj : Function.Injective
          (TensorProduct.map (LinearMap.id : X →ₗ[R] X) lQ) := by
        apply (IsLocalizedModule.injective_iff_isRegular
          (S := p.primeCompl)
          (f := TensorProduct.map (LinearMap.id : X →ₗ[R] X) lQ)).mpr
        intro c
        have hc : IsUnit
            (algebraMap R (Module.End R (X ⊗[R] Q)) (c : R)) := by
          rw [← (Algebra.lsmul R (A := P) R (X ⊗[R] Q)).commutes]
          exact (IsLocalization.map_units P c).map _
        have hreg := hc.isSMulRegular (X ⊗[R] Q)
        intro x y hxy
        apply hreg
        change (c : R) • x = (c : R) • y at hxy
        change (c : R) • x = (c : R) • y
        exact hxy
      have hmapYinj : Function.Injective
          (TensorProduct.map (LinearMap.id : Y →ₗ[R] Y) lQ) := by
        apply (IsLocalizedModule.injective_iff_isRegular
          (S := p.primeCompl)
          (f := TensorProduct.map (LinearMap.id : Y →ₗ[R] Y) lQ)).mpr
        intro c
        have hc : IsUnit
            (algebraMap R (Module.End R (Y ⊗[R] Q)) (c : R)) := by
          rw [← (Algebra.lsmul R (A := P) R (Y ⊗[R] Q)).commutes]
          exact (IsLocalization.map_units P c).map _
        have hreg := hc.isSMulRegular (Y ⊗[R] Q)
        intro x y hxy
        apply hreg
        change (c : R) • x = (c : R) • y at hxy
        change (c : R) • x = (c : R) • y
        exact hxy
      have hxe : Function.Injective eX := by
        intro x y hxy
        apply hmapXinj
        apply (eX₀.symm.restrictScalars R).injective
        simpa [eX] using hxy
      have hye : Function.Injective eY := by
        intro x y hxy
        apply hmapYinj
        apply (eY₀.symm.restrictScalars R).injective
        simpa [eY] using hxy
      have hq' := hq
      dsimp [universallyInjectiveAtPrimeOver, universallyInjectiveAsAlgebra,
        universallyInjectiveOver] at hq'
      have hq'' := hq' Qp
      let gR : @LinearMap R R _ _ (RingHom.id R) X Y _ _
          (Module.restrictScalars R (Localization.AtPrime q) X)
          (Module.restrictScalars R (Localization.AtPrime q) Y) :=
        @LinearMap.mk R R _ _ (RingHom.id R) X Y _ _
          (Module.restrictScalars R (Localization.AtPrime q) X)
          (Module.restrictScalars R (Localization.AtPrime q) Y)
          { toFun := LocalizedModule.map q.primeCompl f
            map_add' := by intro x y; exact map_add _ _ _ }
          (by
            intro r x
            calc
              LocalizedModule.map q.primeCompl f
                  (@SMul.smul R X
                    (Module.restrictScalars R (Localization.AtPrime q) X).toSMul r x) =
                  LocalizedModule.map q.primeCompl f
                    ((algebraMap R (Localization.AtPrime q) r) • x) := by rfl
              _ = (algebraMap R (Localization.AtPrime q) r) •
                  LocalizedModule.map q.primeCompl f x := by
                rw [map_smul]
              _ = @SMul.smul R Y
                  (Module.restrictScalars R (Localization.AtPrime q) Y).toSMul r
                  (LocalizedModule.map q.primeCompl f x) := by rfl)
      have hqP : Function.Injective
          (LinearMap.rTensor Qp
            ((LocalizedModule.map q.primeCompl f).restrictScalars P)) := by
        simpa [X, Y, P, p] using hq''
      have hcomm (z : X ⊗[R] Q) :
          eY ((LinearMap.rTensor Q gR) z) =
            (LinearMap.rTensor Qp
              ((LocalizedModule.map q.primeCompl f).restrictScalars P)) (eX z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
            simp only [eX, eY, gR, lQ,
              LinearMap.comp_apply,
              TensorProduct.map_tmul,
              LinearMap.rTensor_tmul]
            change
              (LocalizedModule.map q.primeCompl f x) ⊗ₜ[P]
                  (LocalizedModule.mkLinearMap p.primeCompl Q y) =
                (LocalizedModule.map q.primeCompl f x) ⊗ₜ[P]
                  (LocalizedModule.mkLinearMap p.primeCompl Q y)
            rfl
      intro x y hxy
      apply hxe
      apply hqP
      calc
        (LinearMap.rTensor Qp
          ((LocalizedModule.map q.primeCompl f).restrictScalars P)) (eX x) =
            eY ((LinearMap.rTensor Q gR) x) :=
          (hcomm x).symm
        _ = eY ((LinearMap.rTensor Q gR) y) := congrArg eY hxy
        _ = (LinearMap.rTensor Qp
          ((LocalizedModule.map q.primeCompl f).restrictScalars P)) (eX y) := hcomm y
  have hprimeAt :
      universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
        ∀ (q : Ideal A) [q.IsPrime],
          universallyInjectiveAtPrimeOver (R := R) (A := A) q f := by
    constructor
    · intro hf q
      exact (hlocalize_prime q).mp ((hprime.mp hf) q)
    · intro hq
      apply hprime.mpr
      intro q
      exact (hlocalize_prime q).mpr (hq q)
  have hmaxAt :
      universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
        ∀ (q : Ideal A) [q.IsMaximal],
          universallyInjectiveAtPrimeOver (R := R) (A := A) q f := by
    constructor
    · intro hf q
      exact (hlocalize_prime q).mp ((hmax.mp hf) q)
    · intro hq
      apply hmax.mpr
      intro q
      exact (hlocalize_prime q).mpr (hq q)
  exact ⟨hprime, hmax, hprimeAt, hmaxAt⟩

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
  let _ : Module R M := Module.restrictScalars R A M
  let _ : Module R N := Module.restrictScalars R A N
  let _ : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let _ : IsScalarTower R A N := IsScalarTower.of_compHom R A N
  constructor
  · dsimp [universallyInjectiveAsAlgebra, universallyInjectiveOver]
    intro Q _ _
    let _ : Module R (LocalizedModule S' M) :=
      Module.restrictScalars R (Localization S') (LocalizedModule S' M)
    let _ : Module R (LocalizedModule S' N) :=
      Module.restrictScalars R (Localization S') (LocalizedModule S' N)
    let _ : SMul R (LocalizedModule S' M) :=
      (Module.restrictScalars R (Localization S') (LocalizedModule S' M)).toSMul
    let _ : SMul R (LocalizedModule S' N) :=
      (Module.restrictScalars R (Localization S') (LocalizedModule S' N)).toSMul
    let _ : IsScalarTower R (Localization S') (LocalizedModule S' M) := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rfl
    let _ : IsScalarTower R (Localization S') (LocalizedModule S' N) := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rfl
    let _ : IsScalarTower R A (LocalizedModule S' M) := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := A) (A := Localization S')
        (algebraMap R A r) x]
      change _ = (algebraMap R (Localization S') r) • x
      congr 1
    let _ : IsScalarTower R A (LocalizedModule S' N) := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := A) (A := Localization S')
        (algebraMap R A r) x]
      change _ = (algebraMap R (Localization S') r) • x
      congr 1
    let F : (M ⊗[R] Q) →ₗ[A] (N ⊗[R] Q) :=
      TensorProduct.AlgebraTensorModule.rTensor R Q f
    have hF : Function.Injective F := by
      change Function.Injective ((f.restrictScalars R).rTensor Q)
      exact hf Q
    let gM : M →ₗ[A] LocalizedModule S' M :=
      LocalizedModule.mkLinearMap S' M
    let gN : N →ₗ[A] LocalizedModule S' N :=
      LocalizedModule.mkLinearMap S' N
    let gMQ : M ⊗[R] Q →ₗ[A]
        LocalizedModule S' M ⊗[R] Q :=
      TensorProduct.AlgebraTensorModule.rTensor R Q gM
    let gNQ : N ⊗[R] Q →ₗ[A]
        LocalizedModule S' N ⊗[R] Q :=
      TensorProduct.AlgebraTensorModule.rTensor R Q gN
    have hmap :
        IsLocalizedModule.map S' gMQ gNQ F =
          TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.map S' f) := by
      apply IsLocalizedModule.linearMap_ext S' gMQ gNQ
      dsimp [gMQ, gNQ, F]
      rw [IsLocalizedModule.map_comp]
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
          have hmk : LocalizedModule.map S' f (gM x) = gN (f x) := by
            dsimp [gM, gN, LocalizedModule.mkLinearMap]
            exact LocalizedModule.map_mk S' f x 1
          change gN (f x) ⊗ₜ[R] y =
            LocalizedModule.map S' f (gM x) ⊗ₜ[R] y
          rw [hmk]
    change Function.Injective
      (TensorProduct.AlgebraTensorModule.rTensor R Q
        (LocalizedModule.map S' f))
    have hinj := IsLocalizedModule.map_injective S' gMQ gNQ F hF
    rw [hmap] at hinj
    exact hinj
  · letI : Algebra R (Localization S') :=
      ((algebraMap A (Localization S')).comp (algebraMap R A)).toAlgebra
    letI : Algebra (Localization S) (Localization S') :=
      (localizationRingHom S S' hS).toAlgebra
    dsimp [universallyInjectiveAsAlgebra, universallyInjectiveOver]
    intro Q _ _
    let X := LocalizedModule S' M
    let Y := LocalizedModule S' N
    let P := Localization S
    let _ : SMul R (Localization S') := Algebra.toSMul
    let _ : Module R (Localization S') := Algebra.toModule
    let _ : SMul R X :=
      (Module.restrictScalars R (Localization S') X).toSMul
    let _ : SMul R Y :=
      (Module.restrictScalars R (Localization S') Y).toSMul
    let _ : SMul P X :=
      (Module.restrictScalars P (Localization S') X).toSMul
    let _ : SMul P Y :=
      (Module.restrictScalars P (Localization S') Y).toSMul
    let _ : Module R X := Module.restrictScalars R (Localization S') X
    let _ : Module R Y := Module.restrictScalars R (Localization S') Y
    let _ : Module P X := Module.restrictScalars P (Localization S') X
    let _ : Module P Y := Module.restrictScalars P (Localization S') Y
    let _ : IsScalarTower P (Localization S') X :=
      IsScalarTower.of_compHom P (Localization S') X
    let _ : IsScalarTower P (Localization S') Y :=
      IsScalarTower.of_compHom P (Localization S') Y
    have hmap :
        (algebraMap P (Localization S')).comp (algebraMap R P) =
          (algebraMap A (Localization S')).comp (algebraMap R A) := by
      change (localizationRingHom S S' hS).comp
          (algebraMap R (Localization S)) =
        (algebraMap A (Localization S')).comp (algebraMap R A)
      exact IsLocalization.map_comp (Q := Localization S') hS
    let _ : IsScalarTower R A (Localization S') :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R P (Localization S') := by
      apply IsScalarTower.of_algebraMap_eq'
      exact hmap.symm
    let _ : IsScalarTower R A X := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := A) (A := Localization S')
        (algebraMap R A r) x]
      change _ = (algebraMap R (Localization S') r) • x
      rw [IsScalarTower.algebraMap_eq R A (Localization S')]
      simp only [RingHom.comp_apply]
    let _ : IsScalarTower R A Y := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := A) (A := Localization S')
        (algebraMap R A r) x]
      change _ = (algebraMap R (Localization S') r) • x
      rw [IsScalarTower.algebraMap_eq R A (Localization S')]
      simp only [RingHom.comp_apply]
    let _ : IsScalarTower R (Localization S') X := by
      exact IsScalarTower.to₁₃₄ R A (Localization S') X
    let _ : IsScalarTower R (Localization S') Y := by
      exact IsScalarTower.to₁₃₄ R A (Localization S') Y
    let _ : IsScalarTower R P X := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := P) (A := Localization S')
        (algebraMap R P r) x]
      change _ = ((algebraMap A (Localization S')).comp (algebraMap R A) r) • x
      exact congrArg (fun z => z • x) (congrArg (fun k => k r) hmap)
    let _ : IsScalarTower R P Y := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := P) (A := Localization S')
        (algebraMap R P r) x]
      change _ = ((algebraMap A (Localization S')).comp (algebraMap R A) r) • x
      exact congrArg (fun z => z • x) (congrArg (fun k => k r) hmap)
    let _ : IsScalarTower R A X := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := A) (A := Localization S')
        (algebraMap R A r) x]
      change _ = (algebraMap R (Localization S') r) • x
      rw [IsScalarTower.algebraMap_eq R A (Localization S')]
      simp only [RingHom.comp_apply]
    let _ : IsScalarTower R A Y := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := A) (A := Localization S')
        (algebraMap R A r) x]
      change _ = (algebraMap R (Localization S') r) • x
      rw [IsScalarTower.algebraMap_eq R A (Localization S')]
      simp only [RingHom.comp_apply]
    let _ : Module R Q := Module.restrictScalars R P Q
    let _ : IsScalarTower R P Q := IsScalarTower.of_compHom R P Q
    let e := IsLocalization.moduleTensorEquiv (R := R)
      (A := Localization S) (S := S)
      (M₁ := X) (M₂ := Q)
    let eN := IsLocalization.moduleTensorEquiv (R := R)
      (A := Localization S) (S := S)
      (M₁ := Y) (M₂ := Q)
    let mM : Module R (LocalizedModule S' M) :=
      Module.restrictScalars R (Localization S') (LocalizedModule S' M)
    let mN : Module R (LocalizedModule S' N) :=
      Module.restrictScalars R (Localization S') (LocalizedModule S' N)
    let gR : @LinearMap R R _ _ (RingHom.id R)
        (LocalizedModule S' M) (LocalizedModule S' N) _ _ mM mN :=
      @LinearMap.mk R R _ _ (RingHom.id R)
        (LocalizedModule S' M) (LocalizedModule S' N) _ _ mM mN
        { toFun := LocalizedModule.map S' f
          map_add' := by intro x y; exact map_add _ _ _ }
        (by
          intro r x
          calc
            LocalizedModule.map S' f
                (@SMul.smul R (LocalizedModule S' M) mM.toSMul r x) =
                LocalizedModule.map S' f
                  ((algebraMap R (Localization S') r) • x) := by rfl
            _ = (algebraMap R (Localization S') r) •
                LocalizedModule.map S' f x := by rw [map_smul]
            _ = @SMul.smul R (LocalizedModule S' N) mN.toSMul r
                (LocalizedModule.map S' f x) := by rfl)
    let gP : @LinearMap (Localization S) (Localization S)
        _ _ (RingHom.id (Localization S))
        (LocalizedModule S' M) (LocalizedModule S' N) _ _
        (Module.restrictScalars (Localization S) (Localization S')
          (LocalizedModule S' M))
        (Module.restrictScalars (Localization S) (Localization S')
          (LocalizedModule S' N)) :=
      (LocalizedModule.map S' f).restrictScalars (Localization S)
    have hq : Function.Injective (LinearMap.rTensor Q gP) := by
      have hR : Function.Injective (LinearMap.rTensor Q gR) := by
        let F : (M ⊗[R] Q) →ₗ[A] (N ⊗[R] Q) :=
          TensorProduct.AlgebraTensorModule.rTensor R Q f
        have hF : Function.Injective F := by
          change Function.Injective ((f.restrictScalars R).rTensor Q)
          exact hf Q
        let gM : M →ₗ[A] LocalizedModule S' M :=
          LocalizedModule.mkLinearMap S' M
        let gN : N →ₗ[A] LocalizedModule S' N :=
          LocalizedModule.mkLinearMap S' N
        let gMQ : M ⊗[R] Q →ₗ[A]
            LocalizedModule S' M ⊗[R] Q :=
          TensorProduct.AlgebraTensorModule.rTensor R Q gM
        let gNQ : N ⊗[R] Q →ₗ[A]
            LocalizedModule S' N ⊗[R] Q :=
          TensorProduct.AlgebraTensorModule.rTensor R Q gN
        have hmap :
            IsLocalizedModule.map S' gMQ gNQ F =
              TensorProduct.AlgebraTensorModule.rTensor R Q
                (LocalizedModule.map S' f) := by
          apply IsLocalizedModule.linearMap_ext S' gMQ gNQ
          dsimp [gMQ, gNQ, F]
          rw [IsLocalizedModule.map_comp]
          apply LinearMap.ext
          intro t
          induction t using TensorProduct.induction_on with
          | zero => simp
          | add x y hx hy => simp only [map_add, hx, hy]
          | tmul x y =>
              have hmk : LocalizedModule.map S' f (gM x) = gN (f x) := by
                dsimp [gM, gN, LocalizedModule.mkLinearMap]
                exact LocalizedModule.map_mk S' f x 1
              change gN (f x) ⊗ₜ[R] y =
                LocalizedModule.map S' f (gM x) ⊗ₜ[R] y
              rw [hmk]
        change Function.Injective
          (TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.map S' f))
        have hinj := IsLocalizedModule.map_injective S' gMQ gNQ F hF
        rw [hmap] at hinj
        exact hinj
      intro x y hxy
      apply e.injective
      apply hR
      have hcomm (z : LocalizedModule S' M ⊗[Localization S] Q) :
          eN ((LinearMap.rTensor Q gP) z) =
            (LinearMap.rTensor Q gR) (e z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
            simp only [e, eN, IsLocalization.moduleTensorEquiv,
              TensorProduct.equivOfCompatibleSMul,
              TensorProduct.mapOfCompatibleSMul_tmul,
              LinearMap.rTensor_tmul]
            rfl
      calc
        (LinearMap.rTensor Q gR) (e x) = eN ((LinearMap.rTensor Q gP) x) :=
          (hcomm x).symm
        _ = eN ((LinearMap.rTensor Q gP) y) := congrArg eN hxy
        _ = (LinearMap.rTensor Q gR) (e y) := hcomm y
    exact hq

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
  let _ : Module R M := Module.restrictScalars R A M
  let _ : Module R N := Module.restrictScalars R A N
  let _ : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let _ : IsScalarTower R A N := IsScalarTower.of_compHom R A N
  constructor
  · intro hf
    letI : Algebra R (Localization S') :=
      ((algebraMap A (Localization S')).comp (algebraMap R A)).toAlgebra
    letI : Algebra (Localization S) (Localization S') :=
      (localizationRingHom S S' hS).toAlgebra
    dsimp [universallyInjectiveAsAlgebra, universallyInjectiveOver]
    intro Q _ _
    let P := Localization S
    let T := Localization S'
    let _ : SMul R T := Algebra.toSMul
    let _ : Module R T := Algebra.toModule
    let _ : SMul P M :=
      (Module.restrictScalars P T M).toSMul
    let _ : SMul P N :=
      (Module.restrictScalars P T N).toSMul
    let _ : Module P M := Module.restrictScalars P T M
    let _ : Module P N := Module.restrictScalars P T N
    let _ : IsScalarTower P T M := IsScalarTower.of_compHom P T M
    let _ : IsScalarTower P T N := IsScalarTower.of_compHom P T N
    have hmap :
        (algebraMap P T).comp (algebraMap R P) =
          (algebraMap A T).comp (algebraMap R A) := by
      change (localizationRingHom S S' hS).comp
          (algebraMap R (Localization S)) =
        (algebraMap A (Localization S')).comp (algebraMap R A)
      exact IsLocalization.map_comp (Q := Localization S') hS
    let _ : IsScalarTower R A T :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R P T := by
      apply IsScalarTower.of_algebraMap_eq'
      exact hmap.symm
    let _ : IsScalarTower R P M := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := P) (A := T)
        (algebraMap R P r) x]
      rw [← IsScalarTower.algebraMap_smul (R := R) (A := A) r x]
      rw [← IsScalarTower.algebraMap_smul (R := A) (A := T)
        (algebraMap R A r) x]
      exact congrArg (fun z => z • x) (congrArg (fun k => k r) hmap)
    let _ : IsScalarTower R P N := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := P) (A := T)
        (algebraMap R P r) x]
      rw [← IsScalarTower.algebraMap_smul (R := R) (A := A) r x]
      rw [← IsScalarTower.algebraMap_smul (R := A) (A := T)
        (algebraMap R A r) x]
      exact congrArg (fun z => z • x) (congrArg (fun k => k r) hmap)
    let _ : Module R Q := Module.restrictScalars R P Q
    let _ : IsScalarTower R P Q := IsScalarTower.of_compHom R P Q
    let e := IsLocalization.moduleTensorEquiv (R := R)
      (A := P) (S := S) (M₁ := M) (M₂ := Q)
    let eN := IsLocalization.moduleTensorEquiv (R := R)
      (A := P) (S := S) (M₁ := N) (M₂ := Q)
    let gR : M →ₗ[R] N := f.restrictScalars R
    let gP : M →ₗ[P] N :=
      (f.extendScalarsOfIsLocalization S' T).restrictScalars P
    have hq : Function.Injective (LinearMap.rTensor Q gP) := by
      intro x y hxy
      apply e.injective
      apply hf Q
      have hcomm (z : M ⊗[P] Q) :
          eN ((LinearMap.rTensor Q gP) z) =
            (LinearMap.rTensor Q gR) (e z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
            simp only [e, eN, IsLocalization.moduleTensorEquiv,
              TensorProduct.equivOfCompatibleSMul,
              TensorProduct.mapOfCompatibleSMul_tmul,
              LinearMap.rTensor_tmul]
            rfl
      calc
        (LinearMap.rTensor Q gR) (e x) = eN ((LinearMap.rTensor Q gP) x) :=
          (hcomm x).symm
        _ = eN ((LinearMap.rTensor Q gP) y) := congrArg eN hxy
        _ = (LinearMap.rTensor Q gR) (e y) := hcomm y
    exact hq
  · intro hP
    letI : Algebra R (Localization S') :=
      ((algebraMap A (Localization S')).comp (algebraMap R A)).toAlgebra
    letI : Algebra (Localization S) (Localization S') :=
      (localizationRingHom S S' hS).toAlgebra
    dsimp [universallyInjectiveAsAlgebra, universallyInjectiveOver] at hP
    dsimp [universallyInjectiveAsAlgebra, universallyInjectiveOver]
    intro Q _ _
    let P := Localization S
    let T := Localization S'
    let X := M
    let Y := N
    let Qp := LocalizedModule S Q
    let _ : SMul P X := (Module.restrictScalars P T X).toSMul
    let _ : SMul P Y := (Module.restrictScalars P T Y).toSMul
    let _ : SMul R T := Algebra.toSMul
    let _ : Module R T := Algebra.toModule
    let _ : Module P X := Module.restrictScalars P T X
    let _ : Module P Y := Module.restrictScalars P T Y
    let _ : IsScalarTower P T X := IsScalarTower.of_compHom P T X
    let _ : IsScalarTower P T Y := IsScalarTower.of_compHom P T Y
    have hmap :
        (algebraMap P T).comp (algebraMap R P) =
          (algebraMap A T).comp (algebraMap R A) := by
      change (localizationRingHom S S' hS).comp
          (algebraMap R (Localization S)) =
        (algebraMap A (Localization S')).comp (algebraMap R A)
      exact IsLocalization.map_comp (Q := Localization S') hS
    let _ : IsScalarTower R A T :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R P T := by
      apply IsScalarTower.of_algebraMap_eq'
      exact hmap.symm
    let _ : IsScalarTower R P X := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      rw [← IsScalarTower.algebraMap_smul (R := P) (A := T)
        (algebraMap R P r) x]
      rw [← IsScalarTower.algebraMap_smul (R := R) (A := A) r x]
      rw [← IsScalarTower.algebraMap_smul (R := A) (A := T)
        (algebraMap R A r) x]
      exact congrArg (fun z => z • x) (congrArg (fun k => k r) hmap)
    let _ : IsScalarTower R P Y := by
      apply IsScalarTower.of_algebraMap_smul
      intro r y
      rw [← IsScalarTower.algebraMap_smul (R := P) (A := T)
        (algebraMap R P r) y]
      rw [← IsScalarTower.algebraMap_smul (R := R) (A := A) r y]
      rw [← IsScalarTower.algebraMap_smul (R := A) (A := T)
        (algebraMap R A r) y]
      exact congrArg (fun z => z • y) (congrArg (fun k => k r) hmap)
    let eX₀ := IsLocalization.moduleTensorEquiv (R := R)
      (A := P) (S := S) (M₁ := X) (M₂ := Qp)
    let eY₀ := IsLocalization.moduleTensorEquiv (R := R)
      (A := P) (S := S) (M₁ := Y) (M₂ := Qp)
    let lQ : Q →ₗ[R] Qp := LocalizedModule.mkLinearMap S Q
    let eX : X ⊗[R] Q →ₗ[R] X ⊗[P] Qp :=
      (eX₀.symm.restrictScalars R).toLinearMap.comp
        (TensorProduct.map (LinearMap.id : X →ₗ[R] X) lQ)
    let eY : Y ⊗[R] Q →ₗ[R] Y ⊗[P] Qp :=
      (eY₀.symm.restrictScalars R).toLinearMap.comp
        (TensorProduct.map (LinearMap.id : Y →ₗ[R] Y) lQ)
    let _ : Module P (X ⊗[R] Q) := TensorProduct.leftModule
    let _ : Module P (Y ⊗[R] Q) := TensorProduct.leftModule
    let _ : IsScalarTower R P (X ⊗[R] Q) := by
      apply IsScalarTower.of_algebraMap_smul
      intro r z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [smul_add, hz, hw]
      | tmul x y =>
          change (algebraMap R P r • x) ⊗ₜ[R] y = (r • x) ⊗ₜ[R] y
          rw [IsScalarTower.algebraMap_smul (R := R) (A := P) r x]
    let _ : IsScalarTower R P (Y ⊗[R] Q) := by
      apply IsScalarTower.of_algebraMap_smul
      intro r z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [smul_add, hz, hw]
      | tmul x y =>
          change (algebraMap R P r • x) ⊗ₜ[R] y = (r • x) ⊗ₜ[R] y
          rw [IsScalarTower.algebraMap_smul (R := R) (A := P) r x]
    let _ : IsLocalizedModule S (LinearMap.id : X →ₗ[R] X) :=
      isLocalizedModule_id S X P
    let _ : IsLocalizedModule S (LinearMap.id : Y →ₗ[R] Y) :=
      isLocalizedModule_id S Y P
    have hmapX : IsLocalizedModule S
        (TensorProduct.map (LinearMap.id : X →ₗ[R] X) lQ) := inferInstance
    have hmapY : IsLocalizedModule S
        (TensorProduct.map (LinearMap.id : Y →ₗ[R] Y) lQ) := inferInstance
    have hmapXinj : Function.Injective
        (TensorProduct.map (LinearMap.id : X →ₗ[R] X) lQ) := by
      apply (IsLocalizedModule.injective_iff_isRegular
        (S := S) (f := TensorProduct.map (LinearMap.id : X →ₗ[R] X) lQ)).mpr
      intro c
      have hc : IsUnit
          (algebraMap R (Module.End R (X ⊗[R] Q)) (c : R)) := by
        rw [← (Algebra.lsmul R (A := P) R (X ⊗[R] Q)).commutes]
        exact (IsLocalization.map_units P c).map _
      have hreg := hc.isSMulRegular (X ⊗[R] Q)
      intro x y hxy
      apply hreg
      change (c : R) • x = (c : R) • y at hxy
      change (c : R) • x = (c : R) • y
      exact hxy
    have hmapYinj : Function.Injective
        (TensorProduct.map (LinearMap.id : Y →ₗ[R] Y) lQ) := by
      apply (IsLocalizedModule.injective_iff_isRegular
        (S := S) (f := TensorProduct.map (LinearMap.id : Y →ₗ[R] Y) lQ)).mpr
      intro c
      have hc : IsUnit
          (algebraMap R (Module.End R (Y ⊗[R] Q)) (c : R)) := by
        rw [← (Algebra.lsmul R (A := P) R (Y ⊗[R] Q)).commutes]
        exact (IsLocalization.map_units P c).map _
      have hreg := hc.isSMulRegular (Y ⊗[R] Q)
      intro x y hxy
      apply hreg
      change (c : R) • x = (c : R) • y at hxy
      change (c : R) • x = (c : R) • y
      exact hxy
    have hxe : Function.Injective eX := by
      intro x y hxy
      apply hmapXinj
      apply (eX₀.symm.restrictScalars R).injective
      simpa [eX] using hxy
    have hye : Function.Injective eY := by
      intro x y hxy
      apply hmapYinj
      apply (eY₀.symm.restrictScalars R).injective
      simpa [eY] using hxy
    have hP' := hP
    have hP'' := hP' Qp
    let gR : X →ₗ[R] Y := f.restrictScalars R
    let gP : X →ₗ[P] Y :=
      (f.extendScalarsOfIsLocalization S' T).restrictScalars P
    have hqP : Function.Injective (LinearMap.rTensor Qp gP) := by
      simpa [gP, X, Y, P, T] using hP''
    have hcomm (z : X ⊗[R] Q) :
        eY ((LinearMap.rTensor Q gR) z) =
          (LinearMap.rTensor Qp gP) (eX z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
          simp only [eX, eY, gR, lQ, gP,
            LinearMap.comp_apply,
            TensorProduct.map_tmul,
            LinearMap.rTensor_tmul]
          change
            (f x) ⊗ₜ[P] (LocalizedModule.mkLinearMap S Q y) =
              (f x) ⊗ₜ[P] (LocalizedModule.mkLinearMap S Q y)
          rfl
    intro x y hxy
    apply hxe
    apply hqP
    calc
      (LinearMap.rTensor Qp gP) (eX x) =
          eY ((LinearMap.rTensor Q gR) x) := (hcomm x).symm
      _ = eY ((LinearMap.rTensor Q gR) y) := congrArg eY hxy
      _ = (LinearMap.rTensor Qp gP) (eX y) := hcomm y

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
  constructor
  · intro hf I _
    let Q := R ⧸ I
    let eM : M ⊗[R] Q ≃ₗ[R]
        M ⧸ (I • (⊤ : Submodule R M)) :=
      (TensorProduct.comm R M Q).trans
        (TensorProduct.quotTensorEquivQuotSMul M I)
    let eN : N ⊗[R] Q ≃ₗ[R]
        N ⧸ (I • (⊤ : Submodule R N)) :=
      (TensorProduct.comm R N Q).trans
        (TensorProduct.quotTensorEquivQuotSMul N I)
    have hcomm :
        eN.toLinearMap.comp (f.rTensor Q) =
          (quotientMapByIdeal I f).comp eM.toLinearMap := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
          simp only [eM, eN, LinearMap.comp_apply, LinearMap.rTensor_tmul,
            LinearEquiv.trans_apply, TensorProduct.comm_tmul]
          change (TensorProduct.quotTensorEquivQuotSMul N I)
              ((Ideal.Quotient.mk I) r ⊗ₜ[R] f x) =
            (quotientMapByIdeal I f)
              ((TensorProduct.quotTensorEquivQuotSMul M I)
                ((Ideal.Quotient.mk I) r ⊗ₜ[R] x))
          rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
          rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
          simp [quotientMapByIdeal, Submodule.mapQ_apply]
    have hcomm_apply (z : M ⊗[R] Q) :
        eN ((f.rTensor Q) z) =
          (quotientMapByIdeal I f) (eM z) := by
      have h := congrArg (fun g => g z) hcomm
      simpa [LinearMap.comp_apply] using h
    intro x y hxy
    apply eM.symm.injective
    apply hf Q
    apply eN.injective
    calc
      eN ((f.rTensor Q) (eM.symm x)) =
          (quotientMapByIdeal I f) (eM (eM.symm x)) := by
            exact hcomm_apply _
      _ = (quotientMapByIdeal I f) x := by rw [eM.apply_symm_apply]
      _ = (quotientMapByIdeal I f) y := hxy
      _ = eN ((f.rTensor Q) (eM.symm y)) := by
        simpa using (hcomm_apply (eM.symm y)).symm
  · sorry

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
