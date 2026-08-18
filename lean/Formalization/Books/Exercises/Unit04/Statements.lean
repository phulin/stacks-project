import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Ring.Prod
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products

import Formalization.Books.Exercises.Unit04.Core

/-!
# Exercises, Chapter 4: Tensor product

This file contains the declarations for the four numbered parts of
`exercise-characterize-tensor-functor`.  Proposition proofs are intentionally
left for the prove stage; the functors and examples themselves are defined
explicitly.
-/

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace Formalization.Books.Exercises.Unit04

/-! ## (1) An additive functor which is not `R`-linear -/

/-- The product ring used for the non-`R`-linear additive example. -/
abbrev exampleRing : Type := ℤ × ℤ

/-- The ring automorphism which swaps the two components of `exampleRing`. -/
def exampleRingSwap : exampleRing ≃+* exampleRing :=
  RingEquiv.prodComm (R := ℤ) (S := ℤ)

/-- Restriction of scalars along the component swap. -/
def exampleAdditiveFunctor :
    ModuleCat exampleRing ⥤ ModuleCat exampleRing :=
  ModuleCat.restrictScalars exampleRingSwap.toRingHom

/-- The restriction-of-scalars example is additive but not linear over the
original product ring. -/
theorem additive_not_R_linear_example :
    exampleAdditiveFunctor.Additive ∧
      ¬ Functor.Linear exampleRing exampleAdditiveFunctor := by
  refine ⟨{ map_add := by intros; rfl }, ?_⟩
  intro h
  have h' := (Functor.linear_iff exampleRing exampleAdditiveFunctor).mp h
  let X := ModuleCat.of exampleRing (ULift exampleRing)
  have hx := h' X ((1, 0) : exampleRing)
  have hx' := congrArg (fun f => f (ULift.up ((1, 0) : exampleRing))) hx
  change ULift.up ((1, 0) : exampleRing) = ULift.up ((0, 0) : exampleRing) at hx'
  exact (by norm_num : ((1, 0) : exampleRing) ≠ (0, 0)) (ULift.up.inj hx')

/-! ## (2) Tensoring with a fixed module -/

/-- The canonical functor `M ↦ M ⊗_R N`, namely right tensoring in the
monoidal category of `R`-modules. -/
noncomputable def tensorProductFunctor
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  CategoryTheory.MonoidalCategory.tensorRight N

/-- Tensoring with `N` is `R`-linear in the source's bundled sense. -/
theorem tensorProductFunctor_is_R_linear
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    IsRLinearFunctor (tensorProductFunctor N) := by
  unfold IsRLinearFunctor tensorProductFunctor
  exact ⟨CategoryTheory.tensorRight_additive N, CategoryTheory.tensorRight_linear R N⟩

/-- Tensoring with `N` is right exact. -/
theorem tensorProductFunctor_is_right_exact
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    PreservesFiniteColimits (tensorProductFunctor N) := by
  unfold tensorProductFunctor
  refine ⟨fun J _ _ => ⟨fun {K} => ?_⟩⟩
  exact CategoryTheory.MonoidalCategory.Limits.preservesColimit_of_braided_and_preservesColimit_tensor_left K N

/-- Tensoring with `N` commutes with arbitrary direct sums. -/
theorem tensorProductFunctor_commutes_with_direct_sums
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    CommutesWithDirectSums (tensorProductFunctor N) := by
  unfold CommutesWithDirectSums tensorProductFunctor
  intro ι M
  infer_instance

/-! ## (3) The converse characterization -/

/-- A source-faithful formulation of the Eilenberg--Watts characterization.
The phrase “is of the form” is represented by a natural isomorphism of
functors, since categorical functors are determined only up to isomorphism. -/
theorem exists_tensorProductFunctor_iso
    {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    (hF : IsRLinearFunctor F)
    (hRight : PreservesFiniteColimits F)
    (hSums : CommutesWithDirectSums F) :
    ∃ N : ModuleCat.{u} R, Nonempty (F ≅ tensorProductFunctor N) := by
  have hF_add : F.Additive := hF.1
  have hF_linear : Functor.Linear R F := hF.2
  let N : ModuleCat.{u} R := F.obj (ModuleCat.of R R)
  let span (M : ModuleCat.{u} R) (m : M) : ModuleCat.of R R ⟶ M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)
  let alpha (M : ModuleCat.{u} R) :
      (tensorProductFunctor N).obj M ⟶ F.obj M :=
    ModuleCat.MonoidalCategory.tensorLift
      (fun m n => F.map (span M m) n)
      (by
        intro m₁ m₂ n
        have hspan : span M (m₁ + m₂) = span M m₁ + span M m₂ := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          simp [span]
        rw [hspan, @Functor.map_add _ _ _ _ _ _ F hF_add]
        rfl)
      (by
        intro r m n
        have hspan : span M (r • m) = r • span M m := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          simp [span]
          rw [smul_smul, smul_smul, mul_comm]
        rw [hspan, @Functor.map_smul R _ _ _ _ _ _ _ _ _ F hF_linear]
        rfl)
      (by
        intro m n₁ n₂
        simp)
      (by
        intro r m n
        simp)
  have alpha_unit : alpha (ModuleCat.of R R) =
      (MonoidalCategory.leftUnitor N).hom := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    dsimp [alpha]
    change F.map (span (ModuleCat.of R R) m) n = m • n
    have hspan : span (ModuleCat.of R R) m = m • 𝟙 _ := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [span]
      rw [mul_comm]
    rw [hspan, Functor.map_smul]
    simp
  have hunit : IsIso (alpha (ModuleCat.of R R)) := by
    rw [alpha_unit]
    exact (MonoidalCategory.leftUnitor N).isIso_hom
  let alphaNat : tensorProductFunctor N ⟶ F := {
    app := alpha
    naturality := by
      intro M M' f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro m n
      dsimp [alpha, tensorProductFunctor]
      change F.map (span M' (f.hom m)) n = F.map f (F.map (span M m) n)
      have hspan : span M' (f.hom m) = span M m ≫ f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simp [span]
      rw [hspan, F.map_comp]
      rfl
    }
  have hfree : ∀ X : Type u,
      IsIso (alphaNat.app (∐ (fun _ : X => ModuleCat.of R R))) := by
    intro X
    have hF_sigma : IsIso (sigmaComparison F (fun _ : X => ModuleCat.of R R)) := hSums X _
    have hF_pres : PreservesColimit
        (Discrete.functor (fun _ : X => ModuleCat.of R R)) F :=
      PreservesCoproduct.of_iso_comparison F (fun _ : X => ModuleCat.of R R)
        (i := hF_sigma)
    have hG_sigma : IsIso (sigmaComparison (tensorProductFunctor N)
        (fun _ : X => ModuleCat.of R R)) :=
      tensorProductFunctor_commutes_with_direct_sums N X _
    have hG_pres : PreservesColimit
        (Discrete.functor (fun _ : X => ModuleCat.of R R))
        (tensorProductFunctor N) :=
      PreservesCoproduct.of_iso_comparison (tensorProductFunctor N)
        (fun _ : X => ModuleCat.of R R) (i := hG_sigma)
    let eG : (tensorProductFunctor N).obj
        (∐ (fun _ : X => ModuleCat.of R R)) ≅
        (∐ (fun _ : X => (tensorProductFunctor N).obj (ModuleCat.of R R))) :=
      @PreservesCoproduct.iso _ _ _ _ (tensorProductFunctor N) _
        (fun _ : X => ModuleCat.of R R) _ _ hG_pres
    let eF : F.obj (∐ (fun _ : X => ModuleCat.of R R)) ≅
        (∐ (fun _ : X => F.obj (ModuleCat.of R R))) :=
      @PreservesCoproduct.iso _ _ _ _ F _ (fun _ : X => ModuleCat.of R R)
        _ _ hF_pres
    let eU := asIso (alphaNat.app (ModuleCat.of R R))
    let t :
        (∐ (fun _ : X => (tensorProductFunctor N).obj (ModuleCat.of R R))) ≅
          (∐ (fun _ : X => F.obj (ModuleCat.of R R))) :=
      Sigma.mapIso (fun _ : X ↦ eU)
    have hcomp :
        t.hom = eG.inv ≫
          alphaNat.app (∐ (fun _ : X => ModuleCat.of R R)) ≫ eF.hom := by
      apply Sigma.hom_ext
        (f := fun _ : X => (tensorProductFunctor N).obj (ModuleCat.of R R))
      intro x
      dsimp [eG, eF, t]
      rw [Sigma.ι_mapIso_hom]
      rw [ι_comp_sigmaComparison_assoc]
      rw [← Category.assoc]
      rw [alphaNat.naturality]
      change alphaNat.app (ModuleCat.of R R) ≫
          Sigma.ι (fun _ : X => F.obj (ModuleCat.of R R)) x = _
      change alphaNat.app (ModuleCat.of R R) ≫
          Sigma.ι (fun _ : X => F.obj (ModuleCat.of R R)) x =
        alphaNat.app (ModuleCat.of R R) ≫
          (F.map (Sigma.ι (fun _ : X => ModuleCat.of R R) x) ≫
            (PreservesCoproduct.iso F (fun _ : X => ModuleCat.of R R)).hom)
      exact (cancel_epi (alphaNat.app (ModuleCat.of R R))).2 (by
        have heF : (PreservesCoproduct.iso F
            (fun _ : X => ModuleCat.of R R)).hom =
            inv (sigmaComparison F (fun _ : X => ModuleCat.of R R)) := by
          calc
            (PreservesCoproduct.iso F
              (fun _ : X => ModuleCat.of R R)).hom =
                inv (PreservesCoproduct.iso F
                  (fun _ : X => ModuleCat.of R R)).inv :=
              (IsIso.Iso.inv_inv _).symm
            _ = inv (sigmaComparison F (fun _ : X => ModuleCat.of R R)) := by
              simp only [PreservesCoproduct.inv_hom]
        calc
          Sigma.ι (fun _ : X => F.obj (ModuleCat.of R R)) x =
              F.map (Sigma.ι (fun _ : X => ModuleCat.of R R) x) ≫
                inv (sigmaComparison F (fun _ : X => ModuleCat.of R R)) :=
            (map_ι_comp_inv_sigmaComparison F
              (fun _ : X => ModuleCat.of R R) x).symm
          _ = F.map (Sigma.ι (fun _ : X => ModuleCat.of R R) x) ≫
              (PreservesCoproduct.iso F
                (fun _ : X => ModuleCat.of R R)).hom := by rw [heF])
    have hα : alphaNat.app (∐ (fun _ : X => ModuleCat.of R R)) =
        eG.hom ≫ t.hom ≫ eF.inv := by
      rw [hcomp]
      simp
    rw [hα]
    infer_instance
  have halpha : ∀ Q : ModuleCat.{u} R, IsIso (alphaNat.app Q) := by
    intro Q
    let P : ModuleCat.{u} R := (ModuleCat.free R).obj (Q : Type u)
    let q : P ⟶ Q := ModuleCat.freeDesc (↾fun m => m)
    have hq : ∀ m : Q, ∃ p : P, q p = m := by
      intro m
      refine ⟨ModuleCat.freeMk m, ?_⟩
      exact ModuleCat.freeDesc_apply (↾fun x : Q => x) m
    let K : ModuleCat.{u} R := kernel q
    let r : (ModuleCat.free R).obj (K : Type u) ⟶ P :=
      ModuleCat.freeDesc (↾fun k : K => kernel.ι q k)
    let S : ShortComplex (ModuleCat.{u} R) :=
      ShortComplex.mk r q (by
        apply ModuleCat.free_hom_ext
        intro k
        simp [r]
        )
    have hSexact : S.Exact := by
      apply (ShortComplex.moduleCat_exact_iff S).2
      intro x hx
      let sx : ModuleCat.of R R ⟶ P :=
        ModuleCat.ofHom (LinearMap.toSpanSingleton R P x)
      have hsx : sx ≫ q = 0 := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        change q (y • x) = 0
        rw [map_smul, hx, smul_zero]
      let k : K := (kernel.lift q sx hsx) (1 : R)
      refine ⟨ModuleCat.freeMk k, ?_⟩
      have hk : kernel.ι q k = x := by
        change (kernel.ι q) ((kernel.lift q sx hsx) (1 : R)) = x
        have hsx_one : sx (1 : R) = x := by
          change (1 : R) • x = x
          simp
        have hk' := congrArg (fun f : ModuleCat.of R R ⟶ P => f (1 : R))
          (kernel.lift_ι q sx hsx)
        rw [hsx_one] at hk'
        exact hk'
      simp [S, r, k, hk]
    have hqEpi : Epi q := (ModuleCat.epi_iff_surjective q).2 (by
      intro m
      exact hq m)
    have hqCokernel :
        IsColimit (CokernelCofork.ofπ q S.zero) := by
      exact ((S.exact_and_epi_g_iff_g_is_cokernel).1
        ⟨hSexact, hqEpi⟩).some
    have hF_presShape : PreservesColimitsOfShape WalkingParallelPair F :=
      @PreservesFiniteColimits.preservesFiniteColimits _ _ _ _ F hRight
        WalkingParallelPair _ _
    have hF_pres : PreservesColimit (parallelPair r 0) F :=
      @PreservesColimitsOfShape.preservesColimit _ _ _ _ _ _ _ hF_presShape _
    have hG_right : PreservesFiniteColimits (tensorProductFunctor N) :=
      tensorProductFunctor_is_right_exact N
    have hG_presShape :
        PreservesColimitsOfShape WalkingParallelPair (tensorProductFunctor N) :=
      @PreservesFiniteColimits.preservesFiniteColimits _ _ _ _
        (tensorProductFunctor N) hG_right WalkingParallelPair _ _
    have hG_pres : PreservesColimit (parallelPair r 0) (tensorProductFunctor N) :=
      @PreservesColimitsOfShape.preservesColimit _ _ _ _ _ _ _ hG_presShape _
    have hFmap :=
      @isColimitOfPreserves _ _ _ _ _ _ _ F _ hqCokernel hF_pres
    have hFdesc : ∀ {Z' : ModuleCat.{u} R} (k : F.obj P ⟶ Z'),
        F.map r ≫ k = 0 →
          {l : F.obj Q ⟶ Z' // F.map q ≫ l = k} := by
      intro Z' k hk
      let s : Cocone (parallelPair r 0 ⋙ F) :=
        { pt := Z'
          ι :=
            { app := fun j =>
                WalkingParallelPair.casesOn j (F.map r ≫ k) k
              naturality := by
                intro i j f
                cases i <;> cases j <;> cases f <;> simp [hk] } }
      refine ⟨hFmap.desc s, ?_⟩
      simpa [s] using hFmap.fac s WalkingParallelPair.one
    have hFq : IsColimit (CokernelCofork.ofπ (F.map q) (by
        rw [← F.map_comp, S.zero, F.map_zero])) := by
      refine CokernelCofork.IsColimit.ofπ (F.map q) (by
        rw [← F.map_comp, S.zero, F.map_zero]) ?_ ?_ ?_
      · intro Z' k hk
        exact (hFdesc k hk).1
      · intro Z' k hk
        exact (hFdesc k hk).2
      · intro Z' k hk m hm
        have hm' : F.map q ≫ m = F.map q ≫ hFdesc k hk :=
          hm.trans (hFdesc k hk).property.symm
        apply IsColimit.hom_ext hFmap
        intro j
        cases j with
        | zero =>
            simpa [Category.assoc] using congrArg (fun z => F.map r ≫ z) hm'
        | one => simpa using hm'
    have hGmap :=
      @isColimitOfPreserves _ _ _ _ _ _ _ (tensorProductFunctor N) _
        hqCokernel hG_pres
    have hGdesc : ∀ {Z' : ModuleCat.{u} R}
        (k : (tensorProductFunctor N).obj P ⟶ Z'),
        (tensorProductFunctor N).map r ≫ k = 0 →
          {l : (tensorProductFunctor N).obj Q ⟶ Z' //
            (tensorProductFunctor N).map q ≫ l = k} := by
      intro Z' k hk
      let s : Cocone (parallelPair r 0 ⋙ tensorProductFunctor N) :=
        { pt := Z'
          ι :=
            { app := fun j =>
                WalkingParallelPair.casesOn j
                  ((tensorProductFunctor N).map r ≫ k) k
              naturality := by
                intro i j f
                cases i <;> cases j <;> cases f <;> simp [hk] } }
      refine ⟨hGmap.desc s, ?_⟩
      simpa [s] using hGmap.fac s WalkingParallelPair.one
    have hGq : IsColimit
        (CokernelCofork.ofπ ((tensorProductFunctor N).map q) (by
          rw [← (tensorProductFunctor N).map_comp, S.zero,
            (tensorProductFunctor N).map_zero])) := by
      refine CokernelCofork.IsColimit.ofπ
        ((tensorProductFunctor N).map q) (by
          rw [← (tensorProductFunctor N).map_comp, S.zero,
            (tensorProductFunctor N).map_zero]) ?_ ?_ ?_
      · intro Z' k hk
        exact (hGdesc k hk).1
      · intro Z' k hk
        exact (hGdesc k hk).2
      · intro Z' k hk m hm
        have hm' : (tensorProductFunctor N).map q ≫ m =
            (tensorProductFunctor N).map q ≫ hGdesc k hk :=
          hm.trans (hGdesc k hk).property.symm
        apply IsColimit.hom_ext hGmap
        intro j
        cases j with
        | zero =>
            simpa [Category.assoc] using
              congrArg (fun z => (tensorProductFunctor N).map r ≫ z) hm'
        | one => simpa using hm'
    have hP : IsIso (alphaNat.app P) := by
      let eQ : P ≅ ∐ (fun _ : (Q : Type u) => ModuleCat.of R R) :=
        IsColimit.coconePointUniqueUpToIso
          (ModuleCat.finsuppCoconeIsColimit R R (Q : Type u))
          (colimit.isColimit (Discrete.functor
            (fun _ : (Q : Type u) => ModuleCat.of R R)))
      have hQiso : IsIso
          ((tensorProductFunctor N).map eQ.hom ≫
            alphaNat.app (∐ (fun _ : (Q : Type u) => ModuleCat.of R R)) ≫
            F.map eQ.inv) :=
        have hQtail : IsIso
            (alphaNat.app (∐ (fun _ : (Q : Type u) => ModuleCat.of R R)) ≫
              F.map eQ.inv) :=
          IsIso.comp_isIso' (hfree (Q : Type u))
            (inferInstance : IsIso (F.map eQ.inv))
        IsIso.comp_isIso'
          (inferInstance : IsIso ((tensorProductFunctor N).map eQ.hom)) hQtail
      have heq : alphaNat.app P =
          (tensorProductFunctor N).map eQ.hom ≫
            alphaNat.app (∐ (fun _ : (Q : Type u) => ModuleCat.of R R)) ≫
              F.map eQ.inv := by
        apply (cancel_mono (F.map eQ.hom)).1
        simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
          F.map_id, Category.comp_id]
        exact (alphaNat.naturality eQ.hom).symm
      rw [heq]
      exact hQiso
    have hK : IsIso
        (alphaNat.app ((ModuleCat.free R).obj (K : Type u))) := by
      let eK : (ModuleCat.free R).obj (K : Type u) ≅
          ∐ (fun _ : (K : Type u) => ModuleCat.of R R) :=
        IsColimit.coconePointUniqueUpToIso
          (ModuleCat.finsuppCoconeIsColimit R R (K : Type u))
          (colimit.isColimit (Discrete.functor
            (fun _ : (K : Type u) => ModuleCat.of R R)))
      have hKiso : IsIso
          ((tensorProductFunctor N).map eK.hom ≫
            alphaNat.app (∐ (fun _ : (K : Type u) => ModuleCat.of R R)) ≫
            F.map eK.inv) :=
        have hKtail : IsIso
            (alphaNat.app (∐ (fun _ : (K : Type u) => ModuleCat.of R R)) ≫
              F.map eK.inv) :=
          IsIso.comp_isIso' (hfree (K : Type u))
            (inferInstance : IsIso (F.map eK.inv))
        IsIso.comp_isIso'
          (inferInstance : IsIso ((tensorProductFunctor N).map eK.hom)) hKtail
      have heq :
          alphaNat.app ((ModuleCat.free R).obj (K : Type u)) =
            (tensorProductFunctor N).map eK.hom ≫
              alphaNat.app (∐ (fun _ : (K : Type u) => ModuleCat.of R R)) ≫
                F.map eK.inv := by
        apply (cancel_mono (F.map eK.hom)).1
        simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
          F.map_id, Category.comp_id]
        exact (alphaNat.naturality eK.hom).symm
      rw [heq]
      exact hKiso
    let alphaP : (tensorProductFunctor N).obj P ≅ F.obj P :=
      @asIso _ _ _ _ (alphaNat.app P) hP
    let alphaK :
      (tensorProductFunctor N).obj ((ModuleCat.free R).obj (K : Type u)) ≅
        F.obj ((ModuleCat.free R).obj (K : Type u)) :=
      @asIso _ _ _ _
        (alphaNat.app ((ModuleCat.free R).obj (K : Type u))) hK
    have hfac : F.map r ≫ alphaP.inv =
        alphaK.inv ≫ (tensorProductFunctor N).map r := by
      apply (cancel_mono alphaP.hom).1
      dsimp [alphaP, alphaK]
      simp only [Category.assoc]
      rw [← Category.assoc]
      rw [alphaNat.naturality]
      simp
    let fF : F.obj P ⟶ (tensorProductFunctor N).obj Q :=
      alphaP.inv ≫ (tensorProductFunctor N).map q
    have hfF : F.map r ≫ fF = 0 := by
      dsimp [fF]
      rw [← Category.assoc, hfac, Category.assoc,
        ← (tensorProductFunctor N).map_comp, S.zero,
        (tensorProductFunctor N).map_zero, comp_zero]
    let betaData := CokernelCofork.IsColimit.desc' hFq fF hfF
    let beta : F.obj Q ⟶ (tensorProductFunctor N).obj Q := betaData.1
    have hbeta : F.map q ≫ beta = fF := betaData.2
    let fG : (tensorProductFunctor N).obj P ⟶ F.obj Q :=
      alphaP.hom ≫ F.map q
    have hfG : (tensorProductFunctor N).map r ≫ fG = 0 := by
      dsimp [fG, alphaP]
      rw [← Category.assoc, alphaNat.naturality, Category.assoc,
        ← F.map_comp, S.zero, F.map_zero, comp_zero]
    let gammaData := CokernelCofork.IsColimit.desc' hGq fG hfG
    let gamma : (tensorProductFunctor N).obj Q ⟶ F.obj Q := gammaData.1
    have hgamma : (tensorProductFunctor N).map q ≫ gamma = fG := gammaData.2
    have hnq : (tensorProductFunctor N).map q ≫ alphaNat.app Q = fG := by
      simp [fG, alphaP]
    have halpha_gamma : alphaNat.app Q = gamma := by
      apply Cofork.IsColimit.hom_ext hGq
      change (tensorProductFunctor N).map q ≫ alphaNat.app Q =
        (tensorProductFunctor N).map q ≫ gamma
      rw [hnq, hgamma]
    have hbeta_gamma : beta ≫ gamma = 𝟙 _ := by
      apply Cofork.IsColimit.hom_ext hFq
      change F.map q ≫ (beta ≫ gamma) = F.map q ≫ 𝟙 _
      rw [← Category.assoc, hbeta]
      dsimp [fF]
      rw [Category.assoc, hgamma]
      simp [alphaP, fG]
    have hgamma_beta : gamma ≫ beta = 𝟙 _ := by
      apply Cofork.IsColimit.hom_ext hGq
      change (tensorProductFunctor N).map q ≫ (gamma ≫ beta) =
        (tensorProductFunctor N).map q ≫ 𝟙 _
      rw [← Category.assoc, hgamma]
      dsimp [fG]
      rw [Category.assoc, hbeta]
      simp [alphaP, fF]
    rw [halpha_gamma]
    exact ⟨⟨beta, hgamma_beta, hbeta_gamma⟩⟩
  refine ⟨N, Nonempty.intro ?_⟩
  exact (NatIso.ofComponents
    (fun Q => @asIso _ _ _ _ (alphaNat.app Q) (halpha Q)) (by
    intro X Y f
    change (tensorProductFunctor N).map f ≫ alphaNat.app Y =
      alphaNat.app X ≫ F.map f
    exact alphaNat.naturality f)).symm

/-! ## (4) Why direct sums cannot be omitted -/

/-- The countable product endofunctor on abelian groups, written directly on
objects and morphisms. -/
def infiniteProductFunctor :
    ModuleCat ℤ ⥤ ModuleCat ℤ where
  obj M := ModuleCat.of ℤ (ℕ → M)
  map {M N} f :=
    ModuleCat.ofHom (X := ModuleCat.of ℤ (ℕ → M))
      (Y := ModuleCat.of ℤ (ℕ → N))
      { toFun := fun x n => f.hom (x n)
        map_add' := by
          intro x y
          funext n
          exact f.hom.map_add (x n) (y n)
        map_smul' := by
          intro r x
          funext n
          simp }
  map_id := by
    intro M
    apply ModuleCat.hom_ext
    ext x n
    rfl
  map_comp := by
    intro M N P f g
    apply ModuleCat.hom_ext
    ext x n
    rfl

/-- The product functor supplies the requested counterexample after the
direct-sum hypothesis is removed. -/
theorem exists_right_exact_R_linear_not_tensorProductFunctor :
    ∃ F : ModuleCat ℤ ⥤ ModuleCat ℤ,
      IsRLinearFunctor F ∧
        PreservesFiniteColimits F ∧
          ¬ CommutesWithDirectSums F ∧
            ¬ ∃ N : ModuleCat ℤ, Nonempty (F ≅ tensorProductFunctor N) := by
  refine ⟨infiniteProductFunctor, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · refine { map_add := ?_ }
      intro X Y f g
      apply ModuleCat.hom_ext
      ext x n
      rfl
    · letI lin : CategoryTheory.Linear ℤ (ModuleCat ℤ) := ModuleCat.instLinear
      refine { map_smul := ?_ }
      intro X Y f r
      letI : Module ℤ (X ⟶ Y) := lin.homModule X Y
      letI : SMul ℤ (X ⟶ Y) :=
        (lin.homModule X Y).toDistribMulAction.toDistribSMul.toSMul
      let zf : X ⟶ Y :=
        @SMul.smul ℤ (X ⟶ Y) ModuleCat.instSMulIntHom r f
      have hscalar :
          (@SMul.smul ℤ (X ⟶ Y) this r f) = zf := by
        exact int_smul_eq_zsmul (lin.homModule X Y) r f
      have hmap (g : X ⟶ Y) (x : infiniteProductFunctor.obj X) (n : ℕ) :
          (infiniteProductFunctor.map g).hom x n = g.hom (x n) := by
        rfl
      apply ModuleCat.hom_ext
      ext x
      funext n
      have hleft := hmap zf x n
      have hright := congrArg (fun q => r • q) (hmap f x n)
      have h₁ := congrArg (fun q => q (x n)) (ModuleCat.hom_zsmul r f)
      have h₂ := congrArg (fun q => q x n)
        (ModuleCat.hom_zsmul r (infiniteProductFunctor.map f))
      have htransport := congrArg
        (fun g : X ⟶ Y => (infiniteProductFunctor.map g).hom x n) hscalar
      exact htransport.trans (hleft.trans (h₁.trans (hright.trans h₂.symm)))
  · let G : ModuleCat ℤ ⥤ ModuleCat ℤ :=
      Functor.const (Discrete ℕ) ⋙ lim
    let H : ModuleCat ℤ ⥤ ModuleCat ℤ :=
      { obj := fun M => ∏ᶜ fun _ : ℕ => M
        map := fun {M N} f => CategoryTheory.Limits.Pi.map (fun _ => f)
        map_id := by
          intro M
          apply ModuleCat.hom_ext
          ext x n
          simp
        map_comp := by
          intro M N P f g
          apply CategoryTheory.Limits.Pi.hom_ext
          intro n
          simp [CategoryTheory.Limits.Pi.map_comp_map] }
    let e : G ≅ H :=
      NatIso.ofComponents (fun M =>
        (piEquivalenceFunctorDiscreteCompLim (C := ModuleCat ℤ) ℕ).app (fun _ => M))
    have hGH : PreservesFiniteColimits G := by infer_instance
    have hH : PreservesFiniteColimits H := by
      exact preservesFiniteColimits_of_natIso e
    have hobj : ∀ M : ModuleCat ℤ,
        @ModuleCat.of ℤ Int.instRing (ℕ → (M : Type)) Pi.addCommGroup
            (Pi.module ℕ (fun _ => (M : Type)) ℤ) = infiniteProductFunctor.obj M := by
      intro M
      congr 1
      apply Subsingleton.elim
    have eqToHom_apply {A B : ModuleCat ℤ} (h : A = B) (x : A) :
        (eqToHom h).hom x = cast (congrArg ModuleCat.carrier h) x := by
      cases h
      rfl
    let q : H ≅ infiniteProductFunctor :=
      NatIso.ofComponents (fun M =>
        (ModuleCat.piIsoPi (fun _ : ℕ => M)).trans (eqToIso (hobj M)))
        (by
          intro X Y f
          letI : Module ℤ (ℕ → (X : Type)) :=
            Pi.module ℕ (fun _ => (X : Type)) ℤ
          letI : Module ℤ (ℕ → (Y : Type)) :=
            Pi.module ℕ (fun _ => (Y : Type)) ℤ
          let k :
              @ModuleCat.of ℤ Int.instRing (ℕ → (X : Type)) Pi.addCommGroup
                  (Pi.module ℕ (fun _ => (X : Type)) ℤ) ⟶
                @ModuleCat.of ℤ Int.instRing (ℕ → (Y : Type)) Pi.addCommGroup
                  (Pi.module ℕ (fun _ => (Y : Type)) ℤ) :=
            ModuleCat.ofHom (LinearMap.piMap (fun _ => f.hom))
          have hp :
              H.map f ≫ (ModuleCat.piIsoPi (fun _ : ℕ => Y)).hom =
                (ModuleCat.piIsoPi (fun _ : ℕ => X)).hom ≫ k := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            funext n
            have hy := congrArg
              (fun a : (H.obj Y ⟶ Y) => a.hom ((H.map f).hom x))
              (ModuleCat.piIsoPi_hom_ker_subtype (fun _ : ℕ => Y) n)
            have hm := congrArg
              (fun a : (H.obj X ⟶ Y) => a.hom x)
              (CategoryTheory.Limits.Pi.map_π (fun _ : ℕ => f) n)
            have hx := congrArg
              (fun a : (H.obj X ⟶ X) => a.hom x)
              (ModuleCat.piIsoPi_hom_ker_subtype (fun _ : ℕ => X) n)
            have hxf := congrArg (fun z : X => f.hom z) hx.symm
            have hy' :
                ((ModuleCat.piIsoPi (fun _ : ℕ => Y)).hom.hom
                    ((H.map f).hom x)) n =
                  (Pi.π (fun _ : ℕ => Y) n).hom ((H.map f).hom x) := by
              change ((ModuleCat.piIsoPi (fun _ : ℕ => Y)).hom ≫
                  ModuleCat.ofHom (LinearMap.proj n)).hom ((H.map f).hom x) = _
              exact hy
            have hx' :
                (Pi.π (fun _ : ℕ => X) n).hom x =
                  ((ModuleCat.piIsoPi (fun _ : ℕ => X)).hom.hom x) n := by
              change _ = ((ModuleCat.piIsoPi (fun _ : ℕ => X)).hom ≫
                  ModuleCat.ofHom (LinearMap.proj n)).hom x
              exact hx.symm
            calc
              ((ModuleCat.piIsoPi (fun _ : ℕ => Y)).hom.hom
                    ((H.map f).hom x)) n =
                  (Pi.π (fun _ : ℕ => Y) n).hom ((H.map f).hom x) := hy'
              _ = (f.hom ((Pi.π (fun _ : ℕ => X) n).hom x)) := by
                change ((H.map f ≫
                    Pi.π (fun _ : ℕ => Y) n).hom x) =
                  ((Pi.π (fun _ : ℕ => X) n ≫ f).hom x)
                simpa only [H] using hm
              _ = f.hom (((ModuleCat.piIsoPi (fun _ : ℕ => X)).hom.hom x) n) := by
                rw [hx']
              _ = (k.hom ((ModuleCat.piIsoPi (fun _ : ℕ => X)).hom.hom x)) n := by
                rfl
          have hk : k = eqToHom (hobj X) ≫ infiniteProductFunctor.map f ≫
              eqToHom (hobj Y).symm := by
            have hcX : congrArg ModuleCat.carrier (hobj X) = rfl :=
              Subsingleton.elim _ _
            have hcY : congrArg ModuleCat.carrier (hobj Y).symm = rfl :=
              Subsingleton.elim _ _
            apply ModuleCat.hom_ext
            ext x n
            simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
            rw [eqToHom_apply, eqToHom_apply, hcX, hcY]
            rfl
          calc
            H.map f ≫ ((ModuleCat.piIsoPi (fun _ : ℕ => Y)).trans
                (eqToIso (hobj Y))).hom =
                H.map f ≫ (ModuleCat.piIsoPi (fun _ : ℕ => Y)).hom ≫
                  eqToHom (hobj Y) := by simp [Iso.trans_hom, Category.assoc]
            _ = (ModuleCat.piIsoPi (fun _ : ℕ => X)).hom ≫ k ≫
                eqToHom (hobj Y) := by
              rw [← Category.assoc, hp]
              simp only [Category.assoc]
            _ = ((ModuleCat.piIsoPi (fun _ : ℕ => X)).trans
                (eqToIso (hobj X))).hom ≫ infiniteProductFunctor.map f := by
              rw [Iso.trans_hom, hk]
              simp only [Category.assoc, eqToIso.hom, eqToHom_trans,
                eqToHom_refl, Category.comp_id]
          )
    letI := hH
    exact preservesFiniteColimits_of_natIso q
  · have hnotSums : ¬ CommutesWithDirectSums infiniteProductFunctor := by
      classical
      intro hSums
      unfold CommutesWithDirectSums at hSums
      let Z : ℕ → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
      let W : ℕ → ModuleCat ℤ := fun _ => infiniteProductFunctor.obj (ModuleCat.of ℤ ℤ)
      letI : IsIso (sigmaComparison infiniteProductFunctor Z) := hSums ℕ Z
      let e := ModuleCat.coprodIsoDirectSum Z
      let x : infiniteProductFunctor.obj (∐ Z) := fun n => (Sigma.ι Z n).hom 1
      have hx : ∃ y : (∐ W : ModuleCat ℤ),
          (sigmaComparison infiniteProductFunctor Z).hom y = x := by
        let eσ := asIso (sigmaComparison infiniteProductFunctor Z)
        refine ⟨eσ.inv.hom x, ?_⟩
        change (eσ.inv ≫ eσ.hom).hom x = x
        rw [congrArg ModuleCat.Hom.hom eσ.inv_hom_id]
        rfl
      obtain ⟨y, hy⟩ := hx
      let eW := ModuleCat.coprodIsoDirectSum W
      let y' := eW.hom.hom y
      have hsupport : ∃ i : ℕ, i ∉ y'.support := by
        by_cases hs : y'.support.Nonempty
        · let i := y'.support.max' hs + 1
          refine ⟨i, ?_⟩
          intro hi
          have hle := y'.support.le_max' i hi
          omega
        · have hempty : y'.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
          exact ⟨0, by rw [hempty]; simp⟩
      obtain ⟨i, hi⟩ := hsupport
      have hyi : y' i = 0 := by
        exact DFinsupp.notMem_support_iff.mp hi
      let p : (∐ Z) ⟶ ModuleCat.of ℤ ℤ :=
        e.hom ≫ ModuleCat.ofHom (DirectSum.component ℤ ℕ (fun j => (Z j : Type)) i)
      let q : ∀ j : ℕ, W j ⟶ infiniteProductFunctor.obj (ModuleCat.of ℤ ℤ) :=
        fun j => by
          dsimp [W]
          exact infiniteProductFunctor.map (Sigma.ι Z j ≫ p)
      have hqzero (j : ℕ) (hji : j ≠ i) : q j = 0 := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        funext n
        change p.hom ((Sigma.ι Z j).hom (z n)) = 0
        have hι := ModuleCat.ι_coprodIsoDirectSum_hom Z j
        have hι' := congrArg (fun f => f.hom (z n)) hι
        change e.hom.hom ((Sigma.ι Z j).hom (z n)) =
          (DirectSum.lof ℤ ℕ (fun j => (Z j : Type)) j) (z n) at hι'
        change (DirectSum.component ℤ ℕ (fun j => (Z j : Type)) i)
          (e.hom.hom ((Sigma.ι Z j).hom (z n))) = 0
        rw [hι']
        simp [DirectSum.component.of, hji]
      have hL (j : ℕ) (b : (W j : Type)) :
          (eW.inv ≫ Sigma.desc q).hom
              (DirectSum.lof ℤ ℕ (fun i => (W i : Type)) j b) = q j b := by
        have hW := ModuleCat.lof_coprodIsoDirectSum_inv W j
        have hW' := congrArg (fun f => f.hom b) hW
        change eW.inv.hom ((DirectSum.lof ℤ ℕ (fun i => (W i : Type)) j) b) =
          (Sigma.ι W j).hom b at hW'
        change (Sigma.desc q).hom (eW.inv.hom
            ((DirectSum.lof ℤ ℕ (fun i => (W i : Type)) j) b)) = q j b
        rw [hW']
        simp [q]
      have hyrep : eW.inv.hom y' = y := by
        have heW := congrArg (fun f : (∐ W : ModuleCat ℤ) ⟶ (∐ W : ModuleCat ℤ) =>
          f.hom y) eW.hom_inv_id
        change eW.inv.hom (eW.hom.hom y) = y at heW
        simpa [y'] using heW
      have hq : (Sigma.desc q).hom y = 0 := by
        rw [← hyrep]
        have hzero : y' i = 0 → (eW.inv ≫ Sigma.desc q).hom y' = 0 := by
          induction y' using DirectSum.induction_on' with
          | h0 => intro; simp
          | hadd j b f hf hb ih =>
            intro hv
            have hji : j ≠ i := by
              intro hji
              subst j
              have hb0 : b = 0 := by
                simpa [DirectSum.of_apply, hf] using hv
              exact hb hb0
            have hfi : f i = 0 := by
              simpa [DirectSum.of_apply, hji] using hv
            rw [map_add]
            change (eW.inv ≫ Sigma.desc q).hom
                (DirectSum.lof ℤ ℕ (fun i => (W i : Type)) j b) +
              (eW.inv ≫ Sigma.desc q).hom f = 0
            rw [hL j b, hqzero j hji, ih hfi]
            simp
        exact hzero hyi
      have hp : p = Sigma.desc (fun j => Sigma.ι Z j ≫ p) := by
        apply (coproductIsCoproduct Z).hom_ext
        intro j
        simp
      have hcomp :
          sigmaComparison infiniteProductFunctor Z ≫
              infiniteProductFunctor.map p = Sigma.desc q := by
        rw [hp]
        change sigmaComparison infiniteProductFunctor Z ≫
            infiniteProductFunctor.map (Sigma.desc (fun j => Sigma.ι Z j ≫ p)) =
          Sigma.desc (fun j => infiniteProductFunctor.map (Sigma.ι Z j ≫ p))
        exact sigmaComparison_map_desc infiniteProductFunctor Z (ModuleCat.of ℤ ℤ)
          (fun j => Sigma.ι Z j ≫ p)
      have hcomp' := congrArg (fun f => f.hom y) hcomp
      change (infiniteProductFunctor.map p).hom
          ((sigmaComparison infiniteProductFunctor Z).hom y) =
        (Sigma.desc q).hom y at hcomp'
      rw [hq, hy] at hcomp'
      have hxi := congrFun hcomp' i
      have hcalc : (infiniteProductFunctor.map p).hom x i = 1 := by
        change p.hom (x i) = 1
        change p.hom ((Sigma.ι Z i).hom 1) = 1
        have hι := ModuleCat.ι_coprodIsoDirectSum_hom Z i
        have hι' := congrArg (fun f => f.hom 1) hι
        change e.hom.hom ((Sigma.ι Z i).hom 1) =
          (DirectSum.lof ℤ ℕ (fun j => (Z j : Type)) i) 1 at hι'
        rw [show p.hom ((Sigma.ι Z i).hom 1) =
          (DirectSum.component ℤ ℕ (fun j => (Z j : Type)) i)
            (e.hom.hom ((Sigma.ι Z i).hom 1)) by rfl]
        rw [hι']
        simp [DirectSum.component.of]
      exact one_ne_zero (hcalc.symm.trans hxi)
    refine ⟨hnotSums, ?_⟩
    intro hIso
    obtain ⟨N, ⟨eIso⟩⟩ := hIso
    have hSumsN : CommutesWithDirectSums (tensorProductFunctor N) :=
      tensorProductFunctor_commutes_with_direct_sums N
    have hSumsF : CommutesWithDirectSums infiniteProductFunctor := by
      intro ι M
      letI : IsIso (sigmaComparison (tensorProductFunctor N) M) := hSumsN ι M
      letI : PreservesColimit (Discrete.functor M) (tensorProductFunctor N) :=
        PreservesCoproduct.of_iso_comparison (tensorProductFunctor N) M
      letI : PreservesColimit (Discrete.functor M) infiniteProductFunctor :=
        preservesColimit_of_natIso _ eIso.symm
      infer_instance
    exact hnotSums hSumsF

end Formalization.Books.Exercises.Unit04
