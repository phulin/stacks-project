import Formalization.Books.Functors.Unit02.Core
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Presentable.Limits
import Mathlib.CategoryTheory.Presentable.Type
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Functors on module categories: statements

The propositions below formalize the precise assertions in the section of the
book on functors on module categories.  Proofs are intentionally deferred to
the proving stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit90
open Formalization.Books.Categories.Unit23
open Formalization.Books.Categories.Unit26
open Formalization.Books.Homology.Unit03

universe u v u' v' w

namespace Formalization.Books.Functors.Unit02

/-! ## Extension from finitely presented modules -/

theorem functor_on_finitely_presented_modules
    (A : Type u) [Ring A]
    (B : Type u') [Category.{v'} B]
    [HasFilteredColimitsOfSize.{u, u} B]
    (F : FinitelyPresentedModuleCat.{u, u} A ⥤ B) :
    ∃ E : FilteredColimitExtension
        (finitelyPresentedModuleProperty.{u, u} A) F,
      ∀ E' : FilteredColimitExtension
          (finitelyPresentedModuleProperty.{u, u} A) F,
        ∃! e : E.functor ≅ E'.functor,
          Functor.isoWhiskerLeft
              (finitelyPresentedModuleProperty.{u, u} A).ι e ≪≫
              E'.restrictionIso = E.restrictionIso := by
  let : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  let P := finitelyPresentedModuleProperty.{u, u} A
  have hsmall : ObjectProperty.EssentiallySmall.{u} P :=
    module_finitePresentation_essentiallySmall A
  have hfree (n : ℕ) : IsFinitelyPresentable (ModuleCat.of A (Fin n → A)) := by
    have : IsFinitelyPresentable (ULift.{u} (Fin n)) := by
      exact ((hasCardinalLT_of_finite (ULift.{u} (Fin n)) Cardinal.aleph0)
        (Cardinal.IsRegular.aleph0_le Fact.out)).isCardinalPresentable
    have : (forget (ModuleCat.{u} A)).IsCardinalAccessible.{u} Cardinal.aleph0 :=
      (Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
        (F := forget (ModuleCat.{u} A))).2 inferInstance
    have hfree' : IsFinitelyPresentable
        ((ModuleCat.free A).obj (ULift.{u} (Fin n))) :=
      (ModuleCat.adj A).isCardinalPresentable_leftAdjoint_obj
        Cardinal.aleph0 (ULift.{u} (Fin n))
    let e : (ModuleCat.free A).obj (ULift.{u} (Fin n)) ≅
        ModuleCat.of A (Fin n → A) :=
      ((Finsupp.domLCongr (Equiv.ulift.{u,0} :
          ULift.{u} (Fin n) ≃ Fin n)).trans
        (Finsupp.linearEquivFunOnFinite A A (Fin n))).toModuleIso
    exact isCardinalPresentable_of_iso e Cardinal.aleph0
  exact @exists_filteredColimitExtension_unique_up_to_iso
    _ _ _ _ _ _ P hsmall
    (fun X hX => by
      change Module.FinitePresentation A (X : Type u) at hX
      obtain ⟨n, m, f, g, hf, hfg⟩ :=
        Module.FinitePresentation.exists_fin' A (X : Type u)
      let f' : ModuleCat.of A (Fin n → A) ⟶ X := ModuleCat.ofHom f
      let g' : ModuleCat.of A (Fin m → A) ⟶ ModuleCat.of A (Fin n → A) :=
        ModuleCat.ofHom g
      let c : CokernelCofork g' := CokernelCofork.ofπ f' (by
        apply ModuleCat.hom_ext
        change f.comp g = 0
        exact LinearMap.ext (fun x => hfg.apply_apply_eq_zero x))
      have hc : IsColimit c :=
        ModuleCat.isColimitCokernelCofork g' f' hfg hf
      have hdiag : ∀ k, IsCardinalPresentable
          ((parallelPair g' 0).obj k) Cardinal.aleph0 := by
        intro k
        cases k with
        | zero => exact hfree m
        | one => exact hfree n
      exact @isCardinalPresentable_of_isColimit
        (ModuleCat.{u} A) _ _ WalkingParallelPair _ _ (parallelPair g' 0) c hc
        Cardinal.aleph0 Cardinal.fact_isRegular_aleph0
        ((hasCardinalLT_of_finite (Arrow WalkingParallelPair) Cardinal.aleph0)
          (Cardinal.IsRegular.aleph0_le Fact.out)) hdiag)
    (fun X => module_finitePresentation_ind X)
    F

private lemma module_finitely_presentable_of_finitePresentation
    (A : Type u) [Ring A] (X : ModuleCat.{u} A)
    (hX : Module.FinitePresentation A (X : Type u)) :
    IsFinitelyPresentable.{u} X := by
  let : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  have hfree (n : ℕ) : IsFinitelyPresentable (ModuleCat.of A (Fin n → A)) := by
    have : IsFinitelyPresentable (ULift.{u} (Fin n)) := by
      exact ((hasCardinalLT_of_finite (ULift.{u} (Fin n)) Cardinal.aleph0)
        (Cardinal.IsRegular.aleph0_le Fact.out)).isCardinalPresentable
    have : (forget (ModuleCat.{u} A)).IsCardinalAccessible.{u} Cardinal.aleph0 :=
      (Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
        (F := forget (ModuleCat.{u} A))).2 inferInstance
    have hfree' : IsFinitelyPresentable
        ((ModuleCat.free A).obj (ULift.{u} (Fin n))) :=
      (ModuleCat.adj A).isCardinalPresentable_leftAdjoint_obj
        Cardinal.aleph0 (ULift.{u} (Fin n))
    let e : (ModuleCat.free A).obj (ULift.{u} (Fin n)) ≅
        ModuleCat.of A (Fin n → A) :=
      ((Finsupp.domLCongr (Equiv.ulift.{u,0} :
          ULift.{u} (Fin n) ≃ Fin n)).trans
        (Finsupp.linearEquivFunOnFinite A A (Fin n))).toModuleIso
    exact isCardinalPresentable_of_iso e Cardinal.aleph0
  obtain ⟨n, m, f, g, hf, hfg⟩ :=
    Module.FinitePresentation.exists_fin' A (X : Type u)
  let f' : ModuleCat.of A (Fin n → A) ⟶ X := ModuleCat.ofHom f
  let g' : ModuleCat.of A (Fin m → A) ⟶ ModuleCat.of A (Fin n → A) :=
    ModuleCat.ofHom g
  let c : CokernelCofork g' := CokernelCofork.ofπ f' (by
    apply ModuleCat.hom_ext
    change f.comp g = 0
    exact LinearMap.ext (fun x => hfg.apply_apply_eq_zero x))
  have hc : IsColimit c :=
    ModuleCat.isColimitCokernelCofork g' f' hfg hf
  have hdiag : ∀ k, IsCardinalPresentable
      ((parallelPair g' 0).obj k) Cardinal.aleph0 := by
    intro k
    cases k with
    | zero => exact hfree m
    | one => exact hfree n
  simpa [c] using (@isCardinalPresentable_of_isColimit
    (ModuleCat.{u} A) _ _ WalkingParallelPair _ _ (parallelPair g' 0) c hc
    Cardinal.aleph0 Cardinal.fact_isRegular_aleph0
    ((hasCardinalLT_of_finite (Arrow WalkingParallelPair) Cardinal.aleph0)
      (Cardinal.IsRegular.aleph0_le Fact.out)) hdiag)


theorem additiveCategory_has_arbitrary_direct_sums
    (B : Type u') [Category.{v'} B] [AdditiveCategory B]
    [HasFilteredColimitsOfSize.{w, w} B] :
    HasCoproducts.{w} B := by
  infer_instance

theorem additive_extension_of_finitely_presented_modules
    (A : Type u) [Ring A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B]
    [HasFilteredColimitsOfSize.{u, u} B]
    (F : FinitelyPresentedModuleCat.{u, u} A ⥤ B)
    (E : FilteredColimitExtension
      (finitelyPresentedModuleProperty.{u, u} A) F)
    [Functor.Additive F] :
    Functor.Additive E.functor ∧
      PreservesArbitraryDirectSums E.functor := by
  have hAdd : Functor.Additive E.functor := by
    constructor
    intro X Y f g
    let : PreservesFilteredColimitsOfSize E.functor := E.preservesFilteredColimits
    obtain ⟨J, _, _, pX, hpX⟩ := module_finitePresentation_ind X
    obtain ⟨K, _, _, pY, hpY⟩ := module_finitePresentation_ind Y
    have hcolim : IsColimit (E.functor.mapCocone pX.cocone) :=
      isColimitOfPreserves E.functor pX.isColimit
    apply hcolim.hom_ext
    intro i
    have hXi : Module.FinitePresentation A
        (pX.diag.obj i : Type u) := hpX i
    let : IsFinitelyPresentable.{u} (pX.diag.obj i) :=
      module_finitely_presentable_of_finitePresentation A _ hXi
    obtain ⟨j, qf, hqf⟩ :=
      IsFinitelyPresentable.exists_hom_of_isColimit pY.isColimit
        (pX.ι.app i ≫ f)
    obtain ⟨k, qg, hqg⟩ :=
      IsFinitelyPresentable.exists_hom_of_isColimit pY.isColimit
        (pX.ι.app i ≫ g)
    let l : K := IsFiltered.max j k
    let uj : j ⟶ l := IsFiltered.leftToMax j k
    let uk : k ⟶ l := IsFiltered.rightToMax j k
    let qf' := qf ≫ pY.diag.map uj
    let qg' := qg ≫ pY.diag.map uk
    have hqf' : pX.ι.app i ≫ f = qf' ≫ pY.ι.app l := by
      dsimp [qf', l, uj]
      rw [Category.assoc, pY.ι.naturality]
      simpa using hqf.symm
    have hqg' : pX.ι.app i ≫ g = qg' ≫ pY.ι.app l := by
      dsimp [qg', l, uk]
      rw [Category.assoc, pY.ι.naturality]
      simpa using hqg.symm
    let QX : FinitelyPresentedModuleCat.{u, u} A := ⟨pX.diag.obj i, hpX i⟩
    let QY : FinitelyPresentedModuleCat.{u, u} A := ⟨pY.diag.obj l, hpY l⟩
    let qf'' : QX ⟶ QY := ObjectProperty.homMk qf'
    let qg'' : QX ⟶ QY := ObjectProperty.homMk qg'
    have hres (q : QX ⟶ QY) :
        E.functor.map q.hom ≫ E.restrictionIso.hom.app
            QY = E.restrictionIso.hom.app QX ≫ F.map q := by
      exact E.restrictionIso.hom.naturality q
    have hqadd :
        E.functor.map (qf' + qg') ≫ E.restrictionIso.hom.app QY =
          E.functor.map qf' ≫ E.restrictionIso.hom.app QY +
            E.functor.map qg' ≫ E.restrictionIso.hom.app QY := by
      change E.functor.map (qf'' + qg'').hom ≫
          E.restrictionIso.hom.app QY =
        E.functor.map qf''.hom ≫ E.restrictionIso.hom.app QY +
          E.functor.map qg''.hom ≫ E.restrictionIso.hom.app QY
      rw [hres (qf'' + qg''), F.map_add, Preadditive.comp_add,
        ← hres qf'', ← hres qg'']
    have hqadd0 : E.functor.map (qf' + qg') =
        E.functor.map qf' + E.functor.map qg' := by
      apply (cancel_mono (E.restrictionIso.hom.app QY)).1
      simpa only [Preadditive.add_comp] using hqadd
    change E.functor.map (pX.ι.app i) ≫ E.functor.map (f + g) =
      E.functor.map (pX.ι.app i) ≫
        (E.functor.map f + E.functor.map g)
    have hsum : pX.ι.app i ≫ (f + g) =
        (qf' + qg') ≫ pY.ι.app l := by
      rw [Preadditive.comp_add, hqf', hqg', ← Preadditive.add_comp]
    rw [Preadditive.comp_add, ← E.functor.map_comp,
      ← E.functor.map_comp, ← E.functor.map_comp, hsum]
    calc
      E.functor.map ((qf' + qg') ≫ pY.ι.app l) =
          (E.functor.map qf' + E.functor.map qg') ≫
            E.functor.map (pY.ι.app l) := by
        rw [Functor.map_comp, hqadd0, Preadditive.add_comp]
      _ = E.functor.map (pX.ι.app i ≫ f) +
          E.functor.map (pX.ι.app i ≫ g) := by
        rw [Preadditive.add_comp, ← E.functor.map_comp,
          ← E.functor.map_comp, ← hqf', ← hqg']
  constructor
  · exact hAdd
  · let : Functor.Additive E.functor := hAdd
    let : PreservesFilteredColimitsOfSize E.functor := E.preservesFilteredColimits
    let : PreservesFiniteCoproducts E.functor :=
      Functor.preservesFiniteCoproductsOfAdditive E.functor
    intro J X
    let Xd : Discrete J ⥤ ModuleCat.{u} A := Discrete.functor X
    let D : Finset (Discrete J) ⥤ ModuleCat.{u} A :=
      { obj := fun S => ∐ fun x : S => Xd.obj x
        map := fun {S T} h => Sigma.desc fun y =>
          Sigma.ι (fun x : T => Xd.obj x) ⟨y, h.down.down y.2⟩
        map_id := by
          intro S
          apply Cofan.IsColimit.hom_ext (colimit.isColimit _)
          intro x
          simp [Cofan.inj]
        map_comp := by
          intro S T U h k
          apply Cofan.IsColimit.hom_ext (colimit.isColimit _)
          intro x
          simp [Cofan.inj] }
    let D' : Finset (Discrete J) ⥤ B :=
      { obj := fun S => ∐ fun x : S => E.functor.obj (Xd.obj x)
        map := fun {S T} h => Sigma.desc fun y =>
          Sigma.ι (fun x : T => E.functor.obj (Xd.obj x))
            ⟨y, h.down.down y.2⟩
        map_id := by
          intro S
          apply Cofan.IsColimit.hom_ext (colimit.isColimit _)
          intro x
          simp [Cofan.inj]
        map_comp := by
          intro S T U h k
          apply Cofan.IsColimit.hom_ext (colimit.isColimit _)
          intro x
          simp [Cofan.inj] }
    let e : D ⋙ E.functor ≅ D' :=
      NatIso.ofComponents (fun S =>
        PreservesCoproduct.iso E.functor (fun x : S => Xd.obj x)) (by
          intro S T h
          apply Cofan.IsColimit.hom_ext
            (isColimitOfHasCoproductOfPreservesColimit E.functor
              (fun x : S => Xd.obj x))
          intro x
          have hS : E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x) ≫
              (PreservesCoproduct.iso E.functor (fun x : S => Xd.obj x)).hom =
                Sigma.ι (fun x : S => E.functor.obj (Xd.obj x)) x := by
            simpa [← PreservesCoproduct.inv_hom] using
              (map_ι_comp_inv_sigmaComparison E.functor
                (fun x : S => Xd.obj x) x)
          have hT : E.functor.map
              (Sigma.ι (fun x : T => Xd.obj x) ⟨x, h.down.down x.2⟩) ≫
              (PreservesCoproduct.iso E.functor (fun x : T => Xd.obj x)).hom =
                Sigma.ι (fun x : T => E.functor.obj (Xd.obj x))
                  ⟨x, h.down.down x.2⟩ := by
            simpa [← PreservesCoproduct.inv_hom] using
              (map_ι_comp_inv_sigmaComparison E.functor
                (fun x : T => Xd.obj x) ⟨x, h.down.down x.2⟩)
          change E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x) ≫
              E.functor.map (Sigma.desc fun y =>
                Sigma.ι (fun z : T => Xd.obj z) ⟨y, h.down.down y.2⟩) ≫
                (PreservesCoproduct.iso E.functor (fun x : T => Xd.obj x)).hom =
            E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x) ≫
              (PreservesCoproduct.iso E.functor (fun x : S => Xd.obj x)).hom ≫
                Sigma.desc (fun y =>
                  Sigma.ι (fun z : T => E.functor.obj (Xd.obj z))
                    ⟨y, h.down.down y.2⟩)
          rw [← Category.assoc, ← E.functor.map_comp]
          rw [Sigma.ι_desc]
          rw [hT]
          rw [← Category.assoc, hS]
          rw [Sigma.ι_desc]
        )
    have hD : D = CoproductsFromFiniteFiltered.liftToFinsetObj Xd := by
      fapply CategoryTheory.Functor.ext
      · intro S
        rfl
      · intro S T h
        rfl
    let c : Cocone D := by
      refine
        { pt := ∐ X
          ι :=
            { app := fun S => Sigma.desc fun s => Sigma.ι X s.1.as
              naturality := by
                intro S T h
                dsimp [D]
                apply Cofan.IsColimit.hom_ext (colimit.isColimit _)
                intro x
                simp [Cofan.inj] } }
    have hc : IsColimit c := by
      cases hD
      change IsColimit
        (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone X)
      exact CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone X
    let c' : Cocone D' := by
      refine
        { pt := ∐ fun j => E.functor.obj (X j)
          ι :=
            { app := fun S => Sigma.desc fun s => Sigma.ι
                (fun j => E.functor.obj (X j)) s.1.as
              naturality := by
                intro S T h
                dsimp [D']
                apply Cofan.IsColimit.hom_ext (colimit.isColimit _)
                intro x
                simp [Cofan.inj] } }
    let σ : c'.pt ⟶ E.functor.obj c.pt := by
      simpa [c', c] using (sigmaComparison E.functor X)
    let q : Cocone (D ⋙ E.functor) :=
      { pt := c'.pt
        ι :=
          { app := fun S => (e.app S).hom ≫ c'.ι.app S
            naturality := by
              intro S T h
              dsimp
              simp
              rw [← Functor.comp_map, e.hom.naturality_assoc, c'.ι.naturality]
              simp } }
    let hqcolim : IsColimit (E.functor.mapCocone c) :=
      isColimitOfPreserves E.functor hc
    let i : E.functor.obj c.pt ⟶ c'.pt :=
      hqcolim.desc q
    have hqi (S : Finset (Discrete J)) :
        q.ι.app S ≫ σ =
          E.functor.map (c.ι.app S) := by
      dsimp [q, D]
      apply Cofan.IsColimit.hom_ext
        (isColimitOfHasCoproductOfPreservesColimit E.functor
          (fun x : S => Xd.obj x))
      intro x
      have hS : E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x) ≫
          e.hom.app S =
            Sigma.ι (fun x : S => E.functor.obj (Xd.obj x)) x := by
        change E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x) ≫
            (PreservesCoproduct.iso E.functor (fun x : S => Xd.obj x)).hom =
              Sigma.ι (fun x : S => E.functor.obj (Xd.obj x)) x
        simpa [← PreservesCoproduct.inv_hom] using
          (map_ι_comp_inv_sigmaComparison E.functor
            (fun x : S => Xd.obj x) x)
      simp only [Cofan.inj, Cofan.mk_ι_app]
      rw [Category.assoc (e.hom.app S) (c'.ι.app S) σ]
      rw [← Category.assoc (E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x))
        (e.hom.app S) (c'.ι.app S ≫ σ), hS]
      simp [σ, c', c]
      rw [← E.functor.map_comp, Sigma.ι_desc]
    have hiσ : i ≫ σ = 𝟙 _ := by
      apply hqcolim.hom_ext
      intro S
      dsimp [i]
      have hfac : E.functor.map (c.ι.app S) ≫ hqcolim.desc q =
          q.ι.app S := by
        simpa using hqcolim.fac q S
      rw [← Category.assoc (E.functor.map (c.ι.app S))
        (hqcolim.desc q) σ, hfac, hqi]
      simp
    have hσj (j : J) :
        Sigma.ι (fun j => E.functor.obj (X j)) j ≫ σ =
          E.functor.map (Sigma.ι X j) := by
      let S : Finset (Discrete J) := {Discrete.mk j}
      have hj : (Discrete.mk j : Discrete J) ∈ S := by simp [S]
      let x : S := ⟨Discrete.mk j, hj⟩
      have hS :
          E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x) ≫ e.hom.app S =
            Sigma.ι (fun x : S => E.functor.obj (Xd.obj x)) x := by
        change E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x) ≫
            (PreservesCoproduct.iso E.functor (fun x : S => Xd.obj x)).hom =
              Sigma.ι (fun x : S => E.functor.obj (Xd.obj x)) x
        simpa [← PreservesCoproduct.inv_hom] using
          (map_ι_comp_inv_sigmaComparison E.functor
            (fun x : S => Xd.obj x) x)
      have hc'j :
          Sigma.ι (fun j => E.functor.obj (X j)) j =
            Sigma.ι (fun x : S => E.functor.obj (Xd.obj x)) x ≫
              c'.ι.app S := by
        simp [c', S, x]
      have hcj : Sigma.ι X j =
          Sigma.ι (fun x : S => Xd.obj x) x ≫ c.ι.app S := by
        simp [c, S, x]
      rw [hc'j]
      rw [Category.assoc
        (Sigma.ι (fun x : S => E.functor.obj (Xd.obj x)) x)
        (c'.ι.app S) σ]
      rw [← hS]
      rw [Category.assoc
        (E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x))
        (e.hom.app S) (c'.ι.app S ≫ σ)]
      have hqS : e.hom.app S ≫ c'.ι.app S = q.ι.app S := by
        dsimp [q]
      rw [← Category.assoc (e.hom.app S) (c'.ι.app S) σ, hqS,
        hqi S, ← E.functor.map_comp, hcj]
    have hιi (j : J) :
        E.functor.map (Sigma.ι X j) ≫ i =
          Sigma.ι (fun j => E.functor.obj (X j)) j := by
      let S : Finset (Discrete J) := {Discrete.mk j}
      have hj : (Discrete.mk j : Discrete J) ∈ S := by simp [S]
      let x : S := ⟨Discrete.mk j, hj⟩
      have hS :
          E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x) ≫ e.hom.app S =
            Sigma.ι (fun x : S => E.functor.obj (Xd.obj x)) x := by
        change E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x) ≫
            (PreservesCoproduct.iso E.functor (fun x : S => Xd.obj x)).hom =
              Sigma.ι (fun x : S => E.functor.obj (Xd.obj x)) x
        simpa [← PreservesCoproduct.inv_hom] using
          (map_ι_comp_inv_sigmaComparison E.functor
            (fun x : S => Xd.obj x) x)
      have hc'j :
          Sigma.ι (fun j => E.functor.obj (X j)) j =
            Sigma.ι (fun x : S => E.functor.obj (Xd.obj x)) x ≫
              c'.ι.app S := by
        simp [c', S, x]
      have hcj : Sigma.ι X j =
          Sigma.ι (fun x : S => Xd.obj x) x ≫ c.ι.app S := by
        simp [c, S, x]
      have hfac : E.functor.map (c.ι.app S) ≫ hqcolim.desc q =
          q.ι.app S := by
        simpa using hqcolim.fac q S
      rw [hcj, E.functor.map_comp]
      dsimp [i]
      rw [Category.assoc
        (E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x))
        (E.functor.map (c.ι.app S)) (hqcolim.desc q), hfac]
      have hqS : e.hom.app S ≫ c'.ι.app S = q.ι.app S := by
        dsimp [q]
      rw [← hqS]
      rw [← Category.assoc
        (E.functor.map (Sigma.ι (fun x : S => Xd.obj x) x))
        (e.hom.app S) (c'.ι.app S), hS, hc'j]
    have hσi : σ ≫ i = 𝟙 _ := by
      apply Cofan.IsColimit.hom_ext (colimit.isColimit _)
      intro j
      simp only [Cofan.inj]
      change Sigma.ι (fun j => E.functor.obj (X j)) j ≫ σ ≫ i =
        Sigma.ι (fun j => E.functor.obj (X j)) j ≫ 𝟙 _
      rw [← Category.assoc
        (Sigma.ι (fun j => E.functor.obj (X j)) j) σ i, hσj, hιi]
      simp
    let : IsIso σ := ⟨⟨i, hσi, hiσ⟩⟩
    simpa [σ, c', c] using (inferInstance : IsIso σ)

theorem additiveCategory_has_arbitrary_colimits
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B]
    [HasFilteredColimitsOfSize.{w, w} B] :
    HasColimitsOfSize.{w, w} B := by
  let hCoProd : HasCoproducts.{w} B :=
    additiveCategory_hasCoproducts_of_hasFilteredColimits B
  let hCoEq : HasCoequalizers B := Preadditive.hasCoequalizers_of_hasCokernels
  exact @has_colimits_of_hasCoequalizers_and_coproducts B _ hCoProd hCoEq

theorem right_exact_extension_of_finitely_presented_modules
    (A : Type u) [Ring A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B]
    [HasFilteredColimitsOfSize.{u, u} B]
    (F : FinitelyPresentedModuleCat.{u, u} A ⥤ B)
    (E : FilteredColimitExtension
      (finitelyPresentedModuleProperty.{u, u} A) F)
    (hF : IsRightExact F) :
    Functor.Additive E.functor ∧
      IsRightExact E.functor ∧
        PreservesArbitraryDirectSums E.functor := by
  sorry

theorem additiveCategory_has_finite_limits
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasKernels B] :
    HasFiniteLimits B := by
  exact hasFiniteLimits_of_additive_of_hasKernels B

theorem left_exact_extension_of_finitely_presented_modules
    (A : Type u) [CommRing A] (hA : IsCoherentRing A)
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasKernels B]
    [HasFilteredColimitsOfSize.{u, u} B]
    (hComm : FilteredColimitsCommuteWithKernels B)
    (F : FinitelyPresentedModuleCat.{u, u} A ⥤ B)
    (E : FilteredColimitExtension
      (finitelyPresentedModuleProperty.{u, u} A) F)
    (hF : @IsLeftExact
      (FinitelyPresentedModuleCat.{u, u} A) _ B _
      (finitelyPresentedModuleCat_hasFiniteLimits_of_coherent.{u, u} A hA) F) :
    Functor.Additive E.functor ∧
      IsLeftExact E.functor ∧
        PreservesArbitraryDirectSums E.functor := by
  sorry

theorem additiveCategory_has_finite_colimits
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B] :
    HasFiniteColimits B := by
  exact hasFiniteColimits_of_additive_of_hasCokernels B

/-! ## Classification by the image of the regular module -/

def regularModule (A : Type u) [CommRing A] : ModuleCat.{u} A :=
  ModuleCat.of A A

def regularModuleFp (A : Type u) [CommRing A] :
    FinitelyPresentedModuleCat.{u, u} A :=
  ⟨regularModule A, by
    change Module.FinitePresentation A (A : Type u)
    infer_instance⟩

def regularModuleScalar (A : Type u) [CommRing A] (a : A) :
    regularModule A ⟶ regularModule A :=
  ModuleCat.ofHom (LinearMap.mulLeft A a)

def regularModuleFpScalar (A : Type u) [CommRing A] (a : A) :
    regularModuleFp A ⟶ regularModuleFp A :=
  ObjectProperty.homMk (regularModuleScalar A a)

def moduleActionOfFinitelyPresentedFunctor
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [Preadditive B]
    (F : FinitelyPresentedModuleCat.{u, u} A ⥤ B) :
    ModuleActionObject A B where
  carrier := F.obj (regularModuleFp A)
  action :=
    { toFun := fun a => F.map (regularModuleFpScalar A a)
      map_one' := by sorry
      map_mul' := by sorry
      map_zero' := by sorry
      map_add' := by sorry }

def evaluationOnFinitelyPresentedModules
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B] :
    RightExactFunctorCat (FinitelyPresentedModuleCat.{u, u} A) B ⥤
      ModuleActionCat A B where
  obj F := moduleActionOfFinitelyPresentedFunctor A B F.1
  map f :=
    { hom := f.hom.app (regularModuleFp A)
      comm := by sorry }
  map_id := by
    intro F
    apply ModuleActionObject.hom_ext
    rfl
  map_comp := by
    intro F G H f g
    apply ModuleActionObject.hom_ext
    rfl

theorem functor_on_finitely_presented_modules_classification
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B] :
    (evaluationOnFinitelyPresentedModules A B).IsEquivalence := by
  sorry

def moduleActionOfModuleFunctor
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [Preadditive B]
    (F : ModuleCat.{u} A ⥤ B) :
    ModuleActionObject A B where
  carrier := F.obj (regularModule A)
  action :=
    { toFun := fun a => F.map (regularModuleScalar A a)
      map_one' := by sorry
      map_mul' := by sorry
      map_zero' := by sorry
      map_add' := by sorry }

def evaluationOnModules
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B]
    [HasCoproducts.{u} B] :
    RightExactDirectSumsFunctorCat (ModuleCat.{u} A) B ⥤
      ModuleActionCat A B where
  obj F := moduleActionOfModuleFunctor A B F.1
  map f :=
    { hom := f.hom.app (regularModule A)
      comm := by sorry }
  map_id := by
    intro F
    apply ModuleActionObject.hom_ext
    rfl
  map_comp := by
    intro F G H f g
    apply ModuleActionObject.hom_ext
    rfl

theorem functor_on_modules_classification
    (A : Type u) [CommRing A]
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B]
    [HasCoproducts.{u} B] :
    (evaluationOnModules A B).IsEquivalence := by
  sorry

end Formalization.Books.Functors.Unit02
