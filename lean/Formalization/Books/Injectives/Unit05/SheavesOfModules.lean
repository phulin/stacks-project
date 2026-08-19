import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.Sheaves.Unit25.Infrastructure
import Formalization.Books.Sheaves.Unit27.Skyscraper
import Formalization.Books.Injectives.Unit04.AbelianSheaves
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Injectives, Chapter 5: Sheaves of modules on a ringed space

The ringed-space and sheaf-of-modules objects are the canonical interfaces
from the earlier Sheaves chapters.  The pointwise construction in the source
is represented by the existing module skyscrapers and their product; the
underlying additive sheaf is also recorded separately so that the formula
`U ↦ ∏ x ∈ U, I x` remains visible.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Homology.Unit27
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

namespace Formalization.Books.Injectives.Unit05

/-! ## Stalkwise modules and the pointwise product -/

/-- The `𝒪_{X,x}`-module obtained by taking the stalk of an `𝒪_X`-module. -/
abbrev stalkModule (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (x : X) :=
  ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x))

/-- The additive skyscraper used to describe the underlying sheaf of a module
skyscraper.  The generic Mathlib construction is used with classical
decidability of membership in an open. -/
noncomputable def additiveSkyscraperSheaf (X : RingedSpace.{v}) (x : X)
    (A : AddCommGrpCat.{v}) : TopCat.Sheaf AddCommGrpCat.{v} X.carrier := by
  classical
  exact skyscraperSheaf x A

/-- Data for a sheaf of `𝒪_X`-modules whose underlying additive sheaf is the
skyscraper with prescribed value `I` at `x`. -/
structure ModuleSkyscraperData (X : RingedSpace.{v}) (x : X)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) where
  sheaf : Mod X.structureSheaf
  underlying_iso :
    Nonempty (sheaf.val.presheaf ≅
      (additiveSkyscraperSheaf X x (AddCommGrpCat.of (I : Type v))).presheaf)

/-- Existence of the module-valued skyscraper construction.  The underlying
additive sheaf is the canonical Mathlib skyscraper; the scalar action is the
source's varying stalk-sheaf action. -/
theorem exists_moduleSkyscraperSheaf (X : RingedSpace.{v}) (x : X)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    Nonempty (ModuleSkyscraperData X x I) := by
  classical
  let D := Classical.choice
    (Formalization.Books.Sheaves.Unit27.exists_moduleSkyscraperSheaf
      X.structureSheaf x I)
  refine ⟨{ sheaf := D.sheaf, underlying_iso := ?_ }⟩
  simpa [additiveSkyscraperSheaf,
    Formalization.Books.Sheaves.Unit27.abelianSkyscraperSheaf] using D.underlying_iso

/-- A chosen module-valued skyscraper sheaf. -/
noncomputable def moduleSkyscraperSheaf (X : RingedSpace.{v}) (x : X)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    Mod X.structureSheaf :=
  Formalization.Books.Sheaves.Unit27.moduleSkyscraperSheaf X.structureSheaf x I

/-- The family of modules occurring in the source's pointwise formula. -/
abbrev pointwiseProductValue (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
    (U : Opens X.carrier) : Type v :=
  ∀ x : U, (I x : Type v)

/-- The underlying additive sheaf `U ↦ ∏_{x ∈ U} I_x`, expressed as the
product of the canonical additive skyscraper sheaves. -/
noncomputable def pointwiseProductSheaf (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    TopCat.Sheaf AddCommGrpCat.{v} X.carrier :=
  ∏ᶜ fun x : X => additiveSkyscraperSheaf X x (AddCommGrpCat.of (I x : Type v))

/-- The value of the pointwise product sheaf is the product over the points
of the open set, with the zero factors outside the open set omitted. -/
theorem pointwiseProductSheaf_value_formula (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
    (U : Opens X.carrier) :
    Nonempty
      ((pointwiseProductSheaf X I).presheaf.obj (op U) ≅
        AddCommGrpCat.of (pointwiseProductValue X I U)) := by
  simpa [pointwiseProductSheaf, pointwiseProductValue,
    additiveSkyscraperSheaf,
    skyscraperSheafFunctor,
    Formalization.Books.Injectives.Unit04.abelianSheafSkyscraperProduct,
    Formalization.Books.Injectives.Unit04.abelianSkyscraperSheafFunctor,
    Formalization.Books.Injectives.Unit04.abelianSheafPointwiseProductObject] using
    (Formalization.Books.Injectives.Unit04.abelianSheafSkyscraperProduct_pointwise_formula
      (fun x : X => AddCommGrpCat.of (I x : Type v)) U)

/-! ## The module skyscraper product -/

/-- The sheaf of `𝒪_X`-modules obtained by taking the product of the module
skyscrapers with stalk values `I_x`. -/
noncomputable def skyscraperProduct (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    Mod X.structureSheaf :=
  ∏ᶜ fun x : X => moduleSkyscraperSheaf X x (I x)

/-- The underlying additive presheaf of the module skyscraper product is the
pointwise product presheaf. -/
theorem skyscraperProduct_underlying_iso (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    Nonempty
      ((skyscraperProduct X I).val.presheaf ≅
        (pointwiseProductSheaf X I).presheaf) := by
  let G := PresheafOfModules.toPresheaf X.structureSheaf.obj
  let D : Discrete X ⥤ Mod X.structureSheaf :=
    Discrete.functor (fun x => moduleSkyscraperSheaf X x (I x))
  let F : Discrete X ⥤ PresheafOfModules X.structureSheaf.obj :=
    D ⋙ SheafOfModules.forget X.structureSheaf
  let K : Discrete X ⥤ TopCat.Sheaf AddCommGrpCat X.carrier :=
    Discrete.functor (fun x =>
      (additiveSkyscraperSheaf X x
        (AddCommGrpCat.of (I x : Type v))))
  let H : Discrete X ⥤ TopCat.Presheaf AddCommGrpCat X.carrier :=
    K ⋙ TopCat.Sheaf.forget AddCommGrpCat X.carrier
  let eNat : F ⋙ G ≅ H :=
    Discrete.natIso (fun j =>
      (Classical.choice
        (Formalization.Books.Sheaves.Unit27.exists_moduleSkyscraperSheaf
          X.structureSheaf j.as (I j.as))).underlying_iso.some)
  let p₀ : (SheafOfModules.forget X.structureSheaf).obj (limit D) ≅ limit F :=
    CategoryTheory.preservesLimitIso (SheafOfModules.forget X.structureSheaf) D
  let pD : (∏ᶜ fun x : X => moduleSkyscraperSheaf X x (I x)) ≅ limit D :=
    CategoryTheory.Limits.Pi.isoLimit D
  let p : G.obj (limit F) ≅ limit (F ⋙ G) :=
    CategoryTheory.preservesLimitIso G F
  let r₀ : (TopCat.Sheaf.forget AddCommGrpCat X.carrier).obj (limit K) ≅ limit H :=
    CategoryTheory.preservesLimitIso (TopCat.Sheaf.forget AddCommGrpCat X.carrier) K
  let pK : (∏ᶜ fun x : X =>
      additiveSkyscraperSheaf X x (AddCommGrpCat.of (I x : Type v))) ≅ limit K :=
    CategoryTheory.Limits.Pi.isoLimit K
  let c : Cone H :=
    { pt := limit (F ⋙ G)
      π :=
        { app := fun j => limit.π (F ⋙ G) j ≫ eNat.hom.app j
          naturality := by
            intro j j' f
            change limit.π (F ⋙ G) j' ≫ eNat.hom.app j' =
              limit.π (F ⋙ G) j ≫ eNat.hom.app j ≫ H.map f
            rw [← eNat.hom.naturality f, ← Category.assoc, limit.w] } }
  let c' : Cone (F ⋙ G) :=
    { pt := limit H
      π :=
        { app := fun j => limit.π H j ≫ eNat.inv.app j
          naturality := by
            intro j j' f
            change limit.π H j' ≫ eNat.inv.app j' =
              limit.π H j ≫ eNat.inv.app j ≫ (F ⋙ G).map f
            rw [← eNat.inv.naturality f, ← Category.assoc, limit.w] } }
  let q : limit (F ⋙ G) ≅ limit H :=
    { hom := limit.lift H c
      inv := limit.lift (F ⋙ G) c'
      hom_inv_id := by
        apply (limit.isLimit (F ⋙ G)).hom_ext
        intro j
        simp [c, c', eNat]
      inv_hom_id := by
        apply (limit.isLimit H).hom_ext
        intro j
        simp [c, c', eNat] }
  refine ⟨?_⟩
  let underlyingIso (M : PresheafOfModules X.structureSheaf.obj) :
      G.obj M ≅ M.presheaf := by
    refine NatIso.ofComponents (fun U => ?_) (fun {U V} f => ?_)
    · let hU := PresheafOfModules.toPresheaf_obj_coe M U
      refine
        { hom := AddCommGrpCat.ofHom
            { toFun := fun m => hU ▸ m
              map_zero' := by subst hU; rfl
              map_add' := by intro m n; subst hU; rfl }
          inv := AddCommGrpCat.ofHom
            { toFun := fun m => hU.symm ▸ m
              map_zero' := by subst hU; rfl
              map_add' := by intro m n; subst hU; rfl }
          hom_inv_id := by
            apply AddCommGrpCat.hom_ext
            ext m
            subst hU
            rfl
          inv_hom_id := by
            apply AddCommGrpCat.hom_ext
            ext m
            subst hU
            rfl }
    · apply AddCommGrpCat.hom_ext
      ext m
      rfl
  let sheafUnderlyingIso (S : TopCat.Sheaf AddCommGrpCat X.carrier) :
      (TopCat.Sheaf.forget AddCommGrpCat X.carrier).obj S ≅ S.presheaf :=
    Iso.refl _
  let hD : (skyscraperProduct X I).val.presheaf ≅
      G.obj ((SheafOfModules.forget X.structureSheaf).obj (limit D)) := by
    simpa [skyscraperProduct, D] using
      (underlyingIso (skyscraperProduct X I).val).symm.trans
        (G.mapIso ((SheafOfModules.forget X.structureSheaf).mapIso pD))
  let hK : limit H ≅ (pointwiseProductSheaf X I).presheaf := by
    simpa [pointwiseProductSheaf, K, H] using
      r₀.symm.trans
        (((TopCat.Sheaf.forget AddCommGrpCat X.carrier).mapIso pK).symm.trans
          (sheafUnderlyingIso (pointwiseProductSheaf X I)))
  exact hD.trans ((G.mapIso p₀).trans ((p.trans q).trans hK))

/-- The displayed section formula for the `𝒪_X`-module product. -/
theorem skyscraperProduct_value_formula (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
    (U : Opens X.carrier) :
    Nonempty
      ((skyscraperProduct X I).val.presheaf.obj (op U) ≅
        AddCommGrpCat.of (pointwiseProductValue X I U)) := by
  obtain ⟨e⟩ := skyscraperProduct_underlying_iso X I
  obtain ⟨f⟩ := pointwiseProductSheaf_value_formula X I U
  exact ⟨e.app (op U) ≪≫ f⟩

/-! ## The canonical stalk map and injectivity -/

/-- Stalkwise data for the injective modules `I_x` and the embeddings of the
stalks of a fixed sheaf `F`. -/
structure StalkwiseInjectiveEmbeddingData
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) where
  I : ∀ x : X, ModuleCat.{v}
    (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)
  j : ∀ x : X, stalkModule X F x ⟶ I x
  mono_j : ∀ x : X, Mono (j x)
  injective_I : ∀ x : X, Injective (I x)

/-- The stalk/skyscraper Hom correspondence used in the source. -/
theorem exists_stalkSkyscraperHomEquiv (X : RingedSpace.{v}) (x : X)
    (F : Mod X.structureSheaf)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    Nonempty ((stalkModule X F x ⟶ I) ≃
      (F ⟶ moduleSkyscraperSheaf X x I)) := by
  sorry

/-- A chosen stalk/skyscraper Hom equivalence. -/
noncomputable def stalkSkyscraperHomEquiv (X : RingedSpace.{v}) (x : X)
    (F : Mod X.structureSheaf)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    (stalkModule X F x ⟶ I) ≃
    (F ⟶ moduleSkyscraperSheaf X x I) :=
  let K := Classical.choice
    (Formalization.Books.Sheaves.Unit27.exists_moduleSkyscraperSheafFunctor
      X.structureSheaf x)
  let e : (Formalization.Books.Sheaves.Unit27.moduleSkyscraperSheafFunctor
        X.structureSheaf x).obj I ≅ moduleSkyscraperSheaf X x I := by
    simpa [K, Formalization.Books.Sheaves.Unit27.moduleSkyscraperSheafFunctor,
      moduleSkyscraperSheaf, exists_moduleSkyscraperSheaf] using
      (K.obj_iso I).some
  let eHom : (F ⟶ (Formalization.Books.Sheaves.Unit27.moduleSkyscraperSheafFunctor
      X.structureSheaf x).obj I) ≃ (F ⟶ moduleSkyscraperSheaf X x I) :=
    { toFun := fun h => h ≫ e.hom
      invFun := fun h => h ≫ e.inv
      left_inv := by intro h; simp [e, Category.assoc]
      right_inv := by intro h; simp [e, Category.assoc] }
  (Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperHomEquiv
      X.structureSheaf x F I).trans eHom

/-- Each module skyscraper with injective support stalk is injective. -/
theorem moduleSkyscraper_injective (X : RingedSpace.{v}) (x : X)
    (I : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
    (hI : Injective I) :
    Injective (moduleSkyscraperSheaf X x I) := by
  sorry

/-- A product of module skyscrapers with injective stalk values is injective. -/
theorem skyscraperProduct_injective (X : RingedSpace.{v})
    (I : ∀ x : X, ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
    (hI : ∀ x : X, Injective (I x)) :
    Injective (skyscraperProduct X I) := by
  have hSkyscraper : ∀ x : X, Injective (moduleSkyscraperSheaf X x (I x)) :=
    fun x => moduleSkyscraper_injective X x (I x) (hI x)
  exact @Formalization.Books.Homology.Unit27.product_injective
    (Mod X.structureSheaf) inferInstance inferInstance X
    (fun x : X => moduleSkyscraperSheaf X x (I x)) inferInstance hSkyscraper

/-- The source's canonical map from a sheaf to the product of the chosen
injective stalk modules. -/
noncomputable def stalkwiseProductMap (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (D : StalkwiseInjectiveEmbeddingData X F) :
    F ⟶ skyscraperProduct X D.I :=
  Pi.lift fun x => stalkSkyscraperHomEquiv X x F (D.I x) (D.j x)

/-- The component of the product map at `x` is the skyscraper morphism
corresponding to the stalk embedding `j_x`; this is the Lean form of
`s ↦ (j_x(s_x))_x`. -/
theorem stalkwiseProductMap_component (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (D : StalkwiseInjectiveEmbeddingData X F)
    (x : X) :
    stalkwiseProductMap X F D ≫
        Pi.π (fun x : X => moduleSkyscraperSheaf X x (D.I x)) x =
      stalkSkyscraperHomEquiv X x F (D.I x) (D.j x) := by
  change (Pi.lift (fun x : X =>
      stalkSkyscraperHomEquiv X x F (D.I x) (D.j x))) ≫
        Pi.π (fun x : X => moduleSkyscraperSheaf X x (D.I x)) x =
      stalkSkyscraperHomEquiv X x F (D.I x) (D.j x)
  rw [limit.lift_π]
  rfl

/-- The canonical stalkwise map is a monomorphism. -/
theorem stalkwiseProductMap_mono (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (D : StalkwiseInjectiveEmbeddingData X F) :
    Mono (stalkwiseProductMap X F D) := by
  have hstalk (x : X) :
      Mono ((Formalization.Books.Sheaves.Unit27.moduleStalkFunctor X.structureSheaf x).map
        (stalkwiseProductMap X F D)) := by
    let jx :
        (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
          X.structureSheaf x).obj F ⟶ D.I x := D.j x
    let K := Classical.choice
      (Formalization.Books.Sheaves.Unit27.exists_moduleSkyscraperSheafFunctor
        X.structureSheaf x)
    let e : (Formalization.Books.Sheaves.Unit27.moduleSkyscraperSheafFunctor
          X.structureSheaf x).obj (D.I x) ≅
        moduleSkyscraperSheaf X x (D.I x) := by
      simpa [K, Formalization.Books.Sheaves.Unit27.moduleSkyscraperSheafFunctor,
        moduleSkyscraperSheaf, exists_moduleSkyscraperSheaf] using
        (K.obj_iso (D.I x)).some
    let φ :=
      Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperHomEquiv
        X.structureSheaf x F (D.I x)
    have hφ : Mono ((Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
        X.structureSheaf x).map
        (φ jx)) := by
      constructor
      intro Z a b hab
      have hjx : Mono jx := by
        exact D.mono_j x
      apply hjx.right_cancellation
      change a ≫ D.j x = b ≫ D.j x
      have hc :=
        Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperHomEquiv_counit
          X.structureSheaf x F (D.I x) (D.j x)
      rw [hc]
      simpa only [jx, Category.assoc] using congrArg (fun k => k ≫
        (Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperAdjunction
          X.structureSheaf x).counit.app (D.I x)) hab
    have heq :
        stalkSkyscraperHomEquiv X x F (D.I x) (D.j x) =
          φ jx ≫ e.hom := by
      rfl
    have hcomponent : Mono
        ((Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
          X.structureSheaf x).map
          (stalkwiseProductMap X F D ≫
            (show skyscraperProduct X D.I ⟶
                moduleSkyscraperSheaf X x (D.I x) from
              Pi.π (fun x : X => moduleSkyscraperSheaf X x (D.I x)) x))) := by
      rw [stalkwiseProductMap_component, heq]
      change Mono ((Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
        X.structureSheaf x).map (φ jx ≫ e.hom))
      have hcomp : Mono (
          (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
            X.structureSheaf x).map (φ jx) ≫
          (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
            X.structureSheaf x).map e.hom) := by
        have hEmono : Mono ((Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
            X.structureSheaf x).map e.hom) := by
          constructor
          intro Z a b hab
          have hab' := congrArg (fun k => k ≫
            (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
              X.structureSheaf x).map e.inv) hab
          simp only [Category.assoc] at hab'
          rw [← Functor.map_comp, Iso.hom_inv_id] at hab'
          simpa using hab'
        constructor
        intro Z a b hab
        apply hφ.right_cancellation
        apply hEmono.right_cancellation
        exact hab
      rw [← Functor.map_comp] at hcomp
      exact hcomp
    constructor
    intro Z a b hab
    apply hcomponent.right_cancellation
    change a ≫
        (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
          X.structureSheaf x).map
          (stalkwiseProductMap X F D ≫
            (show skyscraperProduct X D.I ⟶
                moduleSkyscraperSheaf X x (D.I x) from
              Pi.π (fun x : X => moduleSkyscraperSheaf X x (D.I x)) x)) =
      b ≫
        (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
          X.structureSheaf x).map
          (stalkwiseProductMap X F D ≫
            (show skyscraperProduct X D.I ⟶
                moduleSkyscraperSheaf X x (D.I x) from
              Pi.π (fun x : X => moduleSkyscraperSheaf X x (D.I x)) x))
    rw [Functor.map_comp]
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫
        (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
          X.structureSheaf x).map
          (show skyscraperProduct X D.I ⟶
              moduleSkyscraperSheaf X x (D.I x) from
            Pi.π (fun x : X => moduleSkyscraperSheaf X x (D.I x)) x)) hab
  have hSheaf : Mono
      ((SheafOfModules.toSheaf X.structureSheaf).map
        (stalkwiseProductMap X F D)) := by
    apply (TopCat.Presheaf.mono_iff_stalk_mono _).2
    intro x
    have hx := hstalk x
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    intro a b hab
    apply (ModuleCat.mono_iff_injective _).mp hx
    exact hab
  constructor
  intro Z f g hfg
  apply (SheafOfModules.toSheaf X.structureSheaf).map_injective
  apply hSheaf.right_cancellation
  simpa only [Functor.map_comp] using congrArg
    (fun k => (SheafOfModules.toSheaf X.structureSheaf).map k) hfg

/-- The target of the canonical stalkwise map is injective. -/
theorem stalkwiseProductMap_target_injective (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (D : StalkwiseInjectiveEmbeddingData X F) :
    Injective (skyscraperProduct X D.I) :=
  skyscraperProduct_injective X D.I D.injective_I

/-- Stalkwise injective embedding data exist for every sheaf of modules. -/
theorem exists_stalkwiseInjectiveEmbeddingData (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) :
    Nonempty (StalkwiseInjectiveEmbeddingData X F) := by
  classical
  let P : ∀ x : X, InjectivePresentation (stalkModule X F x) :=
    fun x => by
      letI : EnoughInjectives (ModuleCat
          (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :=
        ModuleCat.enoughInjectives _
      exact Classical.choice (EnoughInjectives.presentation (stalkModule X F x))
  exact ⟨{
    I := fun x => (P x).J
    j := fun x => (P x).f
    mono_j := fun x => (P x).mono
    injective_I := fun x => (P x).injective
  }⟩

/-! ## Enough injectives and functorial embeddings -/

/-- The category of sheaves of modules on a ringed space has enough
injectives, and the embeddings can be chosen functorially. -/
theorem sheafOfModules_has_enough_injectives (X : RingedSpace.{v}) :
    EnoughInjectives (Mod X.structureSheaf) ∧
      HasFunctorialInjectiveEmbeddings (C := Mod X.structureSheaf) := by
  constructor
  · refine ⟨?_⟩
    intro F
    obtain ⟨D⟩ := exists_stalkwiseInjectiveEmbeddingData X F
    refine ⟨{ J := skyscraperProduct X D.I,
                injective := stalkwiseProductMap_target_injective X F D,
                f := stalkwiseProductMap X F D,
                mono := stalkwiseProductMap_mono X F D }⟩
  · sorry

end Formalization.Books.Injectives.Unit05
