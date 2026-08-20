import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.Sheaves.Unit25.Infrastructure
import Formalization.Books.Sheaves.Unit27.Skyscraper
import Formalization.Books.Injectives.Unit04.AbelianSheaves
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.Generator.Abelian
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

/-- The stalk/skyscraper Hom correspondence used in the source.

Proof roadmap:

* Work throughout with the support ring
  `TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x`.  Choose
  `K` from
  `Formalization.Books.Sheaves.Unit27.exists_moduleSkyscraperSheafFunctor`
  in `Formalization/Books/Sheaves/Unit27/Skyscraper.lean`.
* As in the definition immediately below, obtain
  `e : (Unit27.moduleSkyscraperSheafFunctor X.structureSheaf x).obj I ≅
  moduleSkyscraperSheaf X x I` by `simpa` from `(K.obj_iso I).some`, unfolding
  `K`, both `moduleSkyscraperSheaf` definitions, and
  `Unit27.moduleSkyscraperSheafFunctor`.
* Build an equivalence `eHom` between the two Hom sets out of `F`: its
  forward and inverse maps postcompose with `e.hom` and `e.inv`; discharge
  the inverse laws with `simp [e, Category.assoc]`.
* Transitivity of equivalences now combines `eHom` with
  `Unit27.moduleStalkSkyscraperHomEquiv X.structureSheaf x F I` from the same
  file.  Its source is definitionally `stalkModule X F x`; wrap the composite
  equivalence in `Nonempty.intro`.

Do not try to close this theorem with `stalkSkyscraperHomEquiv`: that
definition occurs below this declaration.  Its body is instead an elaborated
template for the construction just described. -/
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

/-- Each module skyscraper with injective support stalk is injective.

Proof roadmap:

* Put `L := Unit27.moduleStalkFunctor X.structureSheaf x`,
  `R := Unit27.moduleSkyscraperSheafFunctor X.structureSheaf x`, and
  `adj := Unit27.moduleStalkSkyscraperAdjunction X.structureSheaf x`, all at
  universe `v`.  Lean does not currently infer `L.PreservesMonomorphisms`, so
  construct a local term `hL` of that type rather than adding a hypothesis to
  this theorem.
* For the `preserves` field of `hL`, take a mono `f : A ⟶ B`.  First obtain
  `hSheaf : Mono ((SheafOfModules.toSheaf X.structureSheaf).map f)` with
  `Functor.map_mono`; `SheafOfModules.toSheaf` is faithful in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean`.  Then use the following
  explicitly typed local helper (and apply it with `@... hSheaf`): for
  `S T : TopCat.Sheaf AddCommGrpCat.{v} X.carrier` and `g : S ⟶ T` with
  `[Mono g]`, `TopCat.Presheaf.stalk_mono_of_mono g x` from
  `Mathlib/Topology/Sheaves/Stalks.lean` proves
  `Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map g.hom)`.
* Convert that additive stalk mono to `Mono (L.map f)` using
  `ModuleCat.mono_iff_injective` and `AddCommGrpCat.mono_iff_injective`; after
  introducing two stalk elements, the required equality is definitionally
  the equality for `Unit27.moduleStalkAddMap`, so the original equality closes
  it directly.
* Apply
  `@CategoryTheory.Adjunction.map_injective _ _ _ _ L R adj hL I hI` from
  `Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean` to get
  `Injective (R.obj I)`.  Choose `K` from
  `Unit27.exists_moduleSkyscraperSheafFunctor` and, exactly as in
  `stalkSkyscraperHomEquiv` above, derive
  `e : R.obj I ≅ moduleSkyscraperSheaf X x I` from `(K.obj_iso I).some`.
  Finish with `CategoryTheory.Injective.of_iso e` applied to the injectivity
  of `R.obj I`.

Pass the proof terms `hSheaf` and `hL` explicitly through the helper and the
`@Adjunction.map_injective` call.  Introducing them with `haveI` or `letI`
causes the `haveILetI` style warning, which is rejected by PAF. -/
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
  · have hI : ∀ x : X, ∃ I : ModuleCat
        (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x),
        Injective I ∧ IsCoseparator I := by
      intro x
      let R := TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x
      let hEnough : ∀ [h : EnoughInjectives (ModuleCat R)], ∃ I : ModuleCat R,
          Injective I ∧ IsCoseparator I := by
        intro h
        exact Abelian.has_injective_coseparator (ModuleCat.of R (Shrink R))
          (ModuleCat.isSeparator R)
      exact @hEnough (ModuleCat.enoughInjectives R)
    let I : ∀ x : X, ModuleCat
        (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
      fun x => Classical.choose (hI x)
    have hI_injective : ∀ x : X, Injective (I x) := by
      intro x
      exact (Classical.choose_spec (hI x)).1
    have hI_coseparator : ∀ x : X, IsCoseparator (I x) := by
      intro x
      exact (Classical.choose_spec (hI x)).2
    let K : ∀ (F : Mod X.structureSheaf) (x : X), ModuleCat
        (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
      fun F x => ∏ᶜ fun _ : (stalkModule X F x ⟶ I x) => I x
    have hK_injective : ∀ (F : Mod X.structureSheaf) (x : X),
        Injective (K F x) := by
      intro F x
      let hProduct : ∀ [h : Injective (I x)], Injective (K F x) := by
        intro h
        exact inferInstance
      exact @hProduct (hI_injective x)
    have hK_mono : ∀ (F : Mod X.structureSheaf) (x : X), Mono
        (Pi.lift fun h : stalkModule X F x ⟶ I x => h) := by
      intro F x
      exact (isCoseparator_iff_mono (I x)).1 (hI_coseparator x) _
    let D : ∀ F : Mod X.structureSheaf, StalkwiseInjectiveEmbeddingData X F :=
      fun F => {
        I := K F
        j := fun x => Pi.lift fun h : stalkModule X F x ⟶ I x => h
        mono_j := hK_mono F
        injective_I := hK_injective F }
    let S : ∀ x : X, ModuleCat
        (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) ⥤
          Mod X.structureSheaf :=
      fun x => Formalization.Books.Sheaves.Unit27.moduleSkyscraperSheafFunctor
        X.structureSheaf x
    have hS_injective : ∀ (x : X) (A : ModuleCat
        (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)),
        Injective A → Injective ((S x).obj A) := by
      intro x A hA
      let e := Classical.choice
        ((Classical.choice
          (Formalization.Books.Sheaves.Unit27.exists_moduleSkyscraperSheafFunctor
            X.structureSheaf x)).obj_iso A)
      exact Injective.of_iso e.symm
        (moduleSkyscraper_injective X x A hA)
    let T : ∀ F : Mod X.structureSheaf, Mod X.structureSheaf :=
      fun F => ∏ᶜ fun x : X => (S x).obj (K F x)
    have hT_injective : ∀ F : Mod X.structureSheaf, Injective (T F) := by
      intro F
      let hProduct : ∀ [h : ∀ x : X, Injective ((S x).obj (K F x))],
          Injective (T F) := by
        intro h
        exact inferInstance
      exact @hProduct (fun x => hS_injective x (K F x) (hK_injective F x))
    let j' {F : Mod X.structureSheaf} (x : X) :
        (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
          X.structureSheaf x).obj F ⟶ K F x := by
      exact (D F).j x
    let η : ∀ F : Mod X.structureSheaf, F ⟶ T F :=
      fun F => Pi.lift fun x =>
        Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperHomEquiv
          X.structureSheaf x F (K F x) (j' x)
    let stalkMap {F G : Mod X.structureSheaf} (f : F ⟶ G) (x : X) :
        stalkModule X F x ⟶ stalkModule X G x :=
      Formalization.Books.Sheaves.Unit27.moduleStalkFunctor X.structureSheaf x |>.map f
    let k {F G : Mod X.structureSheaf} (f : F ⟶ G) (x : X) :
        K F x ⟶ K G x :=
      Pi.lift fun h : stalkModule X G x ⟶ I x =>
        Pi.π (fun _ : stalkModule X F x ⟶ I x => I x)
          (stalkMap f x ≫ h)
    have k_component {F G : Mod X.structureSheaf} (f : F ⟶ G) (x : X)
        (h : stalkModule X G x ⟶ I x) :
        k f x ≫ Pi.π (fun _ : stalkModule X G x ⟶ I x => I x) h =
          Pi.π (fun _ : stalkModule X F x ⟶ I x => I x)
            (stalkMap f x ≫ h) := by
      dsimp [k]
      exact Pi.lift_π _ _
    have k_id (F : Mod X.structureSheaf) (x : X) :
        k (𝟙 F) x = 𝟙 (K F x) := by
      apply limit.hom_ext
      rintro ⟨h⟩
      change k (𝟙 F) x ≫ Pi.π
        (fun _ : stalkModule X F x ⟶ I x => I x) h =
          𝟙 (K F x) ≫ Pi.π
            (fun _ : stalkModule X F x ⟶ I x => I x) h
      rw [k_component]
      change Pi.π (fun _ : stalkModule X F x ⟶ I x => I x)
        ((Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
          X.structureSheaf x).map (𝟙 F) ≫ h) = _
      rw [(Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
        X.structureSheaf x).map_id]
      exact congrArg (Pi.π (fun _ : stalkModule X F x ⟶ I x => I x))
        (Category.id_comp h)
    have k_comp {F G H : Mod X.structureSheaf}
        (f : F ⟶ G) (g : G ⟶ H) (x : X) :
        k (f ≫ g) x = k f x ≫ k g x := by
      apply limit.hom_ext
      rintro ⟨h⟩
      rw [Category.assoc, k_component, k_component, k_component]
      have hmap : stalkMap (f ≫ g) x = stalkMap f x ≫ stalkMap g x := by
        change (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
            X.structureSheaf x).map (f ≫ g) =
          (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
            X.structureSheaf x).map f ≫
            (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
              X.structureSheaf x).map g
        exact (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
          X.structureSheaf x).map_comp f g
      rw [hmap, Category.assoc]
    have k_fac {F G : Mod X.structureSheaf} (f : F ⟶ G) (x : X) :
        (D F).j x ≫ k f x =
          stalkMap f x ≫ (D G).j x := by
      apply limit.hom_ext
      rintro ⟨h⟩
      have hk : k f x ≫ Pi.π
          (fun _ : stalkModule X G x ⟶ I x => I x) h =
          Pi.π (fun _ : stalkModule X F x ⟶ I x => I x)
            (stalkMap f x ≫ h) := by
        dsimp [k]
        exact Pi.lift_π _ _
      have hj : (D G).j x ≫ limit.π
          (Discrete.functor (fun _ : stalkModule X G x ⟶ I x => I x))
            (Discrete.mk h) = h := by
        change (D G).j x ≫ Pi.π
          (fun _ : stalkModule X G x ⟶ I x => I x) h = h
        dsimp [D]
        exact Pi.lift_π _ _
      have hjF : (D F).j x ≫ Pi.π
          (fun _ : stalkModule X F x ⟶ I x => I x)
            (stalkMap f x ≫ h) = stalkMap f x ≫ h := by
        dsimp [D]
        exact Pi.lift_π _ _
      rw [Category.assoc, hk, hjF, Category.assoc, hj]
    have k_fac' {F G : Mod X.structureSheaf} (f : F ⟶ G) (x : X) :
        j' x ≫ k f x = stalkMap f x ≫ j' x := by
      simpa [j', stalkMap,
        Formalization.Books.Sheaves.Unit27.moduleStalkFunctor, stalkModule] using k_fac f x
    let q {F G : Mod X.structureSheaf} (f : F ⟶ G) : T F ⟶ T G :=
      Pi.lift fun x => Pi.π (fun x : X => (S x).obj (K F x)) x ≫
        (S x).map (k f x)
    have eta_fac {F G : Mod X.structureSheaf} (f : F ⟶ G) :
        f ≫ η G = η F ≫ q f := by
      apply limit.hom_ext
      rintro ⟨x⟩
      have hη : η G ≫ Pi.π
          (fun x : X => (S x).obj (K G x)) x =
          Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperHomEquiv
            X.structureSheaf x G (K G x) (j' x) := by
        dsimp [η]
        exact Pi.lift_π _ _
      have hq : q f ≫ Pi.π
          (fun x : X => (S x).obj (K G x)) x =
          Pi.π (fun x : X => (S x).obj (K F x)) x ≫ (S x).map (k f x) := by
        dsimp [q]
        exact Pi.lift_π _ _
      have hηF : η F ≫ Pi.π
          (fun x : X => (S x).obj (K F x)) x =
          Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperHomEquiv
            X.structureSheaf x F (K F x) (j' x) := by
        dsimp [η]
        exact Pi.lift_π _ _
      rw [Category.assoc, hη, Category.assoc, hq]
      rw [← Category.assoc, hηF]
      dsimp [S]
      rw [← (Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperAdjunction
        X.structureSheaf x).homEquiv_naturality_left,
        ← (Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperAdjunction
          X.structureSheaf x).homEquiv_naturality_right, k_fac' f x]
      rfl
    have hη_mono (F : Mod X.structureSheaf) : Mono (η F) := by
      have hstalk : ∀ x : X, Mono ((Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
          X.structureSheaf x).map (η F)) := by
        intro x
        let φ := (Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperHomEquiv
          X.structureSheaf x F (K F x)) (j' x)
        have hj' : Mono (j' (F := F) x) := by
          dsimp [j']
          exact (D F).mono_j x
        have hφ : Mono ((Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
            X.structureSheaf x).map φ) := by
          have hc := Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperHomEquiv_counit
            X.structureSheaf x F
              (K F x) (j' x)
          constructor
          intro Z a b hab
          apply hj'.right_cancellation
          rw [hc]
          simpa only [Category.assoc] using congrArg (fun t => t ≫
            (Formalization.Books.Sheaves.Unit27.moduleStalkSkyscraperAdjunction
              X.structureSheaf x).counit.app (K F x)) hab
        have hcomponent : Mono ((Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
            X.structureSheaf x).map
            (η F ≫ Pi.π (fun x : X => (S x).obj (K F x)) x)) := by
          have hηx : η F ≫ Pi.π
              (fun x : X => (S x).obj (K F x)) x = φ := by
            dsimp [φ, η]
            exact Pi.lift_π _ _
          rw [hηx]
          exact hφ
        constructor
        intro Z a b hab
        apply hcomponent.right_cancellation
        simpa only [Functor.map_comp, Category.assoc] using congrArg (fun t => t ≫
          (Formalization.Books.Sheaves.Unit27.moduleStalkFunctor
            X.structureSheaf x).map
            (Pi.π (fun x : X => (S x).obj (K F x)) x)) hab
      have hSheaf : Mono ((SheafOfModules.toSheaf X.structureSheaf).map (η F)) := by
        apply (TopCat.Presheaf.mono_iff_stalk_mono _).2
        intro x
        have hx := hstalk x
        apply (AddCommGrpCat.mono_iff_injective _).mpr
        intro a b hab
        apply (ModuleCat.mono_iff_injective _).mp hx
        exact hab
      constructor
      intro Z a b hab
      apply (SheafOfModules.toSheaf X.structureSheaf).map_injective
      apply hSheaf.right_cancellation
      simpa only [Functor.map_comp] using congrArg (fun t =>
        (SheafOfModules.toSheaf X.structureSheaf).map t) hab
    have q_component {F G : Mod X.structureSheaf} (f : F ⟶ G) (x : X) :
        q f ≫ Pi.π (fun x : X => (S x).obj (K G x)) x =
          Pi.π (fun x : X => (S x).obj (K F x)) x ≫ (S x).map (k f x) := by
      dsimp [q]
      exact Pi.lift_π _ _
    have q_id (F : Mod X.structureSheaf) :
        q (𝟙 F) = 𝟙 (T F) := by
      apply limit.hom_ext
      rintro ⟨x⟩
      rw [q_component, k_id]
      simp
    have q_comp {F G H : Mod X.structureSheaf}
        (f : F ⟶ G) (g : G ⟶ H) :
        q (f ≫ g) = q f ≫ q g := by
      apply limit.hom_ext
      rintro ⟨x⟩
      rw [q_component]
      rw [Category.assoc, q_component]
      rw [← Category.assoc, q_component]
      rw [k_comp f g x, Functor.map_comp, Category.assoc]
    let J : Mod X.structureSheaf ⥤ Arrow (Mod X.structureSheaf) :=
      { obj := fun F => Arrow.mk (η F)
        map := fun {F G} f => Arrow.homMk f (q f) (by
          change f ≫ η G = η F ≫ q f
          exact eta_fac f)
        map_id := by
          intro F
          apply Arrow.hom_ext
          · rfl
          · exact q_id F
        map_comp := by
          intro F G H f g
          apply Arrow.hom_ext
          · rfl
          · exact q_comp f g }
    have hJleft : J ⋙ Arrow.leftFunc = 𝟭 (Mod X.structureSheaf) := by
      apply CategoryTheory.Functor.hext
      · intro A
        rfl
      · intro A B f
        rfl
    have hJmono : ∀ A : Mod X.structureSheaf, Mono (J.obj A).hom := by
      intro A
      change Mono (η A)
      exact hη_mono A
    have hJinjective : ∀ A : Mod X.structureSheaf, Injective (J.obj A).right := by
      intro A
      change Injective (T A)
      exact hT_injective A
    exact ⟨J, hJleft, hJmono, hJinjective⟩

end Formalization.Books.Injectives.Unit05
