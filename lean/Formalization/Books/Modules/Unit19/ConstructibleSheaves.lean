import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Formalization.Books.Sheaves.Unit32.Infrastructure
import Formalization.Books.Sheaves.Unit31.Infrastructure
import Formalization.Books.Topology.Unit23.SpectralSpaces
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Modules, Chapter 19, Section 1: Constructible sheaves of sets

The source section is formalized here using the canonical set-valued sheaf,
pushforward, pullback, colimit, spectral-space, and subsheaf interfaces from
the earlier chapters and from Mathlib.
-/

namespace Formalization.Books.Modules.Unit19

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.Topology
open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit11
open Formalization.Books.Sheaves.Unit16
open Formalization.Books.Sheaves.Unit21
open Formalization.Books.Sheaves.Unit22

universe u

noncomputable section

private noncomputable def openSheafRestrictionFormulaIso {X : TopCat.{u}}
    (U : Opens X) (F : TopCat.Sheaf (Type u) X) :
    ((openSheafRestriction (Type u) U).obj F).presheaf ≅
      (openPresheafRestriction (Type u) U).obj F.presheaf := by
  let H : IsOpenEmbedding (TopCat.Hom.hom (TopCat.ofHom ⟨_, continuous_subtype_val⟩)) :=
    U.isOpenEmbedding
  letI : H.functor.IsContinuous (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X) := H.functor_isContinuous
  exact (H.isOpenMap.functor.sheafPushforwardContinuousCompSheafToPresheafIso
      (Type u) (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X)).app F ≪≫
    (H.isOpenMap.pullbackObjIso F.presheaf).symm

private noncomputable def openSheafRestrictionFormulaNatIso {X : TopCat.{u}}
    (U : Opens X) :
    (openSheafRestriction (Type u) U ⋙ TopCat.Sheaf.forget (Type u) (openSubspace U)) ≅
      (TopCat.Sheaf.forget (Type u) X ⋙ openPresheafRestriction (Type u) U) := by
  let H : IsOpenEmbedding (TopCat.Hom.hom (TopCat.ofHom ⟨_, continuous_subtype_val⟩)) :=
    U.isOpenEmbedding
  letI : H.functor.IsContinuous (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X) := H.functor_isContinuous
  exact (H.isOpenMap.functor.sheafPushforwardContinuousCompSheafToPresheafIso
      (Type u) (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X)) ≪≫
    Functor.isoWhiskerLeft (TopCat.Sheaf.forget (Type u) X)
      (H.isOpenMap.pullbackIso (C := Type u)).symm

private noncomputable def localConstantPUnitMap {X : TopCat.{u}} (U : Opens X)
    (F : TopCat.Sheaf (Type u) X) (s : F.presheaf.obj (op U)) :
    constantPresheaf (X := openSubspace U) PUnit ⟶
      ((openSheafRestriction (Type u) U).obj F).presheaf := by
  let T := ((openSheafRestriction (Type u) U).obj F).presheaf
  let Vtop : Opens (openSubspace U) := ⊤
  let e0 := (openSheafRestrictionFormulaNatIso U).app F
  let r := TopCat.Presheaf.pullbackObjObjOfImageOpen
    (openInclusion U) F.presheaf Vtop
    (U.isOpenEmbedding.isOpenMap Vtop Vtop.2)
  have hWU :
      (⟨(openInclusion U) '' Vtop,
        (U.isOpenEmbedding.isOpenMap Vtop Vtop.2)⟩ : Opens X) = U := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  let tP := r.inv
    (eqToHom (congrArg (fun Z : Opens X => F.presheaf.obj (op Z)) hWU.symm) s)
  let t : T.obj (op Vtop) := (e0.app (op Vtop)).inv tP
  exact {
    app := fun V => TypeCat.ofHom
      (show PUnit → T.obj V from
        fun _ => T.map (homOfLE (show V.unop ≤ Vtop from le_top)).op t)
    naturality := by
      intro V W' i
      have hi : i = (homOfLE (leOfHom i.unop)).op := by
        apply Subsingleton.elim
      rw [hi]
      apply ConcreteCategory.hom_ext
      intro a
      change PUnit at a
      cases a
      have hV : V.unop ≤ Vtop := le_top
      have hW : W'.unop ≤ V.unop := leOfHom i.unop
      have hcomp :
          (homOfLE hV).op ≫ (homOfLE hW).op =
            (homOfLE (hW.trans hV)).op := by
        apply Subsingleton.elim
      have hmap := T.map_comp (homOfLE hV).op (homOfLE hW).op
      rw [hcomp] at hmap
      calc
        _ = (ConcreteCategory.hom
            (T.map (homOfLE (hW.trans hV)).op)) t := by rfl
        _ = (ConcreteCategory.hom (T.map (homOfLE hW).op))
            ((ConcreteCategory.hom (T.map (homOfLE hV).op)) t) := by
          simpa using congrArg (fun q => (ConcreteCategory.hom q) t) hmap
        _ = _ := by rfl }

private noncomputable def constantSheafPUnitToConstantPresheaf
    {Y : TopCat.{u}} :
    (constantSheaf Y PUnit).presheaf ⟶ constantPresheaf (X := Y) PUnit := by
  exact {
    app := fun V => TypeCat.ofHom
      (show (constantSheaf Y PUnit).presheaf.obj V → PUnit from
        fun _ => PUnit.unit)
    naturality := by
      intro V W i
      apply ConcreteCategory.hom_ext
      intro a
      rfl }

private noncomputable def localSectionHom {X : TopCat.{u}} (U : Opens X)
    (F : TopCat.Sheaf (Type u) X) (s : F.presheaf.obj (op U)) :
    constantSheaf (openSubspace U) PUnit ⟶
      (openSheafRestriction (Type u) U).obj F :=
  (CategoryTheory.Sheaf.homEquiv).symm
    (constantSheafPUnitToConstantPresheaf (Y := openSubspace U) ≫
      localConstantPUnitMap U F s)

private noncomputable def openRestrictionStalkIso {X : TopCat.{u}}
    (U : Opens X) (F : TopCat.Sheaf (Type u) X) (x : openSubspace U) :
    ((openSheafRestriction (Type u) U).obj F).presheaf.stalk x ≅
      F.presheaf.stalk ((openInclusion U) x) := by
  let e := (openSheafRestrictionFormulaNatIso U).app F
  exact (TopCat.Presheaf.stalkFunctor (Type u) x).mapIso e ≪≫
    (TopCat.Presheaf.stalkPullbackIso (Type u) (openInclusion U)
      F.presheaf x).symm

private lemma openRestrictionStalkIso_naturality {X : TopCat.{u}}
    (U : Opens X) {E F : TopCat.Sheaf (Type u) X} (g : E ⟶ F)
    (y : openSubspace U) (a : E.presheaf.stalk ((openInclusion U) y)) :
    (openRestrictionStalkIso U F y).hom
        (StalkMap (((openSheafRestriction (Type u) U).map g).hom) y
          ((openRestrictionStalkIso U E y).inv a)) =
      StalkMap g.hom ((openInclusion U) y) a := by
  let lhs := (openRestrictionStalkIso U E y).inv ≫
    StalkMap (((openSheafRestriction (Type u) U).map g).hom) y ≫
    (openRestrictionStalkIso U F y).hom
  change (ConcreteCategory.hom lhs) a =
    (ConcreteCategory.hom (StalkMap g.hom ((openInclusion U) y))) a
  have hlhs : lhs = StalkMap g.hom ((openInclusion U) y) := by
    apply TopCat.Presheaf.stalk_hom_ext E.presheaf
    intro V hV
    dsimp [lhs, openRestrictionStalkIso, Functor.mapIso,
      TopCat.Presheaf.stalkPullbackIso, Iso.trans, Iso.symm]
    have hE := TopCat.Presheaf.germ_stalkPullbackHom
      (C := Type u) (X := openSubspace U) (Y := X)
      (f := openInclusion U) (F := E.presheaf) (x := y)
      (U := V) (hU := hV)
    have hy : (y.1 : X) = (ConcreteCategory.hom (openInclusion U)) y := rfl
    have hV' : (y.1 : X) ∈ V := by
      simpa only [hy] using hV
    have hVpull : y ∈ (Opens.map (openInclusion U)).obj V := hV
    have hE' :
        E.presheaf.germ V (y.1 : X) hV ≫
            TopCat.Presheaf.stalkPullbackHom (Type u) (openInclusion U)
              E.presheaf y =
          ((TopCat.Presheaf.pullbackPushforwardAdjunction
            (Type u) (openInclusion U)).unit.app E.presheaf).app (op V) ≫
            ((openPresheafRestriction (Type u) U).obj E.presheaf).germ
              ((Opens.map (openInclusion U)).obj V) y hV := by
      convert hE using 1
      · cases hy
        rfl
    let mE : ((openPresheafRestriction (Type u) U).obj E.presheaf).stalk y ⟶
        ((openSheafRestriction (Type u) U).obj E).presheaf.stalk y :=
      (TopCat.Presheaf.stalkFunctor (Type u) y).map
        ((openSheafRestrictionFormulaNatIso U).inv.app E)
    have hE'' :
        E.presheaf.germ V (y.1 : X) hV ≫
            (TopCat.Presheaf.stalkPullbackHom (Type u) (openInclusion U)
              E.presheaf y ≫ mE) =
          (((TopCat.Presheaf.pullbackPushforwardAdjunction
            (Type u) (openInclusion U)).unit.app E.presheaf).app (op V) ≫
            ((openPresheafRestriction (Type u) U).obj E.presheaf).germ
              ((Opens.map (openInclusion U)).obj V) y hV) ≫ mE := by
      calc
        _ = (E.presheaf.germ V (y.1 : X) hV ≫
            TopCat.Presheaf.stalkPullbackHom (Type u) (openInclusion U)
              E.presheaf y) ≫ mE := by
          exact (Category.assoc _ _ _).symm
        _ = (((TopCat.Presheaf.pullbackPushforwardAdjunction
            (Type u) (openInclusion U)).unit.app E.presheaf).app (op V) ≫
            ((openPresheafRestriction (Type u) U).obj E.presheaf).germ
              ((Opens.map (openInclusion U)).obj V) y hV) ≫ mE := by
          rw [hE']
    dsimp [mE] at hE''
    have hmapE := TopCat.Presheaf.stalkFunctor_map_germ
      (C := Type u) ((Opens.map (openInclusion U)).obj V) y hV
      ((openSheafRestrictionFormulaNatIso U).app E).inv
    conv_lhs =>
      rw [← Category.assoc]
      change (E.presheaf.germ V (y.1 : X) hV ≫
        (TopCat.Presheaf.stalkPullbackHom (Type u) (openInclusion U)
          E.presheaf y ≫
          (TopCat.Presheaf.stalkFunctor (Type u) y).map
            ((openSheafRestrictionFormulaNatIso U).inv.app E))) ≫ _
      erw [hE'']
    have hassoc :
        (((TopCat.Presheaf.pullbackPushforwardAdjunction
            (Type u) (openInclusion U)).unit.app E.presheaf).app (op V) ≫
          ((openPresheafRestriction (Type u) U).obj E.presheaf).germ
            ((Opens.map (openInclusion U)).obj V) y hVpull) ≫ mE =
          ((TopCat.Presheaf.pullbackPushforwardAdjunction
            (Type u) (openInclusion U)).unit.app E.presheaf).app (op V) ≫
            (((openPresheafRestriction (Type u) U).obj E.presheaf).germ
              ((Opens.map (openInclusion U)).obj V) y hVpull ≫ mE) :=
      Category.assoc _ _ _
    erw [hassoc]
    erw [hmapE]
    have hmapG := TopCat.Presheaf.stalkFunctor_map_germ
      (C := Type u) ((Opens.map (openInclusion U)).obj V) y hVpull
      (((openSheafRestriction (Type u) U).map g).hom)
    have hmapF := TopCat.Presheaf.stalkFunctor_map_germ
      (C := Type u) ((Opens.map (openInclusion U)).obj V) y hVpull
      ((openSheafRestrictionFormulaNatIso U).app F).hom
    have hF := TopCat.Presheaf.germ_stalkPullbackInv
      (C := Type u) (f := openInclusion U) (F := F.presheaf)
      (x := y) (V := (Opens.map (openInclusion U)).obj V) (hV := hVpull)
    dsimp [StalkMap]
    let uE : E.presheaf.obj (op V) ⟶
        ((TopCat.Presheaf.pullback (Type u) (openInclusion U)).obj E.presheaf).obj
          (op ((Opens.map (openInclusion U)).obj V)) :=
      ((TopCat.Presheaf.pullbackPushforwardAdjunction
        (Type u) (openInclusion U)).unit.app E.presheaf).app (op V)
    let uF : F.presheaf.obj (op V) ⟶
        ((TopCat.Presheaf.pullback (Type u) (openInclusion U)).obj F.presheaf).obj
          (op ((Opens.map (openInclusion U)).obj V)) :=
      ((TopCat.Presheaf.pullbackPushforwardAdjunction
        (Type u) (openInclusion U)).unit.app F.presheaf).app (op V)
    let eE :
        ((TopCat.Presheaf.pullback (Type u) (openInclusion U)).obj E.presheaf).obj
          (op ((Opens.map (openInclusion U)).obj V)) ⟶
        ((openSheafRestriction (Type u) U).obj E).obj.obj
          (op ((Opens.map (openInclusion U)).obj V)) :=
      ((openSheafRestrictionFormulaNatIso U).inv.app E).app
        (op ((Opens.map (openInclusion U)).obj V))
    let rE := TopCat.Presheaf.germ
      ((openSheafRestriction (Type u) U).obj E).obj
      ((Opens.map (openInclusion U)).obj V) y hVpull
    let sG := (TopCat.Presheaf.stalkFunctor (Type u) y).map
      (((openSheafRestriction (Type u) U).map g).hom)
    let sF := (TopCat.Presheaf.stalkFunctor (Type u) y).map
      ((openSheafRestrictionFormulaNatIso U).hom.app F)
    let pInv := TopCat.Presheaf.stalkPullbackInv
      (Type u) (openInclusion U) F.presheaf y
    have hassoc1 : (uE ≫ eE) ≫ rE = uE ≫ (eE ≫ rE) :=
      Category.assoc _ _ _
    have hassoc2 : ((uE ≫ eE) ≫ rE) ≫ (sG ≫ (sF ≫ pInv)) =
        (uE ≫ eE) ≫ (rE ≫ (sG ≫ (sF ≫ pInv))) :=
      Category.assoc _ _ _
    change ((uE ≫ eE ≫ rE) ≫ (sG ≫ (sF ≫ pInv))) =
      E.presheaf.germ V ((ConcreteCategory.hom (openInclusion U)) y) hV ≫
        (TopCat.Presheaf.stalkFunctor (Type u)
          ((ConcreteCategory.hom (openInclusion U)) y)).map g.hom
    let mapG := ((openSheafRestriction (Type u) U).map g).hom.app
      (op ((Opens.map (openInclusion U)).obj V))
    let rF := TopCat.Presheaf.germ
      ((openSheafRestriction (Type u) U).obj F).obj
      ((Opens.map (openInclusion U)).obj V) y hVpull
    let eF := ((openSheafRestrictionFormulaNatIso U).hom.app F).app
      (op ((Opens.map (openInclusion U)).obj V))
    let qF := TopCat.Presheaf.germ
      ((TopCat.Sheaf.forget (Type u) X ⋙
        openPresheafRestriction (Type u) U).obj F)
      ((Opens.map (openInclusion U)).obj V) y hVpull
    let qToF := TopCat.Presheaf.germToPullbackStalk
      (Type u) (openInclusion U) F.presheaf
      ((Opens.map (openInclusion U)).obj V) y hVpull
    have hmapG_assoc : rE ≫ (sG ≫ (sF ≫ pInv)) =
        (mapG ≫ rF) ≫ (sF ≫ pInv) := by
      calc
        _ = (rE ≫ sG) ≫ (sF ≫ pInv) :=
          (Category.assoc _ _ _).symm
        _ = (mapG ≫ rF) ≫ (sF ≫ pInv) := by
          convert congrArg (fun k => k ≫ (sF ≫ pInv)) hmapG using 1 <;> rfl
    have hmapF_eq : rF ≫ sF = eF ≫ qF := by
      convert hmapF using 1 ; rfl
    have hmapF_assoc : (mapG ≫ rF) ≫ (sF ≫ pInv) =
        mapG ≫ ((eF ≫ qF) ≫ pInv) := by
      calc
        _ = mapG ≫ (rF ≫ (sF ≫ pInv)) := Category.assoc _ _ _
        _ = mapG ≫ ((rF ≫ sF) ≫ pInv) := by
          congr 1
        _ = mapG ≫ ((eF ≫ qF) ≫ pInv) := by
          rw [hmapF_eq]
          rfl
    have hF_eq : qF ≫ pInv = qToF := by
      convert hF using 1 ; rfl
    have hF_assoc : (eF ≫ qF) ≫ pInv = eF ≫ qToF := by
      calc
        _ = eF ≫ (qF ≫ pInv) := Category.assoc _ _ _
        _ = eF ≫ qToF := by rw [hF_eq]
    have hmapG_assoc_prefix :
        (uE ≫ eE) ≫ (rE ≫ (sG ≫ (sF ≫ pInv))) =
          (uE ≫ eE) ≫ ((mapG ≫ rF) ≫ (sF ≫ pInv)) :=
      congrArg (fun k => (uE ≫ eE) ≫ k) hmapG_assoc
    have he := (openSheafRestrictionFormulaNatIso U).hom.naturality g
    let bG :
        ((TopCat.Presheaf.pullback (Type u) (openInclusion U)).obj E.presheaf).obj
          (op ((Opens.map (openInclusion U)).obj V)) ⟶
        ((TopCat.Presheaf.pullback (Type u) (openInclusion U)).obj F.presheaf).obj
          (op ((Opens.map (openInclusion U)).obj V)) :=
      ((TopCat.Sheaf.forget (Type u) X ⋙
        openPresheafRestriction (Type u) U).map g).app
        (op ((Opens.map (openInclusion U)).obj V))
    have hunit_map :
        g.hom.app (op V) ≫ uF = uE ≫ bG := by
      have hu :=
        (TopCat.Presheaf.pullbackPushforwardAdjunction
          (Type u) (openInclusion U)).unit.naturality g.hom
      have huV := congrArg (fun k => k.app (op V)) hu
      exact huV
    have heW : mapG ≫ eF =
        ((openSheafRestrictionFormulaNatIso U).hom.app E).app
            (op ((Opens.map (openInclusion U)).obj V)) ≫ bG := by
      convert congrArg
        (fun k => k.app (op ((Opens.map (openInclusion U)).obj V))) he using 1 ; rfl
    have hformula : eE ≫ (mapG ≫ eF) = bG := by
      calc
        _ = eE ≫
            (((openSheafRestrictionFormulaNatIso U).hom.app E).app
              (op ((Opens.map (openInclusion U)).obj V)) ≫ bG) := by
          exact congrArg (fun k => eE ≫ k) heW
        _ = bG := by
          dsimp [eE]
          have hiE :
              ((openSheafRestrictionFormulaNatIso U).inv.app E).app
                  (op ((Opens.map (openInclusion U)).obj V)) ≫
                ((openSheafRestrictionFormulaNatIso U).hom.app E).app
                  (op ((Opens.map (openInclusion U)).obj V)) =
              𝟙 (((TopCat.Presheaf.pullback (Type u) (openInclusion U)).obj
                E.presheaf).obj
                  (op ((Opens.map (openInclusion U)).obj V))) := by
            convert congrArg
              (fun k => k.app (op ((Opens.map (openInclusion U)).obj V)))
              ((openSheafRestrictionFormulaNatIso U).app E).inv_hom_id using 1 ; rfl
          convert congrArg (fun k => k ≫ bG) hiE using 1 <;> rfl
    have hformula_q :
        (eE ≫ (mapG ≫ eF)) ≫ qToF = bG ≫ qToF :=
      congrArg (fun k => k ≫ qToF) hformula
    have hformula_q' : eE ≫ mapG ≫ (eF ≫ qToF) = bG ≫ qToF := by
      calc
        _ = (eE ≫ mapG) ≫ (eF ≫ qToF) :=
          (Category.assoc _ _ _).symm
        _ = ((eE ≫ mapG) ≫ eF) ≫ qToF :=
          (Category.assoc _ _ _).symm
        _ = (eE ≫ (mapG ≫ eF)) ≫ qToF := by
          exact congrArg (fun k => k ≫ qToF) (Category.assoc eE mapG eF)
        _ = bG ≫ qToF := hformula_q
    have hunit_map_q : uE ≫ bG ≫ qToF =
        (g.hom.app (op V) ≫ uF) ≫ qToF := by
      convert (congrArg (fun k => k ≫ qToF) hunit_map).symm using 1 ;
        simp only [Category.assoc]
    have hmapF_assoc_prefix :
        (uE ≫ eE) ≫ ((mapG ≫ rF) ≫ (sF ≫ pInv)) =
          (uE ≫ eE) ≫ (mapG ≫ ((eF ≫ qF) ≫ pInv)) :=
      congrArg (fun k => (uE ≫ eE) ≫ k) hmapF_assoc
    have hF_assoc_prefix :
        (uE ≫ eE) ≫ (mapG ≫ ((eF ≫ qF) ≫ pInv)) =
          (uE ≫ eE) ≫ (mapG ≫ (eF ≫ qToF)) :=
      congrArg (fun k => (uE ≫ eE) ≫ (mapG ≫ k)) hF_assoc
    have hunitF : uF ≫ qToF =
        F.presheaf.germ V ((ConcreteCategory.hom (openInclusion U)) y) hV := by
      simpa [uF, qToF] using
        (TopCat.Presheaf.pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk
          (C := Type u) (f := openInclusion U) (F := F.presheaf)
          (V := op V) (x := y) (hx := hV))
    have hstalk := TopCat.Presheaf.stalkFunctor_map_germ
      (C := Type u) V ((ConcreteCategory.hom (openInclusion U)) y) hV g.hom
    rw [← hassoc1, hassoc2, hmapG_assoc_prefix,
      hmapF_assoc_prefix, hF_assoc_prefix]
    simp only [Category.assoc]
    rw [hformula_q', hunit_map_q]
    simp only [Category.assoc]
    rw [hunitF]
    exact hstalk.symm
  rw [hlhs]

private lemma germ_eqToHom_of_eq {X : TopCat.{u}}
    (F : X.Presheaf (Type u)) {U V : Opens X} (h : U = V)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) (s : F.obj (op U)) :
    (ConcreteCategory.hom (F.germ V x hxV))
        ((ConcreteCategory.hom (eqToHom (congrArg
          (fun Z : Opens X => F.obj (op Z)) h))) s) =
      (ConcreteCategory.hom (F.germ U x hxU)) s := by
  subst V
  rfl

private lemma localConstantPUnitMap_stalk_germ {X : TopCat.{u}}
    (U : Opens X) (F : TopCat.Sheaf (Type u) X)
    (s : F.presheaf.obj (op U)) (y : openSubspace U) :
    (openRestrictionStalkIso U F y).hom
        (StalkMap (localConstantPUnitMap U F s) y
          (constantPresheafStalkMap (X := openSubspace U) PUnit y PUnit.unit)) =
      F.presheaf.germ U ((openInclusion U) y) (by exact y.2) s := by
  dsimp [constantPresheafStalkMap]
  have h1 := stalkMap_germ (localConstantPUnitMap U F s) y
    (U := (⊤ : Opens (openSubspace U)))
    (show y ∈ (⊤ : Opens (openSubspace U)) from Set.mem_univ y) PUnit.unit
  let p : (constantPresheaf (X := openSubspace U) PUnit).obj
      (op (⊤ : Opens (openSubspace U))) := PUnit.unit
  rw [h1]
  dsimp [openRestrictionStalkIso, TopCat.Presheaf.stalkFunctor, Functor.mapIso,
    Iso.trans, Iso.symm]
  have h2 := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := Type u) (⊤ : Opens (openSubspace U)) y
    (show y ∈ (⊤ : Opens (openSubspace U)) from Set.mem_univ y)
    ((openSheafRestrictionFormulaNatIso U).app F).hom
    ((ConcreteCategory.hom ((localConstantPUnitMap U F s).app
      (op (⊤ : Opens (openSubspace U))))) p)
  change (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkPullbackIso (Type u) (openInclusion U)
        F.presheaf y).symm.hom))
      ((ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor (Type u) y).map
          ((openSheafRestrictionFormulaNatIso U).app F).hom))
        ((ConcreteCategory.hom
          (((openSheafRestriction (Type u) U ⋙
            TopCat.Sheaf.forget (Type u) (openSubspace U)).obj F).germ
              (⊤ : Opens (openSubspace U)) y (Set.mem_univ y)))
          ((ConcreteCategory.hom ((localConstantPUnitMap U F s).app
            (op (⊤ : Opens (openSubspace U))))) p))) = _
  rw [h2]
  change (TopCat.Presheaf.stalkPullbackIso (Type u) (openInclusion U)
      F.presheaf y).symm.hom
      (((openPresheafRestriction (Type u) U).obj F.presheaf).germ
        (⊤ : Opens (openSubspace U)) y (Set.mem_univ y)
        (((openSheafRestrictionFormulaNatIso U).app F).hom.app
          (op (⊤ : Opens (openSubspace U)))
          (((localConstantPUnitMap U F s).app
            (op (⊤ : Opens (openSubspace U)))) p))) = _
  dsimp [openPresheafRestriction, TopCat.Presheaf.stalkPullbackIso]
  have h3 := TopCat.Presheaf.germ_stalkPullbackInv
    (C := Type u) (openInclusion U) F.presheaf y
      (⊤ : Opens (openSubspace U)) (Set.mem_univ y)
  have h4 := congrArg (fun q => ConcreteCategory.hom q) h3
  have h5 := congrArg (fun q =>
      q ((ConcreteCategory.hom (((openSheafRestrictionFormulaNatIso U).app F).hom.app
        (op (⊤ : Opens (openSubspace U)))))
        ((ConcreteCategory.hom ((localConstantPUnitMap U F s).app
          (op (⊤ : Opens (openSubspace U))))) p))) h4
  exact h5.trans (by
    let e0 := (openSheafRestrictionFormulaNatIso U).app F
    let Vtop : Opens (openSubspace U) := ⊤
    let r := TopCat.Presheaf.pullbackObjObjOfImageOpen
      (openInclusion U) F.presheaf Vtop
      (U.isOpenEmbedding.isOpenMap Vtop Vtop.2)
    have hWU :
        (⟨(openInclusion U) '' Vtop,
          (U.isOpenEmbedding.isOpenMap Vtop Vtop.2)⟩ : Opens X) = U := by
      ext x
      constructor
      · rintro ⟨z, -, rfl⟩
        exact z.property
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have htop :
        let pV : (constantPresheaf (X := openSubspace U) PUnit).obj
            (op Vtop) := PUnit.unit
        (ConcreteCategory.hom (e0.hom.app (op Vtop)))
            ((ConcreteCategory.hom ((localConstantPUnitMap U F s).app
              (op Vtop))) pV) =
          (ConcreteCategory.hom (r.inv))
            ((ConcreteCategory.hom (eqToHom (congrArg
              (fun Z : Opens X => F.presheaf.obj (op Z)) hWU.symm))) s) := by
      dsimp [localConstantPUnitMap, e0, Vtop]
      have hmap := (((openSheafRestriction (Type u) U).obj F).presheaf).map_id
        (op (⊤ : Opens (openSubspace U)))
      rw [hmap]
      change (ConcreteCategory.hom (e0.app (op Vtop)).hom)
          ((ConcreteCategory.hom (e0.app (op Vtop)).inv)
            ((ConcreteCategory.hom r.inv)
              ((ConcreteCategory.hom (eqToHom (congrArg
                (fun Z : Opens X => F.presheaf.obj (op Z)) hWU.symm))) s))) = _
      exact Iso.inv_hom_id_apply (e0.app (op Vtop))
        ((ConcreteCategory.hom r.inv)
          ((ConcreteCategory.hom (eqToHom (congrArg
            (fun Z : Opens X => F.presheaf.obj (op Z)) hWU.symm))) s))
    rw [htop]
    let x : CostructuredArrow (Opens.map (openInclusion U)).op (op Vtop) :=
      CostructuredArrow.mk
        (@homOfLE _ _ _ ((Opens.map (openInclusion U)).obj
          (⟨(openInclusion U) '' Vtop,
            (U.isOpenEmbedding.isOpenMap Vtop Vtop.2)⟩ : Opens X))
          (Set.image_preimage.le_u_l _)).op
    have hx : IsTerminal x :=
      { lift := fun q ↦ by
          fapply CostructuredArrow.homMk
          · change op (unop _) ⟶
              op (⟨(openInclusion U) '' Vtop,
                (U.isOpenEmbedding.isOpenMap Vtop Vtop.2)⟩ : Opens X)
            refine (homOfLE ?_).op
            apply (Set.image_mono q.pt.hom.unop.le).trans
            exact Set.image_preimage.l_u_le (SetLike.coe q.pt.left.unop)
          · simp [eq_iff_true_of_subsingleton] }
    have hr0 :=
      Limits.IsColimit.comp_coconePointUniqueUpToIso_inv
        ((Opens.map (openInclusion U)).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
          F.presheaf (op Vtop))
        (colimitOfDiagramTerminal hx _) x
    have hxx : hx.from x = 𝟙 x := by
      apply hx.hom_ext
    dsimp [Limits.coconeOfDiagramTerminal] at hr0
    rw [hxx] at hr0
    have hproj :=
      (CostructuredArrow.proj (Opens.map (openInclusion U)).op (op Vtop)).map_id x
    rw [hproj, F.presheaf.map_id] at hr0
    have hr1 :
        r.inv =
          (((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u)
            (openInclusion U)).unit.app F.presheaf).app x.left ≫
            ((TopCat.Presheaf.pullback (Type u) (openInclusion U)).obj
              F.presheaf).map x.hom) := by
      dsimp [r, openPresheafRestriction_obj_iso]
      rw [Category.id_comp] at hr0
      have hOp :
          (⟨(openInclusion U) '' Vtop,
            (U.isOpenEmbedding.isOpenMap Vtop Vtop.2)⟩ : Opens X) = x.left.unop := by
        ext z
        rfl
      cases hOp
      convert hr0 using 1 ;
        simp [x, TopCat.Presheaf.pullbackObjObjOfImageOpen,
          CostructuredArrow.proj, CostructuredArrow.mk, Comma.fst, Functor.fromPUnit,
          TopCat.Presheaf.pullback, Functor.lan,
          Functor.lanUnit, Functor.LeftExtension.coconeAt,
          Functor.LeftExtension.mk,
          TopCat.Presheaf.pullbackPushforwardAdjunction,
          Functor.lanAdjunction_unit] ;
        try { exact Iff.rfl }
    rw [hr1]
    rw [ConcreteCategory.comp_apply]
    have hgerm :=
      TopCat.Presheaf.pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
        (C := Type u) (openInclusion U) F.presheaf Vtop y
        (show y ∈ Vtop from Set.mem_univ y) x.left.unop x.hom.unop.le
    have hgerm_apply := congrArg (fun q =>
        (ConcreteCategory.hom q)
          ((ConcreteCategory.hom (eqToHom (congrArg
            (fun Z : Opens X => F.presheaf.obj (op Z)) hWU.symm))) s)) hgerm
    rw [ConcreteCategory.comp_apply] at hgerm_apply
    rw [ConcreteCategory.comp_apply] at hgerm_apply
    have hleft :
        x.left.unop =
          (⟨(openInclusion U) '' Vtop,
            (U.isOpenEmbedding.isOpenMap Vtop Vtop.2)⟩ : Opens X) := by
      rfl
    have hxhom :
        x.hom =
          (@homOfLE _ _ _ ((Opens.map (openInclusion U)).obj
            (⟨(openInclusion U) '' Vtop,
              (U.isOpenEmbedding.isOpenMap Vtop Vtop.2)⟩ : Opens X))
            (Set.image_preimage.le_u_l _)).op := by
      rfl
    rw [← hxhom] at hgerm_apply
    have htransport := germ_eqToHom_of_eq F.presheaf hWU.symm
      ((openInclusion U) y) (by exact y.2)
      (by exact ⟨y, trivial, rfl⟩) s
    simpa [x, Vtop] using (hgerm_apply.trans htransport))

/-! ## The coproducts and finite coequalizer presentations in the source -/

/-- The coproduct of extensions by the empty set of constant sheaves on opens.

The `U` and `S` arguments are allowed to be indexed by an arbitrary type so
that the same construction can be used for the source's arbitrary coproduct
and its finite coproducts.
-/
noncomputable def openExtensionCoproduct {X : TopCat.{u}} (I : Type u)
    (U : I → Opens X) (S : I → Type u) : TopCat.Sheaf (Type u) X :=
  letI : HasColimitsOfSize.{u, u} (TopCat.Sheaf (Type u) X) :=
    Formalization.Books.Sheaves.Unit22.sheaf_has_colimits (X := X)
  colimit (Discrete.functor fun i =>
    (Formalization.Books.Sheaves.Unit22.openSetSheafExtensionByEmpty (U i)).obj
      (Formalization.Books.Sheaves.Unit07.constantSheaf
        (Formalization.Books.Sheaves.Unit22.openSubspace (U i)) (S i)))

/-- The set of quasi-compact open subsets of a topological space. -/
def quasiCompactOpenBasis (X : TopCat.{u}) : Set (Opens X) :=
  {U : Opens X | IsCompact (U : Set X)}

/-- A finite coequalizer presentation by extensions of finite constant sheaves.

The two maps are retained explicitly, together with the colimit cocone, so
the displayed coequalizer in the source is available as a usable categorical
interface rather than only as an informal predicate.
-/
structure FiniteOpenCoequalizerPresentation
    {X : TopCat.{u}} (B : Set (Opens X))
    (F : TopCat.Sheaf (Type u) X) where
  m : ℕ
  n : ℕ
  U : Fin n → Opens X
  V : Fin m → Opens X
  U_mem : ∀ a, U a ∈ B
  V_mem : ∀ b, V b ∈ B
  S : Fin n → Type u
  T : Fin m → Type u
  finiteS : ∀ a, Finite (S a)
  finiteT : ∀ b, Finite (T b)
  left :
    openExtensionCoproduct (X := X) (ULift.{u} (Fin m))
        (fun i => V i.down) (fun i => T i.down) ⟶
      openExtensionCoproduct (X := X) (ULift.{u} (Fin n))
        (fun i => U i.down) (fun i => S i.down)
  right :
    openExtensionCoproduct (X := X) (ULift.{u} (Fin m))
        (fun i => V i.down) (fun i => T i.down) ⟶
      openExtensionCoproduct (X := X) (ULift.{u} (Fin n))
        (fun i => U i.down) (fun i => S i.down)
  augmentation :
    openExtensionCoproduct (X := X) (ULift.{u} (Fin n))
        (fun i => U i.down) (fun i => S i.down) ⟶ F
  relation_condition : left ≫ augmentation = right ≫ augmentation
  isColimit : IsColimit (Cofork.ofπ augmentation relation_condition)

/-- A sheaf has the finite coequalizer presentation used in the source. -/
def IsFiniteOpenCoequalizerSheaf {X : TopCat.{u}} (B : Set (Opens X))
    (F : TopCat.Sheaf (Type u) X) : Prop :=
  Nonempty (FiniteOpenCoequalizerPresentation B F)

/-- A filtered colimit presentation whose stages have the source's finite form. -/
structure FilteredFiniteOpenCoequalizerColimit
    {X : TopCat.{u}} (B : Set (Opens X))
    (F : TopCat.Sheaf (Type u) X) where
  index : Type u
  [indexCategory : Category index]
  [indexFiltered : IsFiltered index]
  diagram : index ⥤ TopCat.Sheaf (Type u) X
  stagesInPresentation : ∀ i, IsFiniteOpenCoequalizerSheaf B (diagram.obj i)
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  targetIso : cocone.pt ≅ F

/-! ## The four assertions in the source section -/

/-- Every sheaf of sets is covered by a coproduct of extended finite constants.

The source proof chooses singleton constants, but its statement permits an
arbitrary finite set at each basis open, which is recorded here exactly.
-/
theorem lemma_surjection {X : TopCat.{u}} (B : Set (Opens X))
    (hB : Opens.IsBasis B) (F : TopCat.Sheaf (Type u) X) :
    ∃ (I : Type u) (U : I → Opens X) (S : I → Type u),
      (∀ i, U i ∈ B) ∧ (∀ i, Finite (S i)) ∧
        ∃ φ : openExtensionCoproduct (X := X) I U S ⟶ F,
        SheafSurjective φ := by
  classical
  let I := Σ x : X, F.presheaf.stalk x
  have hlocal : ∀ i : I, ∃ U : Opens X, ∃ hxi : i.1 ∈ U, U ∈ B ∧
      ∃ s : F.presheaf.obj (op U),
        F.presheaf.germ U i.1 hxi s = i.2 := by
    intro i
    rcases TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB F.presheaf i.1 i.2 with
      ⟨U, hxi, hUB, s, hs⟩
    exact ⟨U, hxi, hUB, s, hs⟩
  choose U hxi hUB s hs using hlocal
  refine ⟨I, U, fun _ => PUnit, ?_, ?_, ?_⟩
  · intro i
    exact hUB i
  · intro i
    infer_instance
  · let _ : HasColimitsOfSize.{u, u} (TopCat.Sheaf (Type u) X) :=
      Formalization.Books.Sheaves.Unit22.sheaf_has_colimits (X := X)
    let q : ∀ i : I,
        constantSheaf (openSubspace (U i)) PUnit ⟶
          (openSheafRestriction (Type u) (U i)).obj F :=
      fun i => localSectionHom (U i) F (s i)
    let c : Cocone (Discrete.functor fun i =>
        (openSetSheafExtensionByEmpty (U i)).obj
          (constantSheaf (openSubspace (U i)) PUnit)) :=
      Cocone.mk F {
        app := fun j =>
          (openSetSheafExtensionHomEquiv (U j.as)
            (constantSheaf (openSubspace (U j.as)) PUnit) F).symm (q j.as)
        naturality := by
          intro j k f
          rcases j with ⟨j⟩
          rcases k with ⟨k⟩
          have h : j = k := f.down.down
          subst k
          simp }
    let φ : openExtensionCoproduct I U (fun _ => PUnit) ⟶ F := by
      exact colimit.desc _ c
    refine ⟨φ, ?_⟩
    rw [sheaf_surjective_iff_stalk_surjective]
    intro x y
    let i : I := ⟨x, y⟩
    let E := (openSetSheafExtensionByEmpty (U i)).obj
      (constantSheaf (openSubspace (U i)) PUnit)
    let a : E ⟶ F := c.ι.app (Discrete.mk i)
    have ha : (openSetSheafExtensionHomEquiv (U i)
        (constantSheaf (openSubspace (U i)) PUnit) F) a = q i := by
      exact Equiv.apply_symm_apply _ _
    let adj := openSheafExtensionAdjunction (Type u) (U i)
    have hunit := adj.homEquiv_unit (f := a)
    let u := (adj.unit.app (constantSheaf (openSubspace (U i)) PUnit)).hom
    have hqa : u ≫ ((openSheafRestriction (Type u) (U i)).map a).hom =
        (q i).hom := by
      have hh := congrArg (fun k => k.hom) hunit
      rw [ha] at hh
      exact hh.symm
    let y' : openSubspace (U i) := ⟨x, hxi i⟩
    let z : (constantSheaf (openSubspace (U i)) PUnit).presheaf.stalk y' :=
      constantSheafStalkMap (X := openSubspace (U i)) PUnit y'
        (constantPresheafStalkMap (X := openSubspace (U i)) PUnit y' PUnit.unit)
    let z' := ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor (Type u) y').map u) z
    let zE : ((openSheafRestriction (Type u) (U i)).obj E).presheaf.stalk y' := by
      exact z'
    let e := ConcreteCategory.hom (openRestrictionStalkIso (U i) E y').hom zE
    let e0 : E.presheaf.stalk x := by
      exact e
    let j : E ⟶ openExtensionCoproduct I U (fun _ => PUnit) :=
      colimit.ι (Discrete.functor fun k =>
        (openSetSheafExtensionByEmpty (U k)).obj
          (constantSheaf (openSubspace (U k)) PUnit)) (Discrete.mk i)
    refine ⟨ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map j.hom) e0, ?_⟩
    have hj : j ≫ φ = a := by
      dsimp [j, a, φ, E]
      exact colimit.ι_desc c (Discrete.mk i)
    change ConcreteCategory.hom
        (((TopCat.Presheaf.stalkFunctor (Type u) x).map j.hom) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map φ.hom)) e0 = y
    rw [← Functor.map_comp]
    have hj' : j.hom ≫ φ.hom = a.hom := by
      change (j ≫ φ).hom = a.hom
      exact congrArg (fun k => k.hom) hj
    rw [hj']
    have hqa_stalk := congrArg
      (fun k => ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor (Type u) y').map k) z) hqa
    dsimp [e0]
    have hn := openRestrictionStalkIso_naturality (U i) a y' e
    have htarget :
        (ConcreteCategory.hom
          (StalkMap a.hom ((ConcreteCategory.hom (openInclusion (U i))) y'))) e = y := by
      rw [← hn]
      dsimp [e]
      have he_inv := Iso.hom_inv_id_apply
        (openRestrictionStalkIso (U i) E y') zE
      have hlocal := localConstantPUnitMap_stalk_germ
        (U i) F (s i) y'
      have hcomp := congrArg
        (fun w => (ConcreteCategory.hom (openRestrictionStalkIso (U i) F y').hom)
          ((ConcreteCategory.hom
            (StalkMap ((openSheafRestriction (Type u) (U i)).map a).hom y')) w)) he_inv
      have hmid :
          (ConcreteCategory.hom (openRestrictionStalkIso (U i) F y').hom)
            ((ConcreteCategory.hom
              (StalkMap ((openSheafRestriction (Type u) (U i)).map a).hom y')) zE) = y := by
        have hqa_elem :
            (ConcreteCategory.hom
              (StalkMap ((openSheafRestriction (Type u) (U i)).map a).hom y')) zE =
              (ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor (Type u) y').map (q i).hom)) z := by
          have hh := hqa_stalk
          rw [Functor.map_comp] at hh
          have hcomp_apply :
              (ConcreteCategory.hom
                (((TopCat.Presheaf.stalkFunctor (Type u) y').map u) ≫
                  ((TopCat.Presheaf.stalkFunctor (Type u) y').map
                    ((openSheafRestriction (Type u) (U i)).map a).hom))) z =
                (ConcreteCategory.hom
                  ((TopCat.Presheaf.stalkFunctor (Type u) y').map
                    ((openSheafRestriction (Type u) (U i)).map a).hom))
                  ((ConcreteCategory.hom
                    ((TopCat.Presheaf.stalkFunctor (Type u) y').map u)) z) := by
            rfl
          rw [hcomp_apply] at hh
          change @Eq (TopCat.Presheaf.stalk
            ((openSheafRestriction (Type u) (U i)).obj F).presheaf y') _ _
          exact hh
        have hq_local :
            (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor (Type u) y').map (q i).hom)) z =
              (ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor (Type u) y').map
                  (localConstantPUnitMap (U i) F (s i))))
                (constantPresheafStalkMap (X := openSubspace (U i)) PUnit y' PUnit.unit) := by
          dsimp [q, localSectionHom]
          change (ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor (Type u) y').map
              (constantSheafPUnitToConstantPresheaf ≫
                localConstantPUnitMap (U i) F (s i)))) z = _
          rw [Functor.map_comp]
          change (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor (Type u) y').map
                (localConstantPUnitMap (U i) F (s i))))
            ((ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor (Type u) y').map
                constantSheafPUnitToConstantPresheaf)) z) = _
          have hA :
              (ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor (Type u) y').map
                  constantSheafPUnitToConstantPresheaf)) z =
                constantPresheafStalkMap (X := openSubspace (U i)) PUnit y' PUnit.unit := by
            rcases (constantPresheafStalkMap_bijective
              (X := openSubspace (U i)) PUnit y').2
              ((ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor (Type u) y').map
                  constantSheafPUnitToConstantPresheaf)) z) with ⟨a, ha⟩
            rcases (constantPresheafStalkMap_bijective
              (X := openSubspace (U i)) PUnit y').2
              (constantPresheafStalkMap (X := openSubspace (U i)) PUnit y' PUnit.unit) with
              ⟨b, hb⟩
            cases a
            cases b
            exact ha.symm.trans hb
          rw [hA]
          rfl
        have hq_local_iso := congrArg
          (fun w => (ConcreteCategory.hom (openRestrictionStalkIso (U i) F y').hom) w)
          hq_local
        have hlocal' :
            (ConcreteCategory.hom (openRestrictionStalkIso (U i) F y').hom)
              ((ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor (Type u) y').map
                  (localConstantPUnitMap (U i) F (s i))))
                (constantPresheafStalkMap (X := openSubspace (U i)) PUnit y' PUnit.unit)) =
              (ConcreteCategory.hom (F.presheaf.germ (U i)
                ((ConcreteCategory.hom (openInclusion (U i))) y') (by exact y'.2))) (s i) := by
          exact hlocal
        have hsy :
            (ConcreteCategory.hom (F.presheaf.germ (U i)
              ((ConcreteCategory.hom (openInclusion (U i))) y') (by exact y'.2))) (s i) = y := by
          exact hs i
        have hmid0 :
            (ConcreteCategory.hom (openRestrictionStalkIso (U i) F y').hom)
                ((ConcreteCategory.hom
                  (StalkMap ((openSheafRestriction (Type u) (U i)).map a).hom y')) zE) =
              (ConcreteCategory.hom (F.presheaf.germ (U i)
                ((ConcreteCategory.hom (openInclusion (U i))) y') (by exact y'.2))) (s i) := by
          calc
          _ = (ConcreteCategory.hom (openRestrictionStalkIso (U i) F y').hom)
              ((ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor (Type u) y').map (q i).hom)) z) := by
            exact congrArg
              (fun w => (ConcreteCategory.hom (openRestrictionStalkIso (U i) F y').hom) w)
              hqa_elem
          _ = (ConcreteCategory.hom (openRestrictionStalkIso (U i) F y').hom)
              ((ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor (Type u) y').map
                  (localConstantPUnitMap (U i) F (s i))))
                (constantPresheafStalkMap (X := openSubspace (U i)) PUnit y' PUnit.unit)) :=
            hq_local_iso
          _ = (ConcreteCategory.hom (F.presheaf.germ (U i)
              ((ConcreteCategory.hom (openInclusion (U i))) y') (by exact y'.2))) (s i) :=
            hlocal'
        convert hmid0.trans hsy using 1
      exact hcomp.trans hmid
    have hpoint : (ConcreteCategory.hom (openInclusion (U i))) y' = x := rfl
    convert htarget using 1
    cases hpoint
    rfl

/-- Every sheaf is a filtered colimit of finite coequalizer presentations. -/
/-
Proof roadmap (the missing boundary is the finite-support/coequalizer construction).

1. Apply `lemma_surjection B hB F`, writing its source as `F₀` and its
   locally-surjective map as `q : F₀ ⟶ F`.  By
   `sheaf_epi_iff_surjective` (Sheaves/Unit16/ExactnessAndPoints.lean), `q`
   is epi.  After the focused import `Mathlib.CategoryTheory.Sites.RegularEpi`,
   the regular-epi instance for type-valued sheaves makes it an
   `EffectiveEpi`.  Form its kernel pair `K := pullback q q`; then
   `isColimitCoforkOfEffectiveEpi q _ (pullbackIsPullback q q)` identifies
   `F` as the coequalizer of `pullback.fst q q` and `pullback.snd q q`.
   Apply `lemma_surjection B hB K` and compose the resulting epi `r : F₁ ⟶ K`
   with these projections.  A small categorical helper is needed here:
   precomposing both legs of a coequalizer by an epi is again a coequalizer
   (prove the universal property by `cancel_epi r`).  This gives an arbitrary
   presentation `F₁ ⇉ F₀ ⟶ F` by `openExtensionCoproduct`s.

2. Add the local finite-subcoproduct API before this theorem.  For a finite
   subset `A₀ : Finset I`, define the subcoproduct indexed by
   `{a // a ∈ A₀}` and its canonical map to `openExtensionCoproduct I U S`.
   Provide (a) an `openExtensionCoproductReindexIso` for an equivalence of
   index types and (b) injectivity on sections of the maps for
   `A₀ ⊆ A₁`.  The latter is what permits the finite-subcoproduct diagram to
   use the following result after proving, by the coproduct universal
   property, that this diagram has colimit the full coproduct:
   `directedColimitSectionsMap_bijective_of_quasiCompact_of_injective`
   (Sheaves/Unit29/Infrastructure.lean).  Instantiate that result at
   universe `v := u`, at each `V b`, with quasi-compactness
   `hB_quasiCompact (V b) (V_mem b)`.  Do not apply it to an arbitrary
   filtered category: its interface specifically expects a directed
   preorder with injective transitions.  Prove transition injectivity on
   stalks using `sheaf_injective_iff_stalk_injective`,
   `sheafColimitStalkIso`, and the evident inclusion of the corresponding
   finite sigma types.

3. Package the resulting factorization as a helper with the following
   boundary: for a morphism between two arbitrary `openExtensionCoproduct`s
   and `B₀ : Finset J`, there are `A₀ : Finset I` and a morphism between the
   two finite subcoproducts whose composite with the target inclusion is the
   restriction of the original morphism.  To prove it, use
   `openSetSheafExtensionHomEquiv`
   (Sheaves/Unit31/Infrastructure.lean) on every `b ∈ B₀`.  A leg is then a
   finite family (indexed by the finite type `T b`) of sections over `V b`;
   the bijectivity from step 2 descends every section, and directedness plus
   finiteness of `B₀` and all `T b` supplies one common `A₀`.  Apply this
   helper to both parallel arrows and enlarge the two supports by union.

4. Define `FiniteSubpresentationIndex` to consist of finite supports
   `A₀, B₀` together with factorizations of both arrows.  Order it by support
   inclusion (factorizations are unique because the inclusions are
   sectionwise injective).  The empty supports give an object and unions give
   upper bounds, hence its thin category is filtered.  At an index take the
   coequalizer of the two finite factorizations.  Reindex the two finite
   support types with `Fintype.equivFin` followed by the appropriate
   `Equiv.ulift` equivalence (so the index is `ULift.{u} (Fin n)` exactly as in
   `FiniteOpenCoequalizerPresentation`) and use
   `coequalizerIsCoequalizer` to fill `isColimit`; this proves
   `stagesInPresentation` without changing the definition above.

5. The final missing helper is the universal-property statement that the
   cocone from these finite coequalizers to the arbitrary coequalizer `F` is
   colimiting.  Construct a map out of `F` by first gluing the compatible
   maps out of all finite target subcoproducts; every target generator occurs
   at the stage `(A₀, ∅)`, and every source relation occurs after step 3 at a
   stage containing its finite support.  Uniqueness reduces in the same way
   to finite supports.  Assemble `FilteredFiniteOpenCoequalizerColimit` with
   this index and diagram, cocone point `F`, this `IsColimit`, and
   `targetIso := Iso.refl F`.

Known dead end: `lemma_surjection` plus `sheaf_epi_iff_surjective` only gives
the arbitrary kernel-pair coequalizer.  It cannot produce the required finite
stages until the quasi-compact finite-support helper in steps 2--3 exists.
-/
theorem lemma_filtered_colimit_constructibles {X : TopCat.{u}}
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hB_quasiCompact : ∀ U : Opens X, U ∈ B → IsCompact (U : Set X))
    (F : TopCat.Sheaf (Type u) X) :
    Nonempty (FilteredFiniteOpenCoequalizerColimit B F) := by
  sorry

/-- A finite coequalizer presentation descends from a spectral space to a
finite sober space, with finite-stalk sheaf pullback. -/
/-
Proof roadmap (the missing boundary is descent of a finite presentation, not
the existence of the inverse-limit presentation).

1. Choose `P : FiniteOpenCoequalizerPresentation (quasiCompactOpenBasis X) F`
   from `hF`, and choose
   `D : DirectedFiniteSoberPresentation (X : Type u)` using
   `spectralSpace_iff_directed_inverse_limit_finite_sober`
   (Topology/Unit23/SpectralSpaces.lean).  Install `D.preorder`, `D.directed`,
   and `D.nonempty`.  Add the focused import
   `Formalization.Books.Topology.Unit24.LimitsOfSpectralSpaces`.  For the
   diagram `D.diagram : D.indexᵒᵖ ⥤ TopCat.{u}`, build
   `IsSpectralDiagram D.diagram` using `spectralSpace_of_finite_sober` on
   objects and `isSpectralMap_of_continuous_of_finite_sober` on transitions;
   then `spectralSpace_of_inverseLimit_spectralDiagram` supplies spectral
   projections.

2. The limit in `D` is only homeomorphic to `X`.  Set
   `e := TopCat.isoOfHomeo D.homeomorph` and first transport `P` to the literal
   limit along `e.inv`.  This requires a local
   `FiniteOpenCoequalizerPresentation.transportIso` helper.  Its open sets
   are transported by the homeomorphism, its two coproduct objects use the
   open-extension base-change iso from step 3, and its coequalizer proof is
   transported by `IsColimit.ofIsoColimit`.  At the end the required map is
   `f := e.hom ≫ limit.π D.diagram i`; its spectrality is
   `(spectralSpace_of_inverseLimit_spectralDiagram _ _).2 i` composed with
   `D.homeomorph.isProperMap.isSpectralMap` via `IsSpectralMap.comp`.

3. Add the essential sheaf API which is currently absent:
   `pullbackOpenExtensionCoproductIso`.  For `g : X' ⟶ X`, a finite family
   `U : Fin n → Opens X`, and `S : Fin n → Type u`, it must identify
   the pullback of
   `openExtensionCoproduct (ULift.{u} (Fin n))
     (fun a => U a.down) (fun a => S a.down)` with the analogous coproduct on
   the inverse-image opens `(Opens.map g).obj (U a)`.  Build it from the
   extension-by-empty
   adjunction `openSetSheafExtensionHomEquiv`, the pullback composition iso
   `pullbackSheafCompIso` (Sheaves/Unit21/ContinuousMaps.lean), and
   preservation of the finite coproduct by the left adjoint `pullbackSheaf`.
   No such base-change declaration is presently available.

4. Descend the finitely many quasi-compact opens `P.U a` and `P.V b`.
   Transport them to the literal limit and apply
   `inverseLimit_quasiCompactOpen_descends`
   (Topology/Unit24/LimitsOfSpectralSpaces.lean).  Use cofilteredness and the
   finiteness of `Fin P.n` and `Fin P.m` to replace the individual stages by
   one `i : D.indexᵒᵖ`; pull the descended opens to that common stage.  Record
   equalities saying their inverse images under `limit.π D.diagram i` are
   exactly the opens in the transported presentation.

5. Descend the two arrows after the opens.  Introduce a reusable
   `openExtensionCoproductHomEquiv`: by
   `openSetSheafExtensionHomEquiv`, `constantTypeSheafIso`
   (Sheaves/Unit31/Infrastructure.lean), and
   `CategoryTheory.constantSheafΓAdj`
   (Mathlib/CategoryTheory/Sites/GlobalSections.lean), a map out of the finite source
   coproduct is equivalent to the family, for `b : Fin P.m`, of functions
   `P.T b` into sections of the target coproduct over `P.V b`.  For the
   target coproduct at stage `i`, use
   `computePullbackToSpectralLimitSections`
   (Sheaves/Unit29/Infrastructure.lean).  Its source is a filtered colimit
   over refinements `j ⟶ i`; `Types.jointly_surjective` descends each section.
   Finiteness of `Fin P.m` and of every `P.T b` gives one common refinement
   for every section in both arrows.  Reassemble the descended functions
   with `openExtensionCoproductHomEquiv.symm` to obtain `left_i` and
   `right_i`.

6. Let `G := coequalizer left_i right_i`.  Use
   `coequalizerIsCoequalizer` for its presentation.  The iso in step 3,
   preservation of this coequalizer by the left adjoint `pullbackSheaf`, and
   `P.isColimit.coconePointUniqueUpToIso` identify the pullback of `G` with
   the transported `F`; compose with the equivalence from step 2 to obtain
   `Nonempty ((pullbackSheaf f).obj G ≅ F)`.

7. Prove the stalks of `G` finite through one local helper:
   `openExtensionCoproduct_finite_stalk` for a finite index and finite values.
   Use `sheafColimitStalkIso` (Sheaves/Unit29/Infrastructure.lean),
   `openSetSheafExtension_stalk_empty`/`_stalk_iso`
   (Sheaves/Unit31/Infrastructure.lean), and `constantSheafStalkEquiv`
   (Sheaves/Unit11/Stalks.lean).  The coequalizer projection to `G` is epi,
   hence stalk-surjective by `sheaf_epi_iff_surjective` and
   `sheaf_surjective_iff_stalk_surjective`; `Finite.of_surjective` then gives
   `Finite (G.presheaf.stalk y)`.

Known dead end: `computePullbackToSpectralLimitSections` descends individual
sections on a literal inverse limit; it does not by itself descend a sheaf
morphism, a finite coproduct, or data across `D.homeomorph`.  Steps 2--5 are
therefore required before it can be used.
-/
theorem lemma_constructible_comes_from_finite {X : TopCat.{u}}
    [SpectralSpace (X : Type u)]
    (F : TopCat.Sheaf (Type u) X)
    (hF : IsFiniteOpenCoequalizerSheaf (quasiCompactOpenBasis X) F) :
    ∃ (Y : TopCat.{u}),
      Finite (Y : Type u) ∧ QuasiSober (Y : Type u) ∧ T0Space (Y : Type u) ∧
        ∃ (f : X ⟶ Y), IsSpectralMap f ∧
          ∃ (G : TopCat.Sheaf (Type u) Y),
            (∀ y : Y, Finite (G.presheaf.stalk y)) ∧
              Nonempty ((pullbackSheaf f).obj G ≅ F) := by
  sorry

/-- Constructible-closed subsets, i.e. closed subsets for the constructible
topology of a spectral space. -/
abbrev IsConstructibleClosed {X : TopCat.{u}} (Z : Set X) : Prop :=
  @IsClosed (X : Type u) (constructibleTopology (X : Type u)) Z

/-- A finite product of pushforwards of constant sheaves from subspaces. -/
noncomputable def constructibleClosedPushforwardProduct
    {X : TopCat.{u}} (n : ℕ) (Z : Fin n → Set X)
    (S : Fin n → Type u) : TopCat.Sheaf (Type u) X :=
  limit (Discrete.functor fun i =>
    (pushforwardSheaf (Formalization.Books.Sheaves.Unit22.closedInclusion (Z i))).obj
      (Formalization.Books.Sheaves.Unit07.constantSheaf
        (Formalization.Books.Sheaves.Unit22.closedSubspace (Z i)) (S i)))

/-- A sheaf with a finite presentation embeds, up to isomorphism, into a
finite product of constant pushforwards from constructible-closed subsets. -/
/-
Proof roadmap (the missing boundary is a mono/product decomposition and its
closed-subspace base change).

1. Apply `lemma_constructible_comes_from_finite F hF` and install the returned
   `Finite Y`, `QuasiSober Y`, and `T0Space Y` instances.  Write the result as
   `f : X ⟶ Y`, `hf : IsSpectralMap f`, a finite-stalk sheaf `G`, and
   `eFG : (pullbackSheaf f).obj G ≅ F`.  Choose `Fintype Y := Fintype.ofFinite Y`,
   put `n := Fintype.card Y`, and enumerate the points with
   `(Fintype.equivFin Y).symm : Fin n → Y`.

2. First prove a finite-space helper returning an actual mono.  For `y : Y`,
   the component
   `(stalkSkyscraperSheafAdjunction y).unit.app G` maps `G` to the
   skyscraper sheaf with value `G.presheaf.stalk y`
   (Mathlib/Topology/Sheaves/Skyscraper.lean).  Use these as the legs of a
   cone and `limit.lift` to obtain
   `G ⟶ limit (Discrete.functor fun y =>
     skyscraperSheaf y (G.presheaf.stalk y))`.
   Prove it mono with `sheaf_mono_iff_injective`
   (Sheaves/Unit16/ExactnessAndPoints.lean): equality after every projection
   says that two sections have equal germs at every point, and
   `TopCat.Presheaf.section_ext` (Mathlib/Topology/Sheaves/Stalks.lean)
   finishes.  Finiteness of each value is exactly the returned stalk
   hypothesis.

3. Add the absent comparison
   `skyscraperSheafClosureIso`.  For a finite sober space and `y : Y`, it
   must identify `skyscraperSheaf y A` with
   `(pushforwardSheaf (closedInclusion (closure {y}))).obj
     (constantSheaf (closedSubspace (closure {y})) A)`.
   Prove it sectionwise: an open meets `closure {y}` iff it contains `y`, and
   every locally constant map from the nonempty open subspace of the
   irreducible space `closure {y}` is constant.  The existing
   `constantSheaf_sections_equiv` (Sheaves/Unit07/Sheaves.lean) and the
   concrete formula for `pushforwardSheaf` provide the two section types.
   Assemble these component isos into a diagram iso and then a limit iso.
   This comparison is not definitionally true and has no current project API.

4. Keep the embedding as a categorical mono while pulling it back.  The
   sheaf pullback preserves finite limits (the instance for
   `Functor.sheafPullback` is in
   Mathlib/CategoryTheory/Sites/Pullback.lean), so `Functor.map_mono` applies;
   `preservesLimitIso` commutes it with the finite discrete product.  Do not
   try to pull back `IsSubsheaf` directly: that predicate is represented by
   an existential `Subfunctor` and currently has no pullback interface.

5. Add the second absent comparison, a closed-embedding base-change iso.  For
   `Z : Set Y` closed and `A : Type u`, its exact target is
   `(pullbackSheaf f).obj
       ((pushforwardSheaf (closedInclusion Z)).obj
         (constantSheaf (closedSubspace Z) A)) ≅
     (pushforwardSheaf (closedInclusion (f ⁻¹' Z))).obj
       (constantSheaf (closedSubspace (f ⁻¹' Z)) A)`.
   Construct it from the cartesian square of subtype inclusions, the
   pullback/pushforward adjunction, and a new `pullbackConstantSheafIso`
   (obtained from `constantTypeSheafIso` and preservation of coproducts and
   the terminal sheaf by pullback); no Beck--Chevalley declaration for this
   square exists in the imported API.
   Apply it to `Z = closure {y}` and assemble the finite component isos to
   identify the pulled-back product with
   `constructibleClosedPushforwardProduct n
     (fun i => f ⁻¹' closure {(Fintype.equivFin Y).symm i})
     (fun i => G.presheaf.stalk ((Fintype.equivFin Y).symm i))`.

6. For these `Z i`, prove `IsConstructibleClosed (Z i)`.  A subset of the
   finite space `Y` is compact; hence `closure {y}` is constructible (apply
   `IsCompact.isConstructible` to its open complement and take complements).
   Convert this with
   `isConstructible_isOpen_isClosed_constructibleTopology`, and pull the
   closed set back along the constructible-topology continuity supplied by
   `(isSpectralMap_iff_continuous_constructibleTopology hf.continuous).mp hf`
   (Topology/Unit23/SpectralSpaces.lean).  Set `S i` to the corresponding
   stalk; its `Finite` instance is the finite-stalk hypothesis on `G`.

7. Finally add `isSubsheaf_of_mono`: for a sheaf morphism `k : H ⟶ K` with
   `[Mono k]`, take the range of each component of `k.hom` as a `Subfunctor`
   of `K.presheaf`; `presheaf_mono_iff_injective` makes the induced map from
   `H.presheaf` an isomorphism onto that range.  Together with the two sheaf
   conditions this yields `IsSubsheaf H.presheaf K.presheaf`.  Take
   `H := (pullbackSheaf f).obj G`, use `eFG.symm : F ≅ H`, and apply this
   bridge to the mono assembled in steps 2--5.

Known dead ends: the skyscraper/closure comparison and closed-subspace base
change are mathematical constructions, not simplification lemmas; and an
`IsSubsheaf` witness cannot be transported by `Functor.map` without first
replacing it by a mono as in step 4.
-/
theorem lemma_constructible_in_constant {X : TopCat.{u}}
    [SpectralSpace (X : Type u)]
    (F : TopCat.Sheaf (Type u) X)
    (hF : IsFiniteOpenCoequalizerSheaf (quasiCompactOpenBasis X) F) :
    ∃ (n : ℕ) (Z : Fin n → Set X) (S : Fin n → Type u),
      (∀ i, IsConstructibleClosed (Z i)) ∧ (∀ i, Finite (S i)) ∧
        ∃ H : TopCat.Sheaf (Type u) X,
          Nonempty (F ≅ H) ∧
            IsSubsheaf H.presheaf
              (constructibleClosedPushforwardProduct n Z S).presheaf := by
  sorry

end
end Formalization.Books.Modules.Unit19
