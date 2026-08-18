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
  dsimp [openRestrictionStalkIso]
  simp [Category.assoc]

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
  dsimp [openRestrictionStalkIso]
  change (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkPullbackIso (Type u) (openInclusion U)
        F.presheaf y).symm.hom))
      ((ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor (Type u) y).map
          ((openSheafRestrictionFormulaNatIso U).app F).hom))
        (germApply (F := ((openSheafRestriction (Type u) U).obj F).presheaf)
          (⊤ : Opens (openSubspace U)) y (Set.mem_univ y)
          ((ConcreteCategory.hom ((localConstantPUnitMap U F s).app
            (op (⊤ : Opens (openSubspace U))))) p) = _
  have h2 := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := Type u) (⊤ : Opens (openSubspace U)) y
    (show y ∈ (⊤ : Opens (openSubspace U)) from Set.mem_univ y)
    ((openSheafRestrictionFormulaNatIso U).app F).hom
    ((ConcreteCategory.hom ((localConstantPUnitMap U F s).app
      (op (⊤ : Opens (openSubspace U))))) p)
  rw [h2]
  change (ConcreteCategory.hom
      (((openPresheafRestriction (Type u) U).obj F.presheaf).germ
        (⊤ : Opens (openSubspace U)) y (Set.mem_univ y) ≫
        (TopCat.Presheaf.stalkPullbackIso (Type u) (openInclusion U)
          F.presheaf y).symm.hom))
      ((ConcreteCategory.hom (((openSheafRestrictionFormulaNatIso U).app F).hom.app
        (op (⊤ : Opens (openSubspace U)))))
        ((ConcreteCategory.hom ((localConstantPUnitMap U F s).app
        (op (⊤ : Opens (openSubspace U))))) p) = _
  dsimp [openPresheafRestriction, TopCat.Presheaf.stalkPullbackIso]
  have h3 := TopCat.Presheaf.germ_stalkPullbackInv
    (C := Type u) (openInclusion U) F.presheaf y
      (⊤ : Opens (openSubspace U)) (Set.mem_univ y)
  have h4 := congrArg (fun q => ConcreteCategory.hom q) h3
  have h5 := congrArg (fun q => q
      ((ConcreteCategory.hom (((openSheafRestrictionFormulaNatIso U).app F).hom.app
        (op (⊤ : Opens (openSubspace U)))))
        ((ConcreteCategory.hom ((localConstantPUnitMap U F s).app
          (op (⊤ : Opens (openSubspace U))))) p) h4
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
    have hpre : (Opens.map (openInclusion U)).obj U =
        (⊤ : Opens (openSubspace U)) := by
      ext z
      change ((openInclusion U) z ∈ U) ↔ _
      constructor
      · intro _
        trivial
      · intro _
        exact z.property
    simp only [hpre]
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
      convert hr0 using 1 <;>
        simp [x, TopCat.Presheaf.pullbackObjObjOfImageOpen,
          CostructuredArrow.proj, CostructuredArrow.mk, Comma.fst, Functor.fromPUnit,
          openPresheafRestriction, TopCat.Presheaf.pullback, Functor.lan,
          Functor.lanUnit, Functor.LeftExtension.coconeAt,
          Functor.LeftExtension.mk,
          TopCat.Presheaf.pullbackPushforwardAdjunction,
          Functor.lanAdjunction_unit] <;>
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
    intro x
    sorry

/-- Every sheaf is a filtered colimit of finite coequalizer presentations. -/
theorem lemma_filtered_colimit_constructibles {X : TopCat.{u}}
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hB_quasiCompact : ∀ U : Opens X, U ∈ B → IsCompact (U : Set X))
    (F : TopCat.Sheaf (Type u) X) :
    Nonempty (FilteredFiniteOpenCoequalizerColimit B F) := by
  sorry

/-- A finite coequalizer presentation descends from a spectral space to a
finite sober space, with finite-stalk sheaf pullback. -/
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
