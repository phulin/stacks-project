import Formalization.Books.Sheaves.Unit23.Infrastructure
import Formalization.Books.Sheaves.Unit06.PresheavesOfModules
import Formalization.Books.Sheaves.Unit10.SheavesOfModules
import Formalization.Books.Sheaves.Unit20.SheafificationOfPresheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Topology.Sheaves.Module

/-!
# Shared infrastructure for Chapter 24: Continuous maps and sheaves of modules

The module constructions are expressed with Mathlib's canonical presheaves and
sheaves of modules.  In particular, the ring maps used by pushforward and
pullback are displayed explicitly; this keeps the scalar structures in the
source statements visible in Lean.
-/

namespace Formalization.Books.Sheaves.Unit22

-- The historical namespace is retained for API compatibility.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17

universe v

noncomputable section

/-! ## Presheaves of modules -/

/-- The pushforward of presheaves of rings along a continuous map. -/
abbrev moduleRingPresheafPushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    RingPresheaf.{v, v} X ⥤ RingPresheaf.{v, v} Y :=
  TopCat.Presheaf.pushforward RingCat f

/-- The pullback of presheaves of rings along a continuous map. -/
abbrev moduleRingPresheafPullback {X Y : TopCat.{v}} (f : X ⟶ Y) :
    RingPresheaf.{v, v} Y ⥤ RingPresheaf.{v, v} X :=
  TopCat.Presheaf.pullback RingCat f

@[simp]
theorem moduleRingPresheafPushforward_obj_obj {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingPresheaf.{v, v} X) (V : Opens Y) :
    ((moduleRingPresheafPushforward f).obj O).obj (op V) =
      O.obj (op ((Opens.map f).obj V)) := rfl

/-- The pullback/pushforward adjunction for presheaves of rings. -/
noncomputable abbrev moduleRingPresheafPullbackPushforwardAdjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    moduleRingPresheafPullback f ⊣ moduleRingPresheafPushforward f :=
  TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f

/-- The scalar unit `i_O : O ⟶ f_* f_p O`. -/
noncomputable abbrev moduleRingPresheafUnit {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingPresheaf.{v, v} Y) :
    O ⟶ (moduleRingPresheafPushforward f).obj
      ((moduleRingPresheafPullback f).obj O) :=
  (moduleRingPresheafPullbackPushforwardAdjunction f).unit.app O

/- The scalar counit `c_O : f_p f_* O ⟶ O`. -/
noncomputable abbrev moduleRingPresheafCounit {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingPresheaf.{v, v} X) :
    (moduleRingPresheafPullback f).obj
        ((moduleRingPresheafPushforward f).obj O) ⟶ O :=
  (moduleRingPresheafPullbackPushforwardAdjunction f).counit.app O

/-- Pushforward of presheaves of modules along a specified scalar map. -/
noncomputable def modulePresheafPushforwardAlong {X Y : TopCat.{v}}
    {O_X : RingPresheaf.{v, v} X} {O_Y : RingPresheaf.{v, v} Y}
    (f : X ⟶ Y) (α : O_Y ⟶ (moduleRingPresheafPushforward f).obj O_X) :
    PMod O_X ⥤ PMod O_Y :=
  PresheafOfModules.pushforward (F := Opens.map f) α

/-- Pushforward of a presheaf of modules, with its induced scalar ring. -/
noncomputable def modulePresheafPushforward {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (f : X ⟶ Y) :
    PMod O ⥤ PMod ((moduleRingPresheafPushforward f).obj O) :=
  modulePresheafPushforwardAlong f (𝟙 _)

/-- Pullback of a presheaf of modules, with the scalar ring pulled back by
the left Kan extension of presheaves of rings. -/
noncomputable def modulePresheafPullback {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} Y} (f : X ⟶ Y) :
  PMod O ⥤ PMod ((moduleRingPresheafPullback f).obj O) :=
  PresheafOfModules.pullback
    (F := Opens.map f)
    ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).unit.app O)

/-- The sectionwise scalar action on a module pushforward. -/
abbrev modulePresheafPushforwardAction {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (f : X ⟶ Y) (F : PMod O) (V : Opens Y) :
    ((moduleRingPresheafPushforward f).obj O).obj (op V) →
      ((modulePresheafPushforward f).obj F).obj (op V) →
        ((modulePresheafPushforward f).obj F).obj (op V) :=
  fun r m => r • m

/-- The sectionwise scalar action on a module pullback. -/
abbrev modulePresheafPullbackAction {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} Y} (f : X ⟶ Y) (G : PMod O) (U : Opens X) :
    ((moduleRingPresheafPullback f).obj O).obj (op U) →
      ((modulePresheafPullback f).obj G).obj (op U) →
        ((modulePresheafPullback f).obj G).obj (op U) :=
  fun r m => r • m

/-- Pushforward is computed by precomposition on the underlying presheaf and
retains the pointwise module action. -/
theorem modulePresheafPushforward_underlying_formula {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (f : X ⟶ Y) (F : PMod O) :
    Nonempty
      ((((modulePresheafPushforward f).obj F).presheaf) ≅
        (TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) f).obj F.presheaf) := by
  exact ⟨Iso.refl _⟩

/-- A chosen isomorphism for the underlying presheaf pushforward formula. -/
noncomputable def modulePresheafPushforward_underlyingIso {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (f : X ⟶ Y) (F : PMod O) :
    (((modulePresheafPushforward f).obj F).presheaf) ≅
      (TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) f).obj F.presheaf :=
  Classical.choice (modulePresheafPushforward_underlying_formula f F)

/-- The pullback sections are the filtered colimit sections underlying the
presheaf left Kan extension, with the induced module structure. -/
theorem modulePresheafPullback_sections_formula {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} Y} (f : X ⟶ Y) (G : PMod O) (U : Opens X) :
    Nonempty
      (((modulePresheafPullback f).obj G).presheaf.obj (op U) ≅
        ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) f).obj G.presheaf).obj
          (op U)) := by
  sorry

/-- A chosen isomorphism for the underlying pullback-section formula. -/
noncomputable def modulePresheafPullback_sectionsIso {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} Y} (f : X ⟶ Y) (G : PMod O) (U : Opens X) :
    ((modulePresheafPullback f).obj G).presheaf.obj (op U) ≅
      ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) f).obj G.presheaf).obj
        (op U) :=
  Classical.choice (modulePresheafPullback_sections_formula f G U)

/-- The filtered neighbourhood category used by the presheaf pullback. -/
abbrev modulePresheafPullbackIndex {X Y : TopCat.{v}}
    (f : X ⟶ Y) (U : Opens X) :=
  CostructuredArrow (Opens.map f).op (op U)

/-- The additive-group diagram of sections over neighbourhoods of `f(U)`. -/
abbrev modulePresheafPullbackDiagram {X Y : TopCat.{v}}
    (f : X ⟶ Y) {O : RingPresheaf.{v, v} Y} (G : PMod O) (U : Opens X) :=
  CostructuredArrow.proj (Opens.map f).op (op U) ⋙ G.presheaf

/-- The neighbourhood index in the module pullback formula is filtered. -/
theorem modulePresheafPullbackIndex_isFiltered {X Y : TopCat.{v}}
    (f : X ⟶ Y) (U : Opens X) :
    IsFiltered (modulePresheafPullbackIndex f U) := by
  exact algebraicPresheafPullback_index_isFiltered f U

/-- The module pullback sections are the filtered neighbourhood colimit. -/
noncomputable def modulePresheafPullback_obj_colimitIso {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} Y} (f : X ⟶ Y) (G : PMod O) (U : Opens X) :
    ((modulePresheafPullback f).obj G).presheaf.obj (op U) ≅
      colimit (modulePresheafPullbackDiagram f G U) := by
  exact (modulePresheafPullback_sectionsIso f G U).trans
    (algebraicPresheafPullback_obj_colimitIso f G.presheaf U)

/-- The presheaf module pushforward/pullback adjunction. -/
noncomputable abbrev modulePresheafPullbackPushforwardAdjunction
    {X Y : TopCat.{v}} {O : RingPresheaf.{v, v} Y} (f : X ⟶ Y) :
    modulePresheafPullback f ⊣
      modulePresheafPushforwardAlong f
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).unit.app O) :=
  PresheafOfModules.pullbackPushforwardAdjunction
    ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).unit.app O)

/-- The module-valued Hom correspondence for presheaf pullback. -/
noncomputable abbrev modulePresheafHomEquiv {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} Y} (f : X ⟶ Y)
    (G : PMod O) (F : PMod ((moduleRingPresheafPullback f).obj O)) :
    ((modulePresheafPullback f).obj G ⟶ F) ≃
      (G ⟶ (modulePresheafPushforwardAlong f
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).unit.app O)).obj F) :=
  (modulePresheafPullbackPushforwardAdjunction f).homEquiv G F

/-- The unit of the module presheaf pullback adjunction. -/
noncomputable abbrev modulePresheafUnit {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} Y} (f : X ⟶ Y) (G : PMod O) :
    G ⟶ (modulePresheafPushforwardAlong f
      ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).unit.app O)).obj
        ((modulePresheafPullback f).obj G) :=
  (modulePresheafPullbackPushforwardAdjunction f).unit.app G

/-- The counit of the module presheaf pullback adjunction. -/
noncomputable abbrev modulePresheafCounit {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} Y} (f : X ⟶ Y)
    (F : PMod ((moduleRingPresheafPullback f).obj O)) :
    (modulePresheafPullback f).obj
        ((modulePresheafPushforwardAlong f
          ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).unit.app O)).obj F) ⟶ F := by
  exact (modulePresheafPullbackPushforwardAdjunction f).counit.app F

/-! ## Tensor and change of scalars -/

/-- Extension of scalars along a morphism of presheaves of rings. -/
noncomputable abbrev modulePresheafExtensionOfScalars {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{v, v} X} (α : O₁ ⟶ O₂) :
    PMod O₁ ⥤ PMod O₂ :=
  changeOfRings α

/-- The source's presheaf tensor object
`O ⊗_{f_p f_* O} f_p G`. -/
noncomputable abbrev modulePresheafTensorOverPushforward {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} X}
    (f : X ⟶ Y) (G : PMod ((moduleRingPresheafPushforward f).obj O)) : PMod O :=
  modulePresheafExtensionOfScalars
    ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).counit.app O)
    |>.obj ((modulePresheafPullback f).obj G)

/-- The tensor/pushforward Hom correspondence for presheaves of modules. -/
theorem exists_modulePresheafTensorHomEquiv {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (f : X ⟶ Y)
    (G : PMod ((moduleRingPresheafPushforward f).obj O)) (F : PMod O) :
    Nonempty ((modulePresheafTensorOverPushforward f G ⟶ F) ≃
      (G ⟶ (modulePresheafPushforward f).obj F)) := by
  let adj := TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f
  let α := adj.counit.app O
  let β := adj.unit.app ((moduleRingPresheafPushforward f).obj O)
  let H := (modulePresheafPushforwardAlong f β).obj
    ((restrictionOfScalars α).obj F)
  let K := (modulePresheafPushforward f).obj F
  let eapp : ∀ V : (Opens Y)ᵒᵖ, H.obj V ≅ K.obj V := fun V => by
    let V' := V.unop
    let a := (asIdentityRingPresheafMorphism α).app
      (op ((Opens.map f).obj V'))
    let idVcat :=
      ((𝟙 _ :
        (moduleRingPresheafPushforward f).obj O ⟶
          (moduleRingPresheafPushforward f).obj O).app V)
    let idV := idVcat.hom
    have ha : a = α.app (op ((Opens.map f).obj V')) :=
      asIdentityRingPresheafMorphism_app α _
    have htri := adj.right_triangle_components O
    have htri' :
        (β.app V) ≫ ((moduleRingPresheafPushforward f).map α).app V = idVcat := by
      convert congr_app htri V using 1 <;> rfl
    have htri'' := congrArg RingCat.Hom.hom htri'
    change (α.app (op ((Opens.map f).obj V'))).hom.comp
      (β.app V).hom = idV at htri''
    rw [← ha] at htri''
    have hid : idV = RingHom.id (((moduleRingPresheafPushforward f).obj O).obj V) := by
      rfl
    have hgf :
        RingHom.id (((moduleRingPresheafPushforward f).obj O).obj V) =
          a.hom.comp (β.app V).hom := by
      exact hid.symm.trans htri''.symm
    change
      (ModuleCat.restrictScalars (β.app V).hom).obj
          ((ModuleCat.restrictScalars a.hom).obj
            (F.obj (op ((Opens.map f).obj V')))) ≅
        (ModuleCat.restrictScalars idV).obj
          (F.obj (op ((Opens.map f).obj V')))
    exact
      (ModuleCat.restrictScalarsComp'App
        (β.app V).hom a.hom (RingHom.id _) hgf
        (F.obj (op ((Opens.map f).obj V')))).symm ≪≫
        (ModuleCat.restrictScalarsCongr hid.symm).app
          (F.obj (op ((Opens.map f).obj V')))
  let e : H ≅ K := by
    have eapp_apply (V : (Opens Y)ᵒᵖ) (m : H.obj V) :
        (eapp V).hom m = m := by
      dsimp [eapp]
      simp [ModuleCat.restrictScalarsComp'App_inv_apply,
        ModuleCat.restrictScalarsCongr_hom_app]
      rfl
    refine PresheafOfModules.isoMk eapp ?_
    intro U V i
    ext m
    let mV : H.obj V := H.map i m
    change (eapp V).hom mV = K.map i ((eapp U).hom m)
    rw [eapp_apply, eapp_apply]
    dsimp [mV, H, K]
    rfl
  let h₁ :=
    (changeOfRingsHomEquiv α ((modulePresheafPullback f).obj G) F).symm
  let h₂ := modulePresheafHomEquiv f G ((restrictionOfScalars α).obj F)
  let h₃ : (G ⟶ H) ≃ (G ⟶ K) :=
    { toFun := fun q => q ≫ e.hom
      invFun := fun q => q ≫ e.inv
      left_inv := by
        intro q
        simp
      right_inv := by
        intro q
        simp }
  exact ⟨h₁.trans (h₂.trans h₃)⟩

/-- The tensor/pushforward Hom correspondence for presheaves of modules. -/
noncomputable def modulePresheafTensorHomEquiv {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (f : X ⟶ Y)
    (G : PMod ((moduleRingPresheafPushforward f).obj O)) (F : PMod O) :
    (modulePresheafTensorOverPushforward f G ⟶ F) ≃
      (G ⟶ (modulePresheafPushforward f).obj F) := by
  exact Classical.choice (exists_modulePresheafTensorHomEquiv f G F)

/-! ## Sheaves of modules -/

/-- Pushforward of sheaves of rings. -/
abbrev moduleRingSheafPushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    RingSheaf X ⥤ RingSheaf Y :=
  TopCat.Sheaf.pushforward RingCat f

/-- Pullback of sheaves of rings. -/
abbrev moduleRingSheafPullback {X Y : TopCat.{v}} (f : X ⟶ Y) :
    RingSheaf Y ⥤ RingSheaf X :=
  TopCat.Sheaf.pullback RingCat f

/-- The pullback/pushforward adjunction for sheaves of rings. -/
noncomputable abbrev moduleRingSheafPullbackPushforwardAdjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    moduleRingSheafPullback f ⊣ moduleRingSheafPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f

/-- The canonical scalar map from a sheaf to the pushforward of its sheaf
pullback.  Naming this map removes the identity-functor presentation of the
unit from the module interfaces below. -/
noncomputable def moduleSheafPullbackUnit {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingSheaf Y) :
    O ⟶ (moduleRingSheafPushforward f).obj
      ((moduleRingSheafPullback f).obj O) := by
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f).unit.app O

/-- The scalar counit `f⁻¹ f_* O ⟶ O`. -/
noncomputable abbrev moduleSheafPullbackCounit {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingSheaf X) :
    (moduleRingSheafPullback f).obj ((moduleRingSheafPushforward f).obj O) ⟶ O :=
  (moduleRingSheafPullbackPushforwardAdjunction f).counit.app O

/-- Pushforward of sheaves of modules along a continuous map, using the
identity map to the pushed-forward scalar ring. -/
noncomputable def moduleSheafPushforwardAlong {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} (f : X ⟶ Y)
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X) :
    Mod O_X ⥤ Mod O_Y :=
  SheafOfModules.pushforward (F := Opens.map f) α

/-- Pushforward of sheaves of modules along a continuous map, using the
identity map to the pushed-forward scalar ring. -/
noncomputable def moduleSheafPushforward {X Y : TopCat.{v}}
    {O : RingSheaf X} (f : X ⟶ Y) :
    Mod O ⥤ Mod ((moduleRingSheafPushforward f).obj O) :=
  moduleSheafPushforwardAlong f (𝟙 _)

/-- Pullback of sheaves of modules along a continuous map. -/
noncomputable def moduleSheafPullbackAlong {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} (f : X ⟶ Y)
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)] :
    Mod O_Y ⥤ Mod O_X :=
  SheafOfModules.pullback (F := Opens.map f) α

/-- Pullback of sheaves of modules along a continuous map. -/
noncomputable def moduleSheafPullback {X Y : TopCat.{v}}
    {O : RingSheaf Y} (f : X ⟶ Y)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (moduleSheafPullbackUnit f O)).IsRightAdjoint)] :
    Mod O ⥤ Mod ((moduleRingSheafPullback f).obj O) :=
  moduleSheafPullbackAlong f
    (moduleSheafPullbackUnit f O)

/-! ## Restriction to an open subspace -/

/-- The canonical map from a sheaf of rings to the direct image of its
restriction to an open subspace. -/
noncomputable def openModuleRestrictionRingMap {X : TopCat.{v}}
    (U : Opens X) (O : RingSheaf X) :
    O ⟶ (TopCat.Sheaf.pushforward RingCat (Opens.inclusion' U)).obj
      ((TopologicalSpace.Opens.sheafRestrict U).obj O) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
      (Opens.inclusion' U)).unit.app O ≫
    (TopCat.Sheaf.pushforward RingCat (Opens.inclusion' U)).map
      ((Topology.IsOpenEmbedding.sheafPullbackIso (A := RingCat)
        U.isOpenEmbedding).app O).hom

instance openModuleRestrictionMap_isContinuous {X : TopCat.{v}}
    (U : Opens X) :
    (Opens.map (Opens.inclusion' U)).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology U) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map (Opens.inclusion' U)
  · exact coverPreserving_opens_map (Opens.inclusion' U)

/-- Direct image of modules from an open subspace, along the canonical map of
restricted scalar sheaves. -/
noncomputable abbrev openModuleRestrictionDirectImage {X : TopCat.{v}}
    (U : Opens X) (O : RingSheaf X) :
    SheafOfModules.{v} ((TopologicalSpace.Opens.sheafRestrict U).obj O) ⥤
      SheafOfModules.{v} O :=
  SheafOfModules.pushforward (F := Opens.map (Opens.inclusion' U))
    (openModuleRestrictionRingMap U O)

/-- The site functor obtained from the over-category description of an open
subspace agrees with inverse image of open sets along the inclusion. -/
noncomputable def openModuleRestrictionBaseIso {X : TopCat.{v}}
    (U : Opens X) :
    Over.star U ⋙ U.overEquivalence.functor ≅ Opens.map (Opens.inclusion' U) :=
  NatIso.ofComponents (fun V ↦ eqToIso (by
    ext x
    simp
    constructor <;> intro hx <;> exact hx))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The direct image right adjoint in the over-category description agrees
with direct image along the open inclusion. -/
noncomputable def openModuleRestrictionRightAdjointIso {X : TopCat.{v}}
    (U : Opens X) (O : RingSheaf X) :
    (U.sheafOfModulesEquivOver O).inverse ⋙
        SheafOfModules.pushforward.{v} (SheafOfModules.pushforwardOver U) ≅
      openModuleRestrictionDirectImage U O := by
  change Sheaf (Opens.grothendieckTopology X) RingCat at O
  change
    SheafOfModules.pushforward.{v}
        (U.sheafRestrictSheafEquivOver.app O).inv ⋙
      SheafOfModules.pushforward.{v} (SheafOfModules.pushforwardOver U) ≅ _
  letI compContinuous : (Over.star U ⋙ U.overEquivalence.functor).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology U) :=
    Functor.isContinuous_comp _ _ _
      ((Opens.grothendieckTopology X).over U) _
  letI mapContinuous : (Opens.map (Opens.inclusion' U)).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology U) :=
    openModuleRestrictionMap_isContinuous U
  refine SheafOfModules.pushforwardComp
      (SheafOfModules.pushforwardOver U)
      (U.sheafRestrictSheafEquivOver.app O).inv ≪≫ ?_
  refine @SheafOfModules.pushforwardCongr₂.{v}
    (Opens X) _ (Opens U) _
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology U)
    (Opens.map (Opens.inclusion' U))
    (Over.star U ⋙ U.overEquivalence.functor) O
    ((TopologicalSpace.Opens.sheafRestrict U).obj O)
    mapContinuous compContinuous _ _
    (openModuleRestrictionBaseIso U).symm ?_
  let e₁ := TopCat.Sheaf.pullbackIso RingCat (Opens.inclusion' U)
  let e₂ := e₁.symm ≪≫
    Topology.IsOpenEmbedding.sheafPullbackIso (A := RingCat)
      U.isOpenEmbedding
  have he :
      ((Topology.IsOpenEmbedding.sheafPullbackIso (A := RingCat)
        U.isOpenEmbedding).app O).hom =
        e₁.hom.app O ≫ e₂.hom.app O := by
    simp [e₂]
  rw [openModuleRestrictionRingMap]
  erw [he]
  rw [Functor.map_comp, Category.assoc]
  dsimp only [e₁, TopCat.Sheaf.pullbackIso,
    Functor.sheafPullbackConstruction.sheafPullbackIso,
    TopCat.Sheaf.pullbackPushforwardAdjunction, TopCat.Sheaf.pushforward]
  have hunit := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous (Opens.map (Opens.inclusion' U))
      RingCat (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)))
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map (Opens.inclusion' U)) RingCat
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))) O
  conv_rhs => rw [← Category.assoc]
  rw [hunit]
  rw [Sheaf.hom_ext_iff]
  change _ =
    (sheafToPresheaf (Opens.grothendieckTopology X) RingCat).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (Opens.inclusion' U)) RingCat
          (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology
            ((Opens.toTopCat X).obj U))).unit.app O) ≫
      Functor.whiskerLeft (Opens.map (Opens.inclusion' U)).op
        (e₂.hom.app O).hom
  erw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Adjunction.comp_unit_app, sheafificationAdjunction_unit_app,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Functor.comp_obj]
  simp only [Functor.id_obj, ObjectProperty.ι_obj, Iso.app_inv, Iso.symm_hom,
    ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom,
    Functor.whiskeringLeft_obj_obj, Functor.lanAdjunction_unit,
    Functor.whiskeringLeft_obj_map, Functor.comp_map, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.id_hom, Functor.whiskerLeft_id',
    Category.comp_id, Category.assoc]
  simp only [SheafOfModules.pushforwardOver, Functor.op_obj, Over.forget_obj,
    Over.star_obj_left, Opens.overEquivalence, homOfLE_leOfHom, Over.mk_left,
    Functor.id_obj, Functor.comp_obj, Opens.coe_mk,
    Opens.sheafRestrictSheafEquivOver, Opens.overPullbackSheafEquivOver,
    Iso.symm_inv, Iso.isoCompInverse_hom_app, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.comp_id,
    openModuleRestrictionBaseIso, TopCat.Sheaf.pullbackIso,
    Topology.IsOpenEmbedding.sheafPullbackIso, IsOpenMap.functor,
    Opens.coe_inclusion', Functor.whiskeringLeft_obj_obj,
    Iso.symm_self_id_assoc, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Functor.FullyFaithful.preimageIso_hom,
    ObjectProperty.ι_obj, Iso.symm_hom, isoSheafify_inv, e₂, e₁]
  erw [ObjectProperty.FullSubcategory.comp_hom]
  erw [sheafifyMap_sheafifyLift]
  erw [Category.comp_id]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp]
  erw [toSheafify_sheafifyLift]
  ext V : 2
  change ((_ : O.obj.obj V ⟶ _) ≫ _ ≫ _) =
    ((_ : O.obj.obj V ⟶ _) ≫ _)
  dsimp [IsOpenMap.pullbackIso, IsOpenMap.pullbackObjIso,
    TopCat.Presheaf.pullbackObjObjOfImageOpen]
  let g : CostructuredArrow (Opens.map (Opens.inclusion' U)).op
      ((Opens.map (Opens.inclusion' U)).op.obj V) :=
    CostructuredArrow.mk (𝟙 _)
  conv_rhs =>
    lhs
    rw [← Category.comp_id
      (((Opens.map (Opens.inclusion' U)).op.lanUnit.app O.obj).app V)]
    rhs
    change 𝟙 (((Opens.map (Opens.inclusion' U)).op.lan.obj O.obj).obj
      ((Opens.map (Opens.inclusion' U)).op.obj V))
    rw [← CategoryTheory.Functor.map_id
      ((Opens.map (Opens.inclusion' U)).op.lan.obj O.obj)]
  change _ =
    ((Functor.LeftExtension.mk
      ((Opens.map (Opens.inclusion' U)).op.lan.obj O.obj)
      ((Opens.map (Opens.inclusion' U)).op.lanUnit.app O.obj)).coconeAt
        ((Opens.map (Opens.inclusion' U)).op.obj V)).ι.app g ≫ _
  rw [Limits.IsColimit.comp_coconePointUniqueUpToIso_hom]
  rw [Limits.coconeOfDiagramTerminal_ι_app]
  dsimp [g]
  change _ = O.obj.map
    (homOfLE
      (x := U.isOpenEmbedding.isOpenMap.functor.obj
        ((Opens.map (Opens.inclusion' U)).obj (unop V)))
      (Set.image_preimage_subset (Opens.inclusion' U)
        ((unop V : Opens X) : Set X))).op
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Restricting a module through the over category and then identifying the
over site with the open subspace is naturally isomorphic to module pullback
along the open inclusion. -/
noncomputable def openModuleRestrictionComparison {X : TopCat.{v}}
    (U : Opens X) (O : RingSheaf X)
    [(openModuleRestrictionDirectImage U O).IsRightAdjoint] :
    SheafOfModules.overFunctor.{v} O U ⋙
        (U.sheafOfModulesEquivOver.{v} O).functor ≅
      (openModuleRestrictionDirectImage U O).leftAdjoint := by
  let adj := (SheafOfModules.overPushforwardOverAdj (R := O) U).comp
    (U.sheafOfModulesEquivOver O).toAdjunction
  exact Adjunction.leftAdjointUniq
    (adj.ofNatIsoRight (openModuleRestrictionRightAdjointIso U O))
    (Adjunction.ofIsRightAdjoint (openModuleRestrictionDirectImage U O))

/-- Objectwise form of `openModuleRestrictionComparison`, convenient for
transporting a presentation to the restriction of a module. -/
noncomputable def openModuleRestrictionObjIso {X : TopCat.{v}}
    (U : Opens X) (O : RingSheaf X)
    [(openModuleRestrictionDirectImage U O).IsRightAdjoint]
    (F : SheafOfModules.{v} O) :
    (U.sheafOfModulesEquivOver.{v} O).functor.obj (F.over U) ≅
      (openModuleRestrictionDirectImage U O).leftAdjoint.obj F :=
  (openModuleRestrictionComparison U O).app F

/-- The module sheaf pushforward is the sheaf-level form of the presheaf
pushforward module action. -/
theorem moduleSheafPushforward_underlying_formula {X Y : TopCat.{v}}
    {O : RingSheaf X} (f : X ⟶ Y) (F : Mod O) :
    Nonempty
      ((((moduleSheafPushforward f).obj F).val.presheaf) ≅
        (TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) f).obj F.val.presheaf) := by
  exact ⟨Iso.refl _⟩

/-- A chosen isomorphism for the underlying sheaf pushforward formula. -/
noncomputable def moduleSheafPushforward_underlyingIso {X Y : TopCat.{v}}
    {O : RingSheaf X} (f : X ⟶ Y) (F : Mod O) :
    (((moduleSheafPushforward f).obj F).val.presheaf) ≅
      (TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) f).obj F.val.presheaf :=
  Classical.choice (moduleSheafPushforward_underlying_formula f F)

/-- Pullback of sheaves of modules is the sheafification of the presheaf
module pullback. -/
noncomputable def moduleSheafPullback_sheafificationIso {X Y : TopCat.{v}}
    {O : RingSheaf Y} (f : X ⟶ Y) (G : Mod O)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (moduleSheafPullbackUnit f O)).IsRightAdjoint)]
    [(PresheafOfModules.pushforward (moduleSheafPullbackUnit f O).hom).IsRightAdjoint] :
    (moduleSheafPullback f).obj G ≅
      (SheafOfModules.forget O ⋙
        PresheafOfModules.pullback (moduleSheafPullbackUnit f O).hom ⋙
        PresheafOfModules.sheafification
          (R₀ := ((moduleRingSheafPullback f).obj O).obj) (𝟙 _)).obj G :=
  SheafOfModules.pullbackIso
    (F := Opens.map f)
    (moduleSheafPullbackUnit f O) |>.app G

/-- The sheaf module pullback/pushforward adjunction. -/
noncomputable abbrev moduleSheafPullbackPushforwardAdjunction
    {X Y : TopCat.{v}} {O : RingSheaf Y} (f : X ⟶ Y)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (moduleSheafPullbackUnit f O)).IsRightAdjoint)] :
    moduleSheafPullback f ⊣
      moduleSheafPushforwardAlong f
        (moduleSheafPullbackUnit f O) :=
  SheafOfModules.pullbackPushforwardAdjunction
    (F := Opens.map f)
    (moduleSheafPullbackUnit f O)

/-- The module-valued Hom correspondence for sheaf pullback. -/
noncomputable abbrev moduleSheafHomEquiv {X Y : TopCat.{v}}
    {O : RingSheaf Y} (f : X ⟶ Y) (G : Mod O)
    (F : Mod ((moduleRingSheafPullback f).obj O))
    [((SheafOfModules.pushforward (F := Opens.map f)
      (moduleSheafPullbackUnit f O)).IsRightAdjoint)] :
    ((moduleSheafPullback f).obj G ⟶ F) ≃
      (G ⟶ (moduleSheafPushforwardAlong f
        (moduleSheafPullbackUnit f O)).obj F) :=
  (moduleSheafPullbackPushforwardAdjunction f).homEquiv G F

/-- The unit of the sheaf-module pullback/pushforward adjunction. -/
noncomputable abbrev moduleSheafUnit {X Y : TopCat.{v}}
    {O : RingSheaf Y} (f : X ⟶ Y) (G : Mod O)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (moduleSheafPullbackUnit f O)).IsRightAdjoint)] :
    G ⟶ (moduleSheafPushforwardAlong f (moduleSheafPullbackUnit f O)).obj
      ((moduleSheafPullback f).obj G) :=
  (moduleSheafPullbackPushforwardAdjunction f).unit.app G

/-- The counit of the sheaf-module pullback/pushforward adjunction. -/
noncomputable abbrev moduleSheafCounit {X Y : TopCat.{v}}
    {O : RingSheaf Y} (f : X ⟶ Y)
    (F : Mod ((moduleRingSheafPullback f).obj O))
    [((SheafOfModules.pushforward (F := Opens.map f)
      (moduleSheafPullbackUnit f O)).IsRightAdjoint)] :
    (moduleSheafPullback f).obj
        ((moduleSheafPushforwardAlong f (moduleSheafPullbackUnit f O)).obj F) ⟶ F :=
  (moduleSheafPullbackPushforwardAdjunction f).counit.app F

/-- The sheaf-level tensor object
`O_X ⊗_{f⁻¹ f_* O_X} f⁻¹ G`, represented by the canonical module pullback
along the identity map on the pushed-forward scalar sheaf. -/
noncomputable def moduleSheafTensorOverPushforward {X Y : TopCat.{v}}
    {O : RingSheaf X} (f : X ⟶ Y)
    (G : Mod ((moduleRingSheafPushforward f).obj O))
    [((SheafOfModules.pushforward (F := Opens.map f)
      (𝟙 ((moduleRingSheafPushforward f).obj O))).IsRightAdjoint)] :
    Mod O :=
  (moduleSheafPullbackAlong f
    (𝟙 ((moduleRingSheafPushforward f).obj O))).obj G

/-- The sheaf tensor/pushforward Hom correspondence. -/
noncomputable abbrev moduleSheafTensorHomEquiv {X Y : TopCat.{v}}
    {O : RingSheaf X} (f : X ⟶ Y)
    (G : Mod ((moduleRingSheafPushforward f).obj O)) (F : Mod O)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (𝟙 ((moduleRingSheafPushforward f).obj O))).IsRightAdjoint)] :
    (moduleSheafTensorOverPushforward f G ⟶ F) ≃
      (G ⟶ (moduleSheafPushforward f).obj F) :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (F := Opens.map f)
    (𝟙 ((moduleRingSheafPushforward f).obj O))).homEquiv G F

/-- The stalk-level tensor formula for module sheaf pullback. -/
theorem moduleSheafPullback_stalk_formula {X Y : TopCat.{v}}
    {O : RingSheaf Y} (f : X ⟶ Y) (G : Mod O) (x : X)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (moduleSheafPullbackUnit f O)).IsRightAdjoint)] :
    Nonempty
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf (f x) ≅
        TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
          ((moduleSheafPullback f).obj G).val.presheaf x) := by
  sorry

/-! ## Module `f`-maps -/

/-- A presheaf module `f`-map is a morphism into the module pushforward. -/
abbrev ModulePresheafFMap {X Y : TopCat.{v}}
    {O_X : RingPresheaf.{v, v} X} {O_Y : RingPresheaf.{v, v} Y} (f : X ⟶ Y)
    (α : O_Y ⟶ (moduleRingPresheafPushforward f).obj O_X)
    (G : PMod O_Y) (F : PMod O_X) : Type _ :=
  G ⟶ (modulePresheafPushforwardAlong f α).obj F

noncomputable abbrev modulePresheafFMapHomEquiv {X Y : TopCat.{v}}
    {O_X : RingPresheaf.{v, v} X} {O_Y : RingPresheaf.{v, v} Y}
    (f : X ⟶ Y) (α : O_Y ⟶ (moduleRingPresheafPushforward f).obj O_X)
    (G : PMod O_Y) (F : PMod O_X) :
    ModulePresheafFMap f α G F ≃
      (G ⟶ (modulePresheafPushforwardAlong f α).obj F) :=
  Equiv.refl _

noncomputable abbrev modulePresheafFMapPullbackHomEquiv {X Y : TopCat.{v}}
    {O : RingPresheaf.{v, v} Y} (f : X ⟶ Y)
    (G : PMod O) (F : PMod ((moduleRingPresheafPullback f).obj O)) :
    ((modulePresheafPullback f).obj G ⟶ F) ≃
      ModulePresheafFMap f
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).unit.app O)
        G F :=
  modulePresheafHomEquiv f G F

/-- A sheaf module `f`-map is a morphism into the module pushforward. -/
abbrev ModuleSheafFMap {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} (f : X ⟶ Y)
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    (G : Mod O_Y) (F : Mod O_X) : Type _ :=
  G ⟶ (moduleSheafPushforwardAlong f α).obj F

/-- The module pullback Hom description of module `f`-maps. -/
noncomputable abbrev moduleSheafFMapPullbackHomEquiv {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} (f : X ⟶ Y)
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    (G : Mod O_Y) (F : Mod O_X) :
    ((moduleSheafPullbackAlong f α).obj G ⟶ F) ≃
      ModuleSheafFMap f α G F :=
  (SheafOfModules.pullbackPushforwardAdjunction α).homEquiv G F

 /-- Composition of module `f`-maps is induced by the canonical pushforward
composition isomorphism. -/
 noncomputable def moduleSheafFMapComp {X Y Z : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {O_Z : RingSheaf Z}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    (β : O_Z ⟶ (moduleRingSheafPushforward g).obj O_Y)
    {F : Mod O_X} {G : Mod O_Y} {H : Mod O_Z}
    (φ : ModuleSheafFMap f α G F) (ψ : ModuleSheafFMap g β H G) :
    ModuleSheafFMap (f ≫ g)
      (β ≫ (moduleRingSheafPushforward g).map α) H F := by
  exact ψ ≫ (moduleSheafPushforwardAlong g β).map φ ≫
    (SheafOfModules.pushforwardComp β α).hom.app F

 /-- The existential source formulation of module `f`-map composition. -/
 theorem moduleSheafFMap_comp {X Y Z : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {O_Z : RingSheaf Z}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    (β : O_Z ⟶ (moduleRingSheafPushforward g).obj O_Y)
    {F : Mod O_X} {G : Mod O_Y} {H : Mod O_Z}
    (φ : ModuleSheafFMap f α G F) (ψ : ModuleSheafFMap g β H G) :
    Nonempty (ModuleSheafFMap (f ≫ g)
      (β ≫ (moduleRingSheafPushforward g).map α) H F) :=
  ⟨moduleSheafFMapComp α β φ ψ⟩

/-- The induced map on stalks of a module `f`-map is linear over the stalk of
the target ring. -/
abbrev moduleSheafFMapStalkScalarMap {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X) (x : X) :
    TopCat.Presheaf.stalk (C := RingCat.{v}) O_Y.obj (f x) ⟶
      TopCat.Presheaf.stalk (C := RingCat.{v}) O_X.obj x :=
  (TopCat.Presheaf.stalkFunctor (RingCat.{v}) (f x)).map α.hom ≫
    TopCat.Presheaf.stalkPushforward (RingCat.{v}) f O_X.obj x

/-- The scalar-restricted target module used for a module `f`-map on stalks. -/
noncomputable abbrev moduleSheafFMapStalkTarget {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    (F : Mod O_X) (x : X) :=
  (ModuleCat.restrictScalars (moduleSheafFMapStalkScalarMap α x).hom).obj
    (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O_X.obj x)
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x)))

/-- The underlying additive morphism on stalks of a module `f`-map. -/
noncomputable abbrev moduleSheafFMapStalkAddMap {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    {G : Mod O_Y} {F : Mod O_X} (φ : ModuleSheafFMap f α G F) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf (f x) ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (f x)).map
      ((PresheafOfModules.toPresheaf O_Y.obj).map φ.val) ≫
    TopCat.Presheaf.stalkPushforward (AddCommGrpCat.{v}) f F.val.presheaf x

/-- The stalk additive map of a module `f`-map is linear for the scalar map
induced by the ring `f`-map. -/
theorem moduleSheafFMapStalkAddMap_smul {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    {G : Mod O_Y} {F : Mod O_X} (φ : ModuleSheafFMap f α G F) (x : X)
    (r : TopCat.Presheaf.stalk (C := RingCat.{v}) O_Y.obj (f x)) :
    moduleSheafFMapStalkAddMap α φ x ≫
        (moduleSheafFMapStalkTarget α F x).smul r =
        (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O_Y.obj (f x))
        (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf (f x)))).smul r ≫
        moduleSheafFMapStalkAddMap α φ x := by
  classical
  apply TopCat.Presheaf.stalk_hom_ext G.val.presheaf
  intro U hxU
  apply ConcreteCategory.hom_ext
  intro m
  obtain ⟨V, hxV, rV, hr⟩ := TopCat.Presheaf.exists_germ_eq O_Y.obj r
  let W : Opens Y := U ⊓ V
  let hxW : (f x) ∈ W := ⟨hxU, hxV⟩
  let hxW' : x ∈ (Opens.map f).obj W := hxW
  let rW : O_Y.obj.obj (Opposite.op W) :=
    O_Y.obj.map (homOfLE (show W ≤ V from inf_le_right)).op rV
  have hrW :
      TopCat.Presheaf.germ O_Y.obj W (f x) hxW rW = r := by
    dsimp [rW]
    rw [TopCat.Presheaf.germ_res_apply]
    simpa using hr
  let mW : G.val.obj (Opposite.op W) :=
    G.val.map (homOfLE (show W ≤ U from inf_le_left)).op m
  let mW0 : G.val.presheaf.obj (Opposite.op W) :=
    G.val.presheaf.map (homOfLE (show W ≤ U from inf_le_left)).op m
  have hmW0 : mW0 = mW := by
    dsimp [mW0, mW]
    rfl
  have hmW :
      TopCat.Presheaf.germ G.val.presheaf W (f x) hxW mW0 =
        TopCat.Presheaf.germ G.val.presheaf U (f x) hxU m := by
    simpa only [mW0] using
      (TopCat.Presheaf.germ_res_apply G.val.presheaf
        (homOfLE (show W ≤ U from inf_le_left)) (f x) hxW m)
  let φAdd : G.val.presheaf ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.val.presheaf :=
    (PresheafOfModules.toPresheaf O_Y.obj).map φ.val
  let q : TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf (f x) ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
        ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.val.presheaf) (f x) :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map φAdd
  let p : TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
        ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.val.presheaf) (f x) ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x :=
    TopCat.Presheaf.stalkPushforward AddCommGrpCat f F.val.presheaf x
  let a := (RingCat.Hom.hom (moduleSheafFMapStalkScalarMap α x)) r
  let gmU := (ConcreteCategory.hom
    (TopCat.Presheaf.germ G.val.presheaf U (f x) hxU)) m
  let gmW := (ConcreteCategory.hom
    (TopCat.Presheaf.germ G.val.presheaf W (f x) hxW)) mW
  have hgm : gmW = gmU := by
    dsimp [gmW, gmU]
    rw [← hmW0]
    exact hmW
  let toF (n : G.val.obj (Opposite.op W)) :
      F.val.obj (Opposite.op ((Opens.map f).obj W)) :=
    φ.val.app (Opposite.op W) n
  let toF0 (n : G.val.obj (Opposite.op W)) :
      F.val.presheaf.obj (Opposite.op ((Opens.map f).obj W)) :=
    toF n
  change ConcreteCategory.hom
      ((ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat) O_X.obj x)
        (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat) F.val.presheaf x))).smul a)
      (ConcreteCategory.hom (q ≫ p) gmU) =
    ConcreteCategory.hom (q ≫ p)
      (ConcreteCategory.hom
        ((ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat) O_Y.obj (f x))
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat) G.val.presheaf (f x)))).smul r)
          gmU)
  rw [← hgm]
  rw [← hrW]
  have hmap (n : G.val.obj (Opposite.op W)) :
      ConcreteCategory.hom (q ≫ p)
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ G.val.presheaf W (f x) hxW)
              (show G.val.presheaf.obj (Opposite.op W) from n)) =
        ConcreteCategory.hom
          (TopCat.Presheaf.germ F.val.presheaf ((Opens.map f).obj W) x hxW')
          (toF0 n) := by
    change (ConcreteCategory.hom p)
        ((ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map φAdd))
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ G.val.presheaf W (f x) hxW)
              (show G.val.presheaf.obj (Opposite.op W) from n))) = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change (ConcreteCategory.hom
        (((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.val.presheaf).germ
          W (f x) hxW ≫
          TopCat.Presheaf.stalkPushforward AddCommGrpCat f F.val.presheaf x))
        ((φ.val.app (Opposite.op W)).hom n) = _
    have hpush := TopCat.Presheaf.stalkPushforward_germ
      (C := AddCommGrpCat) f F.val.presheaf W x hxW'
    have hpush' := congrArg
        (fun k : ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.val.presheaf).obj
          (Opposite.op W) ⟶
          TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x =>
        ConcreteCategory.hom k ((φ.val.app (Opposite.op W)).hom n)) hpush
    simpa only [toF0, toF, φAdd, TopCat.Presheaf.pushforward,
      ConcreteCategory.comp_apply] using hpush'
  let aW : O_X.obj.obj (Opposite.op ((Opens.map f).obj W)) :=
    (α.hom.app (Opposite.op W)).hom rW
  have hscalar :
      a = ConcreteCategory.hom
        (TopCat.Presheaf.germ O_X.obj ((Opens.map f).obj W) x hxW')
        aW := by
    dsimp [a, moduleSheafFMapStalkScalarMap]
    rw [← hrW]
    change (RingCat.Hom.hom
        (TopCat.Presheaf.stalkPushforward RingCat f O_X.obj x))
        ((RingCat.Hom.hom
          ((TopCat.Presheaf.stalkFunctor RingCat (f x)).map α.hom))
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ O_Y.obj W (f x) hxW) rW)) = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change (RingCat.Hom.hom
        (TopCat.Presheaf.stalkPushforward RingCat f O_X.obj x))
        ((ConcreteCategory.hom
          (((TopCat.Presheaf.pushforward RingCat f).obj O_X.obj).germ W
            (f x) hxW)) ((RingCat.Hom.hom (α.hom.app (Opposite.op W))) rW)) = _
    have hpush := TopCat.Presheaf.stalkPushforward_germ
      (C := RingCat) f O_X.obj W x hxW'
    have hpush' := congrArg
      (fun k : ((TopCat.Presheaf.pushforward RingCat f).obj O_X.obj).obj
          (Opposite.op W) ⟶ TopCat.Presheaf.stalk (C := RingCat) O_X.obj x =>
        RingCat.Hom.hom k ((RingCat.Hom.hom (α.hom.app (Opposite.op W))) rW)) hpush
    convert hpush' using 1 <;> rfl
  let nF : F.val.obj (Opposite.op ((Opens.map f).obj W)) :=
    toF mW
  let nF0 : F.val.presheaf.obj (Opposite.op ((Opens.map f).obj W)) :=
    toF0 mW
  let nFsmul : F.val.presheaf.obj (Opposite.op ((Opens.map f).obj W)) :=
    aW • nF
  have hsmulF :
      (ConcreteCategory.hom
        (TopCat.Presheaf.germ O_X.obj ((Opens.map f).obj W) x hxW') aW) •
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ F.val.presheaf ((Opens.map f).obj W) x hxW') nF0) =
        ConcreteCategory.hom
          (TopCat.Presheaf.germ F.val.presheaf ((Opens.map f).obj W) x hxW') nFsmul := by
    simpa [nF0, nFsmul, toF0, nF, toF] using
      (PresheafOfModules.germ_ringCat_smul F.val x
        ((Opens.map f).obj W) hxW' aW nF).symm
  have hφsmul : toF0 (rW • mW) = nFsmul := by
    change (φ.val.app (Opposite.op W)).hom (rW • mW) = aW • nF
    exact (φ.val.app (Opposite.op W)).hom.map_smul rW mW
  have hsmulG :
      ConcreteCategory.hom
          ((ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat) O_Y.obj (f x))
            (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat) G.val.presheaf (f x)))).smul
            (ConcreteCategory.hom (TopCat.Presheaf.germ O_Y.obj W (f x) hxW) rW))
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ G.val.presheaf W (f x) hxW) mW) =
        ConcreteCategory.hom
          (TopCat.Presheaf.germ G.val.presheaf W (f x) hxW)
          (rW • mW) := by
    change
      (ConcreteCategory.hom (TopCat.Presheaf.germ O_Y.obj W (f x) hxW) rW) •
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ G.val.presheaf W (f x) hxW) mW) = _
    exact (PresheafOfModules.germ_ringCat_smul G.val (f x) W hxW rW mW).symm
  rw [hmap mW]
  rw [hscalar]
  change
    (ConcreteCategory.hom
      (TopCat.Presheaf.germ O_X.obj ((Opens.map f).obj W) x hxW') aW) •
        (ConcreteCategory.hom
          (TopCat.Presheaf.germ F.val.presheaf ((Opens.map f).obj W) x hxW') nF0) = _
  rw [hsmulF]
  rw [hsmulG]
  rw [hmap (rW • mW)]
  rw [hφsmul]

/-- The induced module morphism on stalks of a module `f`-map. -/
noncomputable def moduleSheafFMapStalkMap {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    {G : Mod O_Y} {F : Mod O_X} (φ : ModuleSheafFMap f α G F) (x : X) :
    ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O_Y.obj (f x))
        (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf (f x))) ⟶
      moduleSheafFMapStalkTarget α F x := by
  exact ModuleCat.homMk (moduleSheafFMapStalkAddMap α φ x)
    (moduleSheafFMapStalkAddMap_smul α φ x)

theorem moduleSheafFMap_stalk_linear {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    {G : Mod O_Y} {F : Mod O_X} (φ : ModuleSheafFMap f α G F) (x : X)
    (r : TopCat.Presheaf.stalk (C := RingCat.{v}) O_Y.obj (f x))
    (m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf (f x))) :
    (moduleSheafFMapStalkMap α φ x).hom (r • m) =
      r • (moduleSheafFMapStalkMap α φ x).hom m := by
  exact (moduleSheafFMapStalkMap α φ x).hom.map_smul r m

/-! The plain pair `(f_*, f⁻¹)` generally has different scalar categories. -/

/-- The source's warning about the untyped module pair is recorded as the
precise scalar-category mismatch that must be repaired by a ringed map. -/
def plainModulePushPullScalarMismatch {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O_X : RingSheaf X) (O_Y : RingSheaf Y) : Prop :=
  (moduleRingSheafPushforward f).obj O_X ≠ O_Y ∨
    (moduleRingSheafPullback f).obj O_Y ≠ O_X

end

end Formalization.Books.Sheaves.Unit22
