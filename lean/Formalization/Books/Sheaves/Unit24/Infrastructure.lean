import Formalization.Books.Sheaves.Unit23.Infrastructure
import Formalization.Books.Sheaves.Unit06.PresheavesOfModules
import Formalization.Books.Sheaves.Unit10.SheavesOfModules
import Formalization.Books.Sheaves.Unit20.SheafificationOfPresheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

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
  sorry

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
  sorry

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

/-- The module sheaf pushforward is the sheaf-level form of the presheaf
pushforward module action. -/
theorem moduleSheafPushforward_underlying_formula {X Y : TopCat.{v}}
    {O : RingSheaf X} (f : X ⟶ Y) (F : Mod O) :
    Nonempty
      ((((moduleSheafPushforward f).obj F).val.presheaf) ≅
        (TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) f).obj F.val.presheaf) := by
  sorry

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
  sorry

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
