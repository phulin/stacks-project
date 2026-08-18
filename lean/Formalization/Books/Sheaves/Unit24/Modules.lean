import Formalization.Books.Sheaves.Unit24.Infrastructure

/-!
# Sheaves on Spaces, Chapter 24: Continuous maps and sheaves of modules

This chapter-facing interface follows `books/sheaves.tex:2682-3029`.  The
module-valued pushforward, pullback, and change-of-scalars constructions were
already implemented canonically in Chapter 22 using Mathlib's
`PresheafOfModules` and `SheafOfModules` APIs.  The declarations below expose
those constructions in the source order and make the scalar unit and counit
maps used by the displayed tensor formulas explicit.
-/

namespace Formalization.Books.Sheaves.Unit24

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10

universe v

noncomputable section

/-! ## Presheaves of modules -/

/-!
The two functors below are the source's `f_*` and `f_p`.  Their codomains
carry the required scalar rings, so the sectionwise actions and their
functoriality are part of the bundled module-valued constructions.
-/

/-- Pushforward of presheaves of rings along `f`. -/
abbrev presheafRingPushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    RingPresheaf.{v, v} X ⥤ RingPresheaf.{v, v} Y :=
  Formalization.Books.Sheaves.Unit22.moduleRingPresheafPushforward f

/-- Pullback presheaf of rings along `f`, defined by the neighbourhood colimit. -/
abbrev presheafRingPullback {X Y : TopCat.{v}} (f : X ⟶ Y) :
    RingPresheaf.{v, v} Y ⥤ RingPresheaf.{v, v} X :=
  Formalization.Books.Sheaves.Unit22.moduleRingPresheafPullback f

/-- Pushforward of presheaves of modules along a specified scalar map. -/
noncomputable abbrev presheafModulePushforwardAlong {X Y : TopCat.{v}}
    {O_X : RingPresheaf.{v, v} X} {O_Y : RingPresheaf.{v, v} Y}
    (f : X ⟶ Y) (α : O_Y ⟶ (presheafRingPushforward f).obj O_X) :
    PMod O_X ⥤ PMod O_Y :=
  Formalization.Books.Sheaves.Unit22.modulePresheafPushforwardAlong f α

/-- The source's module-valued `f_* : PMod(O_X) ⥤ PMod(f_* O_X)`. -/
noncomputable abbrev presheafModulePushforward {X Y : TopCat.{v}}
    {O_X : RingPresheaf.{v, v} X} (f : X ⟶ Y) :
    PMod O_X ⥤ PMod ((presheafRingPushforward f).obj O_X) :=
  Formalization.Books.Sheaves.Unit22.modulePresheafPushforward f

/-- The source's module-valued `f_p : PMod(O_Y) ⥤ PMod(f_p O_Y)`. -/
noncomputable abbrev presheafModulePullback {X Y : TopCat.{v}}
    {O_Y : RingPresheaf.{v, v} Y} (f : X ⟶ Y) :
    PMod O_Y ⥤ PMod ((presheafRingPullback f).obj O_Y) :=
  Formalization.Books.Sheaves.Unit22.modulePresheafPullback f

/-- The sectionwise action on the pushed-forward module presheaf. -/
abbrev presheafModulePushforwardActionAt {X Y : TopCat.{v}}
    {O_X : RingPresheaf.{v, v} X} (f : X ⟶ Y) (F : PMod O_X) (V : Opens Y) :
    ((presheafRingPushforward f).obj O_X).obj (op V) →
      ((presheafModulePushforward f).obj F).obj (op V) →
        ((presheafModulePushforward f).obj F).obj (op V) :=
  Formalization.Books.Sheaves.Unit22.modulePresheafPushforwardAction f F V

/-- The sectionwise action on the pulled-back module presheaf. -/
abbrev presheafModulePullbackActionAt {X Y : TopCat.{v}}
    {O_Y : RingPresheaf.{v, v} Y} (f : X ⟶ Y) (G : PMod O_Y) (U : Opens X) :
    ((presheafRingPullback f).obj O_Y).obj (op U) →
      ((presheafModulePullback f).obj G).obj (op U) →
        ((presheafModulePullback f).obj G).obj (op U) :=
  Formalization.Books.Sheaves.Unit22.modulePresheafPullbackAction f G U

/-!
The ring pushforward is literally evaluation on the inverse image, while the
module pushforward has the same formula after forgetting to additive groups.
-/

@[simp]
theorem presheafRingPushforward_obj_obj {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingPresheaf.{v, v} X) (V : Opens Y) :
    ((presheafRingPushforward f).obj O).obj (op V) =
      O.obj (op ((Opens.map f).obj V)) := rfl

/-- The underlying presheaf formula for module pushforward. -/
theorem presheafModulePushforward_underlying_formula {X Y : TopCat.{v}}
    {O_X : RingPresheaf.{v, v} X} (f : X ⟶ Y) (F : PMod O_X) :
    Nonempty
      ((((presheafModulePushforward f).obj F).presheaf) ≅
        (TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) f).obj F.presheaf) := by
  exact Formalization.Books.Sheaves.Unit22.modulePresheafPushforward_underlying_formula f F

/-- A chosen usable isomorphism for the underlying pushforward formula. -/
noncomputable def presheafModulePushforward_underlyingIso {X Y : TopCat.{v}}
    {O_X : RingPresheaf.{v, v} X} (f : X ⟶ Y) (F : PMod O_X) :
    (((presheafModulePushforward f).obj F).presheaf) ≅
      (TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) f).obj F.presheaf :=
  Classical.choice (presheafModulePushforward_underlying_formula f F)

/-- The filtered-neighbourhood formula for module pullback sections. -/
theorem presheafModulePullback_sections_formula {X Y : TopCat.{v}}
    {O_Y : RingPresheaf.{v, v} Y} (f : X ⟶ Y) (G : PMod O_Y) (U : Opens X) :
    Nonempty
      (((presheafModulePullback f).obj G).presheaf.obj (op U) ≅
        ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) f).obj G.presheaf).obj
          (op U)) := by
  exact Formalization.Books.Sheaves.Unit22.modulePresheafPullback_sections_formula f G U

/-- A chosen usable isomorphism for the underlying pullback-section formula. -/
noncomputable def presheafModulePullback_sectionsIso {X Y : TopCat.{v}}
    {O_Y : RingPresheaf.{v, v} Y} (f : X ⟶ Y) (G : PMod O_Y) (U : Opens X) :
    ((presheafModulePullback f).obj G).presheaf.obj (op U) ≅
      ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) f).obj G.presheaf).obj
        (op U) :=
  Classical.choice (presheafModulePullback_sections_formula f G U)

/-- The filtered neighbourhood category used by the presheaf pullback. -/
abbrev presheafModulePullbackIndex {X Y : TopCat.{v}}
    (f : X ⟶ Y) (U : Opens X) :=
  CostructuredArrow (Opens.map f).op (op U)

/-- The additive-group diagram of sections over neighbourhoods of `f(U)`. -/
abbrev presheafModulePullbackDiagram {X Y : TopCat.{v}}
    (f : X ⟶ Y) {O_Y : RingPresheaf.{v, v} Y} (G : PMod O_Y) (U : Opens X) :=
  CostructuredArrow.proj (Opens.map f).op (op U) ⋙ G.presheaf

/-- The neighbourhood index is filtered. -/
theorem presheafModulePullbackIndex_isFiltered {X Y : TopCat.{v}}
    (f : X ⟶ Y) (U : Opens X) :
    IsFiltered (presheafModulePullbackIndex f U) := by
  exact Formalization.Books.Sheaves.Unit22.algebraicPresheafPullback_index_isFiltered f U

/-- The module pullback section is the filtered neighbourhood colimit. -/
noncomputable def presheafModulePullback_obj_colimitIso {X Y : TopCat.{v}}
    {O_Y : RingPresheaf.{v, v} Y} (f : X ⟶ Y) (G : PMod O_Y) (U : Opens X) :
    ((presheafModulePullback f).obj G).presheaf.obj (op U) ≅
      colimit (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ G.presheaf) := by
  exact (presheafModulePullback_sectionsIso f G U).trans
    (Formalization.Books.Sheaves.Unit22.algebraicPresheafPullback_obj_colimitIso
      f G.presheaf U)

/-! ## Scalar unit, counit, and presheaf adjunction -/

/-- The ring-presheaf pullback/pushforward adjunction. -/
noncomputable abbrev presheafRingPullbackPushforwardAdjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    presheafRingPullback f ⊣ presheafRingPushforward f :=
  TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f

/-- The scalar map `i_O : O ⟶ f_* f_p O`. -/
noncomputable abbrev presheafRingUnit {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingPresheaf.{v, v} Y) :
    O ⟶ (presheafRingPushforward f).obj ((presheafRingPullback f).obj O) :=
  (presheafRingPullbackPushforwardAdjunction f).unit.app O

/-- The scalar map `c_O : f_p f_* O ⟶ O`. -/
noncomputable abbrev presheafRingCounit {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingPresheaf.{v, v} X) :
    (presheafRingPullback f).obj ((presheafRingPushforward f).obj O) ⟶ O :=
  (presheafRingPullbackPushforwardAdjunction f).counit.app O

/-- The presheaf-module pullback/pushforward adjunction. -/
noncomputable abbrev presheafModulePullbackPushforwardAdjunction
    {X Y : TopCat.{v}} {O_Y : RingPresheaf.{v, v} Y} (f : X ⟶ Y) :
    presheafModulePullback f ⊣
      presheafModulePushforwardAlong f (presheafRingUnit f O_Y) :=
  Formalization.Books.Sheaves.Unit22.modulePresheafPullbackPushforwardAdjunction f

/-- The Hom equivalence expressing the presheaf-module adjunction. -/
noncomputable abbrev presheafModuleHomEquiv {X Y : TopCat.{v}}
    {O_Y : RingPresheaf.{v, v} Y} (f : X ⟶ Y)
    (G : PMod O_Y) (F : PMod ((presheafRingPullback f).obj O_Y)) :
    ((presheafModulePullback f).obj G ⟶ F) ≃
      (G ⟶ (presheafModulePushforwardAlong f
        (presheafRingUnit f O_Y)).obj F) :=
  (presheafModulePullbackPushforwardAdjunction f).homEquiv G F

/-- The unit of the presheaf-module adjunction. -/
noncomputable abbrev presheafModuleUnit {X Y : TopCat.{v}}
    {O_Y : RingPresheaf.{v, v} Y} (f : X ⟶ Y) (G : PMod O_Y) :
    G ⟶ (presheafModulePushforwardAlong f (presheafRingUnit f O_Y)).obj
      ((presheafModulePullback f).obj G) :=
  (presheafModulePullbackPushforwardAdjunction f).unit.app G

/-- The counit of the presheaf-module adjunction. -/
noncomputable abbrev presheafModuleCounit {X Y : TopCat.{v}}
    {O_Y : RingPresheaf.{v, v} Y} (f : X ⟶ Y)
    (F : PMod ((presheafRingPullback f).obj O_Y)) :
    (presheafModulePullback f).obj
        ((presheafModulePushforwardAlong f (presheafRingUnit f O_Y)).obj F) ⟶ F :=
  (presheafModulePullbackPushforwardAdjunction f).counit.app F

/-! ## Presheaf tensor products and change of scalars -/

/-- Extension of scalars for presheaves of modules. -/
noncomputable abbrev presheafModuleExtensionOfScalars {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{v, v} X} (α : O₁ ⟶ O₂) :
    PMod O₁ ⥤ PMod O₂ :=
  Formalization.Books.Sheaves.Unit22.modulePresheafExtensionOfScalars α

/-- The source's `O ⊗_{p, f_p f_* O} f_p G`. -/
noncomputable abbrev presheafModuleTensorOverPushforward {X Y : TopCat.{v}}
    {O_X : RingPresheaf.{v, v} X} (f : X ⟶ Y)
    (G : PMod ((presheafRingPushforward f).obj O_X)) : PMod O_X :=
  Formalization.Books.Sheaves.Unit22.modulePresheafTensorOverPushforward f G

/-- The tensor/pushforward Hom equivalence for presheaves of modules. -/
noncomputable abbrev presheafModuleTensorHomEquiv {X Y : TopCat.{v}}
    {O_X : RingPresheaf.{v, v} X} (f : X ⟶ Y)
    (G : PMod ((presheafRingPushforward f).obj O_X)) (F : PMod O_X) :
    (presheafModuleTensorOverPushforward f G ⟶ F) ≃
      (G ⟶ (presheafModulePushforward f).obj F) :=
  Formalization.Books.Sheaves.Unit22.modulePresheafTensorHomEquiv f G F

/-! ## Sheaves of modules -/

/-- Pushforward of sheaves of rings. -/
abbrev sheafRingPushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    RingSheaf X ⥤ RingSheaf Y :=
  Formalization.Books.Sheaves.Unit22.moduleRingSheafPushforward f

/-- Pullback of sheaves of rings. -/
abbrev sheafRingPullback {X Y : TopCat.{v}} (f : X ⟶ Y) :
    RingSheaf Y ⥤ RingSheaf X :=
  Formalization.Books.Sheaves.Unit22.moduleRingSheafPullback f

/-- The sheaf-ring pullback/pushforward adjunction. -/
noncomputable abbrev sheafRingPullbackPushforwardAdjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    sheafRingPullback f ⊣ sheafRingPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f

/-- The sheaf-ring unit `O_Y ⟶ f_* f⁻¹ O_Y`. -/
noncomputable abbrev sheafRingUnit {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingSheaf Y) :
    O ⟶ (sheafRingPushforward f).obj ((sheafRingPullback f).obj O) :=
  Formalization.Books.Sheaves.Unit22.moduleSheafPullbackUnit f O

/-- The sheaf-ring counit `f⁻¹ f_* O_X ⟶ O_X`. -/
noncomputable abbrev sheafRingCounit {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingSheaf X) :
    (sheafRingPullback f).obj ((sheafRingPushforward f).obj O) ⟶ O :=
  (sheafRingPullbackPushforwardAdjunction f).counit.app O

/-- Pushforward of sheaves of modules along a specified scalar map. -/
noncomputable abbrev sheafModulePushforwardAlong {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} (f : X ⟶ Y)
    (α : O_Y ⟶ (sheafRingPushforward f).obj O_X) :
    Mod O_X ⥤ Mod O_Y :=
  Formalization.Books.Sheaves.Unit22.moduleSheafPushforwardAlong f α

/-- The source's module-valued `f_* : Mod(O_X) ⥤ Mod(f_* O_X)`. -/
noncomputable abbrev sheafModulePushforward {X Y : TopCat.{v}}
    {O_X : RingSheaf X} (f : X ⟶ Y) :
    Mod O_X ⥤ Mod ((sheafRingPushforward f).obj O_X) :=
  Formalization.Books.Sheaves.Unit22.moduleSheafPushforward f

/-- Pullback of sheaves of modules along a specified scalar map. -/
noncomputable abbrev sheafModulePullbackAlong {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} (f : X ⟶ Y)
    (α : O_Y ⟶ (sheafRingPushforward f).obj O_X)
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)] :
    Mod O_Y ⥤ Mod O_X :=
  Formalization.Books.Sheaves.Unit22.moduleSheafPullbackAlong f α

/-- The source's module-valued `f⁻¹ : Mod(O_Y) ⥤ Mod(f⁻¹ O_Y)`. -/
noncomputable abbrev sheafModulePullback {X Y : TopCat.{v}}
    {O_Y : RingSheaf Y} (f : X ⟶ Y)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (sheafRingUnit f O_Y)).IsRightAdjoint)] :
    Mod O_Y ⥤ Mod ((sheafRingPullback f).obj O_Y) :=
  Formalization.Books.Sheaves.Unit22.moduleSheafPullback f

/-- The underlying presheaf formula for sheaf module pushforward. -/
theorem sheafModulePushforward_underlying_formula {X Y : TopCat.{v}}
    {O_X : RingSheaf X} (f : X ⟶ Y) (F : Mod O_X) :
    Nonempty
      ((((sheafModulePushforward f).obj F).val.presheaf) ≅
        (TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) f).obj F.val.presheaf) := by
  exact Formalization.Books.Sheaves.Unit22.moduleSheafPushforward_underlying_formula f F

/-- A chosen usable isomorphism for the underlying sheaf pushforward formula. -/
noncomputable def sheafModulePushforward_underlyingIso {X Y : TopCat.{v}}
    {O_X : RingSheaf X} (f : X ⟶ Y) (F : Mod O_X) :
    (((sheafModulePushforward f).obj F).val.presheaf) ≅
      (TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) f).obj F.val.presheaf :=
  Classical.choice (sheafModulePushforward_underlying_formula f F)

/-- Pullback of module sheaves is the sheafification of the presheaf pullback. -/
noncomputable abbrev sheafModulePullback_sheafificationIso {X Y : TopCat.{v}}
    {O_Y : RingSheaf Y} (f : X ⟶ Y) (G : Mod O_Y)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (sheafRingUnit f O_Y)).IsRightAdjoint)]
    [(PresheafOfModules.pushforward (sheafRingUnit f O_Y).hom).IsRightAdjoint] :
    (sheafModulePullback f).obj G ≅
      (SheafOfModules.forget O_Y ⋙
        PresheafOfModules.pullback (sheafRingUnit f O_Y).hom ⋙
        PresheafOfModules.sheafification
          (R₀ := ((sheafRingPullback f).obj O_Y).obj) (𝟙 _)).obj G :=
  Formalization.Books.Sheaves.Unit22.moduleSheafPullback_sheafificationIso f G

/-! ## Sheaf adjunctions and tensor products -/

/-- The sheaf-module pullback/pushforward adjunction. -/
noncomputable abbrev sheafModulePullbackPushforwardAdjunction
    {X Y : TopCat.{v}} {O_Y : RingSheaf Y} (f : X ⟶ Y)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (sheafRingUnit f O_Y)).IsRightAdjoint)] :
    sheafModulePullback f ⊣
      sheafModulePushforwardAlong f (sheafRingUnit f O_Y) :=
  Formalization.Books.Sheaves.Unit22.moduleSheafPullbackPushforwardAdjunction f

/-- The Hom equivalence expressing the sheaf-module adjunction. -/
noncomputable abbrev sheafModuleHomEquiv {X Y : TopCat.{v}}
    {O_Y : RingSheaf Y} (f : X ⟶ Y) (G : Mod O_Y)
    (F : Mod ((sheafRingPullback f).obj O_Y))
    [((SheafOfModules.pushforward (F := Opens.map f)
      (sheafRingUnit f O_Y)).IsRightAdjoint)] :
    ((sheafModulePullback f).obj G ⟶ F) ≃
      (G ⟶ (sheafModulePushforwardAlong f
        (sheafRingUnit f O_Y)).obj F) :=
  (sheafModulePullbackPushforwardAdjunction f).homEquiv G F

/-- The unit of the sheaf-module adjunction. -/
noncomputable abbrev sheafModuleUnit {X Y : TopCat.{v}}
    {O_Y : RingSheaf Y} (f : X ⟶ Y) (G : Mod O_Y)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (sheafRingUnit f O_Y)).IsRightAdjoint)] :
    G ⟶ (sheafModulePushforwardAlong f (sheafRingUnit f O_Y)).obj
      ((sheafModulePullback f).obj G) :=
  (sheafModulePullbackPushforwardAdjunction f).unit.app G

/-- The counit of the sheaf-module adjunction. -/
noncomputable abbrev sheafModuleCounit {X Y : TopCat.{v}}
    {O_Y : RingSheaf Y} (f : X ⟶ Y)
    (F : Mod ((sheafRingPullback f).obj O_Y))
    [((SheafOfModules.pushforward (F := Opens.map f)
      (sheafRingUnit f O_Y)).IsRightAdjoint)] :
    (sheafModulePullback f).obj
        ((sheafModulePushforwardAlong f (sheafRingUnit f O_Y)).obj F) ⟶ F :=
  (sheafModulePullbackPushforwardAdjunction f).counit.app F

/-- The source's `O_X ⊗_{f⁻¹ f_* O_X} f⁻¹ G`. -/
noncomputable abbrev sheafModuleTensorOverPushforward {X Y : TopCat.{v}}
    {O_X : RingSheaf X} (f : X ⟶ Y)
    (G : Mod ((sheafRingPushforward f).obj O_X))
    [((SheafOfModules.pushforward (F := Opens.map f)
      (𝟙 ((sheafRingPushforward f).obj O_X))).IsRightAdjoint)] :
    Mod O_X :=
  Formalization.Books.Sheaves.Unit22.moduleSheafTensorOverPushforward f G

/-- The tensor/pushforward Hom equivalence for sheaf modules. -/
noncomputable abbrev sheafModuleTensorHomEquiv {X Y : TopCat.{v}}
    {O_X : RingSheaf X} (f : X ⟶ Y)
    (G : Mod ((sheafRingPushforward f).obj O_X)) (F : Mod O_X)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (𝟙 ((sheafRingPushforward f).obj O_X))).IsRightAdjoint)] :
    (sheafModuleTensorOverPushforward f G ⟶ F) ≃
      (G ⟶ (sheafModulePushforward f).obj F) :=
  Formalization.Books.Sheaves.Unit22.moduleSheafTensorHomEquiv f G F

/-! The final warning in the source is a scalar-category mismatch, not a
claim that the two untyped functors do not exist. -/

/-- The scalar mismatch obstructing an untyped module adjunction in general. -/
def plainModulePushPullScalarMismatch {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O_X : RingSheaf X) (O_Y : RingSheaf Y) : Prop :=
  Formalization.Books.Sheaves.Unit22.plainModulePushPullScalarMismatch f O_X O_Y

end

end Formalization.Books.Sheaves.Unit24
