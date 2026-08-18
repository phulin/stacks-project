import Formalization.Books.Sheaves.Unit31.Infrastructure
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks

/-!
# Shared infrastructure for Chapter 32: Closed immersions

The direct image along a closed inclusion is represented by Mathlib's
pushforward functor.  The stalk and essential-image descriptions from the
source are recorded as interfaces, while the functorial constructions use
the canonical presheaf and sheaf APIs.
-/

namespace Formalization.Books.Sheaves.Unit22

-- The historical namespace is retained for API compatibility.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit10
open scoped ZeroObject

universe v u

noncomputable section

/-! ## The closed subspace and its direct/inverse images -/

/-- The topological space carried by a closed subset. -/
abbrev closedSubspace {X : TopCat.{v}} (Z : Set X) : TopCat.{v} :=
  TopCat.of Z

/-- The canonical inclusion of a subset as a topological subspace. -/
abbrev closedInclusion {X : TopCat.{v}} (Z : Set X) : closedSubspace Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Direct image of presheaves along a closed inclusion. -/
abbrev closedPresheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z) :
    TopCat.Presheaf C (closedSubspace Z) ⥤ TopCat.Presheaf C X :=
  TopCat.Presheaf.pushforward C (closedInclusion Z)

/-- Inverse image of presheaves along a closed inclusion. -/
noncomputable abbrev closedPresheafRestriction (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z) :
    TopCat.Presheaf C X ⥤ TopCat.Presheaf C (closedSubspace Z) :=
  TopCat.Presheaf.pullback C (closedInclusion Z)

/-- Direct image of sheaves along a closed inclusion. -/
abbrev closedSheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z) :
    TopCat.Sheaf C (closedSubspace Z) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pushforward C (closedInclusion Z)

/-- Direct image of sheaves valued in a category of algebraic structures. -/
abbrev closedAlgebraicSheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z) :
    TopCat.Sheaf C (closedSubspace Z) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pushforward C (closedInclusion Z)

/-- Inverse image of set-valued sheaves along a closed inclusion. -/
noncomputable abbrev closedSetSheafRestriction {X : TopCat.{v}} (Z : Set X)
    (_hZ : IsClosed Z) :
    TopCat.Sheaf (Type v) X ⥤ TopCat.Sheaf (Type v) (closedSubspace Z) :=
  TopCat.Sheaf.pullback (Type v) (closedInclusion Z)

/-- Inverse image of abelian sheaves along a closed inclusion. -/
noncomputable abbrev closedAbelianSheafRestriction {X : TopCat.{v}} (Z : Set X)
    (_hZ : IsClosed Z) :
    TopCat.Sheaf (AddCommGrpCat.{v}) X ⥤
      TopCat.Sheaf (AddCommGrpCat.{v}) (closedSubspace Z) :=
  TopCat.Sheaf.pullback (AddCommGrpCat.{v}) (closedInclusion Z)

/-- Inverse image of algebraic-structure sheaves along a closed inclusion. -/
noncomputable abbrev closedAlgebraicSheafRestriction
    (C : Type u) [Category.{v} C] [HasColimits C] [HasLimits C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z) :
    AlgebraicSheaf C X ⥤ AlgebraicSheaf C (closedSubspace Z) :=
  algebraicSheafPullback C (closedInclusion Z)

@[simp]
theorem closedPresheafDirectImage_obj (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Presheaf C (closedSubspace Z)) (V : Opens X) :
    ((closedPresheafDirectImage C Z hZ).obj F).obj (op V) =
      F.obj (op ((Opens.map (closedInclusion Z)).obj V)) := rfl

/-! ## Stalks and restriction identities -/

private theorem closedSheafDirectImage_stalkIso_terminal_of_not_mem
    {C : Type u} [Category.{v} C] [HasColimits C] [HasTerminal C]
    {X : TopCat.{v}} {Z : Set X} (hZ : IsClosed Z)
    (F : TopCat.Sheaf C (closedSubspace Z)) {x : X} (hx : x ∉ Z) :
    Nonempty (((closedSheafDirectImage C Z hZ).obj F).presheaf.stalk x ≅ (⊤_ C)) := by
  let P : TopCat.Presheaf C X :=
    ((closedSheafDirectImage C Z hZ).obj F).presheaf
  have h1 : ∃ U : OpenNhds x,
      (Opens.map (closedInclusion Z)).obj U.1 = ⊥ := by
    rcases mem_nhds_iff.mp (hZ.compl_mem_nhds hx) with ⟨U, hU, hUo, hxU⟩
    let U' : OpenNhds x := ⟨⟨U, hUo⟩, hxU⟩
    refine ⟨U', ?_⟩
    ext z
    change (z : X) ∈ U ↔ z ∈ (⊥ : Opens (TopCat.of Z))
    constructor
    · intro hz
      exact (hU hz) z.property
    · intro hz
      exact hz.elim
  let c : Cocone ((OpenNhds.inclusion x).op ⋙ P) :=
    { pt := ⊤_ C
      ι :=
        { app := fun _ => terminal.from _
          naturality := fun _ _ _ => terminalIsTerminal.hom_ext _ _ } }
  rcases h1 with ⟨U, hU⟩
  have hUt : IsTerminal (P.obj (op U.1)) := by
    change IsTerminal (F.presheaf.obj (op ((Opens.map (closedInclusion Z)).obj U.1)))
    rw [hU]
    exact F.isTerminalOfEmpty
  have hUt' : IsTerminal (((OpenNhds.inclusion x).op ⋙ P).obj (op U)) := by
    change IsTerminal (P.obj (op U.1))
    exact hUt
  let e : ((OpenNhds.inclusion x).op ⋙ P).obj (op U) ≅ (⊤_ C) :=
    hUt'.uniqueUpToIso terminalIsTerminal
  have hUdis : ∀ z : Z, (z : X) ∉ U.1 := by
    intro z hz
    have hz' : z ∈ (Opens.map (closedInclusion Z)).obj U.1 := by
      change (z : X) ∈ U.1
      exact hz
    rw [hU] at hz'
    exact hz'.elim
  have hc : IsColimit c := by
    refine
      { desc := fun d => e.inv ≫ d.ι.app (op U)
        fac := fun d V => by
          change _ = d.ι.app (op V.unop)
          simp only [← d.w (homOfLE <| @inf_le_left _ _ U V.unop).op,
            ← d.w (homOfLE <| @inf_le_right _ _ U V.unop).op, ← Category.assoc]
          have hWt : IsTerminal
              (((OpenNhds.inclusion x).op ⋙ P).obj (op (U ⊓ V.unop))) := by
            change IsTerminal
              (F.presheaf.obj (op ((Opens.map (closedInclusion Z)).obj
                (U.1 ⊓ V.unop.1))))
            apply F.isTerminalOfEqEmpty
            ext z
            change ((z : X) ∈ U.1 ∧ (z : X) ∈ V.unop.1) ↔ False
            constructor
            · intro hz
              exact hUdis z hz.1
            · intro hz
              exact hz.elim
          have hm :
              (c.ι.app V ≫ e.inv) ≫
                  ((OpenNhds.inclusion x).op ⋙ P).map
                    (homOfLE <| @inf_le_left _ _ U V.unop).op =
                ((OpenNhds.inclusion x).op ⋙ P).map
                (homOfLE <| @inf_le_right _ _ U V.unop).op :=
            hWt.hom_ext _ _
          change
            ((c.ι.app V ≫ e.inv) ≫
                ((OpenNhds.inclusion x).op ⋙ P).map
                  (homOfLE <| @inf_le_left _ _ U V.unop).op) ≫
                d.ι.app (op (U ⊓ V.unop)) =
              ((OpenNhds.inclusion x).op ⋙ P).map
                (homOfLE <| @inf_le_right _ _ U V.unop).op ≫
                d.ι.app (op (U ⊓ V.unop))
          rw [hm]
        uniq := fun d f H => by
          rw [← cancel_epi e.hom]
          let j : (OpenNhds x)ᵒᵖ := Opposite.op U
          have Hj : c.ι.app j ≫ f = d.ι.app j := H j
          have he : c.ι.app j = e.hom := terminalIsTerminal.hom_ext _ _
          simpa [he, Category.assoc] using Hj }
  exact ⟨colimit.isoColimitCocone ⟨_, hc⟩⟩

/-- The set-valued direct image has a singleton stalk off the closed subset. -/
theorem closedSetSheafDirectImage_stalk_outside {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : TopCat.Sheaf (Type v) (closedSubspace Z))
    (x : X) (hx : x ∉ Z) :
    Nonempty (((closedSheafDirectImage (Type v) Z hZ).obj F).presheaf.stalk x ≃
      PUnit.{v}) := by
  rcases closedSheafDirectImage_stalkIso_terminal_of_not_mem hZ F hx with ⟨e⟩
  exact ⟨e.toEquiv.trans (Types.terminalIso.toEquiv.trans
    (Equiv.punitEquivPUnit.{v + 1, v}))⟩

/-- On the closed subset, the direct-image stalk is the original stalk. -/
theorem closedSetSheafDirectImage_stalk_inside {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : TopCat.Sheaf (Type v) (closedSubspace Z))
    (x : X) (hx : x ∈ Z) :
    Nonempty (((closedSheafDirectImage (Type v) Z hZ).obj F).presheaf.stalk x ≃
      F.presheaf.stalk ⟨x, hx⟩) := by
  let hIso : IsIso (TopCat.Presheaf.stalkPushforward (Type v)
      (closedInclusion Z) F.presheaf ⟨x, hx⟩) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (Type v) hZ.isClosedEmbedding_subtypeVal.isInducing F.presheaf ⟨x, hx⟩
  change Nonempty (((TopCat.Presheaf.pushforward (Type v)
      (closedInclusion Z)).obj F.presheaf).stalk x ≃ F.presheaf.stalk ⟨x, hx⟩)
  exact ⟨(@asIso _ _ _ _ (TopCat.Presheaf.stalkPushforward (Type v)
      (closedInclusion Z) F.presheaf ⟨x, hx⟩) hIso).toEquiv⟩

/-- The additive direct image has a zero stalk off the closed subset. -/
theorem closedAbelianSheafDirectImage_stalk_outside {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : TopCat.Sheaf (AddCommGrpCat.{v}) (closedSubspace Z))
    (x : X) (hx : x ∉ Z) :
    Nonempty (((closedSheafDirectImage AddCommGrpCat Z hZ).obj F).presheaf.stalk x ≅
      (0 : AddCommGrpCat.{v})) := by
  rcases closedSheafDirectImage_stalkIso_terminal_of_not_mem hZ F hx with ⟨e⟩
  exact ⟨e.trans HasZeroObject.zeroIsoTerminal.symm⟩

/-- On the closed subset, the additive direct-image stalk is the original
stalk. -/
theorem closedAbelianSheafDirectImage_stalk_inside {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : TopCat.Sheaf (AddCommGrpCat.{v}) (closedSubspace Z))
    (x : X) (hx : x ∈ Z) :
    Nonempty (((closedSheafDirectImage AddCommGrpCat Z hZ).obj F).presheaf.stalk x ≅
      F.presheaf.stalk ⟨x, hx⟩) := by
  let hIso : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat
      (closedInclusion Z) F.presheaf ⟨x, hx⟩) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat hZ.isClosedEmbedding_subtypeVal.isInducing F.presheaf ⟨x, hx⟩
  change Nonempty (((TopCat.Presheaf.pushforward AddCommGrpCat
      (closedInclusion Z)).obj F.presheaf).stalk x ≅ F.presheaf.stalk ⟨x, hx⟩)
  exact ⟨(@asIso _ _ _ _ (TopCat.Presheaf.stalkPushforward AddCommGrpCat
      (closedInclusion Z) F.presheaf ⟨x, hx⟩) hIso)⟩

/-- The generic direct-image stalk is the original stalk on the closed subset. -/
theorem closedAlgebraicSheafDirectImage_stalk_inside
    (C : Type u) [Category.{v} C] [HasColimits C]
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf C (closedSubspace Z)) (x : X) (hx : x ∈ Z) :
    Nonempty (((closedAlgebraicSheafDirectImage C Z hZ).obj F).presheaf.stalk x ≅
      F.presheaf.stalk ⟨x, hx⟩) := by
  let hIso : IsIso (TopCat.Presheaf.stalkPushforward C
      (closedInclusion Z) F.presheaf ⟨x, hx⟩) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      C hZ.isClosedEmbedding_subtypeVal.isInducing F.presheaf ⟨x, hx⟩
  change Nonempty (((TopCat.Presheaf.pushforward C
      (closedInclusion Z)).obj F.presheaf).stalk x ≅ F.presheaf.stalk ⟨x, hx⟩)
  exact ⟨(@asIso _ _ _ _ (TopCat.Presheaf.stalkPushforward C
      (closedInclusion Z) F.presheaf ⟨x, hx⟩) hIso)⟩

/-- Inverse image followed by direct image is the identity for set-valued sheaves. -/
private theorem closedSheafRestriction_directImage_counit_isIso
    {C : Type u} [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)]
    [ConcreteCategory.{v} C FC] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {Z : Set X} (hZ : IsClosed Z) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C
      (closedInclusion Z)).counit) := by
  let f : TopCat.of Z ⟶ X := closedInclusion Z
  have hpmap (F : TopCat.Sheaf C (TopCat.of Z)) (z : Z) :
      (TopCat.Presheaf.stalkFunctor (C := C) (X := TopCat.of Z) z).map
          ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).counit.app
            F.presheaf) =
        (TopCat.Presheaf.stalkPullbackIso C f
            ((TopCat.Presheaf.pushforward C f).obj F.presheaf) z).inv ≫
          TopCat.Presheaf.stalkPushforward C f F.presheaf z := by
    apply TopCat.Presheaf.stalk_hom_ext _
    intro U hxU
    rw [TopCat.Presheaf.stalkFunctor_map_germ]
    simp only [Functor.id_obj]
    dsimp [TopCat.Presheaf.stalkPullbackIso]
    rw [← Category.assoc]
    apply TopCat.Presheaf.pullback_obj_obj_ext (op U)
    intro V hV
    simp only [TopCat.Presheaf.germ_stalkPullbackInv]
    have hnat := ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).counit.app
      F.presheaf).naturality (homOfLE hV).op
    have hnat' :
        ((TopCat.Presheaf.pullback C f).obj
            ((TopCat.Presheaf.pushforward C f).obj F.presheaf)).map
            (homOfLE hV).op ≫
          ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).counit.app
            F.presheaf).app (op U) =
        ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).counit.app
            F.presheaf).app (op ((Opens.map f).obj V)) ≫
          F.presheaf.map (homOfLE hV).op := by
      simpa only [Functor.comp_obj, Functor.id_obj] using hnat
    have hnat'' :
        ((TopCat.Presheaf.pullback C f).obj
            ((TopCat.Presheaf.pushforward C f).obj F.presheaf)).map
            (homOfLE hV).op ≫
          ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).counit.app
            F.presheaf).app (op U) ≫ F.presheaf.germ U z hxU =
        ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).counit.app
            F.presheaf).app (op ((Opens.map f).obj V)) ≫
          F.presheaf.map (homOfLE hV).op ≫ F.presheaf.germ U z hxU := by
      rw [← Category.assoc, hnat']
      simp only [Category.assoc]
    rw [hnat'']
    have htri' :
        ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app
            ((TopCat.Presheaf.pushforward C f).obj F.presheaf)).app (op V) ≫
          ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).counit.app
            F.presheaf).app (op ((Opens.map f).obj V)) =
          (NatTrans.id ((TopCat.Presheaf.pushforward C f).obj F.presheaf)).app
            (op V) := by
      have htri :=
        (TopCat.Presheaf.pullbackPushforwardAdjunction C f).right_triangle_components
          F.presheaf
      convert congr_app htri (op V) using 1
      all_goals rfl
    rw [← Category.assoc, htri']
    rw [TopCat.Presheaf.pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk_assoc]
    have hzV' := hV hxU
    change (ConcreteCategory.hom f) z ∈ V at hzV'
    have hres := F.presheaf.germ_res (homOfLE hV) z hxU
    have hpush := TopCat.Presheaf.stalkPushforward_germ C f F.presheaf V z hzV'
    simpa using hres.trans hpush.symm
  have hsheafify {P Q : TopCat.Presheaf C (TopCat.of Z)}
      (φ : P ⟶ Q) (hφ : ∀ z : Z, IsIso
        ((TopCat.Presheaf.stalkFunctor (C := C) (X := TopCat.of Z) z).map φ)) :
      IsIso ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of Z)) C).map φ) := by
    let K := Opens.grothendieckTopology (TopCat.of Z)
    let : ∀ z : Z, IsIso
        ((TopCat.Presheaf.stalkFunctor (C := C) (X := TopCat.of Z) z).map
          ((presheafToSheaf K C).map φ).hom) := by
      intro z
      let uP := (TopCat.Presheaf.stalkFunctor C z).map
        (toSheafify K P)
      let uQ := (TopCat.Presheaf.stalkFunctor C z).map
        (toSheafify K Q)
      let m := (TopCat.Presheaf.stalkFunctor C z).map
        ((presheafToSheaf K C).map φ).hom
      let p := (TopCat.Presheaf.stalkFunctor C z).map φ
      let : IsIso uP := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        (X := TopCat.of Z) (p₀ := z) (C := C) P
      let : IsIso uQ := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        (X := TopCat.of Z) (p₀ := z) (C := C) Q
      let : IsIso p := hφ z
      have hcomp : uP ≫ m = p ≫ uQ := by
        have h := congrArg (fun q =>
          (TopCat.Presheaf.stalkFunctor C z).map q)
          ((sheafificationAdjunction K C).unit.naturality φ)
        dsimp [uP, uQ, m, p] at h
        rw [Functor.map_comp, Functor.map_comp] at h
        exact h.symm
      have hm : m = inv uP ≫ p ≫ uQ := by
        apply (IsIso.eq_inv_comp uP).2
        exact hcomp
      change IsIso m
      rw [hm]
      infer_instance
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  let K := Opens.grothendieckTopology (TopCat.of Z)
  let f₀ : Opens X ⥤ Opens (TopCat.of Z) := Opens.map f
  let F' : Sheaf K C := F
  let c₀ := (f₀.op.lanAdjunction C).counit.app F'.obj
  have hc₀ : IsIso ((presheafToSheaf K C).map c₀) := by
    apply hsheafify c₀
    intro z
    have hh : IsIso
        ((TopCat.Presheaf.stalkFunctor (C := C) (X := TopCat.of Z) z).map
          ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).counit.app
            F.presheaf)) := by
      rw [hpmap F z]
      let : IsIso (TopCat.Presheaf.stalkPushforward C f F.presheaf z) :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
          C hZ.isClosedEmbedding_subtypeVal.isInducing F.presheaf z
      let : IsIso (TopCat.Presheaf.stalkPullbackIso C f
          ((TopCat.Presheaf.pushforward C f).obj F.presheaf) z).inv := by
        infer_instance
      exact IsIso.comp_isIso'
        (by infer_instance : IsIso
          (TopCat.Presheaf.stalkPullbackIso C f
            ((TopCat.Presheaf.pushforward C f).obj F.presheaf) z).inv)
        (by infer_instance : IsIso
          (TopCat.Presheaf.stalkPushforward C f F.presheaf z))
    simpa [c₀, f₀, TopCat.Presheaf.pullbackPushforwardAdjunction,
      TopCat.Presheaf.pullback] using hh
  have hc₁ : IsIso ((sheafificationAdjunction K C).counit.app F') := by
    infer_instance
  let adj₀ := (f₀.op.lanAdjunction C).comp
    (sheafificationAdjunction K C)
  have hcomp : adj₀.counit.app F' =
      (presheafToSheaf K C).map c₀ ≫
        (sheafificationAdjunction K C).counit.app F' := by
    simp [adj₀, c₀, Adjunction.comp_counit_app]
  have hc : IsIso (adj₀.counit.app F') := by
    rw [hcomp]
    infer_instance
  let J := Opens.grothendieckTopology X
  let : f₀.IsContinuous J K := by
    dsimp [f₀, f]
    apply Functor.isContinuous_of_coverPreserving
    · exact compatiblePreserving_opens_map (closedInclusion Z)
    · exact coverPreserving_opens_map (closedInclusion Z)
  let adj₂ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    f₀ C J K
  let : IsIso (adj₀.counit.app F') := hc
  have hc₂ : IsIso (adj₂.counit.app F') := by
    let L₃ := Functor.sheafPullbackConstruction.sheafPullback f₀ C J K
    let R₃ := Functor.sheafPushforwardContinuous f₀ C J K
    let comm1₃ :
        sheafToPresheaf J C ⋙
            (f₀.op.lan ⋙ presheafToSheaf K C) ≅
          L₃ ⋙ 𝟭 (Sheaf K C) := by
      dsimp [L₃, Functor.sheafPullbackConstruction.sheafPullback]
      exact (Functor.rightUnitor _).symm
    let adj₃ : L₃ ⊣ R₃ :=
      adj₀.restrictFullyFaithful
        (fullyFaithfulSheafToPresheaf J C) (Functor.FullyFaithful.id _)
        (L := L₃) (R := R₃) comm1₃ (Iso.refl _)
    have hmap := Adjunction.map_restrictFullyFaithful_counit_app
      (adj := adj₀)
      (hiC := fullyFaithfulSheafToPresheaf J C)
      (hiD := Functor.FullyFaithful.id _)
      (L := L₃) (R := R₃) (comm1 := comm1₃) (comm2 := Iso.refl _) F'
    have hc₃ : IsIso (adj₃.counit.app F') := by
      have hmap' := hmap
      let : IsIso (comm1₃.inv.app (R₃.obj F')) :=
        (comm1₃.app (R₃.obj F')).isIso_inv
      change IsIso ((𝟭 (Sheaf K C)).map (adj₃.counit.app F'))
      rw [hmap']
      have h₁ : IsIso (comm1₃.inv.app (R₃.obj F')) := by
        exact (comm1₃.app (R₃.obj F')).isIso_inv
      have h₂₀ : IsIso ((Iso.refl
          (𝟭 (Sheaf K C) ⋙ sheafToPresheaf K C ⋙
            (Functor.whiskeringLeft (Opens X)ᵒᵖ
              (Opens (TopCat.of Z))ᵒᵖ C).obj f₀.op)).inv.app F') := by
        infer_instance
      let : IsIso ((Iso.refl
          (𝟭 (Sheaf K C) ⋙ sheafToPresheaf K C ⋙
            (Functor.whiskeringLeft (Opens X)ᵒᵖ
              (Opens (TopCat.of Z))ᵒᵖ C).obj f₀.op)).inv.app F') := h₂₀
      have h₂ : IsIso ((f₀.op.lan ⋙ presheafToSheaf K C).map
          ((Iso.refl
            (𝟭 (Sheaf K C) ⋙ sheafToPresheaf K C ⋙
              (Functor.whiskeringLeft (Opens X)ᵒᵖ
                (Opens (TopCat.of Z))ᵒᵖ C).obj f₀.op)).inv.app F')) :=
        Functor.map_isIso _ _
      have h₃ : IsIso (adj₀.counit.app ((𝟭 (Sheaf K C)).obj F')) := by
        simpa using hc
      exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h₂ h₃)
    have huniq := Adjunction.leftAdjointUniq_hom_app_counit adj₂ adj₃ F'
    let : IsIso (adj₃.counit.app F') := hc₃
    rw [← huniq]
    infer_instance
  let : IsIso (adj₂.counit.app F') := hc₂
  let e₀ := (TopCat.Sheaf.pullbackPushforwardAdjunction C f).leftAdjointUniq adj₂
  have huniq₀ := Adjunction.leftAdjointUniq_hom_app_counit
    (TopCat.Sheaf.pullbackPushforwardAdjunction C f) adj₂ F'
  rw [← huniq₀]
  let : IsIso (e₀.hom.app ((TopCat.Sheaf.pushforward C f).obj F')) :=
    (e₀.app ((TopCat.Sheaf.pushforward C f).obj F')).isIso_hom
  change IsIso (e₀.hom.app ((TopCat.Sheaf.pushforward C f).obj F') ≫ adj₂.counit.app F')
  exact IsIso.comp_isIso'
    (e₀.app ((TopCat.Sheaf.pushforward C f).obj F')).isIso_hom hc₂

theorem closedSetSheafRestriction_directImage_iso {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : TopCat.Sheaf (Type v) (closedSubspace Z)) :
    Nonempty ((closedSetSheafRestriction Z hZ).obj
      ((closedSheafDirectImage (Type v) Z hZ).obj F) ≅ F) := by
  let : IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      (closedInclusion Z)).counit) :=
    closedSheafRestriction_directImage_counit_isIso hZ
  exact ⟨asIso ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
    (closedInclusion Z)).counit.app F)⟩

/-- Inverse image followed by direct image is the identity for abelian sheaves. -/
theorem closedAbelianSheafRestriction_directImage_iso {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : TopCat.Sheaf (AddCommGrpCat.{v}) (closedSubspace Z)) :
    Nonempty ((closedAbelianSheafRestriction Z hZ).obj
      ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj F) ≅ F) := by
  let : IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
      (closedInclusion Z)).counit) :=
    closedSheafRestriction_directImage_counit_isIso hZ
  exact ⟨asIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
    (closedInclusion Z)).counit.app F)⟩

theorem closedAlgebraicSheafRestriction_directImage_iso
    (C : Type u) [Category.{v} C] [HasColimits C] [HasLimits C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : AlgebraicSheaf C (closedSubspace Z)) :
    Nonempty ((closedAlgebraicSheafRestriction C Z hZ).obj
      ((closedAlgebraicSheafDirectImage C Z hZ).obj F) ≅ F) := by
  let : IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C
      (closedInclusion Z)).counit) :=
    closedSheafRestriction_directImage_counit_isIso hZ
  exact ⟨asIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C
    (closedInclusion Z)).counit.app F)⟩

/-! ## Essential images -/

/-- The set-valued stalk condition characterizing a closed direct image. -/
def ClosedSingletonStalkCondition {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z)
    (G : TopCat.Sheaf (Type v) X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty (G.presheaf.stalk x ≃ PUnit.{v})

/-- Direct image along a closed inclusion is fully faithful on sheaves of sets. -/
theorem closedSetSheafDirectImage_fullFaithful {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    Nonempty (closedSheafDirectImage (Type v) Z hZ).FullyFaithful := by
  sorry

/-- The essential image of a closed direct image is characterized by singleton stalks
outside the closed subset. -/
theorem closedSetSheafDirectImage_essentialImage {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z)
    (G : TopCat.Sheaf (Type v) X) :
    (∃ F, Nonempty ((closedSheafDirectImage (Type v) Z hZ).obj F ≅ G)) ↔
      ClosedSingletonStalkCondition Z hZ G := by
  sorry

/-- Direct image along a closed inclusion is fully faithful on abelian sheaves. -/
theorem closedAbelianSheafDirectImage_fullFaithful {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    Nonempty (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).FullyFaithful := by
  sorry

/-- The abelian essential image is characterized by zero stalks off the closed subset. -/
def ClosedZeroStalkCondition {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z)
    (G : TopCat.Sheaf (AddCommGrpCat.{v}) X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty
    (G.presheaf.stalk x ≅ (0 : AddCommGrpCat.{v}))

theorem closedAbelianSheafDirectImage_essentialImage {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z)
    (G : TopCat.Sheaf (AddCommGrpCat.{v}) X) :
    (∃ F, Nonempty ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj F ≅ G)) ↔
      ClosedZeroStalkCondition Z hZ G := by
  sorry

/-! ## Category-valued algebraic structures -/

/-- The generic final-stalk condition for a closed direct image. -/
def ClosedFinalStalkCondition (C : Type u) [Category.{v} C]
    [HasColimits C] [HasTerminal C] {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z)
    (G : TopCat.Sheaf C X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty (G.presheaf.stalk x ≅ (⊤_ C))

/-- The generic closed direct image has final stalks off the closed subset. -/
theorem closedAlgebraicSheafDirectImage_stalk_outside
    (C : Type u) [Category.{v} C] [HasColimits C] [HasTerminal C]
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf C (closedSubspace Z)) (x : X) (hx : x ∉ Z) :
    Nonempty (((closedAlgebraicSheafDirectImage C Z hZ).obj F).presheaf.stalk x ≅
      (⊤_ C)) := by
  sorry

/-- The generic closed direct image is fully faithful. -/
theorem closedAlgebraicSheafDirectImage_fullFaithful
    (C : Type u) [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (closedAlgebraicSheafDirectImage C Z hZ).FullyFaithful := by
  sorry

/-- The generic essential image is characterized by final stalks off the closed subset. -/
theorem closedAlgebraicSheafDirectImage_essentialImage
    (C : Type u) [Category.{v} C] [HasColimits C] [HasTerminal C]
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (G : TopCat.Sheaf C X) :
    (∃ F, Nonempty ((closedAlgebraicSheafDirectImage C Z hZ).obj F ≅ G)) ↔
      ClosedFinalStalkCondition C Z hZ G := by
  sorry

/-! ## Exactness warning -/

/-- A nonempty complement prevents the set-valued closed direct image from being right exact. -/
theorem closedSetSheafDirectImage_not_right_exact {X : TopCat.{v}} (Z : Set X)
    (hclosed : IsClosed Z) (hZ : ∃ x : X, x ∉ Z) :
    ¬ PreservesFiniteColimits (closedSheafDirectImage (Type v) Z hclosed) := by
  sorry

end

end Formalization.Books.Sheaves.Unit22
