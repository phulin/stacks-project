import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Categories.Unit24.AdjointFunctors
import Formalization.Books.Sheaves.Unit08.AbelianSheaves
import Formalization.Books.Sheaves.Unit21.ContinuousMaps
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves on Spaces, Chapter 32: Closed immersions and (pre)sheaves

The source section is `books/sheaves.tex:4925-5070`.  The inclusion of a
closed subset is represented by the canonical subtype inclusion in `TopCat`,
and pushforward, pullback, stalks, essential images, and exactness use the
corresponding Mathlib and earlier-chapter interfaces.

The source's later abelian-sheaf result and its ringed-space scope remark are
recorded as documentation only.  Their constructions and results belong to
later material, so they are not moved into this chapter by artificial
declarations.
-/

namespace Formalization.Books.Sheaves.Unit32

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open scoped ZeroObject
open Formalization.Books.Categories.Unit23
open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit21

universe u v w

noncomputable section

/- Mathlib's site-level colimit instance is stated for
   `CategoryTheory.Sheaf`, while `TopCat.Sheaf` is its canonical topological
   specialization introduced by a reducible definition.  This small bridge
   exposes the existing site-level finite-colimit API at the specialization;
   no new colimit construction is introduced here. -/
noncomputable instance topCatSheaf_hasFiniteColimits
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (X : TopCat.{w})
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    HasFiniteColimits (TopCat.Sheaf C X) := by
  change HasFiniteColimits (CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) C)
  infer_instance
def closedSubsetInclusion {X : TopCat.{w}} (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The subtype inclusion is a closed embedding when the subset is closed. -/
theorem closedSubsetInclusion_isClosedEmbedding {X : TopCat.{w}} {Z : Set X}
    (hZ : IsClosed Z) : IsClosedEmbedding (closedSubsetInclusion Z) := by
  exact hZ.isClosedEmbedding_subtypeVal
abbrev closedSubsetPushforward {C : Type u} [Category.{v} C]
    {X : TopCat.{w}} (Z : Set X) :
    TopCat.Sheaf C (TopCat.of Z) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pushforward C (closedSubsetInclusion Z)

/-- Set-valued pushforward along the closed subset inclusion. -/
abbrev closedSubsetSetPushforward {X : TopCat.{w}} (Z : Set X) :
    Sh.{w, w} (TopCat.of Z) ⥤ Sh.{w, w} X :=
  pushforwardSheaf (closedSubsetInclusion Z)

/-- Set-valued pullback along the closed subset inclusion. -/
noncomputable abbrev closedSubsetSetPullback {X : TopCat.{w}} (Z : Set X) :
    Sh.{w, w} X ⥤ Sh.{w, w} (TopCat.of Z) :=
  pullbackSheaf (closedSubsetInclusion Z)

/-- The set-valued pullback/pushforward adjunction. -/
noncomputable abbrev closedSubsetSetAdjunction {X : TopCat.{w}} (Z : Set X) :
    closedSubsetSetPullback Z ⊣ closedSubsetSetPushforward Z :=
  pullbackSheafPushforwardAdjunction (closedSubsetInclusion Z)

/-! ## Stalks and the counit -/

/- The following is the canonical stalk comparison at a point of the closed
   subset.  It has a real body: the comparison is the Mathlib
   `stalkPushforward` map, which is an isomorphism for an inducing map. -/

/-- The pushforward stalk at a point of the subset is the original stalk. -/
noncomputable def closedSubsetPushforward_stalkIso
    {C : Type u} [Category.{w} C] [HasColimits C]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : TopCat.Sheaf C (TopCat.of Z)) (z : Z) :
    TopCat.Presheaf.stalk (C := C) (X := X)
        ((closedSubsetPushforward (C := C) Z).obj F).presheaf
        (closedSubsetInclusion Z z) ≅
      TopCat.Presheaf.stalk (C := C) (X := TopCat.of Z) F.presheaf z := by
  let hIso : IsIso (TopCat.Presheaf.stalkPushforward C
      (closedSubsetInclusion Z) F.presheaf z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      C hZ.isClosedEmbedding_subtypeVal.isInducing F.presheaf z
  change ((TopCat.Presheaf.pushforward C
      (closedSubsetInclusion Z)).obj F.presheaf).stalk (closedSubsetInclusion Z z) ≅
    F.presheaf.stalk z
  exact @asIso _ _ _ _ (TopCat.Presheaf.stalkPushforward C
    (closedSubsetInclusion Z) F.presheaf z) hIso
theorem closedSubsetPushforward_stalkIso_terminal_of_not_mem
    {C : Type u} [Category.{w} C] [HasColimits C] [HasTerminal C]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : TopCat.Sheaf C (TopCat.of Z)) {x : X} (hx : x ∉ Z) :
    Nonempty (TopCat.Presheaf.stalk (C := C) (X := X)
      ((closedSubsetPushforward (C := C) Z).obj F).presheaf x ≅ (⊤_ C)) := by
  let P : TopCat.Presheaf C X :=
    ((closedSubsetPushforward (C := C) Z).obj F).presheaf
  have h1 : ∃ U : OpenNhds x,
      (Opens.map (closedSubsetInclusion Z)).obj U.1 = ⊥ := by
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
    change IsTerminal (F.presheaf.obj (op ((Opens.map
      (closedSubsetInclusion Z)).obj U.1)))
    rw [hU]
    exact F.isTerminalOfEmpty
  have hUt' : IsTerminal (((OpenNhds.inclusion x).op ⋙ P).obj (op U)) := by
    change IsTerminal (P.obj (op U.1))
    exact hUt
  let e : ((OpenNhds.inclusion x).op ⋙ P).obj (op U) ≅ (⊤_ C) :=
    hUt'.uniqueUpToIso terminalIsTerminal
  have hUdis : ∀ z : Z, (z : X) ∉ U.1 := by
    intro z hz
    have hz' : z ∈ (Opens.map (closedSubsetInclusion Z)).obj U.1 := by
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
              (F.presheaf.obj (op ((Opens.map (closedSubsetInclusion Z)).obj
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
theorem closedSubsetSetPushforward_stalk_equiv_punit_of_not_mem
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : Sh.{w, w} (TopCat.of Z)) {x : X} (hx : x ∉ Z) :
    Nonempty (((closedSubsetSetPushforward Z).obj F).presheaf.stalk x ≃
      (PUnit : Type w)) := by
  change Nonempty (((closedSubsetPushforward (C := Type w) Z).obj F).presheaf.stalk x ≃
    (PUnit : Type w))
  rcases closedSubsetPushforward_stalkIso_terminal_of_not_mem (C := Type w) hZ F hx with ⟨e⟩
  apply Nonempty.intro
  exact e.toEquiv.trans (Types.terminalIso.toEquiv)
noncomputable def closedSubsetSetPushforward_stalkEquiv
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : Sh.{w, w} (TopCat.of Z)) (z : Z) :
    TopCat.Presheaf.stalk (C := Type w) (X := X)
        ((closedSubsetSetPushforward Z).obj F).presheaf
        (closedSubsetInclusion Z z) ≃
      TopCat.Presheaf.stalk (C := Type w) (X := TopCat.of Z) F.presheaf z :=
  (closedSubsetPushforward_stalkIso (C := Type w) hZ F z).toEquiv

private theorem closedSubsetPushforward_counit_isIso_of_category
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C
      (closedSubsetInclusion Z)).counit) := by
  let f : TopCat.of Z ⟶ X := closedSubsetInclusion Z
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
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        Functor.map_id, Category.comp_id]
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
    · exact compatiblePreserving_opens_map (closedSubsetInclusion Z)
    · exact coverPreserving_opens_map (closedSubsetInclusion Z)
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
theorem closedSubsetSet_inverseImage_pushforward_counit_isIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    IsIso (closedSubsetSetAdjunction Z |>.counit) := by
  change IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type w)
    (closedSubsetInclusion Z)).counit)
  exact closedSubsetPushforward_counit_isIso_of_category (C := Type w) hZ
noncomputable def closedSubsetSet_inverseImagePushforwardIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    closedSubsetSetPushforward Z ⋙ closedSubsetSetPullback Z ≅
      𝟭 (Sh.{w, w} (TopCat.of Z)) := by
  let : IsIso (closedSubsetSetAdjunction Z |>.counit) :=
    closedSubsetSet_inverseImage_pushforward_counit_isIso hZ
  exact asIso (closedSubsetSetAdjunction Z |>.counit)
abbrev closedSubsetSet_terminalStalkCondition
    {X : TopCat.{w}} (Z : Set X) (G : Sh.{w, w} X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty (G.presheaf.stalk x ≃ (PUnit : Type w))

/-- Pushforward along a closed subset inclusion is fully faithful for sets. -/
theorem closedSubsetSetPushforward_fullyFaithful
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (closedSubsetSetPushforward Z).FullyFaithful := by
  let : IsIso (closedSubsetSetAdjunction Z |>.counit) :=
    closedSubsetSet_inverseImage_pushforward_counit_isIso hZ
  exact ⟨closedSubsetSetAdjunction Z |>.fullyFaithfulROfIsIsoCounit⟩
theorem closedSubsetSetPushforward_mem_essImage_iff
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) (G : Sh.{w, w} X) :
    (closedSubsetSetPushforward Z).essImage G ↔
      closedSubsetSet_terminalStalkCondition Z G := by
  let adj := closedSubsetSetAdjunction Z
  let : IsIso adj.counit := closedSubsetSet_inverseImage_pushforward_counit_isIso hZ
  let hff : (closedSubsetSetPushforward Z).FullyFaithful :=
    adj.fullyFaithfulROfIsIsoCounit
  let : (closedSubsetSetPushforward Z).Full := hff.full
  let : (closedSubsetSetPushforward Z).Faithful := hff.faithful
  rw [← adj.isIso_unit_app_iff_mem_essImage]
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  constructor
  · intro h x hx
    rcases closedSubsetSetPushforward_stalk_equiv_punit_of_not_mem hZ
        ((closedSubsetSetPullback Z).obj G) hx with ⟨e⟩
    exact ⟨(asIso ((TopCat.Presheaf.stalkFunctor (Type w) x).map
      (adj.unit.app G).hom)).toEquiv.trans e⟩
  · intro h x
    change Sheaf (Opens.grothendieckTopology X) (Type w) at G
    by_cases hx : x ∈ Z
    · let z : Z := ⟨x, hx⟩
      let f : TopCat.of Z ⟶ X := closedSubsetInclusion Z
      let f₀ : Opens X ⥤ Opens (TopCat.of Z) := Opens.map f
      let : f₀.IsContinuous (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (TopCat.of Z)) := by
        apply Functor.isContinuous_of_coverPreserving
        · exact compatiblePreserving_opens_map (closedSubsetInclusion Z)
        · exact coverPreserving_opens_map (closedSubsetInclusion Z)
      let L₂ : TopCat.Sheaf (Type w) X ⥤
          TopCat.Sheaf (Type w) (TopCat.of Z) :=
        Functor.sheafPullbackConstruction.sheafPullback f₀ (Type w)
          (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (TopCat.of Z))
      dsimp [TopCat.Sheaf] at L₂
      let adj₀ := (f₀.op.lanAdjunction (Type w)).comp
        (sheafificationAdjunction
          (Opens.grothendieckTopology (TopCat.of Z)) (Type w))
      let comm1 :
          sheafToPresheaf (Opens.grothendieckTopology X) (Type w) ⋙
              f₀.op.lan ⋙
                presheafToSheaf
                  (Opens.grothendieckTopology (TopCat.of Z)) (Type w) ≅
            L₂ ⋙ 𝟭 (Sheaf
              (Opens.grothendieckTopology (TopCat.of Z)) (Type w)) := by
        dsimp [L₂, Functor.sheafPullbackConstruction.sheafPullback]
        exact (Functor.rightUnitor _).symm
      let adj₂ := adj₀.restrictFullyFaithful
        (fullyFaithfulSheafToPresheaf
          (Opens.grothendieckTopology X) (Type w))
        (Functor.FullyFaithful.id _)
        (L := L₂)
        (R := f₀.sheafPushforwardContinuous (Type w)
          (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (TopCat.of Z)))
        comm1 (Iso.refl _)
      let e₀ := adj.leftAdjointUniq adj₂
      let P₂ : TopCat.Presheaf (Type w) (TopCat.of Z) :=
        ((presheafToSheaf
          (Opens.grothendieckTopology (TopCat.of Z)) (Type w)).obj
          (f₀.op.lan.obj G.obj)).obj
      let hpush₂ : IsIso
          (TopCat.Presheaf.stalkPushforward (Type w) f P₂ z) :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
          (C := Type w) hZ.isClosedEmbedding_subtypeVal.isInducing
          P₂ z
      let ePush₂ := @asIso _ _ _ _
        (TopCat.Presheaf.stalkPushforward (Type w) f P₂ z) hpush₂
      let hU₂ := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        (X := TopCat.of Z) (p₀ := z) (C := Type w)
          ((pullbackPresheaf f).obj G.1)
      let e₂ := (pullbackPresheafStalkIso f G.1 z).trans
        (@asIso _ _ _ _
          ((TopCat.Presheaf.stalkFunctor (Type w) z).map
            (CategoryTheory.toSheafify
              (Opens.grothendieckTopology (TopCat.of Z))
              ((pullbackPresheaf f).obj G.1))) hU₂)
      let : IsIso e₂.hom := e₂.isIso_hom
      have hpush_map {P Q : TopCat.Presheaf (Type w) (TopCat.of Z)}
          (φ : P ⟶ Q) :
          (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
              ((TopCat.Presheaf.pushforward (Type w) f).map φ) ≫
            TopCat.Presheaf.stalkPushforward (Type w) f Q z =
          TopCat.Presheaf.stalkPushforward (Type w) f P z ≫
            (TopCat.Presheaf.stalkFunctor (Type w) z).map φ := by
        apply TopCat.Presheaf.stalk_hom_ext
          ((TopCat.Presheaf.pushforward (Type w) f).obj P)
        intro U hxU
        change _ ≫
            (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
              ((TopCat.Presheaf.pushforward (Type w) f).map φ) ≫ _ = _
        have hmap := TopCat.Presheaf.stalkFunctor_map_germ
          (C := Type w) U (f z) hxU
            ((TopCat.Presheaf.pushforward (Type w) f).map φ)
        have hmap' := hmap
        change TopCat.Presheaf.germ
              ((TopCat.Presheaf.pushforward (Type w) f).obj P) U
              (f z) hxU ≫
              (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
                ((TopCat.Presheaf.pushforward (Type w) f).map φ) =
            ((TopCat.Presheaf.pushforward (Type w) f).map φ).app (op U) ≫
              TopCat.Presheaf.germ
                ((TopCat.Presheaf.pushforward (Type w) f).obj Q) U
                (f z) hxU at hmap'
        have hpushP := TopCat.Presheaf.stalkPushforward_germ
          (C := Type w) f P U z hxU
        have hpushQ := TopCat.Presheaf.stalkPushforward_germ
          (C := Type w) f Q U z hxU
        have hpushP' :
            TopCat.Presheaf.germ
                ((TopCat.Presheaf.pushforward (Type w) f).obj P) U
                (f z) hxU ≫
              TopCat.Presheaf.stalkPushforward (Type w) f P z =
            P.germ ((Opens.map f).obj U) z hxU := by
          simpa only [TopCat.Presheaf.pushforward] using hpushP
        have hpushQ' :
            TopCat.Presheaf.germ
                ((TopCat.Presheaf.pushforward (Type w) f).obj Q) U
                (f z) hxU ≫
              TopCat.Presheaf.stalkPushforward (Type w) f Q z =
            Q.germ ((Opens.map f).obj U) z hxU := by
          simpa only [TopCat.Presheaf.pushforward] using hpushQ
        have hφmap := TopCat.Presheaf.stalkFunctor_map_germ
          (C := Type w) ((Opens.map f).obj U) z hxU φ
        have hφmap' := hφmap
        change P.germ ((Opens.map f).obj U) z hxU ≫
              (TopCat.Presheaf.stalkFunctor (Type w) z).map φ =
            φ.app (op ((Opens.map f).obj U)) ≫
              Q.germ ((Opens.map f).obj U) z hxU at hφmap'
        have hleft :
            (TopCat.Presheaf.germ
                  ((TopCat.Presheaf.pushforward (Type w) f).obj P) U
                  (f z) hxU ≫
                (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
                  ((TopCat.Presheaf.pushforward (Type w) f).map φ)) ≫
                TopCat.Presheaf.stalkPushforward (Type w) f Q z =
            ((TopCat.Presheaf.pushforward (Type w) f).map φ).app (op U) ≫
              Q.germ ((Opens.map f).obj U) z hxU := by
          calc
            _ = (((TopCat.Presheaf.pushforward (Type w) f).map φ).app (op U) ≫
                ((TopCat.Presheaf.pushforward (Type w) f).obj Q).germ U
                  (f z) hxU) ≫
                TopCat.Presheaf.stalkPushforward (Type w) f Q z := by
              convert congrArg (fun k =>
                k ≫ TopCat.Presheaf.stalkPushforward (Type w) f Q z) hmap' using 1
              all_goals (simp only [TopCat.Presheaf.pushforward] ; rfl)
            _ = ((TopCat.Presheaf.pushforward (Type w) f).map φ).app (op U) ≫
                Q.germ ((Opens.map f).obj U) z hxU := by
              exact congrArg
                (fun k => ((TopCat.Presheaf.pushforward (Type w) f).map φ).app
                  (op U) ≫ k) hpushQ'
        have hright :
            (TopCat.Presheaf.germ
                  ((TopCat.Presheaf.pushforward (Type w) f).obj P) U
                  (f z) hxU ≫
                TopCat.Presheaf.stalkPushforward (Type w) f P z) ≫
              (TopCat.Presheaf.stalkFunctor (Type w) z).map φ =
            ((TopCat.Presheaf.pushforward (Type w) f).map φ).app (op U) ≫
              Q.germ ((Opens.map f).obj U) z hxU := by
          rw [hpushP']
          rw [TopCat.Presheaf.pushforward_map_app']
          exact hφmap'
        exact hleft.trans hright.symm
      have hunit₂ :
          (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
            (adj₂.unit.app G).hom ≫
            ePush₂.hom = e₂.hom := by
        have hmapunit := Adjunction.map_restrictFullyFaithful_unit_app
          (adj := adj₀)
          (hiC := fullyFaithfulSheafToPresheaf
            (Opens.grothendieckTopology X) (Type w))
          (hiD := Functor.FullyFaithful.id _)
          (L := L₂)
          (R := f₀.sheafPushforwardContinuous (Type w)
            (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (TopCat.of Z)))
          (comm1 := comm1) (comm2 := Iso.refl _) G
        change (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
            ((sheafToPresheaf (Opens.grothendieckTopology X) (Type w)).map
              (adj₂.unit.app G)) ≫ ePush₂.hom = e₂.hom
        rw [hmapunit]
        change
          (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
              (adj₀.unit.app
                ((sheafToPresheaf (Opens.grothendieckTopology X) (Type w)).obj G)) ≫
            (@asIso _ _ _ _
              (TopCat.Presheaf.stalkPushforward (Type w) f P₂ z) hpush₂).hom =
          e₂.hom
        simp [e₂, adj₀, f₀, f,
          TopCat.Presheaf.pullbackPushforwardAdjunction,
          TopCat.Presheaf.pullback, pullbackPresheaf,
          Adjunction.comp_unit_app, pullbackPresheafStalkIso,
          TopCat.Presheaf.stalkPullbackIso,
          TopCat.Presheaf.stalkPullbackHom]
        have hnat :
            (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
                ((TopCat.Presheaf.pushforward (Type w) f).map
                  (CategoryTheory.toSheafify
                    (Opens.grothendieckTopology (TopCat.of Z))
                    (f₀.op.lan.obj G.obj))) ≫
              TopCat.Presheaf.stalkPushforward (Type w) f
                (((presheafToSheaf
                  (Opens.grothendieckTopology (TopCat.of Z)) (Type w)).obj
                    (f₀.op.lan.obj G.obj)).obj) z =
            TopCat.Presheaf.stalkPushforward (Type w) f
                (f₀.op.lan.obj G.obj) z ≫
              (TopCat.Presheaf.stalkFunctor (Type w) z).map
                (CategoryTheory.toSheafify
                  (Opens.grothendieckTopology (TopCat.of Z))
                  (f₀.op.lan.obj G.obj)) := by
          exact hpush_map (P := f₀.op.lan.obj G.obj)
            (Q := ((presheafToSheaf
              (Opens.grothendieckTopology (TopCat.of Z)) (Type w)).obj
                (f₀.op.lan.obj G.obj)).obj)
            (CategoryTheory.toSheafify
              (Opens.grothendieckTopology (TopCat.of Z))
              (f₀.op.lan.obj G.obj))
        change
          ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
                ((Opens.map f).op.lanUnit.app G.obj) ≫
              (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
                ((TopCat.Presheaf.pushforward (Type w) f).map
                  (CategoryTheory.toSheafify
                    (Opens.grothendieckTopology (TopCat.of Z))
                    ((Opens.map f).op.lan.obj G.obj))) ≫
              TopCat.Presheaf.stalkPushforward (Type w) f
                (((presheafToSheaf
                  (Opens.grothendieckTopology (TopCat.of Z)) (Type w)).obj
                    ((Opens.map f).op.lan.obj G.obj)).obj) z) =
            ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
                ((Opens.map f).op.lanUnit.app G.obj) ≫
              TopCat.Presheaf.stalkPushforward (Type w) f
                ((Opens.map f).op.lan.obj G.obj) z) ≫
            (@asIso _ _ _ _
              ((TopCat.Presheaf.stalkFunctor (Type w) z).map
                (CategoryTheory.toSheafify
                  (Opens.grothendieckTopology (TopCat.of Z))
                  ((Opens.map f).op.lan.obj G.obj))) hU₂).hom
        have hnat' := congrArg (fun q =>
          (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
              ((Opens.map f).op.lanUnit.app G.obj) ≫ q) hnat
        convert hnat' using 1 ; rfl
      let : IsIso
          ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
            ((closedSubsetSetPushforward Z).map (e₀.hom.app G)).hom) := by
        let : IsIso (e₀.hom.app G) := (e₀.app G).isIso_hom
        let : IsIso ((closedSubsetSetPushforward Z).map (e₀.hom.app G)) := by
          exact Functor.map_isIso _ _
        let : IsIso (((closedSubsetSetPushforward Z).map
            (e₀.hom.app G)).hom) :=
          (TopCat.Sheaf.forget (Type w) X).map_isIso
            ((closedSubsetSetPushforward Z).map (e₀.hom.app G))
        exact Functor.map_isIso
          (TopCat.Presheaf.stalkFunctor (Type w) (f z))
          (((closedSubsetSetPushforward Z).map (e₀.hom.app G)).hom)
      have hunit :
          adj.unit.app G ≫ (closedSubsetSetPushforward Z).map (e₀.hom.app G) =
            adj₂.unit.app G := by
        exact Adjunction.unit_leftAdjointUniq_hom_app adj adj₂ G
      have hcomp :
          (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
              (adj.unit.app G).hom ≫
            (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
              ((closedSubsetSetPushforward Z).map (e₀.hom.app G)).hom =
            (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
              (adj₂.unit.app G).hom := by
        rw [← Functor.map_comp]
        have hunit_hom := congrArg (fun q => q.hom) hunit
        exact congrArg
          (fun q => (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map q)
          hunit_hom
      let : IsIso
          ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
              (adj₂.unit.app G).hom ≫ ePush₂.hom) := by
        let : IsIso e₂.hom := e₂.isIso_hom
        rw [hunit₂]
        exact e₂.isIso_hom
      have hIsoAdj₂ : IsIso
          ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
            (adj₂.unit.app G).hom) := by
        have hf :
            (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
                (adj₂.unit.app G).hom = e₂.hom ≫ ePush₂.inv := by
          exact ePush₂.eq_comp_inv.mpr hunit₂
        rw [hf]
        exact (e₂.trans ePush₂.symm).isIso_hom
      let : IsIso ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
          (adj₂.unit.app G).hom) := by
        exact hIsoAdj₂
      let : IsIso ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
          (adj.unit.app G).hom ≫
        (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
          ((closedSubsetSetPushforward Z).map (e₀.hom.app G)).hom) := by
        rw [hcomp]
        exact hIsoAdj₂
      let : IsIso
          ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
            ((closedSubsetSetPushforward Z).map (e₀.hom.app G)).hom) := by
        infer_instance
      exact IsIso.of_isIso_comp_right
        ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
          (adj.unit.app G).hom)
        ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
          ((closedSubsetSetPushforward Z).map (e₀.hom.app G)).hom)
    · rcases h x hx with ⟨eG⟩
      let F := (closedSubsetSetPullback Z).obj G
      rcases closedSubsetSetPushforward_stalk_equiv_punit_of_not_mem hZ F hx with ⟨eF⟩
      rw [isIso_iff_bijective]
      constructor
      · intro a b hab
        apply eG.injective
        exact Subsingleton.elim _ _
      · intro b
        refine ⟨eG.symm PUnit.unit, ?_⟩
        apply eF.injective
        exact Subsingleton.elim _ _
abbrev closedSubsetAbelianPushforward {X : TopCat.{w}} (Z : Set X) :
    TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z) ⥤
      TopCat.Sheaf AddCommGrpCat.{w} X :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{w} (closedSubsetInclusion Z)

/-- Pullback of abelian sheaves along the closed subset inclusion. -/
noncomputable abbrev closedSubsetAbelianPullback {X : TopCat.{w}} (Z : Set X) :
    TopCat.Sheaf AddCommGrpCat.{w} X ⥤
      TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z) :=
  TopCat.Sheaf.pullback AddCommGrpCat.{w} (closedSubsetInclusion Z)

/-- The abelian sheaf pullback/pushforward adjunction. -/
noncomputable abbrev closedSubsetAbelianAdjunction {X : TopCat.{w}} (Z : Set X) :
    closedSubsetAbelianPullback Z ⊣ closedSubsetAbelianPushforward Z :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{w}
    (closedSubsetInclusion Z)

/-- The outside stalk of an abelian pushforward is isomorphic to zero. -/
theorem closedSubsetAbelianPushforward_stalkIso_zero_of_not_mem
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z)) {x : X} (hx : x ∉ Z) :
    Nonempty (((closedSubsetAbelianPushforward Z).obj F).presheaf.stalk x ≅
      (0 : AddCommGrpCat.{w})) := by
  change Nonempty (((closedSubsetPushforward (C := AddCommGrpCat.{w}) Z).obj F).presheaf.stalk x ≅
    (0 : AddCommGrpCat.{w}))
  rcases closedSubsetPushforward_stalkIso_terminal_of_not_mem
      (C := AddCommGrpCat.{w}) hZ F hx with ⟨e⟩
  exact ⟨e ≪≫ (HasZeroObject.zeroIsoTerminal :
    (0 : AddCommGrpCat.{w}) ≅ (⊤_ AddCommGrpCat.{w})).symm⟩
noncomputable def closedSubsetAbelianPushforward_stalkIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z)) (z : Z) :
    ((closedSubsetAbelianPushforward Z).obj F).presheaf.stalk
        (closedSubsetInclusion Z z) ≅ F.presheaf.stalk z :=
  closedSubsetPushforward_stalkIso (C := AddCommGrpCat.{w}) hZ F z

/-- The abelian sheaf counit is an isomorphism. -/
theorem closedSubsetAbelian_inverseImage_pushforward_counit_isIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    IsIso (closedSubsetAbelianAdjunction Z |>.counit) := by
  change IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{w}
    (closedSubsetInclusion Z)).counit)
  exact closedSubsetPushforward_counit_isIso_of_category
    (C := AddCommGrpCat.{w}) hZ
noncomputable def closedSubsetAbelian_inverseImagePushforwardIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    closedSubsetAbelianPushforward Z ⋙ closedSubsetAbelianPullback Z ≅
      𝟭 (TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z)) := by
  let : IsIso (closedSubsetAbelianAdjunction Z |>.counit) :=
    closedSubsetAbelian_inverseImage_pushforward_counit_isIso hZ
  exact asIso (closedSubsetAbelianAdjunction Z |>.counit)
abbrev closedSubsetAbelian_zeroStalkCondition
    {X : TopCat.{w}} (Z : Set X)
    (G : TopCat.Sheaf AddCommGrpCat.{w} X) : Prop :=
  ∀ x : X, x ∉ Z →
    Nonempty (TopCat.Presheaf.stalk (C := AddCommGrpCat.{w}) (X := X)
      G.presheaf x ≅ (0 : AddCommGrpCat.{w}))

/-- Pushforward along a closed subset inclusion is fully faithful for abelian sheaves. -/
theorem closedSubsetAbelianPushforward_fullyFaithful
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (closedSubsetAbelianPushforward Z).FullyFaithful := by
  let : IsIso (closedSubsetAbelianAdjunction Z |>.counit) :=
    closedSubsetAbelian_inverseImage_pushforward_counit_isIso hZ
  exact ⟨closedSubsetAbelianAdjunction Z |>.fullyFaithfulROfIsIsoCounit⟩
private noncomputable def closedSubsetPullbackStalkIso
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X}
    (G : TopCat.Sheaf C X) (z : Z) :
    G.presheaf.stalk (closedSubsetInclusion Z z) ≅
      ((TopCat.Sheaf.pullback C (closedSubsetInclusion Z)).obj G).presheaf.stalk z := by
  let e := (TopCat.Sheaf.pullbackIso C (closedSubsetInclusion Z)).app G
  let e' := (CategoryTheory.sheafToPresheaf
    (Opens.grothendieckTopology (TopCat.of Z)) C).mapIso e
  let P := (TopCat.Presheaf.pullback C (closedSubsetInclusion Z)).obj G.presheaf
  let u := (TopCat.Presheaf.stalkFunctor C z).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z)) P)
  let hU : IsIso u := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    (X := TopCat.of Z) (p₀ := z) (C := C) P
  exact (TopCat.Presheaf.stalkPullbackIso C (closedSubsetInclusion Z) G.presheaf z).trans <|
    (asIso u).trans <| (TopCat.Presheaf.stalkFunctor C z).mapIso e'.symm
private lemma category_comp_iso_inv_hom_cancel
    {C : Type u} [Category.{w} C]
    {A B D E F : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E)
    (e : F ≅ E) :
    (f ≫ g ≫ h ≫ e.inv) ≫ e.hom = f ≫ g ≫ h := by simp
set_option backward.isDefEq.respectTransparency false in
private theorem stalkPushforward_map_naturality
    {C : Type u} [Category.{w} C] [HasColimits C]
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    {P Q : TopCat.Presheaf C X} (φ : P ⟶ Q) (x : X) :
    (TopCat.Presheaf.stalkFunctor C (f x)).map
          ((TopCat.Presheaf.pushforward C f).map φ) ≫
        TopCat.Presheaf.stalkPushforward C f Q x =
      TopCat.Presheaf.stalkPushforward C f P x ≫
        (TopCat.Presheaf.stalkFunctor C x).map φ := by
  apply TopCat.Presheaf.stalk_hom_ext
    ((TopCat.Presheaf.pushforward C f).obj P)
  intro U hxU
  change _ ≫
      (TopCat.Presheaf.stalkFunctor C (f x)).map
        ((TopCat.Presheaf.pushforward C f).map φ) ≫ _ = _
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ
    (C := C) U (f x) hxU
      ((TopCat.Presheaf.pushforward C f).map φ)
  have hmap' := hmap
  change TopCat.Presheaf.germ
        ((TopCat.Presheaf.pushforward C f).obj P) U
        (f x) hxU ≫
      (TopCat.Presheaf.stalkFunctor C (f x)).map
        ((TopCat.Presheaf.pushforward C f).map φ) =
    ((TopCat.Presheaf.pushforward C f).map φ).app (op U) ≫
      TopCat.Presheaf.germ
        ((TopCat.Presheaf.pushforward C f).obj Q) U
        (f x) hxU at hmap'
  have hpushP := TopCat.Presheaf.stalkPushforward_germ
    (C := C) f P U x hxU
  have hpushQ := TopCat.Presheaf.stalkPushforward_germ
    (C := C) f Q U x hxU
  have hpushP' :
      TopCat.Presheaf.germ
          ((TopCat.Presheaf.pushforward C f).obj P) U
          (f x) hxU ≫
        TopCat.Presheaf.stalkPushforward C f P x =
      P.germ ((Opens.map f).obj U) x hxU := by
    simpa only [TopCat.Presheaf.pushforward] using hpushP
  have hpushQ' :
      TopCat.Presheaf.germ
          ((TopCat.Presheaf.pushforward C f).obj Q) U
          (f x) hxU ≫
        TopCat.Presheaf.stalkPushforward C f Q x =
      Q.germ ((Opens.map f).obj U) x hxU := by
    simpa only [TopCat.Presheaf.pushforward] using hpushQ
  have hφmap := TopCat.Presheaf.stalkFunctor_map_germ
    (C := C) ((Opens.map f).obj U) x hxU φ
  have hφmap' := hφmap
  change P.germ ((Opens.map f).obj U) x hxU ≫
        (TopCat.Presheaf.stalkFunctor C x).map φ =
      φ.app (op ((Opens.map f).obj U)) ≫
        Q.germ ((Opens.map f).obj U) x hxU at hφmap'
  have hleft :
      (TopCat.Presheaf.germ
            ((TopCat.Presheaf.pushforward C f).obj P) U
            (f x) hxU ≫
          (TopCat.Presheaf.stalkFunctor C (f x)).map
            ((TopCat.Presheaf.pushforward C f).map φ)) ≫
        TopCat.Presheaf.stalkPushforward C f Q x =
      ((TopCat.Presheaf.pushforward C f).map φ).app (op U) ≫
        Q.germ ((Opens.map f).obj U) x hxU := by
    calc
      _ = (((TopCat.Presheaf.pushforward C f).map φ).app (op U) ≫
          ((TopCat.Presheaf.pushforward C f).obj Q).germ U
            (f x) hxU) ≫
          TopCat.Presheaf.stalkPushforward C f Q x := by
        convert congrArg (fun k =>
          k ≫ TopCat.Presheaf.stalkPushforward C f Q x) hmap' using 1
        all_goals (simp only [TopCat.Presheaf.pushforward] ; rfl)
      _ = ((TopCat.Presheaf.pushforward C f).map φ).app (op U) ≫
          Q.germ ((Opens.map f).obj U) x hxU := by
        simpa only [Category.assoc] using congrArg
          (fun k => ((TopCat.Presheaf.pushforward C f).map φ).app
            (op U) ≫ k) hpushQ'
  have hright :
      (TopCat.Presheaf.germ
            ((TopCat.Presheaf.pushforward C f).obj P) U
            (f x) hxU ≫
          TopCat.Presheaf.stalkPushforward C f P x) ≫
        (TopCat.Presheaf.stalkFunctor C x).map φ =
      ((TopCat.Presheaf.pushforward C f).map φ).app (op U) ≫
        Q.germ ((Opens.map f).obj U) x hxU := by
    rw [hpushP']
    rw [TopCat.Presheaf.pushforward_map_app']
    exact hφmap'
  rw [Category.assoc] at hleft hright
  exact hleft.trans hright.symm
private theorem closedSubsetPushforward_unit_stalk_comp
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (G : TopCat.Sheaf C X) (z : Z) :
    (TopCat.Presheaf.stalkFunctor (C := C) (X := X)
        (closedSubsetInclusion Z z)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction C
          (closedSubsetInclusion Z)).unit.app G).hom ≫
    (closedSubsetPushforward_stalkIso (C := C) hZ
        ((TopCat.Sheaf.pullback C (closedSubsetInclusion Z)).obj G) z).hom =
    (closedSubsetPullbackStalkIso G z).hom := by
  let f : TopCat.of Z ⟶ X := closedSubsetInclusion Z
  let K := Opens.grothendieckTopology (TopCat.of Z)
  let e := (TopCat.Sheaf.pullbackIso C f).app G
  let e' := (CategoryTheory.sheafToPresheaf K C).mapIso e
  let P := (TopCat.Presheaf.pullback C f).obj G.presheaf
  let u := (TopCat.Presheaf.stalkFunctor C z).map
    (CategoryTheory.toSheafify K P)
  let hU : IsIso u := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    (X := TopCat.of Z) (p₀ := z) (C := C) P
  let : IsIso ((TopCat.Presheaf.stalkFunctor C z).map e'.hom) :=
    Functor.map_isIso _ _
  apply (cancel_mono ((TopCat.Presheaf.stalkFunctor C z).map e'.hom)).1
  change
    ((TopCat.Presheaf.stalkFunctor C (f z)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).hom ≫
      (closedSubsetPushforward_stalkIso (C := C) hZ
        ((TopCat.Sheaf.pullback C f).obj G) z).hom) ≫
        (TopCat.Presheaf.stalkFunctor C z).map e'.hom =
      ((TopCat.Presheaf.stalkPullbackIso C f G.presheaf z).hom ≫
        (asIso u).hom ≫
          (TopCat.Presheaf.stalkFunctor C z).map e'.symm.hom) ≫
        (TopCat.Presheaf.stalkFunctor C z).map e'.hom
  simp only [Iso.symm_hom, Category.assoc]
  let f₀ : Opens X ⥤ Opens (TopCat.of Z) := Opens.map f
  let : f₀.IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)) := by
    apply Functor.isContinuous_of_coverPreserving
    · exact compatiblePreserving_opens_map f
    · exact coverPreserving_opens_map f
  let G₀ : Sheaf (Opens.grothendieckTopology X) C := G
  let P₂ : TopCat.Presheaf C (TopCat.of Z) := f₀.op.lan.obj G₀.obj
  let L₂ : Sheaf (Opens.grothendieckTopology X) C ⥤
      Sheaf (Opens.grothendieckTopology (TopCat.of Z)) C :=
    Functor.sheafPullbackConstruction.sheafPullback f₀ C
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z))
  dsimp [TopCat.Sheaf] at L₂
  let Q : TopCat.Presheaf C (TopCat.of Z) :=
    ((CategoryTheory.presheafToSheaf K C).obj
      (f₀.op.lan.obj G₀.obj)).obj
  let hQ : IsIso (TopCat.Presheaf.stalkPushforward C f Q z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      C hZ.isClosedEmbedding_subtypeVal.isInducing Q z
  let ePushQ := @asIso _ _ _ _
    (TopCat.Presheaf.stalkPushforward C f Q z) hQ
  let adj₀ := (f₀.op.lanAdjunction C).comp
    (CategoryTheory.sheafificationAdjunction
      (Opens.grothendieckTopology (TopCat.of Z)) C)
  let adj₂ := adj₀.restrictFullyFaithful
    (CategoryTheory.fullyFaithfulSheafToPresheaf
      (Opens.grothendieckTopology X) C)
    (Functor.FullyFaithful.id _)
    (L := L₂)
    (R := f₀.sheafPushforwardContinuous C
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)))
    (Iso.refl _) (Iso.refl _)
  let hU₂ := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    (X := TopCat.of Z) (p₀ := z) (C := C) P₂
  let e₂ := (TopCat.Presheaf.stalkPullbackIso C f G₀.obj z).trans
    (@asIso _ _ _ _
      ((TopCat.Presheaf.stalkFunctor C z).map
        (CategoryTheory.toSheafify K P₂)) hU₂)
  have hunit₂ :
      (TopCat.Presheaf.stalkFunctor C (f z)).map
          ((CategoryTheory.sheafToPresheaf
            (Opens.grothendieckTopology X) C).map
      (adj₂.unit.app G₀)) ≫ ePushQ.hom = e₂.hom := by
    have hmapunit := Adjunction.map_restrictFullyFaithful_unit_app
      (adj := adj₀)
      (hiC := CategoryTheory.fullyFaithfulSheafToPresheaf
        (Opens.grothendieckTopology X) C)
      (hiD := Functor.FullyFaithful.id _)
      (L := L₂)
      (R := f₀.sheafPushforwardContinuous C
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (TopCat.of Z)))
      (comm1 := Iso.refl _) (comm2 := Iso.refl _) G₀
    change (TopCat.Presheaf.stalkFunctor C (f z)).map
        ((CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology X) C).map
          (adj₂.unit.app G₀)) ≫ ePushQ.hom = e₂.hom
    have hadj0 :
        adj₀.unit.app G₀.obj =
          (Opens.map f).op.lanUnit.app G₀.obj ≫
            (Opens.map f).op.whiskerLeft
              (CategoryTheory.toSheafify K P₂) := by
      simp [adj₀, Adjunction.comp_unit_app, f₀, P₂, K]
    have hnat₂ := stalkPushforward_map_naturality (f := f)
      (CategoryTheory.toSheafify K P₂) z
    have hunit0 :
        (TopCat.Presheaf.stalkFunctor C (f z)).map
              ((Opens.map f).op.lanUnit.app G₀.obj) ≫
            TopCat.Presheaf.stalkPushforward C f P₂ z =
          (TopCat.Presheaf.stalkPullbackIso C f G₀.obj z).hom := by
      dsimp [P₂, f₀]
      simp [TopCat.Presheaf.stalkPullbackIso,
        TopCat.Presheaf.stalkPullbackHom,
      TopCat.Presheaf.pullbackPushforwardAdjunction,
      TopCat.Presheaf.pullback]
    have hleft := congrArg (fun q =>
      (TopCat.Presheaf.stalkFunctor C (f z)).map
          ((Opens.map f).op.lanUnit.app G₀.obj) ≫ q) hnat₂
    have hright0 := congrArg (fun q =>
      q ≫ (TopCat.Presheaf.stalkFunctor C z).map
        (CategoryTheory.toSheafify K P₂)) hunit0
    have hright1 :=
      (Category.assoc
        ((TopCat.Presheaf.stalkFunctor C (f z)).map
          ((Opens.map f).op.lanUnit.app G₀.obj))
        (TopCat.Presheaf.stalkPushforward C f P₂ z)
        ((TopCat.Presheaf.stalkFunctor C z).map
          (CategoryTheory.toSheafify K P₂))).symm.trans hright0
    have hright :
        (TopCat.Presheaf.stalkFunctor C (f z)).map
              ((Opens.map f).op.lanUnit.app G₀.obj) ≫
            TopCat.Presheaf.stalkPushforward C f P₂ z ≫
          (TopCat.Presheaf.stalkFunctor C z).map
            (CategoryTheory.toSheafify K P₂) = e₂.hom := by
      dsimp [e₂]
      change _ =
        (TopCat.Presheaf.stalkPullbackIso C f G₀.obj z).hom ≫
          (TopCat.Presheaf.stalkFunctor C z).map
            (CategoryTheory.toSheafify K P₂)
      exact hright1
    have hmapunit' :
        (CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology X) C).map
            (adj₂.unit.app G₀) = adj₀.unit.app G₀.obj := by
      rw [hmapunit]
      simp only [Iso.refl_hom, NatTrans.id_app]
      change _ ≫ 𝟙 _ ≫ 𝟙 _ = _
      simp only [Category.comp_id]
      rfl
    rw [hmapunit']
    rw [hadj0]
    change
      (TopCat.Presheaf.stalkFunctor C (f z)).map
          ((Opens.map f).op.lanUnit.app G₀.obj ≫
            (TopCat.Presheaf.pushforward C f).map
              (CategoryTheory.toSheafify K P₂)) ≫ ePushQ.hom = e₂.hom
    have hfinal := hleft.trans hright
    have hePush :
        ePushQ.hom = TopCat.Presheaf.stalkPushforward C f
          (CategoryTheory.sheafify K P₂) z := by
      dsimp [ePushQ, Q]
    rw [hePush]
    erw [Functor.map_comp_assoc]
    simp only [Functor.id_obj, Functor.comp_obj,
      TopCat.Presheaf.stalkFunctor_obj] at hfinal ⊢
    exact hfinal
  have hnat := stalkPushforward_map_naturality (f := f) e'.hom z
  have hnat' :
      (TopCat.Presheaf.stalkFunctor C (f z)).map
          ((TopCat.Presheaf.pushforward C f).map e'.hom) ≫
        TopCat.Presheaf.stalkPushforward C f
          Q z =
        TopCat.Presheaf.stalkPushforward C f
          ((TopCat.Sheaf.pullback C f).obj G).presheaf z ≫
        (TopCat.Presheaf.stalkFunctor C z).map e'.hom := by
    change
      (TopCat.Presheaf.stalkFunctor C (f z)).map
          ((TopCat.Presheaf.pushforward C f).map e'.hom) ≫
        TopCat.Presheaf.stalkPushforward C f
          ((CategoryTheory.presheafToSheaf K C).obj
          ((TopCat.Presheaf.pullback C f).obj G.presheaf)).obj z =
      TopCat.Presheaf.stalkPushforward C f
          ((TopCat.Sheaf.pullback C f).obj G).presheaf z ≫
        (TopCat.Presheaf.stalkFunctor C z).map e'.hom
    exact hnat
  have hunit :
      (TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G ≫
          (TopCat.Sheaf.pushforward C f).map e.hom =
        adj₂.unit.app G₀ := by
    exact Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction C f) adj₂ G
  dsimp [closedSubsetPushforward_stalkIso]
  dsimp [f]
  set_option backward.isDefEq.respectTransparency false in
    rw [Category.assoc]
  have hnat'' := hnat'.symm
  dsimp [f] at hnat''
  rw [hnat'']
  calc
    _ = (TopCat.Presheaf.stalkFunctor C ((closedSubsetInclusion Z) z)).map
          ((CategoryTheory.sheafToPresheaf
            (Opens.grothendieckTopology X) C).map
            (adj₂.unit.app G₀)) ≫
        TopCat.Presheaf.stalkPushforward C (closedSubsetInclusion Z) Q z := by
      have hmap :
          (TopCat.Presheaf.pushforward C (closedSubsetInclusion Z)).map e'.hom =
            ((TopCat.Sheaf.pushforward C (closedSubsetInclusion Z)).map
              e.hom).hom := by
        rfl
      have hunit_hom := congrArg (fun q => q.hom) hunit
      have hcomp :
          ((TopCat.Sheaf.pullbackPushforwardAdjunction C
            (closedSubsetInclusion Z)).unit.app G).hom ≫
              ((TopCat.Sheaf.pushforward C (closedSubsetInclusion Z)).map
                e.hom).hom =
            ((CategoryTheory.sheafToPresheaf
              (Opens.grothendieckTopology X) C).map
              (adj₂.unit.app G₀)) := by
        exact hunit_hom
      have hmapcomp :
          (TopCat.Presheaf.stalkFunctor C ((closedSubsetInclusion Z) z)).map
                ((TopCat.Sheaf.pullbackPushforwardAdjunction C
                  (closedSubsetInclusion Z)).unit.app G).hom ≫
              (TopCat.Presheaf.stalkFunctor C ((closedSubsetInclusion Z) z)).map
                (((TopCat.Sheaf.pushforward C (closedSubsetInclusion Z)).map
                  e.hom).hom) =
            (TopCat.Presheaf.stalkFunctor C ((closedSubsetInclusion Z) z)).map
              (((TopCat.Sheaf.pullbackPushforwardAdjunction C
                (closedSubsetInclusion Z)).unit.app G).hom ≫
                ((TopCat.Sheaf.pushforward C (closedSubsetInclusion Z)).map
                  e.hom).hom) := by
        exact (Functor.map_comp _ _ _).symm
      rw [hmap]
      have hmapcomp' := congrArg (fun q =>
        q ≫ TopCat.Presheaf.stalkPushforward C
          (closedSubsetInclusion Z) Q z) hmapcomp
      have hcomp' := congrArg (fun q =>
        (TopCat.Presheaf.stalkFunctor C ((closedSubsetInclusion Z) z)).map q ≫
          TopCat.Presheaf.stalkPushforward C (closedSubsetInclusion Z) Q z) hcomp
      have hstep := hmapcomp'.trans hcomp'
      have hassoc :
          ((TopCat.Presheaf.stalkFunctor C ((closedSubsetInclusion Z) z)).map
                ((TopCat.Sheaf.pullbackPushforwardAdjunction C
                  (closedSubsetInclusion Z)).unit.app G).hom ≫
              (TopCat.Presheaf.stalkFunctor C ((closedSubsetInclusion Z) z)).map
                ((TopCat.Sheaf.pushforward C (closedSubsetInclusion Z)).map
                  e.hom).hom) ≫
              TopCat.Presheaf.stalkPushforward C (closedSubsetInclusion Z) Q z =
            (TopCat.Presheaf.stalkFunctor C ((closedSubsetInclusion Z) z)).map
                ((TopCat.Sheaf.pullbackPushforwardAdjunction C
                  (closedSubsetInclusion Z)).unit.app G).hom ≫
              (TopCat.Presheaf.stalkFunctor C ((closedSubsetInclusion Z) z)).map
                ((TopCat.Sheaf.pushforward C (closedSubsetInclusion Z)).map
                  e.hom).hom ≫
              TopCat.Presheaf.stalkPushforward C (closedSubsetInclusion Z) Q z := by
        exact Category.assoc _ _ _
      exact hassoc.symm.trans hstep
    _ = _ := by
      have hunit₂' :
          (TopCat.Presheaf.stalkFunctor C ((closedSubsetInclusion Z) z)).map
                ((CategoryTheory.sheafToPresheaf
                  (Opens.grothendieckTopology X) C).map
                  (adj₂.unit.app G₀)) ≫
              TopCat.Presheaf.stalkPushforward C (closedSubsetInclusion Z) Q z =
            e₂.hom := by
        simpa [ePushQ, f] using hunit₂
      rw [hunit₂']
      have hP :
          f₀.op.lan.obj G₀.obj =
            (TopCat.Presheaf.pullback C (closedSubsetInclusion Z)).obj
              G.presheaf := by
        rfl
      have hP' :
          (TopCat.Presheaf.stalkFunctor C z).map
              (CategoryTheory.toSheafify K (f₀.op.lan.obj G₀.obj)) =
            (TopCat.Presheaf.stalkFunctor C z).map
              (CategoryTheory.toSheafify K
                ((TopCat.Presheaf.pullback C (closedSubsetInclusion Z)).obj
                  G.presheaf)) := by
        rfl
      cases hP
      simp [e₂, u, f, f₀, G₀, P₂, P, K]
      have hP'' :
          (TopCat.Presheaf.stalkFunctor C z).map
              (CategoryTheory.toSheafify
                (Opens.grothendieckTopology (TopCat.of Z))
                ((Opens.map (closedSubsetInclusion Z)).op.lan.obj G.obj)) =
            (TopCat.Presheaf.stalkFunctor C z).map
              (CategoryTheory.toSheafify
                (Opens.grothendieckTopology (TopCat.of Z))
                ((TopCat.Presheaf.pullback C (closedSubsetInclusion Z)).obj
                  G.presheaf)) := by
        simpa [f₀, G₀] using hP'
      cases hP''
      have he' :
          (TopCat.Presheaf.stalkFunctor C z).map e'.inv ≫
              (TopCat.Presheaf.stalkFunctor C z).map e'.hom =
            𝟙 _ := by
        rw [← Functor.map_comp]
        rw [e'.inv_hom_id]
        exact (TopCat.Presheaf.stalkFunctor C (X := TopCat.of Z) z).map_id _
      let b := (asIso
          ((TopCat.Presheaf.stalkFunctor C z).map
            (CategoryTheory.toSheafify K
              ((TopCat.Presheaf.pullback C (closedSubsetInclusion Z)).obj
                G.presheaf)))).hom
      have hcancel :
          (b ≫ (TopCat.Presheaf.stalkFunctor C z).map e'.inv) ≫
          (TopCat.Presheaf.stalkFunctor C z).map e'.hom =
        b := by
        set_option backward.isDefEq.respectTransparency false in
          rw [Category.assoc, he']
        exact Category.comp_id b
      set_option backward.isDefEq.respectTransparency false in
        rw [hcancel]
      rfl
private theorem closedSubsetPushforward_mem_essImage_iff_of_category
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [HasTerminal C]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (G : TopCat.Sheaf C X) :
    (closedSubsetPushforward (C := C) Z).essImage G ↔
      ∀ x : X, x ∉ Z →
        Nonempty (TopCat.Presheaf.stalk (C := C) G.presheaf x ≅ (⊤_ C)) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction C
    (closedSubsetInclusion Z)
  let : IsIso adj.counit :=
    closedSubsetPushforward_counit_isIso_of_category (C := C) hZ
  let hff : (closedSubsetPushforward (C := C) Z).FullyFaithful :=
    adj.fullyFaithfulROfIsIsoCounit
  let : (closedSubsetPushforward (C := C) Z).Full := hff.full
  let : (closedSubsetPushforward (C := C) Z).Faithful := hff.faithful
  rw [← adj.isIso_unit_app_iff_mem_essImage]
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  constructor
  · intro h x hx
    rcases closedSubsetPushforward_stalkIso_terminal_of_not_mem
        (C := C) hZ
        ((TopCat.Sheaf.pullback C (closedSubsetInclusion Z)).obj G) hx with ⟨e⟩
    exact ⟨(asIso ((TopCat.Presheaf.stalkFunctor C x).map
      (adj.unit.app G).hom)).trans e⟩
  · intro h x
    by_cases hx : x ∈ Z
    · let z : Z := ⟨x, hx⟩
      let eStalk := closedSubsetPushforward_stalkIso (C := C) hZ
        ((TopCat.Sheaf.pullback C (closedSubsetInclusion Z)).obj G) z
      haveI : IsIso eStalk.hom := eStalk.isIso_hom
      have hcomp : IsIso
          ((TopCat.Presheaf.stalkFunctor C (closedSubsetInclusion Z z)).map
              (adj.unit.app G).hom ≫ eStalk.hom) := by
        rw [closedSubsetPushforward_unit_stalk_comp (C := C) hZ G z]
        exact (closedSubsetPullbackStalkIso G z).isIso_hom
      letI : IsIso
          ((TopCat.Presheaf.stalkFunctor C (closedSubsetInclusion Z z)).map
              (adj.unit.app G).hom ≫ eStalk.hom) := hcomp
      exact @IsIso.of_isIso_comp_right _ _ _ _ _
        ((TopCat.Presheaf.stalkFunctor C (closedSubsetInclusion Z z)).map
          (adj.unit.app G).hom) eStalk.hom eStalk.isIso_hom hcomp
    · rcases h x hx with ⟨eG⟩
      let F := (TopCat.Sheaf.pullback C (closedSubsetInclusion Z)).obj G
      rcases closedSubsetPushforward_stalkIso_terminal_of_not_mem
          (C := C) hZ F hx with ⟨eF⟩
      letI : IsIso eG.hom := eG.isIso_hom
      letI : IsIso eF.inv := eF.isIso_inv
      have hm :
          (TopCat.Presheaf.stalkFunctor C x).map (adj.unit.app G).hom =
            eG.hom ≫ eF.inv := by
        apply (cancel_mono eF.hom).1
        exact terminalIsTerminal.hom_ext _ _
      rw [hm]
      exact (eG.trans eF.symm).isIso_hom
theorem closedSubsetAbelianPushforward_mem_essImage_iff
    {X : TopCat.{w}} {Z : Set X}
    (hZ : IsClosed Z) (G : TopCat.Sheaf AddCommGrpCat.{w} X) :
    (closedSubsetAbelianPushforward Z).essImage G ↔
      closedSubsetAbelian_zeroStalkCondition Z G := by
  change (closedSubsetPushforward (C := AddCommGrpCat.{w}) Z).essImage G ↔ _
  rw [closedSubsetPushforward_mem_essImage_iff_of_category
    (C := AddCommGrpCat.{w}) hZ G]
  constructor
  · intro h x hx
    rcases h x hx with ⟨e⟩
    exact ⟨e ≪≫ (HasZeroObject.zeroIsoTerminal :
      (0 : AddCommGrpCat.{w}) ≅ (⊤_ AddCommGrpCat.{w})).symm⟩
  · intro h x hx
    rcases h x hx with ⟨e⟩
    exact ⟨e ≪≫ (HasZeroObject.zeroIsoTerminal :
      (0 : AddCommGrpCat.{w}) ≅ (⊤_ AddCommGrpCat.{w}))⟩
noncomputable abbrev closedSubsetStructurePullback
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} (Z : Set X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (TopCat.of Z) :=
  TopCat.Sheaf.pullback C (closedSubsetInclusion Z)

/-- The generic sheaf pullback/pushforward adjunction for a closed subset. -/
noncomputable abbrev closedSubsetStructureAdjunction
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} (Z : Set X) :
    closedSubsetStructurePullback (C := C) Z ⊣ closedSubsetPushforward (C := C) Z :=
  TopCat.Sheaf.pullbackPushforwardAdjunction C (closedSubsetInclusion Z)

/-- Generic terminal-stalk condition for sheaves of algebraic structures. -/
abbrev closedSubsetTerminalStalkCondition
    {C : Type u} [Category.{w} C] [HasColimits C] [HasTerminal C]
    {X : TopCat.{w}}
    (Z : Set X) (G : TopCat.Sheaf C X) : Prop :=
  ∀ x : X, x ∉ Z →
    Nonempty (TopCat.Presheaf.stalk (C := C) (X := X) G.presheaf x ≅ (⊤_ C))

/-- Generic counit form of `i⁻¹ i_* ≅ id` for algebraic-structure sheaves. -/
theorem closedSubsetPushforward_inverseImage_counit_isIso
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    IsIso ((closedSubsetStructureAdjunction (C := C) Z).counit) := by
  change IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C
    (closedSubsetInclusion Z)).counit)
  exact closedSubsetPushforward_counit_isIso_of_category
    (C := C) hZ
noncomputable def closedSubsetStructure_inverseImagePushforwardIso
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    closedSubsetPushforward (C := C) Z ⋙
        closedSubsetStructurePullback (C := C) Z ≅
      𝟭 (TopCat.Sheaf C (TopCat.of Z)) := by
  let : IsIso (closedSubsetStructureAdjunction (C := C) Z |>.counit) :=
    closedSubsetPushforward_inverseImage_counit_isIso hZ
  exact asIso (closedSubsetStructureAdjunction (C := C) Z |>.counit)
theorem closedSubsetPushforward_fullyFaithful
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (closedSubsetPushforward (C := C) Z).FullyFaithful := by
  let : IsIso (closedSubsetStructureAdjunction (C := C) Z |>.counit) :=
    closedSubsetPushforward_inverseImage_counit_isIso hZ
  exact ⟨closedSubsetStructureAdjunction (C := C) Z |>.fullyFaithfulROfIsIsoCounit⟩
theorem closedSubsetPushforward_mem_essImage_iff
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (G : TopCat.Sheaf C X) :
    (closedSubsetPushforward (C := C) Z).essImage G ↔
      closedSubsetTerminalStalkCondition Z G := by
  exact closedSubsetPushforward_mem_essImage_iff_of_category
    (C := C) hZ G
def singletonSheaf (X : TopCat.{w}) : Sh.{w, w} X :=
  constantSheaf X (PUnit : Type w)

/-- The sheaf coproduct of two singleton sheaves is the source's two-point example. -/
abbrev twoPointSheaf (X : TopCat.{w}) : Sh.{w, w} X :=
  singletonSheaf X ⨿ singletonSheaf X

/-- Outside the closed subset, the two-point coproduct stalk is not the
    coproduct of the two singleton pushforward stalks. -/
theorem closedSubsetSetPushforward_stalk_twoPoint_mismatch
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (x : X) (hx : x ∉ Z) :
    ¬ Nonempty
      ((((closedSubsetSetPushforward Z).obj (twoPointSheaf (TopCat.of Z))).presheaf.stalk x) ≃
        (((closedSubsetSetPushforward Z).obj (singletonSheaf (TopCat.of Z))).presheaf.stalk x) ⊕
          (((closedSubsetSetPushforward Z).obj (singletonSheaf (TopCat.of Z))).presheaf.stalk x)) := by sorry
theorem closedSubsetSetPushforward_not_rightExact
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (x : X) (hx : x ∉ Z) :
    ¬ IsRightExact (closedSubsetSetPushforward Z) := by sorry
theorem closedSubsetSetPushforward_no_rightAdjoint
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (x : X) (hx : x ∉ Z) :
    ¬ ∃ (R : Sh.{w, w} X ⥤ Sh.{w, w} (TopCat.of Z)),
      Nonempty (closedSubsetSetPushforward Z ⊣ R) := by sorry
