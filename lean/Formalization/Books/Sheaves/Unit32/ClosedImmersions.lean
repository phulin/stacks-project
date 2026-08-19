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
  letI : (closedSubsetSetPushforward Z).Full := hff.full
  letI : (closedSubsetSetPushforward Z).Faithful := hff.faithful
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
      letI : IsIso e₂.hom := e₂.isIso_hom
      have hpush_map {P Q : TopCat.Presheaf (Type w) (TopCat.of Z)}
          (φ : P ⟶ Q) :
          (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
              ((TopCat.Presheaf.pushforward (Type w) f).map φ) ≫
            TopCat.Presheaf.stalkPushforward (Type w) f Q z =
          TopCat.Presheaf.stalkPushforward (Type w) f P z ≫
            (TopCat.Presheaf.stalkFunctor (Type w) z).map φ := by
        set_option backward.isDefEq.respectTransparency false in
        exact TopCat.Presheaf.stalk_hom_ext _ (fun U hxU => by
          rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
          rw [TopCat.Presheaf.stalkPushforward_germ]
          rw [TopCat.Presheaf.stalkPushforward_germ_assoc]
          rw [TopCat.Presheaf.stalkFunctor_map_germ]
          rw [TopCat.Presheaf.pushforward_map_app'])
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
          TopCat.Presheaf.stalkPullbackHom, Category.assoc]
        have hnat :
            (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
                (f₀.op.whiskerLeft
                  (CategoryTheory.toSheafify
                    (Opens.grothendieckTopology (TopCat.of Z))
                    (f₀.op.lan.obj G.obj))) ≫
              TopCat.Presheaf.stalkPushforward (Type w) f P₂ z =
            TopCat.Presheaf.stalkPushforward (Type w) f
                (f₀.op.lan.obj G.obj) z ≫
              (TopCat.Presheaf.stalkFunctor (Type w) z).map
                (CategoryTheory.toSheafify
                  (Opens.grothendieckTopology (TopCat.of Z))
                  (f₀.op.lan.obj G.obj)) := by
          set_option backward.isDefEq.respectTransparency false in
          simpa [TopCat.Presheaf.pushforward] using
            (hpush_map (P := f₀.op.lan.obj G.obj) (Q := P₂)
              (CategoryTheory.toSheafify
                (Opens.grothendieckTopology (TopCat.of Z))
                (f₀.op.lan.obj G.obj)))
        set_option backward.isDefEq.respectTransparency false in
        rw [Category.assoc, hnat]
        rfl
      letI : IsIso
          ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
            ((closedSubsetSetPushforward Z).map (e₀.hom.app G)).hom) := by
        letI : IsIso (e₀.hom.app G) := (e₀.app G).isIso_hom
        letI : IsIso ((closedSubsetSetPushforward Z).map (e₀.hom.app G)) := by
          exact Functor.map_isIso _ _
        letI : IsIso (((closedSubsetSetPushforward Z).map
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
      letI : IsIso
          ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
              (adj₂.unit.app G).hom ≫ ePush₂.hom) := by
        letI : IsIso e₂.hom := e₂.isIso_hom
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
      letI : IsIso ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
          (adj₂.unit.app G).hom) := by
        exact hIsoAdj₂
      letI : IsIso ((TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
          (adj.unit.app G).hom ≫
        (TopCat.Presheaf.stalkFunctor (Type w) (f z)).map
          ((closedSubsetSetPushforward Z).map (e₀.hom.app G)).hom) := by
        rw [hcomp]
        exact hIsoAdj₂
      letI : IsIso
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
      𝟭 (TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z)) := by sorry
abbrev closedSubsetAbelian_zeroStalkCondition
    {X : TopCat.{w}} (Z : Set X)
    (G : TopCat.Sheaf AddCommGrpCat.{w} X) : Prop :=
  ∀ x : X, x ∉ Z →
    Nonempty (TopCat.Presheaf.stalk (C := AddCommGrpCat.{w}) (X := X)
      G.presheaf x ≅ (0 : AddCommGrpCat.{w}))

/-- Pushforward along a closed subset inclusion is fully faithful for abelian sheaves. -/
theorem closedSubsetAbelianPushforward_fullyFaithful
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (closedSubsetAbelianPushforward Z).FullyFaithful := by sorry
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
      ((TopCat.Sheaf.pullback C (closedSubsetInclusion Z)).obj G).presheaf.stalk z := by sorry
private lemma category_comp_iso_inv_hom_cancel
    {C : Type u} [Category.{w} C]
    {A B D E F : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E)
    (e : F ≅ E) :
    (f ≫ g ≫ h ≫ e.inv) ≫ e.hom = f ≫ g ≫ h := by sorry
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
    (closedSubsetPullbackStalkIso G z).hom := by sorry
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
        Nonempty (TopCat.Presheaf.stalk (C := C) G.presheaf x ≅ (⊤_ C)) := by sorry
theorem closedSubsetAbelianPushforward_mem_essImage_iff
    {X : TopCat.{w}} {Z : Set X}
    (hZ : IsClosed Z) (G : TopCat.Sheaf AddCommGrpCat.{w} X) :
    (closedSubsetAbelianPushforward Z).essImage G ↔
      closedSubsetAbelian_zeroStalkCondition Z G := by sorry
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
    IsIso ((closedSubsetStructureAdjunction (C := C) Z).counit) := by sorry
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
      𝟭 (TopCat.Sheaf C (TopCat.of Z)) := by sorry
theorem closedSubsetPushforward_fullyFaithful
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (closedSubsetPushforward (C := C) Z).FullyFaithful := by sorry
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
      closedSubsetTerminalStalkCondition Z G := by sorry
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
