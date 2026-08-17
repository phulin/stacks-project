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

/-! ## The closed-subset inclusion and pushforward -/

/- The source fixes a closed subset `Z ⊆ X` and writes `i : Z → X` for its
   inclusion.  `TopCat.of Z` is the induced-subspace topology, so this is the
   canonical concrete morphism rather than a parallel topological-space type. -/

/-- The canonical inclusion of a subset with its induced topology. -/
def closedSubsetInclusion {X : TopCat.{w}} (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The subtype inclusion is a closed embedding when the subset is closed. -/
theorem closedSubsetInclusion_isClosedEmbedding {X : TopCat.{w}} {Z : Set X}
    (hZ : IsClosed Z) : IsClosedEmbedding (closedSubsetInclusion Z) := by
  change IsClosedEmbedding ((↑) : Z → X)
  exact hZ.isClosedEmbedding_subtypeVal

/-- Pushforward of sheaves of objects of a category along a subset inclusion. -/
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
  letI : IsIso (TopCat.Presheaf.stalkPushforward C
      (closedSubsetInclusion Z) F.presheaf z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      C (f := closedSubsetInclusion Z)
      (closedSubsetInclusion_isClosedEmbedding hZ).isInducing F.presheaf z
  change ((TopCat.Presheaf.pushforward C (closedSubsetInclusion Z)).obj
      F.presheaf).stalk (closedSubsetInclusion Z z) ≅ F.presheaf.stalk z
  exact asIso (TopCat.Presheaf.stalkPushforward C
    (closedSubsetInclusion Z) F.presheaf z)

/- The source writes a stalk outside the closed subset as the singleton.  For
   a general category of algebraic structures, the invariant formulation is
   an isomorphism with the chosen terminal object. -/

/-- A pushforward stalk away from the closed subset is isomorphic to terminal. -/
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
    change IsTerminal (F.presheaf.obj (op ((Opens.map (closedSubsetInclusion Z)).obj U.1)))
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

/-- Set-valued form of the outside stalk calculation, with `PUnit` as singleton. -/
theorem closedSubsetSetPushforward_stalk_equiv_punit_of_not_mem
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : Sh.{w, w} (TopCat.of Z)) {x : X} (hx : x ∉ Z) :
    Nonempty (((closedSubsetSetPushforward Z).obj F).presheaf.stalk x ≃
      (PUnit : Type w)) := by
  rcases closedSubsetPushforward_stalkIso_terminal_of_not_mem
      (C := Type w) hZ F hx with ⟨e⟩
  exact ⟨e.toEquiv.trans Types.terminalIso.toEquiv⟩

/-- Set-valued stalk comparison at a point of the closed subset. -/
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
    simp only [NatTrans.id_app, Category.id_comp, Category.comp_id]
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
    letI : ∀ z : Z, IsIso
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
      letI : IsIso uP := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        (X := TopCat.of Z) (p₀ := z) (C := C) P
      letI : IsIso uQ := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        (X := TopCat.of Z) (p₀ := z) (C := C) Q
      letI : IsIso p := hφ z
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
      letI : IsIso (TopCat.Presheaf.stalkPushforward C f F.presheaf z) :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
          C (closedSubsetInclusion_isClosedEmbedding hZ).isInducing F.presheaf z
      letI : IsIso (TopCat.Presheaf.stalkPullbackIso C f
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
  letI : f₀.IsContinuous J K := by
    dsimp [f₀, f]
    apply Functor.isContinuous_of_coverPreserving
    · exact compatiblePreserving_opens_map (closedSubsetInclusion Z)
    · exact coverPreserving_opens_map (closedSubsetInclusion Z)
  let adj₂ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    f₀ C J K
  letI : IsIso (adj₀.counit.app F') := hc
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
      letI : IsIso (comm1₃.inv.app (R₃.obj F')) :=
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
      letI : IsIso ((Iso.refl
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
    letI : IsIso (adj₃.counit.app F') := hc₃
    rw [← huniq]
    infer_instance
  letI : IsIso (adj₂.counit.app F') := hc₂
  let e₀ := (TopCat.Sheaf.pullbackPushforwardAdjunction C f).leftAdjointUniq adj₂
  letI : IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).leftAdjointUniq adj₂).hom.app
      ((TopCat.Sheaf.pushforward C f).obj F')) := by
    change IsIso (e₀.hom.app ((TopCat.Sheaf.pushforward C f).obj F'))
    exact (e₀.app ((TopCat.Sheaf.pushforward C f).obj F')).isIso_hom
  have huniq₀ := Adjunction.leftAdjointUniq_hom_app_counit
    (TopCat.Sheaf.pullbackPushforwardAdjunction C f) adj₂ F'
  rw [← huniq₀]
  letI : IsIso (e₀.hom.app ((TopCat.Sheaf.pushforward C f).obj F')) :=
    (e₀.app ((TopCat.Sheaf.pushforward C f).obj F')).isIso_hom
  change IsIso (e₀.hom.app ((TopCat.Sheaf.pushforward C f).obj F') ≫ adj₂.counit.app F')
  exact IsIso.comp_isIso'
    (e₀.app ((TopCat.Sheaf.pushforward C f).obj F')).isIso_hom hc₂

/-- The counit of `i⁻¹ i_* ⊣ id` is an isomorphism for set sheaves. -/
theorem closedSubsetSet_inverseImage_pushforward_counit_isIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    IsIso (closedSubsetSetAdjunction Z |>.counit) := by
  exact closedSubsetPushforward_counit_isIso_of_category hZ

/-- The source's identity `i⁻¹ i_* ≅ id` on sheaves of sets. -/
noncomputable def closedSubsetSet_inverseImagePushforwardIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    closedSubsetSetPushforward Z ⋙ closedSubsetSetPullback Z ≅
      𝟭 (Sh.{w, w} (TopCat.of Z)) := by
  letI : IsIso (closedSubsetSetAdjunction Z |>.counit) :=
    closedSubsetSet_inverseImage_pushforward_counit_isIso hZ
  exact asIso (closedSubsetSetAdjunction Z).counit

/-! ## Full faithfulness and essential image -/

/-- The stalk condition describing the set-valued essential image. -/
abbrev closedSubsetSet_terminalStalkCondition
    {X : TopCat.{w}} (Z : Set X) (G : Sh.{w, w} X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty (G.presheaf.stalk x ≃ (PUnit : Type w))

/-- Pushforward along a closed subset inclusion is fully faithful for sets. -/
theorem closedSubsetSetPushforward_fullyFaithful
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (closedSubsetSetPushforward Z).FullyFaithful := by
  letI : IsIso (closedSubsetSetAdjunction Z |>.counit) :=
    closedSubsetSet_inverseImage_pushforward_counit_isIso hZ
  exact ⟨(closedSubsetSetAdjunction Z).fullyFaithfulROfIsIsoCounit⟩

/-- Its essential image consists exactly of sheaves with singleton outside stalks. -/
theorem closedSubsetSetPushforward_mem_essImage_iff
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) (G : Sh.{w, w} X) :
    (closedSubsetSetPushforward Z).essImage G ↔
      closedSubsetSet_terminalStalkCondition Z G := by
  let hff := (closedSubsetSetPushforward_fullyFaithful hZ).some
  letI : (closedSubsetSetPushforward Z).Full := hff.full
  letI : (closedSubsetSetPushforward Z).Faithful := hff.faithful
  have hu := Adjunction.isIso_unit_app_iff_mem_essImage
    (closedSubsetSetAdjunction Z) (Y := G)
  rw [← hu]
  constructor
  · intro h
    letI : IsIso ((closedSubsetSetAdjunction Z).unit.app G) := h
    letI : IsIso ((closedSubsetSetAdjunction Z).unit.app G).hom := by
      exact Functor.map_isIso (TopCat.Sheaf.forget (Type w) X) _
    intro x hx
    rcases closedSubsetSetPushforward_stalk_equiv_punit_of_not_mem hZ
        ((closedSubsetSetPullback Z).obj G) hx with ⟨e⟩
    exact ⟨(asIso ((TopCat.Presheaf.stalkFunctor (Type w) x).map
        ((closedSubsetSetAdjunction Z).unit.app G).hom)).toEquiv.trans e⟩
  · intro h
    letI : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor (Type w) x).map
        ((closedSubsetSetAdjunction Z).unit.app G).hom) := by
      intro x
      by_cases hx : x ∈ Z
      · let z : Z := ⟨x, hx⟩
        let F := (closedSubsetSetPullback Z).obj G
        let eP := pullbackSheafStalkIso (closedSubsetInclusion Z) G z
        let eS := closedSubsetPushforward_stalkIso (C := Type w) hZ F z
        let m := (TopCat.Presheaf.stalkFunctor (Type w) x).map
          ((closedSubsetSetAdjunction Z).unit.app G).hom
        let f₀ : Opens X ⥤ Opens (TopCat.of Z) :=
          Opens.map (closedSubsetInclusion Z)
        let J := Opens.grothendieckTopology X
        let K := Opens.grothendieckTopology (TopCat.of Z)
        letI : f₀.IsContinuous J K := by
          dsimp [f₀]
          apply Functor.isContinuous_of_coverPreserving
          · exact compatiblePreserving_opens_map (closedSubsetInclusion Z)
          · exact coverPreserving_opens_map (closedSubsetInclusion Z)
        have hu := Adjunction.unit_leftAdjointUniq_hom_app
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w)
            (closedSubsetInclusion Z))
          (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            f₀ (Type w) J K) G
        let e₀ := (TopCat.Sheaf.pullbackIso (Type w)
          (closedSubsetInclusion Z)).app G
        let eMapIso := (TopCat.Presheaf.stalkFunctor (Type w) z).mapIso
          ((sheafToPresheaf K (Type w)).mapIso e₀)
        let F' : TopCat.Sheaf (Type w) (TopCat.of Z) :=
          (Functor.sheafPullbackConstruction.sheafPullback
            f₀ (Type w) J K).obj G
        let eS' := closedSubsetPushforward_stalkIso (C := Type w) hZ F' z
        have hpush :
            (TopCat.Presheaf.stalkFunctor (Type w) x).map
                (((TopCat.Sheaf.pushforward (Type w) (closedSubsetInclusion Z)).map
                  e₀.hom).hom) ≫ eS'.hom =
              eS.hom ≫ eMapIso.hom := by
          apply TopCat.Presheaf.stalk_hom_ext _
          intro U hU
          dsimp [eS', eS, eMapIso, closedSubsetPushforward_stalkIso]
          change
            ((TopCat.Sheaf.pushforward (Type w) (closedSubsetInclusion Z)).obj
                ((TopCat.Sheaf.pullback (Type w) (closedSubsetInclusion Z)).obj G)).presheaf.germ
                U x hU ≫
              (TopCat.Presheaf.stalkFunctor (Type w) x).map
                (((TopCat.Sheaf.pushforward (Type w) (closedSubsetInclusion Z)).map
                  e₀.hom).hom) ≫
              TopCat.Presheaf.stalkPushforward (Type w)
                (closedSubsetInclusion Z) F'.presheaf z =
            ((TopCat.Sheaf.pushforward (Type w) (closedSubsetInclusion Z)).obj
                ((TopCat.Sheaf.pullback (Type w) (closedSubsetInclusion Z)).obj G)).presheaf.germ
                U x hU ≫
              TopCat.Presheaf.stalkPushforward (Type w)
                (closedSubsetInclusion Z) F.presheaf z ≫
              (TopCat.Presheaf.stalkFunctor (Type w) z).map
                ((sheafToPresheaf K (Type w)).mapIso e₀).hom
          let P : TopCat.Presheaf (Type w) X :=
            ((TopCat.Sheaf.pushforward (Type w) (closedSubsetInclusion Z)).obj
              ((TopCat.Sheaf.pullback (Type w) (closedSubsetInclusion Z)).obj G)).presheaf
          let Q : TopCat.Presheaf (Type w) X :=
            ((TopCat.Sheaf.pushforward (Type w) (closedSubsetInclusion Z)).obj F').presheaf
          let α : P ⟶ Q :=
            ((TopCat.Sheaf.pushforward (Type w) (closedSubsetInclusion Z)).map e₀.hom).hom
          let β : Q.stalk x ⟶ F'.presheaf.stalk z :=
            TopCat.Presheaf.stalkPushforward (Type w)
              (closedSubsetInclusion Z) F'.presheaf z
          let β₀ : P.stalk x ⟶ F.presheaf.stalk z :=
            TopCat.Presheaf.stalkPushforward (Type w)
              (closedSubsetInclusion Z) F.presheaf z
          let δ : F.presheaf.stalk z ⟶ F'.presheaf.stalk z :=
            (TopCat.Presheaf.stalkFunctor (Type w) z).map
              ((sheafToPresheaf K (Type w)).map e₀.hom)
          have hmap :
              P.germ U x hU ≫
                  (TopCat.Presheaf.stalkFunctor (Type w) x).map α =
                α.app (op U) ≫ Q.germ U x hU := by
            exact TopCat.Presheaf.stalkFunctor_map_germ U x hU α
          have hpush' : Q.germ U x hU ≫ β =
              F'.presheaf.germ ((Opens.map (closedSubsetInclusion Z)).obj U)
                z hU := by
            exact TopCat.Presheaf.stalkPushforward_germ (Type w)
              (closedSubsetInclusion Z) F'.presheaf U z hU
          have hpush₀ : P.germ U x hU ≫ β₀ =
              F.presheaf.germ ((Opens.map (closedSubsetInclusion Z)).obj U)
                z hU := by
            exact TopCat.Presheaf.stalkPushforward_germ (Type w)
              (closedSubsetInclusion Z) F.presheaf U z hU
          have hmap' :
              F.presheaf.germ ((Opens.map (closedSubsetInclusion Z)).obj U)
                  z hU ≫ δ =
                ((sheafToPresheaf K (Type w)).map e₀.hom).app
                    (op ((Opens.map (closedSubsetInclusion Z)).obj U)) ≫
                  F'.presheaf.germ ((Opens.map (closedSubsetInclusion Z)).obj U)
                    z hU := by
            exact TopCat.Presheaf.stalkFunctor_map_germ
              ((Opens.map (closedSubsetInclusion Z)).obj U) z hU
              ((sheafToPresheaf K (Type w)).map e₀.hom)
          change P.germ U x hU ≫
                (TopCat.Presheaf.stalkFunctor (Type w) x).map α ≫ β =
              P.germ U x hU ≫ β₀ ≫ δ
          calc
            P.germ U x hU ≫
                  (TopCat.Presheaf.stalkFunctor (Type w) x).map α ≫ β =
                (P.germ U x hU ≫
                  (TopCat.Presheaf.stalkFunctor (Type w) x).map α) ≫ β := by
                    rw [Category.assoc]
            _ = (α.app (op U) ≫ Q.germ U x hU) ≫ β :=
              congrArg (fun q => q ≫ β) hmap
            _ = α.app (op U) ≫
                  F'.presheaf.germ ((Opens.map (closedSubsetInclusion Z)).obj U)
                    z hU := by
              rw [Category.assoc, hpush']
            _ = ((sheafToPresheaf K (Type w)).map e₀.hom).app
                  (op ((Opens.map (closedSubsetInclusion Z)).obj U)) ≫
                  F'.presheaf.germ ((Opens.map (closedSubsetInclusion Z)).obj U)
                    z hU := by
              rfl
            _ = F.presheaf.germ ((Opens.map (closedSubsetInclusion Z)).obj U)
                  z hU ≫ δ := hmap'.symm
            _ = (P.germ U x hU ≫ β₀) ≫ δ := by
              rw [hpush₀]
        have hcomp : m ≫ eS.hom = eP.hom := by
          apply (cancel_mono eMapIso.hom).1
          apply TopCat.Presheaf.stalk_hom_ext _
          intro U hU
          simp [m, eP, eS, F, pullbackSheafStalkIso,
            pullbackSheaf_sheafificationIso,
            pullbackPresheafStalkIso, TopCat.Presheaf.germ_stalkPullbackHom,
            e₀, eMapIso, hu]
        change IsIso m
        rw [← hcomp]
        infer_instance
      · rcases h x hx with ⟨eG⟩
        rcases closedSubsetSetPushforward_stalk_equiv_punit_of_not_mem hZ
            ((closedSubsetSetPullback Z).obj G) hx with ⟨eT⟩
        apply (isIso_iff_bijective _).2
        constructor
        · intro a b hab
          apply eG.injective
          exact Subsingleton.elim _ _
        · intro b
          refine ⟨eG.symm PUnit.unit, ?_⟩
          apply eT.injective
          exact Subsingleton.elim _ _
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

/-! ## Abelian and generic algebraic-structure versions -/

/-- Pushforward of abelian sheaves along the closed subset inclusion. -/
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
  rcases closedSubsetPushforward_stalkIso_terminal_of_not_mem
      (C := AddCommGrpCat.{w}) hZ F hx with ⟨e⟩
  exact ⟨e.trans (terminalIsTerminal.uniqueUpToIso (isZero_zero _).isTerminal)⟩

/-- The abelian stalk comparison at a point of the closed subset. -/
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
  exact closedSubsetPushforward_counit_isIso_of_category hZ

/-- The source's identity `i⁻¹ i_* ≅ id` for abelian sheaves. -/
noncomputable def closedSubsetAbelian_inverseImagePushforwardIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    closedSubsetAbelianPushforward Z ⋙ closedSubsetAbelianPullback Z ≅
      𝟭 (TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z)) := by
  letI : IsIso (closedSubsetAbelianAdjunction Z |>.counit) :=
    closedSubsetAbelian_inverseImage_pushforward_counit_isIso hZ
  exact asIso (closedSubsetAbelianAdjunction Z).counit

/-- The stalk condition describing the abelian essential image. -/
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
  letI : IsIso (closedSubsetAbelianAdjunction Z |>.counit) :=
    closedSubsetAbelian_inverseImage_pushforward_counit_isIso hZ
  exact ⟨(closedSubsetAbelianAdjunction Z).fullyFaithfulROfIsIsoCounit⟩

/-- Its abelian essential image consists exactly of sheaves with zero outside stalks. -/
theorem closedSubsetAbelianPushforward_mem_essImage_iff
    {X : TopCat.{w}} {Z : Set X}
    (hZ : IsClosed Z) (G : TopCat.Sheaf AddCommGrpCat.{w} X) :
    (closedSubsetAbelianPushforward Z).essImage G ↔
      closedSubsetAbelian_zeroStalkCondition Z G := by
  sorry

/-- Pullback of algebraic-structure sheaves along the closed-subset inclusion. -/
/- The source's generic inverse image is Mathlib's canonical sheaf pullback;
   the assumptions are exactly those required by that existing construction. -/
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
  exact closedSubsetPushforward_counit_isIso_of_category hZ

/-- The source's identity `i⁻¹ i_* ≅ id` for algebraic-structure sheaves. -/
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
  letI : IsIso ((closedSubsetStructureAdjunction (C := C) Z).counit) :=
    closedSubsetPushforward_inverseImage_counit_isIso hZ
  exact asIso (closedSubsetStructureAdjunction (C := C) Z).counit

/-- Generic full faithfulness of closed-subset pushforward. -/
theorem closedSubsetPushforward_fullyFaithful
    {C : Type u} [Category.{w} C]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (closedSubsetPushforward (C := C) Z).FullyFaithful := by
  sorry

/-- Generic form of the essential-image characterization. -/
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
  sorry

/-! ## The non-exactness warning and the later abelian remark -/
/-- The singleton sheaf used in the source's coproduct counterexample. -/
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
          (((closedSubsetSetPushforward Z).obj (singletonSheaf (TopCat.of Z))).presheaf.stalk x)) := by
  intro h
  rcases h with ⟨e⟩
  rcases closedSubsetSetPushforward_stalk_equiv_punit_of_not_mem
      hZ (twoPointSheaf (TopCat.of Z)) hx with ⟨e₂⟩
  rcases closedSubsetSetPushforward_stalk_equiv_punit_of_not_mem
      hZ (singletonSheaf (TopCat.of Z)) hx with ⟨e₁⟩
  let q : (PUnit : Type w) ≃ (PUnit : Type w) ⊕ PUnit :=
    e₂.symm.trans (e.trans (Equiv.sumCongr e₁ e₁))
  have hq : q.symm (Sum.inl PUnit.unit) = q.symm (Sum.inr PUnit.unit) :=
    Subsingleton.elim _ _
  have hq' :
      (Sum.inl (PUnit.unit : PUnit) : (PUnit : Type w) ⊕ (PUnit : Type w)) =
        Sum.inr (PUnit.unit : PUnit) := by
    simpa using congrArg q hq
  exact Sum.inl_ne_inr hq'

/-- The closed-subset pushforward of set sheaves is not right exact. -/
theorem closedSubsetSetPushforward_not_rightExact
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (x : X) (hx : x ∉ Z) :
    ¬ IsRightExact (closedSubsetSetPushforward Z) := by
  intro h
  let A : Sh.{w, w} (TopCat.of Z) := singletonSheaf (TopCat.of Z)
  let F := closedSubsetSetPushforward Z
  letI : PreservesFiniteColimits F := h
  let c₀ : BinaryCofan A A :=
    BinaryCofan.mk (coprod.inl : A ⟶ A ⨿ A) coprod.inr
  have hc₀ : IsColimit c₀ := coprodIsCoprod A A
  have hF : PreservesColimit (pair A A) F := by infer_instance
  have hcF : IsColimit (F.mapCocone c₀) := (hF.preserves hc₀).some
  let c₁ : BinaryCofan (F.obj A) (F.obj A) :=
    BinaryCofan.mk (F.map (coprod.inl : A ⟶ A ⨿ A)) (F.map coprod.inr)
  have hc₁ : IsColimit c₁ :=
    (BinaryCofan.isColimitMapConeEquiv (F := F) (s := c₀)) hcF
  let S := TopCat.Sheaf.forget (Type w) X ⋙
    TopCat.Presheaf.stalkFunctor (Type w) x
  have hS : PreservesColimit (pair (F.obj A) (F.obj A)) S := by
    infer_instance
  have hcS₀ : IsColimit (S.mapCocone c₁) := (hS.preserves hc₁).some
  have hcS : IsColimit
      (BinaryCofan.mk (S.map (c₁.inl)) (S.map (c₁.inr))) :=
    (BinaryCofan.isColimitMapConeEquiv (F := S) (s := c₁)) hcS₀
  let e : S.obj (F.obj (A ⨿ A)) ≅
      S.obj (F.obj A) ⨿ S.obj (F.obj A) :=
    hcS.coconePointUniqueUpToIso
      (colimit.isColimit (pair (S.obj (F.obj A)) (S.obj (F.obj A))))
  apply closedSubsetSetPushforward_stalk_twoPoint_mismatch hZ x hx
  refine ⟨?_⟩
  exact (e.trans (Types.binaryCoproductIso _ _)).toEquiv

/-- Consequently, set-valued closed-subset pushforward has no right adjoint. -/
theorem closedSubsetSetPushforward_no_rightAdjoint
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (x : X) (hx : x ∉ Z) :
    ¬ ∃ (R : Sh.{w, w} X ⥤ Sh.{w, w} (TopCat.of Z)),
      Nonempty (closedSubsetSetPushforward Z ⊣ R) := by
  rintro ⟨R, ⟨hR⟩⟩
  apply closedSubsetSetPushforward_not_rightExact hZ x hx
  exact Formalization.Books.Categories.Unit24.left_adjoint_is_right_exact hR

/- The source defers exactness and the right adjoint for abelian sheaves to
   the later Modules chapter; those results are intentionally not declared
   here.  It likewise defers the relationship with ringed-space closed
   immersions to the later quasi-coherent-sheaves discussion. -/

end

end Formalization.Books.Sheaves.Unit32
