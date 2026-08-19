import Formalization.Books.Sheaves.Unit30.Infrastructure
import Formalization.Books.Sheaves.Unit06.PresheavesOfModules
import Formalization.Books.Sheaves.Unit08.AbelianSheaves
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Stalks

/-!
# Shared infrastructure for Chapter 31: Open immersions

The restriction functors use Mathlib's pullback and open-subspace sheaf
restriction APIs.  Extension by the initial object is kept as a named
interface, since its concrete sectionwise construction depends on the value
category; its sheaf version is obtained by sheafification.
-/

namespace Formalization.Books.Sheaves.Unit22

-- The historical namespace is retained for API compatibility.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.Topology
open scoped ZeroObject
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit10

universe v u

noncomputable section

/-! ## Restriction to an open subspace -/

/-- The topological space underlying an open subspace. -/
abbrev openSubspace {X : TopCat.{v}} (U : Opens X) : TopCat.{v} :=
  (Opens.toTopCat X).obj U

/-- The canonical open-subspace inclusion. -/
abbrev openInclusion {X : TopCat.{v}} (U : Opens X) : openSubspace U ⟶ X :=
  Opens.inclusion' U

/-- Pullback/restriction of presheaves to an open subspace. -/
noncomputable abbrev openPresheafRestriction (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C X ⥤ TopCat.Presheaf C (openSubspace U) :=
  TopCat.Presheaf.pullback C (openInclusion U)

/-- Direct image of presheaves along an open inclusion. -/
abbrev openPresheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X :=
  TopCat.Presheaf.pushforward C (openInclusion U)

/-- Restriction of sheaves to an open subspace. -/
abbrev openSheafRestriction (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubspace U) :=
  TopologicalSpace.Opens.sheafRestrict U

/-- Direct image of sheaves along an open inclusion. -/
abbrev openSheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pushforward C (openInclusion U)

/-- The presheaf restriction is the canonical pullback construction. -/
theorem openPresheafRestriction_formula (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C X) :
    Nonempty ((openPresheafRestriction C U).obj F ≅
      (TopCat.Presheaf.pullback C (openInclusion U)).obj F) := by
  exact ⟨Iso.refl _⟩

/-- Restriction to an open subspace is computed by taking sections over the
image open in the ambient space. -/
noncomputable def openPresheafRestriction_obj_iso (C : Type u)
    [Category.{v} C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C X) (V : Opens (openSubspace U)) :
    ((openPresheafRestriction C U).obj F).obj (op V) ≅
      F.obj (op ⟨(openInclusion U) '' V,
        (U.isOpenEmbedding.isOpenMap V V.2)⟩) := by
  exact TopCat.Presheaf.pullbackObjObjOfImageOpen
    (openInclusion U) F V (U.isOpenEmbedding.isOpenMap V V.2)

/-- The open-subspace sheaf restriction has the corresponding presheaf. -/
theorem openSheafRestriction_formula (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C X) :
    Nonempty (((openSheafRestriction C U).obj F).presheaf ≅
      (openPresheafRestriction C U).obj F.presheaf) := by
  refine ⟨?_⟩
  let H : IsOpenEmbedding (TopCat.Hom.hom (TopCat.ofHom ⟨_, continuous_subtype_val⟩)) :=
    U.isOpenEmbedding
  let : H.functor.IsContinuous (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X) := H.functor_isContinuous
  exact (H.isOpenMap.functor.sheafPushforwardContinuousCompSheafToPresheafIso
      C (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X)).app F ≪≫
    (H.isOpenMap.pullbackObjIso F.presheaf).symm

/-- Sections of a sheaf restricted to an open subspace are the ambient
sections over the corresponding image open. -/
theorem openSheafRestriction_obj_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C X)
    (V : Opens (openSubspace U)) :
    Nonempty ((((openSheafRestriction C U).obj F).presheaf).obj (op V) ≅
      F.presheaf.obj (op ⟨(openInclusion U) '' V,
        (U.isOpenEmbedding.isOpenMap V V.2)⟩)) := by
  rcases openSheafRestriction_formula C U F with ⟨e⟩
  exact ⟨e.app (op V) ≪≫ openPresheafRestriction_obj_iso C U F.presheaf V⟩

/-- Restriction preserves the stalk at a point of the open subspace. -/
theorem openSheafRestriction_stalk_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C X)
    (u : openSubspace U) :
    Nonempty (((openSheafRestriction C U).obj F).presheaf.stalk u ≅
      F.presheaf.stalk ((openInclusion U) u)) := by
  rcases openSheafRestriction_formula C U F with ⟨e⟩
  exact ⟨(TopCat.Presheaf.stalkFunctor C u).mapIso e ≪≫
    (TopCat.Presheaf.stalkPullbackIso C (openInclusion U) F.presheaf u).symm⟩

/-- An epimorphism of additive sheaves is epimorphic on every stalk. -/
theorem openAbelianSheaf_stalk_map_epi {X : TopCat.{v}}
    {F G : TopCat.Sheaf AddCommGrpCat.{v} X} (f : F ⟶ G) [Epi f] (x : X) :
    Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks f.hom).mp
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr inferInstance

/-- Direct image is computed by inverse images of opens. -/
@[simp] theorem openPresheafDirectImage_obj (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) (V : Opens X) :
    ((openPresheafDirectImage C U).obj F).obj (op V) =
      F.obj (op ((Opens.map (openInclusion U)).obj V)) := rfl

/-- Restriction followed by direct image is the identity on presheaves of an open subspace. -/
theorem openPresheafRestriction_directImage_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) :
    Nonempty ((openPresheafRestriction C U).obj
      ((openPresheafDirectImage C U).obj F) ≅ F) := by
  let f := openInclusion U
  refine ⟨?_⟩
  let hf := U.isOpenEmbedding
  have hfun : hf.functor ⋙ Opens.map f = 𝟭 _ := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro V
      exact TopologicalSpace.Opens.map_functor_eq' f hf V
    · subsingleton
  let e : hf.functor.op ⋙ (TopCat.Presheaf.pushforward C f).obj F ≅ F :=
    eqToIso (by
      dsimp [TopCat.Presheaf.pushforward]
      change ((hf.functor ⋙ Opens.map f).op ⋙ F) = F
      rw [hfun]
      rfl)
  exact (hf.isOpenMap.pullbackObjIso ((TopCat.Presheaf.pushforward C f).obj F)) ≪≫ e

/-- Restriction followed by direct image is the identity on sheaves of an open subspace. -/
theorem openSheafRestriction_directImage_iso {C : Type u} [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C (openSubspace U)) :
    Nonempty ((openSheafRestriction C U).obj
      ((openSheafDirectImage C U).obj F) ≅ F) := by
  let f := openInclusion U
  let hf := U.isOpenEmbedding
  have hfun : hf.functor ⋙ Opens.map f = 𝟭 _ := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro V
      exact TopologicalSpace.Opens.map_functor_eq' f hf V
    · subsingleton
  have hobj :
      (openSheafRestriction C U).obj ((openSheafDirectImage C U).obj F) = F := by
    apply ObjectProperty.FullSubcategory.ext
    dsimp [openSheafRestriction, openSheafDirectImage, TopCat.Sheaf.pushforward,
      Functor.sheafPushforwardContinuous]
    change ((hf.functor ⋙ Opens.map f).op ⋙ F.presheaf) = F.presheaf
    rw [hfun]
    rfl
  exact ⟨eqToIso hobj⟩

/-- Direct image along an open inclusion is fully faithful. -/
theorem openSheafDirectImage_fullFaithful (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    Nonempty (openSheafDirectImage C U).FullyFaithful := by
  let f := openInclusion U
  let hf := U.isOpenEmbedding
  have hfun : hf.functor ⋙ Opens.map f = 𝟭 _ := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro V
      exact TopologicalSpace.Opens.map_functor_eq' f hf V
    · subsingleton
  have hcont : hf.functor.IsContinuous (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X) := hf.functor_isContinuous
  let adj₀ := hf.isOpenMap.adjunction
  let adj : openSheafRestriction C U ⊣ openSheafDirectImage C U :=
    adj₀.sheafPushforwardContinuous
    (Opens.grothendieckTopology (openSubspace U))
    (Opens.grothendieckTopology X)
  have hIso : IsIso adj.counit := by
    have hF : ∀ F, IsIso (adj.counit.app F) := by
      intro F
      apply (ObjectProperty.isIso_hom_iff
        (adj.counit.app F)).mp
      change IsIso ((adj₀.op.whiskerLeft _).counit.app F.presheaf)
      have hV : ∀ V, IsIso (((adj₀.op.whiskerLeft _).counit.app F.presheaf).app V) := by
        intro V
        dsimp [CategoryTheory.Adjunction.whiskerLeft]
        rw [show adj₀.op.counit.app V =
          eqToHom (by
            change op ((hf.functor ⋙ Opens.map f).obj V.unop) = V
            rw [hfun]
            rfl) from Subsingleton.elim _ _]
        infer_instance
      exact NatIso.isIso_of_isIso_app _
    exact NatIso.isIso_of_isIso_app _
  exact ⟨adj.fullyFaithfulROfIsIsoCounit⟩

/-! ## Extension by the initial object -/

/-- Extension by the initial object at the presheaf level. -/
noncomputable def openPresheafExtensionByInitial (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X := by
  classical
  let j := Opens.map (openInclusion U)
  exact {
    obj := fun F => {
      obj := fun V => if hV : V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C
      map := by
        intro V W i
        by_cases hV : V.unop ≤ U
        · have hW : W.unop ≤ U := by
            exact (show W.unop ≤ V.unop from leOfHom i.unop).trans hV
          exact eqToHom (by simp [hV]) ≫ F.map (j.op.map i) ≫
            eqToHom (by simp [hW])
        · exact eqToHom (by simp [hV]) ≫ initial.to _
      map_id := by
        intro V
        by_cases hV : V.unop ≤ U
        · simp [hV]
        · let e : (if V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C) ≅ (⊥_ C) :=
            eqToIso (if_neg hV)
          rw [← cancel_epi e.inv]
          simp only [dif_neg hV]
          exact initial.hom_ext _ _
      map_comp := by
        intro V W T i k
        by_cases hV : V.unop ≤ U
        · have hW : W.unop ≤ U := by
            exact (show W.unop ≤ V.unop from leOfHom i.unop).trans hV
          have hT : T.unop ≤ U := by
            exact (show T.unop ≤ W.unop from leOfHom k.unop).trans hW
          simp [hV, hW, hT]
        · let e : (if V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C) ≅ (⊥_ C) :=
            eqToIso (if_neg hV)
          rw [← cancel_epi e.inv]
          simp only [dif_neg hV]
          exact initial.hom_ext _ _
    }
    map := fun {F G} φ => {
      app := fun V => if hV : V.unop ≤ U then
          eqToHom (by simp [hV]) ≫ φ.app (j.op.obj V) ≫
            eqToHom (by simp [hV])
        else eqToHom (by simp [hV]) ≫ initial.to _
      naturality := by
        intro V W i
        by_cases hV : V.unop ≤ U
        · have hW : W.unop ≤ U := by
            exact (show W.unop ≤ V.unop from leOfHom i.unop).trans hV
          simp [hV, hW]
        · let e : (if V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C) ≅ (⊥_ C) :=
            eqToIso (if_neg hV)
          rw [← cancel_epi e.inv]
          simp only [dif_neg hV]
          exact initial.hom_ext _ _
      }
    map_id := by
      intro F
      sorry
    map_comp := by
      intro F G H φ ψ
      sorry
  }

/-- On opens contained in `U`, extension by the initial object has the original
sections. -/
@[simp] theorem openPresheafExtensionByInitial_obj_of_le (C : Type u)
    [Category.{v} C] [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) (V : Opens X) (hV : V ≤ U) :
    ((openPresheafExtensionByInitial C U).obj F).obj (op V) =
      F.obj (op ((Opens.map (openInclusion U)).obj V)) := by
  simp [openPresheafExtensionByInitial, hV]

/-- On opens not contained in `U`, extension by the initial object has the
initial section object. -/
@[simp] theorem openPresheafExtensionByInitial_obj_of_not_le (C : Type u)
    [Category.{v} C] [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) (V : Opens X) (hV : ¬ V ≤ U) :
    ((openPresheafExtensionByInitial C U).obj F).obj (op V) = (⊥_ C) := by
  simp [openPresheafExtensionByInitial, hV]

/-- Extension by the empty set for set-valued presheaves. -/
noncomputable abbrev openPresheafExtensionByEmpty {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf (Type v) (openSubspace U) ⥤ TopCat.Presheaf (Type v) X :=
  openPresheafExtensionByInitial (Type v) U

/-! The same initial-object construction for abelian and algebraic
presheaves. -/

noncomputable abbrev openAbelianPresheafExtensionByZero {X : TopCat.{v}}
    (U : Opens X) :
    AbelianPresheaf (openSubspace U) ⥤ AbelianPresheaf X :=
  openPresheafExtensionByInitial AddCommGrpCat U

noncomputable abbrev openAlgebraicPresheafExtensionByInitial
    (C : Type u) [Category.{v} C] [HasInitial C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X :=
  openPresheafExtensionByInitial C U

/-- Sheafification of extension by the initial object. -/
noncomputable def openSheafExtensionByInitial (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C X := by
  exact (TopCat.Sheaf.forget C (openSubspace U) ⋙
    openPresheafExtensionByInitial C U ⋙
    CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C)

/-- Extension by the empty set for sheaves of sets. -/
noncomputable abbrev openSetSheafExtensionByEmpty {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    TopCat.Sheaf (Type v) (openSubspace U) ⥤ TopCat.Sheaf (Type v) X :=
  openSheafExtensionByInitial (Type v) U

noncomputable abbrev openAbelianSheafExtensionByZero {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    Ab (openSubspace U) ⥤ Ab X :=
  openSheafExtensionByInitial AddCommGrpCat U

/-- The presheaf extension/restriction adjunction. -/
theorem exists_openPresheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    Nonempty (openPresheafExtensionByInitial C U ⊣ openPresheafRestriction C U) := by
  sorry

/-- The presheaf extension/restriction adjunction. -/
noncomputable def openPresheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    openPresheafExtensionByInitial C U ⊣ openPresheafRestriction C U := by
  exact Classical.choice (exists_openPresheafExtensionAdjunction C U)

noncomputable abbrev openAbelianPresheafExtensionAdjunction
    {X : TopCat.{v}} (U : Opens X) :
    openAbelianPresheafExtensionByZero U ⊣ openPresheafRestriction AddCommGrpCat U :=
  openPresheafExtensionAdjunction AddCommGrpCat U

/-- The sheaf extension/restriction adjunction. -/
theorem exists_openSheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    Nonempty (openSheafExtensionByInitial C U ⊣ openSheafRestriction C U) := by
  sorry

/-- The sheaf extension/restriction adjunction. -/
noncomputable def openSheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    openSheafExtensionByInitial C U ⊣ openSheafRestriction C U := by
  exact Classical.choice (exists_openSheafExtensionAdjunction C U)

/-- Restricting the presheaf extension by the initial object recovers the
original presheaf on the open subspace. -/
theorem openPresheafExtension_restrict_iso (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) :
    Nonempty ((openPresheafRestriction C U).obj
      ((openPresheafExtensionByInitial C U).obj F) ≅ F) := by
  sorry

/-- Restricting the sheaf extension by the initial object recovers the
original sheaf on the open subspace. -/
theorem openAlgebraicSheafExtension_restrict_iso (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : TopCat.Sheaf C (openSubspace U)) :
    Nonempty ((openSheafRestriction C U).obj
      ((openSheafExtensionByInitial C U).obj F) ≅ F) := by
  sorry

/-- The set-valued Hom correspondence for extension by the empty set. -/
noncomputable abbrev openSetSheafExtensionHomEquiv {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) (G : TopCat.Sheaf (Type v) X) :
    ((openSetSheafExtensionByEmpty U).obj F ⟶ G) ≃
      (F ⟶ (openSheafRestriction (Type v) U).obj G) :=
  (openSheafExtensionAdjunction (Type v) U).homEquiv F G

/-- Outside the open, extension by the empty set has empty stalks. -/
theorem openSetSheafExtension_stalk_empty {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) (x : X) (hx : x ∉ U) :
    IsEmpty (((openSetSheafExtensionByEmpty U).obj F).presheaf.stalk x) := by
  sorry

/-- On the open, extension by the empty set has the original stalk. -/
theorem openSetSheafExtension_stalk_iso {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) (x : X) (hx : x ∈ U) :
    Nonempty (((openSetSheafExtensionByEmpty U).obj F).presheaf.stalk x ≃
      F.presheaf.stalk ⟨x, hx⟩) := by
  sorry

/-- Restricting an extension by the empty set recovers the original sheaf. -/
theorem openSetSheafExtension_restrict_iso {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) :
    Nonempty ((openSheafRestriction (Type v) U).obj
      ((openSetSheafExtensionByEmpty U).obj F) ≅ F) := by
  sorry

/-! ## Algebraic structures and modules -/

/-- Extension by the initial object for a category-valued sheaf. -/
noncomputable def openAlgebraicSheafExtensionFunctor (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C X :=
  openSheafExtensionByInitial C U

/-- The algebraic-structure extension/restriction adjunction. -/
noncomputable def openAlgebraicSheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    openAlgebraicSheafExtensionFunctor C U ⊣ openSheafRestriction C U := by
  exact openSheafExtensionAdjunction C U

/-- Initial stalk outside the open for an algebraic-structure extension. -/
theorem openAlgebraicSheafExtension_stalk_initial (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : TopCat.Sheaf C (openSubspace U)) (x : X) (hx : x ∉ U) :
    Nonempty (((openAlgebraicSheafExtensionFunctor C U).obj F).presheaf.stalk x ≅
      (⊥_ C)) := by
  sorry

/-- The original stalk on the open for an algebraic-structure extension. -/
theorem openAlgebraicSheafExtension_stalk_iso (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : TopCat.Sheaf C (openSubspace U)) (x : X) (hx : x ∈ U) :
    Nonempty (((openAlgebraicSheafExtensionFunctor C U).obj F).presheaf.stalk x ≅
      F.presheaf.stalk ⟨x, hx⟩) := by
  sorry

/-- Abelian sheaf extension by zero. -/
noncomputable abbrev openAbelianSheafExtensionFunctor {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :=
  openAlgebraicSheafExtensionFunctor AddCommGrpCat U

/-- The abelian sheaf extension/restriction adjunction. -/
noncomputable abbrev openAbelianSheafExtensionAdjunction
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    openAbelianSheafExtensionFunctor U ⊣
      openSheafRestriction AddCommGrpCat U :=
  openAlgebraicSheafExtensionAdjunction AddCommGrpCat U

/-- The module-valued open subspace of a ringed space. -/
def ringedOpenSubspace (X : RingedSpace.{v}) (U : Opens X.carrier) : RingedSpace.{v} where
  carrier := openSubspace U
  structureSheaf := (TopologicalSpace.Opens.sheafRestrict U).obj X.structureSheaf

/-- The canonical morphism of ringed spaces from an open subspace. -/
noncomputable def ringedOpenInclusion (X : RingedSpace.{v}) (U : Opens X.carrier) :
    RingedSpaceHom (ringedOpenSubspace X U) X where
  continuous := openInclusion U
  sharp := by
    let hU : IsOpenEmbedding (openInclusion U) := U.isOpenEmbedding
    exact (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
      (openInclusion U)).unit.app X.structureSheaf ≫
      (TopCat.Sheaf.pushforward RingCat (openInclusion U)).map
        ((Topology.IsOpenEmbedding.sheafPullbackIso (A := RingCat) hU).app
          X.structureSheaf).hom

 /-- A module extension by zero together with its underlying additive
presheaf identification. -/
 structure OpenModulePresheafExtensionData (X : RingedSpace.{v})
    (U : Opens X.carrier) where
  functor : PMod (ringedOpenSubspace X U).structureSheaf.obj ⥤
    PMod X.structureSheaf.obj
  restriction : PMod X.structureSheaf.obj ⥤
    PMod (ringedOpenSubspace X U).structureSheaf.obj
  underlying_functor_iso :
    Nonempty
      (functor ⋙ PresheafOfModules.toPresheaf X.structureSheaf.obj ≅
        PresheafOfModules.toPresheaf (ringedOpenSubspace X U).structureSheaf.obj ⋙
          openPresheafExtensionByInitial AddCommGrpCat U)
  adjunction : functor ⊣ restriction

 /-- Extension by zero for modules on an open subspace. -/
theorem exists_openModulePresheafExtensionByZero (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty (OpenModulePresheafExtensionData X U) := by
  sorry

noncomputable def openModulePresheafExtensionData (X : RingedSpace.{v})
    (U : Opens X.carrier) : OpenModulePresheafExtensionData X U :=
  Classical.choice (exists_openModulePresheafExtensionByZero X U)

/-! The module-valued presheaf construction is the initial-object extension
on the underlying additive presheaf, equipped with the ambient structure-sheaf
action.  Its categorical interface is chosen from the source construction. -/
noncomputable def openModulePresheafExtensionByZero (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    PMod (ringedOpenSubspace X U).structureSheaf.obj ⥤
      PMod X.structureSheaf.obj :=
  (openModulePresheafExtensionData X U).functor

/-- The underlying additive presheaf of module extension by zero is the
initial-object extension. -/
theorem openModulePresheafExtension_underlying_iso (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty
      (openModulePresheafExtensionByZero X U ⋙
          PresheafOfModules.toPresheaf X.structureSheaf.obj ≅
        PresheafOfModules.toPresheaf
            (ringedOpenSubspace X U).structureSheaf.obj ⋙
          openPresheafExtensionByInitial AddCommGrpCat U) :=
  (openModulePresheafExtensionData X U).underlying_functor_iso

/-- Restriction of presheaves of modules to an open subspace. -/
noncomputable def openModulePresheafRestrictionFunctor (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    PMod X.structureSheaf.obj ⥤
      PMod (ringedOpenSubspace X U).structureSheaf.obj :=
  (openModulePresheafExtensionData X U).restriction

/-- The presheaf-module extension by zero is left adjoint to restriction. -/
theorem exists_openModulePresheafExtensionAdjunction (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty (openModulePresheafExtensionByZero X U ⊣
      openModulePresheafRestrictionFunctor X U) := by
  exact ⟨(openModulePresheafExtensionData X U).adjunction⟩

noncomputable def openModulePresheafExtensionAdjunction (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    openModulePresheafExtensionByZero X U ⊣
      openModulePresheafRestrictionFunctor X U :=
  (openModulePresheafExtensionData X U).adjunction

/-- Extension by zero for modules on an open subspace. -/
noncomputable def openModuleExtensionFunctor (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod (ringedOpenSubspace X U).structureSheaf ⥤ Mod X.structureSheaf := by
  exact
    SheafOfModules.forget (ringedOpenSubspace X U).structureSheaf ⋙
      openModulePresheafExtensionByZero X U ⋙
      PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)

theorem exists_openModuleExtensionFunctor (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty (Mod (ringedOpenSubspace X U).structureSheaf ⥤ Mod X.structureSheaf) :=
  ⟨openModuleExtensionFunctor X U⟩

noncomputable abbrev openModuleSheafExtensionByZero (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Mod (ringedOpenSubspace X U).structureSheaf ⥤ Mod X.structureSheaf :=
  openModuleExtensionFunctor X U

/-- Restriction of modules to an open subspace. -/
noncomputable def openModuleRestrictionFunctor (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod X.structureSheaf ⥤ Mod (ringedOpenSubspace X U).structureSheaf := by
  letI : (SheafOfModules.pushforward (ringedOpenInclusion X U).sharp).IsRightAdjoint := by
    sorry
  exact ringedSpaceModulePullback (ringedOpenInclusion X U)

/-- The module extension/restriction adjunction for an open subspace. -/
theorem exists_openModuleExtensionAdjunction (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (openModuleExtensionFunctor X U ⊣ openModuleRestrictionFunctor X U) := by
  sorry

/-- The module extension/restriction adjunction for an open subspace. -/
noncomputable def openModuleExtensionAdjunction (X : RingedSpace.{v}) (U : Opens X.carrier) :
    openModuleExtensionFunctor X U ⊣ openModuleRestrictionFunctor X U := by
  exact Classical.choice (exists_openModuleExtensionAdjunction X U)

/-- Module stalks of extension by zero vanish outside the open. -/
theorem openModuleExtension_stalk_zero (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) (x : X.carrier) (hx : x ∉ U) :
    Nonempty ((moduleStalkFunctor X.structureSheaf x).obj
      ((openModuleExtensionFunctor X U).obj F) ≅ 0) := by
  sorry

/-- Module stalks of extension by zero agree with the original stalk on the open. -/
theorem openModuleExtension_stalk_iso (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) (x : X.carrier) (hx : x ∈ U) :
    Nonempty ((moduleStalkFunctor X.structureSheaf x).obj
      ((openModuleExtensionFunctor X U).obj F) ≅
      (ModuleCat.restrictScalars
        (moduleSheafFMapStalkScalarMap
          (ringedOpenInclusion X U).sharp ⟨x, hx⟩).hom).obj
        ((moduleStalkFunctor (ringedOpenSubspace X U).structureSheaf
          ⟨x, hx⟩).obj F)) := by
  sorry

/-- The module restriction of extension by zero is the identity. -/
theorem openModuleExtension_restrict_iso (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) :
    Nonempty ((openModuleRestrictionFunctor X U).obj
      ((openModuleExtensionFunctor X U).obj F) ≅ F) := by
  sorry

/-! ## Essential images and exactness warnings -/

/-- The set-valued essential-image stalk condition for `j_!`. -/
def OpenEmptyStalkCondition {X : TopCat.{v}} (U : Opens X)
    (G : TopCat.Sheaf (Type v) X) : Prop :=
  ∀ x : X, x ∉ U → IsEmpty (G.presheaf.stalk x)

/-- Extension by the empty set is fully faithful. -/
theorem openSetSheafExtension_fullFaithful {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    Nonempty (openSetSheafExtensionByEmpty U).FullyFaithful := by
  sorry

/-- The essential image of `j_!` is characterized by empty outside stalks. -/
theorem openSetSheafExtension_essentialImage {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (G : TopCat.Sheaf (Type v) X) :
    (∃ F, Nonempty ((openSetSheafExtensionByEmpty U).obj F ≅ G)) ↔
      OpenEmptyStalkCondition U G := by
  sorry

/-- Extension by zero for abelian sheaves is fully faithful. -/
theorem openAbelianSheafExtension_fullFaithful {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    Nonempty (openAbelianSheafExtensionFunctor U).FullyFaithful := by
  sorry

/-- The abelian essential image of extension by zero is characterized by
zero stalks outside the open. -/
def OpenAbelianZeroStalkCondition {X : TopCat.{v}} (U : Opens X)
    (G : Ab X) : Prop :=
  ∀ x : X, x ∉ U → Nonempty (G.presheaf.stalk x ≅ (0 : AddCommGrpCat.{v}))

theorem openAbelianSheafExtension_essentialImage {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    (G : Ab X) :
    (∃ F, Nonempty ((openAbelianSheafExtensionFunctor U).obj F ≅ G)) ↔
      OpenAbelianZeroStalkCondition U G := by
  sorry

/-- The generic algebraic essential image of extension by the initial object
is characterized by initial stalks outside the open. -/
def OpenInitialStalkCondition (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X) [HasColimits C]
    (G : TopCat.Sheaf C X) : Prop :=
  ∀ x : X, x ∉ U → Nonempty (G.presheaf.stalk x ≅ (⊥_ C))

theorem openAlgebraicSheafExtension_fullFaithful (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    Nonempty (openAlgebraicSheafExtensionFunctor C U).FullyFaithful := by
  sorry

theorem openAlgebraicSheafExtension_essentialImage (C : Type u)
    [Category.{v} C] [HasInitial C] [HasColimits C]
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (G : TopCat.Sheaf C X) :
    (∃ F, Nonempty ((openAlgebraicSheafExtensionFunctor C U).obj F ≅ G)) ↔
      OpenInitialStalkCondition C U G := by
  sorry

/-- Extension by zero for modules is fully faithful. -/
theorem openModuleExtension_fullFaithful (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (openModuleExtensionFunctor X U).FullyFaithful := by
  sorry

/-- The module essential image of extension by zero is characterized by zero
stalk modules outside the open. -/
def OpenModuleZeroStalkCondition (X : RingedSpace.{v})
    (U : Opens X.carrier) (G : Mod X.structureSheaf) : Prop :=
  ∀ x : X.carrier, x ∉ U →
    Nonempty ((moduleStalkFunctor X.structureSheaf x).obj G ≅ 0)

theorem openModuleExtension_essentialImage (X : RingedSpace.{v})
    (U : Opens X.carrier) (G : Mod X.structureSheaf) :
    (∃ F, Nonempty ((openModuleExtensionFunctor X U).obj F ≅ G)) ↔
      OpenModuleZeroStalkCondition X U G := by
  sorry

/-- The set-valued `j_!` warning: a nontrivial open complement prevents left exactness. -/
theorem openSetSheafExtension_not_left_exact {X : TopCat.{v}} (U : Opens X)
    (hU : ∃ x : X, x ∉ U)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    ¬ PreservesFiniteLimits (openSetSheafExtensionByEmpty U) := by
  sorry

end

end Formalization.Books.Sheaves.Unit22
