import Formalization.Books.Sheaves.Unit22.Bases
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves on Spaces, Chapter 22, Section 10: Open immersions

The restriction functors use Mathlib's pullback and open-subspace sheaf
restriction APIs.  Extension by the initial object is kept as a named
interface, since its concrete sectionwise construction depends on the value
category; its sheaf version is obtained by sheafification.
-/

namespace Formalization.Books.Sheaves.Unit22

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
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

/-- The open-subspace sheaf restriction has the corresponding presheaf. -/
theorem openSheafRestriction_formula (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C X) :
    Nonempty (((openSheafRestriction C U).obj F).presheaf ≅
      (openPresheafRestriction C U).obj F.presheaf) := by
  sorry

/-- Restriction preserves the stalk at a point of the open subspace. -/
theorem openSheafRestriction_stalk_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C X)
    (u : openSubspace U) :
    Nonempty (((openSheafRestriction C U).obj F).presheaf.stalk u ≅
      F.presheaf.stalk ((openInclusion U) u)) := by
  sorry

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
  sorry

/-- Restriction followed by direct image is the identity on sheaves of an open subspace. -/
theorem openSheafRestriction_directImage_iso {C : Type u} [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C (openSubspace U)) :
    Nonempty ((openSheafRestriction C U).obj
      ((openSheafDirectImage C U).obj F) ≅ F) := by
  sorry

/-! ## Extension by the initial object -/

/-- Extension by the initial object at the presheaf level. -/
noncomputable def openPresheafExtensionByInitial (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X := by
  classical
  let j := Opens.map (openInclusion U)
  exact {
    obj := fun F => {
      obj := fun V => if V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C
      map := by
        intro V W i
        by_cases hV : V.unop ≤ U
        · have hW : W.unop ≤ U := by
            exact (show W.unop ≤ V.unop from i.unop).trans hV
          exact eqToHom (by simp [hV]) ≫ F.map (j.op.map i) ≫
            eqToHom (by simp [hW])
        · exact eqToHom (by simp [hV]) ≫ initial.to _
      map_id := by
        sorry
      map_comp := by
        sorry
    }
    map := fun {F G} φ => {
      app := fun V => if hV : V.unop ≤ U then
          eqToHom (by simp [hV]) ≫ φ.app (j.op.obj V) ≫
            eqToHom (by simp [hV])
        else eqToHom (by simp [hV]) ≫ initial.to _
      naturality := by
        sorry
    }
    map_id := by
      sorry
    map_comp := by
      sorry
  }

/-- Extension by the empty set for set-valued presheaves. -/
noncomputable abbrev openPresheafExtensionByEmpty {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf (Type v) (openSubspace U) ⥤ TopCat.Presheaf (Type v) X :=
  openPresheafExtensionByInitial (Type v) U

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

/-- The presheaf extension/restriction adjunction. -/
noncomputable def openPresheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    openPresheafExtensionByInitial C U ⊣ openPresheafRestriction C U := by
  sorry

/-- The sheaf extension/restriction adjunction. -/
noncomputable def openSheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    openSheafExtensionByInitial C U ⊣ openSheafRestriction C U := by
  sorry

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

/-- Extension by zero for modules on an open subspace. -/
noncomputable def openModuleExtensionFunctor (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod (ringedOpenSubspace X U).structureSheaf ⥤ Mod X.structureSheaf := by
  sorry

/-- Restriction of modules to an open subspace. -/
noncomputable abbrev openModuleRestrictionFunctor (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod X.structureSheaf ⥤ Mod (ringedOpenSubspace X U).structureSheaf :=
  ringedSpaceModulePullback (ringedOpenInclusion X U)

/-- The module extension/restriction adjunction for an open subspace. -/
noncomputable def openModuleExtensionAdjunction (X : RingedSpace.{v}) (U : Opens X.carrier) :
    openModuleExtensionFunctor X U ⊣ openModuleRestrictionFunctor X U := by
  sorry

/-- Module stalks of extension by zero vanish outside the open. -/
theorem openModuleExtension_stalk_zero (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) (x : X.carrier) (hx : x ∉ U) :
    Nonempty (TopCat.Presheaf.stalk (C := Type v)
      (((openModuleExtensionFunctor X U).obj F).val.presheaf ⋙
        (CategoryTheory.forget AddCommGrpCat)) x ≃ PUnit.{v}) := by
  sorry

/-- Module stalks of extension by zero agree with the original stalk on the open. -/
theorem openModuleExtension_stalk_iso (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) (x : X.carrier) (hx : x ∈ U) :
    Nonempty (TopCat.Presheaf.stalk (C := Type v)
      (((openModuleExtensionFunctor X U).obj F).val.presheaf ⋙
        (CategoryTheory.forget AddCommGrpCat)) x ≃
      TopCat.Presheaf.stalk (C := Type v)
        (F.val.presheaf ⋙ (CategoryTheory.forget AddCommGrpCat)) ⟨x, hx⟩) := by
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
    (openSetSheafExtensionByEmpty U).Full := by
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
    (openAbelianSheafExtensionFunctor U).Full := by
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
    (openAlgebraicSheafExtensionFunctor C U).Full := by
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
    (openModuleExtensionFunctor X U).Full := by
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
