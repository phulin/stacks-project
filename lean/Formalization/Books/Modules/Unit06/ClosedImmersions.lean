import Formalization.Books.Sheaves.Unit08.AbelianSheaves
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves of Modules, Chapter 6: Closed immersions and abelian sheaves

This file formalizes the source section `books/modules.tex:548-649`.
The notation `Ab X` is the existing `AddCommGrpCat`-valued sheaf category,
so abelian sheaves are represented by the source's sheaves of
`\underline{ℤ}_X`-modules.
-/

namespace Formalization.Books.Modules.Unit06

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.ObjectProperty
open scoped ZeroObject
open Formalization.Books.Categories.Unit23
open Formalization.Books.Sheaves.Unit08

universe v u

noncomputable section

/-! ## The closed subspace and its canonical sheaf functors -/

/- These are the canonical Mathlib constructions used by the source's closed
   immersion.  They are kept local to this chapter so that the formalization
   depends only on the general sheaf functor and stalk APIs. -/

/-- The topological space carried by a closed subset. -/
abbrev closedSubspace {X : TopCat.{v}} (Z : Set X) : TopCat.{v} :=
  TopCat.of Z

/-- The inclusion of a subset as a topological subspace. -/
abbrev closedInclusion {X : TopCat.{v}} (Z : Set X) : closedSubspace Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Direct image along the inclusion of a closed subset. -/
abbrev closedSheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z) :
    TopCat.Sheaf C (closedSubspace Z) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pushforward C (closedInclusion Z)

/-- Inverse image along the inclusion of a closed subset for abelian sheaves. -/
noncomputable abbrev closedAbelianSheafRestriction {X : TopCat.{v}}
    (Z : Set X) (_hZ : IsClosed Z) :
    Ab X ⥤ Ab (closedSubspace Z) :=
  TopCat.Sheaf.pullback (AddCommGrpCat.{v}) (closedInclusion Z)

/-- The support of an abelian sheaf, as the set of points with nonzero stalk. -/
def additiveSheafSupport {X : TopCat.{v}} (F : Ab X) : Set X :=
  {x | Nontrivial (F.presheaf.stalk x)}

/-- Vanishing of all stalks outside a closed subset. -/
def ClosedZeroStalkCondition {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z)
    (G : Ab X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty (G.presheaf.stalk x ≅ (0 : AddCommGrpCat.{v}))

/- The site-level colimit API is stated for `CategoryTheory.Sheaf`; this
   bridge exposes that existing instance for the topological specialization. -/
noncomputable instance topCatSheaf_hasFiniteColimits
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    HasFiniteColimits (TopCat.Sheaf C X) := by
  change HasFiniteColimits (CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) C)
  infer_instance

/- The additive-group colimits are constructed in Mathlib at arbitrary small
   sizes; this specializes that API to the finite-colimit class needed above. -/
theorem addCommGrpCat_hasColimitsOfSize :
    HasColimitsOfSize.{0, 0} (AddCommGrpCat.{v}) := by
  infer_instance

noncomputable instance addCommGrpCat_hasFiniteColimits :
    HasFiniteColimits (AddCommGrpCat.{v}) := by
  exact @hasFiniteColimits_of_hasColimitsOfSize (AddCommGrpCat.{v})
    inferInstance addCommGrpCat_hasColimitsOfSize

/-! ## Sections with support in a closed subset -/

/- The support of a section is the support of its germ, as in the preceding
   Modules chapter.  We spell out the additive version here because an
   abelian sheaf is not presented as a module over a chosen structure sheaf. -/

/-- The germ of an abelian-sheaf section at a point of its domain. -/
noncomputable def abelianSectionGerm {X : TopCat.{v}} {F : Ab X}
    (U : Opens X) (s : F.presheaf.obj (op U)) (x : U) :
    F.presheaf.stalk x.1 :=
  TopCat.Presheaf.germ (C := AddCommGrpCat.{v}) F.presheaf U x.1 x.property s

/-- The support of a section of an abelian sheaf, inside its open domain. -/
def abelianSectionSupport {X : TopCat.{v}} {F : Ab X} (U : Opens X)
    (s : F.presheaf.obj (op U)) : Set U :=
  {x | abelianSectionGerm U s x ≠ 0}

/-- The part of a subset of `X` seen inside an open subset `U`. -/
def closedSubsetInOpen {X : TopCat.{v}} (Z : Set X) (U : Opens X) : Set U :=
  (Subtype.val : U → X) ⁻¹' Z

/-- A section is supported in `Z` when its support is contained in `Z ∩ U`. -/
def abelianSectionSupportedInClosed {X : TopCat.{v}} (Z : Set X)
    {F : Ab X} (U : Opens X) (s : F.presheaf.obj (op U)) : Prop :=
  abelianSectionSupport U s ⊆ closedSubsetInOpen Z U

/-- The sections over `U` supported in the closed subset `Z`. -/
def abelianSectionsWithSupportInClosed {X : TopCat.{v}} (Z : Set X)
    {F : Ab X} (U : Opens X) : Set (F.presheaf.obj (op U)) :=
  {s | abelianSectionSupportedInClosed Z U s}

/-- The support of an abelian sheaf is contained in a subset of its space. -/
def abelianSheafSupportContainedIn {X : TopCat.{v}} (Z : Set X)
    (F : Ab X) : Prop :=
  additiveSheafSupport F ⊆ Z

/-- A section belongs to a categorical subsheaf when it has a lift to it. -/
def abelianSubsheafContainsSection {X : TopCat.{v}} {F : Ab X}
    (P : Subobject F) (U : Opens X) (s : F.presheaf.obj (op U)) : Prop :=
  ∃ t : (P : Ab X).presheaf.obj (op U),
    P.arrow.hom.app (op U) t = s

/-! ## The largest supported subsheaf -/

/-- There is a largest abelian subsheaf whose support is contained in `Z`. -/
theorem exists_closedSupportSubsheaf {X : TopCat.{v}} (Z : Set X)
    (_hZ : IsClosed Z) (F : Ab X) :
    ∃ P : Subobject F,
      abelianSheafSupportContainedIn Z (P : Ab X) ∧
        ∀ Q : Subobject F,
          abelianSheafSupportContainedIn Z (Q : Ab X) → Q ≤ P := by
  let U : Opens X := ⟨Zᶜ, _hZ.isOpen_compl⟩
  let j : TopCat.of U ⟶ X := Opens.inclusion' U
  let raw := (TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).obj F.presheaf
  have hraw : raw.IsSheaf := by
    apply TopCat.Presheaf.isSheaf_of_iso
      ((U.isOpenEmbedding).isOpenMap.pullbackObjIso F.presheaf).symm
    exact TopCat.Presheaf.isSheaf_of_isOpenEmbedding U.isOpenEmbedding F.2
  let ηu :=
    (TopCat.Presheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v}) j).unit.app F.presheaf
  let η : F ⟶ (TopCat.Sheaf.pushforward (AddCommGrpCat.{v}) j).obj
      (⟨raw, hraw⟩ : TopCat.Sheaf (AddCommGrpCat.{v}) (TopCat.of U)) :=
    ObjectProperty.homMk ηu
  let P : Subobject F := kernelSubobject η
  have hη (x : TopCat.of U) :
      IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (j x)).map ηu) := by
    let a := (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (j x)).map ηu
    let b : (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (j x)).obj
          ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j ⋙
            TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) j).obj F.presheaf) ⟶
          ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).obj F.presheaf).stalk x :=
      TopCat.Presheaf.stalkPushforward (AddCommGrpCat.{v}) j
        ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).obj F.presheaf) x
    have hpush : IsIso b := by
      change IsIso (TopCat.Presheaf.stalkPushforward (AddCommGrpCat.{v}) j raw x)
      exact TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        (f := j) (C := AddCommGrpCat.{v}) U.isOpenEmbedding.isInducing raw x
    letI : IsIso b := hpush
    have hcomp : IsIso (a ≫ b) := by
      change IsIso (TopCat.Presheaf.stalkPullbackHom
        (AddCommGrpCat.{v}) j F.presheaf x)
      exact (TopCat.Presheaf.stalkPullbackIso
        (AddCommGrpCat.{v}) j F.presheaf x).isIso_hom
    letI : IsIso (a ≫ b) := hcomp
    change IsIso a
    exact IsIso.of_isIso_comp_right a b
  have heta : η.1 = ηu := rfl
  have hP_support :
      abelianSheafSupportContainedIn Z (P : Ab X) := by
    intro x hx
    by_contra hnon
    have hzero : IsZero
        ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).obj
          (P : Ab X).presheaf) := by
      let k := (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map P.arrow.1
      have hk0p : P.arrow.1 ≫ ηu = 0 := by
        rw [← heta]
        exact congrArg (fun f => f.1) (kernelSubobject_arrow_comp η)
      have hcomp : k ≫
          (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map ηu = 0 := by
        rw [← Functor.map_comp, hk0p, Functor.map_zero]
      haveI : Mono k := by
        dsimp [k]
        exact TopCat.Presheaf.stalk_mono_of_mono P.arrow x
      haveI : IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map ηu) :=
        hη ⟨x, hnon⟩
      rw [IsZero.iff_id_eq_zero]
      apply (cancel_mono k).1
      simp only [CategoryTheory.Category.id_comp, zero_comp]
      apply (cancel_mono
        ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map ηu)).1
      simpa only [zero_comp] using hcomp
    exact (not_nontrivial_iff_subsingleton.mpr
      (AddCommGrpCat.subsingleton_of_isZero hzero)) hx
  refine ⟨P, hP_support, ?_⟩
  intro Q hQ
  let rawQ := (TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).obj
    (Q : Ab X).presheaf
  have hrawQ : rawQ.IsSheaf := by
    apply TopCat.Presheaf.isSheaf_of_iso
      ((U.isOpenEmbedding).isOpenMap.pullbackObjIso (Q : Ab X).presheaf).symm
    exact TopCat.Presheaf.isSheaf_of_isOpenEmbedding U.isOpenEmbedding (Q : Ab X).2
  let SQ : TopCat.Sheaf (AddCommGrpCat.{v}) (TopCat.of U) := ⟨rawQ, hrawQ⟩
  have hQzero : IsZero SQ := by
    rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
    intro x
    have hnot : ¬ Nontrivial ((Q : Ab X).presheaf.stalk (j x)) := by
      intro h
      exact x.property (hQ h)
    have hzQ : IsZero
        ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (j x)).obj
          (Q : Ab X).presheaf) := by
      rw [AddCommGrpCat.isZero_iff_subsingleton]
      exact not_nontrivial_iff_subsingleton.mp hnot
    change IsZero (rawQ.stalk x)
    exact (TopCat.Presheaf.stalkPullbackIso
      (AddCommGrpCat.{v}) j (Q : Ab X).presheaf x).isZero_iff.mp hzQ
  have hpushzero : IsZero
      ((TopCat.Sheaf.pushforward (AddCommGrpCat.{v}) j).obj SQ) := by
    exact Functor.map_isZero _ hQzero
  let ηQu :=
    (TopCat.Presheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v}) j).unit.app
      (Q : Ab X).presheaf
  let ηQ : (Q : Ab X) ⟶ (TopCat.Sheaf.pushforward (AddCommGrpCat.{v}) j).obj SQ :=
    ObjectProperty.homMk ηQu
  have hηQzero : ηQ = 0 := by
    exact hpushzero.eq_of_tgt _ _
  let qmap : SQ ⟶ (⟨raw, hraw⟩ : TopCat.Sheaf (AddCommGrpCat.{v}) (TopCat.of U)) :=
    ObjectProperty.homMk
      ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).map Q.arrow.1)
  have hsq : Q.arrow ≫ η =
      ηQ ≫ (TopCat.Sheaf.pushforward (AddCommGrpCat.{v}) j).map qmap := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro s
    have hn := congr_app
      ((TopCat.Presheaf.pullbackPushforwardAdjunction
        (AddCommGrpCat.{v}) j).unit.naturality Q.arrow.1) V
    exact congrArg (fun f => f s) hn
  have hzero : Q.arrow ≫ η = 0 := by
    rw [hsq, hηQzero, zero_comp]
  exact le_kernelSubobject η Q hzero

/-- The canonical largest abelian subsheaf supported in `Z`. -/
noncomputable def closedSupportSubsheaf {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) : Subobject F :=
  Classical.choose (exists_closedSupportSubsheaf Z hZ F)

theorem closedSupportSubsheaf_supportContainedIn {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) :
    abelianSheafSupportContainedIn Z
      (closedSupportSubsheaf Z hZ F : Ab X) := by
  exact (Classical.choose_spec (exists_closedSupportSubsheaf Z hZ F)).1

theorem closedSupportSubsheaf_isLargest {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) (Q : Subobject F)
    (hQ : abelianSheafSupportContainedIn Z (Q : Ab X)) :
    Q ≤ closedSupportSubsheaf Z hZ F := by
  exact (Classical.choose_spec (exists_closedSupportSubsheaf Z hZ F)).2 Q hQ

/-- Sections of the largest subsheaf are exactly the supported sections. -/
theorem closedSupportSubsheaf_section_iff {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) (U : Opens X)
    (s : F.presheaf.obj (op U)) :
    abelianSubsheafContainsSection (closedSupportSubsheaf Z hZ F) U s ↔
      s ∈ abelianSectionsWithSupportInClosed Z U := by
  constructor
  · rintro ⟨t, ht⟩
    intro x hx
    change abelianSectionGerm U s x ≠ 0 at hx
    change (x : X) ∈ Z
    by_contra hnot
    have hPnot : ¬ Nontrivial
        ((closedSupportSubsheaf Z hZ F : Ab X).presheaf.stalk (x : X)) := by
      intro hP
      exact hnot (closedSupportSubsheaf_supportContainedIn Z hZ F hP)
    have hPsub : Subsingleton
        ((closedSupportSubsheaf Z hZ F : Ab X).presheaf.stalk (x : X)) :=
      not_nontrivial_iff_subsingleton.mp hPnot
    have ht0 :
        (closedSupportSubsheaf Z hZ F : Ab X).presheaf.germ U (x : X) x.property t = 0 := by
      exact Subsingleton.elim _ _
    have hs0 : F.presheaf.germ U (x : X) x.property s = 0 := by
      have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply U (x : X) x.property
        (closedSupportSubsheaf Z hZ F).arrow.1 t
      change (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (x : X)).map
            (closedSupportSubsheaf Z hZ F).arrow.1
            ((closedSupportSubsheaf Z hZ F : Ab X).presheaf.germ U (x : X)
              x.property t) =
          F.presheaf.germ U (x : X) x.property
            (((closedSupportSubsheaf Z hZ F).arrow.hom.app (op U)) t) at hmap
      rw [← ht, ← hmap, ht0]
      change (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (x : X)).map
          (closedSupportSubsheaf Z hZ F).arrow.1)) 0 = 0
      exact map_zero _
    exact hx hs0
  · intro hs
    change ∀ x : U, abelianSectionGerm U s x ≠ 0 → (x : X) ∈ Z at hs
    let Uc : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩
    let j : TopCat.of Uc ⟶ X := Opens.inclusion' Uc
    let raw := (TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).obj F.presheaf
    have hraw : raw.IsSheaf := by
      apply TopCat.Presheaf.isSheaf_of_iso
        ((Uc.isOpenEmbedding).isOpenMap.pullbackObjIso F.presheaf).symm
      exact TopCat.Presheaf.isSheaf_of_isOpenEmbedding Uc.isOpenEmbedding F.2
    let ηu :=
      (TopCat.Presheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v}) j).unit.app
        F.presheaf
    let η : F ⟶ (TopCat.Sheaf.pushforward (AddCommGrpCat.{v}) j).obj
        (⟨raw, hraw⟩ : TopCat.Sheaf (AddCommGrpCat.{v}) (TopCat.of Uc)) :=
      ObjectProperty.homMk ηu
    have hη (x : TopCat.of Uc) :
        IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (j x)).map ηu) := by
      let a := (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (j x)).map ηu
      let b : (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (j x)).obj
            ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j ⋙
              TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) j).obj F.presheaf) ⟶
            ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).obj F.presheaf).stalk x :=
        TopCat.Presheaf.stalkPushforward (AddCommGrpCat.{v}) j
          ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).obj F.presheaf) x
      have hpush : IsIso b := by
        change IsIso (TopCat.Presheaf.stalkPushforward (AddCommGrpCat.{v}) j raw x)
        exact TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
          (f := j) (C := AddCommGrpCat.{v}) Uc.isOpenEmbedding.isInducing raw x
      letI : IsIso b := hpush
      have hcomp : IsIso (a ≫ b) := by
        change IsIso (TopCat.Presheaf.stalkPullbackHom
          (AddCommGrpCat.{v}) j F.presheaf x)
        exact (TopCat.Presheaf.stalkPullbackIso
          (AddCommGrpCat.{v}) j F.presheaf x).isIso_hom
      letI : IsIso (a ≫ b) := hcomp
      change IsIso a
      exact IsIso.of_isIso_comp_right a b
    have hs0 : ηu.app (op U) s = 0 := by
      apply hraw.section_ext
      intro x hx
      have hx' : (j x : X) ∈ U := by
        exact hx
      have hFs : F.presheaf.germ U (j x : X) hx' s = 0 := by
        apply Classical.byContradiction
        intro hne
        exact x.property (hs ⟨j x, hx'⟩ hne)
      have hg : raw.germ ((Opens.map j).obj U) x hx
          ((ηu.app (op U)) s) = raw.germ ((Opens.map j).obj U) x hx 0 := by
        let e := TopCat.Presheaf.stalkPullbackIso
          (AddCommGrpCat.{v}) j F.presheaf x
        have hinj : Function.Injective (ConcreteCategory.hom e.inv) := by
          intro a b hab
          have hab' := congrArg (fun z => ConcreteCategory.hom e.hom z) hab
          change (ConcreteCategory.hom (e.inv ≫ e.hom)) a =
            (ConcreteCategory.hom (e.inv ≫ e.hom)) b at hab'
          simpa using hab'
        apply hinj
        change (ConcreteCategory.hom
              (raw.germ ((Opens.map j).obj U) x hx ≫
                TopCat.Presheaf.stalkPullbackInv (AddCommGrpCat.{v}) j F.presheaf x))
              ((ConcreteCategory.hom (ηu.app (op U))) s) =
            (ConcreteCategory.hom
              (raw.germ ((Opens.map j).obj U) x hx ≫
                TopCat.Presheaf.stalkPullbackInv (AddCommGrpCat.{v}) j F.presheaf x)) 0
        rw [← ConcreteCategory.comp_apply,
          TopCat.Presheaf.germ_stalkPullbackInv]
        have hunit := congrArg (fun q => (ConcreteCategory.hom q) s)
          (TopCat.Presheaf.pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk
          (AddCommGrpCat.{v}) j F.presheaf (op U)
            (show (Opens.toTopCat X).obj Uc from x) hx')
        have hunit' :
            (ConcreteCategory.hom
              (ηu.app (op U) ≫
                TopCat.Presheaf.germToPullbackStalk (AddCommGrpCat.{v}) j F.presheaf
                  ((Opens.map j).obj U) x hx)) s =
              F.presheaf.germ U (j x : X) hx' s := by
          simpa [ηu] using hunit
        rw [hunit', hFs]
        simp only [Functor.map_zero, map_zero]
      rcases raw.germ_eq x hx hx ((ηu.app (op U)) s) 0 hg with
        ⟨V, hxV, hV, hV', h⟩
      refine ⟨V, hV.le, hxV, ?_⟩
      simpa [show hV = homOfLE hV.le from Subsingleton.elim _ _,
        show hV' = homOfLE hV'.le from Subsingleton.elim _ _] using h
    have heta : η.1 = ηu := rfl
    let K : Subobject F := kernelSubobject η
    have hK_support : abelianSheafSupportContainedIn Z (K : Ab X) := by
      intro x hx
      by_contra hnot
      have hzero : IsZero
          ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).obj
            (K : Ab X).presheaf) := by
        let k := (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map K.arrow.1
        have hk0p : K.arrow.1 ≫ ηu = 0 := by
          rw [← heta]
          exact congrArg (fun f => f.1) (kernelSubobject_arrow_comp η)
        have hcomp : k ≫
            (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map ηu = 0 := by
          rw [← Functor.map_comp, hk0p, Functor.map_zero]
        haveI : Mono k := by
          dsimp [k]
          exact TopCat.Presheaf.stalk_mono_of_mono K.arrow x
        haveI : IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map ηu) := by
          exact hη ⟨x, hnot⟩
        rw [IsZero.iff_id_eq_zero]
        apply (cancel_mono k).1
        simp only [CategoryTheory.Category.id_comp, zero_comp]
        apply (cancel_mono
          ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map ηu)).1
        simpa only [zero_comp] using hcomp
      exact (not_nontrivial_iff_subsingleton.mpr
        (AddCommGrpCat.subsingleton_of_isZero hzero)) hx
    have hle : K ≤ closedSupportSubsheaf Z hZ F :=
      closedSupportSubsheaf_isLargest Z hZ F K hK_support
    let E : Ab X ⥤ AddCommGrpCat.{v} :=
        TopCat.Sheaf.forget (AddCommGrpCat.{v}) X ⋙
          (evaluation (Opens X)ᵒᵖ (AddCommGrpCat.{v})).obj (op U)
    change E.obj F at s
    letI : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
    letI : PreservesLimits (TopCat.Sheaf.forget (AddCommGrpCat.{v}) X) := by
      infer_instance
    letI : PreservesLimit
        ((parallelPair η 0) ⋙ TopCat.Sheaf.forget (AddCommGrpCat.{v}) X)
        ((evaluation (Opens X)ᵒᵖ (AddCommGrpCat.{v})).obj (op U)) := by
      have hEval := preservesSmallestLimits_of_preservesLimits
        ((evaluation (Opens X)ᵒᵖ (AddCommGrpCat.{v})).obj (op U))
      exact hEval.preservesLimitsOfShape.preservesLimit
    letI : PreservesLimit (parallelPair η 0) E := by
      dsimp [E]
      infer_instance
    let eK : (K : Ab X).presheaf.obj (op U) ≅ kernel (E.map η) := by
      change E.obj (K : Ab X) ≅ kernel (E.map η)
      exact (Functor.mapIso E (kernelSubobjectIso η)) ≪≫
        PreservesKernel.iso E η
    let f : (AddCommGrpCat.of (ULift.{v} ℤ)) ⟶ E.obj F :=
      AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun n : ULift.{v} ℤ => n.down • s) (by
        intro a b
        change (a.down + b.down) • s = a.down • s + b.down • s
        rw [add_smul]))
    have hs0E : (ConcreteCategory.hom (E.map η)) s = 0 := by
      change (ConcreteCategory.hom (ηu.app (op U))) s = 0
      exact hs0
    have hf : f ≫ E.map η = 0 := by
      apply ConcreteCategory.hom_ext
      intro n
      change (ConcreteCategory.hom (E.map η)) (n.down • s) = 0
      rw [map_zsmul, hs0E]
      simp
    let l := kernel.lift (E.map η) f hf
    let tK : (K : Ab X).presheaf.obj (op U) :=
      ConcreteCategory.hom (l ≫ eK.inv) (ULift.up 1)
    have heK_arrow : eK.hom ≫ kernel.ι (E.map η) = E.map K.arrow := by
      change ((E.map (kernelSubobjectIso η).hom) ≫
          (PreservesKernel.iso E η).hom) ≫ kernel.ι (E.map η) = E.map K.arrow
      have heval : (PreservesKernel.iso E η).hom ≫ kernel.ι (E.map η) =
          E.map (kernel.ι η) := by
        rw [← PreservesKernel.iso_inv_ι]
        simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [Category.assoc, heval, ← Functor.map_comp, kernelSubobject_arrow]
    have heK_inv_arrow : eK.inv ≫ E.map K.arrow = kernel.ι (E.map η) := by
      rw [← heK_arrow]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have htK : K.arrow.hom.app (op U) tK = s := by
      change ConcreteCategory.hom (E.map K.arrow) tK = s
      change ConcreteCategory.hom (E.map K.arrow)
          (ConcreteCategory.hom (l ≫ eK.inv) (ULift.up 1)) = s
      change ConcreteCategory.hom ((l ≫ eK.inv) ≫ E.map K.arrow) (ULift.up 1) = s
      have hcat : (l ≫ eK.inv) ≫ E.map K.arrow = f := by
        calc
          (l ≫ eK.inv) ≫ E.map K.arrow =
              l ≫ (eK.inv ≫ E.map K.arrow) := Category.assoc _ _ _
          _ = l ≫ kernel.ι (E.map η) := by rw [heK_inv_arrow]
          _ = f := kernel.lift_ι _ _ _
      rw [hcat]
      change ConcreteCategory.hom f (ULift.up 1) = s
      simp [f]
    let qmap : (K : Ab X) ⟶ (closedSupportSubsheaf Z hZ F : Ab X) :=
      Subobject.ofLE K (closedSupportSubsheaf Z hZ F) hle
    let t : (closedSupportSubsheaf Z hZ F : Ab X).presheaf.obj (op U) :=
      qmap.hom.app (op U) tK
    refine ⟨t, ?_⟩
    change ConcreteCategory.hom
        ((closedSupportSubsheaf Z hZ F).arrow.hom.app (op U)) t = s
    change ConcreteCategory.hom
        (qmap.hom.app (op U) ≫
          (closedSupportSubsheaf Z hZ F).arrow.hom.app (op U)) tK = s
    have hq : qmap.hom.app (op U) ≫
        (closedSupportSubsheaf Z hZ F).arrow.hom.app (op U) =
        K.arrow.hom.app (op U) := by
      change (Subobject.ofLE K (closedSupportSubsheaf Z hZ F) hle).hom.app (op U) ≫
          (closedSupportSubsheaf Z hZ F).arrow.hom.app (op U) =
        K.arrow.hom.app (op U)
      exact congrArg (fun g => g.hom.app (op U)) (Subobject.ofLE_arrow hle)
    have hq' := congrArg (fun g => (ConcreteCategory.hom g) tK) hq
    simpa [ConcreteCategory.comp_apply, htK] using hq'

/-! ## The right adjoint on abelian sheaves -/

private theorem closedSupport_directImage_counit_isIso
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
      (closedInclusion Z)).counit) := by
  let f : TopCat.of Z ⟶ X := closedInclusion Z
  have hpmap (F : TopCat.Sheaf (AddCommGrpCat.{v}) (TopCat.of Z)) (z : Z) :
      (TopCat.Presheaf.stalkFunctor (C := AddCommGrpCat.{v})
          (X := TopCat.of Z) z).map
          ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).counit.app
            F.presheaf) =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat f
            ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.presheaf) z).inv ≫
          TopCat.Presheaf.stalkPushforward AddCommGrpCat f F.presheaf z := by
    apply TopCat.Presheaf.stalk_hom_ext _
    intro U hxU
    rw [TopCat.Presheaf.stalkFunctor_map_germ]
    simp only [Functor.id_obj]
    dsimp [TopCat.Presheaf.stalkPullbackIso]
    rw [← Category.assoc]
    apply TopCat.Presheaf.pullback_obj_obj_ext (op U)
    intro V hV
    simp only [TopCat.Presheaf.germ_stalkPullbackInv]
    have hnat := ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).counit.app
      F.presheaf).naturality (homOfLE hV).op
    have hnat' :
        ((TopCat.Presheaf.pullback AddCommGrpCat f).obj
            ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.presheaf)).map
            (homOfLE hV).op ≫
          ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).counit.app
            F.presheaf).app (op U) =
        ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).counit.app
            F.presheaf).app (op ((Opens.map f).obj V)) ≫
          F.presheaf.map (homOfLE hV).op := by
      simpa only [Functor.comp_obj, Functor.id_obj] using hnat
    have hnat'' :
        ((TopCat.Presheaf.pullback AddCommGrpCat f).obj
            ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.presheaf)).map
            (homOfLE hV).op ≫
          ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).counit.app
            F.presheaf).app (op U) ≫ F.presheaf.germ U z hxU =
        ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).counit.app
            F.presheaf).app (op ((Opens.map f).obj V)) ≫
          F.presheaf.map (homOfLE hV).op ≫ F.presheaf.germ U z hxU := by
      rw [← Category.assoc, hnat']
      simp only [Category.assoc]
    rw [hnat'']
    have htri' :
        ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit.app
            ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.presheaf)).app (op V) ≫
          ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).counit.app
            F.presheaf).app (op ((Opens.map f).obj V)) =
          (NatTrans.id ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.presheaf)).app
            (op V) := by
      have htri :=
        (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).right_triangle_components
          F.presheaf
      convert congr_app htri (op V) using 1
      all_goals rfl
    rw [← Category.assoc, htri']
    rw [TopCat.Presheaf.pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk_assoc]
    have hzV' := hV hxU
    change (ConcreteCategory.hom f) z ∈ V at hzV'
    have hres := F.presheaf.germ_res (homOfLE hV) z hxU
    have hpush := TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat f F.presheaf V z hzV'
    simpa using hres.trans hpush.symm
  have hsheafify {P Q : TopCat.Presheaf (AddCommGrpCat.{v}) (TopCat.of Z)}
      (φ : P ⟶ Q) (hφ : ∀ z : Z, IsIso
        ((TopCat.Presheaf.stalkFunctor (C := AddCommGrpCat.{v})
            (X := TopCat.of Z) z).map φ)) :
      IsIso ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of Z))
        AddCommGrpCat).map φ) := by
    let K := Opens.grothendieckTopology (TopCat.of Z)
    let : ∀ z : Z, IsIso
        ((TopCat.Presheaf.stalkFunctor (C := AddCommGrpCat.{v})
            (X := TopCat.of Z) z).map
          ((presheafToSheaf K AddCommGrpCat).map φ).hom) := by
      intro z
      let uP := (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) z).map
        (toSheafify K P)
      let uQ := (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) z).map
        (toSheafify K Q)
      let m := (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) z).map
        ((presheafToSheaf K AddCommGrpCat).map φ).hom
      let p := (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) z).map φ
      let : IsIso uP := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        (X := TopCat.of Z) (p₀ := z) (C := AddCommGrpCat) P
      let : IsIso uQ := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        (X := TopCat.of Z) (p₀ := z) (C := AddCommGrpCat) Q
      let : IsIso p := hφ z
      have hcomp : uP ≫ m = p ≫ uQ := by
        have h := congrArg (fun q =>
          (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) z).map q)
          ((sheafificationAdjunction K AddCommGrpCat).unit.naturality φ)
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
  let F' : Sheaf K AddCommGrpCat := F
  let c₀ := (f₀.op.lanAdjunction AddCommGrpCat).counit.app F'.obj
  have hc₀ : IsIso ((presheafToSheaf K AddCommGrpCat).map c₀) := by
    apply hsheafify c₀
    intro z
    have hh : IsIso
        ((TopCat.Presheaf.stalkFunctor (C := AddCommGrpCat.{v})
            (X := TopCat.of Z) z).map
          ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).counit.app
            F.presheaf)) := by
      rw [hpmap F z]
      let : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat f F.presheaf z) :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
          AddCommGrpCat hZ.isClosedEmbedding_subtypeVal.isInducing F.presheaf z
      let : IsIso (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat f
          ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.presheaf) z).inv := by
        infer_instance
      exact IsIso.comp_isIso'
        (by infer_instance : IsIso
          (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat f
            ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F.presheaf) z).inv)
        (by infer_instance : IsIso
          (TopCat.Presheaf.stalkPushforward AddCommGrpCat f F.presheaf z))
    simpa [c₀, f₀, TopCat.Presheaf.pullbackPushforwardAdjunction,
      TopCat.Presheaf.pullback] using hh
  have hc₁ : IsIso ((sheafificationAdjunction K AddCommGrpCat).counit.app F') := by
    infer_instance
  let adj₀ := (f₀.op.lanAdjunction AddCommGrpCat).comp
    (sheafificationAdjunction K AddCommGrpCat)
  have hcomp : adj₀.counit.app F' =
      (presheafToSheaf K AddCommGrpCat).map c₀ ≫
        (sheafificationAdjunction K AddCommGrpCat).counit.app F' := by
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
    f₀ AddCommGrpCat J K
  let : IsIso (adj₀.counit.app F') := hc
  have hc₂ : IsIso (adj₂.counit.app F') := by
    let L₃ := Functor.sheafPullbackConstruction.sheafPullback f₀ AddCommGrpCat J K
    let R₃ := Functor.sheafPushforwardContinuous f₀ AddCommGrpCat J K
    let comm1₃ :
        sheafToPresheaf J AddCommGrpCat ⋙
            (f₀.op.lan ⋙ presheafToSheaf K AddCommGrpCat) ≅
          L₃ ⋙ 𝟭 (Sheaf K AddCommGrpCat) := by
      dsimp [L₃, Functor.sheafPullbackConstruction.sheafPullback]
      exact (Functor.rightUnitor _).symm
    let adj₃ : L₃ ⊣ R₃ :=
      adj₀.restrictFullyFaithful
        (fullyFaithfulSheafToPresheaf J AddCommGrpCat) (Functor.FullyFaithful.id _)
        (L := L₃) (R := R₃) comm1₃ (Iso.refl _)
    have hmap := Adjunction.map_restrictFullyFaithful_counit_app
      (adj := adj₀)
      (hiC := fullyFaithfulSheafToPresheaf J AddCommGrpCat)
      (hiD := Functor.FullyFaithful.id _)
      (L := L₃) (R := R₃) (comm1 := comm1₃) (comm2 := Iso.refl _) F'
    have hc₃ : IsIso (adj₃.counit.app F') := by
      have hmap' := hmap
      let : IsIso (comm1₃.inv.app (R₃.obj F')) :=
        (comm1₃.app (R₃.obj F')).isIso_inv
      change IsIso ((𝟭 (Sheaf K AddCommGrpCat)).map (adj₃.counit.app F'))
      rw [hmap']
      have h₁ : IsIso (comm1₃.inv.app (R₃.obj F')) := by
        exact (comm1₃.app (R₃.obj F')).isIso_inv
      have h₂₀ : IsIso ((Iso.refl
          (𝟭 (Sheaf K AddCommGrpCat) ⋙ sheafToPresheaf K AddCommGrpCat ⋙
            (Functor.whiskeringLeft (Opens X)ᵒᵖ
              (Opens (TopCat.of Z))ᵒᵖ AddCommGrpCat).obj f₀.op)).inv.app F') := by
        infer_instance
      let : IsIso ((Iso.refl
          (𝟭 (Sheaf K AddCommGrpCat) ⋙ sheafToPresheaf K AddCommGrpCat ⋙
            (Functor.whiskeringLeft (Opens X)ᵒᵖ
              (Opens (TopCat.of Z))ᵒᵖ AddCommGrpCat).obj f₀.op)).inv.app F') := h₂₀
      have h₂ : IsIso ((f₀.op.lan ⋙ presheafToSheaf K AddCommGrpCat).map
          ((Iso.refl
            (𝟭 (Sheaf K AddCommGrpCat) ⋙ sheafToPresheaf K AddCommGrpCat ⋙
              (Functor.whiskeringLeft (Opens X)ᵒᵖ
                (Opens (TopCat.of Z))ᵒᵖ AddCommGrpCat).obj f₀.op)).inv.app F')) :=
        Functor.map_isIso _ _
      have h₃ : IsIso (adj₀.counit.app ((𝟭 (Sheaf K AddCommGrpCat)).obj F')) := by
        simpa using hc
      exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h₂ h₃)
    let : IsIso (adj₃.counit.app F') := hc₃
    have huniq := Adjunction.leftAdjointUniq_hom_app_counit adj₂ adj₃ F'
    let : IsIso (adj₃.counit.app F') := hc₃
    rw [← huniq]
    infer_instance
  let : IsIso (adj₂.counit.app F') := hc₂
  let e₀ := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).leftAdjointUniq adj₂
  have huniq₀ := Adjunction.leftAdjointUniq_hom_app_counit
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f) adj₂ F'
  rw [← huniq₀]
  let : IsIso (e₀.hom.app ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F')) :=
    (e₀.app ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F')).isIso_hom
  change IsIso (e₀.hom.app ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F') ≫
    adj₂.counit.app F')
  exact IsIso.comp_isIso'
    (e₀.app ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F')).isIso_hom hc₂

private theorem closedSupport_directImage_stalk_isZero_of_not_mem
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z)
    (G : Ab (closedSubspace Z)) {x : X} (hx : x ∉ Z) :
    IsZero (((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj G).presheaf.stalk x) := by
  let P : TopCat.Presheaf (AddCommGrpCat.{v}) X :=
    ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj G).presheaf
  let c : Cocone ((OpenNhds.inclusion x).op ⋙ P) :=
    { pt := (⊤_ (AddCommGrpCat.{v}))
      ι :=
        { app := fun _ => terminal.from _
          naturality := fun _ _ _ => terminalIsTerminal.hom_ext _ _ } }
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
  rcases h1 with ⟨U, hU⟩
  have hUt : IsTerminal (P.obj (op U.1)) := by
    change IsTerminal (G.presheaf.obj (op ((Opens.map (closedInclusion Z)).obj U.1)))
    rw [hU]
    exact G.isTerminalOfEmpty
  have hUt' : IsTerminal (((OpenNhds.inclusion x).op ⋙ P).obj (op U)) := by
    change IsTerminal (P.obj (op U.1))
    exact hUt
  let e : ((OpenNhds.inclusion x).op ⋙ P).obj (op U) ≅
      (⊤_ (AddCommGrpCat.{v})) :=
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
              (((OpenNhds.inclusion x).op ⋙ P).obj
                (op (U ⊓ V.unop))) := by
            change IsTerminal (G.presheaf.obj
              (op ((Opens.map (closedInclusion Z)).obj (U.1 ⊓ V.unop.1))))
            apply G.isTerminalOfEqEmpty
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
  have hIso : P.stalk x ≅ (⊤_ (AddCommGrpCat.{v})) :=
    colimit.isoColimitCocone ⟨_, hc⟩
  change IsZero (P.stalk x)
  exact (isZero_zero _).of_iso (hIso ≪≫
    ((isZero_zero (AddCommGrpCat.{v})).isoIsTerminal
      (terminalIsTerminal : IsTerminal (⊤_ (AddCommGrpCat.{v})))).symm)

private abbrev closedSupport_complementOpen {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

private noncomputable def closedSupport_complementRaw {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    TopCat.Presheaf (AddCommGrpCat.{v})
      (TopCat.of (closedSupport_complementOpen Z hZ)) :=
  (TopCat.Presheaf.pullback (AddCommGrpCat.{v})
    (Opens.inclusion' (closedSupport_complementOpen Z hZ))).obj F.presheaf

private theorem closedSupport_complementRaw_isSheaf {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    (closedSupport_complementRaw Z hZ F).IsSheaf := by
  apply TopCat.Presheaf.isSheaf_of_iso
    (((closedSupport_complementOpen Z hZ).isOpenEmbedding).isOpenMap.pullbackObjIso
      F.presheaf).symm
  exact TopCat.Presheaf.isSheaf_of_isOpenEmbedding
    (closedSupport_complementOpen Z hZ).isOpenEmbedding F.2

private noncomputable def closedSupport_complementSheaf {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    Ab (TopCat.of (closedSupport_complementOpen Z hZ)) :=
  ⟨closedSupport_complementRaw Z hZ F,
    closedSupport_complementRaw_isSheaf Z hZ F⟩

private noncomputable def closedSupport_complementUnit {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    F ⟶ (TopCat.Sheaf.pushforward (AddCommGrpCat.{v})
      (Opens.inclusion' (closedSupport_complementOpen Z hZ))).obj
        (closedSupport_complementSheaf Z hZ F) :=
  ObjectProperty.homMk
    ((TopCat.Presheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v})
      (Opens.inclusion' (closedSupport_complementOpen Z hZ))).unit.app F.presheaf)

private theorem closedSupport_complementUnit_stalk_isIso {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Ab X)
    (x : TopCat.of (closedSupport_complementOpen Z hZ)) :
    IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v})
      (x : X)).map (closedSupport_complementUnit Z hZ F).1) := by
  let j := Opens.inclusion' (closedSupport_complementOpen Z hZ)
  let a := (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (j x)).map
    ((TopCat.Presheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v}) j).unit.app
      F.presheaf)
  let b : (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (j x)).obj
          ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j ⋙
            TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) j).obj F.presheaf) ⟶
          ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).obj F.presheaf).stalk x :=
    TopCat.Presheaf.stalkPushforward (AddCommGrpCat.{v}) j
      ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).obj F.presheaf) x
  have hpush : IsIso b := by
    change IsIso (TopCat.Presheaf.stalkPushforward
      (AddCommGrpCat.{v}) j (closedSupport_complementRaw Z hZ F) x)
    exact TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (f := j) (C := AddCommGrpCat.{v})
      (closedSupport_complementOpen Z hZ).isOpenEmbedding.isInducing
      (closedSupport_complementRaw Z hZ F) x
  letI : IsIso b := hpush
  have hcomp : IsIso (a ≫ b) := by
    change IsIso (TopCat.Presheaf.stalkPullbackHom
      (AddCommGrpCat.{v}) j F.presheaf x)
    exact (TopCat.Presheaf.stalkPullbackIso
      (AddCommGrpCat.{v}) j F.presheaf x).isIso_hom
  letI : IsIso (a ≫ b) := hcomp
  change IsIso a
  exact IsIso.of_isIso_comp_right a b

private theorem closedSupport_complementKernel_support {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    abelianSheafSupportContainedIn Z
      (kernelSubobject (closedSupport_complementUnit Z hZ F) : Ab X) := by
  intro x hx
  by_contra hnot
  have hzero : IsZero
      ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).obj
        (kernelSubobject (closedSupport_complementUnit Z hZ F) : Ab X).presheaf) := by
    let k := (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
      (kernelSubobject (closedSupport_complementUnit Z hZ F)).arrow.1
    have hk0p : (kernelSubobject (closedSupport_complementUnit Z hZ F)).arrow.1 ≫
        (closedSupport_complementUnit Z hZ F).1 = 0 := by
      exact congrArg (fun f => f.1)
        (kernelSubobject_arrow_comp (closedSupport_complementUnit Z hZ F))
    have hcomp : k ≫
        (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
          (closedSupport_complementUnit Z hZ F).1 = 0 := by
      rw [← Functor.map_comp, hk0p, Functor.map_zero]
    haveI : Mono k := by
      dsimp [k]
      exact TopCat.Presheaf.stalk_mono_of_mono
        (kernelSubobject (closedSupport_complementUnit Z hZ F)).arrow x
    haveI : IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
        (closedSupport_complementUnit Z hZ F).1) := by
      exact closedSupport_complementUnit_stalk_isIso Z hZ F ⟨x, hnot⟩
    rw [IsZero.iff_id_eq_zero]
    apply (cancel_mono k).1
    simp only [CategoryTheory.Category.id_comp, zero_comp]
    apply (cancel_mono
      ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
        (closedSupport_complementUnit Z hZ F).1)).1
    simpa only [zero_comp] using hcomp
  exact (not_nontrivial_iff_subsingleton.mpr
    (AddCommGrpCat.subsingleton_of_isZero hzero)) hx

private theorem closedSupport_complementUnit_app_eq_zero_of_supported
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X)
    (U : Opens X) (s : F.presheaf.obj (op U))
    (hs : abelianSectionSupportedInClosed Z U s) :
    (closedSupport_complementUnit Z hZ F).1.app (op U) s = 0 := by
  let Uc : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩
  let j : TopCat.of Uc ⟶ X := Opens.inclusion' Uc
  let raw := (TopCat.Presheaf.pullback (AddCommGrpCat.{v}) j).obj F.presheaf
  let ηu := (TopCat.Presheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v}) j).unit.app
    F.presheaf
  have hraw : raw.IsSheaf := by
    apply TopCat.Presheaf.isSheaf_of_iso
      (Uc.isOpenEmbedding.isOpenMap.pullbackObjIso F.presheaf).symm
    exact TopCat.Presheaf.isSheaf_of_isOpenEmbedding Uc.isOpenEmbedding F.2
  change ∀ x : U, abelianSectionGerm U s x ≠ 0 → (x : X) ∈ Z at hs
  have hs0 : (closedSupport_complementUnit Z hZ F).1.app (op U) s = 0 := by
    change (ηu.app (op U)) s = 0
    apply hraw.section_ext
    intro x hx
    have hxj : x ∈ (Opens.map j).obj U := by
      exact hx
    have hx' : (j x : X) ∈ U := by
      exact hx
    have hFs : F.presheaf.germ U (j x : X) hx' s = 0 := by
      apply Classical.byContradiction
      intro hne
      exact x.property (hs ⟨j x, hx'⟩ hne)
    have hg : raw.germ ((Opens.map j).obj U) x hxj
          ((ηu.app (op U)) s) =
        raw.germ ((Opens.map j).obj U) x hxj 0 := by
      let e := TopCat.Presheaf.stalkPullbackIso
        (AddCommGrpCat.{v}) j F.presheaf x
      have hinj : Function.Injective (ConcreteCategory.hom e.inv) := by
        intro a b hab
        have hab' := congrArg (fun z => ConcreteCategory.hom e.hom z) hab
        change (ConcreteCategory.hom (e.inv ≫ e.hom)) a =
          (ConcreteCategory.hom (e.inv ≫ e.hom)) b at hab'
        simpa using hab'
      apply hinj
      change (ConcreteCategory.hom
            (raw.germ ((Opens.map j).obj U) x hxj ≫
              TopCat.Presheaf.stalkPullbackInv (AddCommGrpCat.{v}) j F.presheaf x))
          ((ConcreteCategory.hom (ηu.app (op U))) s) =
        (ConcreteCategory.hom
            (raw.germ ((Opens.map j).obj U) x hxj ≫
              TopCat.Presheaf.stalkPullbackInv (AddCommGrpCat.{v}) j F.presheaf x)) 0
      change (ConcreteCategory.hom
            (raw.germ ((Opens.map j).obj U) x hxj ≫
              TopCat.Presheaf.stalkPullbackInv (AddCommGrpCat.{v}) j F.presheaf x))
          ((ConcreteCategory.hom (ηu.app (op U))) s) =
        (ConcreteCategory.hom
            (raw.germ ((Opens.map j).obj U) x hxj ≫
              TopCat.Presheaf.stalkPullbackInv (AddCommGrpCat.{v}) j F.presheaf x)) 0
      rw [← ConcreteCategory.comp_apply,
        TopCat.Presheaf.germ_stalkPullbackInv]
      have hunit := congrArg (fun q => (ConcreteCategory.hom q) s)
          (TopCat.Presheaf.pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk
          (AddCommGrpCat.{v}) j F.presheaf (op U) x hx')
      have hunit' :
          (ConcreteCategory.hom
            (ηu.app (op U) ≫
              TopCat.Presheaf.germToPullbackStalk (AddCommGrpCat.{v}) j F.presheaf
                ((Opens.map j).obj U) x hx)) s =
          F.presheaf.germ U (j x : X) hx' s := by
        simpa [ηu, closedSupport_complementUnit, j, Uc] using hunit
      rw [hunit', hFs]
      simp only [Functor.map_zero, map_zero]
    rcases raw.germ_eq x hxj hxj
      ((ηu.app (op U)) s) 0 hg with
      ⟨V, hxV, hV, hV', h⟩
    refine ⟨V, hV.le, hxV, ?_⟩
    have h' := h
    rw [show hV' = hV from Subsingleton.elim _ _] at h'
    change (ConcreteCategory.hom (raw.map (homOfLE hV.le).op))
        ((ConcreteCategory.hom (ηu.app (op U))) s) =
      (ConcreteCategory.hom (raw.map (homOfLE hV.le).op)) 0
    have hm : raw.map (homOfLE hV.le).op = raw.map hV.op := by
      congr 1
    rw [hm]
    exact h'
  assumption

set_option backward.isDefEq.respectTransparency false in
private theorem closedSupport_stalkPullbackHom_naturality
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    {F G : TopCat.Presheaf AddCommGrpCat Y} (g : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (f x)).map g ≫
        TopCat.Presheaf.stalkPullbackHom (AddCommGrpCat.{v}) f G x =
      TopCat.Presheaf.stalkPullbackHom (AddCommGrpCat.{v}) f F x ≫
        (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
          ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) f).map g) := by
  apply TopCat.Presheaf.stalk_hom_ext F
  intro V hV
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  simp only [TopCat.Presheaf.germ_stalkPullbackHom]
  have hnat := NatTrans.congr_app
    ((TopCat.Presheaf.pullbackPushforwardAdjunction
      (AddCommGrpCat.{v}) f).unit.naturality g) (op V)
  change g.app (op V) ≫
      ((TopCat.Presheaf.pullbackPushforwardAdjunction
        (AddCommGrpCat.{v}) f).unit.app G).app (op V) =
    ((TopCat.Presheaf.pullbackPushforwardAdjunction
      (AddCommGrpCat.{v}) f).unit.app F).app (op V) ≫
      ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) f).map g).app
        (op ((Opens.map f).obj V)) at hnat
  rw [← Category.assoc, hnat]
  rw [TopCat.Presheaf.germ_stalkPullbackHom_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def closedSupport_pullbackStalkIso
    {X Y : TopCat.{v}} (f : X ⟶ Y) (x : X) :
    TopCat.Presheaf.pullback (AddCommGrpCat.{v}) f ⋙
        TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x ≅
      TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (f x) :=
  NatIso.ofComponents
    (fun F ↦ (TopCat.Presheaf.stalkPullbackIso
      (AddCommGrpCat.{v}) f F x).symm)
    (fun {F G} g ↦ by
      apply (cancel_epi (TopCat.Presheaf.stalkPullbackIso
        (AddCommGrpCat.{v}) f F x).hom).1
      change (TopCat.Presheaf.stalkPullbackIso
          (AddCommGrpCat.{v}) f F x).hom ≫
          (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
            ((TopCat.Presheaf.pullback (AddCommGrpCat.{v}) f).map g) ≫
          (TopCat.Presheaf.stalkPullbackIso
            (AddCommGrpCat.{v}) f G x).inv =
        (TopCat.Presheaf.stalkPullbackIso
            (AddCommGrpCat.{v}) f F x).hom ≫
          (TopCat.Presheaf.stalkPullbackIso
            (AddCommGrpCat.{v}) f F x).inv ≫
          (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (f x)).map g
      calc
        _ = ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (f x)).map g ≫
            (TopCat.Presheaf.stalkPullbackIso
              (AddCommGrpCat.{v}) f G x).hom) ≫
              (TopCat.Presheaf.stalkPullbackIso
                (AddCommGrpCat.{v}) f G x).inv := by
          simpa only [TopCat.Presheaf.stalkPullbackIso, Category.assoc] using
            congrArg (fun k ↦ k ≫ (TopCat.Presheaf.stalkPullbackIso
              (AddCommGrpCat.{v}) f G x).inv)
              (closedSupport_stalkPullbackHom_naturality f g x).symm
        _ = (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (f x)).map g := by
          simp
        _ = ((TopCat.Presheaf.stalkPullbackIso
              (AddCommGrpCat.{v}) f F x).hom ≫
            (TopCat.Presheaf.stalkPullbackIso
              (AddCommGrpCat.{v}) f F x).inv) ≫
              (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (f x)).map g := by simp
        _ = _ := by simp)

private noncomputable def closedSupport_sheafificationStalkIso
    {X : TopCat.{v}} (x : X) :
    TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x ≅
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
          TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x :=
  NatIso.ofComponents
    (fun P ↦ by
      letI : IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
          (toSheafify (Opens.grothendieckTopology X) P)) :=
        TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
          (X := X) (p₀ := x) (C := AddCommGrpCat) P
      exact asIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
        (toSheafify (Opens.grothendieckTopology X) P)))
    (fun {P Q} g ↦ by
      have h := congrArg (fun q =>
        (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map q)
        ((sheafificationAdjunction (Opens.grothendieckTopology X)
          AddCommGrpCat).unit.naturality g)
      change (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map g ≫
          (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
            (toSheafify (Opens.grothendieckTopology X) Q) =
        (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
            (toSheafify (Opens.grothendieckTopology X) P) ≫
          (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
            ((sheafToPresheaf (Opens.grothendieckTopology X)
              AddCommGrpCat).map
              ((presheafToSheaf (Opens.grothendieckTopology X)
                AddCommGrpCat).map g))
      simpa only [Functor.id_map, Functor.comp_map, Functor.map_comp] using h)

private noncomputable def closedSupport_sheafPullbackStalkIso
    {X Y : TopCat.{v}} (f : X ⟶ Y) (x : X) :
    TopCat.Sheaf.forget (AddCommGrpCat.{v}) Y ⋙
        TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (f x) ≅
      TopCat.Sheaf.pullback (AddCommGrpCat.{v}) f ⋙
        TopCat.Sheaf.forget (AddCommGrpCat.{v}) X ⋙
          TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x :=
  Functor.isoWhiskerLeft (TopCat.Sheaf.forget (AddCommGrpCat.{v}) Y)
      (closedSupport_pullbackStalkIso f x).symm ≪≫
    Functor.isoWhiskerLeft
      (TopCat.Sheaf.forget (AddCommGrpCat.{v}) Y ⋙
        TopCat.Presheaf.pullback (AddCommGrpCat.{v}) f)
      (closedSupport_sheafificationStalkIso x) ≪≫
    (Functor.isoWhiskerRight (TopCat.Sheaf.pullbackIso
      (AddCommGrpCat.{v}) f)
      (TopCat.Sheaf.forget (AddCommGrpCat.{v}) X ⋙
        TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x)).symm

private theorem closedSupport_restriction_unit_stalk_isIso
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z)
    (G : Ab X) (x : X) (hx : x ∈ Z) :
    IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v})
        (closedInclusion Z)).unit.app G).hom) := by
  let f := closedInclusion Z
  let L := TopCat.Sheaf.pullback (AddCommGrpCat.{v}) f
  let R := TopCat.Sheaf.pushforward (AddCommGrpCat.{v}) f
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v}) f
  letI : IsIso adj.counit := closedSupport_directImage_counit_isIso Z hZ
  let hff := adj.fullyFaithfulROfIsIsoCounit
  letI : R.Full := hff.full
  letI : R.Faithful := hff.faithful
  let g := adj.unit.app G
  haveI : IsIso (L.map g) := inferInstance
  haveI : IsIso ((L.map g).hom) := by
    change IsIso ((TopCat.Sheaf.forget AddCommGrpCat (closedSubspace Z)).map (L.map g))
    infer_instance
  haveI : IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v})
      (⟨x, hx⟩ : (closedSubspace Z : Type v))).map (L.map g).hom) := by
    infer_instance
  let e := closedSupport_sheafPullbackStalkIso f
    (⟨x, hx⟩ : (closedSubspace Z : Type v))
  have h := e.hom.naturality g
  letI : IsIso e.hom := e.isIso_hom
  letI : IsIso (e.hom.app G) := by
    infer_instance
  have hright : IsIso
      (e.hom.app G ≫
        (TopCat.Sheaf.pullback (AddCommGrpCat.{v}) f ⋙
          TopCat.Sheaf.forget AddCommGrpCat (closedSubspace Z) ⋙
          TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v})
            (⟨x, hx⟩ : (closedSubspace Z : Type v))).map g) := by
    exact IsIso.comp_isIso' (inferInstance : IsIso (e.hom.app G)) (by
      change IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v})
          (⟨x, hx⟩ : (closedSubspace Z : Type v))).map (L.map g).hom)
      infer_instance)
  letI := hright
  have hright' : IsIso
      (e.hom.app ((𝟭 (TopCat.Sheaf (AddCommGrpCat.{v}) X)).obj G) ≫
        (TopCat.Sheaf.pullback (AddCommGrpCat.{v}) f ⋙
          TopCat.Sheaf.forget AddCommGrpCat (closedSubspace Z) ⋙
          TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v})
            (⟨x, hx⟩ : (closedSubspace Z : Type v))).map g) := by
    simpa only [Functor.id_obj, Functor.comp_map] using hright
  letI := hright'
  have hmap : IsIso ((TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v})
        (f (⟨x, hx⟩ : (closedSubspace Z : Type v)))).map g) :=
    IsIso.of_isIso_fac_right h
  change IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map g.hom) at hmap
  change IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map g.hom)
  exact hmap

private theorem closedSupport_restriction_unit_isIso
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v})
      (closedInclusion Z)).unit.app (closedSupportSubsheaf Z hZ F)).hom := by
  let u := (TopCat.Sheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v})
    (closedInclusion Z)).unit.app (closedSupportSubsheaf Z hZ F)
  letI : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor
      (AddCommGrpCat.{v}) x).map u.hom) := by
    intro x
    by_cases hx : x ∈ Z
    · exact closedSupport_restriction_unit_stalk_isIso Z hZ
        (closedSupportSubsheaf Z hZ F : Ab X) x hx
    · have hsource : IsZero
          ((closedSupportSubsheaf Z hZ F : Ab X).presheaf.stalk x) := by
        apply AddCommGrpCat.isZero_iff_subsingleton.mpr
        exact not_nontrivial_iff_subsingleton.mp
          (fun h => hx (closedSupportSubsheaf_supportContainedIn Z hZ F h))
      have htarget : IsZero
          (((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj
            ((closedAbelianSheafRestriction Z hZ).obj
              (closedSupportSubsheaf Z hZ F : Ab X))).presheaf.stalk x) := by
        rcases closedSupport_directImage_stalk_isZero_of_not_mem Z hZ
          ((closedAbelianSheafRestriction Z hZ).obj
            (closedSupportSubsheaf Z hZ F : Ab X)) hx with h
        exact h
      exact isIso_of_source_target_iso_zero _ hsource.isoZero htarget.isoZero
  change IsIso u.hom
  haveI : IsIso u := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso u
  change IsIso ((TopCat.Sheaf.forget (AddCommGrpCat.{v}) X).map u)
  infer_instance

private theorem closedSupport_directImage_map_complement_zero
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (G : Ab (closedSubspace Z))
    (F : Ab X) (α : (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj G ⟶ F) :
    α ≫ closedSupport_complementUnit Z hZ F = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  apply closedSupport_complementUnit_app_eq_zero_of_supported Z hZ F V.unop
  intro x hx
  have hxV : (x : X) ∈ V.unop := x.property
  change abelianSectionGerm V.unop ((α.1.app V) s) x ≠ 0 at hx
  by_contra hnot
  have hzero :
      ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj G).presheaf.germ V.unop
        (x : X) hxV s = 0 := by
    exact (AddCommGrpCat.subsingleton_of_isZero
      (closedSupport_directImage_stalk_isZero_of_not_mem Z hZ G hnot)).elim _ _
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply V.unop (x : X) hxV α.1 s
  change (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (x : X)).map α.1))
      (((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj G).presheaf.germ V.unop
        (x : X) hxV s) =
    F.presheaf.germ V.unop (x : X) hxV ((α.1.app V) s) at hmap
  rw [hzero] at hmap
  have hmap0 : (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (x : X)).map α.1)) 0 = 0 := by
    exact map_zero _
  apply hx
  change F.presheaf.germ V.unop (x : X) hxV ((α.1.app V) s) = 0
  calc
    _ = (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (x : X)).map α.1)) 0 :=
      hmap.symm
    _ = 0 := hmap0

private theorem closedSupport_canonical_exists {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    ∃ H : Ab X ⥤ Ab (closedSubspace Z),
      Nonempty (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ ⊣ H) ∧
        ∀ F : Ab X, Nonempty ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj
          (H.obj F) ≅ (closedSupportSubsheaf Z hZ F : Ab X)) := by
  classical
  let R : Ab (closedSubspace Z) ⥤ Ab X :=
    closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ
  let L : Ab X ⥤ Ab (closedSubspace Z) :=
    closedAbelianSheafRestriction Z hZ
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction
    (AddCommGrpCat.{v}) (closedInclusion Z)
  letI : IsIso adj.counit := by
    exact closedSupport_directImage_counit_isIso Z hZ
  let vObj : Ab X → Ab (closedSubspace Z) := fun F =>
    L.obj (closedSupportSubsheaf Z hZ F : Ab X)
  let u : ∀ F : Ab X, (closedSupportSubsheaf Z hZ F : Ab X) ⟶ R.obj (vObj F) :=
    fun F => adj.unit.app (closedSupportSubsheaf Z hZ F : Ab X)
  have hu (F : Ab X) : IsIso (u F) := by
    letI : IsIso ((TopCat.Sheaf.forget (AddCommGrpCat.{v}) X).map (u F)) := by
      change IsIso (u F).hom
      exact closedSupport_restriction_unit_isIso Z hZ F
    exact isIso_of_reflects_iso (u F) (TopCat.Sheaf.forget (AddCommGrpCat.{v}) X)
  let factor : ∀ {G : Ab (closedSubspace Z)} {F : Ab X},
      (R.obj G ⟶ F) → (R.obj G ⟶ (closedSupportSubsheaf Z hZ F : Ab X)) :=
    fun {G F} α =>
      let η := closedSupport_complementUnit Z hZ F
      let K := kernelSubobject η
      let hzero := closedSupport_directImage_map_complement_zero Z hZ G F α
      let hK := closedSupport_complementKernel_support Z hZ F
      let hle := closedSupportSubsheaf_isLargest Z hZ F K hK
      factorThruKernelSubobject η α hzero ≫ Subobject.ofLE K
        (closedSupportSubsheaf Z hZ F) hle
  have factor_arrow {G : Ab (closedSubspace Z)} {F : Ab X}
      (α : R.obj G ⟶ F) :
      factor α ≫ (closedSupportSubsheaf Z hZ F).arrow = α := by
    let η := closedSupport_complementUnit Z hZ F
    let K := kernelSubobject η
    let hzero := closedSupport_directImage_map_complement_zero Z hZ G F α
    let hK := closedSupport_complementKernel_support Z hZ F
    let hle := closedSupportSubsheaf_isLargest Z hZ F K hK
    dsimp [factor, K]
    rw [Category.assoc, Subobject.ofLE_arrow,
      factorThruKernelSubobject_comp_arrow]
  let forward : ∀ {G : Ab (closedSubspace Z)} {F : Ab X},
      (R.obj G ⟶ F) → (G ⟶ vObj F) := fun {G F} α =>
    letI := hu F
    letI : R.Full := (adj.fullyFaithfulROfIsIsoCounit).full
    (adj.fullyFaithfulROfIsIsoCounit).preimage
      (factor α ≫ u F)
  let backward : ∀ {G : Ab (closedSubspace Z)} {F : Ab X},
      (G ⟶ vObj F) → (R.obj G ⟶ F) := fun {G F} β =>
    letI := hu F
    R.map β ≫ inv (u F) ≫ (closedSupportSubsheaf Z hZ F).arrow
  have forward_backward {G : Ab (closedSubspace Z)} {F : Ab X}
      (α : R.obj G ⟶ F) : backward (forward α) = α := by
    letI := hu F
    letI : R.Full := (adj.fullyFaithfulROfIsIsoCounit).full
    dsimp [backward]
    have hp : R.map (forward α) ≫ inv (u F) = factor α := by
      apply (cancel_mono (closedSupportSubsheaf Z hZ F).arrow).1
      rw [Category.assoc, (adj.fullyFaithfulROfIsIsoCounit).map_preimage]
      simp [Category.assoc]
    rw [← Category.assoc, hp, factor_arrow]
  have backward_forward {G : Ab (closedSubspace Z)} {F : Ab X}
      (β : G ⟶ vObj F) : forward (backward β) = β := by
    letI := hu F
    letI : R.Full := (adj.fullyFaithfulROfIsIsoCounit).full
    dsimp [forward]
    apply (adj.fullyFaithfulROfIsIsoCounit).map_injective
    rw [(adj.fullyFaithfulROfIsIsoCounit).map_preimage]
    have hp : factor (backward β) = R.map β ≫ inv (u F) := by
      apply (cancel_mono (closedSupportSubsheaf Z hZ F).arrow).1
      rw [factor_arrow]
      dsimp [backward]
      simp [Category.assoc]
    rw [hp]
    simp [Category.assoc]
    dsimp [R]
  let e : ∀ (G : Ab (closedSubspace Z)) (F : Ab X),
      (R.obj G ⟶ F) ≃ (G ⟶ vObj F) := fun G F =>
    { toFun := forward
      invFun := backward
      left_inv := forward_backward
      right_inv := backward_forward }
  have he : ∀ (G' G : Ab (closedSubspace Z)) (F : Ab X)
      (f : G' ⟶ G) (α : R.obj G ⟶ F),
      e G' F (R.map f ≫ α) = f ≫ e G F α := by
    intro G' G F f α
    letI := hu F
    letI : R.Full := (adj.fullyFaithfulROfIsIsoCounit).full
    dsimp [e, forward]
    apply (adj.fullyFaithfulROfIsIsoCounit).map_injective
    have hfac : factor (R.map f ≫ α) = R.map f ≫ factor α := by
      apply (cancel_mono (closedSupportSubsheaf Z hZ F).arrow).1
      calc
        factor (R.map f ≫ α) ≫ (closedSupportSubsheaf Z hZ F).arrow =
            R.map f ≫ α := factor_arrow _
        _ = (R.map f ≫ factor α) ≫
            (closedSupportSubsheaf Z hZ F).arrow := by
          rw [Category.assoc, factor_arrow]
    have hpre : R.map ((adj.fullyFaithfulROfIsIsoCounit).preimage
        (factor α ≫ u F)) = factor α ≫ u F :=
      (adj.fullyFaithfulROfIsIsoCounit).map_preimage _
    change R.map ((adj.fullyFaithfulROfIsIsoCounit).preimage
        (factor (R.map f ≫ α) ≫ u F)) =
      R.map (f ≫ (adj.fullyFaithfulROfIsIsoCounit).preimage (factor α ≫ u F))
    rw [Functor.map_comp, (adj.fullyFaithfulROfIsIsoCounit).map_preimage,
      hpre, hfac, Category.assoc]
  let H := Adjunction.rightAdjointOfEquiv e he
  have hadj : R ⊣ H := Adjunction.adjunctionOfEquivRight e he
  refine ⟨H, ⟨hadj⟩, ?_⟩
  intro F
  letI := hu F
  change Nonempty (R.obj (vObj F) ≅ (closedSupportSubsheaf Z hZ F : Ab X))
  exact ⟨(asIso (u F)).symm⟩

/-- Existence of the sheaf of sections supported in `Z`, on `Z`. -/
theorem exists_closedSupportSectionsFunctor {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    ∃ H : Ab X ⥤ Ab (closedSubspace Z),
      Nonempty (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ ⊣ H) := by
  rcases closedSupport_canonical_exists Z hZ with ⟨H, hH, _⟩
  exact ⟨H, hH⟩

/-- The sheaf-valued functor `F ↦ H_Z(F)`. -/
noncomputable def closedSupportSectionsFunctor {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) : Ab X ⥤ Ab (closedSubspace Z) :=
  Classical.choose (exists_closedSupportSectionsFunctor Z hZ)

/-- The chosen adjunction between closed direct image and `H_Z`. -/
noncomputable def closedSupportSectionsFunctor_adjunction
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ ⊣
      closedSupportSectionsFunctor Z hZ :=
  Classical.choice (Classical.choose_spec
    (exists_closedSupportSectionsFunctor Z hZ))

/-- The source notation `H_Z(F)`, viewed as a sheaf on `Z`. -/
abbrev sectionsWithSupportInClosed {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) : Ab (closedSubspace Z) :=
  (closedSupportSectionsFunctor Z hZ).obj F

/-- `H_Z(F)` is the sheaf corresponding to the largest supported subsheaf. -/
theorem closedSupportSectionsFunctor_obj_iso_closedSupportSubsheaf
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    Nonempty ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj
      (sectionsWithSupportInClosed Z hZ F) ≅
        (closedSupportSubsheaf Z hZ F : Ab X)) := by
  rcases closedSupport_canonical_exists Z hZ with ⟨H₀, hH₀, hIso₀⟩
  let adj₀ := Classical.choice hH₀
  let adj₁ := closedSupportSectionsFunctor_adjunction Z hZ
  let i := Adjunction.rightAdjointUniq adj₀ adj₁
  rcases hIso₀ F with ⟨e₀⟩
  let e₁ := asIso ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).map
    (i.inv.app F)) ≪≫ e₀
  change Nonempty ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj
    ((closedSupportSectionsFunctor Z hZ).obj F) ≅
      (closedSupportSubsheaf Z hZ F : Ab X))
  exact ⟨e₁⟩

/-- The adjunction Hom correspondence for sections with support. -/
noncomputable abbrev closedSupportSectionsHomEquiv {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (G : Ab (closedSubspace Z)) (F : Ab X) :
    ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj G ⟶ F) ≃
      (G ⟶ sectionsWithSupportInClosed Z hZ F) :=
  (closedSupportSectionsFunctor_adjunction Z hZ).homEquiv G F

/-- The supported-sections functor is left exact. -/
theorem closedSupportSectionsFunctor_isLeftExact {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    IsLeftExact (closedSupportSectionsFunctor Z hZ) := by
  sorry

/-! ## Closed direct image -/

/-- Closed direct image is exact on abelian sheaves. -/
theorem closedAbelianSheafDirectImage_isExact {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    IsExact (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ) := by
  sorry

/-- Closed direct image is fully faithful. -/
theorem closedAbelianSheafDirectImage_fullyFaithful {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).FullyFaithful := by
  sorry

/-- The essential image of closed direct image consists of sheaves supported in
`Z`. -/
theorem closedAbelianSheafDirectImage_essentialImage_support
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (G : Ab X) :
    (∃ F, Nonempty
      ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj F ≅ G)) ↔
      abelianSheafSupportContainedIn Z G := by
  sorry

/-- Support containment is equivalent to vanishing stalks off `Z`. -/
theorem abelianSheafSupportContainedIn_iff_closedZeroStalkCondition
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (G : Ab X) :
    abelianSheafSupportContainedIn Z G ↔
      ClosedZeroStalkCondition Z hZ G := by
  sorry

/-- Inverse image is a left inverse to closed direct image. -/
theorem closedAbelianSheafRestriction_leftInverse {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Ab (closedSubspace Z)) :
    Nonempty ((closedAbelianSheafRestriction Z hZ).obj
      ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj F) ≅ F) := by
  sorry

/-- Functorial form of the left-inverse statement. -/
theorem closedAbelianSheafRestriction_leftInverse_functor
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty
      (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ ⋙
          closedAbelianSheafRestriction Z hZ ≅
        𝟭 (Ab (closedSubspace Z))) := by
  sorry

/-- Closed direct image preserves colimits of every size represented here. -/
theorem closedAbelianSheafDirectImage_preserves_all_colimits
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    PreservesColimitsOfSize.{v, v}
      (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ) := by
  sorry

/-! ## The set-valued warning -/

/-- Closed direct image for sheaves of sets. -/
abbrev closedSetSheafDirectImage {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    TopCat.Sheaf (Type v) (closedSubspace Z) ⥤ TopCat.Sheaf (Type v) X :=
  closedSheafDirectImage (Type v) Z hZ

/-- A proper closed inclusion's set-valued direct image is not right exact. -/
theorem closedSetSheafDirectImage_not_right_exact {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (hproper : ∃ x : X, x ∉ Z) :
    ¬ PreservesFiniteColimits (closedSetSheafDirectImage Z hZ) := by
  sorry

/-- Consequently, a proper closed inclusion's set-valued direct image has no
right adjoint. -/
theorem closedSetSheafDirectImage_no_right_adjoint {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (hproper : ∃ x : X, x ∉ Z) :
    ¬ ∃ H : TopCat.Sheaf (Type v) X ⥤
        TopCat.Sheaf (Type v) (closedSubspace Z),
      Nonempty (closedSetSheafDirectImage Z hZ ⊣ H) := by
  sorry

/-! ## The pointed-sheaf warning -/

/-- Germs of sections for a sheaf of pointed sets. -/
noncomputable def pointedSectionGerm {X : TopCat.{v}}
    {F : TopCat.Sheaf (Pointed.{v}) X} (U : Opens X)
    (s : F.presheaf.obj (op U)) (x : U) :
    TopCat.Presheaf.stalk (C := Type v)
      (F.presheaf ⋙ CategoryTheory.forget Pointed) x.1 :=
  TopCat.Presheaf.germ (C := Type v)
    (F.presheaf ⋙ CategoryTheory.forget Pointed) U x.1 x.property s

/-- The germ of the distinguished point of a pointed-sheaf section. -/
noncomputable def pointedSectionBaseGerm {X : TopCat.{v}}
    {F : TopCat.Sheaf (Pointed.{v}) X} (U : Opens X) (x : U) :
    TopCat.Presheaf.stalk (C := Type v)
      (F.presheaf ⋙ CategoryTheory.forget Pointed) x.1 :=
  TopCat.Presheaf.germ (C := Type v)
    (F.presheaf ⋙ CategoryTheory.forget Pointed) U x.1 x.property
      (F.presheaf.obj (op U)).point

/-- The support of a pointed-sheaf section, relative to the basepoint. -/
def pointedSectionSupport {X : TopCat.{v}}
    {F : TopCat.Sheaf (Pointed.{v}) X} (U : Opens X)
    (s : F.presheaf.obj (op U)) : Set U :=
  {x | pointedSectionGerm U s x ≠ pointedSectionBaseGerm U x}

/-- Pointed-sheaf sections supported in a closed subset. -/
def pointedSectionsWithSupportInClosed {X : TopCat.{v}} (Z : Set X)
    {F : TopCat.Sheaf (Pointed.{v}) X} (U : Opens X) :
    Set (F.presheaf.obj (op U)) :=
  {s | pointedSectionSupport U s ⊆ closedSubsetInOpen Z U}

/-- Closed direct image for sheaves of pointed sets. -/
abbrev closedPointedSheafDirectImage {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    TopCat.Sheaf (Pointed.{v}) (closedSubspace Z) ⥤
      TopCat.Sheaf (Pointed.{v}) X :=
  closedSheafDirectImage (Pointed.{v}) Z hZ

/-- Closed direct image is exact for pointed sheaves whenever the relevant
finite limits and colimits are available. -/
theorem closedPointedSheafDirectImage_isExact {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z)
    [HasFiniteLimits (TopCat.Sheaf (Pointed.{v}) (closedSubspace Z))]
    [HasFiniteColimits (TopCat.Sheaf (Pointed.{v}) (closedSubspace Z))]
    [HasFiniteLimits (TopCat.Sheaf (Pointed.{v}) X)]
    [HasFiniteColimits (TopCat.Sheaf (Pointed.{v}) X)] :
    IsExact (closedPointedSheafDirectImage Z hZ) := by
  sorry

/-- The pointed-sheaf supported-sections functor is right adjoint to closed
direct image. -/
theorem exists_closedPointedSupportSectionsFunctor {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) :
    ∃ H : TopCat.Sheaf (Pointed.{v}) X ⥤
        TopCat.Sheaf (Pointed.{v}) (closedSubspace Z),
      Nonempty (closedPointedSheafDirectImage Z hZ ⊣ H) := by
  sorry

noncomputable def closedPointedSupportSectionsFunctor {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) :
    TopCat.Sheaf (Pointed.{v}) X ⥤
      TopCat.Sheaf (Pointed.{v}) (closedSubspace Z) :=
  Classical.choose (exists_closedPointedSupportSectionsFunctor Z hZ)

noncomputable def closedPointedSupportSectionsFunctor_adjunction
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    closedPointedSheafDirectImage Z hZ ⊣
      closedPointedSupportSectionsFunctor Z hZ :=
  Classical.choice (Classical.choose_spec
    (exists_closedPointedSupportSectionsFunctor Z hZ))

end

end Formalization.Books.Modules.Unit06
