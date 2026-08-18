import Formalization.Books.Sheaves.Unit07.Sheaves
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Over
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sheaves on Spaces, Chapter 33: Glueing sheaves

The source section is `books/sheaves.tex:5070-5327`.  Restrictions to open
subspaces and their coherence are expressed with Mathlib's canonical sheaf
pullback functors.  The category of cover glueing data below is the
source-facing packaging of the local sheaves, transition isomorphisms, and
cocycle condition.
-/

namespace Formalization.Books.Sheaves.Unit33

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Formalization.Books.Sheaves.Unit07

universe u v w

noncomputable section

/-! The module-valued part uses Mathlib's canonical sheaf-of-modules
construction directly.  These aliases have the same source-facing names as
the earlier sheaf-module chapter, while avoiding a dependency on its
presheaf-of-modules development. -/

abbrev RingSheaf (X : TopCat.{v}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) (RingCat.{w})

abbrev Mod {X : TopCat.{v}} (O : RingSheaf.{v, v} X) :=
  _root_.SheafOfModules.{v} O

abbrev openSubspace {X : TopCat.{v}} (U : Opens X) : TopCat.{v} :=
  (Opens.toTopCat X).obj U

abbrev openInclusion {X : TopCat.{v}} (U : Opens X) : openSubspace U ⟶ X :=
  Opens.inclusion' U

/-! ## Restriction along open inclusions -/

/-- The inclusion of one open subspace into a larger open subspace. -/
def openSubsetInclusion {X : TopCat.{v}} {U V : Opens X} (h : V ≤ U) :
    openSubspace V ⟶ openSubspace U :=
  (Opens.toTopCat X).map (homOfLE h)

/-- The composite of an open-subspace inclusion with the ambient inclusion. -/
theorem openSubsetInclusion_comp_openInclusion {X : TopCat.{v}}
    {U V : Opens X} (h : V ≤ U) :
    openSubsetInclusion h ≫ openInclusion U = openInclusion V := by
  apply TopCat.ext
  intro x
  rfl

/-- Composites of inclusions of nested opens are the direct inclusion. -/
theorem openSubsetInclusion_comp {X : TopCat.{v}}
    {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) :
    openSubsetInclusion hWV ≫ openSubsetInclusion hVU =
      openSubsetInclusion (hWV.trans hVU) := by
  apply TopCat.ext
  intro x
  rfl

/-- Pullback of sheaves of objects of a concrete category along a continuous map. -/
noncomputable abbrev sheafPullback (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    TopCat.Sheaf C Y ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pullback C f

/-- Pullback along a composite is canonically the composite of pullbacks. -/
noncomputable def sheafPullbackCompIso (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sheafPullback C (f ≫ g) ≅ sheafPullback C g ⋙ sheafPullback C f := by
  exact Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction C (f ≫ g))
    ((TopCat.Sheaf.pullbackPushforwardAdjunction C g).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction C f))

private theorem sheafPullbackCompIso_assoc_app (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y Z T : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (F : TopCat.Sheaf C T) :
    (sheafPullbackCompIso C f (g ≫ h)).hom.app F ≫
        (sheafPullback C f).map ((sheafPullbackCompIso C g h).hom.app F) =
      (sheafPullbackCompIso C (f ≫ g) h).hom.app F ≫
        (sheafPullbackCompIso C f g).hom.app
          ((sheafPullback C h).obj F) := by
  simp [sheafPullbackCompIso, Category.assoc]

/-- Restriction of sheaves to an open subspace. -/
noncomputable abbrev sheafRestriction (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubspace U) :=
  sheafPullback C (openInclusion U)

/-- Restriction of a sheaf on `U` to a smaller open `V ≤ U`. -/
noncomputable abbrev sheafMapRestriction (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {U V : Opens X} (h : V ≤ U) :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C (openSubspace V) :=
  sheafPullback C (openSubsetInclusion h)

/-! ## Coherent restriction maps -/

/-- Restriction twice to an open intersection, canonically identified with direct restriction. -/
noncomputable def sheafRestrictionRestrictionIso (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {U V : Opens X} (h : V ≤ U)
    (F : TopCat.Sheaf C X) :
    ((sheafMapRestriction C h).obj ((sheafRestriction C U).obj F)) ≅
      (sheafRestriction C V).obj F := by
  let e := (sheafPullbackCompIso C
    (openSubsetInclusion h) (openInclusion U)).app F
  let e' :
      (sheafPullback C (openSubsetInclusion h ≫ openInclusion U)).obj F ≅
        (sheafPullback C (openInclusion V)).obj F :=
    eqToIso (by rw [openSubsetInclusion_comp_openInclusion h])
  exact e.symm ≪≫ e'

/-- Restriction of a morphism between sheaves on an open subspace. -/
noncomputable def sheafMapRestriction_map (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {U V : Opens X} (h : V ≤ U)
    {F G : TopCat.Sheaf C (openSubspace U)} (φ : F ⟶ G) :
    (sheafMapRestriction C h).obj F ⟶ (sheafMapRestriction C h).obj G :=
  (sheafMapRestriction C h).map φ

/-- Restrict a morphism on `X` directly to a smaller open, transporting the two
successive pullbacks through the canonical comparison isomorphisms. -/
noncomputable def sheafMap_restrictToOpen (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {U V : Opens X} (h : V ≤ U)
    {F G : TopCat.Sheaf C X}
    (φ : (sheafRestriction C U).obj F ⟶ (sheafRestriction C U).obj G) :
    (sheafRestriction C V).obj F ⟶ (sheafRestriction C V).obj G :=
  (sheafRestrictionRestrictionIso C h F).inv ≫
  (sheafMapRestriction C h).map φ ≫
      (sheafRestrictionRestrictionIso C h G).hom

/-- Restrict a map from a global sheaf to a sheaf on `U` to a smaller open. -/
noncomputable def sheafMap_toOpen (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {U V : Opens X} (h : V ≤ U)
    {F : TopCat.Sheaf C X} {G : TopCat.Sheaf C (openSubspace U)}
    (φ : (sheafRestriction C U).obj F ⟶ G) :
    (sheafRestriction C V).obj F ⟶ (sheafMapRestriction C h).obj G :=
    (sheafRestrictionRestrictionIso C h F).inv ≫
    (sheafMapRestriction C h).map φ

/-- Restriction twice inside a fixed open is canonically direct restriction. -/
noncomputable def sheafNestedRestrictionIso (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V)
    (F : TopCat.Sheaf C (openSubspace U)) :
    ((sheafMapRestriction C hWV).obj ((sheafMapRestriction C hVU).obj F)) ≅
      (sheafMapRestriction C (hWV.trans hVU)).obj F := by
  let e := (sheafPullbackCompIso C
    (openSubsetInclusion hWV) (openSubsetInclusion hVU)).app F
  let e' :
      (sheafPullback C (openSubsetInclusion hWV ≫ openSubsetInclusion hVU)).obj F ≅
        (sheafPullback C (openSubsetInclusion (hWV.trans hVU))).obj F :=
    eqToIso (by rw [openSubsetInclusion_comp hVU hWV])
  exact e.symm ≪≫ e'

/-- Sections of a sheaf on an open subspace and sections of its pullback to a
smaller open are canonically identified. -/
theorem exists_sheafRestrictionSectionsIso (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {U V : Opens X} (h : V ≤ U)
    (F : TopCat.Sheaf C (openSubspace U)) :
    Nonempty (F.presheaf.obj
        (op (Opens.comap (openInclusion U).hom V)) ≅
      ((sheafMapRestriction C h).obj F).presheaf.obj (op ⊤)) := by
  let hf : Topology.IsOpenEmbedding (openSubsetInclusion h) := by
    change Topology.IsOpenEmbedding (Set.inclusion (SetLike.coe_subset_coe.2 h))
    exact Opens.isOpenEmbedding_of_le h
  have htop : hf.functor.obj ⊤ = Opens.comap (openInclusion U).hom V := by
    ext x
    constructor
    · rintro ⟨y, -, hxy⟩
      rw [← hxy]
      exact y.property
    · intro hx
      refine ⟨⟨x.1, hx⟩, trivial, ?_⟩
      rfl
  let e := (hf.sheafPullbackIso C).app F
  let e' : ((hf.sheafPullback C).obj F).presheaf.obj (op ⊤) ≅
      ((sheafPullback C (openSubsetInclusion h)).obj F).presheaf.obj (op ⊤) :=
    { hom := e.inv.hom.app (op ⊤)
      inv := e.hom.hom.app (op ⊤)
      hom_inv_id := by
        change e.inv.hom.app (op ⊤) ≫ e.hom.hom.app (op ⊤) = 𝟙 _
        exact congrArg (fun f => f.hom.app (op ⊤)) e.inv_hom_id
      inv_hom_id := by
        change e.hom.hom.app (op ⊤) ≫ e.inv.hom.app (op ⊤) = 𝟙 _
        exact congrArg (fun f => f.hom.app (op ⊤)) e.hom_inv_id }
  refine ⟨eqToIso ?_ ≪≫ e'⟩
  change F.presheaf.obj (op (Opens.comap (openInclusion U).hom V)) =
    F.presheaf.obj (op (hf.functor.obj ⊤))
  rw [htop]

/-- A chosen section comparison for an open-subspace restriction. -/
noncomputable def sheafRestrictionSectionsIso (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {U V : Opens X} (h : V ≤ U)
    (F : TopCat.Sheaf C (openSubspace U)) :
    F.presheaf.obj (op (Opens.comap (openInclusion U).hom V)) ≅
      ((sheafMapRestriction C h).obj F).presheaf.obj (op ⊤) :=
  Classical.choice (exists_sheafRestrictionSectionsIso C h F)

/-! ## Maps and the internal Hom sheaf -/

/-- The compatibility condition for a family of local sheaf maps. -/
abbrev SheafMapGlueingCondition (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {ι : Type v} (U : ι → Opens X)
    {F G : TopCat.Sheaf C X}
    (φ : ∀ i, (sheafRestriction C (U i)).obj F ⟶
      (sheafRestriction C (U i)).obj G) : Prop :=
  ∀ i j,
    sheafMap_restrictToOpen C (show U i ⊓ U j ≤ U i from inf_le_left) (φ i) =
      sheafMap_restrictToOpen C (show U i ⊓ U j ≤ U j from inf_le_right) (φ j)

/- A category-valued form used for the structure-preserving variants below. -/
theorem glue_maps_of_concrete_category (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {ι : Type v} (U : ι → Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    {F G : TopCat.Sheaf C X}
    (φ : ∀ i, (sheafRestriction C (U i)).obj F ⟶
      (sheafRestriction C (U i)).obj G)
    (hφ : SheafMapGlueingCondition C U φ) :
    ∃! ψ : F ⟶ G, ∀ i, (sheafRestriction C (U i)).map ψ = φ i := by
  let localMap (i : ι) :
      ((Opens.grothendieckTopology X).overPullback C (U i)).obj F ⟶
        ((Opens.grothendieckTopology X).overPullback C (U i)).obj G := by
    let eF := (U i).isOpenEmbedding.sheafPullbackIso C
    let eG := (U i).isOpenEmbedding.sheafPullbackIso C
    exact (U i).sheafRestrictSheafEquivOver.inv.app F ≫
      (U i).sheafEquivOver.inverse.map
        (eF.inv.app F ≫ φ i ≫ eG.hom.app G) ≫
        (U i).sheafRestrictSheafEquivOver.hom.app G
  let H := CategoryTheory.sheafHom F G
  let localSection (i : ι) : H.1.obj (op (U i)) := localMap i
  have hlocal : TopCat.Presheaf.IsCompatible H.1 U localSection := by
    intro i j
    simpa [H, localSection, localMap] using hφ i j
  have htop : (⊤ : Opens X) ≤ iSup U := by
    rw [hU.iSup_eq_top]
  obtain ⟨s₀, hs₀, hs₀_unique⟩ := TopCat.Sheaf.existsUnique_gluing' H U (⊤ : Opens X)
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) htop localSection hlocal
  let sec : H.1.sections :=
    ⟨fun V => H.1.map (homOfLE le_top).op s₀, by
      intro V W f
      change H.1.map f
          (H.1.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op s₀) =
        H.1.map (homOfLE (show W.unop ≤ ⊤ from le_top)).op s₀
      rw [← ConcreteCategory.comp_apply, ← H.1.map_comp]
      congr 1
      simp⟩
  let ψ : F ⟶ G := (CategoryTheory.sheafHomSectionsEquiv F G) sec
  refine ⟨ψ, ?_, ?_⟩
  · intro i
    have hi := hs₀ i
    simpa [ψ, sec, localSection, localMap] using hi
  · intro ψ' hψ'
    let sec' : H.1.sections :=
      (CategoryTheory.sheafHomSectionsEquiv F G).symm ψ'
    have hs' (i : ι) :
        H.1.map (homOfLE (show U i ≤ ⊤ from le_top)).op (sec'.val (op ⊤)) =
          localSection i := by
      simpa [sec', localSection, localMap] using hψ' i
    have htop_eq : sec'.val (op ⊤) = s₀ := by
      apply hs₀_unique
      exact hs'
    have hsec_eq : sec' = sec := by
      apply (Functor.sections_ext_iff).2
      intro V
      have hsec' := sec'.property (homOfLE le_top).op
      have hsec := sec.property (homOfLE le_top).op
      rw [← hsec', ← hsec, htop_eq]
    apply (CategoryTheory.sheafHomSectionsEquiv F G).injective
    simpa [ψ, sec'] using hsec_eq
/-
  let localMap (i : ι) :
      ((Opens.grothendieckTopology X).overPullback C (U i)).obj F ⟶
        ((Opens.grothendieckTopology X).overPullback C (U i)).obj G := by
    let eF := (U i).isOpenEmbedding.sheafPullbackIso C
    let eG := (U i).isOpenEmbedding.sheafPullbackIso C
    exact (U i).sheafRestrictSheafEquivOver.inv.app F ≫
      (U i).sheafEquivOver.inverse.map
        (eF.inv.app F ≫ φ i ≫ eG.hom.app G) ≫
        (U i).sheafRestrictSheafEquivOver.hom.app G
  let H := CategoryTheory.sheafHom F G
  let localSection (i : ι) : H.1.obj (op (U i)) := localMap i
  have hlocal : TopCat.Presheaf.IsCompatible H.1 U localSection := by
    intro i j
    simpa [H, localSection, localMap] using hφ i j
  have htop : (⊤ : Opens X) ≤ iSup U := by
    rw [hU.iSup_eq_top]
  obtain ⟨s₀, hs₀, hs₀_unique⟩ := TopCat.Sheaf.existsUnique_gluing' H U (⊤ : Opens X)
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) htop localSection hlocal
  let sec : H.1.sections :=
    ⟨fun V => H.1.map (homOfLE le_top).op s₀, by
      intro V W f
      change H.1.map f
          (H.1.map (homOfLE (show W.unop ≤ ⊤ from le_top)).op s₀) =
        H.1.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op s₀
      rw [← ConcreteCategory.comp_apply, ← H.1.map_comp]
      congr 1
      simp⟩
  let ψ : F ⟶ G := (CategoryTheory.sheafHomSectionsEquiv F G) sec
  refine ⟨ψ, ?_, ?_⟩
  · intro i
    have hi := hs₀ i
    simpa [ψ, sec, localSection, localMap] using hi
  · intro ψ' hψ'
    let sec' : H.1.sections :=
      (CategoryTheory.sheafHomSectionsEquiv F G).symm ψ'
    have hs' (i : ι) :
        H.1.map (homOfLE (show U i ≤ ⊤ from le_top)).op (sec'.val (op ⊤)) =
          localSection i := by
      simpa [sec', localSection, localMap] using hψ' i
    have htop_eq : sec'.val (op ⊤) = s₀ := by
      apply hs₀_unique
      exact hs'
    have hsec_eq : sec' = sec := by
      apply (Functor.sections_ext_iff).2
      intro V
      have hsec' := sec'.property (homOfLE le_top).op
      have hsec := sec.property (homOfLE le_top).op
      rw [← hsec', ← hsec, htop_eq]
    simpa [ψ, sec'] using hsec_eq
 -/

/-! The source's set-valued statement.  The general declaration above is only
used as the reusable interface for the later algebraic variants. -/

/-- Compatibility of maps between restrictions of set-valued sheaves. -/
abbrev SetSheafMapGlueingCondition {X : TopCat.{v}} {ι : Type v}
    (U : ι → Opens X) {F G : Sh.{v, v} X}
    (φ : ∀ i, (sheafRestriction (Type v) (U i)).obj F ⟶
      (sheafRestriction (Type v) (U i)).obj G) : Prop :=
  SheafMapGlueingCondition (Type v) U φ

/-- Compatible maps of sheaves of sets glue uniquely over an open cover. -/
theorem glue_maps {X : TopCat.{v}} {ι : Type v} (U : ι → Opens X)
    (hU : TopologicalSpace.IsOpenCover U) {F G : Sh.{v, v} X}
    (φ : ∀ i, (sheafRestriction (Type v) (U i)).obj F ⟶
      (sheafRestriction (Type v) (U i)).obj G)
    (hφ : SetSheafMapGlueingCondition U φ) :
    ∃! ψ : F ⟶ G, ∀ i, (sheafRestriction (Type v) (U i)).map ψ = φ i := by
  exact glue_maps_of_concrete_category (Type v) U hU φ hφ

/- The source's internal Hom sheaf consequence.  Mathlib's `sheafHom` is
the canonical construction: its value on an object is the morphism type
between the two restrictions to the corresponding over-category. -/
noncomputable abbrev sheafInternalHom {X : TopCat.{v}}
    (F G : TopCat.Sheaf (Type v) X) :
    TopCat.Sheaf (Type v) X :=
  CategoryTheory.sheafHom F G

/-- Global sections of the internal Hom sheaf are morphisms of sheaves. -/
noncomputable abbrev sheafInternalHom_sections_equiv {X : TopCat.{v}}
    (F G : TopCat.Sheaf (Type v) X) :
    (sheafInternalHom F G).presheaf.sections ≃ (F ⟶ G) :=
  CategoryTheory.sheafHomSectionsEquiv F G

/-- The component of the internal Hom on an open `U`. -/
noncomputable abbrev sheafInternalHomSections {X : TopCat.{v}}
    (F G : Sh.{v, v} X) (U : Opens X) : Type v :=
  (sheafInternalHom F G).presheaf.obj (op U)

/-- On each open, the canonical internal-Hom sections identify with maps
between the corresponding restrictions of the two sheaves. -/
theorem exists_sheafInternalHomSectionsEquiv {X : TopCat.{v}}
    (F G : Sh.{v, v} X) (U : Opens X) :
    Nonempty (sheafInternalHomSections F G U ≃
      ((sheafRestriction (Type v) U).obj F ⟶
        (sheafRestriction (Type v) U).obj G)) := by
  let E := (U.sheafEquivOver (A := Type v)).functor
  let qF := (U.sheafRestrictSheafEquivOver (A := Type v)).app F
  let qG := (U.sheafRestrictSheafEquivOver (A := Type v)).app G
  let eF : E.obj (((Opens.grothendieckTopology X).overPullback (Type v) U).obj F) ≅
      (U.sheafRestrict (C := Type v)).obj F :=
    E.mapIso qF.symm ≪≫
      (U.sheafEquivOver (A := Type v)).counitIso.app
        ((U.sheafRestrict (C := Type v)).obj F)
  let eG : E.obj (((Opens.grothendieckTopology X).overPullback (Type v) U).obj G) ≅
      (U.sheafRestrict (C := Type v)).obj G :=
    E.mapIso qG.symm ≪≫
      (U.sheafEquivOver (A := Type v)).counitIso.app
        ((U.sheafRestrict (C := Type v)).obj G)
  let rF :=
    (Topology.IsOpenEmbedding.sheafPullbackIso (Type v) U.isOpenEmbedding).app F
  let rG :=
    (Topology.IsOpenEmbedding.sheafPullbackIso (Type v) U.isOpenEmbedding).app G
  exact ⟨
    ((U.sheafEquivOver (A := Type v)).fullyFaithfulFunctor.homEquiv.trans
      (eF.homCongr eG)).trans
      (rF.symm.homCongr rG.symm)⟩

/-- A chosen version of the internal-Hom identification on an open. -/
noncomputable def sheafInternalHomSectionsEquiv {X : TopCat.{v}}
    (F G : Sh.{v, v} X) (U : Opens X) :
    sheafInternalHomSections F G U ≃
      ((sheafRestriction (Type v) U).obj F ⟶
        (sheafRestriction (Type v) U).obj G) :=
  Classical.choice (exists_sheafInternalHomSectionsEquiv F G U)

/-! ## Glueing data -/

/-- The transition map of glueing data, restricted to an arbitrary smaller open. -/
noncomputable def glueingTransitionAt (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {ι : Type v} (U : ι → Opens X)
    (sheaf : ∀ i, TopCat.Sheaf C (openSubspace (U i)))
    (transition : ∀ i j,
      (sheafMapRestriction C (show U i ⊓ U j ≤ U i from inf_le_left)).obj (sheaf i) ≅
        (sheafMapRestriction C (show U i ⊓ U j ≤ U j from inf_le_right)).obj (sheaf j))
    (i j : ι) (W : Opens X) (hW : W ≤ U i ⊓ U j) :
    (sheafMapRestriction C (hW.trans (show U i ⊓ U j ≤ U i from inf_le_left))).obj (sheaf i) ⟶
      (sheafMapRestriction C (hW.trans (show U i ⊓ U j ≤ U j from inf_le_right))).obj (sheaf j) := by
  let e₁ := sheafNestedRestrictionIso C
    (show U i ⊓ U j ≤ U i from inf_le_left) hW (sheaf i)
  let e₂ := sheafNestedRestrictionIso C
    (show U i ⊓ U j ≤ U j from inf_le_right) hW (sheaf j)
  exact e₁.inv ≫
      (sheafMapRestriction C hW).map (transition i j).hom ≫ e₂.hom

/-- A family of local sheaves, transition isomorphisms, and their cocycle. -/
structure SheafGlueingData (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{v}} {ι : Type v} (U : ι → Opens X) where
  sheaf : ∀ i, TopCat.Sheaf C (openSubspace (U i))
  transition : ∀ i j,
    (sheafMapRestriction C (show U i ⊓ U j ≤ U i from inf_le_left)).obj (sheaf i) ≅
      (sheafMapRestriction C (show U i ⊓ U j ≤ U j from inf_le_right)).obj (sheaf j)
  cocycle : ∀ i j k,
    glueingTransitionAt C U sheaf transition i j ((U i ⊓ U j) ⊓ U k)
        (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left) ≫
      glueingTransitionAt C U sheaf transition j k ((U i ⊓ U j) ⊓ U k)
        (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right) =
    glueingTransitionAt C U sheaf transition i k ((U i ⊓ U j) ⊓ U k)
        (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
          le_inf (inf_le_left.trans inf_le_left) inf_le_right)

namespace SheafGlueingData

variable {C : Type u} [Category.{v} C]
  {FC : C → C → Type*} {CC : C → Type v}
  [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
  [HasColimits C] [HasLimits C]
  [PreservesLimits (CategoryTheory.forget C)]
  [PreservesFilteredColimits (CategoryTheory.forget C)]
  [(CategoryTheory.forget C).ReflectsIsomorphisms]
  {X : TopCat.{v}} {ι : Type v} {U : ι → Opens X}

/- A morphism of glueing data is a compatible family of local morphisms. -/
@[ext]
structure Hom (D E : SheafGlueingData C U) where
  app : ∀ i, D.sheaf i ⟶ E.sheaf i
  comm : ∀ i j,
    (sheafMapRestriction C (show U i ⊓ U j ≤ U i from inf_le_left)).map (app i) ≫
        (E.transition i j).hom =
      (D.transition i j).hom ≫
        (sheafMapRestriction C (show U i ⊓ U j ≤ U j from inf_le_right)).map (app j)

instance : Category (SheafGlueingData C U) where
  Hom D E := Hom D E
  id D :=
    { app := fun i => 𝟙 _
      comm := by simp }
  comp f g :=
    { app := fun i => f.app i ≫ g.app i
      comm := by
        intro i j
        rw [Functor.map_comp, Category.assoc, g.comm, ← Category.assoc,
          f.comm, Category.assoc, Functor.map_comp] }
  id_comp f := by
    ext i
    simp
  comp_id f := by
    ext i
    simp
  assoc f g h := by
    ext i
    simp [Category.assoc]

end SheafGlueingData

/-! ## The canonical glueing datum and its realization -/

section CanonicalGlueing

variable {C : Type u} [Category.{v} C]
  {FC : C → C → Type*} {CC : C → Type v}
  [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
  [HasColimits C] [HasLimits C]
  [PreservesLimits (CategoryTheory.forget C)]
  [PreservesFilteredColimits (CategoryTheory.forget C)]
  [(CategoryTheory.forget C).ReflectsIsomorphisms]
  {X : TopCat.{v}} {ι : Type v} {U : ι → Opens X}

/-- The transition isomorphism induced by a sheaf on the ambient space. -/
noncomputable def canonicalSheafGlueingTransition
    (F : TopCat.Sheaf C X) (i j : ι) :
    (sheafMapRestriction C (show U i ⊓ U j ≤ U i from inf_le_left)).obj
        ((sheafRestriction C (U i)).obj F) ≅
      (sheafMapRestriction C (show U i ⊓ U j ≤ U j from inf_le_right)).obj
        ((sheafRestriction C (U j)).obj F) :=
  sheafRestrictionRestrictionIso C (show U i ⊓ U j ≤ U i from inf_le_left) F ≪≫
    (sheafRestrictionRestrictionIso C (show U i ⊓ U j ≤ U j from inf_le_right) F).symm

/-- The canonical transitions satisfy the cocycle condition. -/
theorem canonicalSheafGlueingTransition_cocycle
    (F : TopCat.Sheaf C X) (i j k : ι) :
    glueingTransitionAt C U
        (fun i => (sheafRestriction C (U i)).obj F)
        (canonicalSheafGlueingTransition (U := U) F)
        i j ((U i ⊓ U j) ⊓ U k)
        (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left) ≫
      glueingTransitionAt C U
        (fun i => (sheafRestriction C (U i)).obj F)
        (canonicalSheafGlueingTransition (U := U) F)
        j k ((U i ⊓ U j) ⊓ U k)
        (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right) =
    glueingTransitionAt C U
        (fun i => (sheafRestriction C (U i)).obj F)
        (canonicalSheafGlueingTransition (U := U) F)
        i k ((U i ⊓ U j) ⊓ U k)
        (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
          le_inf (inf_le_left.trans inf_le_left) inf_le_right) := by
  sorry

/-- The glueing datum obtained by restricting a sheaf to every member of the
cover. -/
noncomputable def canonicalSheafGlueingData (F : TopCat.Sheaf C X) :
    SheafGlueingData C U where
  sheaf i := (sheafRestriction C (U i)).obj F
  transition := canonicalSheafGlueingTransition (U := U) F
  cocycle := canonicalSheafGlueingTransition_cocycle (U := U) F

/-- A sheaf together with the local identifications supplied by glueing. -/
structure SheafGlueingSolution (D : SheafGlueingData C U) where
  sheaf : TopCat.Sheaf C X
  iso : ∀ i, (sheafRestriction C (U i)).obj sheaf ≅ D.sheaf i
  comm : ∀ i j,
    (sheafRestrictionRestrictionIso C
        (show U i ⊓ U j ≤ U i from inf_le_left) sheaf).inv ≫
        (sheafMapRestriction C
          (show U i ⊓ U j ≤ U i from inf_le_left)).map (iso i).hom ≫
        (D.transition i j).hom =
      (sheafRestrictionRestrictionIso C
        (show U i ⊓ U j ≤ U j from inf_le_right) sheaf).inv ≫
        (sheafMapRestriction C
          (show U i ⊓ U j ≤ U j from inf_le_right)).map (iso j).hom

/-- The sheaf-glueing construction exists for every open-cover glueing datum. -/
theorem exists_sheafGlueingSolution
    (hU : TopologicalSpace.IsOpenCover U) (D : SheafGlueingData C U) :
    Nonempty (SheafGlueingSolution D) := by
  sorry

/-- The existential form of the sheaf-glueing lemma.  This is the direct
source-facing interface: it exposes the glued sheaf, its local comparison
isomorphisms, and the commuting intersection squares separately. -/
theorem glue_sheaves_exists
    (hU : TopologicalSpace.IsOpenCover U) (D : SheafGlueingData C U) :
    ∃ (F : TopCat.Sheaf C X)
      (φ : ∀ i, (sheafRestriction C (U i)).obj F ≅ D.sheaf i),
      ∀ i j,
        (sheafRestrictionRestrictionIso C
            (show U i ⊓ U j ≤ U i from inf_le_left) F).inv ≫
            (sheafMapRestriction C
              (show U i ⊓ U j ≤ U i from inf_le_left)).map (φ i).hom ≫
            (D.transition i j).hom =
          (sheafRestrictionRestrictionIso C
            (show U i ⊓ U j ≤ U j from inf_le_right) F).inv ≫
            (sheafMapRestriction C
              (show U i ⊓ U j ≤ U j from inf_le_right)).map (φ j).hom := by
  rcases exists_sheafGlueingSolution hU D with ⟨S⟩
  exact ⟨S.sheaf, S.iso, S.comm⟩

/-- A chosen realization of glueing data. -/
noncomputable def gluedSheafGlueingSolution
    (hU : TopologicalSpace.IsOpenCover U) (D : SheafGlueingData C U) :
    SheafGlueingSolution D :=
  Classical.choice (exists_sheafGlueingSolution hU D)

/-- The sheaf underlying the chosen realization of glueing data. -/
noncomputable abbrev gluedSheaf
    (hU : TopologicalSpace.IsOpenCover U) (D : SheafGlueingData C U) :
    TopCat.Sheaf C X :=
  (gluedSheafGlueingSolution hU D).sheaf

/-- The local comparison isomorphisms for the chosen glued sheaf. -/
noncomputable abbrev gluedSheafIso
    (hU : TopologicalSpace.IsOpenCover U) (D : SheafGlueingData C U) (i : ι) :
    (sheafRestriction C (U i)).obj (gluedSheaf hU D) ≅ D.sheaf i :=
  (gluedSheafGlueingSolution hU D).iso i

/-- The commutative square identifying the two local presentations on an
intersection. -/
theorem gluedSheafIso_comm
    (hU : TopologicalSpace.IsOpenCover U) (D : SheafGlueingData C U)
    (i j : ι) :
    (sheafRestrictionRestrictionIso C
        (show U i ⊓ U j ≤ U i from inf_le_left) (gluedSheaf hU D)).inv ≫
        (sheafMapRestriction C
          (show U i ⊓ U j ≤ U i from inf_le_left)).map (gluedSheafIso hU D i).hom ≫
        (D.transition i j).hom =
      (sheafRestrictionRestrictionIso C
        (show U i ⊓ U j ≤ U j from inf_le_right) (gluedSheaf hU D)).inv ≫
        (sheafMapRestriction C
          (show U i ⊓ U j ≤ U j from inf_le_right)).map (gluedSheafIso hU D j).hom :=
  (gluedSheafGlueingSolution hU D).comm i j

end CanonicalGlueing

/-! ## Set-valued and structure-preserving instances -/

section StructureVariants

variable {X : TopCat.{v}} {ι : Type v} {U : ι → Opens X}

/-- Glueing data for sheaves of sets. -/
abbrev SetSheafGlueingData (U : ι → Opens X) :=
  SheafGlueingData (Type v) U

/-- The sections of the `i`-th local sheaf over `W ∩ U i`. -/
abbrev GlueingLocalSection (D : SetSheafGlueingData U) (W : Opens X) (i : ι) :=
  (D.sheaf i).presheaf.obj
    (op (Opens.comap (openInclusion (U i)).hom (W ⊓ U i)))

/-- The pairwise compatibility relation in the sectionwise construction of a
glued sheaf. -/
def glueingSectionCompatibilityAt (D : SetSheafGlueingData U) (W : Opens X)
    (s : ∀ i, GlueingLocalSection D W i) (i j : ι) : Prop := by
  let T : Opens X := (W ⊓ U i) ⊓ U j
  let hT : T ≤ U i ⊓ U j :=
    show (W ⊓ U i) ⊓ U j ≤ U i ⊓ U j from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
  let hT_i : T ≤ U i := hT.trans inf_le_left
  let hT_j : T ≤ U j := hT.trans inf_le_right
  let hT_Wi : T ≤ W ⊓ U i := inf_le_left
  let hT_Wj : T ≤ W ⊓ U j :=
    show (W ⊓ U i) ⊓ U j ≤ W ⊓ U j from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
  let hW_i : W ⊓ U i ≤ U i := inf_le_right
  let hW_j : W ⊓ U j ≤ U j := inf_le_right
  let siT :=
    (D.sheaf i).presheaf.map
      (homOfLE (Opens.comap_mono (openInclusion (U i)).hom hT_Wi)).op (s i)
  let sjT :=
    (D.sheaf j).presheaf.map
      (homOfLE (Opens.comap_mono (openInclusion (U j)).hom hT_Wj)).op (s j)
  let ei' := sheafRestrictionSectionsIso (Type v) hT_i (D.sheaf i)
  let ej' := sheafRestrictionSectionsIso (Type v) hT_j (D.sheaf j)
  exact ((glueingTransitionAt (Type v) U D.sheaf D.transition i j T hT).hom.app
      (op (⊤ : Opens (openSubspace T))))
      (ei'.hom (siT)) = ej'.hom (sjT)

/-- A compatible family of local sections over `W`, as in the explicit first
proof of the sheaf-glueing lemma. -/
structure GlueingSection (D : SetSheafGlueingData U) (W : Opens X) where
  value : ∀ i, GlueingLocalSection D W i
  compatible : ∀ i j, glueingSectionCompatibilityAt D W value i j

/-- The equalizer presentation of the compatible-family sections. -/
abbrev GlueingSectionEqualizer (D : SetSheafGlueingData U) (W : Opens X) :=
  {s : ∀ i, GlueingLocalSection D W i //
    ∀ i j, glueingSectionCompatibilityAt D W s i j}

/-- The explicit family structure and its equalizer presentation are
canonically equivalent. -/
def glueingSection_equalizerEquiv (D : SetSheafGlueingData U) (W : Opens X) :
    GlueingSection D W ≃ GlueingSectionEqualizer D W where
  toFun s := ⟨s.value, s.compatible⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sectionwise family used in the explicit construction of the glued
sheaf. -/
abbrev GlueingSectionFamily (D : SetSheafGlueingData U) (W : Opens X) :=
  GlueingSection D W

/-- The componentwise restriction of a family of local sections. -/
noncomputable def glueingSectionRestrictValue
    (D : SetSheafGlueingData U) {W W' : Opens X} (h : W' ≤ W)
    (s : GlueingSection D W) (i : ι) : GlueingLocalSection D W' i :=
  (D.sheaf i).presheaf.map
    (homOfLE (Opens.comap_mono (openInclusion (U i)).hom
      (show W' ⊓ U i ≤ W ⊓ U i from
        le_inf (inf_le_left.trans h) inf_le_right))).op (s.value i)

/-- Componentwise restriction preserves the pairwise compatibility relation. -/
theorem glueingSectionRestrict_compatible
    (D : SetSheafGlueingData U) {W W' : Opens X} (h : W' ≤ W)
    (s : GlueingSection D W) (i j : ι) :
      glueingSectionCompatibilityAt D W'
      (fun i => glueingSectionRestrictValue D h s i) i j := by
  have hs := s.compatible i j
  unfold glueingSectionCompatibilityAt at hs ⊢
  dsimp [glueingSectionRestrictValue] at hs ⊢
  simpa [Category.assoc] using hs
/-
  have hs := s.compatible i j
  unfold glueingSectionCompatibilityAt at hs ⊢
  dsimp [glueingSectionRestrictValue] at hs ⊢
  

 -/
/-- Restriction maps for the sectionwise construction of the glued sheaf. -/
noncomputable def glueingSectionRestrict
    (D : SetSheafGlueingData U) {W W' : Opens X} (h : W' ≤ W)
    (s : GlueingSection D W) : GlueingSection D W' where
  value := fun i => glueingSectionRestrictValue D h s i
  compatible := glueingSectionRestrict_compatible D h s

/-- The identity law for the sectionwise restriction maps. -/
theorem glueingSectionRestrict_id
    (D : SetSheafGlueingData U) (W : Opens X) (s : GlueingSection D W) :
    glueingSectionRestrict D (le_refl W) s = s := by
  sorry

/-- The composition law for the sectionwise restriction maps. -/
theorem glueingSectionRestrict_comp
    (D : SetSheafGlueingData U) {W W' W'' : Opens X}
    (h₁ : W' ≤ W) (h₂ : W'' ≤ W') (s : GlueingSection D W) :
    glueingSectionRestrict D h₂ (glueingSectionRestrict D h₁ s) =
      glueingSectionRestrict D (h₂.trans h₁) s := by
  sorry

/-- The presheaf whose sections are the compatible families in the explicit
construction. -/
noncomputable def glueingSectionPresheaf (D : SetSheafGlueingData U) :
    TopCat.Presheaf (Type v) X where
  obj W := GlueingSection D W.unop
  map f := TypeCat.ofHom (fun s => glueingSectionRestrict D f.unop.le s)
  map_id := by
    intro W
    ext s
    exact glueingSectionRestrict_id D W.unop s
  map_comp := by
    intro W W' W'' f g
    ext s
    dsimp
    exact (glueingSectionRestrict_comp D f.unop.le g.unop.le s).symm

/-- Glueing data for sheaves of abelian groups. -/
abbrev AbelianSheafGlueingData (U : ι → Opens X) :=
  SheafGlueingData (AddCommGrpCat.{v}) U

/-!
The source also includes sheaves of modules over a sheaf of rings.  Such
sheaves are not sheaves valued in one fixed algebraic category: the scalar
ring varies with the open.  The following small interface keeps that scalar
dependence explicit while reusing the additive-sheaf glueing data above.
-/

/-- The restriction of a sheaf of rings to an open subspace. -/
abbrev restrictedRingSheaf (O : RingSheaf.{v, v} X) (V : Opens X) :
    RingSheaf.{v, v} (openSubspace V) :=
  (TopologicalSpace.Opens.sheafRestrict V).obj O

/-- The underlying additive sheaf of a sheaf of modules. -/
def moduleUnderlyingSheaf {Y : TopCat.{v}} {O : RingSheaf.{v, v} Y}
    (M : Mod O) : TopCat.Sheaf (AddCommGrpCat.{v}) Y :=
  ⟨M.val.presheaf, M.isSheaf⟩

/-- The underlying additive morphism of a morphism of sheaf modules. -/
def moduleUnderlyingSheafMorphism {Y : TopCat.{v}} {O : RingSheaf.{v, v} Y}
    {M N : Mod O} (f : M ⟶ N) :
    moduleUnderlyingSheaf M ⟶ moduleUnderlyingSheaf N :=
  ⟨(PresheafOfModules.toPresheaf O.obj).map f.val⟩

/-- A scalar-compatibility certificate for a transition of local module
sheaves.  The two local restrictions are presented by module sheaves over
the scalar sheaf on the intersection, and the underlying additive transition
is induced by a module isomorphism. -/
structure OModuleGlueingTransition {O : RingSheaf.{v, v} X}
    {U : ι → Opens X} {i j : ι}
    (Mi : Mod (restrictedRingSheaf (X := X) O (U i)))
    (Mj : Mod (restrictedRingSheaf (X := X) O (U j)))
    (τ :
      (sheafMapRestriction (AddCommGrpCat.{v})
        (show U i ⊓ U j ≤ U i from inf_le_left)).obj
          (moduleUnderlyingSheaf Mi) ≅
        (sheafMapRestriction (AddCommGrpCat.{v})
          (show U i ⊓ U j ≤ U j from inf_le_right)).obj
          (moduleUnderlyingSheaf Mj)) where
  left : Mod (restrictedRingSheaf (X := X) O (U i ⊓ U j))
  right : Mod (restrictedRingSheaf (X := X) O (U i ⊓ U j))
  leftIso :
    moduleUnderlyingSheaf left ≅
      (sheafMapRestriction (AddCommGrpCat.{v})
        (show U i ⊓ U j ≤ U i from inf_le_left)).obj
          (moduleUnderlyingSheaf Mi)
  rightIso :
    moduleUnderlyingSheaf right ≅
      (sheafMapRestriction (AddCommGrpCat.{v})
        (show U i ⊓ U j ≤ U j from inf_le_right)).obj
          (moduleUnderlyingSheaf Mj)
  map : left ≅ right
  comm :
    leftIso.hom ≫ τ.hom =
      moduleUnderlyingSheafMorphism map.hom ≫
        rightIso.hom

/-- Glueing data for sheaves of modules over a fixed sheaf of rings. -/
structure OModuleGlueingData (O : RingSheaf.{v, v} X) (U : ι → Opens X) where
  module : ∀ i, Mod (restrictedRingSheaf O (U i))
  transition : ∀ i j,
    (sheafMapRestriction (AddCommGrpCat.{v})
      (show U i ⊓ U j ≤ U i from inf_le_left)).obj
        (moduleUnderlyingSheaf (module i)) ≅
      (sheafMapRestriction (AddCommGrpCat.{v})
        (show U i ⊓ U j ≤ U j from inf_le_right)).obj
        (moduleUnderlyingSheaf (module j))
  transition_is_module : ∀ i j,
    OModuleGlueingTransition (module i) (module j) (transition i j)
  cocycle : ∀ i j k,
    glueingTransitionAt (AddCommGrpCat.{v}) U
        (fun i => moduleUnderlyingSheaf (module i)) transition
        i j ((U i ⊓ U j) ⊓ U k)
        (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left) ≫
      glueingTransitionAt (AddCommGrpCat.{v}) U
        (fun i => moduleUnderlyingSheaf (module i)) transition
        j k ((U i ⊓ U j) ⊓ U k)
        (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right) =
    glueingTransitionAt (AddCommGrpCat.{v}) U
        (fun i => moduleUnderlyingSheaf (module i)) transition
        i k ((U i ⊓ U j) ⊓ U k)
        (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
          le_inf (inf_le_left.trans inf_le_left) inf_le_right)

/-- The additive sheaf glueing datum underlying module glueing data. -/
def OModuleGlueingData.underlying
    {O : RingSheaf.{v, v} X} {U : ι → Opens X}
    (D : OModuleGlueingData O U) : SheafGlueingData (AddCommGrpCat.{v}) U where
  sheaf i := moduleUnderlyingSheaf (D.module i)
  transition := D.transition
  cocycle := D.cocycle

/-- A sheaf of `O`-modules realizing module glueing data. -/
structure OModuleGlueingSolution {O : RingSheaf.{v, v} X}
    {U : ι → Opens X} (D : OModuleGlueingData O U) where
  sheaf : Mod O
  iso : ∀ i,
    (sheafRestriction (AddCommGrpCat.{v}) (U i)).obj
        (moduleUnderlyingSheaf sheaf) ≅
      moduleUnderlyingSheaf (D.module i)
  comm : ∀ i j,
    (sheafRestrictionRestrictionIso (AddCommGrpCat.{v})
        (show U i ⊓ U j ≤ U i from inf_le_left)
        (moduleUnderlyingSheaf sheaf)).inv ≫
        (sheafMapRestriction (AddCommGrpCat.{v})
          (show U i ⊓ U j ≤ U i from inf_le_left)).map (iso i).hom ≫
        (D.transition i j).hom =
      (sheafRestrictionRestrictionIso (AddCommGrpCat.{v})
        (show U i ⊓ U j ≤ U j from inf_le_right)
        (moduleUnderlyingSheaf sheaf)).inv ≫
        (sheafMapRestriction (AddCommGrpCat.{v})
          (show U i ⊓ U j ≤ U j from inf_le_right)).map (iso j).hom

/-- Sheaf glueing preserves sheaves of modules over a fixed sheaf of rings. -/
theorem exists_omoduleGlueingSolution
    {O : RingSheaf.{v, v} X} {U : ι → Opens X}
    (hU : TopologicalSpace.IsOpenCover U) (D : OModuleGlueingData O U) :
    Nonempty (OModuleGlueingSolution D) := by
  sorry

/-- The source-facing existence statement for gluing sheaves of modules over
   a fixed sheaf of rings. -/
theorem glue_omodule_sheaves
    {O : RingSheaf.{v, v} X} {U : ι → Opens X}
    (hU : TopologicalSpace.IsOpenCover U) (D : OModuleGlueingData O U) :
    Nonempty (OModuleGlueingSolution D) :=
  exists_omoduleGlueingSolution hU D

/-- Glueing data for sheaves valued in any of Mathlib's concrete algebraic
categories satisfying the standard pullback hypotheses. -/
abbrev AlgebraicSheafGlueingData (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    (U : ι → Opens X) :=
  SheafGlueingData C U

/-- The source's existence lemma for sheaves of sets. -/
theorem glueingSectionPresheaf_isSheaf
    (hU : TopologicalSpace.IsOpenCover U) (D : SetSheafGlueingData U) :
    TopCat.Presheaf.IsSheaf (glueingSectionPresheaf D) := by
  sorry

/-- The explicit sheaf from the compatible-family construction. -/
noncomputable def glueingSectionSheaf
    (hU : TopologicalSpace.IsOpenCover U) (D : SetSheafGlueingData U) :
    Sh.{v, v} X :=
  ⟨glueingSectionPresheaf D, glueingSectionPresheaf_isSheaf hU D⟩

/-- The explicit compatible-family sheaf carries the local isomorphisms and
commuting intersection squares required by the abstract glueing solution. -/
theorem glueingSectionSheaf_solution
    (hU : TopologicalSpace.IsOpenCover U) (D : SetSheafGlueingData U) :
    Nonempty {S : SheafGlueingSolution D //
      S.sheaf = glueingSectionSheaf hU D} := by
  sorry

@[simp]
theorem glueingSectionSheaf_sections
    (hU : TopologicalSpace.IsOpenCover U) (D : SetSheafGlueingData U)
    (W : Opens X) :
    (glueingSectionSheaf hU D).presheaf.obj (op W) = GlueingSection D W := rfl

/-- The chosen explicit sections are the sectionwise construction used by the
source's first proof of the glueing lemma. -/
theorem glue_sheaves
    (hU : TopologicalSpace.IsOpenCover U) (D : SetSheafGlueingData U) :
    Nonempty (SheafGlueingSolution D) :=
  exists_sheafGlueingSolution hU D

/-- The same construction preserves a concrete algebraic sheaf structure. -/
theorem glue_sheaves_structures
    {C : Type u} [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    (hU : TopologicalSpace.IsOpenCover U)
    (D : SheafGlueingData C U) :
    Nonempty (SheafGlueingSolution D) :=
  exists_sheafGlueingSolution hU D

/-- In particular, glueing data of abelian sheaves glue in `AddCommGrpCat`. -/
theorem glue_abelian_sheaves
    (hU : TopologicalSpace.IsOpenCover U) (D : AbelianSheafGlueingData U) :
    Nonempty (SheafGlueingSolution (C := AddCommGrpCat.{v}) D) :=
  exists_sheafGlueingSolution (C := AddCommGrpCat.{v}) hU D

end StructureVariants

/-! ## The mapping-property equivalence -/

section MappingProperty

variable {C : Type u} [Category.{v} C]
  {FC : C → C → Type*} {CC : C → Type v}
  [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
  [HasColimits C] [HasLimits C]
  [PreservesLimits (CategoryTheory.forget C)]
  [PreservesFilteredColimits (CategoryTheory.forget C)]
  [(CategoryTheory.forget C).ReflectsIsomorphisms]
  {X : TopCat.{v}} {ι : Type v} {U : ι → Opens X}

/-- A morphism of ambient sheaves induces a morphism of their canonical local
glueing data. -/
theorem canonicalSheafGlueingHom_comm
    {F G : TopCat.Sheaf C X} (f : F ⟶ G) (i j : ι) :
    (sheafMapRestriction C (show U i ⊓ U j ≤ U i from inf_le_left)).map
          ((sheafRestriction C (U i)).map f) ≫
        ((canonicalSheafGlueingData (U := U) G).transition i j).hom =
      (canonicalSheafGlueingTransition (U := U) F i j).hom ≫
        (sheafMapRestriction C (show U i ⊓ U j ≤ U j from inf_le_right)).map
          ((sheafRestriction C (U j)).map f) := by
  sorry

/-- The functor sending a sheaf to its local restrictions and transition maps. -/
noncomputable def sheafToGlueingData :
    TopCat.Sheaf C X ⥤ SheafGlueingData C U where
  obj F := canonicalSheafGlueingData (U := U) F
  map f :=
    { app := fun i => (sheafRestriction C (U i)).map f
      comm := canonicalSheafGlueingHom_comm (U := U) f }
  map_id := by
    intro F
    apply SheafGlueingData.Hom.ext
    funext i
    change (sheafRestriction C (U i)).map (𝟙 F) = 𝟙 _
    rw [(sheafRestriction C (U i)).map_id]
  map_comp f g := by
    apply SheafGlueingData.Hom.ext
    funext i
    change (sheafRestriction C (U i)).map (f ≫ g) =
      (sheafRestriction C (U i)).map f ≫
        (sheafRestriction C (U i)).map g
    exact (sheafRestriction C (U i)).map_comp f g

/-- The mapping-property form of the glueing lemma: restriction to a cover is
an equivalence between ambient sheaves and glueing data. -/
theorem sheafToGlueingData_isEquivalence
    (hU : TopologicalSpace.IsOpenCover U) :
    (sheafToGlueingData (C := C) (U := U)).IsEquivalence := by
  sorry

/-- A categorical equivalence realizing the mapping-property lemma. -/
noncomputable def sheafGlueingEquivalence
    (hU : TopologicalSpace.IsOpenCover U) :
    TopCat.Sheaf C X ≌ SheafGlueingData C U := by
  letI : (sheafToGlueingData (C := C) (U := U)).IsEquivalence :=
    sheafToGlueingData_isEquivalence (C := C) (U := U) hU
  exact (sheafToGlueingData (C := C) (U := U)).asEquivalence

/-! The source's categorical statement for sheaves of sets. -/

/-- The functor sending a sheaf of sets to its local glueing datum. -/
noncomputable def setSheafToGlueingData {X : TopCat.{v}} {ι : Type v}
    (U : ι → Opens X) :
    Sh.{v, v} X ⥤ SetSheafGlueingData U :=
  sheafToGlueingData (C := Type v) (U := U)

/-- Restriction to an open cover is an equivalence with set-valued glueing
data. -/
theorem setSheafToGlueingData_isEquivalence {X : TopCat.{v}} {ι : Type v}
    (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    (setSheafToGlueingData U).IsEquivalence := by
  exact sheafToGlueingData_isEquivalence (C := Type v) (U := U) hU

/-- A categorical equivalence between sheaves of sets and glueing data. -/
noncomputable def setSheafGlueingEquivalence {X : TopCat.{v}} {ι : Type v}
    (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    Sh.{v, v} X ≌ SetSheafGlueingData U := by
  letI : (setSheafToGlueingData U).IsEquivalence :=
    setSheafToGlueingData_isEquivalence U hU
  exact (setSheafToGlueingData U).asEquivalence

/-- Local descriptions of maps from a glued sheaf to an ambient sheaf. -/
abbrev GlueingMapToAmbient (D : SheafGlueingData C U)
    (G : TopCat.Sheaf C X) :=
  SheafGlueingData.Hom D (canonicalSheafGlueingData (U := U) G)

/-- Local descriptions of maps from an ambient sheaf to a glued sheaf. -/
abbrev GlueingMapFromAmbient (D : SheafGlueingData C U)
    (G : TopCat.Sheaf C X) :=
  SheafGlueingData.Hom (canonicalSheafGlueingData (U := U) G) D

/-- Maps out of the glued sheaf are exactly compatible local maps out of the
members of the glueing datum. -/
theorem gluedSheaf_hom_equiv_toAmbient_exists
    (hU : TopologicalSpace.IsOpenCover U) (D : SheafGlueingData C U)
    (G : TopCat.Sheaf C X) :
    Nonempty ((gluedSheaf hU D ⟶ G) ≃ GlueingMapToAmbient D G) := by
  sorry

/-- Maps into the glued sheaf are exactly compatible local maps into the
members of the glueing datum. -/
theorem gluedSheaf_hom_equiv_fromAmbient_exists
    (hU : TopologicalSpace.IsOpenCover U) (D : SheafGlueingData C U)
    (G : TopCat.Sheaf C X) :
    Nonempty ((G ⟶ gluedSheaf hU D) ≃ GlueingMapFromAmbient D G) := by
  sorry

/-- Chosen versions of the two local-to-global mapping equivalences. -/
noncomputable def gluedSheaf_hom_equiv_toAmbient
    (hU : TopologicalSpace.IsOpenCover U) (D : SheafGlueingData C U)
    (G : TopCat.Sheaf C X) :
    (gluedSheaf hU D ⟶ G) ≃ GlueingMapToAmbient D G :=
  Classical.choice (gluedSheaf_hom_equiv_toAmbient_exists hU D G)

noncomputable def gluedSheaf_hom_equiv_fromAmbient
    (hU : TopologicalSpace.IsOpenCover U) (D : SheafGlueingData C U)
    (G : TopCat.Sheaf C X) :
    (G ⟶ gluedSheaf hU D) ≃ GlueingMapFromAmbient D G :=
  Classical.choice (gluedSheaf_hom_equiv_fromAmbient_exists hU D G)

end MappingProperty

end

end Formalization.Books.Sheaves.Unit33
