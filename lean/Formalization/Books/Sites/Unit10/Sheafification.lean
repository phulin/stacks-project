import Formalization.Books.Sites.Unit08.Refinements
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Sites and Sheaves, Chapter 10: Sheafification

The source section `Sheafification` is formalized with Mathlib's canonical
cover posets, compatible-family (`Meq`) construction, plus construction, and
sheafification API.  A cover in this file is a covering sieve, which is the
canonical quotient of the source's indexed covering families; its order is the
refinement order.
-/

namespace Formalization.Books.Sites.Unit10

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presieve
open Formalization.Books.Sites.Unit02
open Formalization.Books.Sites.Unit06
open Formalization.Books.Sites.Unit07
open Formalization.Books.Sites.Unit08
open Opposite

universe u v w w' u' v'

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-! ## Čech zero-cohomology and refinements -/

variable (J : Site C)

/-- The category of covering objects of `U`, with morphisms given by
refinements.  This is Mathlib's canonical cover poset. -/
abbrev CoveringCategory (U : C) := J.toGrothendieck.Cover U

/-- The zeroth Čech cohomology set of a presheaf on a chosen cover.

`Meq` is the canonical compatible-family/equalizer construction. -/
abbrev CechH0 (F : Cᵒᵖ ⥤ Type w) {U : C} (S : CoveringCategory J U) :=
  CategoryTheory.Meq F S

/-- The canonical map from sections over `U` to compatible sections on a
covering `S`. -/
noncomputable def cechRestrictionMap (F : Cᵒᵖ ⥤ Type w) {U : C}
    (S : CoveringCategory J U) : F.obj (op U) → CechH0 J F S :=
  fun s => CategoryTheory.Meq.mk (P := F) S s

/-- Pullback of a compatible family along a morphism of the site. -/
noncomputable def cechPullback {U V : C} (f : V ⟶ U) {S : CoveringCategory J U}
    (x : CechH0 J F S) : CechH0 J F (S.pullback f) :=
  CategoryTheory.Meq.pullback x f

/-- Restriction of a compatible family along a refinement. -/
noncomputable def cechRefinementMap {U : C} {S T : CoveringCategory J U}
    (e : S ⟶ T) : CechH0 J F T → CechH0 J F S :=
  fun x => CategoryTheory.Meq.refine x e

theorem cechRefinementMap_independent (F : Cᵒᵖ ⥤ Type w)
    {U : C} {S T : CoveringCategory J U}
    (e e' : S ⟶ T) :
    cechRefinementMap (F := F) (J := J) e =
      cechRefinementMap (F := F) (J := J) e' := by
  sorry

theorem cechH0_equiv_of_mutual_refinement {U : C}
    {S T : CoveringCategory J U} (e : S ⟶ T) (e' : T ⟶ S) :
    Nonempty (CechH0 J F S ≃ CechH0 J F T) := by
  sorry

/-- Pullback and restriction maps are the maps induced by the commutative
diagrams of covering families in the source. -/
theorem cechPullback_id {U : C} {S : CoveringCategory J U}
    (x : CechH0 J F S) :
    cechPullback J (𝟙 U) x =
      CategoryTheory.Meq.refine x (S.pullbackId.hom) := by
  sorry

theorem cechPullback_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {S : CoveringCategory J U} (x : CechH0 J F S) :
    cechPullback J g (cechPullback J f x) =
      CategoryTheory.Meq.refine (cechPullback J (g ≫ f) x)
        (S.pullbackComp g f).inv := by
  sorry

/-- The source's equalizer characterization of the sheaf condition. -/
theorem isSheaf_iff_cechRestrictionMap_bijective (F : Cᵒᵖ ⥤ Type w) :
    CategoryTheory.Presheaf.IsSheaf J.toGrothendieck F ↔
      ∀ (U : C) (S : CoveringCategory J U),
        Function.Bijective (cechRestrictionMap J F S) := by
  sorry

/-- The cover poset is nonempty, since the maximal cover is available. -/
theorem coveringCategory_nonempty (U : C) : Nonempty (CoveringCategory J U) :=
  ⟨⊤⟩

/-- Two covers have a common refinement, represented by their intersection. -/
def commonRefinement {U : C} (S T : CoveringCategory J U) : CoveringCategory J U :=
  S ⊓ T

def commonRefinement_refines_left {U : C} (S T : CoveringCategory J U) :
    commonRefinement (J := J) S T ⟶ S :=
  homOfLE inf_le_left

def commonRefinement_refines_right {U : C} (S T : CoveringCategory J U) :
    commonRefinement (J := J) S T ⟶ T :=
  homOfLE inf_le_right

/-! ## The plus construction -/

/- The following are the universe-sized limit and colimit instances used by
Mathlib's canonical plus construction.  They are automatic for the usual
choice `w = max u v`, but are kept explicit so the declarations also work for
any universe in which the chosen category of sets has these colimits. -/
variable [∀ (P : Cᵒᵖ ⥤ Type w) (X : C)
  (S : J.toGrothendieck.Cover X), HasMultiequalizer (S.index P)]
variable [∀ X : C, HasColimitsOfShape (J.toGrothendieck.Cover X)ᵒᵖ (Type w)]

/-- The value of the plus construction over `U`, as the colimit over the
opposite of the cover/refinement category. -/
noncomputable def plusValue (F : Cᵒᵖ ⥤ Type w) (U : C) : Type w :=
  colimit (J.toGrothendieck.diagram F U)

/-- The plus presheaf, reusing Mathlib's functorial construction. -/
noncomputable def plusPresheaf (F : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w :=
  J.toGrothendieck.plusObj F

theorem plusValue_eq_obj (F : Cᵒᵖ ⥤ Type w) (U : C) :
    plusValue (J := J) F U = (plusPresheaf (J := J) F).obj (op U) := rfl

/-- The canonical map from a presheaf to its plus construction. -/
noncomputable def plusUnit (F : Cᵒᵖ ⥤ Type w) : F ⟶ plusPresheaf J F :=
  J.toGrothendieck.toPlus F

/-- The map on plus constructions induced by a morphism of presheaves. -/
noncomputable def plusMap {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) :
    plusPresheaf J F ⟶ plusPresheaf J G :=
  J.toGrothendieck.plusMap η

theorem plusMap_id (F : Cᵒᵖ ⥤ Type w) : plusMap J (𝟙 F) = 𝟙 _ := by
  exact J.toGrothendieck.plusMap_id F

theorem plusMap_comp {F G H : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) (θ : G ⟶ H) :
    plusMap J (η ≫ θ) = plusMap J η ≫ plusMap J θ := by
  exact J.toGrothendieck.plusMap_comp η θ

theorem plusUnit_naturality {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) :
    η ≫ plusUnit J G = plusUnit J F ≫ plusMap J η := by
  exact J.toGrothendieck.toPlus_naturality η

theorem plus_restriction_of_representative (F : Cᵒᵖ ⥤ Type w)
    {U V : C} (f : V ⟶ U) {S : CoveringCategory J U}
    (x : CechH0 J F S) :
    (plusPresheaf J F).map f.op
        (GrothendieckTopology.Plus.mk x) =
      GrothendieckTopology.Plus.mk (cechPullback J f x) := by
  sorry

/-- The plus construction is functorial in the presheaf. -/
noncomputable def plusFunctor :
    (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w) :=
  J.toGrothendieck.plusFunctor (Type w)

/-- A local section of `F⁺` is represented by compatible sections on a cover.
This is the source's local-surjectivity statement in the canonical cover API. -/
theorem plus_sections_locally_from_original (F : Cᵒᵖ ⥤ Type w) {U : C}
    (s : (plusPresheaf J F).obj (op U)) :
    ∃ (S : CoveringCategory J U) (x : CechH0 J F S),
      ∀ I : S.Arrow,
        (plusPresheaf J F).map I.f.op s =
          (plusUnit J F).app (op I.Y) (x I) := by
  sorry

/-- The source's separatedness condition, expressed through Mathlib's
canonical topology-level predicate. -/
abbrev IsSeparated (F : Cᵒᵖ ⥤ Type w) : Prop :=
  Presieve.IsSeparated J.toGrothendieck F

theorem plus_isSeparated (F : Cᵒᵖ ⥤ Type w) :
    IsSeparated J (plusPresheaf J F) := by
  sorry

theorem plus_isSheaf_of_isSeparated (F : Cᵒᵖ ⥤ Type w)
    (hF : IsSeparated J F) :
    CategoryTheory.Presheaf.IsSheaf J.toGrothendieck (plusPresheaf J F) := by
  sorry

theorem plusUnit_pointwise_injective (F : Cᵒᵖ ⥤ Type w)
    (hF : IsSeparated J F) :
    ∀ U : C, Function.Injective ((plusUnit J F).app (op U)) := by
  sorry

theorem plusUnit_isIso_of_isSheaf (F : Cᵒᵖ ⥤ Type w)
    (hF : CategoryTheory.Presheaf.IsSheaf J.toGrothendieck F) :
    IsIso (plusUnit J F) := by
  exact J.toGrothendieck.isIso_toPlus_of_isSheaf F hF

theorem plus_preserves_finite_limits :
    PreservesFiniteLimits (plusFunctor J) := by
  sorry

/-- If `F` is already a sheaf, the canonical map to `F⁺` is an isomorphism. -/
noncomputable def plusIsoOfSheaf (F : Cᵒᵖ ⥤ Type w)
    (hF : CategoryTheory.Presheaf.IsSheaf J.toGrothendieck F) :
    F ≅ plusPresheaf J F :=
  J.toGrothendieck.isoToPlus F hF

/-! ## Associated sheaf and its universal property -/

/-- The associated sheaf `F# = F⁺⁺`. -/
noncomputable def associatedSheafPresheaf (F : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w :=
  J.toGrothendieck.sheafify F

/-- The canonical map `F → F#`. -/
noncomputable def associatedSheafUnit (F : Cᵒᵖ ⥤ Type w) :
    F ⟶ associatedSheafPresheaf J F :=
  J.toGrothendieck.toSheafify F

/-- The map on associated sheaves induced by a map of presheaves. -/
noncomputable def associatedSheafMap {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) :
    associatedSheafPresheaf J F ⟶ associatedSheafPresheaf J G :=
  J.toGrothendieck.sheafifyMap η

theorem associatedSheafMap_id (F : Cᵒᵖ ⥤ Type w) :
    associatedSheafMap J (𝟙 F) = 𝟙 _ := by
  exact J.toGrothendieck.sheafifyMap_id F

theorem associatedSheafMap_comp {F G H : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) (θ : G ⟶ H) :
    associatedSheafMap J (η ≫ θ) =
      associatedSheafMap J η ≫ associatedSheafMap J θ := by
  exact J.toGrothendieck.sheafifyMap_comp η θ

theorem associatedSheafUnit_naturality {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) :
    η ≫ associatedSheafUnit J G =
      associatedSheafUnit J F ≫ associatedSheafMap J η := by
  exact J.toGrothendieck.toSheafify_naturality η

/-- The double-plus construction is a sheaf. -/
theorem associatedSheaf_isSheaf (F : Cᵒᵖ ⥤ Type w) :
    CategoryTheory.Presheaf.IsSheaf J.toGrothendieck
      (associatedSheafPresheaf J F) := by
  exact J.toGrothendieck.sheafify_isSheaf F

/-- The sheafification functor, with values in the full sheaf category. -/
noncomputable def associatedSheafFunctor :
    (Cᵒᵖ ⥤ Type w) ⥤ Sheaf J.toGrothendieck (Type w) :=
  plusPlusSheaf J.toGrothendieck (Type w)

noncomputable def associatedSheafAdjunction :
    associatedSheafFunctor J ⊣
      sheafToPresheaf J.toGrothendieck (Type w) :=
  plusPlusAdjunction J.toGrothendieck (Type w)

/-- The universal map from `F#` to a sheaf receiving a map from `F`. -/
noncomputable def associatedSheafLift {F G : Cᵒᵖ ⥤ Type w}
    (η : F ⟶ G) (hG : CategoryTheory.Presheaf.IsSheaf J.toGrothendieck G) :
    associatedSheafPresheaf J F ⟶ G :=
  J.toGrothendieck.sheafifyLift η hG

theorem associatedSheafUnit_lift {F G : Cᵒᵖ ⥤ Type w}
    (η : F ⟶ G) (hG : CategoryTheory.Presheaf.IsSheaf J.toGrothendieck G) :
    associatedSheafUnit J F ≫ associatedSheafLift J η hG = η := by
  exact J.toGrothendieck.toSheafify_sheafifyLift η hG

theorem associatedSheafLift_unique {F G : Cᵒᵖ ⥤ Type w}
    (η : F ⟶ G) (hG : CategoryTheory.Presheaf.IsSheaf J.toGrothendieck G)
    (γ : associatedSheafPresheaf J F ⟶ G)
    (hγ : associatedSheafUnit J F ≫ γ = η) :
    γ = associatedSheafLift J η hG := by
  exact J.toGrothendieck.sheafifyLift_unique η hG γ hγ

/-! ## Examples and limits/colimits -/

/-- The terminal sheaf of sets, whose underlying presheaf is constantly a
singleton. -/
noncomputable def singletonSheaf : Sheaf J.toGrothendieck (Type w) :=
  Sheaf.terminal J.toGrothendieck
    (CategoryTheory.Limits.Types.isTerminalPUnit : IsTerminal (PUnit : Type w))

noncomputable def singletonSheaf_isTerminal :
    IsTerminal (singletonSheaf J : Sheaf J.toGrothendieck (Type w)) := by
  exact Sheaf.isTerminalTerminal J.toGrothendieck
    (CategoryTheory.Limits.Types.isTerminalPUnit : IsTerminal (PUnit : Type w))

omit [∀ (P : Cᵒᵖ ⥤ Type w) (X : C)
  (S : J.toGrothendieck.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.toGrothendieck.Cover X)ᵒᵖ (Type w)] in
theorem limit_sheaves_exists {I : Type u'} [Category.{v'} I] [SmallCategory I]
    (F : I ⥤ Sheaf J.toGrothendieck (Type w))
    [HasLimitsOfShape I (Type w)] : HasLimit F := by
  infer_instance

noncomputable def limit_sheaves_underlying_isLimit {I : Type u'} [Category.{v'} I] [SmallCategory I]
    (F : I ⥤ Sheaf J.toGrothendieck (Type w))
    [HasLimitsOfShape I (Type w)] :
    IsLimit ((sheafToPresheaf J.toGrothendieck (Type w)).mapCone (limit.cone F)) := by
  exact isLimitOfPreserves (sheafToPresheaf J.toGrothendieck (Type w))
    (limit.isLimit F)

/-- The constant presheaf with value `E`. -/
def constantPresheaf (E : Type w) : Cᵒᵖ ⥤ Type w :=
  (Functor.const Cᵒᵖ).obj E

/-- The constant sheaf is the associated sheaf of the constant presheaf. -/
noncomputable def constantSheaf (E : Type w) :
    Sheaf J.toGrothendieck (Type w) :=
  (associatedSheafFunctor J).obj (constantPresheaf (C := C) E)

noncomputable def constantSheaf_hom_equiv (E : Type w)
    (G : Sheaf J.toGrothendieck (Type w)) :
    (constantSheaf J E ⟶ G) ≃
      (constantPresheaf (C := C) E ⟶ G.obj) := by
  simpa [constantSheaf, associatedSheafFunctor] using
    (plusPlusAdjunction J.toGrothendieck (Type w)).homEquiv
      (constantPresheaf (C := C) E) G

/-- Colimits of sheaves are obtained by sheafifying the corresponding
presheaf colimits. -/
theorem colimit_sheaves_exists {I : Type u'} [Category.{v'} I] [SmallCategory I]
    (F : I ⥤ Sheaf J.toGrothendieck (Type w))
    [HasColimitsOfShape I (Type w)] : HasColimit F := by
  infer_instance

noncomputable def colimit_sheaves_is_sheafification {I : Type u'} [Category.{v'} I] [SmallCategory I]
    (F : I ⥤ Sheaf J.toGrothendieck (Type w))
    [HasColimitsOfShape I (Type w)] :
    IsColimit (Sheaf.sheafifyCocone (colimit.cocone
      (F ⋙ sheafToPresheaf J.toGrothendieck (Type w)))) := by
  exact Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)

/-- The associated-sheaf functor preserves finite limits. -/
theorem associatedSheaf_preserves_finite_limits :
    PreservesFiniteLimits (associatedSheafFunctor J) := by
  sorry

/-- The associated-sheaf functor preserves finite colimits. -/
theorem associatedSheaf_preserves_finite_colimits :
    PreservesFiniteColimits (associatedSheafFunctor J) := by
  sorry

/-- In the source's terminology, associated sheafification is exact: it
preserves both finite limits and finite colimits. -/
theorem associatedSheaf_exact :
    PreservesFiniteLimits (associatedSheafFunctor J) ∧
      PreservesFiniteColimits (associatedSheafFunctor J) :=
  ⟨associatedSheaf_preserves_finite_limits J,
    associatedSheaf_preserves_finite_colimits J⟩

/-! ## Local descriptions and comparison -/

/-- Pairwise local agreement of sections on a covering, expressed using the
chosen categorical pullbacks. -/
def PairwiseLocallyCompatible (F : Cᵒᵖ ⥤ Type w) {U : C}
    (S : CoveringCategory J U) (s : ∀ I : S.Arrow, F.obj (op I.Y)) : Prop :=
  ∀ I I' : S.Arrow,
    ∃ T : CoveringCategory J (pullback I.f I'.f),
      ∀ K : T.Arrow,
        F.map K.f.op
            (F.map (pullback.fst I.f I'.f).op (s I)) =
          F.map K.f.op
            (F.map (pullback.snd I.f I'.f).op (s I'))

structure SheafificationPresentation (F : Cᵒᵖ ⥤ Type w) {U : C}
    (s : (associatedSheafPresheaf J F).obj (op U)) where
  cover : CoveringCategory J U
  localSection : ∀ I : cover.Arrow, F.obj (op I.Y)
  restrict_eq : ∀ I : cover.Arrow,
    (associatedSheafPresheaf J F).map I.f.op s =
      (associatedSheafUnit J F).app (op I.Y) (localSection I)
  locally_compatible : PairwiseLocallyCompatible J F cover localSection

theorem exists_sheafificationPresentation (F : Cᵒᵖ ⥤ Type w) {U : C}
    (s : (associatedSheafPresheaf J F).obj (op U)) :
    Nonempty (SheafificationPresentation J F s) := by
  sorry

theorem unique_sheafification_section (F : Cᵒᵖ ⥤ Type w) {U : C}
    (S : CoveringCategory J U)
    (s : ∀ I : S.Arrow, F.obj (op I.Y))
    (hs : PairwiseLocallyCompatible J F S s) :
    ∃! t : (associatedSheafPresheaf J F).obj (op U),
      ∀ I : S.Arrow,
        (associatedSheafPresheaf J F).map I.f.op t =
          (associatedSheafUnit J F).app (op I.Y) (s I) := by
  sorry

/-- The objects on which a presheaf map is pointwise bijective. -/
def BijectiveObjects {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) : Set C :=
  {U | Function.Bijective (η.app (op U))}

/-- Every object is covered by objects on which a map is bijective. -/
def LocallyBijective {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) : Prop :=
  ∀ U : C, ∃ S : CoveringCategory J U,
    ∀ I : S.Arrow, I.Y ∈ BijectiveObjects η

theorem associatedSheafMap_isIso_of_locallyBijective
    {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G)
    (hη : LocallyBijective J η) :
    IsIso (associatedSheafMap J η) := by
  sorry

end Formalization.Books.Sites.Unit10
