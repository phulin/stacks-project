import Formalization.Books.Sites.Unit02.Presheaves
import Formalization.Books.Categories.Unit19.FilteredColimits
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Sites and Sheaves, Chapter 5: Functoriality of categories of presheaves

The source section constructs restriction along a functor and its left
adjoint.  The restriction is Mathlib's whiskering functor.  Its left adjoint
is Mathlib's functorial left Kan extension; the pointwise colimit description
is exposed below using the structured-arrow/costructured-arrow equivalence.

The source uses `Sets` and suppresses size hypotheses.  The set-valued
declarations below use one common morphism universe for the two small
categories, while the value-category version records the value category's
universe explicitly.  The assumptions saying that the relevant colimits
exist are expressed by Mathlib's pointwise left Kan extension interface.
-/

namespace Formalization.Books.Sites.Unit05

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Sites.Unit02
open Opposite

universe u u' a v v' w w'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v} D]

/-! ## Restriction of presheaves -/

/-- The pullback `u^p`, implemented by precomposition with `u.op`. -/
noncomputable def pullbackPresheafFunctor (u : C ⥤ D) : PSh D ⥤ PSh C :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj u.op

/-- The pullback of an individual presheaf. -/
noncomputable def pullbackPresheaf (u : C ⥤ D) (G : PSh D) : PSh C :=
  (pullbackPresheafFunctor u).obj G

/-- Precomposition preserves limits of every shape for which `Type v` has them. -/
theorem pullbackPresheaf_preserves_limits_of_shape
    {J : Type w} [Category.{w'} J] [HasLimitsOfShape J (Type v)]
    (u : C ⥤ D) :
    PreservesLimitsOfShape J (pullbackPresheafFunctor u) := by
  change PreservesLimitsOfShape J
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj u.op)
  infer_instance

/-- Precomposition preserves colimits of every shape for which `Type v` has them. -/
theorem pullbackPresheaf_preserves_colimits_of_shape
    {J : Type w} [Category.{w'} J] [HasColimitsOfShape J (Type v)]
    (u : C ⥤ D) :
    PreservesColimitsOfShape J (pullbackPresheafFunctor u) := by
  change PreservesColimitsOfShape J
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj u.op)
  infer_instance

/-! ## The index categories -/

/-- The category whose objects are arrows `V ⟶ u.obj U`.

Its morphisms are exactly the arrows `f : U ⟶ U'` satisfying
`φ ≫ u.map f = φ'`, as in the source.  This is Mathlib's canonical
`StructuredArrow` category.
-/
abbrev indexCategory (u : C ⥤ D) (V : D) := StructuredArrow V u

/-- The structured-arrow object associated to `φ : V ⟶ u.obj U`. -/
def indexObject (u : C ⥤ D) (V : D) (U : C) (φ : V ⟶ u.obj U) :
    indexCategory u V :=
  StructuredArrow.mk φ

/-- The compatibility equation carried by every morphism of `indexCategory`. -/
theorem indexMorphism_condition (u : C ⥤ D) (V : D)
    {X Y : indexCategory u V} (f : X ⟶ Y) :
    X.hom ≫ u.map f.right = Y.hom :=
  StructuredArrow.w f

/-- A morphism `V' ⟶ V` induces the source's functor `I_V ⥤ I_V'`. -/
def indexRestriction {V' V : D} (u : C ⥤ D) (g : V' ⟶ V) :
    indexCategory u V ⥤ indexCategory u V' :=
  StructuredArrow.map g

@[simp]
theorem indexRestriction_obj (u : C ⥤ D) {V' V : D} (g : V' ⟶ V)
    (U : C) (φ : V ⟶ u.obj U) :
    (indexRestriction u g).obj (indexObject u V U φ) =
      indexObject u V' U (g ≫ φ) :=
  rfl

/-- The identity and composition laws for the induced index functors. -/
@[simp]
theorem indexRestriction_id (u : C ⥤ D) (V : D) :
    indexRestriction u (𝟙 V) = 𝟭 (indexCategory u V) := by
  change StructuredArrow.map (𝟙 V) = 𝟭 (indexCategory u V)
  exact CategoryTheory.Functor.ext (fun ⟨_, _, _⟩ => by simp)

theorem indexRestriction_comp (u : C ⥤ D) {V₀ V₁ V₂ : D}
    (g : V₀ ⟶ V₁) (h : V₁ ⟶ V₂) :
    indexRestriction u (g ≫ h) =
      indexRestriction u h ⋙ indexRestriction u g := by
  change StructuredArrow.map (g ≫ h) =
    StructuredArrow.map h ⋙ StructuredArrow.map g
  exact CategoryTheory.Functor.ext (fun ⟨_, _, _⟩ => by simp)

/-! ## The diagrams indexed by `I_V` -/

/-- The set-valued diagram `F_V : I_Vᵒᵖ ⥤ Sets`. -/
def indexPresheaf (u : C ⥤ D) (F : Presheaf C) (V : D) :
    (indexCategory u V)ᵒᵖ ⥤ Type v :=
  (StructuredArrow.proj V u).op ⋙ F

@[simp]
theorem indexPresheaf_obj (u : C ⥤ D) (F : Presheaf C) (V : D)
    (X : indexCategory u V) :
    (indexPresheaf u F V).obj (op X) = F.obj (op X.right) :=
  rfl

/-- Pulling `F_V'` back along the index functor induced by `g : V' ⟶ V`
gives `F_V`. -/
theorem indexPresheaf_restrict {V' V : D} (u : C ⥤ D) (F : Presheaf C)
    (g : V' ⟶ V) :
    (indexRestriction u g).op ⋙ indexPresheaf u F V' = indexPresheaf u F V := by
  rfl

/-! ## The pointwise colimit presentation -/

/-- The canonical costructured-arrow index for the pointwise left Kan
extension of `F` along `u.op` at `op V`. -/
abbrev kanIndexCategory (u : C ⥤ D) (V : D) :=
  CostructuredArrow u.op (op V)

/-- The canonical pointwise left Kan extension diagram. -/
abbrev kanIndexDiagram (u : C ⥤ D) (F : Presheaf C) (V : D) :=
  CostructuredArrow.proj u.op (op V) ⋙ F

/-- The source index category, after taking opposites, is canonically the
costructured-arrow index used by Mathlib's pointwise Kan extension. -/
def indexCostructuredEquivalence (u : C ⥤ D) (V : D) :
    (indexCategory u V)ᵒᵖ ≌ kanIndexCategory u V :=
  structuredArrowOpEquivalence u V

/-- The two presentations of the `F_V` diagram agree under the canonical
index equivalence. -/
theorem indexPresheaf_under_equivalence (u : C ⥤ D) (F : Presheaf C) (V : D) :
    (indexCostructuredEquivalence u V).functor ⋙ kanIndexDiagram u F V =
      indexPresheaf u F V := by
  rfl

/-- The source's size/existence condition that every diagram on an index
category `I_Vᵒᵖ` has a colimit in `Sets`. -/
abbrev HasIndexColimits (u : C ⥤ D) :=
  ∀ (V : D) (K : (indexCategory u V)ᵒᵖ ⥤ Type v), HasColimit K

/-! ## Almost-directedness and filteredness -/

/-- Pullbacks and equalizers in `C`, preserved by `u`, give the two
almost-directedness conditions for `(I_V)ᵒᵖ` from the source's
filtered-components lemma.  These conditions do not assert that the whole
index category is filtered: different connected components are allowed. -/
theorem indexCategory_op_almostDirected (u : C ⥤ D) (V : D)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Formalization.Books.Categories.Unit19.HasCoconesForSpans
        ((indexCategory u V)ᵒᵖ) ∧
      Formalization.Books.Categories.Unit19.HasParallelEqualizers
        ((indexCategory u V)ᵒᵖ) := by
  constructor
  · intro X Y Z a b
    let f := a.unop.right
    let g := b.unop.right
    let p := pullback f g
    let : HasPullback (u.map f) (u.map g) :=
      hasPullback_of_preservesPullback u f g
    let e := PreservesPullback.iso u f g
    let q : V ⟶ pullback (u.map f) (u.map g) :=
      pullback.lift Y.unop.hom Z.unop.hom (by
        rw [indexMorphism_condition u V a.unop,
          indexMorphism_condition u V b.unop])
    let φ : V ⟶ u.obj p := q ≫ e.inv
    let c : indexObject u V p φ ⟶ Y.unop :=
      StructuredArrow.homMk (pullback.fst f g) (by
        change φ ≫ u.map (pullback.fst f g) = Y.unop.hom
        dsimp [φ]
        rw [Category.assoc, PreservesPullback.iso_inv_fst]
        simpa [q] using
          (pullback.lift_fst Y.unop.hom Z.unop.hom _))
    let d : indexObject u V p φ ⟶ Z.unop :=
      StructuredArrow.homMk (pullback.snd f g) (by
        change φ ≫ u.map (pullback.snd f g) = Z.unop.hom
        dsimp [φ]
        rw [Category.assoc, PreservesPullback.iso_inv_snd]
        simpa [q] using
          (pullback.lift_snd Y.unop.hom Z.unop.hom _))
    refine ⟨op (indexObject u V p φ), c.op, d.op, ?_⟩
    apply Quiver.Hom.unop_inj
    apply StructuredArrow.hom_ext
    change pullback.fst f g ≫ f = pullback.snd f g ≫ g
    exact pullback.condition
  · intro X Y a b
    let f := a.unop.right
    let g := b.unop.right
    let e := equalizer f g
    let : HasEqualizer (u.map f) (u.map g) :=
      HasLimit.mk ⟨_, isLimitForkMapOfIsLimit u _ (equalizerIsEqualizer f g)⟩
    let q : V ⟶ equalizer (u.map f) (u.map g) :=
      equalizer.lift Y.unop.hom (by
        rw [indexMorphism_condition u V a.unop,
          indexMorphism_condition u V b.unop])
    let eIso := PreservesEqualizer.iso u f g
    let φ : V ⟶ u.obj e := q ≫ eIso.inv
    let c : indexObject u V e φ ⟶ Y.unop :=
      StructuredArrow.homMk (equalizer.ι f g) (by
        change φ ≫ u.map (equalizer.ι f g) = Y.unop.hom
        dsimp [φ]
        rw [Category.assoc, PreservesEqualizer.iso_inv_ι]
        simp [q])
    refine ⟨op (indexObject u V e φ), c.op, ?_⟩
    apply Quiver.Hom.unop_inj
    apply StructuredArrow.ext
    change equalizer.ι f g ≫ f = equalizer.ι f g ≫ g
    exact equalizer.condition f g

/-- If `C` has a final object carried by `u` to a final object of `D`, then
the same index category is filtered. -/
theorem indexCategory_op_isFiltered (u : C ⥤ D) (V : D) (X : C)
    (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    IsFiltered (indexCategory u V)ᵒᵖ := by
  let : HasTerminal C := hX.hasTerminal
  let : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesLimit (Functor.empty.{0} C) u :=
    preservesLimit_of_preserves_limit_cone hX
      ((isLimitMapConeEmptyConeEquiv u X).symm huX)
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    preservesLimitsOfShape_pempty_of_preservesTerminal u
  let : PreservesFiniteLimits u :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  let t : indexCategory u V := indexObject u V X (huX.from V)
  let hAD := indexCategory_op_almostDirected u V
  let hupper : Formalization.Books.Categories.Unit19.HasCommonUpperBounds
      ((indexCategory u V)ᵒᵖ) := by
    intro x y
    let cX : x.unop ⟶ t :=
      StructuredArrow.homMk (hX.from x.unop.right) (by
        dsimp [t]
        apply huX.hom_ext)
    let cY : y.unop ⟶ t :=
      StructuredArrow.homMk (hX.from y.unop.right) (by
        dsimp [t]
        apply huX.hom_ext)
    obtain ⟨z, c, d, _⟩ := hAD.1 cX.op cY.op
    exact ⟨z, ⟨c⟩, ⟨d⟩⟩
  let : IsFilteredOrEmpty (indexCategory u V)ᵒᵖ :=
    Formalization.Books.Categories.Unit19.isFilteredOrEmpty_of_common_upper_bounds_and_parallel
      hupper hAD.2
  let : Nonempty (indexCategory u V)ᵒᵖ := ⟨op t⟩
  exact IsFiltered.mk

/-! ## The pushforward -/

/-- The existence hypothesis for the functorial left Kan extension along
`u.op`. -/
abbrev HasLeftPushforward (u : C ⥤ D) :=
  ∀ F : Presheaf C, Functor.HasLeftKanExtension u.op F

/-- The stronger pointwise-colimit hypothesis used by the source's explicit
colimit formula. -/
abbrev HasPointwisePushforward (u : C ⥤ D) :=
  ∀ F : Presheaf C, Functor.HasPointwiseLeftKanExtension u.op F

/-- Colimits of all diagrams on the source index categories supply the
pointwise colimits used by the Kan-extension construction. -/
theorem hasPointwisePushforward_of_indexColimits (u : C ⥤ D)
    [HasIndexColimits u] : HasPointwisePushforward u := by
  intro F V
  change HasColimit (kanIndexDiagram u F V.unop)
  let e := indexCostructuredEquivalence u V.unop
  let : HasColimit (e.functor ⋙ kanIndexDiagram u F V.unop) := by
    rw [indexPresheaf_under_equivalence]
    exact inferInstance
  exact hasColimit_of_equivalence_comp e

/-- Pointwise left Kan extensions supply the left Kan extensions needed by
the functorial construction. -/
theorem hasLeftPushforward_of_pointwise (u : C ⥤ D)
    [HasPointwisePushforward u] : HasLeftPushforward u :=
  fun _F => inferInstance

/-- The pushforward `u_p`, represented by Mathlib's functorial left Kan
extension. -/
noncomputable def pushforwardPresheafFunctor (u : C ⥤ D)
    [h : HasLeftPushforward u] : PSh C ⥤ PSh D :=
  Functor.lan u.op

/-- The pushforward of an individual presheaf. -/
noncomputable def pushforwardPresheaf (u : C ⥤ D) (F : Presheaf C)
    [HasLeftPushforward u] : Presheaf D :=
  (pushforwardPresheafFunctor u).obj F

/-- The pointwise colimit formula for the pushforward. -/
noncomputable def pushforwardValueColimitIso (u : C ⥤ D) (F : Presheaf C)
  (V : D) [hLeft : HasLeftPushforward u]
    [hPoint : HasPointwisePushforward u] :
    (pushforwardPresheaf u F).obj (op V) ≅ colimit (kanIndexDiagram u F V) := by
  letI : Functor.HasLeftKanExtension u.op F := hLeft F
  letI : Functor.HasPointwiseLeftKanExtension u.op F := hPoint F
  simpa [pushforwardPresheaf, pushforwardPresheafFunctor] using!
    (u.op.leftKanExtensionObjIsoColimit F (op V))

/-- The canonical map from `F(U)` into the value of the pushforward over
`u.obj U`, corresponding to the source's `c(id)`. -/
noncomputable def recoverMap (u : C ⥤ D) (F : Presheaf C) (U : C)
    [HasLeftPushforward u] :
    F.obj (op U) ⟶ (pushforwardPresheaf u F).obj (op (u.obj U)) :=
  ((u.op.lanUnit.app F).app (op U))

/-- The canonical map from a component `F(U)` into the pointwise colimit. -/
noncomputable def pushforwardCoprojection (u : C ⥤ D) (F : Presheaf C)
    (V : D) (U : C) (φ : V ⟶ u.obj U)
    [hLeft : HasLeftPushforward u] [hPoint : HasPointwisePushforward u] :
    F.obj (op U) ⟶ (pushforwardPresheaf u F).obj (op V) :=
  letI : Functor.HasLeftKanExtension u.op F := hLeft F
  letI : Functor.HasPointwiseLeftKanExtension u.op F := hPoint F
  colimit.ι (kanIndexDiagram u F V) (CostructuredArrow.mk φ.op) ≫
    (pushforwardValueColimitIso u F V).inv

/-- The source's `c(id)` description of `recoverMap`. -/
theorem recoverMap_eq_pushforwardCoprojection (u : C ⥤ D) (F : Presheaf C) (U : C)
    [HasLeftPushforward u] [HasPointwisePushforward u] :
    recoverMap u F U =
      pushforwardCoprojection u F (u.obj U) U (𝟙 (u.obj U)) := by
  let : Functor.HasLeftKanExtension u.op F :=
    (inferInstance : HasLeftPushforward u) F
  let : Functor.HasPointwiseLeftKanExtension u.op F :=
    (inferInstance : HasPointwisePushforward u) F
  have hbase :
      (u.op.leftKanExtensionUnit F).app (op U) =
        colimit.ι (CostructuredArrow.proj u.op (op (u.obj U)) ⋙ F)
            (CostructuredArrow.mk (𝟙 (op (u.obj U)))) ≫
          (u.op.leftKanExtensionObjIsoColimit F (op (u.obj U))).inv := by
    dsimp only [Functor.comp_obj, Functor.op]
    exact (Iso.eq_comp_inv (u.op.leftKanExtensionObjIsoColimit F (op (u.obj U)))).2
      (u.op.leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom F (op U))
  change (u.op.leftKanExtensionUnit F).app (op U) =
    colimit.ι (CostructuredArrow.proj u.op (op (u.obj U)) ⋙ F)
        (CostructuredArrow.mk (𝟙 (op (u.obj U)))) ≫
      (u.op.leftKanExtensionObjIsoColimit F (op (u.obj U))).inv
  exact hbase

/-- The recovery maps are compatible with restriction in `F`. -/
theorem recoverMap_naturality (u : C ⥤ D) (F : Presheaf C)
    {U V : C} (f : V ⟶ U) [HasLeftPushforward u] :
    F.map f.op ≫ recoverMap u F V =
      recoverMap u F U ≫
        (pushforwardPresheaf u F).map (u.map f).op := by
  let : Functor.HasLeftKanExtension u.op F :=
    (inferInstance : HasLeftPushforward u) F
  change F.map f.op ≫ (u.op.lanUnit.app F).app (op V) =
    (u.op.lanUnit.app F).app (op U) ≫
      (u.op ⋙ (pushforwardPresheafFunctor u).obj F).map f.op
  simp [pushforwardPresheafFunctor]

/-- The restriction map on the pushforward induced by `g : V' ⟶ V`. -/
noncomputable def pushforwardRestrictionMap (u : C ⥤ D) (F : Presheaf C)
    {V' V : D} (g : V' ⟶ V) [HasLeftPushforward u] :
    (pushforwardPresheaf u F).obj (op V) ⟶
      (pushforwardPresheaf u F).obj (op V') :=
  (pushforwardPresheaf u F).map g.op

/-- The canonical colimit maps satisfy the square defining the restriction
map on the pushforward. -/
theorem pushforwardCoprojection_naturality (u : C ⥤ D) (F : Presheaf C)
    {V' V : D} (g : V' ⟶ V) (U : C) (φ : V ⟶ u.obj U)
    [HasLeftPushforward u] [HasPointwisePushforward u] :
    pushforwardCoprojection u F V U φ ≫
        pushforwardRestrictionMap u F g =
      pushforwardCoprojection u F V' U (g ≫ φ) := by
  let : Functor.HasLeftKanExtension u.op F :=
    (inferInstance : HasLeftPushforward u) F
  let : Functor.HasPointwiseLeftKanExtension u.op F :=
    (inferInstance : HasPointwisePushforward u) F
  let kV : CostructuredArrow u.op (op V) := CostructuredArrow.mk φ.op
  let kV' : CostructuredArrow u.op (op V') :=
    CostructuredArrow.mk (g ≫ φ).op
  change
    ((colimit.ι (CostructuredArrow.proj u.op (op V) ⋙ F)
          kV : F.obj (op U) ⟶ _) ≫
        (u.op.leftKanExtensionObjIsoColimit F (op V)).inv) ≫
      (u.op.leftKanExtension F).map g.op =
    (colimit.ι (CostructuredArrow.proj u.op (op V') ⋙ F)
        kV' : F.obj (op U) ⟶ _) ≫
      (u.op.leftKanExtensionObjIsoColimit F (op V')).inv
  have hV :
      colimit.ι (kanIndexDiagram u F V) kV ≫
          (u.op.leftKanExtensionObjIsoColimit F (op V)).inv =
        (u.op.leftKanExtensionUnit F).app (op U) ≫
          (u.op.leftKanExtension F).map φ.op := by
    simpa [kanIndexDiagram, kV] using
      (u.op.ι_leftKanExtensionObjIsoColimit_inv F (op V) kV)
  have hV' :
      colimit.ι (kanIndexDiagram u F V') kV' ≫
          (u.op.leftKanExtensionObjIsoColimit F (op V')).inv =
        (u.op.leftKanExtensionUnit F).app (op U) ≫
          (u.op.leftKanExtension F).map (g ≫ φ).op := by
    simpa [kanIndexDiagram, kV'] using
      (u.op.ι_leftKanExtensionObjIsoColimit_inv F (op V') kV')
  dsimp only [kanIndexDiagram, Functor.comp_obj, CostructuredArrow.proj,
    Comma.fst, kV, kV'] at hV hV' ⊢
  rw [hV, hV']
  rw [Category.assoc, ← Functor.map_comp, ← op_comp]

/-- The restriction map is uniquely characterized by its composites with
the canonical maps from all the components of the colimit. -/
theorem pushforwardRestrictionMap_unique (u : C ⥤ D) (F : Presheaf C)
    {V' V : D} (g : V' ⟶ V)
    [HasLeftPushforward u] [HasPointwisePushforward u]
    (m : (pushforwardPresheaf u F).obj (op V) ⟶
      (pushforwardPresheaf u F).obj (op V'))
    (hm : ∀ (U : C) (φ : V ⟶ u.obj U),
      pushforwardCoprojection u F V U φ ≫ m =
        pushforwardCoprojection u F V' U (g ≫ φ)) :
    m = pushforwardRestrictionMap u F g := by
  let : Functor.HasLeftKanExtension u.op F :=
    (inferInstance : HasLeftPushforward u) F
  let : Functor.HasPointwiseLeftKanExtension u.op F :=
    (inferInstance : HasPointwisePushforward u) F
  apply (cancel_epi (pushforwardValueColimitIso u F V).inv).1
  apply colimit.hom_ext
  intro j
  obtain ⟨W, ψ, rfl⟩ := CostructuredArrow.mk_surjective j
  dsimp only [kanIndexDiagram, Functor.comp_obj, CostructuredArrow.proj,
    Comma.fst] at ⊢
  have hnat := pushforwardCoprojection_naturality u F g W.unop ψ.unop
  simpa [pushforwardCoprojection, pushforwardRestrictionMap, kanIndexDiagram,
    Functor.comp_obj, CostructuredArrow.proj, Comma.fst, Category.assoc] using
    (hm W.unop ψ.unop).trans hnat.symm

/-- A natural transformation of presheaves is sent to the corresponding
natural transformation of pushforwards. -/
noncomputable def pushforwardPresheafMap (u : C ⥤ D)
    {F F' : Presheaf C} (η : F ⟶ F') [HasLeftPushforward u] :
    pushforwardPresheaf u F ⟶ pushforwardPresheaf u F' :=
  (pushforwardPresheafFunctor u).map η

/-! ## The adjunction -/

/-- The adjunction `u_p ⊣ u^p`. -/
noncomputable def pushforwardPullbackAdjunction (u : C ⥤ D)
    [HasLeftPushforward u] :
    pushforwardPresheafFunctor u ⊣ pullbackPresheafFunctor u := by
  simpa [pushforwardPresheafFunctor, pullbackPresheafFunctor] using
    (Functor.lanAdjunction u.op (Type v))

/-- The hom-set equivalence expressing the adjunction bifunctorially. -/
noncomputable def pushforwardHomEquiv (u : C ⥤ D) (F : Presheaf C) (G : Presheaf D)
    [HasLeftPushforward u] :
    (pushforwardPresheaf u F ⟶ G) ≃ (F ⟶ pullbackPresheaf u G) :=
  (pushforwardPullbackAdjunction u).homEquiv F G

/-- The same adjunction equivalence in the source's opposite orientation. -/
noncomputable def pullbackHomEquiv (u : C ⥤ D) (F : Presheaf C) (G : Presheaf D)
    [HasLeftPushforward u] :
    (F ⟶ pullbackPresheaf u G) ≃ (pushforwardPresheaf u F ⟶ G) :=
  (pushforwardHomEquiv u F G).symm

/-! ## Arbitrary value categories -/

/-- Restriction of presheaves with values in an arbitrary category `A`. -/
noncomputable def pullbackPresheafWithValuesFunctor (u : C ⥤ D)
    (A : Type a) [Category.{v'} A] :
    PresheafWithValues D A ⥤ PresheafWithValues C A :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op

/-- The `A`-valued version of the source diagram `F_V`. -/
def indexPresheafWithValues (u : C ⥤ D) (A : Type a) [Category.{v'} A]
    (F : PresheafWithValues C A) (V : D) :
    (indexCategory u V)ᵒᵖ ⥤ A :=
  (StructuredArrow.proj V u).op ⋙ F

/-- The costructured-arrow presentation of the same `A`-valued diagram. -/
abbrev kanIndexDiagramWithValues (u : C ⥤ D) (A : Type a) [Category.{v'} A]
    (F : PresheafWithValues C A) (V : D) :=
  CostructuredArrow.proj u.op (op V) ⋙ F

/-- The `A`-valued source diagram agrees with the canonical Kan-extension
diagram under the structured/costructured-arrow equivalence. -/
theorem indexPresheafWithValues_under_equivalence (u : C ⥤ D)
    (A : Type a) [Category.{v'} A] (F : PresheafWithValues C A) (V : D) :
    (indexCostructuredEquivalence u V).functor ⋙ kanIndexDiagramWithValues u A F V =
      indexPresheafWithValues u A F V := by
  rfl

/-- The source's arbitrary-value-category hypothesis that every diagram on
`I_Vᵒᵖ` has a colimit in `A`. -/
abbrev HasIndexColimitsWithValues (u : C ⥤ D)
    (A : Type a) [Category.{v'} A] :=
  ∀ (V : D) (K : (indexCategory u V)ᵒᵖ ⥤ A), HasColimit K

/-- The existence hypothesis for the `A`-valued functorial left Kan extension. -/
abbrev HasLeftPushforwardWithValues (u : C ⥤ D)
    (A : Type a) [Category.{v'} A] :=
  ∀ F : PresheafWithValues C A, Functor.HasLeftKanExtension u.op F

/-- The pointwise-colimit hypothesis for `A`-valued presheaves. -/
abbrev HasPointwisePushforwardWithValues (u : C ⥤ D)
    (A : Type a) [Category.{v'} A] :=
  ∀ F : PresheafWithValues C A, Functor.HasPointwiseLeftKanExtension u.op F

/-- The arbitrary-value-category index-colimit hypothesis supplies the
pointwise Kan-extension hypothesis. -/
theorem hasPointwisePushforwardWithValues_of_indexColimits
    (u : C ⥤ D) (A : Type a) [Category.{v'} A]
    [HasIndexColimitsWithValues u A] :
    HasPointwisePushforwardWithValues u A := by
  intro F V
  change HasColimit (kanIndexDiagramWithValues u A F V.unop)
  let e := indexCostructuredEquivalence u V.unop
  let : HasColimit (e.functor ⋙ kanIndexDiagramWithValues u A F V.unop) := by
    rw [indexPresheafWithValues_under_equivalence]
    exact inferInstance
  exact hasColimit_of_equivalence_comp e

/-- Pointwise `A`-valued colimits supply the existence hypothesis for the
functorial `A`-valued left Kan extension. -/
theorem hasLeftPushforwardWithValues_of_pointwise (u : C ⥤ D)
    (A : Type a) [Category.{v'} A]
    [HasPointwisePushforwardWithValues u A] :
    HasLeftPushforwardWithValues u A :=
  fun _F => inferInstance

/-- The `A`-valued pushforward, whenever all the required pointwise colimits
exist. -/
noncomputable def pushforwardPresheafWithValuesFunctor (u : C ⥤ D)
    (A : Type a) [Category.{v'} A]
    [h : HasLeftPushforwardWithValues u A] :
    PresheafWithValues C A ⥤ PresheafWithValues D A :=
  Functor.lan u.op

/-- The arbitrary-value-category adjunction in the source's remark. -/
noncomputable def pushforwardWithValuesAdjunction (u : C ⥤ D)
    (A : Type a) [Category.{v'} A]
    [HasLeftPushforwardWithValues u A] :
    pushforwardPresheafWithValuesFunctor u A ⊣
      pullbackPresheafWithValuesFunctor u A := by
  simpa [pushforwardPresheafWithValuesFunctor,
    pullbackPresheafWithValuesFunctor] using
    (Functor.lanAdjunction u.op A)

/-! ## Representables -/

/-- Pushforward carries a representable presheaf to the representable at the
image object, up to the canonical Yoneda isomorphism. -/
noncomputable def pushforwardRepresentableIso (u : C ⥤ D) (U : C)
    [HasLeftPushforward u] :
    pushforwardPresheaf u (representablePresheaf U) ≅
      representablePresheaf (u.obj U) := by
  simpa [pushforwardPresheaf, pushforwardPresheafFunctor] using
    (Functor.leftKanExtensionUnique
      (u.op.lan.obj (representablePresheaf U))
      ((u.op.lanUnit.app (representablePresheaf U)))
      (representablePresheaf (u.obj U))
      (yonedaMap u U))

end Formalization.Books.Sites.Unit05
