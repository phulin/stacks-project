import Formalization.Books.Sites.Unit02.Presheaves
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
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
  sorry

theorem indexRestriction_comp (u : C ⥤ D) {V₀ V₁ V₂ : D}
    (g : V₀ ⟶ V₁) (h : V₁ ⟶ V₂) :
    indexRestriction u (g ≫ h) =
      indexRestriction u h ⋙ indexRestriction u g := by
  sorry

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
  sorry

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
  sorry

/-- The source's size/existence condition that every diagram on an index
category `I_Vᵒᵖ` has a colimit in `Sets`. -/
abbrev HasIndexColimits (u : C ⥤ D) :=
  ∀ (V : D) (K : (indexCategory u V)ᵒᵖ ⥤ Type v), HasColimit K

/-! ## Almost-directedness and filteredness -/

/-- Pullbacks and equalizers in `C`, preserved by `u`, give the two
almost-directedness conditions for `(I_V)ᵒᵖ`.  This is Mathlib's
empty-allowed filtered-category interface. -/
theorem indexCategory_op_almostDirected (u : C ⥤ D) (V : D)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    IsFilteredOrEmpty (indexCategory u V)ᵒᵖ := by
  sorry

/-- If `C` has a final object carried by `u` to a final object of `D`, then
the same index category is filtered. -/
theorem indexCategory_op_isFiltered (u : C ⥤ D) (V : D) (X : C)
    (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    IsFiltered (indexCategory u V)ᵒᵖ := by
  sorry

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
  sorry

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
  sorry

/-- The recovery maps are compatible with restriction in `F`. -/
theorem recoverMap_naturality (u : C ⥤ D) (F : Presheaf C)
    {U V : C} (f : V ⟶ U) [HasLeftPushforward u] :
    F.map f.op ≫ recoverMap u F V =
      recoverMap u F U ≫
        (pushforwardPresheaf u F).map (u.map f).op := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The source's arbitrary-value-category hypothesis that every diagram on
`I_Vᵒᵖ` has a colimit in `A`. -/
abbrev HasIndexColimitsWithValues (u : C ⥤ D)
    (A : Type a) [Category.{v'} A] :=
  ∀ (V : D) (K : (indexCategory u V)ᵒᵖ ⥤ A), HasColimit K

/-- The pointwise-colimit hypothesis for `A`-valued presheaves. -/
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
  sorry

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
