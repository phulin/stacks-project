import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.IndYoneda
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Categories, Chapter 25: A criterion for representability

The source calls a covariant functor `F : C ⥤ Sets` representable when it is
naturally isomorphic to `Hom_C(x, -)`.  Mathlib calls this notion
`Functor.IsCorepresentable`; the declarations below use that canonical
orientation and expose the source's Brown-style construction data.
-/

namespace Formalization.Books.Categories.Unit25

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open Opposite

universe u v u' v'

noncomputable section

/-! ## Brown's criterion -/

/-- A family of elements covers every element of a covariant functor. -/
def IsGeneratingFamily {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) : Prop :=
  ∀ (Y : C) (g : F.obj Y),
    ∃ (i : I) (f : X i ⟶ Y), F.map f (x i) = g

/-- The source's category of selected pairs `(X i, x i)`. -/
structure BrownIndex {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) where
  index : I

namespace BrownIndex

instance category {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) : Category (BrownIndex F X x) where
  Hom a b := {f : X a.index ⟶ X b.index // F.map f (x a.index) = x b.index}
  id a := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.1 ≫ g.1, by
    rw [F.map_comp]
    change F.map g.1 (F.map f.1 (x _)) = _
    rw [f.2, g.2]⟩
  id_comp f := by
    apply Subtype.ext
    simp
  comp_id f := by
    apply Subtype.ext
    simp
  assoc f g h := by
    apply Subtype.ext
    simp [Category.assoc]

end BrownIndex

/- The projection forgets the selected element and remembers its object in C. -/
def brownIndexProjection {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) : BrownIndex F X x ⥤ C where
  obj a := X a.index
  map f := f.1
  map_id _ := rfl
  map_comp _ _ := rfl

/- The following cone is the compatible family of chosen elements. -/
def brownUniversalCone {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) :
    Cone (brownIndexProjection F X x ⋙ F) where
  pt := PUnit.{v + 1}
  π :=
    { app := fun a => ↾fun _ => x a.index
      naturality := by
        intro a b f
        ext z
        change x b.index = F.map f.1 (x a.index)
        exact f.2.symm }

/- The object called `x` in the source proof is the limit of the selected
   objects. -/
noncomputable def brownLimitObject {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) [HasLimits C] : C :=
  limit (brownIndexProjection F X x)

/-- The universal element obtained by transporting the compatible family through
the limit-preservation isomorphism. -/
noncomputable def brownUniversalElement {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) [HasLimits C] [PreservesLimits F] :
    F.obj (brownLimitObject F X x) := by
  let hpres : Nonempty
      (IsLimit (F.mapCone (limit.cone (brownIndexProjection F X x)))) :=
    (inferInstance : PreservesLimit (brownIndexProjection F X x) F).preserves
      (limit.isLimit _)
  exact hpres.some.lift (brownUniversalCone F X x) PUnit.unit

/- The source's element-induced transformation is the canonical Coyoneda
   Yoneda map. -/
noncomputable def brownUniversalTransformation {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) [HasLimits C] [PreservesLimits F] :
    coyoneda.obj (op (brownLimitObject F X x)) ⟶ F :=
  coyonedaEquiv.symm (brownUniversalElement F X x)

theorem brownUniversalElement_map_projection {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) [HasLimits C] [PreservesLimits F] (i : I) :
    F.map (limit.π (brownIndexProjection F X x) (BrownIndex.mk i))
        (brownUniversalElement F X x) = x i := by
  sorry

theorem brownUniversalTransformation_app_apply {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) [HasLimits C] [PreservesLimits F]
    {Y : C} (f : brownLimitObject F X x ⟶ Y) :
    (brownUniversalTransformation F X x).app Y f =
      F.map f (brownUniversalElement F X x) := by
  rfl

/- The first half of the source proof: the generating-family hypothesis makes
   the element-induced transformation surjective. -/
theorem brownUniversalTransformation_surjective
    {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {I : Type v} (X : I → C)
    (x : ∀ i, F.obj (X i)) [HasLimits C] [PreservesLimits F]
    (hgen : IsGeneratingFamily F X x) :
    ∀ Y : C, Function.Surjective
      ((brownUniversalTransformation F X x).app Y) := by
  sorry

/-- Brown's representability criterion, in Mathlib's covariant terminology. -/
theorem brown_representability_criterion
    {C : Type u} [Category.{v} C] [HasLimits C]
    (F : C ⥤ Type v) [PreservesLimits F]
    {I : Type v} (X : I → C) (x : ∀ i, F.obj (X i))
    (hgen : IsGeneratingFamily F X x) :
    F.IsCorepresentable := by
  sorry

/-! ## The equalizer refinement in Brown's proof -/

/-- Self-maps fixing a chosen element, as used in the source's wide equalizer. -/
def BrownStabilizer {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) : Type v :=
  {f : Y ⟶ Y // F.map f y = y}

/-- The family consisting of every stabilizing endomorphism and the identity. -/
def brownStabilizerFamily {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) :
    (BrownStabilizer F y ⊕ PUnit.{v + 1}) → (Y ⟶ Y)
  | Sum.inl f => f.1
  | Sum.inr _ => 𝟙 Y

instance brownStabilizerFamily_nonempty {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) :
    Nonempty (BrownStabilizer F y ⊕ PUnit.{v + 1}) :=
  ⟨Sum.inr PUnit.unit⟩

noncomputable def brownEqualizerObject {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) [HasLimits C] : C :=
  wideEqualizer (brownStabilizerFamily F y)

noncomputable def brownEqualizerMap {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) [HasLimits C] :
    brownEqualizerObject F y ⟶ Y :=
  wideEqualizer.ι (brownStabilizerFamily F y)

theorem brownEqualizerMap_mono {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) [HasLimits C] :
    Mono (brownEqualizerMap F y) := by
  change Mono (wideEqualizer.ι (brownStabilizerFamily F y))
  infer_instance

theorem brownEqualizerMap_stabilizes {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) [HasLimits C]
    (f : BrownStabilizer F y) :
    brownEqualizerMap F y ≫ f.1 = brownEqualizerMap F y := by
  change wideEqualizer.ι (brownStabilizerFamily F y) ≫ f.1 =
    wideEqualizer.ι (brownStabilizerFamily F y)
  simpa [brownStabilizerFamily] using
    (wideEqualizer.condition (f := brownStabilizerFamily F y)
      (Sum.inl f) (Sum.inr PUnit.unit))

theorem exists_brownEqualizerElement {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) [HasLimits C] [PreservesLimits F] :
    ∃ y' : F.obj (brownEqualizerObject F y),
      F.map (brownEqualizerMap F y) y' = y := by
  sorry

noncomputable def brownEqualizerTransformation {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y' : C} (y' : F.obj Y') :
    coyoneda.obj (op Y') ⟶ F :=
  coyonedaEquiv.symm y'

theorem brownEqualizerTransformation_surjective {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y)
    {Y' : C} (y' : F.obj Y') (e : Y' ⟶ Y)
    (he : F.map e y' = y)
    (hξ : ∀ Z : C, Function.Surjective
      ((coyonedaEquiv.symm y).app Z)) :
    ∀ Z : C, Function.Surjective
      ((brownEqualizerTransformation F y').app Z) := by
  sorry

/- The second equalizer in the source proof is an ordinary equalizer. -/
noncomputable def brownFinalEqualizerObject {C : Type u} [Category.{v} C]
    {Y' Z : C} (a b : Y' ⟶ Z) [HasLimits C] : C :=
  equalizer a b

noncomputable def brownFinalEqualizerMap {C : Type u} [Category.{v} C]
    {Y' Z : C} (a b : Y' ⟶ Z) [HasLimits C] :
    brownFinalEqualizerObject a b ⟶ Y' :=
  equalizer.ι a b

theorem brownFinalEqualizerMap_condition {C : Type u} [Category.{v} C]
    {Y' Z : C} (a b : Y' ⟶ Z) [HasLimits C] :
    brownFinalEqualizerMap a b ≫ a = brownFinalEqualizerMap a b ≫ b := by
  exact equalizer.condition a b

theorem exists_brownFinalEqualizerElement {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y' Z : C} (a b : Y' ⟶ Z) (y' : F.obj Y')
    (hab : F.map a y' = F.map b y') [HasLimits C] [PreservesLimits F] :
    ∃ y'' : F.obj (brownFinalEqualizerObject a b),
      F.map (brownFinalEqualizerMap a b) y'' = y' := by
  sorry

theorem brown_final_equalizer_argument
    {C : Type u} [Category.{v} C] [HasLimits C]
    (F : C ⥤ Type v) [PreservesLimits F]
    {I : Type v} (X : I → C) (x : ∀ i, F.obj (X i))
    (hgen : IsGeneratingFamily F X x)
    (hξ : ∀ Y : C, Function.Surjective
      ((brownUniversalTransformation F X x).app Y))
    {Z : C} (y' : F.obj (brownEqualizerObject F (brownUniversalElement F X x)))
    (he : F.map (brownEqualizerMap F (brownUniversalElement F X x)) y' =
      brownUniversalElement F X x)
    (a b : brownEqualizerObject F (brownUniversalElement F X x) ⟶ Z)
    (hab : F.map a y' = F.map b y') :
    a = b := by
  sorry

theorem brown_equalizer_represents
    {C : Type u} [Category.{v} C] [HasLimits C]
    (F : C ⥤ Type v) [PreservesLimits F]
    {I : Type v} (X : I → C) (x : ∀ i, F.obj (X i))
    (hgen : IsGeneratingFamily F X x) :
    ∃ y' : F.obj (brownEqualizerObject F (brownUniversalElement F X x)),
      (∀ Z : C, Function.Bijective
        ((brownEqualizerTransformation F y').app Z)) ∧
      F.map (brownEqualizerMap F (brownUniversalElement F X x)) y' =
        brownUniversalElement F X x := by
  sorry

/-! ## The free-group application -/

/- The source's `G ↦ Map(E, G)` is this composite of the forgetful functor
   with the Coyoneda functor. -/
abbrev groupMapsFunctor (E : Type v) : GrpCat.{v} ⥤ Type v :=
  (forget GrpCat) ⋙ coyoneda.obj (op E)

instance groupMapsFunctor_preservesLimits_instance (E : Type v) :
    PreservesLimits (groupMapsFunctor E) := by
  infer_instance

def freeGroupCorepresentableBy (E : Type v) :
    (groupMapsFunctor E).CorepresentableBy ((GrpCat.free).obj E) :=
  GrpCat.adj.corepresentableBy E

theorem groupMapsFunctor_isCorepresentable (E : Type v) :
    (groupMapsFunctor E).IsCorepresentable :=
  (freeGroupCorepresentableBy E).isCorepresentable

/- The identity of the free group corresponds to the universal map from E. -/
def freeGroupGenerator (E : Type v) :
    E → ((GrpCat.free).obj E : Type v) :=
  TypeCat.homEquiv ((freeGroupCorepresentableBy E).homEquiv (𝟙 _))

def groupMapAsHom {E : Type v} {G : GrpCat.{v}}
    (f : E → (G : Type v)) : E ⟶ (G : Type v) :=
  TypeCat.homEquiv.symm f

/- The cardinal estimate behind the bounded-family construction: the subgroup
   generated by the image of a map from `E` is no larger than the stated
   bound. -/
theorem subgroup_closure_cardinal_le {E : Type v} {G : GrpCat.{v}}
    (f : E → (G : Type v)) :
    Cardinal.mk (Subgroup.closure (Set.range f)) ≤
      max Cardinal.aleph0 (Cardinal.mk E) := by
  sorry

def IsBoundedGroupMapFamily (E : Type v) {I : Type v}
    (G : I → GrpCat.{v}) (f : ∀ i, E → (G i : Type v)) : Prop :=
  (∀ i, Cardinal.mk (G i) ≤ max Cardinal.aleph0 (Cardinal.mk E)) ∧
    IsGeneratingFamily (groupMapsFunctor E) G (fun i => groupMapAsHom (f i))

theorem groupMapsFunctor_isCorepresentable_of_bounded_family
    (E : Type v) {I : Type v} (G : I → GrpCat.{v})
    (f : ∀ i, E → (G i : Type v)) [HasLimits (GrpCat.{v})]
    [PreservesLimits (groupMapsFunctor E)]
    (hfamily : IsBoundedGroupMapFamily E G f) :
    (groupMapsFunctor E).IsCorepresentable := by
  exact brown_representability_criterion (groupMapsFunctor E) G
    (fun i => groupMapAsHom (f i)) hfamily.2

theorem freeGroupGenerator_generates (E : Type v) :
    Subgroup.closure (Set.range (freeGroupGenerator E)) = ⊤ := by
  sorry

/-! ## The topological-space application -/

/- The source's `Y ↦ lim_i Hom(X_i, Y)` is a limit in the functor category.
   The opposite diagram is used because `Hom(-, Y)` is contravariant in its
   first argument. -/
abbrev topologicalHomFunctor {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) : TopCat.{v} ⥤ Type v :=
  limit (D.op ⋙ coyoneda)

def topologicalHomFunctor_objIso {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) (Y : TopCat.{v}) :
    (topologicalHomFunctor D).obj Y ≅
      limit ((D.op ⋙ coyoneda) ⋙ (evaluation _ _).obj Y) :=
  limitObjIsoLimitCompEvaluation (D.op ⋙ coyoneda) Y

/-- The `i`-th map in a compatible family of maps into `Y`. -/
def topologicalHomFamily {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) {Y : TopCat.{v}}
    (φ : (topologicalHomFunctor D).obj Y) (i : I) : D.obj i ⟶ Y :=
  (limit.π (D.op ⋙ coyoneda) (op i)).app Y φ

/-- The union of the images of the maps in a compatible family. -/
def topologicalHomImage {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) {Y : TopCat.{v}}
    (φ : (topologicalHomFunctor D).obj Y) : Set Y :=
  ⋃ i, Set.range (topologicalHomFamily D φ i)

/-- The source's subspace of `Y` generated by the images of a compatible family. -/
def topologicalHomSubspace {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) {Y : TopCat.{v}}
    (φ : (topologicalHomFunctor D).obj Y) : TopCat.{v} :=
  TopCat.of (topologicalHomImage D φ)

def topologicalHomSubspaceInclusion {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) {Y : TopCat.{v}}
    (φ : (topologicalHomFunctor D).obj Y) :
    topologicalHomSubspace D φ ⟶ Y :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Every map in the compatible family factors through the induced subspace. -/
def topologicalHomFactor {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) {Y : TopCat.{v}}
    (φ : (topologicalHomFunctor D).obj Y) (i : I) :
    D.obj i ⟶ topologicalHomSubspace D φ :=
  TopCat.ofHom
    ⟨fun z =>
        ⟨topologicalHomFamily D φ i z,
          Set.mem_iUnion.2 ⟨i, Set.mem_range.2 ⟨z, rfl⟩⟩⟩,
      (topologicalHomFamily D φ i).hom.continuous.subtype_mk (fun z =>
        Set.mem_iUnion.2 ⟨i, Set.mem_range.2 ⟨z, rfl⟩⟩)⟩

theorem topologicalHomFactor_comp_inclusion {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) {Y : TopCat.{v}}
    (φ : (topologicalHomFunctor D).obj Y) (i : I) :
    topologicalHomFactor D φ i ≫ topologicalHomSubspaceInclusion D φ =
      topologicalHomFamily D φ i := by
  ext z
  rfl

/- The source observes that this functor preserves limits; we retain the
   assertion as a reusable instance for the representability application. -/
instance topologicalHomFunctor_preservesLimits_instance {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) : PreservesLimits (topologicalHomFunctor D) := by
  sorry

def IsBoundedTopologicalHomFamily {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) {J : Type v} (Y : J → TopCat.{v})
    (φ : ∀ j, (topologicalHomFunctor D).obj (Y j)) : Prop :=
  (∀ j, Cardinal.mk (Y j) ≤ Cardinal.mk (Σ i : I, D.obj i)) ∧
    IsGeneratingFamily (topologicalHomFunctor D) Y φ

theorem topologicalHomFunctor_isCorepresentable_of_bounded_family
    {I : Type v} [Category.{v} I] (D : I ⥤ TopCat.{v})
    {J : Type v} (Y : J → TopCat.{v})
    (φ : ∀ j, (topologicalHomFunctor D).obj (Y j))
    (hfamily : IsBoundedTopologicalHomFamily D Y φ) :
    (topologicalHomFunctor D).IsCorepresentable := by
  exact brown_representability_criterion (topologicalHomFunctor D) Y φ hfamily.2

/-- The induced subspace has cardinality bounded by the disjoint union of the
    spaces in the diagram. -/
theorem topologicalHomSubspace_cardinal_le {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) {Y : TopCat.{v}}
    (φ : (topologicalHomFunctor D).obj Y) :
    Cardinal.mk (topologicalHomSubspace D φ) ≤
      Cardinal.mk (Σ i : I, D.obj i) := by
  sorry

/- The factorization assertion used to pass from an arbitrary compatible
   family to the bounded subspace family. -/
theorem exists_topologicalHomSubspaceElement {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) {Y : TopCat.{v}}
    (φ : (topologicalHomFunctor D).obj Y) :
    ∃ φ' : (topologicalHomFunctor D).obj (topologicalHomSubspace D φ),
      (topologicalHomFunctor D).map (topologicalHomSubspaceInclusion D φ) φ' = φ := by
  sorry

noncomputable def topologicalHomFunctor_corepresentable_by_colimit {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) :
    (topologicalHomFunctor D).CorepresentableBy (colimit D) := by
  exact Functor.corepresentableByEquiv.symm (coyonedaOpColimitIsoLimitCoyoneda D)

/-! ## The adjoint functor theorem -/

/- For a fixed object `Y` of the target, this is the covariant Hom functor
   whose representability is the central step in the source's proof. -/
abbrev adjointHomFunctor
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) (Y : D) : C ⥤ Type v' :=
  G ⋙ coyoneda.obj (op Y)

theorem adjointHomFunctor_isCorepresentable
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) [HasLimits C]
    [PreservesLimitsOfSize.{v, v} G]
    (hG : SolutionSetCondition.{v} G) (Y : D) :
    (adjointHomFunctor G Y).IsCorepresentable := by
  sorry

/-- The general adjoint functor theorem, using Mathlib's canonical
    solution-set-condition interface. -/
theorem adjointFunctorTheorem
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) [HasLimits C]
    [PreservesLimitsOfSize.{v, v} G]
    (hG : SolutionSetCondition.{v} G) : G.IsRightAdjoint := by
  exact isRightAdjoint_of_preservesLimits_of_solutionSetCondition G hG

noncomputable def leftAdjointOfAdjointFunctorTheorem
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) [HasLimits C]
    [PreservesLimitsOfSize.{v, v} G]
    (hG : SolutionSetCondition.{v} G) : D ⥤ C := by
  exact (adjointFunctorTheorem G hG).exists_leftAdjoint.choose

theorem leftAdjointOfAdjointFunctorTheorem_isLeftAdjoint
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) [HasLimits C]
    [PreservesLimitsOfSize.{v, v} G]
    (hG : SolutionSetCondition.{v} G) :
    Nonempty (leftAdjointOfAdjointFunctorTheorem G hG ⊣ G) := by
  exact (adjointFunctorTheorem G hG).exists_leftAdjoint.choose_spec
