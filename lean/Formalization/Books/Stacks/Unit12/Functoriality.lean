import Formalization.Books.Stacks.Unit09.StackificationGroupoids
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Sites.Over

/-!
# Stacks, Chapter 1, Section 12: functoriality for stacks

The reindexing construction is expressed using Mathlib's pseudofunctor
composition.  The localization construction is recorded by data structures
whose fields expose the mathematical properties used by the chapter.
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Pseudofunctor
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t v' v u' u w' w

abbrev FixedFiberedCategory (C : Type u) [Category.{v} C] :=
  Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}

def pushforwardFiberedCategory {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory D) : FixedFiberedCategory C :=
  Pseudofunctor.comp u.op.toPseudofunctor S

theorem pushforward_fibered_morphism_exists {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    {S T : FixedFiberedCategory D} (η : S ⟶ T) :
    Nonempty (pushforwardFiberedCategory u S ⟶ pushforwardFiberedCategory u T) := by
  change Nonempty (Pseudofunctor.comp u.op.toPseudofunctor S ⟶
    Pseudofunctor.comp u.op.toPseudofunctor T)
  let app := fun a => η.app (u.op.toPseudofunctor.obj a)
  let naturality := fun {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) =>
    η.naturality (u.op.toPseudofunctor.map f)
  refine ⟨Pseudofunctor.StrongTrans.mk app naturality ?_ ?_ ?_⟩
  · intro a b f g h
    change
      Bicategory.whiskerRight (S.map₂ (u.op.toPseudofunctor.map₂ h))
          (η.app (u.op.toPseudofunctor.obj b)) ≫
          (η.naturality (u.op.toPseudofunctor.map g)).hom =
        (η.naturality (u.op.toPseudofunctor.map f)).hom ≫
          Bicategory.whiskerLeft (η.app (u.op.toPseudofunctor.obj a))
            (T.map₂ (u.op.toPseudofunctor.map₂ h))
    exact η.naturality_naturality (u.op.toPseudofunctor.map₂ h)
  · intro a
    change
      (η.naturality (u.op.toPseudofunctor.map (𝟙 a))).hom ≫
          Bicategory.whiskerLeft (η.app (u.op.toPseudofunctor.obj a))
            (T.map₂ (u.op.toPseudofunctor.mapId a).hom ≫
              (T.mapId (u.op.toPseudofunctor.obj a)).hom) =
        Bicategory.whiskerRight
            (S.map₂ (u.op.toPseudofunctor.mapId a).hom ≫
              (S.mapId (u.op.toPseudofunctor.obj a)).hom)
            (η.app (u.op.toPseudofunctor.obj a)) ≫
          (Bicategory.leftUnitor (η.app (u.op.toPseudofunctor.obj a))).hom ≫
            (Bicategory.rightUnitor (η.app (u.op.toPseudofunctor.obj a))).inv
    simp only [Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight]
    rw [← Category.assoc]
    rw [← η.naturality_naturality (u.op.toPseudofunctor.mapId a).hom]
    rw [Category.assoc]
    rw [Category.assoc]
    have hη := η.naturality_id (u.op.toPseudofunctor.obj a)
    simpa only [Category.assoc] using congrArg (fun k =>
      Bicategory.whiskerRight (S.map₂ (u.op.toPseudofunctor.mapId a).hom)
        (η.app (u.op.toPseudofunctor.obj a)) ≫ k) hη
  · intro a b c f g
    change
      (η.naturality (u.op.toPseudofunctor.map (f ≫ g))).hom ≫
          Bicategory.whiskerLeft (η.app (u.op.toPseudofunctor.obj a))
            (T.map₂ (u.op.toPseudofunctor.mapComp f g).hom ≫
              (T.mapComp (u.op.toPseudofunctor.map f)
                (u.op.toPseudofunctor.map g)).hom) =
        Bicategory.whiskerRight
            (S.map₂ (u.op.toPseudofunctor.mapComp f g).hom ≫
              (S.mapComp (u.op.toPseudofunctor.map f)
                (u.op.toPseudofunctor.map g)).hom)
            (η.app (u.op.toPseudofunctor.obj c)) ≫
          (Bicategory.associator (S.map (u.op.toPseudofunctor.map f))
            (S.map (u.op.toPseudofunctor.map g))
            (η.app (u.op.toPseudofunctor.obj c))).hom ≫
          Bicategory.whiskerLeft (S.map (u.op.toPseudofunctor.map f))
            (η.naturality (u.op.toPseudofunctor.map g)).hom ≫
          (Bicategory.associator (S.map (u.op.toPseudofunctor.map f))
            (η.app (u.op.toPseudofunctor.obj b))
            (T.map (u.op.toPseudofunctor.map g))).inv ≫
          Bicategory.whiskerRight
            (η.naturality (u.op.toPseudofunctor.map f)).hom
            (T.map (u.op.toPseudofunctor.map g)) ≫
          (Bicategory.associator (η.app (u.op.toPseudofunctor.obj a))
            (T.map (u.op.toPseudofunctor.map f))
            (T.map (u.op.toPseudofunctor.map g))).hom
    rw [Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight]
    simp only [← Category.assoc]
    rw [← η.naturality_naturality (u.op.toPseudofunctor.mapComp f g).hom]
    have hη := η.naturality_comp
      (u.op.toPseudofunctor.map f) (u.op.toPseudofunctor.map g)
    simpa only [Category.assoc] using congrArg (fun k =>
      Bicategory.whiskerRight (S.map₂ (u.op.toPseudofunctor.mapComp f g).hom)
        (η.app (u.op.toPseudofunctor.obj c)) ≫ k) hη

noncomputable def pushforwardFiberedMorphism {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    {S T : FixedFiberedCategory D} (η : S ⟶ T) :
    pushforwardFiberedCategory u S ⟶ pushforwardFiberedCategory u T :=
  Classical.choice (pushforward_fibered_morphism_exists u η)

theorem pushforward_fibre {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory D) (U : C) :
    Fiber (pushforwardFiberedCategory u S) U = Fiber S (u.obj U) := by
  rfl

def PushforwardStack {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory D) (J : GrothendieckTopology C) : Prop :=
  Stack (pushforwardFiberedCategory u S) J

theorem stack_pushforward {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (u : C ⥤ D)
    (S : FixedFiberedCategory D) (hS : Stack S K)
    (hu : u.IsContinuous J K)
    [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    PushforwardStack u S J := by
  sorry

theorem stack_in_groupoids_pushforward {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (u : C ⥤ D)
    (S : FixedFiberedCategory D) (hS : StackInGroupoids S K)
    (hu : u.IsContinuous J K)
    [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    StackInGroupoids (pushforwardFiberedCategory u S) J := by
  refine ⟨?_, ?_⟩
  · intro U
    rw [pushforward_fibre u S U]
    exact hS.1 (u.obj U)
  · exact stack_pushforward u S hS.2 hu

structure PullbackPrecategoryObject {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) where
  object : Pseudofunctor.CoGrothendieck S
  base : D
  anchor : base ⟶ u.obj object.base

structure PullbackPrecategoryMorphism {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (x y : PullbackPrecategoryObject u S) where
  base : x.base ⟶ y.base
  object : x.object ⟶ y.object
  commutes : x.anchor ≫ u.map object.base = base ≫ y.anchor

def pullbackPrecategoryIdentity {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (x : PullbackPrecategoryObject u S) :
    PullbackPrecategoryMorphism u S x x where
  base := 𝟙 x.base
  object := 𝟙 x.object
  commutes := by simp

def pullbackPrecategoryComp {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) {x y z : PullbackPrecategoryObject u S}
    (f : PullbackPrecategoryMorphism u S x y)
    (g : PullbackPrecategoryMorphism u S y z) :
    PullbackPrecategoryMorphism u S x z where
  base := f.base ≫ g.base
  object := f.object ≫ g.object
  commutes := by
    change x.anchor ≫ u.map (f.object.base ≫ g.object.base) =
      (f.base ≫ g.base) ≫ z.anchor
    rw [u.map_comp, ← Category.assoc, f.commutes]
    simp only [Category.assoc]
    rw [g.commutes]

instance pullbackPrecategoryCategory {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) :
    Category (PullbackPrecategoryObject u S) where
  Hom := PullbackPrecategoryMorphism u S
  id := pullbackPrecategoryIdentity u S
  comp := @pullbackPrecategoryComp C _ D _ u S
  id_comp := by
    intro x y f
    cases f
    simp [pullbackPrecategoryIdentity, pullbackPrecategoryComp]
  comp_id := by
    intro x y f
    cases f
    simp [pullbackPrecategoryIdentity, pullbackPrecategoryComp]
  assoc := by
    intro w x y z f g h
    cases f
    cases g
    cases h
    simp [pullbackPrecategoryComp]

def pullbackPrecategoryForget {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) :
    PullbackPrecategoryObject u S ⥤ D where
  obj x := x.base
  map f := f.base

def rightCartesianSystem {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) {x y : PullbackPrecategoryObject u S}
    (f : PullbackPrecategoryMorphism u S x y) : Prop :=
  (∃ h : x.base = y.base, f.base = eqToHom h) ∧
    IsStronglyCartesian (Pseudofunctor.CoGrothendieck.forget S)
      f.object.base f.object

def rightCartesianMorphismProperty {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) :
    MorphismProperty (PullbackPrecategoryObject u S) :=
  fun _ _ f => rightCartesianSystem u S f

structure RightMultiplicativeSystem {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) where
  hasRightCalculusOfFractions :
    (rightCartesianMorphismProperty u S).HasRightCalculusOfFractions

theorem right_multiplicative_system {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) [HasFiniteProducts C] [HasEqualizers C]
    [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty (RightMultiplicativeSystem u S) := by
  sorry

structure PullbackFiberedData {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) where
  value : FixedFiberedCategory.{v', u', w} D
  projection : PullbackPrecategoryObject u S ⥤
    Pseudofunctor.CoGrothendieck value
  projection_over :
    projection ⋙ Pseudofunctor.CoGrothendieck.forget value =
      pullbackPrecategoryForget u S
  unit : S ⟶ pushforwardFiberedCategory u value
  isLocalization :
    projection.IsLocalization (rightCartesianMorphismProperty u S)

theorem fibred_category_pullback {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) [HasFiniteProducts C] [HasEqualizers C]
    [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty (PullbackFiberedData u S) := by
  sorry

theorem fibred_groupoids_category_pullback
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (u : C ⥤ D) (S : FixedFiberedCategory C) (hS : FiberwiseGroupoid S)
    [HasFiniteProducts C] [HasEqualizers C] [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    ∃ P : PullbackFiberedData u S, FiberwiseGroupoid P.value := by
  sorry

structure PullbackStackData {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (K : GrothendieckTopology D) where
  fibered : PullbackFiberedData u S
  stackification : Stackification.{t, v', u', w} fibered.value K

structure PullbackStackificationComparison {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    {J : GrothendieckTopology C} (K : GrothendieckTopology D)
    {S : FixedFiberedCategory C}
    (A : Stackification.{t, v, u, w} S J) where
  source : PullbackStackData.{t, v', v, u', u, w} u S K
  target : PullbackStackData.{t, v', v, u', u, w} u A.value K
  induced : source.fibered.value ⟶ target.fibered.value
  compatibility : Nonempty
    (A.map ≫ target.fibered.unit ≅
      source.fibered.unit ≫ pushforwardFiberedMorphism u induced)
  rawStackification :
    Stackification.{t, v', u', w} source.fibered.value K
  comparison : rawStackification.value ⟶ target.stackification.value
  comparisonCompatibility : Nonempty
    (rawStackification.map ≫ comparison ≅
      induced ≫ target.stackification.map)
  comparisonIsEquivalence : FiberwiseEquivalence comparison

noncomputable def pullbackStackification {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (K : GrothendieckTopology D)
    (h : Nonempty (PullbackStackData u S K)) : FixedFiberedCategory D :=
  (Classical.choice h).stackification.value

theorem adjunction_pullback_pushforward
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (u : C ⥤ D) (S : FixedFiberedCategory C) (T : FixedFiberedCategory D)
    [HasFiniteProducts C] [HasEqualizers C] [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : Nonempty (PullbackFiberedData u S)) :
    Nonempty
      ((S ⟶ pushforwardFiberedCategory u T) ≌
        ((Classical.choice h).value ⟶ T)) := by
  sorry

theorem pullback_stack_exists {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (K : GrothendieckTopology D)
    [HasFiniteProducts C] [HasEqualizers C] [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty (PullbackStackData u S K) := by
  rcases fibred_category_pullback u S with ⟨fibered⟩
  rcases stackification_exists fibered.value K with ⟨stackification⟩
  exact ⟨⟨fibered, stackification⟩⟩

theorem adjunction_pullback_pushforward_stacks
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) (S : FixedFiberedCategory C) (T : FixedFiberedCategory D)
    (hS : Stack S J) (hT : Stack T K) (hu : u.IsContinuous J K)
    [HasFiniteProducts C] [HasEqualizers C] [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty ((S ⟶ pushforwardFiberedCategory u T) ≌
      ((Classical.choice (pullback_stack_exists u S K)).stackification.value ⟶ T)) := by
  sorry

theorem technical_pullback_stackification
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) (S : FixedFiberedCategory C)
    (A : Stackification.{t, v, u, w} S J)
    (hu : u.IsContinuous J K)
    [HasFiniteProducts C] [HasEqualizers C] [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty (PullbackStackificationComparison.{t, v', v, u', u, w} u K A) := by
  sorry

structure BiggerSiteAssumptions {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) where
  fullyFaithful : u.FullyFaithful
  continuous : u.IsContinuous J K
  cocontinuous : u.IsCocontinuous J K

structure BiggerSiteResult {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) where
  isStack : Stack S J
  pullback : PullbackStackData.{t, v', v, u', u, w} u S K
  canonical : S ⟶ pushforwardFiberedCategory u pullback.stackification.value
  equivalence : FiberwiseEquivalence canonical
  fullOnMorphisms : ∀ (T : FixedFiberedCategory.{v, u, w} C)
    (_hT : Stack T J)
    (pullbackT : PullbackStackData.{t, v', v, u', u, w} u T K),
    Nonempty ((S ⟶ T) ≌
      (pullback.stackification.value ⟶ pullbackT.stackification.value))

theorem bigger_site {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (h : BiggerSiteAssumptions u J K) (S : FixedFiberedCategory C)
    (hS : Stack S J) [HasFiniteProducts C] [HasEqualizers C]
    [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty (BiggerSiteResult.{t, v', v, u', u, w} u S J K) := by
  sorry

end Formalization.Books.Stacks.Unit01
