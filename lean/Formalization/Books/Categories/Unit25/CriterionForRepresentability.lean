import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.IndYoneda
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Free
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
  let hpres : Nonempty
      (IsLimit (F.mapCone (limit.cone (brownIndexProjection F X x)))) :=
    (inferInstance : PreservesLimit (brownIndexProjection F X x) F).preserves
      (limit.isLimit _)
  change (F.map (limit.π (brownIndexProjection F X x) (BrownIndex.mk i)))
      ((hpres.some.lift (brownUniversalCone F X x)) PUnit.unit) = x i
  have h := hpres.some.fac (brownUniversalCone F X x) (BrownIndex.mk i)
  exact congrArg (fun q => q PUnit.unit) h

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
  intro Y g
  obtain ⟨i, f, hf⟩ := hgen Y g
  change (brownIndexProjection F X x).obj (BrownIndex.mk i) ⟶ Y at f
  refine ⟨limit.π (brownIndexProjection F X x) (BrownIndex.mk i) ≫ f, ?_⟩
  rw [brownUniversalTransformation_app_apply]
  change F.map (limit.π (brownIndexProjection F X x) (BrownIndex.mk i) ≫ f)
      (brownUniversalElement F X x) = g
  rw [F.map_comp]
  change (F.map f)
      (F.map (limit.π (brownIndexProjection F X x) (BrownIndex.mk i))
        (brownUniversalElement F X x)) = g
  rw [brownUniversalElement_map_projection]
  change (F.map f) (x i) = g at hf
  exact hf

private def brownCriterionStabilizer {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) : Type v :=
  {f : Y ⟶ Y // F.map f y = y}

private def brownCriterionStabilizerFamily {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) :
    (brownCriterionStabilizer F y ⊕ PUnit.{v + 1}) → (Y ⟶ Y)
  | Sum.inl f => f.1
  | Sum.inr _ => 𝟙 Y

private noncomputable def brownCriterionEqualizerObject {C : Type u}
    [Category.{v} C] (F : C ⥤ Type v) {Y : C} (y : F.obj Y)
    [HasLimits C] : C :=
  wideEqualizer (brownCriterionStabilizerFamily F y)

private noncomputable def brownCriterionEqualizerMap {C : Type u}
    [Category.{v} C] (F : C ⥤ Type v) {Y : C} (y : F.obj Y)
    [HasLimits C] : brownCriterionEqualizerObject F y ⟶ Y :=
  wideEqualizer.ι (brownCriterionStabilizerFamily F y)

private theorem brownCriterionEqualizerElement {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {Y : C} (y : F.obj Y) [HasLimits C] [PreservesLimits F] :
    ∃ y' : F.obj (brownCriterionEqualizerObject F y),
      F.map (brownCriterionEqualizerMap F y) y' = y := by
  let hpres : Nonempty
      (IsLimit (F.mapCone (limit.cone
        (parallelFamily (brownCriterionStabilizerFamily F y))))) :=
    (inferInstance : PreservesLimit
      (parallelFamily (brownCriterionStabilizerFamily F y)) F).preserves
      (limit.isLimit _)
  let c : Cone ((parallelFamily (brownCriterionStabilizerFamily F y)) ⋙ F) :=
    { pt := PUnit.{v + 1}
      π :=
        { app := fun j => match j with
          | WalkingParallelFamily.zero => ↾(fun _ => y)
          | WalkingParallelFamily.one => ↾(fun _ => y)
          naturality := by
            intro j k f
            cases f with
            | id => simp
            | line j =>
                rcases j with f | _
                · ext z
                  simpa [brownCriterionStabilizerFamily] using f.2.symm
                · simp [brownCriterionStabilizerFamily] } }
  refine ⟨hpres.some.lift c PUnit.unit, ?_⟩
  have h := hpres.some.fac c WalkingParallelFamily.zero
  exact congrArg (fun q => q PUnit.unit) h

private theorem brownCriterionFinalEqualizerElement {C : Type u}
    [Category.{v} C] (F : C ⥤ Type v) {Y' Z : C}
    (a b : Y' ⟶ Z) (y' : F.obj Y')
    (hab : F.map a y' = F.map b y') [HasLimits C] [PreservesLimits F] :
    ∃ y'' : F.obj (equalizer a b),
      F.map (equalizer.ι a b) y'' = y' := by
  let hpres : Nonempty
      (IsLimit (F.mapCone (limit.cone (parallelPair a b)))) :=
    (inferInstance : PreservesLimit (parallelPair a b) F).preserves
      (limit.isLimit _)
  let c : Cone ((parallelPair a b) ⋙ F) :=
    Cone.ofFork (Fork.ofι (↾(fun _ : PUnit.{v + 1} => y')) (by
      ext z
      exact hab))
  refine ⟨hpres.some.lift c PUnit.unit, ?_⟩
  have h := hpres.some.fac c WalkingParallelPair.zero
  exact congrArg (fun q => q PUnit.unit) h

private theorem brown_representability_criterion_corepresentableBy
    {C : Type u} [Category.{v} C] [HasLimits C]
    (F : C ⥤ Type v) [PreservesLimits F]
    {I : Type v} (X : I → C) (x : ∀ i, F.obj (X i))
    (hgen : IsGeneratingFamily F X x) :
    ∃ Y : C, Nonempty (F.CorepresentableBy Y) := by
  have hξ := brownUniversalTransformation_surjective F X x hgen
  obtain ⟨y', he⟩ :=
    brownCriterionEqualizerElement F (brownUniversalElement F X x)
  have hsurj : ∀ Z : C, Function.Surjective
      ((coyonedaEquiv.symm y').app Z) := by
    intro Z g
    obtain ⟨f, hf⟩ := hξ Z g
    refine ⟨brownCriterionEqualizerMap F
      (brownUniversalElement F X x) ≫ f, ?_⟩
    change F.map (brownCriterionEqualizerMap F
      (brownUniversalElement F X x) ≫ f) y' = g
    rw [F.map_comp]
    change F.map f (F.map (brownCriterionEqualizerMap F
      (brownUniversalElement F X x)) y') = g
    rw [he]
    exact hf
  have hinj : ∀ Z : C, Function.Injective
      ((coyonedaEquiv.symm y').app Z) := by
    intro Z a b hab
    change F.map a y' = F.map b y' at hab
    obtain ⟨y'', hy''⟩ := brownCriterionFinalEqualizerElement F a b y' hab
    obtain ⟨ψ, hψ⟩ := hξ (equalizer a b) y''
    rw [brownUniversalTransformation_app_apply] at hψ
    let e₀ := brownCriterionEqualizerMap F
      (brownUniversalElement F X x)
    let e' := equalizer.ι a b
    have hs : F.map (ψ ≫ e' ≫ e₀) (brownUniversalElement F X x) =
        brownUniversalElement F X x := by
      rw [F.map_comp, F.map_comp]
      change F.map e₀ (F.map e' (F.map ψ
        (brownUniversalElement F X x))) = brownUniversalElement F X x
      rw [hψ, hy'', he]
    let s : brownCriterionStabilizer F (brownUniversalElement F X x) :=
      ⟨ψ ≫ e' ≫ e₀, hs⟩
    have he_mono : Mono (brownCriterionEqualizerMap F
        (brownUniversalElement F X x)) := by
      change Mono (wideEqualizer.ι
        (brownCriterionStabilizerFamily F (brownUniversalElement F X x)))
      infer_instance
    have hstab : e₀ ≫ s.1 = e₀ := by
      simpa [e₀, brownCriterionEqualizerMap, brownCriterionEqualizerObject,
        brownCriterionStabilizerFamily] using
        (wideEqualizer.condition
          (f := brownCriterionStabilizerFamily F
            (brownUniversalElement F X x))
          (Sum.inl s) (Sum.inr PUnit.unit))
    have hsplit : e₀ ≫ ψ ≫ e' = 𝟙 _ := by
      apply he_mono.right_cancellation
      simpa [e₀, s, Category.assoc] using hstab
    calc
      a = 𝟙 _ ≫ a := by simp
      _ = (e₀ ≫ ψ ≫ e') ≫ a := by rw [hsplit]
      _ = e₀ ≫ ψ ≫ (e' ≫ a) := by simp [Category.assoc]
      _ = e₀ ≫ ψ ≫ (e' ≫ b) := by
        simpa [e'] using congrArg (fun q => e₀ ≫ ψ ≫ q)
          (equalizer.condition a b)
      _ = (e₀ ≫ ψ ≫ e') ≫ b := by simp [Category.assoc]
      _ = 𝟙 _ ≫ b := by rw [hsplit]
      _ = b := by simp
  have hbij : ∀ Z : C, Function.Bijective
      ((coyonedaEquiv.symm y').app Z) := fun Z =>
    ⟨hinj Z, hsurj Z⟩
  let e : F.CorepresentableBy
      (brownCriterionEqualizerObject F (brownUniversalElement F X x)) :=
    { homEquiv := fun {Z} =>
        Equiv.ofBijective ((coyonedaEquiv.symm y').app Z) (hbij Z)
      homEquiv_comp := by
        intro Z Z' g f
        change (coyonedaEquiv.symm y').app Z' (f ≫ g) =
          F.map g ((coyonedaEquiv.symm y').app Z f)
        exact (coyonedaEquiv.symm y').naturality_apply g f }
  exact ⟨brownCriterionEqualizerObject F
    (brownUniversalElement F X x), ⟨e⟩⟩

/-- Brown's representability criterion, in Mathlib's covariant terminology. -/
theorem brown_representability_criterion
    {C : Type u} [Category.{v} C] [HasLimits C]
    (F : C ⥤ Type v) [PreservesLimits F]
    {I : Type v} (X : I → C) (x : ∀ i, F.obj (X i))
  (hgen : IsGeneratingFamily F X x) :
    F.IsCorepresentable := by
  obtain ⟨Y, hY⟩ := brown_representability_criterion_corepresentableBy F X x hgen
  exact hY.some.isCorepresentable

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
  let hpres : Nonempty
      (IsLimit (F.mapCone (limit.cone (parallelFamily (brownStabilizerFamily F y))))) :=
    (inferInstance : PreservesLimit (parallelFamily (brownStabilizerFamily F y)) F).preserves
      (limit.isLimit _)
  let c : Cone ((parallelFamily (brownStabilizerFamily F y)) ⋙ F) :=
    { pt := PUnit.{v + 1}
      π :=
        { app := fun j => match j with
          | WalkingParallelFamily.zero => ↾(fun _ => y)
          | WalkingParallelFamily.one => ↾(fun _ => y)
          naturality := by
            intro j k f
            cases f with
            | id => simp
            | line j =>
                rcases j with f | _
                · ext z
                  simpa [brownStabilizerFamily] using f.2.symm
                · simp [brownStabilizerFamily] } }
  refine ⟨hpres.some.lift c PUnit.unit, ?_⟩
  have h := hpres.some.fac c WalkingParallelFamily.zero
  exact congrArg (fun q => q PUnit.unit) h

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
  intro Z g
  obtain ⟨f, hf⟩ := hξ Z g
  refine ⟨e ≫ f, ?_⟩
  change F.map (e ≫ f) y' = g
  rw [F.map_comp]
  change F.map f (F.map e y') = g
  rw [he]
  exact hf

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
  let hpres : Nonempty
      (IsLimit (F.mapCone (limit.cone (parallelPair a b)))) :=
    (inferInstance : PreservesLimit (parallelPair a b) F).preserves
      (limit.isLimit _)
  let c : Cone ((parallelPair a b) ⋙ F) :=
    Cone.ofFork (Fork.ofι (↾(fun _ : PUnit.{v + 1} => y')) (by
      ext z
      exact hab))
  refine ⟨hpres.some.lift c PUnit.unit, ?_⟩
  have h := hpres.some.fac c WalkingParallelPair.zero
  exact congrArg (fun q => q PUnit.unit) h

theorem brown_final_equalizer_argument
    {C : Type u} [Category.{v} C] [HasLimits C]
    (F : C ⥤ Type v) [PreservesLimits F]
    {I : Type v} (X : I → C) (x : ∀ i, F.obj (X i))
    (hξ : ∀ Y : C, Function.Surjective
      ((brownUniversalTransformation F X x).app Y))
    {Z : C} (y' : F.obj (brownEqualizerObject F (brownUniversalElement F X x)))
    (he : F.map (brownEqualizerMap F (brownUniversalElement F X x)) y' =
      brownUniversalElement F X x)
    (a b : brownEqualizerObject F (brownUniversalElement F X x) ⟶ Z)
    (hab : F.map a y' = F.map b y') :
    a = b := by
  obtain ⟨y'', hy''⟩ := exists_brownFinalEqualizerElement F a b y' hab
  obtain ⟨ψ, hψ⟩ := hξ (brownFinalEqualizerObject a b) y''
  rw [brownUniversalTransformation_app_apply] at hψ
  let e₀ := brownEqualizerMap F (brownUniversalElement F X x)
  let e' := brownFinalEqualizerMap a b
  have hs : F.map (ψ ≫ e' ≫ e₀) (brownUniversalElement F X x) =
      brownUniversalElement F X x := by
    rw [F.map_comp, F.map_comp]
    change F.map e₀ (F.map e' (F.map ψ (brownUniversalElement F X x))) =
      brownUniversalElement F X x
    rw [hψ, hy'', he]
  let s : BrownStabilizer F (brownUniversalElement F X x) :=
    ⟨ψ ≫ e' ≫ e₀, hs⟩
  have hstab := brownEqualizerMap_stabilizes F (brownUniversalElement F X x) s
  have hsplit : e₀ ≫ ψ ≫ e' = 𝟙 _ := by
    apply (brownEqualizerMap_mono F (brownUniversalElement F X x)).right_cancellation
    simpa [e₀, s, Category.assoc] using hstab
  calc
    a = 𝟙 _ ≫ a := by simp
    _ = (e₀ ≫ ψ ≫ e') ≫ a := by rw [hsplit]
    _ = e₀ ≫ ψ ≫ (e' ≫ a) := by simp [Category.assoc]
    _ = e₀ ≫ ψ ≫ (e' ≫ b) := by
      rw [brownFinalEqualizerMap_condition a b]
    _ = (e₀ ≫ ψ ≫ e') ≫ b := by simp [Category.assoc]
    _ = 𝟙 _ ≫ b := by rw [hsplit]
    _ = b := by simp

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
  have hξ := brownUniversalTransformation_surjective F X x hgen
  obtain ⟨y', he⟩ :=
    exists_brownEqualizerElement F (brownUniversalElement F X x)
  have hsurj : ∀ Z : C, Function.Surjective
      ((brownEqualizerTransformation F y').app Z) := by
    apply brownEqualizerTransformation_surjective F
      (brownUniversalElement F X x) y'
      (brownEqualizerMap F (brownUniversalElement F X x)) he
    simpa [brownUniversalTransformation] using hξ
  refine ⟨y', ?_, he⟩
  intro Z
  constructor
  · intro a b hab
    apply brown_final_equalizer_argument F X x hξ y' he a b
    change F.map a y' = F.map b y' at hab
    exact hab
  · exact hsurj Z

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
  classical
  cases isEmpty_or_nonempty E with
  | inl hE =>
      letI := hE
      have hr : Set.range f = (∅ : Set (G : Type v)) := by
        ext z
        constructor
        · rintro ⟨e, rfl⟩
          exact isEmptyElim e
        · simp
      rw [hr, Subgroup.closure_empty]
      simp
  | inr hE =>
      letI := hE
      let q : FreeGroup E → Subgroup.closure (Set.range f) := fun w =>
        ⟨FreeGroup.lift f w, by
          rw [← FreeGroup.range_lift_eq_closure]
          exact ⟨w, rfl⟩⟩
      calc
        Cardinal.mk (Subgroup.closure (Set.range f)) ≤ Cardinal.mk (FreeGroup E) := by
          apply Cardinal.mk_le_of_surjective (f := q)
          intro z
          have hz : z.1 ∈ (FreeGroup.lift f).range := by
            rw [FreeGroup.range_lift_eq_closure]
            exact z.2
          rcases hz with ⟨w, hw⟩
          exact ⟨w, Subtype.ext hw⟩
        _ = max (Cardinal.mk E) Cardinal.aleph0 := Cardinal.mk_freeGroup E
        _ = max Cardinal.aleph0 (Cardinal.mk E) := max_comm _ _

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
  change Subgroup.closure (Set.range (FreeGroup.of : E → FreeGroup E)) = ⊤
  exact FreeGroup.closure_range_of E

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
  let F : Iᵒᵖ ⥤ TopCat.{v} ⥤ Type v := D.op ⋙ coyoneda
  letI : PreservesLimits (F.flip) := by
    apply preservesLimits_of_evaluation
    intro k
    change PreservesLimits (coyoneda.obj (D.op.obj k))
    infer_instance
  letI : PreservesLimits (F.flip ⋙ lim) := by
    infer_instance
  apply preservesLimits_of_natIso (limitIsoFlipCompLim F).symm

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
  let q : (Σ i : I, D.obj i) → topologicalHomSubspace D φ := fun z =>
    ⟨topologicalHomFamily D φ z.1 z.2,
      Set.mem_iUnion.2 ⟨z.1, Set.mem_range.2 ⟨z.2, rfl⟩⟩⟩
  apply Cardinal.mk_le_of_surjective (f := q)
  intro z
  have hz := z.2
  change z.1 ∈ ⋃ i, Set.range (topologicalHomFamily D φ i) at hz
  rcases Set.mem_iUnion.1 hz with ⟨i, hi⟩
  rcases Set.mem_range.1 hi with ⟨w, hw⟩
  refine ⟨⟨i, w⟩, ?_⟩
  exact Subtype.ext hw

/- The factorization assertion used to pass from an arbitrary compatible
   family to the bounded subspace family. -/
theorem exists_topologicalHomSubspaceElement {I : Type v} [Category.{v} I]
    (D : I ⥤ TopCat.{v}) {Y : TopCat.{v}}
    (φ : (topologicalHomFunctor D).obj Y) :
    ∃ φ' : (topologicalHomFunctor D).obj (topologicalHomSubspace D φ),
      (topologicalHomFunctor D).map (topologicalHomSubspaceInclusion D φ) φ' = φ := by
  let F : Iᵒᵖ ⥤ TopCat.{v} ⥤ Type v := D.op ⋙ coyoneda
  let S := topologicalHomSubspace D φ
  let c : Cone (F ⋙ (evaluation _ _).obj S) :=
    { pt := PUnit.{v + 1}
      π :=
        { app := fun j => ↾(fun _ => topologicalHomFactor D φ j.unop)
          naturality := by
            intro j k f
            ext z
            change topologicalHomFactor D φ k.unop =
              (F ⋙ (evaluation _ _).obj S).map f
                (topologicalHomFactor D φ j.unop)
            ext w
            have h := congrArg (fun q => q.app Y φ)
              ((limit.cone F).π.naturality f)
            have h' : topologicalHomFamily D φ k.unop =
                (F.map f).app Y (topologicalHomFamily D φ j.unop) := by
              simpa [F, topologicalHomFamily, Category.assoc] using h
            apply Subtype.ext
            change topologicalHomFamily D φ k.unop w =
              topologicalHomFamily D φ j.unop (D.map f.unop w)
            simpa [F] using congrArg (fun g => g w) h' } }
  let φ' := (topologicalHomFunctor_objIso D S).inv
    (limit.lift _ c PUnit.unit)
  refine ⟨φ', ?_⟩
  have hgoal :
      (topologicalHomFunctor_objIso D Y).hom
          ((topologicalHomFunctor D).map (topologicalHomSubspaceInclusion D φ) φ') =
        (topologicalHomFunctor_objIso D Y).hom φ := by
    apply Types.limit_ext' (F ⋙ (evaluation _ _).obj Y)
    intro j
    calc
      (limit.π (F ⋙ (evaluation _ _).obj Y) j)
          ((topologicalHomFunctor_objIso D Y).hom
            ((topologicalHomFunctor D).map (topologicalHomSubspaceInclusion D φ) φ')) =
          (F.obj j).map (topologicalHomSubspaceInclusion D φ)
            ((limit.π F j).app S φ') := by
        calc
          _ = (limit.π F j).app Y
              ((topologicalHomFunctor D).map
                (topologicalHomSubspaceInclusion D φ) φ') := by
            have h := congrArg
              (fun q => q ((topologicalHomFunctor D).map
                (topologicalHomSubspaceInclusion D φ) φ'))
              (limitObjIsoLimitCompEvaluation_hom_π F j Y)
            change
              (limit.π (F ⋙ (evaluation _ _).obj Y) j)
                  ((limitObjIsoLimitCompEvaluation F Y).hom
                    ((limit F).map (topologicalHomSubspaceInclusion D φ) φ')) =
                (limit.π F j).app Y
                  ((limit F).map (topologicalHomSubspaceInclusion D φ) φ')
            simpa only [ConcreteCategory.comp_apply] using h
          _ = _ := by
            have h := congrArg (fun q => q φ')
              ((limit.π F j).naturality
                (topologicalHomSubspaceInclusion D φ))
            exact h
      _ = (F.obj j).map (topologicalHomSubspaceInclusion D φ)
          ((limit.π (F ⋙ (evaluation _ _).obj S) j)
            (limit.lift _ c PUnit.unit)) := by
        congr 1
        have h := congrArg (fun q => q (limit.lift _ c PUnit.unit))
          (limitObjIsoLimitCompEvaluation_inv_π_app F j S)
        change
          (limit.π F j).app S
              ((limitObjIsoLimitCompEvaluation F S).inv
                (limit.lift _ c PUnit.unit)) =
            (limit.π (F ⋙ (evaluation _ _).obj S) j)
              (limit.lift _ c PUnit.unit)
        simpa only [ConcreteCategory.comp_apply] using h
      _ = (F.obj j).map (topologicalHomSubspaceInclusion D φ)
          (c.π.app j PUnit.unit) := by
        rw [limit.lift_π_apply]
      _ = (limit.π F j).app Y φ := by
        dsimp only [c, F]
        change topologicalHomFactor D φ j.unop ≫
            topologicalHomSubspaceInclusion D φ =
          topologicalHomFamily D φ j.unop
        exact topologicalHomFactor_comp_inclusion D φ j.unop
      _ = (limit.π (F ⋙ (evaluation _ _).obj Y) j)
          ((topologicalHomFunctor_objIso D Y).hom φ) := by
        have h := congrArg (fun q => q φ)
          (limitObjIsoLimitCompEvaluation_hom_π F j Y)
        simpa only [F, topologicalHomFunctor_objIso,
          ConcreteCategory.comp_apply] using h.symm
  have hgoal' := congrArg (fun q => (topologicalHomFunctor_objIso D Y).inv q) hgoal
  simpa using hgoal'

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
  letI : G.IsRightAdjoint :=
    isRightAdjoint_of_preservesLimits_of_solutionSetCondition G hG
  exact (Adjunction.ofIsRightAdjoint G).corepresentableBy Y |>.isCorepresentable

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
