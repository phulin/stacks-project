import Formalization.Books.Sheaves.Unit05.PresheavesOfAlgebraicStructures
import Mathlib.Algebra.Category.AlgCat.Limits
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts

/-!
# Sheaves on Spaces, Chapter 9: Sheaves of algebraic structures

This file formalizes the precise statements in `books/sheaves.tex`, lines
679--855.  The equalizer-of-products formulation is Mathlib's canonical
`TopCat.Presheaf.IsSheafEqualizerProducts`; the underlying-presheaf criterion
is the stronger, general statement already provided by
`TopCat.Presheaf.isSheaf_iff_isSheaf_comp`.
-/

namespace Formalization.Books.Sheaves.Unit09

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

universe w v u

/-! ## The equalizer diagram for a category-valued sheaf -/

/-- The product of the sections over the members of an open cover.

This is an alias for Mathlib's canonical product in the equalizer-products
formulation of the sheaf condition.
-/
noncomputable abbrev sheafConditionSectionsProduct
    {C : Type u} [Category.{v} C] [HasProducts.{w} C]
    {X : TopCat.{w}} (F : TopCat.Presheaf C X) (U : ι → Opens X) : C :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens F U

/-- The product of the sections over all pairwise intersections in an open cover. -/
noncomputable abbrev sheafConditionIntersectionProduct
    {C : Type u} [Category.{v} C] [HasProducts.{w} C]
    {X : TopCat.{w}} (F : TopCat.Presheaf C X) (U : ι → Opens X) : C :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.piInters F U

/-- The map restricting a family of sections from the first member of each pair. -/
noncomputable abbrev sheafConditionLeftRestriction
    {C : Type u} [Category.{v} C] [HasProducts.{w} C]
    {X : TopCat.{w}} (F : TopCat.Presheaf C X) (U : ι → Opens X) :
    sheafConditionSectionsProduct F U ⟶ sheafConditionIntersectionProduct F U :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes F U

/-- The map restricting a family of sections from the second member of each pair. -/
noncomputable abbrev sheafConditionRightRestriction
    {C : Type u} [Category.{v} C] [HasProducts.{w} C]
    {X : TopCat.{w}} (F : TopCat.Presheaf C X) (U : ι → Opens X) :
    sheafConditionSectionsProduct F U ⟶ sheafConditionIntersectionProduct F U :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes F U

/-- The restriction map from sections over the union to sections over each member. -/
noncomputable abbrev sheafConditionRestriction
    {C : Type u} [Category.{v} C] [HasProducts.{w} C]
    {X : TopCat.{w}} (F : TopCat.Presheaf C X) (U : ι → Opens X) :
    F.obj (op (iSup U)) ⟶ sheafConditionSectionsProduct F U :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.res F U

/-- The equalizer diagram displayed in the source. -/
noncomputable abbrev sheafConditionDiagram
    {C : Type u} [Category.{v} C] [HasProducts.{w} C]
    {X : TopCat.{w}} (F : TopCat.Presheaf C X) (U : ι → Opens X) :
    WalkingParallelPair ⥤ C :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.diagram F U

/-- The canonical fork whose point is `F` on the union of the cover. -/
noncomputable abbrev sheafConditionFork
    {C : Type u} [Category.{v} C] [HasProducts.{w} C]
    {X : TopCat.{w}} (F : TopCat.Presheaf C X) (U : ι → Opens X) :
    Fork (sheafConditionLeftRestriction F U) (sheafConditionRightRestriction F U) :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.fork F U

/-- A presheaf valued in a category with products, in the source's
equalizer-of-products sense of sheaf. -/
abbrev CategoryValuedSheaf
    {C : Type u} [Category.{v} C] [HasProducts.{w} C]
    {X : TopCat.{w}} (F : TopCat.Presheaf C X) : Prop :=
  TopCat.Presheaf.IsSheafEqualizerProducts F

/-- The equalizer-of-products definition is equivalent to Mathlib's intrinsic
sheaf condition. -/
theorem categoryValuedSheaf_iff_isSheaf
    {C : Type u} [Category.{v} C] [HasProducts.{w} C]
    {X : TopCat.{w}} (F : TopCat.Presheaf C X) :
    CategoryValuedSheaf F ↔ TopCat.Presheaf.IsSheaf F :=
  (TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts F).symm

/-! ## Passing to the underlying presheaf of sets -/

/-- The source's faithful-limit-reflecting criterion for sheaves of structures.

The explicit faithfulness assumption is retained because it is part of the
textbook hypothesis, although Mathlib's stronger categorical theorem only
needs preservation of limits and reflection of isomorphisms.
-/
theorem categoryValuedSheaf_iff_underlying_isSheaf
    {C : Type u} [Category.{v} C]
    (G : C ⥤ Type v) [G.Faithful] [HasLimits C]
    [PreservesLimits G]
    [G.ReflectsIsomorphisms] {X : TopCat.{v}} (F : TopCat.Presheaf C X) :
    CategoryValuedSheaf F ↔
      TopCat.Presheaf.IsSheaf
        (Formalization.Books.Sheaves.Unit05.underlyingPresheaf G F) := by
  rw [categoryValuedSheaf_iff_isSheaf]
  exact TopCat.Presheaf.isSheaf_iff_isSheaf_comp G F

/-- The forward use of the criterion: an underlying sheaf gives a sheaf of
objects in the original category. -/
theorem categoryValuedSheaf_of_underlying_isSheaf
    {C : Type u} [Category.{v} C]
    (G : C ⥤ Type v) [G.Faithful] [HasLimits C]
    [PreservesLimits G]
    [G.ReflectsIsomorphisms] {X : TopCat.{v}} (F : TopCat.Presheaf C X)
    (hF : TopCat.Presheaf.IsSheaf
      (Formalization.Books.Sheaves.Unit05.underlyingPresheaf G F)) :
    CategoryValuedSheaf F :=
  (categoryValuedSheaf_iff_underlying_isSheaf G F).2 hF

/-- For a functor to types, reflection of isomorphisms is exactly the
source's condition that a morphism is an isomorphism whenever its underlying
function is bijective. -/
theorem reflectsIsomorphisms_iff_bijective
    {C : Type u} [Category.{v} C] (G : C ⥤ Type w)
    [G.ReflectsIsomorphisms] {A B : C} (f : A ⟶ B) :
    IsIso f ↔ Function.Bijective (G.map f) := by
  exact (isIso_iff_of_reflects_iso f G).symm.trans (isIso_iff_bijective _)

/-! ## Standard algebraic examples -/

/-- The forgetful functor from topological spaces to types. -/
abbrev topologicalSpaceForgetful : TopCat ⥤ Type :=
  CategoryTheory.forget TopCat

/-- The topological-space forgetful functor is faithful and preserves limits. -/
theorem topologicalSpaceForgetful_properties :
    topologicalSpaceForgetful.Faithful ∧
      PreservesLimits topologicalSpaceForgetful := by
  exact ⟨inferInstance, inferInstance⟩

/-- The forgetful functor from topological spaces does not reflect
isomorphisms. -/
theorem topologicalSpaceForgetful_not_reflectsIsomorphisms :
    ¬ topologicalSpaceForgetful.ReflectsIsomorphisms := by
  sorry

/-- The presheaf of real-valued continuous functions, with its canonical
commutative-ring and hence real-algebra structure on every section. -/
def realContinuousFunctionPresheaf (X : TopCat) :
    TopCat.Presheaf CommRingCat X :=
  TopCat.presheafToTopCommRing X (TopCommRingCat.of ℝ)

/-- The sections of `realContinuousFunctionPresheaf` are the continuous
maps from the open set to `ℝ`. -/
abbrev realContinuousFunctionSections (X : TopCat) (U : Opens X) :=
  (realContinuousFunctionPresheaf X).obj (op U)

/-- The pointwise scalar action makes every section an `ℝ`-algebra. -/
instance realContinuousFunctionSections_algebra (X : TopCat) (U : Opens X) :
    Algebra ℝ (realContinuousFunctionSections X U) := by
  change Algebra ℝ
    ((Opens.toTopCat X).obj U ⟶
      (CategoryTheory.forget₂ TopCommRingCat TopCat).obj (TopCommRingCat.of ℝ))
  let i : ℝ →+*
      ((Opens.toTopCat X).obj U ⟶
        (CategoryTheory.forget₂ TopCommRingCat TopCat).obj (TopCommRingCat.of ℝ)) :=
    { toFun := fun r =>
        TopCat.ofHom (ContinuousMap.C (α := (Opens.toTopCat X).obj U) r)
      map_one' := by
        ext x
        rfl
      map_mul' r s := by
        ext x
        rfl
      map_zero' := by
        ext x
        rfl
      map_add' r s := by
        ext x
        rfl }
  exact i.toAlgebra

/-- Restriction of real-valued continuous functions is an algebra homomorphism. -/
def realContinuousFunctionRestrictionAlgHom (X : TopCat) {U V : Opens X} (h : V ≤ U) :
    realContinuousFunctionSections X U →ₐ[ℝ] realContinuousFunctionSections X V where
  toFun f := (Opens.toTopCat X).map h.hom ≫ f
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    apply TopCat.ext
    intro x
    rfl

/-- The continuous-function presheaf, presented as a presheaf of real algebras. -/
def realContinuousFunctionAlgebraPresheaf (X : TopCat) :
    TopCat.Presheaf (AlgCat ℝ) X where
  obj U := AlgCat.of ℝ (realContinuousFunctionSections X U.unop)
  map {U V} f := AlgCat.ofHom (realContinuousFunctionRestrictionAlgHom X f.unop.le)
  map_id U := by
    apply AlgCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply AlgCat.hom_ext
    ext x
    rfl

/-- The underlying presheaf of the real continuous-function presheaf is a
sheaf of sets. -/
theorem realContinuousFunctionPresheaf_underlying_isSheaf (X : TopCat) :
    TopCat.Presheaf.IsSheaf
      (Formalization.Books.Sheaves.Unit05.underlyingPresheaf
        (CategoryTheory.forget CommRingCat) (realContinuousFunctionPresheaf X)) := by
  change (TopCat.presheafToTop X
    ((CategoryTheory.forget₂ TopCommRingCat TopCat).obj (TopCommRingCat.of ℝ))).IsSheaf
  exact (TopCat.sheafToTop
    ((CategoryTheory.forget₂ TopCommRingCat TopCat).obj (TopCommRingCat.of ℝ))).property

/-- The real continuous-function presheaf is a sheaf of commutative rings. -/
theorem realContinuousFunctionPresheaf_isSheaf (X : TopCat) :
    CategoryValuedSheaf (realContinuousFunctionPresheaf X) := by
  exact categoryValuedSheaf_of_underlying_isSheaf
    (CategoryTheory.forget CommRingCat)
    (realContinuousFunctionPresheaf X)
    (realContinuousFunctionPresheaf_underlying_isSheaf X)

/-- The continuous-function presheaf is a sheaf when regarded as a presheaf of
real algebras. -/
theorem realContinuousFunctionAlgebraPresheaf_isSheaf (X : TopCat) :
    CategoryValuedSheaf (realContinuousFunctionAlgebraPresheaf X) := by
  apply categoryValuedSheaf_of_underlying_isSheaf
    (CategoryTheory.forget (AlgCat ℝ))
    (realContinuousFunctionAlgebraPresheaf X)
  change (TopCat.presheafToTop X
    ((CategoryTheory.forget₂ TopCommRingCat TopCat).obj (TopCommRingCat.of ℝ))).IsSheaf
  exact (TopCat.sheafToTop
    ((CategoryTheory.forget₂ TopCommRingCat TopCat).obj (TopCommRingCat.of ℝ))).property

/-! ## The topological-space counterexample -/

/-- The pointwise presheaf `U ↦ ∏ x ∈ U, A x`, with the discrete topology on
each product. -/
def pointwiseDiscretePresheaf {X : TopCat.{w}} (A : X → Type w) :
    TopCat.Presheaf TopCat.{w} X :=
  TopCat.presheafToTypes X A ⋙ TopCat.discrete

/-- “Every fibre has at least two elements”, in the form used by the
topological-space counterexample. -/
def HasAtLeastTwoElements {X : TopCat.{w}} (A : X → Type w) : Prop :=
  ∀ x, ∃ a b : A x, a ≠ b

/-- The underlying pointwise presheaf is a sheaf of sets. -/
theorem pointwiseDiscretePresheaf_underlying_isSheaf
    {X : TopCat.{w}} (A : X → Type w) :
      TopCat.Presheaf.IsSheaf
      (Formalization.Books.Sheaves.Unit05.underlyingPresheaf
        (CategoryTheory.forget TopCat) (pointwiseDiscretePresheaf A)) := by
  change (TopCat.presheafToTypes X A).IsSheaf
  exact TopCat.Presheaf.toTypes_isSheaf X A

/-- If every fibre has at least two elements, the discrete-topology
pointwise presheaf is not a sheaf of topological spaces. -/
theorem pointwiseDiscretePresheaf_not_isSheaf
    (A : ℕ → Type)
    (hA : HasAtLeastTwoElements (X := TopCat.discrete.obj ℕ) A) :
    ¬ CategoryValuedSheaf
      (pointwiseDiscretePresheaf (X := TopCat.discrete.obj ℕ) A) := by
  sorry

/-! ## Replacing the discrete topology by the product topology -/

/-- The product topology on the dependent product of the fibres over an open.
The fibres are given their discrete topologies, as in the source. -/
def pointwiseProductTopologyObject {X : TopCat} (A : X → Type)
    (U : Opens X) : TopCat := by
  letI : ∀ x : X, TopologicalSpace (A x) := fun _ => ⊥
  exact TopCat.of (∀ x : U, A x)

/-- Restriction of a product-topology pointwise section to a smaller open. -/
def pointwiseProductTopologyRestriction {X : TopCat} (A : X → Type)
    {U V : Opens X} (h : V ≤ U) :
    pointwiseProductTopologyObject A U ⟶ pointwiseProductTopologyObject A V := by
  letI : ∀ x : X, TopologicalSpace (A x) := fun _ => ⊥
  exact TopCat.ofHom
    ⟨fun f x => f ⟨x.1, h x.2⟩, continuous_pi (fun x => continuous_apply _)⟩

/-- The pointwise presheaf with the product topology on each section space. -/
def pointwiseProductTopologyPresheaf (A : ℕ → Type) :
    TopCat.Presheaf TopCat (TopCat.discrete.obj ℕ) where
  obj U := pointwiseProductTopologyObject A U.unop
  map {U V} f := pointwiseProductTopologyRestriction A f.unop.le
  map_id U := by
    apply TopCat.ext
    intro x
    rfl
  map_comp f g := by
    apply TopCat.ext
    intro x
    rfl

/-- With the product topology, the pointwise presheaf is a sheaf of
topological spaces. -/
theorem pointwiseProductTopologyPresheaf_isSheaf (A : ℕ → Type) :
    CategoryValuedSheaf (pointwiseProductTopologyPresheaf A) := by
  sorry

end Formalization.Books.Sheaves.Unit09
