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
  intro h
  let f : TopCat.discrete.obj Bool ⟶ TopCat.trivial.obj Bool :=
    @TopCat.ofHom Bool Bool ⊥ ⊤
      (@ContinuousMap.mk Bool Bool ⊥ ⊤ id (by
        exact continuous_bot))
  let : topologicalSpaceForgetful.ReflectsIsomorphisms := h
  have : IsIso (topologicalSpaceForgetful.map f) := by
    rw [isIso_iff_bijective]
    constructor
    · intro x y hxy
      exact hxy
    · intro y
      exact ⟨y, rfl⟩
  have : IsIso f :=
    Functor.ReflectsIsomorphisms.reflects topologicalSpaceForgetful f
  let e : TopCat.trivial.obj Bool ≃ₜ TopCat.discrete.obj Bool :=
    (TopCat.homeoOfIso (asIso f)).symm
  have he : e.toFun = id := by
    funext x
    have hx := e.left_inv x
    have he_inv : e.invFun = id := by
      funext y
      rfl
    rw [he_inv] at hx
    exact hx
  have hcont : @Continuous Bool Bool ⊤ ⊥ id := by
    exact he ▸ e.continuous_toFun
  have hopen : @IsOpen Bool ⊤ ({true} : Set Bool) := by
    simpa using (@continuous_discrete_rng Bool Bool ⊤ ⊥
      (discreteTopology_bot Bool)).mp hcont true
  rw [TopologicalSpace.isOpen_top_iff] at hopen
  rcases hopen with hopen | hopen
  · have hmem : true ∈ ({true} : Set Bool) := by simp
    rw [hopen] at hmem
    simp at hmem
  · have hmem : false ∈ ({true} : Set Bool) := by
      rw [hopen]
      simp
    simp at hmem

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
  intro hF
  let F := pointwiseDiscretePresheaf (X := TopCat.discrete.obj ℕ) A
  have hsheaf : TopCat.Presheaf.IsSheaf F :=
    (categoryValuedSheaf_iff_isSheaf F).1 hF
  have hFcover :=
    (TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover _).mp hsheaf
  let U : ℕ → Opens (TopCat.discrete.obj ℕ) :=
    fun n => ⟨({n} : Set ℕ), isOpen_discrete _⟩
  have hU : iSup U = ⊤ := by
    apply le_antisymm le_top
    intro n hn
    refine Opens.mem_iSup.mpr ⟨(n : ℕ), ?_⟩
    change (n : ℕ) ∈ ({(n : ℕ)} : Set ℕ)
    rfl
  have hset := pointwiseDiscretePresheaf_underlying_isSheaf
    (X := TopCat.discrete.obj ℕ) A
  have hsetcover :=
    (TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover _).mp hset
  obtain ⟨hlim⟩ := hsetcover U
  let K := F.mapCone (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U).op
  have htop :=
    (TopCat.nonempty_isLimit_iff_eq_induced K (by
      convert hlim using 1 <;> rfl)).1 (hFcover U)
  change (⊥ : TopologicalSpace (↑K.pt)) = _ at htop
  have hPiRHS :
      @Pi.topologicalSpace (↑(iSup U)) (fun x : ↑(iSup U) => A x.1) (fun _ => ⊥) ≤
        ⨅ j, TopologicalSpace.induced
          (⇑(ConcreteCategory.hom (K.π.app j)))
          (((ObjectProperty.ι (fun V => ∃ i, V ≤ U i)).op ⋙ F).obj j).str := by
    apply le_iInf
    intro j
    let V : TopCat.Presheaf.SheafCondition.OpensLeCover U := j.unop
    obtain ⟨i, hVi⟩ := V.property
    have hfin_set : (V.obj : Set (TopCat.discrete.obj ℕ)).Finite := by
      apply (Set.finite_singleton i).subset
      exact hVi
    let : Finite V.obj := hfin_set.to_subtype
    let : ∀ y : V.obj, TopologicalSpace (A y.1) := fun _ => ⊥
    let : ∀ y : V.obj, DiscreteTopology (A y.1) :=
      fun _ => discreteTopology_bot _
    have hPiDisc :
        @Pi.topologicalSpace V.obj (fun y : V.obj => A y.1) (fun _ => ⊥) = ⊥ := by
      exact @DiscreteTopology.eq_bot (∀ y : V.obj, A y.1)
        (@Pi.topologicalSpace V.obj (fun y : V.obj => A y.1) (fun _ => ⊥))
        inferInstance
    let : ∀ x : (↑(iSup U)), TopologicalSpace (A x.1) := fun _ => ⊥
    apply (continuous_iff_le_induced).1
    change @Continuous (∀ x : (↑(iSup U)), A x.1)
      (∀ y : V.obj, A y.1)
      (@Pi.topologicalSpace (↑(iSup U)) (fun x : ↑(iSup U) => A x.1) (fun _ => ⊥))
      ⊥ (fun f y => f ⟨y.1,
        (le_iSup U V.property.choose) (V.property.choose_spec y.2)⟩)
    rw [← hPiDisc]
    exact continuous_pi (fun y => continuous_apply _)
  have hPiBot :
      @Pi.topologicalSpace (↑(iSup U)) (fun x : ↑(iSup U) => A x.1) (fun _ => ⊥) ≤
        (⊥ : TopologicalSpace (↑K.pt)) := by
    rw [htop]
    exact hPiRHS
  classical
  let : ∀ x : (↑(iSup U)), TopologicalSpace (A x.1) := fun _ => ⊥
  have hPiEq :
      @Pi.topologicalSpace (↑(iSup U)) (fun x : ↑(iSup U) => A x.1) (fun _ => ⊥) =
        (⊥ : TopologicalSpace (↑K.pt)) :=
    le_antisymm hPiBot bot_le
  let f : ∀ x : (↑(iSup U)), A x.1 := fun x => (hA x.1).choose
  have hsingle :
      @IsOpen (∀ x : (↑(iSup U)), A x.1)
        (@Pi.topologicalSpace (↑(iSup U)) (fun x : ↑(iSup U) => A x.1) (fun _ => ⊥))
        ({f} : Set (∀ x : (↑(iSup U)), A x.1)) := by
    rw [hPiEq]
    change @IsOpen (∀ x : (↑(iSup U)), A x.1)
      (⊥ : TopologicalSpace (∀ x : (↑(iSup U)), A x.1))
      ({f} : Set (∀ x : (↑(iSup U)), A x.1))
    exact @isOpen_discrete (∀ x : (↑(iSup U)), A x.1)
      (⊥ : TopologicalSpace (∀ x : (↑(iSup U)), A x.1))
      (discreteTopology_bot _) _
  obtain ⟨I, u, hI, hsubset⟩ :=
    (isOpen_pi_iff.mp hsingle) f (by simp)
  have hIfin :
      ((fun x : (↑(iSup U)) => x.1) '' (I : Set (↑(iSup U)))).Finite :=
    Set.Finite.image (fun x : (↑(iSup U)) => x.1) I.finite_toSet
  obtain ⟨n, hnmem, hnnot⟩ :=
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finite hIfin
  have hnSup : ((n : ℕ) : ↑(TopCat.discrete.obj ℕ)) ∈ iSup U := by
    rw [hU]
    exact Set.mem_univ _
  let x : (↑(iSup U)) := ⟨(n : ↑(TopCat.discrete.obj ℕ)), hnSup⟩
  have hxnot : x ∉ (I : Set (↑(iSup U))) := by
    intro hx
    apply hnnot
    exact ⟨x, hx, rfl⟩
  obtain ⟨a, b, hab⟩ := hA x.1
  by_cases hfa : f x = a
  · let g : ∀ y : (↑(iSup U)), A y.1 := Function.update f x b
    have hg : g ∈ (I : Set (↑(iSup U))).pi u := by
      change ∀ y, y ∈ (I : Set (↑(iSup U))) → g y ∈ u y
      intro y hy
      have hyx : y ≠ x := by
        intro hyxeq
        apply hxnot
        simpa [hyxeq] using hy
      rw [show g y = f y by
        exact Function.update_of_ne hyx _ _]
      exact (hI y hy).2
    have hgf : g = f := by
      exact hsubset hg
    have hfb : b = f x := by
      have h := congrFun hgf x
      simpa [g] using h
    exact hab (hfa.symm.trans hfb.symm)
  · let g : ∀ y : (↑(iSup U)), A y.1 := Function.update f x a
    have hg : g ∈ (I : Set (↑(iSup U))).pi u := by
      change ∀ y, y ∈ (I : Set (↑(iSup U))) → g y ∈ u y
      intro y hy
      have hyx : y ≠ x := by
        intro hyxeq
        apply hxnot
        simpa [hyxeq] using hy
      rw [show g y = f y by
        exact Function.update_of_ne hyx _ _]
      exact (hI y hy).2
    have hgf : g = f := by
      exact hsubset hg
    apply hfa
    have h := congrFun hgf x
    simpa [g] using h.symm

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
  let F := pointwiseProductTopologyPresheaf A
  apply (categoryValuedSheaf_iff_isSheaf F).2
  rw [TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover]
  intro ι U
  have hset :
      TopCat.Presheaf.IsSheaf
        (Formalization.Books.Sheaves.Unit05.underlyingPresheaf
          (CategoryTheory.forget TopCat) F) := by
    change (TopCat.presheafToTypes (TopCat.discrete.obj ℕ) A).IsSheaf
    exact TopCat.Presheaf.toTypes_isSheaf _ _
  have hsetcover :=
    (TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover _).mp hset
  obtain ⟨hlim⟩ := hsetcover U
  refine (TopCat.nonempty_isLimit_iff_eq_induced
    (F.mapCone (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U).op) (by
      convert hlim using 1 <;> rfl)).2 ?_
  change @Pi.topologicalSpace (↑(iSup U)) (fun x : ↑(iSup U) => A x.1) (fun _ => ⊥) = _
  apply le_antisymm
  · apply le_iInf
    intro V
    apply (continuous_iff_le_induced).1
    have hVU : V.unop.obj ≤ iSup U :=
      V.unop.2.choose_spec.trans (le_iSup U V.unop.2.choose)
    change Continuous (pointwiseProductTopologyRestriction
      (X := TopCat.discrete.obj ℕ) A hVU)
    exact (pointwiseProductTopologyRestriction
      (X := TopCat.discrete.obj ℕ) A hVU).hom.continuous
  · let : ∀ x : (↑(iSup U)), TopologicalSpace (A x.1) := fun _ => ⊥
    have hpi :
        Pi.topologicalSpace = ⨅ x : (↑(iSup U)),
          TopologicalSpace.induced
            (fun s : (∀ x : (↑(iSup U)), A x.1) => s x)
            (⊥ : TopologicalSpace (A x.1)) := by
      have h := (induced_to_pi (X := ∀ x : (↑(iSup U)), A x.1)
        (A := fun x : (↑(iSup U)) => A x.1)
        (id : (∀ x : (↑(iSup U)), A x.1) → ∀ x : (↑(iSup U)), A x.1))
      simpa only [induced_id, id_eq] using h
    calc
      _ ≤ ⨅ x : (↑(iSup U)),
          TopologicalSpace.induced
            (fun s : (∀ x : (↑(iSup U)), A x.1) => s x)
            (⊥ : TopologicalSpace (A x.1)) := by
        apply le_iInf
        intro x
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.2
        let V : TopCat.Presheaf.SheafCondition.OpensLeCover U :=
          ⟨U i, ⟨i, le_rfl⟩⟩
        refine le_trans (iInf_le _ (Opposite.op V)) ?_
        let g :=
          (F.mapCone (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U).op).π.app
            (Opposite.op V)
        have hxV : x.1 ∈ V.obj := by
          change x.1 ∈ U i
          exact hi
        let : ∀ y : V.obj, TopologicalSpace (A y.1) := fun _ => ⊥
        have hevaltop :
            (((ObjectProperty.ι (fun V => ∃ i, V ≤ U i)).op ⋙ F).obj
              (Opposite.op V)).str ≤
              TopologicalSpace.induced
                (fun s : (((ObjectProperty.ι (fun V => ∃ i, V ≤ U i)).op ⋙ F).obj
                  (Opposite.op V)) => s ⟨x.1, hxV⟩)
                (⊥ : TopologicalSpace (A x.1)) := by
          apply (continuous_iff_le_induced).1
          change @Continuous (∀ y : V.obj, A y.1) (A x.1)
            (@Pi.topologicalSpace V.obj (fun y : V.obj => A y.1) (fun _ => ⊥))
            ⊥ (fun s => s ⟨x.1, hxV⟩)
          exact continuous_apply _
        refine le_trans (induced_mono hevaltop) ?_
        rw [induced_compose]
        apply le_of_eq
        congr 2
      _ = _ := hpi.symm

end Formalization.Books.Sheaves.Unit09
