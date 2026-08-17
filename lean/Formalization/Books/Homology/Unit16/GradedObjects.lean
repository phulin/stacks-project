import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# Graded objects

This file formalizes the graded-object constructions in Chapter 16. The basic
category is Mathlib's CategoryTheory.GradedObject, so an object is a family
G → C and a morphism is a family of component morphisms.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u w

namespace Formalization.Books.Homology.Unit16

/-! ### The category of graded objects -/

/-- A morphism of graded objects is determined by all of its components. -/
theorem gradedHom_ext_iff {G : Type w} {C : Type u} [Category.{v} C]
    {A B : GradedObject G C} (f g : A ⟶ B) :
    f = g ↔ ∀ i, f i = g i := by
  constructor
  · intro h
    subst h
    intro i
    rfl
  · exact fun h => GradedObject.hom_ext f g h

/-! ### The direct-sum/pair presentation -/

/--
A graded object together with a chosen countable direct-sum decomposition of a
total object. This is the categorical version of a pair (A, k) in the
book: component i is k^i A and decomposition identifies their coproduct
with the total object carrier.
-/
structure GradedPair (C : Type u) [Category.{v} C] [HasCountableCoproducts C] where
  carrier : C
  component : GradedObject ℤ C
  decomposition : (∐ component) ≅ carrier

namespace GradedPair

variable {C : Type u} [Category.{v} C] [HasCountableCoproducts C]

/-- Morphisms of graded pairs, including the component maps that make the
preservation of each summand explicit. -/
structure Hom (A B : GradedPair C) where
  carrierHom : A.carrier ⟶ B.carrier
  componentHom : ∀ i, A.component i ⟶ B.component i
  comm : ∀ i,
    Sigma.ι A.component i ≫ A.decomposition.hom ≫ carrierHom =
      componentHom i ≫ Sigma.ι B.component i ≫ B.decomposition.hom

@[ext]
theorem hom_ext {A B : GradedPair C} (f g : Hom A B)
    (hcarrier : f.carrierHom = g.carrierHom)
    (hcomponent : ∀ i, f.componentHom i = g.componentHom i) :
    f = g := by
  cases f with
  | mk fcarrier fcomponent fcomm =>
    cases g with
    | mk gcarrier gcomponent gcomm =>
      simp only [Hom.mk.injEq] at *
      exact ⟨hcarrier, funext hcomponent⟩

instance : Category (GradedPair C) where
  Hom := Hom
  id A :=
    { carrierHom := 𝟙 A.carrier
      componentHom := fun i => 𝟙 (A.component i)
      comm := by intro i; simp }
  comp := fun {A B D} f g =>
    { carrierHom := f.carrierHom ≫ g.carrierHom
      componentHom := fun i => f.componentHom i ≫ g.componentHom i
      comm := by
        intro i
        calc
          Sigma.ι A.component i ≫ A.decomposition.hom ≫
                (f.carrierHom ≫ g.carrierHom) =
              (Sigma.ι A.component i ≫ A.decomposition.hom ≫ f.carrierHom) ≫
                g.carrierHom := by simp [Category.assoc]
          _ = (f.componentHom i ≫ Sigma.ι B.component i ≫
                B.decomposition.hom) ≫ g.carrierHom := by rw [f.comm i]
          _ = f.componentHom i ≫
                (Sigma.ι B.component i ≫ B.decomposition.hom ≫ g.carrierHom) := by
                simp [Category.assoc]
          _ = f.componentHom i ≫
                (g.componentHom i ≫ Sigma.ι D.component i ≫ D.decomposition.hom) := by
                rw [g.comm i]
          _ = (f.componentHom i ≫ g.componentHom i) ≫
                Sigma.ι D.component i ≫ D.decomposition.hom := by
                simp [Category.assoc] }
  id_comp := by
    intro A B f
    apply GradedPair.hom_ext
    · simp
    · intro i
      simp
  comp_id := by
    intro A B f
    apply GradedPair.hom_ext
    · simp
    · intro i
      simp
  assoc := by
    intro A B D E f g h
    apply GradedPair.hom_ext
    · simp [Category.assoc]
    · intro i
      simp [Category.assoc]

end GradedPair

/-- The direct-sum pair presentation is equivalent to the family presentation. -/
theorem gradedPairEquivalence_exists (C : Type u) [Category.{v} C]
    [HasCountableCoproducts C] :
    Nonempty (GradedObject ℤ C ≌ GradedPair C) := by
  sorry

noncomputable def gradedPairEquivalence (C : Type u) [Category.{v} C]
    [HasCountableCoproducts C] : GradedObject ℤ C ≌ GradedPair C :=
  Classical.choice (gradedPairEquivalence_exists C)

/-! ### Direct sums and examples without direct sums -/

/-- The totalization functor for a graded object, under the source's
countable-coproduct hypothesis. -/
def gradedTotal (C : Type u) [Category.{v} C] [HasCountableCoproducts C] :
    GradedObject ℤ C ⥤ C where
  obj A := ∐ A
  map := fun {A B} f =>
    show (∐ A) ⟶ ∐ B from Limits.Sigma.map (fun i : ℤ => f i)
  map_id := by
    intro A
    exact Limits.Sigma.map_id (f := A)
  map_comp := by
    intro A B D f g
    simpa using
      (Limits.Sigma.map_comp_map (fun i : ℤ => f i) (fun i : ℤ => g i)).symm

/-- The finite-dimensional graded-vector-space example from the chapter. -/
abbrev FiniteDimensionalGradedObjects (k : Type u) [Field k] :=
  GradedObject ℤ (FGModuleCat k)

/-- The property that every component of a graded vector space is finite-dimensional. -/
def HasFiniteDimensionalGradedPieces (k : Type u) [Field k]
    (A : GradedObject ℤ (ModuleCat k)) : Prop :=
  ∀ i, Module.Finite k (A i)

/-! ### Abelian structure -/

/-- The preadditive structure on graded objects, transferred from the equivalent
discrete functor category. -/
noncomputable instance gradedObjectPreadditive {C : Type u} [Category.{v} C]
    [Preadditive C] : Preadditive (GradedObject ℤ C) :=
  Preadditive.ofFullyFaithful
    (piEquivalenceFunctorDiscrete ℤ C).fullyFaithfulFunctor

/-- Finite products of graded objects are computed componentwise. -/
instance gradedObjectHasFiniteProducts {C : Type u} [Category.{v} C]
    [HasFiniteProducts C] : HasFiniteProducts (GradedObject ℤ C) where
  out _n :=
    Adjunction.hasLimitsOfShape_of_equivalence
      (piEquivalenceFunctorDiscrete ℤ C).functor

/-- If C is abelian, then the category of integer-graded objects in C is abelian. -/
noncomputable instance gradedObjectAbelian {C : Type u} [Category.{v} C]
    [Abelian C] : Abelian (GradedObject ℤ C) :=
  abelianOfEquivalence (piEquivalenceFunctorDiscrete ℤ C).functor

/-- The kernel of a graded morphism has the componentwise kernels. -/
theorem graded_kernel_component_iso_exists {C : Type u} [Category.{v} C] [Abelian C]
    {A B : GradedObject ℤ C} (f : A ⟶ B) (i : ℤ) :
    Nonempty ((kernel f) i ≅ kernel (f i)) := by
  sorry

noncomputable def graded_kernel_component_iso {C : Type u} [Category.{v} C] [Abelian C]
    {A B : GradedObject ℤ C} (f : A ⟶ B) (i : ℤ) :
    (kernel f) i ≅ kernel (f i) :=
  Classical.choice (graded_kernel_component_iso_exists f i)

/-- The cokernel of a graded morphism has the componentwise cokernels. -/
theorem graded_cokernel_component_iso_exists {C : Type u} [Category.{v} C] [Abelian C]
    {A B : GradedObject ℤ C} (f : A ⟶ B) (i : ℤ) :
    Nonempty ((cokernel f) i ≅ cokernel (f i)) := by
  sorry

noncomputable def graded_cokernel_component_iso {C : Type u} [Category.{v} C] [Abelian C]
    {A B : GradedObject ℤ C} (f : A ⟶ B) (i : ℤ) :
    (cokernel f) i ≅ cokernel (f i) :=
  Classical.choice (graded_cokernel_component_iso_exists f i)

/-- The image/coimage comparison for a graded morphism is an isomorphism. -/
theorem graded_coimage_image_comparison_isIso {C : Type u} [Category.{v} C]
    [Abelian C] {A B : GradedObject ℤ C} (f : A ⟶ B) :
    IsIso (Abelian.coimageImageComparison f) := by
  sorry

/-! ### The warning about non-exact countable direct sums -/

/-- Exactness of the totalization functor, expressed using Mathlib's exact-functor property. -/
def gradedTotalIsExact (C : Type u) [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] : Prop :=
  exactFunctor (GradedObject ℤ C) C (gradedTotal C)

/-- A package for the warning that countable direct sums need not be exact.
The textbook gives the opposite of abelian sheaves on R as an example. -/
structure NonExactGradedTotalExample where
  carrier : Type u
  category : Category.{u} carrier
  abelian : letI := category; Abelian carrier
  coproducts : letI := category; HasCountableCoproducts carrier
  not_exact :
    letI := category
    letI := abelian
    letI := coproducts
    ¬ gradedTotalIsExact carrier

/-- The existence assertion behind the chapter's non-exact-countable-sum warning. -/
theorem exists_nonExactGradedTotalExample :
    Nonempty (NonExactGradedTotalExample.{u}) := by
  sorry

/-- The pair-category kernel candidate obtained by taking the direct sum of
the componentwise kernels. -/
noncomputable def gradedPairComponentwiseKernel {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C] {A B : GradedPair C} (f : A ⟶ B) :
    GradedPair C where
  carrier := ∐ fun i => kernel (f.componentHom i)
  component := fun i => kernel (f.componentHom i)
  decomposition := Iso.refl _

/-- The kernel morphism for the componentwise pair-kernel candidate. -/
noncomputable def gradedPairComponentwiseKernelι {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C] {A B : GradedPair C} (f : A ⟶ B) :
    gradedPairComponentwiseKernel f ⟶ A where
  carrierHom :=
    Limits.Sigma.map (fun i => kernel.ι (f.componentHom i)) ≫ A.decomposition.hom
  componentHom := fun i => kernel.ι (f.componentHom i)
  comm := by
    intro i
    simp only [gradedPairComponentwiseKernel, Iso.refl_hom, Category.id_comp]
    simpa only [Category.assoc] using
      congrArg (fun h => h ≫ A.decomposition.hom)
        (Limits.Sigma.ι_map (fun j => kernel.ι (f.componentHom j)) i)

/-- Zero morphisms on graded pairs are componentwise zero morphisms. -/
instance gradedPairHasZeroMorphisms {C : Type u} [Category.{v} C]
    [HasCountableCoproducts C] [HasZeroMorphisms C] :
    HasZeroMorphisms (GradedPair C) where
  zero X Y := ⟨
    { carrierHom := 0
      componentHom := fun _ => 0
      comm := by intro i; simp }⟩
  comp_zero := by
    intro X Y f Z
    apply GradedPair.hom_ext
    · change f.carrierHom ≫ 0 = 0
      simp
    · intro i
      change f.componentHom i ≫ 0 = 0
      simp
  zero_comp := by
    intro X Y Z f
    apply GradedPair.hom_ext
    · change 0 ≫ f.carrierHom = 0
      simp
    · intro i
      change 0 ≫ f.componentHom i = 0
      simp

/-- The universal-property formulation of being a kernel in the pair category. -/
def IsGradedPairKernel {C : Type u} [Category.{v} C]
    [HasCountableCoproducts C] [HasZeroMorphisms C]
    {A B K : GradedPair C} (f : A ⟶ B) (ι : K ⟶ A) : Prop :=
  ι ≫ f = 0 ∧
    ∀ {X : GradedPair C} (g : X ⟶ A), g ≫ f = 0 →
      ∃ h : X ⟶ K, h ≫ ι = g ∧
        ∀ h' : X ⟶ K, h' ≫ ι = g → h' = h

/-- In the pair presentation, the kernel is the direct sum of the componentwise kernels. -/
theorem gradedPairKernel_is_componentwise {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C] {A B : GradedPair C} (f : A ⟶ B) :
    IsGradedPairKernel f (gradedPairComponentwiseKernelι f) := by
  sorry

/-! ### Shifts and homogeneous maps -/

/-- Translation of a G-graded object by g, with the chapter's convention
(A[g])^(g₀) = A^(g + g₀). -/
def gradedShift {G : Type w} [AddCommGroup G] (C : Type u) [Category.{v} C] (g : G) :
    GradedObject G C ⥤ GradedObject G C :=
  GradedObject.comap C (fun g₀ => g + g₀)

@[simp]
theorem gradedShift_obj_apply {G : Type w} [AddCommGroup G] {C : Type u}
    [Category.{v} C] (g : G) (A : GradedObject G C) (g₀ : G) :
    (gradedShift C g).obj A g₀ = A (g + g₀) :=
  rfl

@[simp]
theorem gradedShift_map_apply {G : Type w} [AddCommGroup G] {C : Type u}
    [Category.{v} C] (g : G) {A B : GradedObject G C} (f : A ⟶ B) (g₀ : G) :
    (gradedShift C g).map f g₀ = f (g + g₀) :=
  rfl

/-- A homogeneous map of integer degree k is a map into the k-shift. -/
abbrev HomogeneousGradedMap {C : Type u} [Category.{v} C] (k : ℤ)
    (A B : GradedObject ℤ C) : Type _ :=
  A ⟶ (gradedShift C k).obj B

/-- The source's hom-space identity is the canonical reindexing equivalence. -/
theorem homIntoShiftEquiv_exists {C : Type u} [Category.{v} C] (k : ℤ)
    (A B : GradedObject ℤ C) :
    Nonempty (HomogeneousGradedMap k A B ≃
      ((gradedShift C (-k)).obj A ⟶ B)) := by
  sorry

noncomputable def homIntoShiftEquiv {C : Type u} [Category.{v} C] (k : ℤ)
    (A B : GradedObject ℤ C) :
    HomogeneousGradedMap k A B ≃
      ((gradedShift C (-k)).obj A ⟶ B) :=
  Classical.choice (homIntoShiftEquiv_exists k A B)

/-! ### General gradings and bigradings -/

/-- For any indexing type G, GradedObject G C is the category of G-graded
objects; this is the canonical Mathlib family category rather than a parallel definition. -/
abbrev GGradedObjects (G : Type w) (C : Type u) [Category.{v} C] :=
  GradedObject G C

/-- The shift functors for an abelian-group grading. -/
abbrev GGradedShift {G : Type w} [AddCommGroup G] (C : Type u) [Category.{v} C]
    (g : G) := gradedShift C g

/-- A bigraded object is a ℤ × ℤ-graded object. -/
abbrev BigradedObject (C : Type u) [Category.{v} C] :=
  GradedObject (ℤ × ℤ) C

/-- The shift of a bigraded object by (a,b). -/
abbrev bigradedShift (C : Type u) [Category.{v} C] (a b : ℤ) :
    BigradedObject C ⥤ BigradedObject C :=
  gradedShift C (a, b)

@[simp]
theorem bigradedShift_component {C : Type u} [Category.{v} C]
    (a b p q : ℤ) (A : BigradedObject C) :
    (bigradedShift C a b).obj A (p, q) = A (a + p, b + q) :=
  rfl

/-- A map of bidegree (a,b) is a map into the (a,b)-shift. -/
abbrev BidegreeMorphism {C : Type u} [Category.{v} C] (a b : ℤ)
    (A B : BigradedObject C) : Type _ :=
  A ⟶ (bigradedShift C a b).obj B

end Formalization.Books.Homology.Unit16
