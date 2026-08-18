import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories

/-!
# Derived Categories, Chapter 3: the definition of a triangulated category

The chapter uses the standard categorical language for triangles, shifts,
pretriangulated categories, triangulated functors, and homological functors.
Mathlib already provides those interfaces.  This file therefore exposes the
source statements through those canonical declarations and adds only the
source's general `δ`-functor interface, which is not part of Mathlib's generic
triangulated-category API.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Homology.Unit03

universe v u w

namespace Formalization.Books.Derived.Unit03

/-! ## Triangles, shifts, and distinguished triangles -/

/-- The source's triangle is Mathlib's canonical `Pretriangulated.Triangle`. -/
abbrev BookTriangle (C : Type u) [Category.{v} C] [HasShift C ℤ] :=
  CategoryTheory.Pretriangulated.Triangle C

/-- The source's morphism of triangles is Mathlib's canonical structure. -/
abbrev BookTriangleMorphism (C : Type u) [Category.{v} C] [HasShift C ℤ]
    (T₁ T₂ : BookTriangle C) :=
  CategoryTheory.Pretriangulated.TriangleMorphism T₁ T₂

/-- The source's family of shifts is Mathlib's shift by `ℤ`. -/
abbrev BookShift (C : Type u) [Category.{v} C] [HasShift C ℤ] (n : ℤ) : C ⥤ C :=
  CategoryTheory.shiftFunctor C n

/-- The zero shift is the identity functor. -/
noncomputable def shiftZeroIso
    (C : Type u) [Category.{v} C] [HasShift C ℤ] :
    BookShift C 0 ≅ 𝟭 C :=
  CategoryTheory.shiftFunctorZero C ℤ

/-- The chosen shift family has the source's composition isomorphisms. -/
noncomputable def shiftCompositionIso
    (C : Type u) [Category.{v} C] [HasShift C ℤ] (n m : ℤ) :
    BookShift C n ⋙ BookShift C m ≅ BookShift C (n + m) :=
  (CategoryTheory.shiftFunctorAdd C n m).symm

/-- The shift by any integer is an auto-equivalence, with inverse shift by its negation. -/
abbrev shiftAutoequivalence
    (C : Type u) [Category.{v} C] [HasShift C ℤ] (n : ℤ) : C ≌ C :=
  CategoryTheory.shiftEquiv C n

/-- The set of distinguished triangles in a pretriangulated category. -/
abbrev distinguishedTriangleSet
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    Set (BookTriangle C) :=
  distTriang C

/-- The source's pretriangulated-category interface, using Mathlib's TR1--TR3. -/
abbrev BookPretriangulated
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] :=
  CategoryTheory.Pretriangulated C

/-- The source's TR4 interface, using Mathlib's octahedron axiom. -/
abbrev BookTriangulated
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] :=
  CategoryTheory.IsTriangulated C

/-- Shifting a triangle by an integer. -/
def shiftedTriangle
    {C : Type u} [Category.{v} C] [AdditiveCategory C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    (T : BookTriangle C) (n : ℤ) : BookTriangle C :=
  (CategoryTheory.Pretriangulated.Triangle.shiftFunctor C n).obj T

/-- Rotation of a distinguished triangle is distinguished. -/
theorem distinguished_rotate_iff
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : BookTriangle C) :
    T ∈ distinguishedTriangleSet C ↔ T.rotate ∈ distinguishedTriangleSet C :=
  CategoryTheory.Pretriangulated.rotate_distinguished_triangle T

/-- Inverse rotation of a distinguished triangle is distinguished. -/
theorem distinguished_inv_rotate
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : BookTriangle C) (hT : T ∈ distinguishedTriangleSet C) :
    T.invRotate ∈ distinguishedTriangleSet C :=
  CategoryTheory.Pretriangulated.inv_rot_of_distTriang T hT

/-- Every integer shift of a distinguished triangle is distinguished. -/
theorem distinguished_shift
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (T : BookTriangle C) (hT : T ∈ distinguishedTriangleSet C) (n : ℤ) :
    shiftedTriangle T n ∈ distinguishedTriangleSet C :=
  CategoryTheory.Pretriangulated.Triangle.shift_distinguished T hT n

/-- The first two maps of a distinguished triangle compose to zero. -/
theorem distinguished_triangle_comp_zero
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : BookTriangle C) (hT : T ∈ distinguishedTriangleSet C) :
    T.mor₁ ≫ T.mor₂ = 0 :=
  CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂ T hT

/-- The second and third maps of a distinguished triangle compose to zero. -/
theorem distinguished_triangle_comp_zero₂₃
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : BookTriangle C) (hT : T ∈ distinguishedTriangleSet C) :
    T.mor₂ ≫ T.mor₃ = 0 :=
  CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₂₃ T hT

/-- The third map and the shifted first map of a distinguished triangle compose to zero. -/
theorem distinguished_triangle_comp_zero₃₁
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : BookTriangle C) (hT : T ∈ distinguishedTriangleSet C) :
    T.mor₃ ≫ T.mor₁⟦1⟧' = 0 :=
  CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₃₁ T hT

/-- The short complex underlying a distinguished triangle. -/
def distinguishedTriangleShortComplex
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : BookTriangle C) (hT : T ∈ distinguishedTriangleSet C) : ShortComplex C :=
  CategoryTheory.Pretriangulated.shortComplexOfDistTriangle T hT

/-! ## Exact functors and triangulated equivalences -/

section ExactFunctors

variable {C D : Type*} [Category* C] [Category* D]
  [AdditiveCategory C] [AdditiveCategory D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- The source's compatibility condition for a 2-morphism of exact functors. -/
abbrev ExactFunctorMorphism {F F' : C ⥤ D} (a : F ⟶ F')
    [F.CommShift ℤ] [F'.CommShift ℤ] :=
  CategoryTheory.NatTrans.CommShift a ℤ

/-- The distinguished-triangle part of the source's exact-functor definition. -/
theorem exact_functor_map_distinguished (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] (T : BookTriangle C) (hT : T ∈ distinguishedTriangleSet C) :
    F.mapTriangle.obj T ∈ distinguishedTriangleSet D :=
  F.map_distinguished T hT

/-- Exact/triangulated functors are additive. -/
theorem exact_functor_additive (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] : F.Additive := by
  infer_instance

/-- The source's notion of equivalence of triangulated categories. -/
abbrev TriangulatedEquivalence (E : C ≌ D)
    [E.functor.CommShift ℤ] [E.inverse.CommShift ℤ] [E.CommShift ℤ] :=
  CategoryTheory.Equivalence.IsTriangulated E

end ExactFunctors

/-! ## General subcategory inclusions -/

section SubcategoryInclusions

variable {C D : Type*} [Category* C] [Category* D]
  [AdditiveCategory C] [AdditiveCategory D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- A faithful exact functor models the source's possibly non-full pretriangulated subcategory.

Its source distinguished triangles are the set `distTriang D`, and exactness is the
canonical Mathlib condition that their images lie in `distTriang C`. -/
abbrev PreTriangulatedSubcategoryInclusion (ι : D ⥤ C)
    [ι.Faithful] [ι.CommShift ℤ] :=
  CategoryTheory.Functor.IsTriangulated ι

/-- A faithful exact inclusion between triangulated categories models a triangulated subcategory. -/
abbrev TriangulatedSubcategoryInclusion (ι : D ⥤ C)
    [ι.Faithful] [ι.CommShift ℤ] [CategoryTheory.IsTriangulated D]
    [CategoryTheory.IsTriangulated C] :=
  CategoryTheory.Functor.IsTriangulated ι

end SubcategoryInclusions

/-! ## Full triangulated subcategories -/

section Subcategories

variable {C : Type*} [Category* C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Mathlib's canonical object-property interface for a pretriangulated subcategory. -/
abbrev PreTriangulatedSubcategory (P : ObjectProperty C) :=
  CategoryTheory.ObjectProperty.IsTriangulated P

/-- The full-subcategory realization of a source triangulated subcategory. -/
abbrev TriangulatedSubcategory (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C] :=
  CategoryTheory.IsTriangulated P.FullSubcategory

/-- The inclusion of the full triangulated subcategory. -/
def triangulatedSubcategoryInclusion (P : ObjectProperty C) :
    P.FullSubcategory ⥤ C :=
  P.ι

/-- The inclusion of a full triangulated subcategory is an exact functor. -/
theorem triangulatedSubcategory_inclusion_exact (P : ObjectProperty C)
    [P.IsTriangulated] :
    P.ι.IsTriangulated := by
  infer_instance

end Subcategories

/-! ## Homological and cohomological functors -/

section HomologicalFunctors

variable {C A : Type*} [Category* C] [Category* A]
  [AdditiveCategory C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Abelian A]

/-- The source's homological-functor predicate is Mathlib's canonical class. -/
abbrev HomologicalFunctor (H : C ⥤ A) :=
  CategoryTheory.Functor.IsHomological H

/-- The corresponding contravariant functor is homological on the opposite target. -/
abbrev CohomologicalFunctor (H : Cᵒᵖ ⥤ A) :=
  CategoryTheory.Functor.IsHomological H.rightOp

/-- The degree-`n` functor `H^n(X) = H(X[n])`. -/
def homologicalDegree (H : C ⥤ A) (n : ℤ) : C ⥤ A :=
  shiftFunctor C n ⋙ H

/-- Degree zero is canonically isomorphic to the original functor. -/
noncomputable def homologicalDegreeZeroIso (H : C ⥤ A) :
    homologicalDegree H 0 ≅ H :=
  Functor.isoWhiskerRight (shiftFunctorZero C ℤ) H ≪≫ H.leftUnitor

/-- A homological functor is additive. -/
theorem homological_functor_additive (H : C ⥤ A) [H.IsHomological] : H.Additive := by
  infer_instance

/-- The exact five-term window in the long exact sequence of a distinguished triangle. -/
noncomputable def homologyLongExactWindow
    (H : C ⥤ A) [H.ShiftSequence ℤ] (T : BookTriangle C) :
    ComposableArrows A 4 :=
  ComposableArrows.mk₄
    (H.homologySequenceδ T (-1) 0 (by simp))
    ((H.shift 0).map T.mor₁)
    ((H.shift 0).map T.mor₂)
    (H.homologySequenceδ T 0 1 (by simp))

/-- The displayed long-exact window is exact for a homological functor. -/
theorem homologyLongExactWindow_exact
    (H : C ⥤ A) [H.ShiftSequence ℤ] [H.IsHomological]
    (T : BookTriangle C) (hT : T ∈ distinguishedTriangleSet C) :
    (homologyLongExactWindow H T).Exact := by
  change (ComposableArrows.mk₄
    (H.homologySequenceδ T (-1) 0 (by simp))
    ((H.shift 0).map T.mor₁)
    ((H.shift 0).map T.mor₂)
    (H.homologySequenceδ T 0 1 (by simp))).Exact
  exact ComposableArrows.exact_of_δ₀
    (H.homologySequence_exact₁ T hT (-1) 0 (by simp)).exact_toComposableArrows
    (ComposableArrows.exact_of_δ₀
      (H.homologySequence_exact₂ T hT 0).exact_toComposableArrows
      (H.homologySequence_exact₃ T hT 0 1 (by simp)).exact_toComposableArrows)

end HomologicalFunctors

/-! ## δ-functors -/

section DeltaFunctors

variable {A D : Type*} [Category* A] [Category* D] [Abelian A]
  [AdditiveCategory D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [CategoryTheory.IsTriangulated D]

/--
The source's `δ`-functor data: a functor from an abelian category to a
triangulated category, a connecting morphism for every short exact sequence,
distinguished image triangles, and naturality for morphisms of short exact
sequences.
-/
structure DeltaFunctor (F : A ⥤ D) [CategoryTheory.IsTriangulated D] where
  delta : ∀ (S : ShortComplex A), S.ShortExact →
    @Quiver.Hom D (inferInstance : Quiver D) (F.obj S.X₃)
      ((shiftFunctor D (1 : ℤ)).obj (F.obj S.X₁))
  distinguished : ∀ (S : ShortComplex A) (hS : S.ShortExact),
    Triangle.mk (F.map S.f) (F.map S.g) (delta S hS) ∈
      distTriang D
  naturality : ∀ {S₁ S₂ : ShortComplex A} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact),
    F.map φ.τ₃ ≫ delta S₂ h₂ =
      delta S₁ h₁ ≫ (shiftFunctor D (1 : ℤ)).map (F.map φ.τ₁)

/-- The distinguished triangle assigned by a `δ`-functor to a short exact sequence. -/
def DeltaFunctor.imageTriangle (F : A ⥤ D) (G : DeltaFunctor F) (S : ShortComplex A)
    (hS : S.ShortExact) : Triangle D :=
  Triangle.mk (F.map S.f) (F.map S.g) (G.delta S hS)

theorem DeltaFunctor.imageTriangle_distinguished (F : A ⥤ D) (G : DeltaFunctor F)
  (S : ShortComplex A) (hS : S.ShortExact) :
    DeltaFunctor.imageTriangle F G S hS ∈ distTriang D := by
  exact G.distinguished S hS

theorem DeltaFunctor.delta_naturality (F : A ⥤ D) (G : DeltaFunctor F)
    {S₁ S₂ : ShortComplex A} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) :
    F.map φ.τ₃ ≫ G.delta S₂ h₂ =
      G.delta S₁ h₁ ≫ (shiftFunctor D (1 : ℤ)).map (F.map φ.τ₁) := by
  exact G.naturality φ h₁ h₂

end DeltaFunctors

end Formalization.Books.Derived.Unit03
