import Formalization.Books.Derived.Unit06.Quotients

/-!
# Derived Categories, Chapter 40: admissible subcategories

The source's full subcategories are represented by Mathlib's canonical
`ObjectProperty` interface.  Orthogonals, distinguished decomposition
triangles, adjunctions of inclusions, and Verdier quotient functors are kept
as explicit source-facing predicates and interfaces below.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit04
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit03
open Formalization.Books.Homology.Unit03

universe v u

namespace Formalization.Books.Derived.Unit40

section AdmissibleSubcategories

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-! ## Orthogonals and distinguished decompositions -/

/- A full subcategory is represented by an object property; its canonical
   full subcategory is `P.FullSubcategory`. -/

/- The source's notation `Hom(X, Y) = 0` is represented by the established
   `HomIsZero` predicate, namely that every morphism from `X` to `Y` is zero. -/

/-- The right orthogonal of a full subcategory. -/
def rightOrthogonal (P : ObjectProperty C) : ObjectProperty C :=
  fun X => ∀ (A : C), P A → HomIsZero A X

/-- The left orthogonal of a full subcategory. -/
def leftOrthogonal (P : ObjectProperty C) : ObjectProperty C :=
  fun X => ∀ (A : C), P A → HomIsZero X A

/-- A distinguished triangle decomposing `X` into a `P`-part and a `Q`-part. -/
def HasTriangleDecomposition
    (P Q : ObjectProperty C) (X : C) : Prop :=
  ∃ (A B : C) (f : A ⟶ X) (g : X ⟶ B)
    (h : B ⟶ A⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C ∧ P A ∧ Q B

/-- A distinguished triangle of the form used for a right adjoint. -/
def HasRightDecomposition (P : ObjectProperty C) (X : C) : Prop :=
  HasTriangleDecomposition P (rightOrthogonal P) X

/-- A distinguished triangle of the form used for a left adjoint. -/
def HasLeftDecomposition (P : ObjectProperty C) (X : C) : Prop :=
  HasTriangleDecomposition (leftOrthogonal P) P X

/-! ## The two preliminary orthogonality lemmas -/

/-- The right-orthogonality criterion for a distinguished triangle.

The map in the second condition is the map induced by the first arrow of
the triangle on representable morphism spaces. -/
theorem pre_prepare_adjoint
    (P : ObjectProperty C) (hP : P.IsStableUnderShift ℤ)
    [CategoryTheory.IsTriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) :
    rightOrthogonal P T.obj₃ ↔
      ∀ (A : C), P A →
        Function.Bijective (fun f : A ⟶ T.obj₁ => f ≫ T.mor₁) := by
  sorry

/-- The left-orthogonality criterion dual to `pre_prepare_adjoint`. -/
theorem pre_prepare_adjoint_dual
    (P : ObjectProperty C) (hP : P.IsStableUnderShift ℤ)
    [CategoryTheory.IsTriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) :
    leftOrthogonal P T.obj₁ ↔
      ∀ (B : C), P B →
        Function.Bijective (fun f : T.obj₃ ⟶ B => T.mor₂ ≫ f) := by
  sorry

/-! ## Orthogonals are triangulated and saturated -/

/-- Both orthogonals are strictly full, saturated, and triangulated. -/
theorem orthogonal_triangulated
    (P : ObjectProperty C) (hP : P.IsStableUnderShift ℤ)
    [CategoryTheory.IsTriangulated C] :
    ((rightOrthogonal P).IsClosedUnderIsomorphisms ∧
        IsSaturated (rightOrthogonal P) ∧
        (rightOrthogonal P).IsTriangulated) ∧
      ((leftOrthogonal P).IsClosedUnderIsomorphisms ∧
        IsSaturated (leftOrthogonal P) ∧
        (leftOrthogonal P).IsTriangulated) := by
  sorry

/-! ## Closure of adjoint decompositions -/

/-- Right-adjoint decompositions satisfy two-out-of-three for triangles. -/
theorem prepare_adjoint_two_out_of_three
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) :
    (HasRightDecomposition P T.obj₁ ∧
        HasRightDecomposition P T.obj₂ →
          HasRightDecomposition P T.obj₃) ∧
      (HasRightDecomposition P T.obj₁ ∧
        HasRightDecomposition P T.obj₃ →
          HasRightDecomposition P T.obj₂) ∧
      (HasRightDecomposition P T.obj₂ ∧
        HasRightDecomposition P T.obj₃ →
          HasRightDecomposition P T.obj₁) := by
  sorry

/-- Right-adjoint decompositions are closed under binary direct sums. -/
theorem prepare_adjoint_biproduct
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    {X Y : C} (hX : HasRightDecomposition P X)
    (hY : HasRightDecomposition P Y) :
    HasRightDecomposition P (X ⊞ Y) := by
  sorry

/-- Left-adjoint decompositions satisfy two-out-of-three for triangles. -/
theorem prepare_adjoint_dual_two_out_of_three
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) :
    (HasLeftDecomposition P T.obj₁ ∧
        HasLeftDecomposition P T.obj₂ →
          HasLeftDecomposition P T.obj₃) ∧
      (HasLeftDecomposition P T.obj₁ ∧
        HasLeftDecomposition P T.obj₃ →
          HasLeftDecomposition P T.obj₂) ∧
      (HasLeftDecomposition P T.obj₂ ∧
        HasLeftDecomposition P T.obj₃ →
          HasLeftDecomposition P T.obj₁) := by
  sorry

/-- Left-adjoint decompositions are closed under binary direct sums. -/
theorem prepare_adjoint_dual_biproduct
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    {X Y : C} (hX : HasLeftDecomposition P X)
    (hY : HasLeftDecomposition P Y) :
    HasLeftDecomposition P (X ⊞ Y) := by
  sorry

/-! ## Adjoints of inclusions -/

/-- The inclusion of `P` has a right adjoint. -/
def HasRightAdjoint (P : ObjectProperty C) : Prop :=
  ∃ (v : C ⥤ P.FullSubcategory), Nonempty (P.ι ⊣ v)

/-- The inclusion of `P` has a left adjoint. -/
def HasLeftAdjoint (P : ObjectProperty C) : Prop :=
  ∃ (v : C ⥤ P.FullSubcategory), Nonempty (v ⊣ P.ι)

/-- A right adjoint of the inclusion is equivalent to right decompositions. -/
theorem right_adjoint_iff_decomposition
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C] :
    HasRightAdjoint P ↔ ∀ X : C, HasRightDecomposition P X := by
  sorry

/-- A right adjoint makes the subcategory saturated. -/
theorem right_adjoint_saturated
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasRightAdjoint P) :
    IsSaturated P := by
  sorry

/-- Under strict fullness, a right-admissible subcategory is the left
orthogonal of its right orthogonal. -/
theorem right_adjoint_eq_left_orthogonal
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasRightAdjoint P)
    (hstrict : P.IsClosedUnderIsomorphisms) :
    P = leftOrthogonal (rightOrthogonal P) := by
  sorry

/-- A left adjoint of the inclusion is equivalent to left decompositions. -/
theorem left_adjoint_iff_decomposition
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C] :
    HasLeftAdjoint P ↔ ∀ X : C, HasLeftDecomposition P X := by
  sorry

/-- A left adjoint makes the subcategory saturated. -/
theorem left_adjoint_saturated
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasLeftAdjoint P) :
    IsSaturated P := by
  sorry

/-- Under strict fullness, a left-admissible subcategory is the right
orthogonal of its left orthogonal. -/
theorem left_adjoint_eq_right_orthogonal
    (P : ObjectProperty C) [P.IsTriangulated]
    [CategoryTheory.IsTriangulated C]
    (hP : HasLeftAdjoint P)
    (hstrict : P.IsClosedUnderIsomorphisms) :
    P = rightOrthogonal (leftOrthogonal P) := by
  sorry

/-! ## Right, left, and two-sided admissibility -/

/-- A strictly full triangulated subcategory with a right adjoint inclusion. -/
def RightAdmissible (P : ObjectProperty C) : Prop :=
  P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧ HasRightAdjoint P

/-- A strictly full triangulated subcategory with a left adjoint inclusion. -/
def LeftAdmissible (P : ObjectProperty C) : Prop :=
  P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧ HasLeftAdjoint P

/-- A subcategory which is both right and left admissible. -/
def TwoSidedAdmissible (P : ObjectProperty C) : Prop :=
  RightAdmissible P ∧ LeftAdmissible P

/-- Right admissibility can equivalently be expressed by decompositions. -/
theorem right_admissible_iff_decomposition
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C] :
    RightAdmissible P ↔
      P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧
        (∀ X : C, HasRightDecomposition P X) := by
  sorry

/-- Left admissibility can equivalently be expressed by decompositions. -/
theorem left_admissible_iff_decomposition
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C] :
    LeftAdmissible P ↔
      P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧
        (∀ X : C, HasLeftDecomposition P X) := by
  sorry

/-! ## Canonicality of the right-adjoint triangle -/

/-- Two right-adjoint decomposition triangles over the same object are
isomorphic by a triangle isomorphism whose middle component is the identity. -/
theorem right_admissible_decomposition_iso
    (P : ObjectProperty C) (hP : RightAdmissible P)
    [CategoryTheory.IsTriangulated C]
    {X A A' B B' : C}
    {f : A ⟶ X} {g : X ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    {f' : A' ⟶ X} {g' : X ⟶ B'} {h' : B' ⟶ A'⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hT' : Triangle.mk f' g' h' ∈ distTriang C)
    (hA : P A) (hB : rightOrthogonal P B)
    (hA' : P A') (hB' : rightOrthogonal P B') :
    ∃ e : Triangle.mk f g h ≅ Triangle.mk f' g' h',
      e.hom.hom₂ = 𝟙 X := by
  sorry

/-! ## The summary proposition -/

/-- The three equivalent conditions for an admissible pair. -/
def AdmissiblePairConditionOne
    (A B : ObjectProperty C) : Prop :=
  RightAdmissible A ∧ B = rightOrthogonal A

def AdmissiblePairConditionTwo
    (A B : ObjectProperty C) : Prop :=
  LeftAdmissible B ∧ A = leftOrthogonal B

def AdmissiblePairConditionThree
    (A B : ObjectProperty C) : Prop :=
  (∀ (X Y : C), A X → B Y → HomIsZero X Y) ∧
    (∀ X : C, HasTriangleDecomposition A B X)

/-- The quotient equivalences and adjoint factorizations in the summary. -/
def AdmissiblePairConclusion
    (A B : ObjectProperty C) : Prop :=
    Functor.IsEquivalence (A.ι ⋙ quotientFunctor B) ∧
    Functor.IsEquivalence (B.ι ⋙ quotientFunctor A) ∧
    (∃ (v : quotientCategory B ⥤ A.FullSubcategory),
      Nonempty (A.ι ⊣ quotientFunctor B ⋙ v)) ∧
    (∃ (u : quotientCategory A ⥤ B.FullSubcategory),
      Nonempty (quotientFunctor A ⋙ u ⊣ B.ι))

/-- The source's equivalence of conditions and its quotient/adjoint
conclusions for an admissible pair. -/
theorem summarize_admissible
    (A B : ObjectProperty C) [CategoryTheory.IsTriangulated C] :
    (AdmissiblePairConditionOne A B ↔
      AdmissiblePairConditionTwo A B) ∧
      (AdmissiblePairConditionTwo A B ↔
        AdmissiblePairConditionThree A B) ∧
      (AdmissiblePairConditionOne A B → AdmissiblePairConclusion A B) := by
  sorry

end AdmissibleSubcategories

end Formalization.Books.Derived.Unit40
