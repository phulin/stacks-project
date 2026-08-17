import Formalization.Books.Dga.Unit25.Totalization
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.CategoryTheory.GradedObject

/-!
# The graded category of graded objects

The homogeneous Hom type is written with the two indices used in the book.
The equality proof in the dependent product is the Lean representation of the
condition `p + q = n`; in particular this is a product of component Hom types,
not a direct sum. -/

noncomputable section

open CategoryTheory
open DirectSum
open scoped DirectSum

universe u v w

namespace Formalization.Books.Dga.Unit25

variable {B : Type u} [Category.{v} B]
  [Formalization.Books.Homology.Unit03.AdditiveCategory B]

abbrev GradedDegreePair (n : ℤ) :=
  {pq : ℤ × ℤ // pq.1 + pq.2 = n}

/-- A degree-`n` map of graded objects, displayed as the family
`f_{p,q} : A^{-q} ⟶ B^p` for `p + q = n`. -/
abbrev GradedObjectHomogeneous
    (A C : CategoryTheory.GradedObject ℤ B) (n : ℤ) :=
  ∀ s : GradedDegreePair n, (A (-s.1.2) ⟶ C s.1.1)

instance gradedObjectHomogeneousAddCommGroup
    (A C : CategoryTheory.GradedObject ℤ B) (n : ℤ) :
    AddCommGroup (GradedObjectHomogeneous A C n) := inferInstance

instance gradedObjectHomogeneousIntModule
    (A C : CategoryTheory.GradedObject ℤ B) (n : ℤ) :
    Module ℤ (GradedObjectHomogeneous A C n) := inferInstance

/-- The component formula for composition of homogeneous graded-object maps. -/
def gradedObjectHomogeneousComponent
    {A C : CategoryTheory.GradedObject ℤ B} {n : ℤ}
    (f : GradedObjectHomogeneous A C n) (p q : ℤ) (h : p + q = n) :
    A (-q) ⟶ C p :=
  f ⟨(p, q), h⟩

def gradedObjectHomogeneousComp
    {A C E : CategoryTheory.GradedObject ℤ B} (i j : ℤ)
    (f : GradedObjectHomogeneous A C i)
    (g : GradedObjectHomogeneous C E j) :
    GradedObjectHomogeneous A E (i + j) :=
  fun s =>
    gradedObjectHomogeneousComponent f (-(j - s.1.1)) s.1.2 (by omega) ≫
      gradedObjectHomogeneousComponent g s.1.1 (j - s.1.1) (by omega)

/-- The degree-zero identity family. -/
def gradedObjectHomogeneousId
    (A : CategoryTheory.GradedObject ℤ B) :
  GradedObjectHomogeneous A A 0 :=
  fun s => eqToHom (congrArg A (by omega))

omit [Formalization.Books.Homology.Unit03.AdditiveCategory B] in
theorem gradedObjectHomogeneousComp_component
    {A C E : CategoryTheory.GradedObject ℤ B} {i j : ℤ}
    (f : GradedObjectHomogeneous A C i)
    (g : GradedObjectHomogeneous C E j)
    (p r : ℤ) (h : p + r = i + j) :
    gradedObjectHomogeneousComponent (gradedObjectHomogeneousComp i j f g) p r h =
      gradedObjectHomogeneousComponent f (-(j - p)) r (by omega) ≫
        gradedObjectHomogeneousComponent g p (j - p) (by omega) :=
  by simp [gradedObjectHomogeneousComp, gradedObjectHomogeneousComponent]

/-- The totalization specification for graded objects.  The subtype pins the
homogeneous composition and identity in the generic totalization data to the
component formulas above. -/
def GradedObjectTotalizationSpec : Type _ :=
  {D : TotalGradedCategoryData ℤ (CategoryTheory.GradedObject ℤ B)
      (fun A C n => GradedObjectHomogeneous A C n) //
    (∀ A, D.homogeneous_id A = gradedObjectHomogeneousId A) ∧
    (∀ {A C E : CategoryTheory.GradedObject ℤ B} {i j : ℤ}
      (f : GradedObjectHomogeneous A C i)
      (g : GradedObjectHomogeneous C E j),
      D.homogeneous_comp f g = gradedObjectHomogeneousComp i j f g)}

/-- The direct-sum extension of the componentwise composition exists. -/
theorem gradedObjectTotalizationSpec_nonempty :
    Nonempty (GradedObjectTotalizationSpec (B := B)) := by
  sorry

noncomputable def gradedObjectTotalizationSpec :
    GradedObjectTotalizationSpec (B := B) :=
  Classical.choice (gradedObjectTotalizationSpec_nonempty (B := B))

noncomputable def gradedObjectCategoryData :
    TotalGradedCategoryData ℤ (CategoryTheory.GradedObject ℤ B)
      (fun A C n => GradedObjectHomogeneous A C n) :=
  (gradedObjectTotalizationSpec (B := B)).1

abbrev GradedObjectCategory :=
  TotalGradedObject (gradedObjectCategoryData (B := B))

def gradedObjectCategoryObject
    (A : CategoryTheory.GradedObject ℤ B) : GradedObjectCategory (B := B) :=
  ⟨A⟩

@[simp] theorem gradedObjectCategoryObject_underlying
    (A : CategoryTheory.GradedObject ℤ B) :
    (gradedObjectCategoryObject (B := B) A).underlying = A :=
  rfl

@[instance_reducible] noncomputable def gradedObjectGradedCategory :
    GradedCategory ℤ (GradedObjectCategory (B := B)) := inferInstance

theorem gradedObjectTotalization_homogeneous_id (A : CategoryTheory.GradedObject ℤ B) :
    (gradedObjectCategoryData (B := B)).homogeneous_id A =
      gradedObjectHomogeneousId A :=
  (gradedObjectTotalizationSpec (B := B)).2.1 A

theorem gradedObjectTotalization_homogeneous_comp
    {A C E : CategoryTheory.GradedObject ℤ B} {i j : ℤ}
    (f : GradedObjectHomogeneous A C i)
    (g : GradedObjectHomogeneous C E j) :
    (gradedObjectCategoryData (B := B)).homogeneous_comp f g =
      gradedObjectHomogeneousComp i j f g :=
  (gradedObjectTotalizationSpec (B := B)).2.2 f g

/-! The degree-zero category is the usual pointwise category of graded
objects, up to the harmless type synonyms used to keep the two category
structures distinct. -/

theorem gradedObject_degree_zero_recovers_graded_objects :
    Nonempty
      (DegreeZero (gradedObjectGradedCategory (B := B)) ≌
        CategoryTheory.GradedObject ℤ B) := by
  sorry

noncomputable def gradedObject_degree_zero_equivalence :
    DegreeZero (gradedObjectGradedCategory (B := B)) ≌
      CategoryTheory.GradedObject ℤ B :=
  Classical.choice (gradedObject_degree_zero_recovers_graded_objects (B := B))

end Formalization.Books.Dga.Unit25
