import Formalization.Books.Dga.Unit25.GradedModules
import Mathlib.CategoryTheory.Equivalence

/-!
# Shift functors and graded totalization

The first structure below is the source's strict collection of shifts on an
`R`-linear category.  The totalized category uses `Hom(X,Y[n])` as its
degree-`n` homogeneous Hom type.  The construction theorem is left as a
proposition proof, while all interfaces and the resulting definitions are
explicit.
-/

noncomputable section

open CategoryTheory
open DirectSum
open scoped DirectSum

universe u v w

namespace Formalization.Books.Dga.Unit25

/-- A strict family of `R`-linear shift functors. -/
structure LinearShiftFamily (R : Type u) (C : Type v)
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C] where
  shift : ℤ → C ⥤ C
  additive : ∀ n, Functor.Additive (shift n)
  linear : ∀ n, Functor.Linear R (shift n)
  shift_comp : ∀ n m, shift m ⋙ shift n = shift (n + m)
  shift_zero : shift 0 = 𝟭 C

namespace LinearShiftFamily

variable {R : Type u} {C : Type v}
  [CommRing R] [Category.{w} C] [Preadditive C]
  [CategoryTheory.Linear R C]
  (S : LinearShiftFamily R C)

/-- The degree-`n` homogeneous Hom type in the shift totalization. -/
abbrev homogeneous (X Y : C) (n : ℤ) : Type w :=
  (X ⟶ (S.shift n).obj Y)

instance homogeneousAddCommGroup (X Y : C) (n : ℤ) :
    AddCommGroup (homogeneous S X Y n) := inferInstance

instance homogeneousModule (X Y : C) (n : ℤ) :
    Module R (homogeneous S X Y n) := inferInstance

/-- The componentwise composition in the shift totalization. -/
def homogeneousComp {X Y Z : C} (i j : ℤ)
    (f : homogeneous S X Y i) (g : homogeneous S Y Z j) :
    homogeneous S X Z (i + j) :=
  f ≫ (S.shift i).map g ≫
    eqToHom (congrArg (fun F : C ⥤ C => F.obj Z) (S.shift_comp i j))

/-- The degree-zero identity in the shift totalization. -/
def homogeneousId (X : C) : homogeneous S X X 0 :=
  eqToHom (congrArg (fun F : C ⥤ C => F.obj X) S.shift_zero).symm

theorem homogeneousComp_component {X Y Z : C} {i j : ℤ}
    (f : homogeneous S X Y i) (g : homogeneous S Y Z j) :
    homogeneousComp S i j f g =
      f ≫ (S.shift i).map g ≫
        eqToHom (congrArg (fun F : C ⥤ C => F.obj Z) (S.shift_comp i j)) :=
  rfl

/-- The totalization specification for a shift family. -/
def TotalizationSpec : Type _ :=
  {D : TotalGradedCategoryData R C (homogeneous S) //
    (∀ X, D.homogeneous_id X = homogeneousId S X) ∧
    (∀ {X Y Z : C} {i j : ℤ}
      (f : homogeneous S X Y i) (g : homogeneous S Y Z j),
      D.homogeneous_comp f g = homogeneousComp S i j f g)}

theorem totalizationSpec_nonempty : Nonempty (TotalizationSpec S) := by
  sorry

noncomputable def totalizationSpec : TotalizationSpec S :=
  Classical.choice (totalizationSpec_nonempty S)

noncomputable def categoryData : TotalGradedCategoryData R C (homogeneous S) :=
  (totalizationSpec S).1

abbrev GradedCategory := TotalGradedObject (categoryData S)

def categoryObject (X : C) : GradedCategory S := ⟨X⟩

@[instance_reducible] noncomputable def gradedCategory :
    Formalization.Books.Dga.Unit25.GradedCategory R (GradedCategory S) :=
  inferInstance

theorem categoryData_homogeneous_id (X : C) :
    (categoryData S).homogeneous_id X = homogeneousId S X :=
  (totalizationSpec S).2.1 X

theorem categoryData_homogeneous_comp {X Y Z : C} {i j : ℤ}
    (f : homogeneous S X Y i) (g : homogeneous S Y Z j) :
    (categoryData S).homogeneous_comp f g = homogeneousComp S i j f g :=
  (totalizationSpec S).2.2 f g

theorem degree_zero_recovers :
    Nonempty (DegreeZero (gradedCategory S) ≌ C) := by
  sorry

noncomputable def degree_zero_equivalence : DegreeZero (gradedCategory S) ≌ C :=
  Classical.choice (degree_zero_recovers S)

end LinearShiftFamily

/-! ## Graded-module shift isomorphisms -/

/-- A degree shift isomorphism between two internal graded modules.  The
`total` equivalence is compatible with the component equivalences, so this
records an isomorphism of graded modules rather than only a family of
set-theoretic bijections. -/
structure GradedModuleShiftIso (R : Type u)
    {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (G : GradedModuleData R M ℤ) (H : GradedModuleData R N ℤ)
    (n : ℤ) where
  total : M ≃ₗ[R] N
  component : ∀ i, G.component i ≃ₗ[R] H.component (i + n)
  component_coe : ∀ i (x : G.component i),
    total (x : M) = (component i x : N)

/-- A graded category equipped with strict shifts and the Hom-shift
isomorphisms required in the source remark. -/
structure GradedShiftFamily (R : Type u) (C : Type v)
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C] [GradedCategory R C] where
  shift : ℤ → C ⥤ C
  graded : ∀ n, GradedFunctor R (shift n)
  shift_comp : ∀ n m, shift m ⋙ shift n = shift (n + m)
  shift_zero : shift 0 = 𝟭 C
  hom_shift : ∀ (X Y : C) (n : ℤ),
    GradedModuleShiftIso R
      (GradedCategory.hom X ((shift n).obj Y))
      (GradedCategory.hom X Y) n
  hom_shift_comp_pre : ∀ {X Y Z : C} (n : ℤ)
    (f : X ⟶ Y) (g : Y ⟶ (shift n).obj Z),
    (hom_shift X Z n).total (f ≫ g) =
      f ≫ (hom_shift Y Z n).total g
  hom_shift_comp_post : ∀ {X Y Z : C} (n : ℤ)
    (f : X ⟶ (shift n).obj Y) (g : Y ⟶ Z),
    (hom_shift X Z n).total (f ≫ (shift n).map g) =
      (hom_shift X Y n).total f ≫ g

namespace GradedFunctor

variable {R : Type u} {C D : Type v}
  [CommRing R] [Category.{w} C] [Category.{w} D]
  [Preadditive C] [Preadditive D]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [GradedCategory R C] [GradedCategory R D]
  {F : C ⥤ D} (G : GradedFunctor R F)

/-- Restrict a graded functor to the degree-zero categories. -/
def degreeZero : DegreeZero (inferInstance : GradedCategory R C) ⥤
    DegreeZero (inferInstance : GradedCategory R D) where
  obj X := DegreeZero.of (inferInstance : GradedCategory R D)
    (F.obj (DegreeZero.obj (inferInstance : GradedCategory R C) X))
  map f :=
    ⟨F.map f.1, G.map_component f⟩
  map_id := by
    intro X
    apply Subtype.ext
    change F.map (𝟙 X.down) = 𝟙 (F.obj X.down)
    exact F.map_id _
  map_comp := by
    intro X Y Z f g
    apply Subtype.ext
    change F.map (f.1 ≫ g.1) = F.map f.1 ≫ F.map g.1
    exact F.map_comp _ _

theorem degreeZero_additive : Functor.Additive (G.degreeZero) := by
  constructor
  intro X Y f g
  apply Subtype.ext
  change F.map (f.1 + g.1) = F.map f.1 + F.map g.1
  exact G.additive.map_add

theorem degreeZero_linear : Functor.Linear R (G.degreeZero) := by
  constructor
  intro X Y f r
  apply Subtype.ext
  change F.map (r • f.1) = r • F.map f.1
  exact G.linear.map_smul f.1 r

end GradedFunctor

namespace GradedShiftFamily

variable {R : Type u} {C : Type v}
  [CommRing R] [Category.{w} C] [Preadditive C]
  [CategoryTheory.Linear R C] [GradedCategory R C]
  (S : GradedShiftFamily R C)

def IsDegreeZeroShiftRestriction
    (S : GradedShiftFamily R C)
    (T : LinearShiftFamily R (DegreeZero (inferInstance : GradedCategory R C))) : Prop :=
  ∀ (n : ℤ) (X : DegreeZero (inferInstance : GradedCategory R C)),
    (T.shift n).obj X =
      DegreeZero.of (inferInstance : GradedCategory R C)
        ((S.shift n).obj X.down)

theorem degree_zero_shift_family_nonempty :
    Nonempty
      {T : LinearShiftFamily R (DegreeZero (inferInstance : GradedCategory R C)) //
        IsDegreeZeroShiftRestriction S T} := by
  sorry

noncomputable def degree_zero_shift_family :
    LinearShiftFamily R (DegreeZero (inferInstance : GradedCategory R C)) :=
  (Classical.choice (degree_zero_shift_family_nonempty S)).1

theorem degree_zero_shift_family_restricts :
    IsDegreeZeroShiftRestriction S (degree_zero_shift_family S) :=
  (Classical.choice (degree_zero_shift_family_nonempty S)).2

theorem reconstructs_from_degree_zero :
    Nonempty
      (C ≌ LinearShiftFamily.GradedCategory (degree_zero_shift_family S)) := by
  sorry

end GradedShiftFamily

/-- The inherited shift family on a totalization, including its action on
objects. -/
structure InheritedGradedShiftFamily
    {R : Type u} {C : Type v}
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C]
    (S : LinearShiftFamily R C) where
  family : GradedShiftFamily R (LinearShiftFamily.GradedCategory S)
  object_shift : ∀ (n : ℤ) (X : LinearShiftFamily.GradedCategory S),
    (family.shift n).obj X =
      LinearShiftFamily.categoryObject S ((S.shift n).obj X.underlying)

theorem shift_totalization_inherits_graded_shifts
    {R : Type u} {C : Type v}
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C]
    (S : LinearShiftFamily R C) :
    Nonempty (InheritedGradedShiftFamily S) := by
  sorry

noncomputable def shift_totalization_graded_shifts
    {R : Type u} {C : Type v}
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C]
    (S : LinearShiftFamily R C) :
    InheritedGradedShiftFamily S :=
  Classical.choice (shift_totalization_inherits_graded_shifts S)

end Formalization.Books.Dga.Unit25
