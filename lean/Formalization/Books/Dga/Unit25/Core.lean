import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Differential Graded Algebra, Chapter 25: Graded categories

The source uses graded modules internally: a graded module is a module together
with a direct-sum decomposition into its homogeneous pieces.  The declarations
in this file use Mathlib's `DirectSum.Decomposition` for that decomposition and
Mathlib's `CategoryTheory.Linear` and `Functor.Linear` interfaces for the
linear parts of the definitions.
-/

noncomputable section

open CategoryTheory
open DirectSum
open scoped DirectSum TensorProduct

universe u v w

namespace Formalization.Books.Dga.Unit25

/-! ## Graded modules and graded categories -/

/-- An internally graded `R`-module, with homogeneous component indexed by `ι`.

The component is a submodule of the underlying module, and the decomposition
field says that these submodules form the direct-sum decomposition of the
underlying module.  This is the internal form of a graded module used by
Mathlib's graded algebra API.
-/
structure GradedModuleData (R : Type u) (M : Type v) (ι : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq ι] where
  component : ι → Submodule R M
  decomposition : DirectSum.Decomposition component

namespace GradedModuleData

/-- The degree-`n` homogeneous submodule of a graded module. -/
abbrev homogeneous
    {R : Type u} {M : Type v} {ι : Type w}
    [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq ι]
    (G : GradedModuleData R M ι) (n : ι) : Submodule R M :=
  G.component n

end GradedModuleData

/-- The canonical homogeneous submodule of a direct sum. -/
def directSumComponent (R : Type u) {ι : Type w} (M : ι → Type v) (n : ι)
    [CommRing R] [DecidableEq ι]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    Submodule R (DirectSum ι M) :=
  LinearMap.range (DirectSum.lof R ι M n)

/-- The direct sum is graded by its canonical summands.

The construction is a small reusable bridge between Mathlib's external direct
sum and the internal `GradedModuleData` interface.  Its proof is deferred with
the other proposition proofs in this statements stage.
-/
theorem directSum_decomposition_nonempty
    (R : Type u) {ι : Type w} (M : ι → Type v)
    [CommRing R] [DecidableEq ι]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    Nonempty (DirectSum.Decomposition (fun n => directSumComponent R M n)) := by
  sorry

/-- Package the canonical direct-sum grading as graded-module data. -/
noncomputable def directSumGradedModuleData
    (R : Type u) {ι : Type w} (M : ι → Type v)
    [CommRing R] [DecidableEq ι]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    GradedModuleData R (DirectSum ι M) ι where
  component := fun n => directSumComponent R M n
  decomposition := Classical.choice (directSum_decomposition_nonempty R M)

/-- A category whose Hom modules are graded and whose composition preserves
degrees.  The `hom` field supplies the graded module structure on each Hom,
while the two fields below encode degree-preserving composition and
degree-zero identities.  The underlying category uses the canonical
`CategoryTheory.Linear` interface.
-/
class GradedCategory (R : Type u) (C : Type v)
    [CommRing R] [Category.{w} C] [Preadditive C] [CategoryTheory.Linear R C] where
  hom : ∀ X Y : C, GradedModuleData R (X ⟶ Y) ℤ
  comp_homogeneous : ∀ {X Y Z : C} {i j : ℤ}
    (f : (hom X Y).component i) (g : (hom Y Z).component j),
    (f : X ⟶ Y) ≫ (g : Y ⟶ Z) ∈ (hom X Z).component (i + j)
  id_homogeneous : ∀ (X : C), 𝟙 X ∈ (hom X X).component 0

namespace GradedCategory

/-- The degree-`n` part of a Hom in a graded category. -/
abbrev homogeneous
    (R : Type u) {C : Type v} [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C] [GradedCategory R C]
    (X Y : C) (n : ℤ) : Submodule R (X ⟶ Y) :=
  (GradedCategory.hom X Y).component n

/-- The direct-sum decomposition of a Hom module into its homogeneous parts. -/
@[instance_reducible] def homDecomposition
    (R : Type u) {C : Type v} [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C] [A : GradedCategory R C] (X Y : C) :
    DirectSum.Decomposition (fun n => (A.hom X Y).component n) :=
  (A.hom X Y).decomposition

/-- Composition of homogeneous morphisms as an `R`-linear map in the second
argument, with the first argument fixed. -/
def compLinearMap
    (R : Type u) {C : Type v} [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C] [A : GradedCategory R C]
    {X Y Z : C} (i j : ℤ) (f : (A.hom X Y).component i) :
    (A.hom Y Z).component j →ₗ[R] (A.hom X Z).component (i + j) :=
  { toFun := fun g =>
      ⟨(f : X ⟶ Y) ≫ (g : Y ⟶ Z), A.comp_homogeneous f g⟩
    map_add' := by
      intro g g'
      apply Subtype.ext
      exact
        (Preadditive.comp_add X Y Z (f : X ⟶ Y) (g : Y ⟶ Z) (g' : Y ⟶ Z))
    map_smul' := by
      intro r g
      apply Subtype.ext
      exact
        (CategoryTheory.Linear.comp_smul X Y Z (f : X ⟶ Y) r (g : Y ⟶ Z)) }

/-- Composition of homogeneous morphisms is bilinear. -/
def compBilinearMap
    (R : Type u) {C : Type v} [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C] [A : GradedCategory R C]
    {X Y Z : C} (i j : ℤ) :
    (A.hom X Y).component i →ₗ[R]
      (A.hom Y Z).component j →ₗ[R] (A.hom X Z).component (i + j) :=
  { toFun := compLinearMap R i j
    map_add' := by
      intro f f'
      apply LinearMap.ext
      intro g
      apply Subtype.ext
      change ((f + f' : (A.hom X Y).component i) : X ⟶ Y) ≫ (g : Y ⟶ Z) =
        (f : X ⟶ Y) ≫ (g : Y ⟶ Z) + (f' : X ⟶ Y) ≫ (g : Y ⟶ Z)
      exact
        (Preadditive.add_comp X Y Z (f : X ⟶ Y) (f' : X ⟶ Y) (g : Y ⟶ Z))
    map_smul' := by
      intro r f
      apply LinearMap.ext
      intro g
      apply Subtype.ext
      change (r • (f : X ⟶ Y)) ≫ (g : Y ⟶ Z) =
        r • (f : X ⟶ Y) ≫ (g : Y ⟶ Z)
      exact
        (CategoryTheory.Linear.smul_comp X Y Z r (f : X ⟶ Y) (g : Y ⟶ Z)) }

/-- The induced map from the tensor product of the two homogeneous Hom
modules, with the source's order `Hom(y,z) ⊗ Hom(x,y)`. -/
def compTensorProductLinearMap
    (R : Type u) {C : Type v} [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C] [A : GradedCategory R C]
    {X Y Z : C} (i j : ℤ) :
    ((A.hom Y Z).component j) ⊗[R] ((A.hom X Y).component i) →ₗ[R]
      (A.hom X Z).component (i + j) :=
  TensorProduct.lift (LinearMap.flip (compBilinearMap R i j))

end GradedCategory

/-- A functor between graded categories which is linear and preserves degrees.

`Functor.Additive` is included explicitly because Mathlib's `Functor.Linear`
records scalar compatibility, while the source asks for a homomorphism of
graded modules and hence also requires additivity.
-/
class GradedFunctor
    (R : Type u) {C : Type v} {D : Type v}
    [CommRing R] [Category.{w} C] [Category.{w} D]
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    [GradedCategory R C] [GradedCategory R D]
    (F : C ⥤ D) where
  additive : Functor.Additive F
  linear : Functor.Linear R F
  map_component : ∀ {X Y : C} {n : ℤ}
    (f : (GradedCategory.hom (R := R) X Y).component n),
    F.map (f : X ⟶ Y) ∈
      (GradedCategory.hom (R := R) (F.obj X) (F.obj Y)).component n

/-! ## The degree-zero category -/

/-- A type synonym carrying the same objects as `C`, used for the associated
category of degree-zero morphisms. -/
def DegreeZero {R : Type u} {C : Type v} [CommRing R] [Category.{w} C]
    [Preadditive C] [CategoryTheory.Linear R C]
    (_A : GradedCategory R C) := ULift C

namespace DegreeZero

variable {R : Type u} {C : Type v} [CommRing R]
  [categoryC : Category.{w} C] [preadditiveC : Preadditive C]
  [linearC : CategoryTheory.Linear R C]
  (A : @GradedCategory R C _ categoryC preadditiveC linearC)

@[simp] def obj (X : DegreeZero A) : C := ULift.down X

def of (X : C) : DegreeZero A := ULift.up X

@[simp] theorem obj_of (X : C) : obj A (of A X) = X := rfl

@[simp] theorem of_obj (X : DegreeZero A) : of A (obj A X) = X := by
  cases X
  rfl

instance category : Category (DegreeZero A) where
  Hom X Y :=
    (@GradedCategory.hom R C _ categoryC preadditiveC linearC A (obj A X) (obj A Y)).component 0
  id X := ⟨𝟙 (obj A X), A.id_homogeneous (obj A X)⟩
  comp f g :=
    ⟨f.1 ≫ g.1, by
      simpa using A.comp_homogeneous f g⟩
  id_comp f := by
    apply Subtype.ext
    simp
  comp_id f := by
    apply Subtype.ext
    simp
  assoc f g h := by
    apply Subtype.ext
    simp [Category.assoc]

instance preadditive : Preadditive (DegreeZero A) where
  homGroup X Y := by
    exact inferInstanceAs
      (AddCommGroup
        ((@GradedCategory.hom R C _ categoryC preadditiveC linearC A
          (obj A X) (obj A Y)).component 0))
  add_comp := by
    intro X Y Z f f' g
    apply Subtype.ext
    change (f.1 + f'.1) ≫ g.1 = f.1 ≫ g.1 + f'.1 ≫ g.1
    simpa using
      (Preadditive.add_comp (obj A X) (obj A Y) (obj A Z)
        (f.1) (f'.1) (g.1))
  comp_add := by
    intro X Y Z f g g'
    apply Subtype.ext
    change f.1 ≫ (g.1 + g'.1) = f.1 ≫ g.1 + f.1 ≫ g'.1
    simpa using
      (Preadditive.comp_add (obj A X) (obj A Y) (obj A Z)
        (f.1) (g.1) (g'.1))

instance linear : CategoryTheory.Linear R (DegreeZero A) where
  homModule X Y := by
    exact inferInstanceAs
      (Module R
        ((@GradedCategory.hom R C _ categoryC preadditiveC linearC A
          (obj A X) (obj A Y)).component 0))
  smul_comp := by
    intro X Y Z r f g
    apply Subtype.ext
    change (r • f.1) ≫ g.1 = r • f.1 ≫ g.1
    simpa using
      (CategoryTheory.Linear.smul_comp (obj A X) (obj A Y) (obj A Z)
        r (f.1) (g.1))
  comp_smul := by
    intro X Y Z f r g
    apply Subtype.ext
    change f.1 ≫ (r • g.1) = r • f.1 ≫ g.1
    simpa using
      (CategoryTheory.Linear.comp_smul (obj A X) (obj A Y) (obj A Z)
        (f.1) r (g.1))

/-- The degree-zero Hom type, exposed without unfolding the category instance. -/
abbrev hom (X Y : DegreeZero A) :=
  (@GradedCategory.hom R C _ categoryC preadditiveC linearC A
    (obj A X) (obj A Y)).component 0

end DegreeZero

/-! ## Graded direct sums -/

/-- The four maps and relations used by the source's direct-sum notation.

This is the map-level characterization from Homology, Remark
`homology-remark-direct-sum`; it is deliberately not replaced by a stronger
existence assumption about a chosen biproduct object.
-/
structure DirectSumData {C : Type v} [Category.{w} C] [Preadditive C]
    (X Y Z : C) where
  i : X ⟶ Z
  j : Y ⟶ Z
  p : Z ⟶ X
  q : Z ⟶ Y
  i_p : i ≫ p = 𝟙 X
  j_q : j ≫ q = 𝟙 Y
  j_p : j ≫ p = 0
  i_q : i ≫ q = 0
  total : p ≫ i + q ≫ j = 𝟙 Z

/-- A direct sum is graded when all four structure maps have degree zero. -/
def IsGradedDirectSum
    (R : Type u) {C : Type v} [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C] [A : GradedCategory R C]
    {X Y Z : C} (d : DirectSumData X Y Z) : Prop :=
  d.i ∈ (A.hom X Z).component 0 ∧
    d.j ∈ (A.hom Y Z).component 0 ∧
      d.p ∈ (A.hom Z X).component 0 ∧
        d.q ∈ (A.hom Z Y).component 0

end Formalization.Books.Dga.Unit25
