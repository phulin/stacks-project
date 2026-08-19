import Formalization.Books.Dga.Unit05.HomotopyCategory
import Formalization.Books.Dga.Unit25.Core
import Formalization.Books.Dga.Unit25.GradedObjects
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Differential graded categories

This file records the differential graded category interface and the two
examples in the corresponding section of the Stacks project.  The homogeneous
Hom objects are `ModuleCat` objects; this makes the grading, the differential,
and the tensor-product composition maps explicit without introducing a second
notion of an `R`-module.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit25

universe u v

namespace Formalization.Books.Dga.Unit26

/-! ## Differential graded categories -/

/-- A differential graded category presented by its homogeneous Hom modules.

`composition` is ordered as in the source: a map of degree `i` is followed by
a map of degree `j`.  The `HEq` in the Leibniz and associativity fields only
records the harmless reassociation of integer degree indices.
-/
class DifferentialGradedCategory (R : Type u) [CommRing R] where
  Obj : Type v
  hom : Obj → Obj → ℤ → ModuleCat.{v} R
  differential : ∀ X Y n, hom X Y n ⟶ hom X Y (n + 1)
  differential_squared : ∀ X Y n (f : hom X Y n),
    (differential X Y (n + 1)).hom ((differential X Y n).hom f) = 0
  composition : ∀ {X Y Z} (i j : ℤ),
    hom X Y i → hom Y Z j → hom X Z (i + j)
  composition_add_left : ∀ {X Y Z} (i j : ℤ)
    (f f' : hom X Y i) (g : hom Y Z j),
    composition i j (f + f') g = composition i j f g + composition i j f' g
  composition_add_right : ∀ {X Y Z} (i j : ℤ)
    (f : hom X Y i) (g g' : hom Y Z j),
    composition i j f (g + g') = composition i j f g + composition i j f g'
  composition_smul_left : ∀ {X Y Z} (i j : ℤ) (r : R)
    (f : hom X Y i) (g : hom Y Z j),
    composition i j (r • f) g = r • composition i j f g
  composition_smul_right : ∀ {X Y Z} (i j : ℤ) (r : R)
    (f : hom X Y i) (g : hom Y Z j),
    composition i j f (r • g) = r • composition i j f g
  identity : ∀ X, hom X X 0
  identity_composition : ∀ {X Y} (i : ℤ) (f : hom X Y i),
    cast (by simp) (composition 0 i (identity X) f) = f
  composition_identity : ∀ {X Y} (i : ℤ) (f : hom X Y i),
    cast (by simp) (composition i 0 f (identity Y)) = f
  composition_associative : ∀ {W X Y Z} (i j k : ℤ)
    (f : hom W X i) (g : hom X Y j) (h : hom Y Z k),
    composition (i + j) k (composition i j f g) h =
      cast (by simp [add_assoc])
        (composition i (j + k) f (composition j k g h))
  composition_differential : ∀ {X Y Z} (i j : ℤ)
    (f : hom X Y i) (g : hom Y Z j),
    (differential X Z (i + j)).hom (composition i j f g) =
      cast (by simp [add_assoc])
          (composition i (j + 1) f ((differential Y Z j).hom g)) +
        ((j.negOnePow : ℤ) : R) •
          cast (by simp [add_assoc, add_comm, add_left_comm])
            (composition (i + 1) j ((differential X Y i).hom f) g)

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R] [A : DifferentialGradedCategory R]

/-! The introductory identifications with ordinary complexes and total tensor
products. -/

theorem ring_is_a_differentialGradedAlgebra (R : Type u) [CommRing R] :
    Nonempty (DifferentialGradedAlgebra R) := by
  sorry

abbrev differentialGradedModuleTensorProduct
    (R : Type u) [CommRing R]
    (M N : CochainComplexOver R) : CochainComplexOver R :=
  tensorProductComplex R M N

theorem differentialGradedModule_tensorProduct_is_total
    (R : Type u) [CommRing R] (M N : CochainComplexOver R) :
    differentialGradedModuleTensorProduct R M N = tensorProductComplex R M N :=
  rfl

/-- A homogeneous closed morphism of degree zero. -/
def cycleSubmodule (X Y : A.Obj) : Submodule R (A.hom X Y 0) :=
  LinearMap.ker (A.differential X Y 0).hom

/-- The degree-zero cohomology class of a closed morphism. -/
def boundarySubmodule (X Y : A.Obj) :
    Submodule R (cycleSubmodule X Y) where
  carrier := {f | ∃ g : A.hom X Y (-1),
    (A.differential X Y (-1)).hom g = (f : A.hom X Y 0)}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

abbrev Cycle (X Y : A.Obj) := cycleSubmodule X Y

abbrev CohomologyClass (X Y : A.Obj) :=
  (cycleSubmodule X Y) ⧸ boundarySubmodule X Y

abbrev ExplicitCohomologyClass
    (A : DifferentialGradedCategory R) (X Y : A.Obj) :=
  (cycleSubmodule (A := A) X Y) ⧸ boundarySubmodule (A := A) X Y

/-- Composition of closed degree-zero morphisms. -/
def cycleComposition {X Y Z : A.Obj}
    (f : Cycle X Y) (g : Cycle Y Z) : Cycle X Z := by
  refine ⟨A.composition 0 0 (f : A.hom X Y 0) (g : A.hom Y Z 0), ?_⟩
  sorry

def cycleIdentity (X : A.Obj) : Cycle X X := by
  refine ⟨A.identity X, ?_⟩
  sorry

/-- The category `Comp(A)` of closed degree-zero morphisms. -/
def ComplexCategoryObject (A : DifferentialGradedCategory R) := ULift A.Obj

namespace ComplexCategoryObject

def of (A : DifferentialGradedCategory R) (X : A.Obj) : ComplexCategoryObject A := ULift.up X

def underlying (A : DifferentialGradedCategory R)
    (X : ComplexCategoryObject A) : A.Obj := ULift.down X

omit A in
@[simp] theorem underlying_of (A : DifferentialGradedCategory R) (X : A.Obj) :
    underlying A (of A X) = X := rfl

omit A in
@[simp] theorem of_underlying (A : DifferentialGradedCategory R)
    (X : ComplexCategoryObject A) :
    of A (underlying A X) = X := by
  cases X
  rfl

end ComplexCategoryObject

instance complexCategory : Category (ComplexCategoryObject A) where
  Hom X Y := Cycle (ComplexCategoryObject.underlying A X)
    (ComplexCategoryObject.underlying A Y)
  id X := cycleIdentity (ComplexCategoryObject.underlying A X)
  comp f g := cycleComposition f g
  id_comp f := by sorry
  comp_id f := by sorry
  assoc f g h := by sorry

abbrev ComplexCategory (A : DifferentialGradedCategory R) :=
  ComplexCategoryObject A

instance complexCategoryPreadditive : Preadditive (ComplexCategory (A := A)) where
  homGroup X Y :=
    Submodule.addCommGroup
      (cycleSubmodule (A := A)
        (ComplexCategoryObject.underlying A X)
        (ComplexCategoryObject.underlying A Y))
  add_comp := by sorry
  comp_add := by sorry

def homotopyRelation : HomRel (ComplexCategory (A := A)) :=
  fun X Y f g => ∃ h : A.hom (ComplexCategoryObject.underlying A X)
      (ComplexCategoryObject.underlying A Y) (-1),
    (A.differential _ _ (-1)).hom h = (f.1 : A.hom _ _ 0) - g.1

instance homotopyCongruence : Congruence (homotopyRelation (A := A)) where
  equivalence := by sorry
  comp_left := by sorry
  comp_right := by sorry

/-- The homotopy category `K(A)`. -/
abbrev DgHomotopyCategory (A : DifferentialGradedCategory R) :=
  CategoryTheory.Quotient (homotopyRelation (A := A))

noncomputable instance homotopyCategoryPreadditive :
    Preadditive (DgHomotopyCategory A) :=
  CategoryTheory.Quotient.preadditive
    (homotopyRelation (A := A)) (by sorry)

/-- The quotient functor from `Comp(A)` to `K(A)`. -/
abbrev homotopyQuotient : ComplexCategory A ⥤
    DgHomotopyCategory A :=
  CategoryTheory.Quotient.functor (homotopyRelation (A := A))

/-- The source's identification of a Hom in `K(A)` with degree-zero
cohomology. -/
noncomputable def homotopyHomologyEquiv (X Y : A.Obj) :
    ((homotopyQuotient (A := A)).obj (ComplexCategoryObject.of A X) ⟶
      (homotopyQuotient (A := A)).obj (ComplexCategoryObject.of A Y)) ≃+
      ExplicitCohomologyClass A X Y := by
  sorry

/-- A direct sum in `Comp(A)` is differential graded when its four structure
maps are closed.  They already have degree zero because `Comp(A)` is the
degree-zero category; this predicate keeps the four source conditions
explicit. -/
def IsDifferentialGradedDirectSum
    {X Y Z : ComplexCategory (A := A)}
    (d : DirectSumData X Y Z) : Prop :=
  (A.differential _ _ 0).hom (d.i.1 : A.hom _ _ 0) = 0 ∧
    (A.differential _ _ 0).hom (d.j.1 : A.hom _ _ 0) = 0 ∧
      (A.differential _ _ 0).hom (d.p.1 : A.hom _ _ 0) = 0 ∧
        (A.differential _ _ 0).hom (d.q.1 : A.hom _ _ 0) = 0

end DifferentialGradedCategory

/-! ## Differential graded functors -/

/-- A functor of differential graded categories, written on homogeneous Hom
modules. -/
structure DifferentialGradedFunctor
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedCategory R) where
  obj : A.Obj → B.Obj
  mapHom : ∀ X Y n, A.hom X Y n →ₗ[R] B.hom (obj X) (obj Y) n
  map_identity : ∀ X, mapHom X X 0 (A.identity X) = B.identity (obj X)
  map_composition : ∀ {X Y Z} (i j : ℤ)
    (f : A.hom X Y i) (g : A.hom Y Z j),
    mapHom X Z (i + j) (A.composition i j f g) =
      B.composition i j (mapHom X Y i f) (mapHom Y Z j g)
  map_differential : ∀ {X Y} (n : ℤ) (f : A.hom X Y n),
    mapHom X Y (n + 1) ((A.differential X Y n).hom f) =
      (B.differential (obj X) (obj Y) n).hom (mapHom X Y n f)

namespace DifferentialGradedFunctor

variable {R : Type u} [CommRing R]
  {A B : DifferentialGradedCategory R}
  (F : DifferentialGradedFunctor A B)

/-- The functor induced by a differential graded functor on `Comp`. -/
def onComplexes :
    DifferentialGradedCategory.ComplexCategory (A := A) ⥤
      DifferentialGradedCategory.ComplexCategory (A := B) where
  obj X := DifferentialGradedCategory.ComplexCategoryObject.of B
    (F.obj (DifferentialGradedCategory.ComplexCategoryObject.underlying A X))
  map f := by
    refine ⟨F.mapHom
      (DifferentialGradedCategory.ComplexCategoryObject.underlying A _)
      (DifferentialGradedCategory.ComplexCategoryObject.underlying A _) 0
      (f.1 : A.hom _ _ 0), ?_⟩
    sorry
  map_id := by sorry
  map_comp := by sorry

/-- A differential graded functor induces a functor on homotopy categories. -/
theorem inducesHomotopyFunctor (F : DifferentialGradedFunctor A B) : Nonempty
    (DifferentialGradedCategory.DgHomotopyCategory A ⥤
      DifferentialGradedCategory.DgHomotopyCategory B) := by
  sorry

noncomputable def onHomotopyCategories :
    DifferentialGradedCategory.DgHomotopyCategory A ⥤
      DifferentialGradedCategory.DgHomotopyCategory B :=
  Classical.choice (DifferentialGradedFunctor.inducesHomotopyFunctor F)

end DifferentialGradedFunctor

/-! ## The category of complexes -/

variable {B : Type u} [Category.{v} B]
  [Formalization.Books.Homology.Unit03.AdditiveCategory B]

abbrev ComplexUnderlyingGradedObject (B : Type u) := CategoryTheory.GradedObject ℤ B

def complexUnderlyingGradedObject (K : CochainComplex B ℤ) :
    ComplexUnderlyingGradedObject B := fun n => K.X n

/-- The degree-`n` Hom family from the source's example. -/
abbrev ComplexHomogeneous
    (K L : CochainComplex B ℤ) (n : ℤ) :=
  GradedObjectHomogeneous (complexUnderlyingGradedObject K)
    (complexUnderlyingGradedObject L) n

/-- Componentwise composition of homogeneous maps of complexes. -/
abbrev complexHomogeneousComposition
    {K L M : CochainComplex B ℤ} (i j : ℤ)
    (f : ComplexHomogeneous K L i) (g : ComplexHomogeneous L M j) :
    ComplexHomogeneous K M (i + j) :=
  gradedObjectHomogeneousComp i j f g

/-- The component formula for the differential on the Hom complex.

The output component indexed by `(p,q)` uses the input components indexed by
`(p - 1,q)` and `(p,q - 1)`, which is the product-form version of the
displayed formula `d_B ∘ f - (-1)^n f ∘ d_A`.
-/
def complexHomogeneousDifferential
    {K L : CochainComplex B ℤ} (n : ℤ)
    (f : ComplexHomogeneous K L n) : ComplexHomogeneous K L (n + 1) :=
  fun ⟨⟨p, q⟩, h⟩ =>
    let h' : p + q = n + 1 := h
    let first : K.X (-q) ⟶ L.X p := by
      simpa [complexUnderlyingGradedObject] using
        ((f ⟨(p - 1, q), by omega⟩) ≫ L.d (p - 1) p)
    let second : K.X (-q) ⟶ L.X p := by
      simpa [complexUnderlyingGradedObject] using
        (K.d (-q) (-q + 1) ≫
          eqToHom (by
            exact congrArg K.X (by ring)) ≫
            f ⟨(p, q - 1), by omega⟩)
    first - (n.negOnePow : ℤ) • second

noncomputable def complexHomogeneousDifferentialLinear
    {K L : CochainComplex B ℤ} (n : ℤ) :
    ComplexHomogeneous K L n →ₗ[ℤ] ComplexHomogeneous K L (n + 1) where
  toFun := complexHomogeneousDifferential n
  map_add' := by sorry
  map_smul' := by sorry

/-- The explicit data of the differential graded category of complexes.  The
Homogeneous and differential fields are the displayed product and
commutator formulas; the remaining fields record the category axioms. -/
structure ComplexDgCategoryData (B : Type u) [Category.{v} B]
    [Formalization.Books.Homology.Unit03.AdditiveCategory B] where
  differential : ∀ {K L : CochainComplex B ℤ} (n : ℤ),
    ComplexHomogeneous K L n → ComplexHomogeneous K L (n + 1)
  composition : ∀ {K L M : CochainComplex B ℤ} (i j : ℤ),
    ComplexHomogeneous K L i → ComplexHomogeneous L M j →
      ComplexHomogeneous K M (i + j)
  identity : ∀ (K : CochainComplex B ℤ), ComplexHomogeneous K K 0
  differential_squared : ∀ (K L : CochainComplex B ℤ) (n : ℤ)
    (f : ComplexHomogeneous K L n),
    complexHomogeneousDifferential (n + 1)
      (complexHomogeneousDifferential n f) = 0
  composition_differential : ∀ (K L M : CochainComplex B ℤ)
    (i j : ℤ) (f : ComplexHomogeneous K L i)
      (g : ComplexHomogeneous L M j),
    complexHomogeneousDifferential (i + j)
        (complexHomogeneousComposition i j f g) =
      cast (by simp [add_assoc])
        (complexHomogeneousComposition i (j + 1) f
          (complexHomogeneousDifferential j g)) +
        (j.negOnePow : ℤ) •
          cast (by simp [add_assoc, add_comm, add_left_comm])
            (complexHomogeneousComposition (i + 1) j
              (complexHomogeneousDifferential i f) g)
  identity_left : ∀ (K L : CochainComplex B ℤ) (n : ℤ)
    (f : ComplexHomogeneous K L n),
    cast (by simp) (composition 0 n (identity K) f) = f
  identity_right : ∀ (K L : CochainComplex B ℤ) (n : ℤ)
    (f : ComplexHomogeneous K L n),
    cast (by simp) (composition n 0 f (identity L)) = f
  composition_associative : ∀ (W X Y Z : CochainComplex B ℤ)
    (i j k : ℤ) (f : ComplexHomogeneous W X i)
      (g : ComplexHomogeneous X Y j) (h : ComplexHomogeneous Y Z k),
    composition (i + j) k (composition i j f g) h =
      cast (by simp [add_assoc])
        (composition i (j + k) f (composition j k g h))

noncomputable def complexDifferentialGradedCategory
    (B : Type u) [Category.{v} B]
    [Formalization.Books.Homology.Unit03.AdditiveCategory B] :
    ComplexDgCategoryData B where
  differential := complexHomogeneousDifferential
  composition := complexHomogeneousComposition
  identity := fun K => gradedObjectHomogeneousId (complexUnderlyingGradedObject K)
  differential_squared := by sorry
  composition_differential := by sorry
  identity_left := by sorry
  identity_right := by sorry
  composition_associative := by sorry

abbrev ComplexesDgCategory (B : Type u) [Category.{v} B]
    [Formalization.Books.Homology.Unit03.AdditiveCategory B] :=
  CochainComplex B ℤ

theorem complexHomogeneous_differential_squared
    {K L : CochainComplex B ℤ} (n : ℤ)
    (f : ComplexHomogeneous K L n) :
    complexHomogeneousDifferential (n + 1)
        (complexHomogeneousDifferential n f) = 0 := by
  sorry

/-- A degree-`n` homogeneous family is a map of complexes to the shifted
target exactly when its Hom-complex differential vanishes. -/
def IsShiftedComplexMap
    {K L : CochainComplex B ℤ} {n : ℤ}
    (f : ComplexHomogeneous K L n) : Prop :=
  complexHomogeneousDifferential n f = 0

theorem complexHomogeneous_closed_iff_shiftedComplexMap
    {K L : CochainComplex B ℤ} {n : ℤ}
    (f : ComplexHomogeneous K L n) :
    complexHomogeneousDifferential n f = 0 ↔ IsShiftedComplexMap f :=
  Iff.rfl

theorem complexes_degree_zero_category_is_category_of_complexes :
    Nonempty
      (ComplexesDgCategory B ≌
        CochainComplex B ℤ) := by
  exact ⟨CategoryTheory.Equivalence.refl⟩

def IsNullHomotopicComplexMap
    {K L : CochainComplex B ℤ} {n : ℤ}
    (f : ComplexHomogeneous K L n) : Prop :=
  ∃ g : ComplexHomogeneous K L (n - 1),
    complexHomogeneousDifferential (n - 1) g =
      cast (congrArg (fun k : ℤ => ComplexHomogeneous K L k)
        (sub_add_cancel n 1).symm) f

theorem complexHomogeneous_nullHomotopic_iff_boundary
    {K L : CochainComplex B ℤ} {n : ℤ}
    (f : ComplexHomogeneous K L n) :
    IsNullHomotopicComplexMap f ↔
      ∃ g : ComplexHomogeneous K L (n - 1),
        complexHomogeneousDifferential (n - 1) g =
          cast (congrArg (fun k : ℤ => ComplexHomogeneous K L k)
            (sub_add_cancel n 1).symm) f :=
  Iff.rfl

noncomputable def complexes_homotopy_homology_iso
    (K L : CochainComplex B ℤ) :
    (((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) ≃+
      CochainComplex.HomComplex.CohomologyClass K L 0 := by
  sorry

theorem complexes_homotopy_category_is_standard_homotopy_category :
    Nonempty
      (HomotopyCategory B (ComplexShape.up ℤ) ≌
        HomotopyCategory B (ComplexShape.up ℤ)) := by
  exact ⟨CategoryTheory.Equivalence.refl⟩

theorem complexHomogeneous_composition_differential_formula
    {K L M : CochainComplex B ℤ} {i j : ℤ}
    (f : ComplexHomogeneous K L i) (g : ComplexHomogeneous L M j) :
    complexHomogeneousDifferential (i + j)
      (complexHomogeneousComposition i j f g) =
      cast (by simp [add_assoc])
        (complexHomogeneousComposition i (j + 1) f
          (complexHomogeneousDifferential j g)) +
        (j.negOnePow : ℤ) •
          cast (by simp [add_assoc, add_comm, add_left_comm])
            (complexHomogeneousComposition (i + 1) j
              (complexHomogeneousDifferential i f) g) := by
  sorry

/-! ## Additive functors and the first example -/

structure ComplexDgFunctorData
    {B B' : Type u} [Category.{v} B] [Category.{v} B']
    [Formalization.Books.Homology.Unit03.AdditiveCategory B]
    [Formalization.Books.Homology.Unit03.AdditiveCategory B']
    (F : B ⥤ B') where
  mapObject : CochainComplex B ℤ → CochainComplex B' ℤ
  mapHom : ∀ {K L : CochainComplex B ℤ} (n : ℤ),
    ComplexHomogeneous K L n →
      ComplexHomogeneous (mapObject K) (mapObject L) n
  map_differential : ∀ {K L : CochainComplex B ℤ} (n : ℤ)
    (f : ComplexHomogeneous K L n),
    mapHom (n + 1) (complexHomogeneousDifferential n f) =
      complexHomogeneousDifferential n (mapHom n f)

theorem additiveFunctor_induces_differentialGradedFunctor
    {B' : Type u} [Category.{v} B']
    [Formalization.Books.Homology.Unit03.AdditiveCategory B']
    (F : B ⥤ B') [F.Additive] :
    Nonempty (ComplexDgFunctorData F) := by
  sorry

noncomputable def additiveFunctorOnComplexes
    {B' : Type u} [Category.{v} B']
    [Formalization.Books.Homology.Unit03.AdditiveCategory B']
    (F : B ⥤ B') [F.Additive] :
    ComplexDgFunctorData F :=
  Classical.choice (additiveFunctor_induces_differentialGradedFunctor F)

/-! ## The differential graded category of differential graded modules -/

/-- The source's homogeneous right-module Hom interface.  The degree pieces
are the established graded right-module maps, while `differential` records
the commutator with the two module differentials. -/
structure DifferentialGradedModuleHomComplex
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R)
    (L M : DifferentialGradedModule A) where
  homogeneous : ℤ → Type u
  homogeneous_identification : ∀ n,
    homogeneous n =
      ∀ s : GradedDegreePair n,
        L.complex.X (-s.1.2) →ₗ[R] M.complex.X s.1.1
  zero : ∀ n, homogeneous n
  differential : ∀ n, homogeneous n → homogeneous (n + 1)
  commutator : ∀ n, homogeneous n → homogeneous (n + 1)
  differential_formula : ∀ n f, differential n f = commutator n f

theorem differentialGradedModuleHomDifferentialFormula
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {L M : DifferentialGradedModule A}
    (H : DifferentialGradedModuleHomComplex A L M) :
    ∀ n f, H.differential n f = H.commutator n f :=
  H.differential_formula

theorem differentialGradedModuleHom_differential_squared
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {L M : DifferentialGradedModule A}
    (H : DifferentialGradedModuleHomComplex A L M) :
    ∀ n f, H.differential (n + 1) (H.differential n f) = H.zero (n + 1 + 1) := by
  sorry

def IsShiftedDifferentialGradedModuleMap
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {L M : DifferentialGradedModule A}
    (H : DifferentialGradedModuleHomComplex A L M) (n : ℤ)
    (f : H.homogeneous n) : Prop :=
  H.differential n f = H.zero (n + 1)

theorem differentialGradedModuleHom_closed_iff_shifted_module_map
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {L M : DifferentialGradedModule A}
    (H : DifferentialGradedModuleHomComplex A L M) :
    ∀ n f, H.differential n f = H.zero (n + 1) ↔
      IsShiftedDifferentialGradedModuleMap H n f := by
  intro n f
  rfl

/-! ## Restriction of scalars and endomorphism actions -/

structure DifferentialGradedModuleRestrictionData
    {R : Type u} [CommRing R]
    (A E : DifferentialGradedAlgebra R) where
  object : DifferentialGradedModule E → DifferentialGradedModule A
  map : ∀ {L M : DifferentialGradedModule E},
    DifferentialGradedModuleHom L M →
      DifferentialGradedModuleHom (object L) (object M)
  functor : DifferentialGradedModuleCategory E ⥤
    DifferentialGradedModuleCategory A

theorem differentialGradedAlgebraHom_induces_restrictionFunctor
    {R : Type u} [CommRing R]
    {A E : DifferentialGradedAlgebra R}
    (φ : DifferentialGradedAlgebraHom A E) :
    Nonempty (DifferentialGradedModuleRestrictionData A E) := by
  sorry

structure EndomorphismActionData
    {R : Type u} [CommRing R]
  (A : DifferentialGradedCategory R) (X : A.Obj) where
  identity : A.hom X X 0
  action : ∀ (Y : A.Obj) (i j : ℤ),
    A.hom X X i → A.hom X Y j → A.hom X Y (i + j)
  action_identity : ∀ (Y : A.Obj) (j : ℤ) (f : A.hom X Y j),
    cast (by simp) (action Y 0 j identity f) = f
  action_associative : ∀ (Y : A.Obj) (i j k : ℤ)
    (f : A.hom X X i) (g : A.hom X X j) (h : A.hom X Y k),
    action Y (i + j) k (A.composition i j f g) h =
      cast (by simp [add_assoc])
        (action Y i (j + k) f (action Y j k g h))
  action_differential : ∀ (Y : A.Obj) (i j : ℤ)
    (f : A.hom X X i) (g : A.hom X Y j),
    (A.differential X Y (i + j)).hom (action Y i j f g) =
      cast (by simp [add_assoc])
        (action Y i (j + 1) f ((A.differential X Y j).hom g)) +
      ((j.negOnePow : ℤ) : R) •
        cast (by simp [add_assoc, add_comm, add_left_comm])
          (action Y (i + 1) j ((A.differential X X i).hom f) g)

noncomputable def endomorphismActionData
    {R : Type u} [CommRing R]
    (A : DifferentialGradedCategory R) (X : A.Obj) :
    EndomorphismActionData A X where
  identity := A.identity X
  action := fun Y i j f g => A.composition i j f g
  action_identity := by sorry
  action_associative := by sorry
  action_differential := by sorry

theorem differentialGradedCategory_endomorphism_action
    {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (X : A.Obj) :
    Nonempty (EndomorphismActionData A X) := by
  exact ⟨endomorphismActionData A X⟩

end Formalization.Books.Dga.Unit26
