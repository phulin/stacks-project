import Formalization.Books.Dga.Unit05.HomotopyCategory
import Formalization.Books.Dga.Unit10.Triangulated
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.CategoryTheory.EqToHom

/-!
# Differential Graded Algebra, Chapter 11: Left modules

This file records the left-module conventions from the source.  The
right-module API from Chapters 4 and 5 is used for the opposite-algebra
translation; the signed tensor flip is the canonical Koszul symmetry from
Chapter 3.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit05
open Formalization.Books.Dga.Unit10

universe u v w

namespace Formalization.Books.Dga.Unit11

/-! A small transport helper for componentwise graded families. -/

def transportGraded {X : ℤ → Type v} {p q : ℤ} (h : p = q)
    (x : X p) : X q := h ▸ x

/-! ## Left differential graded modules -/

/-- A left differential graded module over a cochain differential graded
algebra.  Its action is a chain map `Tot(A ⊗ M) ⟶ M`; the two equations are
the left-module unit and associativity diagrams. -/
structure LeftDifferentialGradedModule
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) where
  complex : CochainComplexOver R
  action : tensorProductComplex R A.complex complex ⟶ complex
  one_action :
    tensorHomComplex A.unit (𝟙 complex) ≫ action =
      (HomologicalComplex.leftUnitor complex).hom
  assoc_action :
    tensorHomComplex A.multiplication (𝟙 complex) ≫ action =
      (HomologicalComplex.associator A.complex A.complex complex).hom ≫
        tensorHomComplex (𝟙 A.complex) action ≫ action

/-- The homogeneous left action. -/
noncomputable def LeftDifferentialGradedModule.homogeneousAction
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (p q : ℤ) :
    A.complex.X p ⊗ M.complex.X q ⟶ M.complex.X (p + q) :=
  HomologicalComplex.ιTensorObj A.complex M.complex p q (p + q) rfl ≫
    M.action.f (p + q)

/-- Evaluation of the homogeneous left action on a pure tensor. -/
def LeftDifferentialGradedModule.actionOnHomogeneous
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (p q : ℤ)
    (a : A.complex.X p) (x : M.complex.X q) : M.complex.X (p + q) :=
  (M.homogeneousAction p q).hom (a ⊗ₜ[R] x)

/-- The elementwise left Leibniz rule exposed by the chain-map action. -/
def LeftDifferentialGradedModule.SatisfiesLeibniz
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) : Prop :=
  ∀ (p q : ℤ) (a : A.complex.X p) (x : M.complex.X q),
    (M.complex.d (p + q) (p + q + 1)).hom
        (M.actionOnHomogeneous p q a x) =
      transportComponent (C := M.complex) (by omega)
          (M.actionOnHomogeneous (p + 1) q
            ((A.complex.d p (p + 1)).hom a) x) +
        ((p.negOnePow : ℤ) : R) •
          transportComponent (C := M.complex) (by omega)
            (M.actionOnHomogeneous p (q + 1) a
              ((M.complex.d q (q + 1)).hom x))

theorem LeftDifferentialGradedModule.satisfiesLeibniz
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) : M.SatisfiesLeibniz := by
  sorry

/-! ## Morphisms and the left-module category -/

def LeftDifferentialGradedModuleHomSubgroup
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M N : LeftDifferentialGradedModule A) :
    AddSubgroup (M.complex ⟶ N.complex) where
  carrier := {f |
    M.action ≫ f = tensorHomComplex (𝟙 A.complex) f ≫ N.action}
  zero_mem' := by sorry
  add_mem' := by
    intro f g hf hg
    sorry
  neg_mem' := by
    intro f hf
    sorry

/-- A morphism of left differential graded modules. -/
abbrev LeftDifferentialGradedModuleHom
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M N : LeftDifferentialGradedModule A) : Type _ :=
  LeftDifferentialGradedModuleHomSubgroup M N

namespace LeftDifferentialGradedModuleHom

def underlying
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : LeftDifferentialGradedModule A}
    (f : LeftDifferentialGradedModuleHom M N) : M.complex ⟶ N.complex :=
  f.1

@[simp]
theorem underlying_mem
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : LeftDifferentialGradedModule A}
    (f : LeftDifferentialGradedModuleHom M N) :
    M.action ≫ f.underlying =
      tensorHomComplex (𝟙 A.complex) f.underlying ≫ N.action :=
  f.2

end LeftDifferentialGradedModuleHom

instance leftDifferentialGradedModuleCategory
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    Category (LeftDifferentialGradedModule A) where
  Hom M N := LeftDifferentialGradedModuleHom M N
  id M := ⟨𝟙 M.complex, by sorry⟩
  comp f g := ⟨f.underlying ≫ g.underlying, by sorry⟩
  id_comp f := by sorry
  comp_id f := by sorry
  assoc f g h := by sorry

abbrev LeftDifferentialGradedModuleCategory
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :=
  LeftDifferentialGradedModule A

instance leftDifferentialGradedModuleHomAddCommGroup
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M N : LeftDifferentialGradedModule A) :
    AddCommGroup (LeftDifferentialGradedModuleHom M N) :=
  AddSubgroupClass.toAddCommGroup _

/-! ## The opposite differential graded algebra -/

/-- The opposite DGA, with multiplication obtained by the signed tensor flip. -/
noncomputable def oppositeDifferentialGradedAlgebra
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) : DifferentialGradedAlgebra R where
  complex := A.complex
  multiplication :=
    (tensorFlipIso R A.complex A.complex).hom ≫ A.multiplication
  unit := A.unit
  one_mul := by sorry
  mul_one := by sorry
  mul_assoc := by sorry

theorem oppositeDifferentialGradedAlgebra_multiplication_factorization
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    (oppositeDifferentialGradedAlgebra A).multiplication =
      (tensorFlipIso R A.complex A.complex).hom ≫ A.multiplication := rfl

/-- The source's homogeneous multiplication formula for the opposite DGA. -/
theorem oppositeDifferentialGradedAlgebra_multiplication_on_homogeneous
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
    (p q : ℤ) (a : A.complex.X p) (b : A.complex.X q) :
    ((oppositeDifferentialGradedAlgebra A).homogeneousMultiplication p q).hom
        (a ⊗ₜ[R] b) =
      transportComponent (C := A.complex) (by omega)
        ((p * q).negOnePow •
          (A.homogeneousMultiplication q p).hom (b ⊗ₜ[R] a)) := by
  sorry

/-- The differential calculation which verifies the opposite Leibniz rule. -/
theorem oppositeDifferentialGradedAlgebra_differential_on_homogeneous
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
    (p q : ℤ) (a : A.complex.X p) (b : A.complex.X q) :
    ((oppositeDifferentialGradedAlgebra A).complex.d (p + q) (p + q + 1)).hom
        (((oppositeDifferentialGradedAlgebra A).homogeneousMultiplication p q).hom
          (a ⊗ₜ[R] b)) =
      ((p.negOnePow : ℤ) : R) •
          transportComponent (C := A.complex) (by omega)
            (((oppositeDifferentialGradedAlgebra A).homogeneousMultiplication p
                (q + 1)).hom
              (a ⊗ₜ[R] (A.complex.d q (q + 1)).hom b)) +
        transportComponent (C := A.complex) (by omega)
          (((oppositeDifferentialGradedAlgebra A).homogeneousMultiplication
              (p + 1) q).hom
            ((A.complex.d p (p + 1)).hom a ⊗ₜ[R] b)) := by
  sorry

/-! ## Passing a left module to a right module over the opposite DGA -/

/-- The signed right action on `Mᵒᵖ`, defined by the Koszul commutativity map. -/
noncomputable def leftModuleOpposite
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) :
    DifferentialGradedModule (oppositeDifferentialGradedAlgebra A) where
  complex := M.complex
  action := (tensorFlipIso R M.complex A.complex).hom ≫ M.action
  one_action := by sorry
  assoc_action := by sorry

/-- On homogeneous elements, the opposite action is
`m ⋅ₒₚₚ a = (-1)^(deg a deg m) a m`. -/
theorem leftModuleOpposite_action_on_homogeneous
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (p q : ℤ)
    (a : A.complex.X p) (x : M.complex.X q) :
    (leftModuleOpposite M).actionOnHomogeneous q p x a =
      transportComponent (C := M.complex) (by omega)
        ((p * q).negOnePow • M.actionOnHomogeneous p q a x) := by
  sorry

/-- The diagram defining the opposite module action, in map form. -/
theorem leftModuleOpposite_action_factorization
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) :
    (leftModuleOpposite M).action =
      (tensorFlipIso R M.complex A.complex).hom ≫ M.action := rfl

/-- The associativity identity for the signed opposite module action. -/
theorem leftModuleOpposite_associative_on_homogeneous
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A)
    (p q r : ℤ) (a : A.complex.X p) (b : A.complex.X q)
    (x : M.complex.X r) :
    HEq
      ((leftModuleOpposite M).actionOnHomogeneous (r + p) q
        ((leftModuleOpposite M).actionOnHomogeneous r p x a) b)
      ((leftModuleOpposite M).actionOnHomogeneous r (p + q) x
        (((oppositeDifferentialGradedAlgebra A).homogeneousMultiplication p q).hom
          (a ⊗ₜ[R] b))) := by
  sorry

noncomputable def leftModuleOppositeHom
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : LeftDifferentialGradedModule A}
    (f : LeftDifferentialGradedModuleHom M N) :
    DifferentialGradedModuleHom (leftModuleOpposite M) (leftModuleOpposite N) :=
  ⟨f.underlying, by sorry⟩

/-- The functor `M ↦ Mᵒᵖ` from left modules to right modules over `Aᵒᵖ`. -/
noncomputable def leftModuleOppositeFunctor
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    LeftDifferentialGradedModuleCategory A ⥤
      DifferentialGradedModuleCategory (oppositeDifferentialGradedAlgebra A) where
  obj M := leftModuleOpposite M
  map f := leftModuleOppositeHom f
  map_id := by
    intro M
    apply Subtype.ext
    rfl
  map_comp := by
    intro M N P f g
    apply Subtype.ext
    rfl

theorem leftModuleOpposite_is_equivalence
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    Functor.IsEquivalence (leftModuleOppositeFunctor A) := by
  sorry

/-! ## Shifts of left differential graded modules -/

/-- The canonical sign-bearing comparison
`Tot(A ⊗ M[k]) ≅ Tot(A ⊗ M)[k]`. -/
noncomputable abbrev leftDgmShiftTensorIso
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (k : ℤ) :
    tensorProductComplex R A.complex
        ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex) ≅
      (CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj
        (tensorProductComplex R A.complex M.complex) :=
  CochainComplex.mapBifunctorShift₂Iso A.complex M.complex
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) k

noncomputable def leftDgmShiftAction
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (k : ℤ) :
    tensorProductComplex R A.complex
        ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex) ⟶
      ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex) :=
  (leftDgmShiftTensorIso M k).hom ≫
    (CategoryTheory.shiftFunctor (CochainComplexOver R) k).map M.action

theorem leftDgmShiftAction_factorization
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (k : ℤ) :
    leftDgmShiftAction M k =
      (leftDgmShiftTensorIso M k).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplexOver R) k).map M.action := rfl

/-- The `k`-shifted left differential graded module. -/
noncomputable def leftDgmShift
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (k : ℤ) :
    LeftDifferentialGradedModule A where
  complex := (CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex
  action := leftDgmShiftAction M k
  one_action := by sorry
  assoc_action := by sorry

@[simp]
theorem leftDgmShift_component
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (k n : ℤ) :
    (leftDgmShift M k).complex.X n = M.complex.X (n + k) := rfl

theorem leftDgmShift_differential
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (k n m : ℤ) :
    (leftDgmShift M k).complex.d n m =
      k.negOnePow • M.complex.d (n + k) (m + k) := rfl

/-- The source's shifted-action formula; the factor is `(-1)^(deg(a)k)`. -/
theorem leftDgmShift_action_on_homogeneous
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (k p q : ℤ)
    (a : A.complex.X p) (x : (leftDgmShift M k).complex.X q) :
    (leftDgmShift M k).actionOnHomogeneous p q a x =
      ((p * k).negOnePow : ℤ) •
        transportComponent (C := M.complex)
          (show p + (q + k) = (p + q) + k by omega)
          (M.actionOnHomogeneous p (q + k) a x) := by
  sorry

theorem leftDgmShift_satisfiesLeibniz
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (k : ℤ) :
    (leftDgmShift M k).SatisfiesLeibniz := by
  exact LeftDifferentialGradedModule.satisfiesLeibniz (leftDgmShift M k)

/-- The opposite construction commutes with shifts, via the identity on the
underlying shifted complex. -/
noncomputable def leftModuleOpposite_shiftIso
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (k : ℤ) :
    leftModuleOpposite (leftDgmShift M k) ≅
      dgmShift (leftModuleOpposite M) k where
  hom := ⟨𝟙 _, by sorry⟩
  inv := ⟨𝟙 _, by sorry⟩
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

/-! ## Shifts of graded modules -/

/-- Reindexing the components of a graded module by `k`. -/
def gradedModuleShiftComponent {M : ℤ → Type v} (k : ℤ) : ℤ → Type v :=
  fun n => M (n + k)

/-- The right graded-module action after shifting the grading. -/
def rightGradedModuleShiftAction
    {A : ℤ → Type v} {M : ℤ → Type w} (k : ℤ)
    (action : ∀ i j, M i → A j → M (i + j)) :
    ∀ i j, gradedModuleShiftComponent (M := M) k i → A j →
      gradedModuleShiftComponent (M := M) k (i + j) :=
  fun i j x a =>
    transportGraded (X := M) (show (i + k) + j = (i + j) + k by omega)
      (action (i + k) j x a)

/-- The left graded-module action after shifting the grading. -/
def leftGradedModuleShiftAction
    {R : Type u} [CommRing R] {A : ℤ → Type v} {M : ℤ → Type w}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (k : ℤ)
    (action : ∀ i j, A i → M j → M (i + j)) :
    ∀ i j, A i → gradedModuleShiftComponent (M := M) k j →
      gradedModuleShiftComponent (M := M) k (i + j) :=
  fun i j a x =>
    transportGraded (X := M) (show i + (j + k) = (i + j) + k by omega)
      ((((i * k).negOnePow : ℤ) : R) • action i (j + k) a x)

/-! ## Homotopies -/

/-! A homotopy map is only required to be a graded module map.  It is not a
chain map in general: the homotopy equation says precisely that it becomes a
map to the shifted complex when `f = g`. -/
structure LeftGradedModuleHom
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M N : LeftDifferentialGradedModule A) where
  component : ∀ n : ℤ,
    M.complex.X n →ₗ[R] (leftDgmShift N (-1 : ℤ)).complex.X n
  map_action : ∀ (p q : ℤ) (a : A.complex.X p) (x : M.complex.X q),
    component (p + q) (M.actionOnHomogeneous p q a x) =
      (leftDgmShift N (-1 : ℤ)).actionOnHomogeneous p q a
        (component q x)

/-- A left-module homotopy consists of a degree `-1` graded module map and an
underlying chain homotopy.  The component equation identifies the two maps. -/
structure LeftDifferentialGradedModuleHomotopy
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : LeftDifferentialGradedModule A}
    (f g : LeftDifferentialGradedModuleHom M N) where
  shiftedMap : LeftGradedModuleHom M N
  homotopy : Homotopy f.underlying g.underlying
  component_eq : ∀ n : ℤ,
    HEq (shiftedMap.component n) (homotopy.hom n (n - 1)).hom

def LeftDifferentialGradedModuleHomotopic
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : LeftDifferentialGradedModule A}
    (f g : LeftDifferentialGradedModuleHom M N) : Prop :=
  Nonempty (LeftDifferentialGradedModuleHomotopy f g)

theorem leftDifferentialGradedModuleHomotopy_formula
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : LeftDifferentialGradedModule A}
    {f g : LeftDifferentialGradedModuleHom M N}
    (H : LeftDifferentialGradedModuleHomotopy f g) (n : ℤ)
    (x : M.complex.X n) :
    (f.underlying.f n).hom x - (g.underlying.f n).hom x =
      (N.complex.d (n - 1) n).hom
          ((H.homotopy.hom n (n - 1)).hom x) +
        (H.homotopy.hom (n + 1) n).hom
          ((M.complex.d n (n + 1)).hom x) := by
  sorry

theorem leftDifferentialGradedModuleHomotopy_self_shiftedMap_exists
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : LeftDifferentialGradedModule A}
    {f : LeftDifferentialGradedModuleHom M N}
    (H : LeftDifferentialGradedModuleHomotopy f f) :
    Nonempty (LeftDifferentialGradedModuleHom M (leftDgmShift N (-1 : ℤ))) := by
  sorry

/-- A self-homotopy gives the corresponding morphism to the shifted module. -/
noncomputable def leftDifferentialGradedModuleHomotopy_self_shiftedMap
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : LeftDifferentialGradedModule A}
    {f : LeftDifferentialGradedModuleHom M N}
    (H : LeftDifferentialGradedModuleHomotopy f f) :
    LeftDifferentialGradedModuleHom M (leftDgmShift N (-1 : ℤ)) :=
  Classical.choice (leftDifferentialGradedModuleHomotopy_self_shiftedMap_exists H)

/-- Opposite-module translation preserves and reflects homotopies. -/
theorem leftDifferentialGradedModuleHomotopic_iff_opposite
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : LeftDifferentialGradedModule A}
    (f g : LeftDifferentialGradedModuleHom M N) :
    LeftDifferentialGradedModuleHomotopic f g ↔
      DifferentialGradedModuleHomotopic
        (leftModuleOppositeHom f) (leftModuleOppositeHom g) := by
  sorry

/-! ## The left-module triangulated conclusion -/

/-- The right-module triangulated data over the opposite DGA is the
source-prescribed construction of the homotopy category, cones, admissible
short exact sequences, and distinguished triangles for left modules. -/
abbrev LeftDgmTriangulatedData
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) : Type _ :=
  DgmTriangulatedData (oppositeDifferentialGradedAlgebra A)

/-- The homotopy category of left differential graded `A`-modules is
triangulated, by transport through the opposite-module equivalence. -/
theorem leftModule_homotopy_category_triangulated
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    Nonempty (LeftDgmTriangulatedData A) := by
  exact dgm_homotopy_category_triangulated
    (oppositeDifferentialGradedAlgebra A)

end Formalization.Books.Dga.Unit11
