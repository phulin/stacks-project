import Formalization.Books.Dga.Unit12.TensorProduct
import Formalization.Books.MoreAlgebra.Unit72.HomComplexes

/-!
# Differential Graded Algebra, Chapter 13: Hom complexes and differential graded modules

This file formalizes the source section on the Hom complex.  The underlying
Hom complex, its componentwise differential, composition, and shift maps are
the canonical constructions from More on Algebra, Chapter 72.  This chapter
adds the differential graded algebra and module structures obtained from
those constructions, together with the tensor--Hom and evaluation interfaces
used in the source.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open HomologicalComplex
open ComplexShape
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit11
open Formalization.Books.Dga.Unit12
open Formalization.Books.MoreAlgebra.Unit72

universe u

namespace Formalization.Books.Dga.Unit13

/-! ## The Hom complex and the endomorphism DGA -/

abbrev HomCochain {R : Type u} [CommRing R]
    (M N : CochainComplexOver R) (n : ℤ) :=
  Formalization.Books.MoreAlgebra.Unit72.homCochain M N n

abbrev HomComplex {R : Type u} [CommRing R]
    (M N : CochainComplexOver R) : CochainComplexOver R :=
  Formalization.Books.MoreAlgebra.Unit72.homComplex M N

abbrev HomComposition {R : Type u} [CommRing R]
    (K L M : CochainComplexOver R) :
    tensorProductComplex R (HomComplex L M) (HomComplex K L) ⟶ HomComplex K M :=
  Formalization.Books.MoreAlgebra.Unit72.homComposition K L M

/- The unit is the chain map corresponding to the identity cocycle.  The
   module-valued lift is not bundled by the earlier API, so this is the small
   bridge needed by the DGA structure below. -/
theorem homIdentity_exists {R : Type u} [CommRing R]
    (M : CochainComplexOver R) :
    Nonempty (tensorUnitComplex R ⟶ HomComplex M M) := by
  sorry

noncomputable def homIdentity {R : Type u} [CommRing R]
    (M : CochainComplexOver R) : tensorUnitComplex R ⟶ HomComplex M M :=
  Classical.choice (homIdentity_exists M)

/- The evaluation chain map is the total-complex version of `(f, x) ↦ f x`.
   Its componentwise construction is canonical, but was not exposed as a
   module-valued map by the earlier chapter. -/
theorem homEvaluation_exists {R : Type u} [CommRing R]
    (M N : CochainComplexOver R) :
    Nonempty (tensorProductComplex R (HomComplex M N) M ⟶ N) := by
  sorry

noncomputable def homEvaluation {R : Type u} [CommRing R]
    (M N : CochainComplexOver R) :
    tensorProductComplex R (HomComplex M N) M ⟶ N :=
  Classical.choice (homEvaluation_exists M N)

/- The composition map is the multiplication of the endomorphism DGA. -/
noncomputable def homEndomorphismDGA {R : Type u} [CommRing R]
    (M : CochainComplexOver R) : DifferentialGradedAlgebra R where
  complex := HomComplex M M
  multiplication := HomComposition M M M
  unit := homIdentity M
  one_mul := by sorry
  mul_one := by sorry
  mul_assoc := by sorry

/- The original complex is the canonical left module over its endomorphism
   DGA by evaluation. -/
noncomputable def homEndomorphismModule {R : Type u} [CommRing R]
    (M : CochainComplexOver R) :
    LeftDifferentialGradedModule (homEndomorphismDGA M) where
  complex := M
  action := homEvaluation M M
  one_action := by sorry
  assoc_action := by sorry

theorem homEndomorphismModule_action_factorization
    {R : Type u} [CommRing R] (M : CochainComplexOver R) :
    (homEndomorphismModule M).action = homEvaluation M M := rfl

theorem homEndomorphismDGA_multiplication_factorization
    {R : Type u} [CommRing R] (M : CochainComplexOver R) :
    (homEndomorphismDGA M).multiplication = HomComposition M M M := rfl

/- The right endomorphism action is composition with an endomorphism of the
   source complex. -/
noncomputable def homEndomorphismRightAction
    {R : Type u} [CommRing R] (M N : CochainComplexOver R) :
    tensorProductComplex R (HomComplex M N) (homEndomorphismDGA M).complex ⟶
      HomComplex M N :=
  HomComposition M M N

noncomputable def homEndomorphismRightModule
    {R : Type u} [CommRing R] (M N : CochainComplexOver R) :
    DifferentialGradedModule (homEndomorphismDGA M) where
  complex := HomComplex M N
  action := homEndomorphismRightAction M N
  one_action := by sorry
  assoc_action := by sorry

/-! ## Left module structures and the first Hom module -/

/- A left module on a fixed complex, with the complex omitted from the
   structure because it is a parameter. -/
structure LeftDGMStructure {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) (M : CochainComplexOver R) where
  action : tensorProductComplex R A.complex M ⟶ M
  one_action :
    tensorHomComplex A.unit (𝟙 M) ≫ action =
      (HomologicalComplex.leftUnitor M).hom
  assoc_action :
    tensorHomComplex A.multiplication (𝟙 M) ≫ action =
      (HomologicalComplex.associator A.complex A.complex M).hom ≫
        tensorHomComplex (𝟙 A.complex) action ≫ action

theorem leftModuleStructure_equiv_exists
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
    (M : CochainComplexOver R) :
    Nonempty (LeftDGMStructure A M ≃
      DifferentialGradedAlgebraHom A (homEndomorphismDGA M)) := by
  sorry

noncomputable def leftModuleStructureEquiv
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
    (M : CochainComplexOver R) :
    LeftDGMStructure A M ≃ DifferentialGradedAlgebraHom A (homEndomorphismDGA M) :=
  Classical.choice (leftModuleStructure_equiv_exists A M)

theorem leftModule_to_endomorphismHom_exists
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) :
    Nonempty (DifferentialGradedAlgebraHom A
      (homEndomorphismDGA M.complex)) := by
  sorry

noncomputable def leftModule_to_endomorphismHom
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) :
    DifferentialGradedAlgebraHom A (homEndomorphismDGA M.complex) :=
  Classical.choice (leftModule_to_endomorphismHom_exists M)

/- The right action on `Hom(M, N)` is composition on the source side. -/
noncomputable def homRightAction
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (N : CochainComplexOver R) :
    tensorProductComplex R (HomComplex M.complex N) A.complex ⟶
      HomComplex M.complex N :=
  tensorHomComplex (𝟙 (HomComplex M.complex N))
      (leftModule_to_endomorphismHom M).map ≫
    HomComposition M.complex M.complex N

noncomputable def homRightModule
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (N : CochainComplexOver R) :
    DifferentialGradedModule A where
  complex := HomComplex M.complex N
  action := homRightAction M N
  one_action := by sorry
  assoc_action := by sorry

/- The source's component formula has no sign.  `Cochain.comp` is the
   canonical componentwise operation used here. -/
def homRightCompositionOnCochains
    {R : Type u} [CommRing R]
    {M N : CochainComplexOver R} (n m : ℤ)
    (f : HomCochain M N n) (a : HomCochain M M m) :
    HomCochain M N (n + m) :=
  CochainComplex.HomComplex.Cochain.comp a f (by omega)

theorem homRightModule_action_formula
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (N : CochainComplexOver R)
    (n m : ℤ) (f : HomCochain M.complex N n)
    (a : A.complex.X m) :
    (homRightModule M N).actionOnHomogeneous n m f a =
      (homRightCompositionOnCochains n m f
        (((leftModule_to_endomorphismHom M).map.f m).hom a)) := by
  sorry

/- The source's tensor--Hom adjunction for right differential graded modules. -/
theorem hom_right_module_hom_equiv_exists
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M' : DifferentialGradedModule A)
    (M : LeftDifferentialGradedModule A) (N : CochainComplexOver R) :
    Nonempty (DifferentialGradedModuleHom M' (homRightModule M N) ≃
      (differentialGradedTensorProduct M' M ⟶ N)) := by
  sorry

noncomputable def hom_right_module_hom_equiv
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M' : DifferentialGradedModule A)
    (M : LeftDifferentialGradedModule A) (N : CochainComplexOver R) :
    DifferentialGradedModuleHom M' (homRightModule M N) ≃
      (differentialGradedTensorProduct M' M ⟶ N) :=
  Classical.choice (hom_right_module_hom_equiv_exists M' M N)

/-! ## Right modules, the opposite endomorphism DGA, and the second Hom module -/

structure RightDGMStructure {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) (M : CochainComplexOver R) where
  action : tensorProductComplex R M A.complex ⟶ M
  one_action :
    tensorHomComplex (𝟙 M) A.unit ≫ action =
      (HomologicalComplex.rightUnitor M).hom
  assoc_action :
    tensorHomComplex action (𝟙 A.complex) ≫ action =
      (HomologicalComplex.associator M A.complex A.complex).hom ≫
        tensorHomComplex (𝟙 M) A.multiplication ≫ action

theorem rightModuleStructure_equiv_exists
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
    (M : CochainComplexOver R) :
    Nonempty (RightDGMStructure A M ≃
      DifferentialGradedAlgebraHom A
        (oppositeDifferentialGradedAlgebra (homEndomorphismDGA M))) := by
  sorry

noncomputable def rightModuleStructureEquiv
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
    (M : CochainComplexOver R) :
    RightDGMStructure A M ≃ DifferentialGradedAlgebraHom A
      (oppositeDifferentialGradedAlgebra (homEndomorphismDGA M)) :=
  Classical.choice (rightModuleStructure_equiv_exists A M)

theorem rightModule_to_opposite_endomorphismHom_exists
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) :
    Nonempty (DifferentialGradedAlgebraHom A
      (oppositeDifferentialGradedAlgebra (homEndomorphismDGA M.complex))) := by
  sorry

noncomputable def rightModule_to_opposite_endomorphismHom
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) :
    DifferentialGradedAlgebraHom A
      (oppositeDifferentialGradedAlgebra (homEndomorphismDGA M.complex)) :=
  Classical.choice (rightModule_to_opposite_endomorphismHom_exists M)

/- The component of the map to the opposite endomorphism DGA.  This is the
   signed formula in the source, with the target index written as `n - q`. -/
noncomputable def rightModuleTauComponent
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (n q : ℤ) (a : A.complex.X n) :
    M.complex.X (-q) ⟶ M.complex.X (n - q) :=
  ModuleCat.ofHom
    { toFun := fun x =>
        ((((-n * q).negOnePow : ℤ) : R) •
          transportComponent (C := M.complex) (by omega)
            (M.actionOnHomogeneous (-q) n x a))
      map_add' := by sorry
      map_smul' := by sorry }

theorem rightModule_tau_component_formula
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (n q : ℤ) (a : A.complex.X n)
    (x : M.complex.X (-q)) :
    (((rightModule_to_opposite_endomorphismHom M).map.f n).hom a).v
        (-q) (n - q) (by omega) x =
      (rightModuleTauComponent M n q a).hom x := by
  sorry

theorem rightModule_tau_opposite_multiplicativity
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) :
    A.multiplication ≫ (rightModule_to_opposite_endomorphismHom M).map =
      tensorHomComplex (rightModule_to_opposite_endomorphismHom M).map
          (rightModule_to_opposite_endomorphismHom M).map ≫
        (oppositeDifferentialGradedAlgebra (homEndomorphismDGA M.complex)).multiplication :=
  (rightModule_to_opposite_endomorphismHom M).map_multiplication

/- Written on homogeneous elements, the preceding opposite-algebra map is
   exactly the signed reverse-composition identity from the source. -/
theorem rightModule_tau_signed_reverse_formula
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (n m : ℤ)
    (a : A.complex.X n) (b : A.complex.X m) :
    (((rightModule_to_opposite_endomorphismHom M).map.f (n + m)).hom
      ((A.homogeneousMultiplication n m).hom (a ⊗ₜ[R] b))) =
      transportComponent (C := (homEndomorphismDGA M.complex).complex) (by omega)
        ((n * m).negOnePow •
          (homEndomorphismDGA M.complex).homogeneousMultiplication m n |>.hom
            ((((rightModule_to_opposite_endomorphismHom M).map.f m).hom b) ⊗ₜ[R]
              (((rightModule_to_opposite_endomorphismHom M).map.f n).hom a))) := by
  sorry

noncomputable def homLeftAction
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (N : CochainComplexOver R) :
    tensorProductComplex R A.complex (HomComplex M.complex N) ⟶
      HomComplex M.complex N :=
  (tensorFlipIso R A.complex (HomComplex M.complex N)).hom ≫
    tensorHomComplex (𝟙 (HomComplex M.complex N))
      (rightModule_to_opposite_endomorphismHom M).map ≫
    HomComposition M.complex M.complex N

noncomputable def homLeftModule
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (N : CochainComplexOver R) :
    LeftDifferentialGradedModule A where
  complex := HomComplex M.complex N
  action := homLeftAction M N
  one_action := by sorry
  assoc_action := by sorry

def homLeftCompositionOnCochains
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (N : CochainComplexOver R)
    (n m : ℤ) (a : A.complex.X n)
    (f : HomCochain M.complex N m) :
    HomCochain M.complex N (n + m) := by
  let τ := ((rightModule_to_opposite_endomorphismHom M).map.f n).hom a
  exact ((n * m).negOnePow •
    CochainComplex.HomComplex.Cochain.comp τ f (by omega))

theorem homLeftModule_action_formula
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (N : CochainComplexOver R)
    (n m : ℤ) (a : A.complex.X n) (f : HomCochain M.complex N m) :
    (homLeftModule M N).actionOnHomogeneous n m a f =
      homLeftCompositionOnCochains M N n m a f := by
  sorry

theorem hom_left_module_hom_equiv_exists
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A)
    (M' : LeftDifferentialGradedModule A) (N : CochainComplexOver R) :
    Nonempty (LeftDifferentialGradedModuleHom M' (homLeftModule M N) ≃
      (differentialGradedTensorProduct M M' ⟶ N)) := by
  sorry

noncomputable def hom_left_module_hom_equiv
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A)
    (M' : LeftDifferentialGradedModule A) (N : CochainComplexOver R) :
    LeftDifferentialGradedModuleHom M' (homLeftModule M N) ≃
      (differentialGradedTensorProduct M M' ⟶ N) :=
  Classical.choice (hom_left_module_hom_equiv_exists M M' N)

/-! ## Componentwise evaluation formulas and evaluation maps -/

def homEvaluationComponent
    {R : Type u} [CommRing R] {M N : CochainComplexOver R}
    (n e : ℤ) (f : HomCochain M N n) (x : M.X e) : N.X (e + n) :=
  (f.v e (e + n) (by omega)).hom x

noncomputable def homEvaluationOnHomogeneous
    {R : Type u} [CommRing R] (M N : CochainComplexOver R)
    (n e : ℤ) (f : HomCochain M N n) (x : M.X e) : N.X (e + n) :=
  (HomologicalComplex.ιTensorObj (HomComplex M N) M n e (e + n) (by omega) ≫
      (homEvaluation M N).f (e + n)).hom (f ⊗ₜ[R] x)

theorem homEvaluation_on_homogeneous
    {R : Type u} [CommRing R] (M N : CochainComplexOver R)
    (n e : ℤ) (f : HomCochain M N n) (x : M.X e) :
    homEvaluationOnHomogeneous M N n e f x = homEvaluationComponent n e f x := by
  sorry

def rightHomEvaluationComponent
    {R : Type u} [CommRing R] {M N : CochainComplexOver R}
    (m e : ℤ) (f : HomCochain M N m) (x : M.X e) : N.X (e + m) :=
  (((m * e).negOnePow : ℤ) : R) • (f.v e (e + m) (by omega)).hom x

theorem left_evaluation_exists
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (N : CochainComplexOver R) :
    Nonempty (LeftDifferentialGradedModuleHom M
      (homLeftModule (homRightModule M N) N)) := by
  sorry

noncomputable def left_evaluation
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (N : CochainComplexOver R) :
    LeftDifferentialGradedModuleHom M (homLeftModule (homRightModule M N) N) :=
  Classical.choice (left_evaluation_exists M N)

theorem left_evaluation_component_formula
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (N : CochainComplexOver R)
    (e m : ℤ) (x : M.complex.X e) (f : HomCochain M.complex N m) :
    (((left_evaluation M N).underlying.f e).hom x).v m (e + m)
        (by omega) f = homEvaluationComponent m e f x := by
  sorry

theorem right_evaluation_exists
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (N : CochainComplexOver R) :
    Nonempty (DifferentialGradedModuleHom M
      (homRightModule (homLeftModule M N) N)) := by
  sorry

noncomputable def right_evaluation
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (N : CochainComplexOver R) :
    DifferentialGradedModuleHom M (homRightModule (homLeftModule M N) N) :=
  Classical.choice (right_evaluation_exists M N)

theorem right_evaluation_component_formula
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (N : CochainComplexOver R)
    (e m : ℤ) (x : M.complex.X e) (f : HomCochain M.complex N m) :
    (((right_evaluation M N).underlying.f e).hom x).v m (e + m)
        (by omega) f = rightHomEvaluationComponent m e f x := by
  sorry

/-! ## Shifted Hom complexes and module compatibility -/

theorem homShiftIso_exists
    {R : Type u} [CommRing R] (M N : CochainComplexOver R) (k : ℤ) :
    Nonempty ((CategoryTheory.shiftFunctor (CochainComplexOver R) (-k)).obj
        (HomComplex M N) ≅
      HomComplex ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M) N) := by
  sorry

noncomputable def homShiftIso
    {R : Type u} [CommRing R] (M N : CochainComplexOver R) (k : ℤ) :
    (CategoryTheory.shiftFunctor (CochainComplexOver R) (-k)).obj
        (HomComplex M N) ≅
      HomComplex ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M) N :=
  Classical.choice (homShiftIso_exists M N k)

theorem homShiftIso_is_right_dgm_map
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : LeftDifferentialGradedModule A) (N : CochainComplexOver R) (k : ℤ) :
    ∃ f : DifferentialGradedModuleHom
        (dgmShift (homRightModule M N) (-k))
        (homRightModule (leftDgmShift M k) N),
      f.underlying = (homShiftIso M.complex N k).hom ∧ IsIso f.underlying := by
  sorry

theorem homShiftIso_is_left_dgm_map
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (N : CochainComplexOver R) (k : ℤ) :
    ∃ f : LeftDifferentialGradedModuleHom
        (leftDgmShift (homLeftModule M N) (-k))
        (homLeftModule (dgmShift M k) N),
      f.underlying = (homShiftIso M.complex N k).hom ∧ IsIso f.underlying := by
  sorry

end Formalization.Books.Dga.Unit13
