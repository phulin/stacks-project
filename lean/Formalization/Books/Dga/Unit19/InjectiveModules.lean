import Formalization.Books.Dga.Unit18.InjectiveModules
import Formalization.Books.Dga.Unit17.InjectiveModules
import Formalization.Books.Dga.Unit13.HomComplexes
import Formalization.Books.Dga.Unit07.AdmissibleShortExactSequences
import Formalization.Books.MoreAlgebra.Unit55.InjectiveModules
import Mathlib.Algebra.Ring.NegOnePow

/-!
# Differential Graded Algebra, Chapter 19: Injective modules and differential graded algebras

This file records the final differential-graded injective statements.  The
right-module DG model and its admissible maps come from Chapters 4 and 7;
the dual components use the earlier additive character dual
`Hom(-, ℚ / ℤ)`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit05
open Formalization.Books.Dga.Unit07
open Formalization.Books.Dga.Unit11
open Formalization.Books.Dga.Unit13
open Formalization.Books.MoreAlgebra.Unit55

universe u

namespace Formalization.Books.Dga.Unit19

/-! ## Graded injectivity and admissible monomorphisms -/

abbrev DgaModule {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) := DifferentialGradedModule A

abbrev DgaLeftModule {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) := LeftDifferentialGradedModule A

/- The preceding chapters expose the graded hom type but do not package a
   separate category whose objects forget the differentials.  This is the
   extension-property form of “injective object of the abelian category of
   graded modules”, restricted to the DG objects used by this chapter. -/
def DgmGradedDegreewiseInjective
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {K L : DgaModule A} (f : DgmGradedHom K L) : Prop :=
  ∀ n : ℤ, Function.Injective (f.component n)

def DgmGradedInjective
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (I : DgaModule A) : Prop :=
  ∀ (K L : DgaModule A) (f : DgmGradedHom K L),
    DgmGradedDegreewiseInjective f →
      ∀ g : DgmGradedHom K I,
        ∃ h : DgmGradedHom L I, DgmGradedHom.comp f h = g

/- The source's “injective homomorphism” is made explicit degreewise; the
   conclusion reuses the chapter-7 admissible-monomorphism definition. -/
theorem source_graded_injective_admissible
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {I M : DgaModule A} (f : DifferentialGradedModuleHom I M)
    (hf : ∀ n : ℤ, Function.Injective (f.underlying.f n))
    (hI : DgmGradedInjective I) :
    DgmAdmissibleMonomorphism f := by
  sorry

/-! ## The differential graded character dual -/

/- The component of the cochain-level character dual is
`Hom_Z(C^(-n), ℚ / ℤ)`.  The differential is the signed precomposition
map; the sign is the one in the Hom-complex convention used in Chapter 13. -/
noncomputable def dgmCharacterDualComplex
    {R : Type u} [CommRing R] (C : CochainComplexOver R) :
    CochainComplexOver R where
  X n := ModuleCat.of R (CharacterDual R (C.X (-n)))
  d n m := by
    classical
    by_cases h : n + 1 = m
    · subst m
      exact ModuleCat.ofHom
        (((((n + 1).negOnePow : ℤ) : R) •
          characterDualMap (R := R)
            ((C.d (-(n + 1)) (-n)).hom)))
    · exact 0
  shape n m hnm := by
    classical
    by_cases h : n + 1 = m
    · exact (hnm (by simpa only [ComplexShape.up_Rel] using h)).elim
    · apply ModuleCat.hom_ext
      simp [h]
  d_comp_d' := by
    sorry

/- A dual DG module is characterized by the canonical component family and
   its DG-module structure.  The source's action and sign checks are exactly
   the construction discussed in Chapters 13 and 18, so the chosen object is
   exposed together with its component identification. -/
structure DgmCharacterDualRightSpec
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaLeftModule A) where
  object : DgaModule A
  component_eq : ∀ n : ℤ,
    (object.complex.X n : Type u) =
      (dgmCharacterDualComplex M.complex).X n
  action_formula : ∀ (n m : ℤ)
      (f : CharacterDual R (M.complex.X (-n)))
      (a : A.complex.X m) (y : M.complex.X (-(n + m))),
    (show CharacterDual R (M.complex.X (-(n + m))) from
      cast (component_eq (n + m))
        (object.actionOnHomogeneous n m
        (cast (component_eq n).symm f) a)) y =
      f (transportComponent (C := M.complex) (by omega)
        (M.actionOnHomogeneous m (-(n + m)) a y))

theorem dgmCharacterDualRightSpec_nonempty
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaLeftModule A) :
    Nonempty (DgmCharacterDualRightSpec M) := by
  sorry

noncomputable def dgmCharacterDualOfLeft
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaLeftModule A) : DgaModule A :=
  (Classical.choice (dgmCharacterDualRightSpec_nonempty M)).object

theorem dgmCharacterDualOfLeft_component
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaLeftModule A) (n : ℤ) :
    ((dgmCharacterDualOfLeft M).complex.X n : Type u) =
      (dgmCharacterDualComplex M.complex).X n :=
  (Classical.choice (dgmCharacterDualRightSpec_nonempty M)).component_eq n

structure DgmCharacterDualLeftSpec
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaModule A) where
  object : DgaLeftModule A
  component_eq : ∀ n : ℤ,
    (object.complex.X n : Type u) =
      (dgmCharacterDualComplex M.complex).X n
  action_formula : ∀ (n m : ℤ)
      (a : A.complex.X m)
      (f : CharacterDual R (M.complex.X (-n)))
      (y : M.complex.X (-(m + n))),
    (show CharacterDual R (M.complex.X (-(m + n))) from
      cast (component_eq (m + n))
        (object.actionOnHomogeneous m n a
          (cast (component_eq n).symm f))) y =
      (m * n).negOnePow •
        f (transportComponent (C := M.complex) (by omega)
          (M.actionOnHomogeneous (-(m + n)) m y a))

theorem dgmCharacterDualLeftSpec_nonempty
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaModule A) :
    Nonempty (DgmCharacterDualLeftSpec M) := by
  sorry

noncomputable def dgmCharacterDualOfRight
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaModule A) : DgaLeftModule A :=
  (Classical.choice (dgmCharacterDualLeftSpec_nonempty M)).object

theorem dgmCharacterDualOfRight_component
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaModule A) (n : ℤ) :
    ((dgmCharacterDualOfRight M).complex.X n : Type u) =
      (dgmCharacterDualComplex M.complex).X n :=
  (Classical.choice (dgmCharacterDualLeftSpec_nonempty M)).component_eq n

/- The evaluation maps are DG-module maps.  Their source and target types
   encode the left/right reversal from the source paragraph; `HEq` records
   the component identifications supplied by the dual specifications. -/
structure DgmLeftEvaluationSpec
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaLeftModule A) where
  map : LeftDifferentialGradedModuleHom M
    (dgmCharacterDualOfRight (dgmCharacterDualOfLeft M))
  formula : ∀ (n : ℤ) (x : M.complex.X n),
    HEq ((map.underlying.f n).hom x)
      (Formalization.Books.Dga.Unit17.characterEvaluationAt x)

structure DgmRightEvaluationSpec
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaModule A) where
  map : DifferentialGradedModuleHom M
    (dgmCharacterDualOfLeft (dgmCharacterDualOfRight M))
  formula : ∀ (n : ℤ) (x : M.complex.X n),
    HEq ((map.underlying.f n).hom x)
      (Formalization.Books.Dga.Unit17.characterEvaluationAt x)

theorem dgm_left_evaluation_exists
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaLeftModule A) :
    Nonempty (DgmLeftEvaluationSpec M) := by
  sorry

noncomputable def dgm_left_evaluation
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaLeftModule A) :
    LeftDifferentialGradedModuleHom M
      (dgmCharacterDualOfRight (dgmCharacterDualOfLeft M)) :=
  (Classical.choice (dgm_left_evaluation_exists M)).map

theorem dgm_right_evaluation_exists
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaModule A) :
    Nonempty (DgmRightEvaluationSpec M) := by
  sorry

noncomputable def dgm_right_evaluation
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaModule A) :
    DifferentialGradedModuleHom M
      (dgmCharacterDualOfLeft (dgmCharacterDualOfRight M)) :=
  (Classical.choice (dgm_right_evaluation_exists M)).map

/-! ## Maps into a dual and differential graded bilinear maps -/

structure DgaCharacterBilinear
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (N : DgaModule A) (M : DgaLeftModule A) where
  component : ∀ n : ℤ,
    N.complex.X n →+ (M.complex.X (-n) →+ RationalModInteger)
  balanced : ∀ (n m : ℤ) (x : N.complex.X n) (a : A.complex.X m)
      (y : M.complex.X (-(n + m))),
    component (n + m) (N.actionOnHomogeneous n m x a) y =
      component n x
        (transportComponent (C := M.complex) (by omega)
          (M.actionOnHomogeneous m (-(n + m)) a y))
  differential : ∀ (n : ℤ) (x : N.complex.X n)
      (y : M.complex.X (-(n + 1))),
    component (n + 1) ((N.complex.d n (n + 1)).hom x) y +
        (n.negOnePow : ℤ) •
          component n x
            (transportComponent (C := M.complex) (by omega)
              ((M.complex.d (-(n + 1)) (-n)).hom y)) = 0

/- This is the usable form of the two displayed Hom equalities: the second
   equality is the tensor-product universal property already formalized in
   Chapter 12, while this chapter records its character-valued bilinear-map
   endpoint. -/
theorem dgm_map_into_dual_equiv
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (N : DgaModule A) (M : DgaLeftModule A) :
    Nonempty (DifferentialGradedModuleHom N
      (dgmCharacterDualOfLeft M) ≃ DgaCharacterBilinear N M) := by
  sorry

/-! ## The regular dual and shifted Hom computations -/

noncomputable def dgmLeftRegularModule
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    DgaLeftModule A where
  complex := A.complex
  action := A.multiplication
  one_action := by
    sorry
  assoc_action := by
    sorry

noncomputable def dgmAlgebraDual
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    DgaModule A :=
  dgmCharacterDualOfLeft (dgmLeftRegularModule A)

abbrev dgmDualCycles
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaModule A) (k : ℤ) :=
  LinearMap.ker ((dgmCharacterDualOfRight M).complex.d k (k + 1)).hom

theorem dgm_hom_into_shifted_algebra_dual_equiv
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaModule A) (k : ℤ) :
    Nonempty (DifferentialGradedModuleHom M
      (dgmShift (dgmAlgebraDual A) k) ≃ dgmDualCycles M k) := by
  sorry

theorem dgm_homotopy_hom_into_shifted_algebra_dual_equiv
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DgaModule A) (k : ℤ) :
    Nonempty
      (((differentialGradedModuleHomotopyQuotient A).obj M ⟶
        (differentialGradedModuleHomotopyQuotient A).obj
          (dgmShift (dgmAlgebraDual A) k)) ≃
        ((dgmCharacterDualOfRight M).complex.homology k : Type u)) := by
  sorry

/- The phrase “as functors in M” is retained as a family-level interface;
   the displayed equivalences above are its component at `M`. -/
def DgmShiftDualComparison
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) (k : ℤ) : Prop :=
  ∀ M : DgaModule A,
    Nonempty (DifferentialGradedModuleHom M
      (dgmShift (dgmAlgebraDual A) k) ≃ dgmDualCycles M k) ∧
    Nonempty
      (((differentialGradedModuleHomotopyQuotient A).obj M ⟶
        (differentialGradedModuleHomotopyQuotient A).obj
          (dgmShift (dgmAlgebraDual A) k)) ≃
        ((dgmCharacterDualOfRight M).complex.homology k : Type u))

theorem dgm_shift_dual_comparison
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) (k : ℤ) :
    DgmShiftDualComparison A k := by
  unfold DgmShiftDualComparison
  intro M
  exact ⟨dgm_hom_into_shifted_algebra_dual_equiv M k,
    dgm_homotopy_hom_into_shifted_algebra_dual_equiv M k⟩

end Formalization.Books.Dga.Unit19
