import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Formalization.Books.Categories.Unit43.MonoidalCategories
import Formalization.Books.Derived.Unit09.ConesAndTermwiseSplitSequences
import Formalization.Books.Homology.Unit13.Complexes
import Formalization.Books.Homology.Unit14.HomotopyAndShift
import Formalization.Books.MoreAlgebra.Unit58.TensorProductsOfComplexes
import Formalization.Books.MoreAlgebra.Unit72.HomComplexes

/-!
# More on Algebra, Chapter 73: Sign rules

This file records the conventions and interfaces in the source section
`Sign rules`.  The constructions which already have canonical Mathlib or
earlier-chapter representatives are exposed directly; the remaining
source-facing comparison maps are stated as theorem interfaces for the later
proof stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex

universe u

namespace Formalization.Books.MoreAlgebra.Unit73

abbrev Comp (R : Type u) [CommRing R] :=
  Formalization.Books.MoreAlgebra.Unit58.Comp R

abbrev K (R : Type u) [CommRing R] :=
  Formalization.Books.MoreAlgebra.Unit58.K R

/- Derived, Chapter 9 uses the earlier chapter's bundled additive-category
interface.  Module categories already have the two required Mathlib
instances, so this is the canonical bridge for the termwise-split triangle. -/
noncomputable instance moduleCatAdditiveCategory {R : Type u} [CommRing R] :
    Formalization.Books.Homology.Unit03.AdditiveCategory (ModuleCat.{u} R) where
  toPreadditive := inferInstance
  toHasFiniteProducts := inferInstance

/-! ## Shifts, connecting maps, and tensor signs -/

@[simp]
theorem shift_term_formula {R : Type u} [CommRing R]
    (M : Comp R) (k n : ℤ) :
    ((CategoryTheory.shiftFunctor (Comp R) k).obj M).X n = M.X (n + k) :=
  CochainComplex.shiftFunctor_obj_X' M k n

@[simp]
theorem shift_differential_formula {R : Type u} [CommRing R]
    (M : Comp R) (k n m : ℤ) :
    ((CategoryTheory.shiftFunctor (Comp R) k).obj M).d n m =
      k.negOnePow • M.d (n + k) (m + k) :=
  CochainComplex.shiftFunctor_obj_d' M k n m

@[simp]
theorem shifted_map_formula {R : Type u} [CommRing R]
    {M N : Comp R} (f : M ⟶ N) (k n : ℤ) :
    ((CategoryTheory.shiftFunctor (Comp R) k).map f).f n = f.f (n + k) :=
  CochainComplex.shiftFunctor_map_f' f k n

/- The source identifies cohomology in the direction
`H^n(M[k]) ≅ H^(n+k)(M)`.  The earlier chapter's comparison is oriented in
the reverse direction, so its inverse is the source-facing definition. -/
noncomputable def cohomologyShiftIso {R : Type u} [CommRing R]
    (M : Comp R) (k n : ℤ) :
    ((CategoryTheory.shiftFunctor (Comp R) k).obj M).homology n ≅
      M.homology (n + k) :=
  (Formalization.Books.Homology.Unit14.CochainComplex.cochainCohomologyShiftIso
    M k n).symm

noncomputable abbrev snakeBoundaryMap {R : Type u} [CommRing R]
    {S : ShortComplex (Comp R)} (hS : S.ShortExact) (n : ℤ) :
    S.X₃.homology n ⟶ S.X₁.homology (n + 1) :=
  Formalization.Books.Homology.Unit13.cochainConnectingMap hS n

/- The following names retain the source's termwise-split notation while
reusing the degreewise-split exact-sequence interface from Derived, Chapter 9. -/
abbrev TermwiseSplitExactSequence {R : Type u} [CommRing R]
    (K L M : Comp R) :=
  Formalization.Books.Derived.Unit09.TermwiseSplitExactSequence
    (C := ModuleCat.{u} R) K L M

abbrev termwiseSplitSection {R : Type u} [CommRing R]
    {K L M : Comp R} (S : TermwiseSplitExactSequence K L M) (n : ℤ) :=
  Formalization.Books.Derived.Unit09.termwiseSplitSection S n

abbrev termwiseSplitProjection {R : Type u} [CommRing R]
    {K L M : Comp R} (S : TermwiseSplitExactSequence K L M) (n : ℤ) :=
  Formalization.Books.Derived.Unit09.termwiseSplitProjection S n

abbrev termwiseSplitConnectingFamily {R : Type u} [CommRing R]
    {K L M : Comp R} (S : TermwiseSplitExactSequence K L M) (n : ℤ) :=
  Formalization.Books.Derived.Unit09.termwiseSplitConnectingFamily S n

noncomputable abbrev termwiseSplitConnectingMap {R : Type u} [CommRing R]
    {K L M : Comp R} (S : TermwiseSplitExactSequence K L M) :
    M ⟶ (CategoryTheory.shiftFunctor (Comp R) (1 : ℤ)).obj K :=
  Formalization.Books.Derived.Unit09.termwiseSplitConnectingMap S

theorem termwiseSplitConnectingMap_component {R : Type u} [CommRing R]
    {K L M : Comp R} (S : TermwiseSplitExactSequence K L M) (n : ℤ) :
    (termwiseSplitConnectingMap S).f n = termwiseSplitConnectingFamily S n :=
  Formalization.Books.Derived.Unit09.termwiseSplitConnectingMap_f S n

abbrev termwiseSplitTriangle {R : Type u} [CommRing R]
    {K L M : Comp R} (S : TermwiseSplitExactSequence K L M) :
    Triangle (Comp R) :=
  Formalization.Books.Derived.Unit09.termwiseSplitTriangle S

abbrev termwiseSplitTriangleh {R : Type u} [CommRing R]
    {K L M : Comp R} (S : TermwiseSplitExactSequence K L M) :
    Triangle (Formalization.Books.MoreAlgebra.Unit58.K R) :=
  Formalization.Books.Derived.Unit09.termwiseSplitTriangleh S

theorem termwiseSplitTriangleh_distinguished {R : Type u} [CommRing R]
    {K L M : Comp R} (S : TermwiseSplitExactSequence K L M) :
    termwiseSplitTriangleh S ∈
      distTriang (Formalization.Books.MoreAlgebra.Unit58.K R) := by
  sorry

/- The total-complex formula is already the canonical component formula from
More Algebra, Chapter 58. -/
abbrev totalTensor_differential_formula {R : Type u} [CommRing R]
    (L M : Comp R) (p q : ℤ) :=
  Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex_differential_formula
    R L M p q

abbrev shiftedTensorSign (p b : ℤ) : ℤˣ := (p * b).negOnePow

/- Mathlib's two-factor shift isomorphisms assemble to the source's
`Tot(M ⊗ N)[a+b] ≅ Tot(M[a] ⊗ N[b])`. -/
noncomputable def shiftedTensorIso {R : Type u} [CommRing R]
    (M N : Comp R) (a b : ℤ) :
    (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R M N)⟦a + b⟧ ≅
      Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        (M⟦a⟧) (N⟦b⟧) :=
  ((CochainComplex.mapBifunctorShift₂Iso
      (M⟦a⟧) N (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) b) ≪≫
      (CategoryTheory.shiftFunctor (Comp R) b).mapIso
        (CochainComplex.mapBifunctorShift₁Iso
          M N (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) a) ≪≫
      ((CategoryTheory.shiftFunctorAdd (Comp R) a b).app
        (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R M N)).symm).symm

/- The component theorem below is the canonical Mathlib source of the sign in
the preceding construction. -/
theorem shiftedTensor_second_factor_sign {R : Type u} [CommRing R]
    (M N : Comp R) (a b p q n : ℤ) (h : p + q = n) :
    ιMapBifunctor (M⟦a⟧) (N⟦b⟧)
        (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)
        p q n h ≫
        (CochainComplex.mapBifunctorShift₂Iso
          (M⟦a⟧) N (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) b).hom.f n =
      shiftedTensorSign p b •
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).obj (M.X (p + a))).map
          (CochainComplex.shiftFunctorObjXIso N b q (q + b) rfl).hom ≫
          ιMapBifunctor (M⟦a⟧) N
            (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)
            p (q + b) (n + b)
            (by dsimp; omega) ≫
          (CochainComplex.shiftFunctorObjXIso
            (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R (M⟦a⟧) N)
            b n (n + b) rfl).inv := by
  exact CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
    (M⟦a⟧) N (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) b p q n h
      (q + b) (n + b) rfl rfl

theorem shiftedTensorIso_component_sign {R : Type u} [CommRing R]
    (p b : ℤ) : shiftedTensorSign p b = (p * b).negOnePow := rfl

/- The second displayed form in the source is the corresponding map after
shifting the target by `-(a+b)`. -/
noncomputable def shiftedTensorMap {R : Type u} [CommRing R]
    (M N : Comp R) (a b : ℤ) :
    Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R M N ⟶
      (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        (M⟦a⟧) (N⟦b⟧))⟦-(a + b)⟧ :=
  (CategoryTheory.shiftFunctorZero (Comp R) ℤ).inv.app
      (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R M N) ≫
    (CategoryTheory.shiftFunctorAdd' (Comp R) (a + b) (-(a + b)) 0 (by ring)).hom.app
      (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R M N) ≫
    (CategoryTheory.shiftFunctor (Comp R) (-(a + b))).map
      (shiftedTensorIso M N a b).hom

theorem shiftedTensorIso_shifted_form {R : Type u} [CommRing R]
    (M N : Comp R) (a b : ℤ) :
    Nonempty ((Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R M N) ⟶
      (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        (M⟦a⟧) (N⟦b⟧))⟦-(a + b)⟧) :=
  ⟨shiftedTensorMap M N a b⟩

noncomputable abbrev tensorAssociativityIso {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L) M ≅
      Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K
        (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R L M) :=
  Formalization.Books.MoreAlgebra.Unit58.tensorAssociator R K L M

noncomputable abbrev tensorFlipIso {R : Type u} [CommRing R]
    (L M : Comp R) :
    Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R L M ≅
      Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R M L :=
  Formalization.Books.MoreAlgebra.Unit58.tensorBraiding R L M

abbrev tensorFlip_component_sign {R : Type u} [CommRing R]
    (L M : Comp R) (p q : ℤ) :=
  Formalization.Books.MoreAlgebra.Unit58.tensorBraiding_on_summand R L M p q

/-! ## Duals of modules and complexes -/

theorem leftDualModule_finiteProjective {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) [ExactPairing M N] :
    (Module.Finite R (M : Type u) ∧ Module.Projective R (M : Type u)) ∧
      (Module.Finite R (N : Type u) ∧ Module.Projective R (N : Type u)) := by
  sorry

theorem leftDualModule_dualIso {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) [ExactPairing M N] :
    Nonempty (Module.Dual R (M : Type u) ≃ₗ[R] (N : Type u)) := by
  sorry

theorem leftDualModule_evaluationFormula {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) [ExactPairing M N] :
    ∃ e : Module.Dual R (M : Type u) ≃ₗ[R] (N : Type u),
      ∀ (n : (N : Type u)) (m : (M : Type u)),
        (ExactPairing.evaluation M N).hom (n ⊗ₜ[R] m) = e.symm n m := by
  sorry

/- The converse construction is the graded dual with the signed dual
differential `-(-1)^n (d_M^{-n-1})^∨`. -/
noncomputable def dualComplex {R : Type u} [CommRing R] (M : Comp R) : Comp R where
  X n := ModuleCat.of R (Module.Dual R (M.X (-n) : Type u))
  d n m := ModuleCat.ofHom
    (-(n.negOnePow) • (M.d (-m) (-n)).hom.dualMap)
  shape n m hnm := by
    sorry
  d_comp_d' n m p hnm hmp := by
    sorry

@[simp]
theorem dualComplex_differential_formula {R : Type u} [CommRing R]
    (M : Comp R) (n m : ℤ) :
    (dualComplex M).d n m = ModuleCat.ofHom
      (-(n.negOnePow) • (M.d (-m) (-n)).hom.dualMap) := rfl

theorem leftDualComplex_bounded_and_finiteProjective {R : Type u} [CommRing R]
    (M N : Comp R) [ExactPairing M N] :
    Formalization.Books.Derived.Unit08.IsBounded
        (C := ModuleCat.{u} R) M ∧
      Formalization.Books.Derived.Unit08.IsBounded
        (C := ModuleCat.{u} R) N ∧
      (∀ n : ℤ,
        (Module.Finite R (M.X n : Type u) ∧ Module.Projective R (M.X n : Type u)) ∧
          (Module.Finite R (N.X n : Type u) ∧ Module.Projective R (N.X n : Type u))) := by
  sorry

theorem leftDualComplex_componentwise_duals {R : Type u} [CommRing R]
    (M N : Comp R) [ExactPairing M N] :
    ∀ n : ℤ, Nonempty (ExactPairing (N.X (-n)) (M.X n)) := by
  sorry

theorem leftDualComplex_signedDifferential {R : Type u} [CommRing R]
    (M N : Comp R) [ExactPairing M N] :
    ∃ e : ∀ n : ℤ,
        ModuleCat.of R (Module.Dual R (M.X (-n) : Type u)) ≅ N.X n,
      ∀ n : ℤ,
        N.d n (n + 1) =
          (e n).inv ≫ ModuleCat.ofHom
            (-(n.negOnePow) • (M.d (-(n + 1)) (-n)).hom.dualMap) ≫
            (e (n + 1)).hom := by
  sorry

theorem dualComplex_is_leftDual {R : Type u} [CommRing R]
    (M : Comp R)
    (hM : Formalization.Books.Derived.Unit08.IsBounded
      (C := ModuleCat.{u} R) M)
    (hfinite : ∀ n : ℤ,
      Module.Finite R (M.X n : Type u) ∧ Module.Projective R (M.X n : Type u)) :
    Nonempty (ExactPairing M (dualComplex M)) := by
  sorry

/-! ## Hom complexes and the remaining sign rules -/

abbrev homCochain {R : Type u} [CommRing R]
    (L M : Comp R) (n : ℤ) :=
  Formalization.Books.MoreAlgebra.Unit72.homCochain L M n

abbrev homDifferential {R : Type u} [CommRing R]
    (L M : Comp R) (n m : ℤ) : homCochain L M n →ₗ[R] homCochain L M m :=
  Formalization.Books.MoreAlgebra.Unit72.homDifferential L M n m

noncomputable abbrev homComplex {R : Type u} [CommRing R] (L M : Comp R) : Comp R :=
  Formalization.Books.MoreAlgebra.Unit72.homComplex L M

abbrev homComplex_degree_product {R : Type u} [CommRing R]
    (L M : Comp R) (n : ℤ) :=
  Formalization.Books.MoreAlgebra.Unit72.homCochain_product_equiv_exists L M n

abbrev homComplex_differential_component {R : Type u} [CommRing R]
    {L M : Comp R} {n m : ℤ} (h : n + 1 = m)
    (f : homCochain L M n) (p q : ℤ) (hpq : p + m = q) :=
  Formalization.Books.MoreAlgebra.Unit72.homDifferential_component h f p q hpq

theorem tensor_leftDual_hom_iso_exists {R : Type u} [CommRing R]
    (K M N : Comp R) [ExactPairing M N] :
    Nonempty (
      Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K N ≅
        homComplex M K) := by
  sorry

noncomputable def tensor_leftDual_hom_iso {R : Type u} [CommRing R]
    (K M N : Comp R) [ExactPairing M N] :
    Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K N ≅
      homComplex M K :=
  Classical.choice (tensor_leftDual_hom_iso_exists K M N)

/- The following maps are the source's signless composition, currying,
diagonal, and evaluation-and-more interfaces, in the order in which they
occur in the section. -/
noncomputable abbrev homCompositionMap {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        (homComplex L K) (homComplex M L) ⟶ homComplex M K :=
  Formalization.Books.MoreAlgebra.Unit72.homComposition M L K

noncomputable abbrev homCurryingIso {R : Type u} [CommRing R]
    (K L M : Comp R) :
    homComplex K (homComplex L M) ≅
      homComplex (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L) M :=
  Formalization.Books.MoreAlgebra.Unit72.homComposeIso K L M

noncomputable abbrev homDiagonalBetterMap {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        K (homComplex M L) ⟶
      homComplex M (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L) :=
  Formalization.Books.MoreAlgebra.Unit72.homDiagonalBetter K L M

noncomputable abbrev homDiagonalMap {R : Type u} [CommRing R]
    (K L : Comp R) :
    K ⟶ homComplex L
      (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L) :=
  Formalization.Books.MoreAlgebra.Unit72.homDiagonal K L

noncomputable abbrev homEvaluateAndMoreMap {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        (homComplex L M) K ⟶ homComplex (homComplex K L) M :=
  Formalization.Books.MoreAlgebra.Unit72.homEvaluate K L M

abbrev evaluationAndMoreSign (q r : ℤ) : ℤˣ :=
  Formalization.Books.MoreAlgebra.Unit72.evaluationSign 0 q r

theorem evaluationAndMoreSign_formula (q r : ℤ) :
    evaluationAndMoreSign q r = (r + q * r).negOnePow :=
  Formalization.Books.MoreAlgebra.Unit72.evaluationSign_solution 0 q r

def evaluationValue {R : Type u} [CommRing R]
    {K M : Comp R} {n m : ℤ}
    (f : homCochain K M m) (x : (K.X n : Type u)) : (M.X (n + m) : Type u) :=
  f.v n (n + m) rfl x

abbrev evaluationValueSign (n m : ℤ) : ℤˣ := (n * m).negOnePow

def homEvaluationValueSpecification {R : Type u} [CommRing R]
    (K M : Comp R) (e : K ⟶ homComplex (homComplex K M) M) : Prop :=
  ∀ (n m : ℤ) (x : (K.X n : Type u)) (f : homCochain K M m),
    ((e.f n x).v m (n + m) (by omega) f) =
      evaluationValueSign n m • evaluationValue f x

theorem homEvaluationMap_exists_with_value {R : Type u} [CommRing R]
    (K M : Comp R) :
    ∃ e : K ⟶ homComplex (homComplex K M) M,
      homEvaluationValueSpecification K M e := by
  sorry

theorem homEvaluationMap_exists {R : Type u} [CommRing R]
    (K M : Comp R) :
    Nonempty (K ⟶ homComplex (homComplex K M) M) := by
  obtain ⟨e, -⟩ := homEvaluationMap_exists_with_value K M
  exact ⟨e⟩

noncomputable def homEvaluationMap {R : Type u} [CommRing R]
    (K M : Comp R) : K ⟶ homComplex (homComplex K M) M :=
  Classical.choose (homEvaluationMap_exists_with_value K M)

theorem homEvaluationMap_value_formula {R : Type u} [CommRing R]
    (K M : Comp R) (n m : ℤ) (x : (K.X n : Type u))
    (f : homCochain K M m) :
    ((homEvaluationMap K M).f n x).v m (n + m) (by omega) f =
      evaluationValueSign n m • evaluationValue f x :=
  Classical.choose_spec (homEvaluationMap_exists_with_value K M) n m x f

theorem evaluationValue_sign_formula (n m : ℤ) :
    evaluationValueSign n m = (n * m).negOnePow := rfl

/- The source's signless shifted-Hom identification is the composite of the
canonical right- and left-shift equivalences for Hom-complex cochains. -/
noncomputable def homShiftIdentificationAt {R : Type u} [CommRing R]
    (M K : Comp R) (n a b : ℤ) :
    homCochain M K (n + a - b) ≃+
      homCochain (M⟦b⟧) (K⟦a⟧) n :=
  (CochainComplex.HomComplex.Cochain.rightShiftAddEquiv M K
      (n + a - b) a (n - b) (by omega)).trans
    (CochainComplex.HomComplex.Cochain.leftShiftAddEquiv M (K⟦a⟧)
      (n - b) b n (by omega))

noncomputable def homShiftedFormAt {R : Type u} [CommRing R]
    (M K : Comp R) (n a b : ℤ) :
    homCochain M K n ≃+
      homCochain (M⟦b⟧) (K⟦a⟧) (n + b - a) :=
  by
    exact
      (AddEquiv.cast (M := fun d : ℤ => homCochain M K d) (by ring)).trans
        (homShiftIdentificationAt M K (n + b - a) a b)

def homShiftedFormSpecification {R : Type u} [CommRing R]
    (M K : Comp R) (a b : ℤ)
    (e : homComplex M K ⟶ homComplex (M⟦b⟧) (K⟦a⟧)⟦b - a⟧) : Prop :=
  ∀ (n p q : ℤ) (h : p + q = n) (f : homCochain M K n),
    ((e.f n f).v (-q - b) (p - a) (by dsimp; omega)) =
      (n * b).negOnePow •
        (CochainComplex.shiftFunctorObjXIso M b (-q - b) (-q) (by ring)).hom ≫
          f.v (-q) p (by omega) ≫
          (CochainComplex.shiftFunctorObjXIso K a (p - a) p (by ring)).inv

theorem homShiftedForm_exists_with_sign {R : Type u} [CommRing R]
    (M K : Comp R) (a b : ℤ) :
    ∃ e : homComplex M K ⟶
        homComplex (M⟦b⟧) (K⟦a⟧)⟦b - a⟧,
      homShiftedFormSpecification M K a b e := by
  sorry

noncomputable def homShiftedFormMap {R : Type u} [CommRing R]
    (M K : Comp R) (a b : ℤ) :
    homComplex M K ⟶ homComplex (M⟦b⟧) (K⟦a⟧)⟦b - a⟧ :=
  Classical.choose (homShiftedForm_exists_with_sign M K a b)

theorem homShiftedFormMap_specification {R : Type u} [CommRing R]
    (M K : Comp R) (a b : ℤ) :
    homShiftedFormSpecification M K a b (homShiftedFormMap M K a b) :=
  Classical.choose_spec (homShiftedForm_exists_with_sign M K a b)

theorem homShiftIdentification_exists {R : Type u} [CommRing R]
    (M K : Comp R) (a b : ℤ) :
    Nonempty (homComplex M K⟦a - b⟧ ≅ homComplex (M⟦b⟧) (K⟦a⟧)) := by
  sorry

theorem homShiftedForm_exists {R : Type u} [CommRing R]
    (M K : Comp R) (a b : ℤ) :
    Nonempty (homComplex M K ⟶
      homComplex (M⟦b⟧) (K⟦a⟧)⟦b - a⟧) := by
  exact ⟨homShiftedFormMap M K a b⟩

abbrev homShiftSign (n b : ℤ) : ℤˣ := (n * b).negOnePow

theorem homShift_component_sign (n b : ℤ) :
    homShiftSign n b = (n * b).negOnePow := rfl

theorem homShift_differential_sign_identity (a b n : ℤ) :
    (b - a).negOnePow * a.negOnePow = b.negOnePow ∧
      (b - a).negOnePow * (n + b - a).negOnePow * b.negOnePow =
        (n + b).negOnePow := by
  sorry

abbrev homShift_differential_calculation {R : Type u} [CommRing R]
    {M K : Comp R} (a b n m : ℤ) (h : n + 1 = m)
    (f : homCochain (M⟦b⟧) (K⟦a⟧) n) (p q : ℤ)
    (hpq : p + m = q) :=
  homComplex_differential_component h f p q hpq

end Formalization.Books.MoreAlgebra.Unit73
