import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Examples, Chapter 23: Non-quasi-affine variety with quasi-affine normalization

This file records the construction in the example.  The algebraic and gluing
objects are defined explicitly; the geometric verification statements are
left as theorem interfaces for the later proof stage.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open scoped TensorProduct

namespace Formalization.«Books.Examples».Unit23

/-! ## The punctured affine plane and its two coordinate curves -/

/-- The coordinate ring of the affine plane in the example. -/
abbrev examplePlaneRing (k : Type u) [Field k] := MvPolynomial (Fin 2) k

/-- The `x` and `y` coordinates of the affine plane. -/
def exampleX (k : Type u) [Field k] : examplePlaneRing k := MvPolynomial.X 0

def exampleY (k : Type u) [Field k] : examplePlaneRing k := MvPolynomial.X 1

def exampleXY (k : Type u) [Field k] : examplePlaneRing k :=
  exampleX k * exampleY k

def exampleXPlusY (k : Type u) [Field k] : examplePlaneRing k :=
  exampleX k + exampleY k

/-- `A²_k`, presented as an affine scheme. -/
abbrev exampleAffinePlane (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (examplePlaneRing k))

/-- The open `D(x) ∪ D(y) = A²_k \ {(0,0)}`. -/
def examplePuncturedAffinePlaneOpen (k : Type u) [Field k] :
    (exampleAffinePlane k).Opens :=
  PrimeSpectrum.basicOpen (R := CommRingCat.of (examplePlaneRing k)) (exampleX k) ⊔
    PrimeSpectrum.basicOpen (R := CommRingCat.of (examplePlaneRing k)) (exampleY k)

/-- The punctured affine plane `Y`. -/
abbrev examplePuncturedAffinePlane (k : Type u) [Field k] : Scheme.{u} :=
  (examplePuncturedAffinePlaneOpen k).toScheme

/-- The origin, used to state that the displayed open is the punctured plane. -/
def exampleOrigin (k : Type u) [Field k] : Set (exampleAffinePlane k).carrier :=
  PrimeSpectrum.zeroLocus ({exampleX k, exampleY k} : Set (examplePlaneRing k))

theorem examplePuncturedAffinePlane_is_complement_origin (k : Type u) [Field k] :
    (examplePuncturedAffinePlaneOpen k).carrier = (exampleOrigin k)ᶜ := by
  sorry

/-- The coordinate ring of either coordinate curve before removing its origin. -/
abbrev exampleCurvePolynomialRing (k : Type u) [Field k] := Polynomial k

/-- The coordinate ring `k[t,t⁻¹]` of a coordinate curve inside `Y`. -/
abbrev exampleCurveRing (k : Type u) [Field k] :=
  Localization.Away (Polynomial.X : Polynomial k)

abbrev exampleCurveScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (exampleCurveRing k))

abbrev exampleCurveOne (k : Type u) [Field k] : Scheme.{u} :=
  exampleCurveScheme k

abbrev exampleCurveTwo (k : Type u) [Field k] : Scheme.{u} :=
  exampleCurveScheme k

def exampleCurveParameter (k : Type u) [Field k] : exampleCurveRing k :=
  algebraMap (Polynomial k) (exampleCurveRing k) Polynomial.X

/-- The maps `C₁ → A²` and `C₂ → A²`, with coordinates `(0,t)` and `(t⁻¹,0)`. -/
def exampleCurveOneToAffinePlaneAlgHom (k : Type u) [Field k] :
    examplePlaneRing k →ₐ[k] exampleCurveRing k :=
  MvPolynomial.eval₂AlgHom k
    (fun i => if i = (0 : Fin 2) then 0 else exampleCurveParameter k)

def exampleCurveTwoToAffinePlaneAlgHom (k : Type u) [Field k] :
    examplePlaneRing k →ₐ[k] exampleCurveRing k :=
  MvPolynomial.eval₂AlgHom k
    (fun i => if i = (0 : Fin 2) then
      IsLocalization.Away.invSelf (S := exampleCurveRing k) (Polynomial.X : Polynomial k)
      else 0)

abbrev exampleCurveOneToAffinePlaneRingHom (k : Type u) [Field k] :
    examplePlaneRing k →+* exampleCurveRing k :=
  (exampleCurveOneToAffinePlaneAlgHom k).toRingHom

abbrev exampleCurveTwoToAffinePlaneRingHom (k : Type u) [Field k] :
    examplePlaneRing k →+* exampleCurveRing k :=
  (exampleCurveTwoToAffinePlaneAlgHom k).toRingHom

theorem exampleCurveOneToAffinePlaneRingHom_sum (k : Type u) [Field k] :
    exampleCurveOneToAffinePlaneRingHom k (exampleXPlusY k) =
      exampleCurveParameter k := by
  simp [exampleCurveOneToAffinePlaneRingHom, exampleCurveOneToAffinePlaneAlgHom,
    exampleXPlusY, exampleX, exampleY]

theorem exampleCurveTwoToAffinePlaneRingHom_sum (k : Type u) [Field k] :
    exampleCurveTwoToAffinePlaneRingHom k (exampleXPlusY k) =
      IsLocalization.Away.invSelf (S := exampleCurveRing k) (Polynomial.X : Polynomial k) := by
  simp [exampleCurveTwoToAffinePlaneRingHom, exampleCurveTwoToAffinePlaneAlgHom,
    exampleXPlusY, exampleX, exampleY]

theorem exampleCurveOneToAffinePlaneAlgHom_sum (k : Type u) [Field k] :
    exampleCurveOneToAffinePlaneAlgHom k (exampleXPlusY k) =
      exampleCurveParameter k := by
  simp [exampleCurveOneToAffinePlaneAlgHom, exampleXPlusY, exampleX, exampleY]

theorem exampleCurveTwoToAffinePlaneAlgHom_sum (k : Type u) [Field k] :
    exampleCurveTwoToAffinePlaneAlgHom k (exampleXPlusY k) =
      IsLocalization.Away.invSelf (S := exampleCurveRing k) (Polynomial.X : Polynomial k) := by
  simp [exampleCurveTwoToAffinePlaneAlgHom, exampleXPlusY, exampleX, exampleY]

def exampleCurveOneToAffinePlane (k : Type u) [Field k] :
    exampleCurveOne k ⟶ exampleAffinePlane k :=
  Spec.map (CommRingCat.ofHom (exampleCurveOneToAffinePlaneRingHom k))

def exampleCurveTwoToAffinePlane (k : Type u) [Field k] :
    exampleCurveTwo k ⟶ exampleAffinePlane k :=
  Spec.map (CommRingCat.ofHom (exampleCurveTwoToAffinePlaneRingHom k))

/-- The two curves lie in the punctured plane. -/
theorem exampleCurveOneToPuncturedAffinePlane_exists (k : Type u) [Field k] :
    ∃ f : exampleCurveOne k ⟶ examplePuncturedAffinePlane k,
      f ≫ (examplePuncturedAffinePlaneOpen k).ι = exampleCurveOneToAffinePlane k := by
  sorry

theorem exampleCurveTwoToPuncturedAffinePlane_exists (k : Type u) [Field k] :
    ∃ f : exampleCurveTwo k ⟶ examplePuncturedAffinePlane k,
      f ≫ (examplePuncturedAffinePlaneOpen k).ι = exampleCurveTwoToAffinePlane k := by
  sorry

noncomputable def exampleCurveOneToPuncturedAffinePlane (k : Type u) [Field k] :
    exampleCurveOne k ⟶ examplePuncturedAffinePlane k :=
  Classical.choose (exampleCurveOneToPuncturedAffinePlane_exists k)

theorem exampleCurveOneToPuncturedAffinePlane_fac (k : Type u) [Field k] :
    exampleCurveOneToPuncturedAffinePlane k ≫ (examplePuncturedAffinePlaneOpen k).ι =
      exampleCurveOneToAffinePlane k :=
  Classical.choose_spec (exampleCurveOneToPuncturedAffinePlane_exists k)

noncomputable def exampleCurveTwoToPuncturedAffinePlane (k : Type u) [Field k] :
    exampleCurveTwo k ⟶ examplePuncturedAffinePlane k :=
  Classical.choose (exampleCurveTwoToPuncturedAffinePlane_exists k)

theorem exampleCurveTwoToPuncturedAffinePlane_fac (k : Type u) [Field k] :
    exampleCurveTwoToPuncturedAffinePlane k ≫ (examplePuncturedAffinePlaneOpen k).ι =
      exampleCurveTwoToAffinePlane k :=
  Classical.choose_spec (exampleCurveTwoToPuncturedAffinePlane_exists k)

theorem exampleCurve_ranges_disjoint (k : Type u) [Field k] :
    Disjoint (Set.range (exampleCurveOneToPuncturedAffinePlane k))
      (Set.range (exampleCurveTwoToPuncturedAffinePlane k)) := by
  sorry

/-- The principal open `D(x+y)` used for the first gluing chart. -/
def exampleSumOpen (k : Type u) [Field k] : (exampleAffinePlane k).Opens :=
  PrimeSpectrum.basicOpen (R := CommRingCat.of (examplePlaneRing k)) (exampleXPlusY k)

abbrev exampleSumOpenScheme (k : Type u) [Field k] : Scheme.{u} :=
  (exampleSumOpen k).toScheme

theorem exampleCurveOneToSumOpen_exists (k : Type u) [Field k] :
    ∃ f : exampleCurveOne k ⟶ exampleSumOpenScheme k,
      f ≫ (exampleSumOpen k).ι = exampleCurveOneToAffinePlane k := by
  sorry

theorem exampleCurveTwoToSumOpen_exists (k : Type u) [Field k] :
    ∃ f : exampleCurveTwo k ⟶ exampleSumOpenScheme k,
      f ≫ (exampleSumOpen k).ι = exampleCurveTwoToAffinePlane k := by
  sorry

abbrev exampleCurveDisjointUnion (k : Type u) [Field k] : Scheme.{u} :=
  exampleCurveOne k ⨿ exampleCurveTwo k

theorem exampleCurves_closedImmersion_into_sumOpen_exists (k : Type u) [Field k] :
    ∃ f : exampleCurveDisjointUnion k ⟶ exampleSumOpenScheme k,
      IsClosedImmersion f := by
  sorry

noncomputable def exampleCurves_closedImmersion_into_sumOpen (k : Type u) [Field k] :
    exampleCurveDisjointUnion k ⟶ exampleSumOpenScheme k :=
  Classical.choose (exampleCurves_closedImmersion_into_sumOpen_exists k)

instance exampleCurves_closedImmersion_into_sumOpen_isClosedImmersion
    (k : Type u) [Field k] :
    IsClosedImmersion (exampleCurves_closedImmersion_into_sumOpen k) := by
  exact Classical.choose_spec (exampleCurves_closedImmersion_into_sumOpen_exists k)

theorem exampleSumOpen_toPuncturedAffinePlane_exists (k : Type u) [Field k] :
    ∃ f : exampleSumOpenScheme k ⟶ examplePuncturedAffinePlane k,
      f ≫ (examplePuncturedAffinePlaneOpen k).ι = (exampleSumOpen k).ι := by
  sorry

noncomputable def exampleSumOpen_toPuncturedAffinePlane (k : Type u) [Field k] :
    exampleSumOpenScheme k ⟶ examplePuncturedAffinePlane k :=
  Classical.choose (exampleSumOpen_toPuncturedAffinePlane_exists k)

theorem exampleSumOpen_toPuncturedAffinePlane_fac (k : Type u) [Field k] :
    exampleSumOpen_toPuncturedAffinePlane k ≫ (examplePuncturedAffinePlaneOpen k).ι =
      (exampleSumOpen k).ι :=
  Classical.choose_spec (exampleSumOpen_toPuncturedAffinePlane_exists k)

/-- The second affine open `D(xy)`, whose coordinate ring is `B`. -/
def exampleXYOpen (k : Type u) [Field k] : (exampleAffinePlane k).Opens :=
  PrimeSpectrum.basicOpen (R := CommRingCat.of (examplePlaneRing k)) (exampleXY k)

abbrev exampleXYOpenScheme (k : Type u) [Field k] : Scheme.{u} :=
  (exampleXYOpen k).toScheme

theorem exampleXYOpen_toPuncturedAffinePlane_exists (k : Type u) [Field k] :
    ∃ f : exampleXYOpenScheme k ⟶ examplePuncturedAffinePlane k,
      f ≫ (examplePuncturedAffinePlaneOpen k).ι = (exampleXYOpen k).ι := by
  sorry

noncomputable def exampleXYOpen_toPuncturedAffinePlane (k : Type u) [Field k] :
    exampleXYOpenScheme k ⟶ examplePuncturedAffinePlane k :=
  Classical.choose (exampleXYOpen_toPuncturedAffinePlane_exists k)

theorem exampleCurveOne_disjoint_from_XYOpen (k : Type u) [Field k] :
    Disjoint (Set.range (exampleCurveOneToPuncturedAffinePlane k))
      (Set.range (exampleXYOpen_toPuncturedAffinePlane k)) := by
  sorry

theorem exampleCurveTwo_disjoint_from_XYOpen (k : Type u) [Field k] :
    Disjoint (Set.range (exampleCurveTwoToPuncturedAffinePlane k))
      (Set.range (exampleXYOpen_toPuncturedAffinePlane k)) := by
  sorry

/-! ## The two rings used for gluing -/

abbrev examplePlaneLocalization (k : Type u) [Field k] :=
  Localization.Away (exampleXPlusY k)

def exampleCurveOneToLocalizationAlgHom (k : Type u) [Field k] :
    examplePlaneLocalization k →ₐ[k] exampleCurveRing k :=
  IsLocalization.Away.liftAlgHom (A := k) (R := examplePlaneRing k)
    (S := examplePlaneLocalization k) (P := exampleCurveRing k)
    (f := exampleCurveOneToAffinePlaneAlgHom k) (exampleXPlusY k) (by
    rw [exampleCurveOneToAffinePlaneAlgHom_sum]
    exact IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k))

def exampleCurveTwoToLocalizationAlgHom (k : Type u) [Field k] :
    examplePlaneLocalization k →ₐ[k] exampleCurveRing k :=
  IsLocalization.Away.liftAlgHom (A := k) (R := examplePlaneRing k)
    (S := examplePlaneLocalization k) (P := exampleCurveRing k)
    (f := exampleCurveTwoToAffinePlaneAlgHom k) (exampleXPlusY k) (by
    rw [exampleCurveTwoToAffinePlaneAlgHom_sum]
    exact isUnit_iff_exists_inv.mpr ⟨algebraMap (Polynomial k) (exampleCurveRing k)
      Polynomial.X, by
        rw [mul_comm]
        exact IsLocalization.Away.mul_invSelf (S := exampleCurveRing k)
          (Polynomial.X : Polynomial k)⟩)

abbrev exampleCurveOneToLocalization (k : Type u) [Field k] :
    examplePlaneLocalization k →+* exampleCurveRing k :=
  (exampleCurveOneToLocalizationAlgHom k).toRingHom

abbrev exampleCurveTwoToLocalization (k : Type u) [Field k] :
    examplePlaneLocalization k →+* exampleCurveRing k :=
  (exampleCurveTwoToLocalizationAlgHom k).toRingHom

/-- The invariant subalgebra in the polynomial ring. -/
def examplePolynomialInvariantSubalgebra (k : Type u) [Field k] :
    Subalgebra k (examplePlaneRing k) :=
  AlgHom.equalizer (exampleCurveOneToAffinePlaneAlgHom k)
    (exampleCurveTwoToAffinePlaneAlgHom k)

/-- The invariant subalgebra after inverting `x+y`. -/
def exampleLocalizedInvariantSubalgebra (k : Type u) [Field k] :
    Subalgebra k (examplePlaneLocalization k) :=
  AlgHom.equalizer (exampleCurveOneToLocalizationAlgHom k)
    (exampleCurveTwoToLocalizationAlgHom k)

/-- The invariant ring `A` on `D(x+y)`. -/
abbrev exampleRingA (k : Type u) [Field k] :=
  ↥(exampleLocalizedInvariantSubalgebra k)

/-- The ring `B = k[x,y,1/(xy)]` on `D(xy)`. -/
abbrev exampleRingB (k : Type u) [Field k] :=
  Localization.Away (exampleXY k)

theorem examplePolynomialInvariantSubalgebra_is_constant_plus_xy (k : Type u) [Field k] :
    (examplePolynomialInvariantSubalgebra k).carrier =
      {f | ∃ c : k, ∃ p : examplePlaneRing k, f = MvPolynomial.C c + exampleXY k * p} := by
  sorry

theorem exampleRingA_finiteType (k : Type u) [Field k] :
    Algebra.FiniteType k (exampleRingA k) := by
  sorry

theorem exampleRingB_finiteType (k : Type u) [Field k] :
    Algebra.FiniteType k (exampleRingB k) := by
  sorry

theorem exampleXY_mul_polynomial_mem_ringA (k : Type u) [Field k]
    (p : examplePlaneRing k) :
    algebraMap (examplePlaneRing k) (examplePlaneLocalization k)
        (exampleXY k * p) ∈ exampleLocalizedInvariantSubalgebra k := by
  sorry

theorem exampleXY_div_sum_mem_ringA (k : Type u) [Field k] :
    algebraMap (examplePlaneRing k) (examplePlaneLocalization k) (exampleXY k) *
        IsLocalization.Away.invSelf (S := examplePlaneLocalization k) (exampleXPlusY k) ∈
      exampleLocalizedInvariantSubalgebra k := by
  sorry

noncomputable def exampleXY_div_sum_in_ringA (k : Type u) [Field k] : exampleRingA k :=
  ⟨algebraMap (examplePlaneRing k) (examplePlaneLocalization k) (exampleXY k) *
      IsLocalization.Away.invSelf (S := examplePlaneLocalization k) (exampleXPlusY k),
    exampleXY_div_sum_mem_ringA k⟩

noncomputable def exampleXY_in_ringA (k : Type u) [Field k] : exampleRingA k :=
  ⟨algebraMap (examplePlaneRing k) (examplePlaneLocalization k) (exampleXY k), by
    simpa using exampleXY_mul_polynomial_mem_ringA k 1⟩

def exampleSeparatingFunctionInPlaneLocalization (k : Type u) [Field k] :
    examplePlaneLocalization k :=
  algebraMap (examplePlaneRing k) (examplePlaneLocalization k)
      (exampleX k + exampleY k ^ 3) *
    IsLocalization.Away.invSelf (S := examplePlaneLocalization k)
      (exampleXPlusY k) ^ 2

theorem exampleSeparatingFunctionInPlaneLocalization_mem_ringA (k : Type u) [Field k] :
    exampleSeparatingFunctionInPlaneLocalization k ∈
      exampleLocalizedInvariantSubalgebra k := by
  sorry

noncomputable def exampleSeparatingFunctionInRingA (k : Type u) [Field k] : exampleRingA k :=
  ⟨exampleSeparatingFunctionInPlaneLocalization k,
    exampleSeparatingFunctionInPlaneLocalization_mem_ringA k⟩

abbrev exampleRingAOverlap (k : Type u) [Field k] :=
  Localization.Away (exampleXY_in_ringA k)

def exampleXY_in_ringB (k : Type u) [Field k] : exampleRingB k :=
  algebraMap (examplePlaneRing k) (exampleRingB k) (exampleXY k)

def exampleSum_in_ringB (k : Type u) [Field k] : exampleRingB k :=
  algebraMap (examplePlaneRing k) (exampleRingB k) (exampleXPlusY k)

abbrev exampleRingBOverlap (k : Type u) [Field k] :=
  Localization.Away (exampleSum_in_ringB k)

theorem example_overlap_ring_equiv_exists (k : Type u) [Field k] :
    Nonempty (exampleRingAOverlap k ≃+* exampleRingBOverlap k) := by
  sorry

noncomputable def example_overlap_ring_equiv (k : Type u) [Field k] :
    exampleRingAOverlap k ≃+* exampleRingBOverlap k :=
  Classical.choice (example_overlap_ring_equiv_exists k)

/-- The element `1/(xy)` in the `xy`-localization of the `B` chart. -/
def exampleInverseXYInRingB (k : Type u) [Field k] : exampleRingB k :=
  IsLocalization.Away.invSelf (S := exampleRingB k) (exampleXY k)

/-- The displayed tensor element `(xy/(x+y)) ⊗ 1/xy`. -/
def exampleTensorElement (k : Type u) [Field k] :
    exampleRingA k ⊗[k] exampleRingB k :=
  exampleXY_div_sum_in_ringA k ⊗ₜ[k] exampleInverseXYInRingB k

theorem exampleTensorMap_exists (k : Type u) [Field k] :
    ∃ f : (exampleRingA k ⊗[k] exampleRingB k) →+* exampleRingBOverlap k,
      Function.Surjective f ∧
        f (exampleTensorElement k) =
          IsLocalization.Away.invSelf (S := exampleRingBOverlap k)
            (exampleSum_in_ringB k) := by
  sorry

noncomputable def exampleTensorMap (k : Type u) [Field k] :
    (exampleRingA k ⊗[k] exampleRingB k) →+* exampleRingBOverlap k :=
  Classical.choose (exampleTensorMap_exists k)

theorem exampleTensorMap_surjective (k : Type u) [Field k] :
    Function.Surjective (exampleTensorMap k) :=
  (Classical.choose_spec (exampleTensorMap_exists k)).1

theorem exampleTensorMap_on_displayed_element (k : Type u) [Field k] :
    exampleTensorMap k (exampleTensorElement k) =
      IsLocalization.Away.invSelf (S := exampleRingBOverlap k)
        (exampleSum_in_ringB k) :=
  (Classical.choose_spec (exampleTensorMap_exists k)).2

/-! ## The gluing scheme and its source-facing properties -/

def exampleAChart (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (exampleRingA k))

def exampleBChart (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (exampleRingB k))

def exampleAOverlapChart (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (exampleRingAOverlap k))

def exampleBOverlapChart (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (exampleRingBOverlap k))

def exampleAChartToOverlap (k : Type u) [Field k] :
    exampleAOverlapChart k ⟶ exampleAChart k :=
  Spec.map (CommRingCat.ofHom (algebraMap (exampleRingA k) (exampleRingAOverlap k)))

def exampleBChartToOverlap (k : Type u) [Field k] :
    exampleBOverlapChart k ⟶ exampleBChart k :=
  Spec.map (CommRingCat.ofHom (algebraMap (exampleRingB k) (exampleRingBOverlap k)))

def exampleOverlapTransition (k : Type u) [Field k] :
    exampleAOverlapChart k ⟶ exampleBOverlapChart k :=
  Spec.map (CommRingCat.ofHom (example_overlap_ring_equiv k).symm.toRingHom)

def exampleOverlapTransitionInv (k : Type u) [Field k] :
    exampleBOverlapChart k ⟶ exampleAOverlapChart k :=
  Spec.map (CommRingCat.ofHom (example_overlap_ring_equiv k).toRingHom)

instance exampleAChartToOverlap_isOpenImmersion (k : Type u) [Field k] :
    IsOpenImmersion (exampleAChartToOverlap k) := by
  sorry

instance exampleBChartToOverlap_isOpenImmersion (k : Type u) [Field k] :
    IsOpenImmersion (exampleBChartToOverlap k) := by
  sorry

theorem exampleOverlapTransition_inv (k : Type u) [Field k] :
    exampleOverlapTransition k ≫ exampleOverlapTransitionInv k = 𝟙 _ := by
  sorry

theorem exampleOverlapTransition_inv' (k : Type u) [Field k] :
    exampleOverlapTransitionInv k ≫ exampleOverlapTransition k = 𝟙 _ := by
  sorry

def exampleCategoryGlueDataPrime (k : Type u) [Field k] :
    CategoryTheory.GlueData' (Scheme.{u}) where
  J := ULift Bool
  U := fun b => match b.down with
    | false => exampleAChart k
    | true => exampleBChart k
  V := by
    intro i j h
    cases i with
    | up i =>
      cases j with
      | up j =>
        cases i <;> cases j
        · exact (h rfl).elim
        · exact exampleAOverlapChart k
        · exact exampleBOverlapChart k
        · exact (h rfl).elim
  f := by
    intro i j h
    cases i with
    | up i =>
      cases j with
      | up j =>
        cases i <;> cases j
        · exact (h rfl).elim
        · exact exampleAChartToOverlap k
        · exact exampleBChartToOverlap k
        · exact (h rfl).elim
  f_mono := by
    intro i j h
    cases i with
    | up i =>
      cases j with
      | up j =>
        cases i <;> cases j
        · exact (h rfl).elim
        · infer_instance
        · infer_instance
        · exact (h rfl).elim
  f_hasPullback := by
    intro i j l hij hil
    infer_instance
  t := by
    intro i j h
    cases i with
    | up i =>
      cases j with
      | up j =>
        cases i <;> cases j
        · exact (h rfl).elim
        · exact exampleOverlapTransition k
        · exact exampleOverlapTransitionInv k
        · exact (h rfl).elim
  t' := by
    intro i j l hij hil hjl
    cases i with
    | up i =>
      cases j with
      | up j =>
        cases l with
        | up l =>
          cases i
          · cases j
            · exact (hij rfl).elim
            · cases l
              · exact (hil rfl).elim
              · exact (hjl rfl).elim
          · cases j
            · cases l
              · exact (hjl rfl).elim
              · exact (hil rfl).elim
            · exact (hij rfl).elim
  t_fac := by
    intro i j l hij hil hjl
    cases i with
    | up i =>
      cases j with
      | up j =>
        cases l with
        | up l =>
          cases i
          · cases j
            · exact (hij rfl).elim
            · cases l
              · exact (hil rfl).elim
              · exact (hjl rfl).elim
          · cases j
            · cases l
              · exact (hjl rfl).elim
              · exact (hil rfl).elim
            · exact (hij rfl).elim
  t_inv := by
    intro i j h
    cases i with
    | up i =>
      cases j with
      | up j =>
        cases i <;> cases j
        · exact (h rfl).elim
        · exact exampleOverlapTransition_inv k
        · exact exampleOverlapTransition_inv' k
        · exact (h rfl).elim
  cocycle := by
    intro i j l hij hil hjl
    cases i with
    | up i =>
      cases j with
      | up j =>
        cases l with
        | up l =>
          cases i
          · cases j
            · exact (hij rfl).elim
            · cases l
              · exact (hil rfl).elim
              · exact (hjl rfl).elim
          · cases j
            · cases l
              · exact (hjl rfl).elim
              · exact (hil rfl).elim
            · exact (hij rfl).elim

def exampleCategoryGlueData (k : Type u) [Field k] :
    CategoryTheory.GlueData (Scheme.{u}) :=
  CategoryTheory.GlueData.ofGlueData' (exampleCategoryGlueDataPrime k)

theorem exampleCategoryGlueData_isOpenImmersion (k : Type u) [Field k] :
    ∀ i j, IsOpenImmersion ((exampleCategoryGlueData k).f i j) := by
  intro i j
  sorry

def exampleSchemeGlueData (k : Type u) [Field k] : Scheme.GlueData.{u} where
  toGlueData := exampleCategoryGlueData k
  f_open := exampleCategoryGlueData_isOpenImmersion k

abbrev exampleGluedScheme (k : Type u) [Field k] : Scheme.{u} :=
  (exampleSchemeGlueData k).glued

theorem exampleAChartIntoGlued_exists (k : Type u) [Field k] :
    ∃ i : exampleAChart k ⟶ exampleGluedScheme k, IsOpenImmersion i := by
  sorry

noncomputable def exampleAChartIntoGlued (k : Type u) [Field k] :
    exampleAChart k ⟶ exampleGluedScheme k :=
  Classical.choose (exampleAChartIntoGlued_exists k)

instance exampleAChartIntoGlued_isOpenImmersion (k : Type u) [Field k] :
    IsOpenImmersion (exampleAChartIntoGlued k) := by
  exact Classical.choose_spec (exampleAChartIntoGlued_exists k)

theorem exampleBChartIntoGlued_exists (k : Type u) [Field k] :
    ∃ i : exampleBChart k ⟶ exampleGluedScheme k, IsOpenImmersion i := by
  sorry

noncomputable def exampleBChartIntoGlued (k : Type u) [Field k] :
    exampleBChart k ⟶ exampleGluedScheme k :=
  Classical.choose (exampleBChartIntoGlued_exists k)

instance exampleBChartIntoGlued_isOpenImmersion (k : Type u) [Field k] :
    IsOpenImmersion (exampleBChartIntoGlued k) := by
  exact Classical.choose_spec (exampleBChartIntoGlued_exists k)

def IsSchemeCoequalizer {C Y X : Scheme.{u}} (f g : C ⟶ Y) (π : Y ⟶ X) : Prop :=
  ∃ h : f ≫ π = g ≫ π, Nonempty (IsColimit (Cofork.ofπ π h))

/-- The pair of curve maps appearing in the coequalizer diagram. -/
def exampleCurveOneAndTwoToY (k : Type u) [Field k] :
    exampleCurveOne k ⟶ examplePuncturedAffinePlane k :=
  exampleCurveOneToPuncturedAffinePlane k

def exampleCurveInversionPolynomialHom (k : Type u) [Field k] :
    Polynomial k →+* exampleCurveRing k :=
  Polynomial.eval₂RingHom (algebraMap k (exampleCurveRing k))
    (IsLocalization.Away.invSelf (S := exampleCurveRing k) (Polynomial.X : Polynomial k))

def exampleCurveInversionRingHom (k : Type u) [Field k] :
    exampleCurveRing k →+* exampleCurveRing k :=
  Localization.awayLift (exampleCurveInversionPolynomialHom k) Polynomial.X (by
    exact isUnit_iff_exists_inv.mpr ⟨algebraMap (Polynomial k) (exampleCurveRing k)
      Polynomial.X, by
        rw [mul_comm]
        simp [exampleCurveInversionPolynomialHom,
          IsLocalization.Away.mul_invSelf (S := exampleCurveRing k)]⟩)

def exampleCurveInversion (k : Type u) [Field k] :
    exampleCurveOne k ⟶ exampleCurveTwo k :=
  Spec.map (CommRingCat.ofHom (exampleCurveInversionRingHom k))

theorem exampleCurveInversion_isIso (k : Type u) [Field k] :
    IsIso (exampleCurveInversion k) := by
  sorry

def exampleCurveOneViaInversionToY (k : Type u) [Field k] :
    exampleCurveOne k ⟶ examplePuncturedAffinePlane k :=
  exampleCurveInversion k ≫ exampleCurveTwoToPuncturedAffinePlane k

/-- The source property that the glued scheme is a variety over `k`. -/
def IsVarietyOver (k : Type u) [Field k] (X : Scheme.{u}) : Prop :=
  ∃ f : X ⟶ Spec (CommRingCat.of k),
    IsIntegral X ∧ IsSeparated f ∧ QuasiCompact f ∧ LocallyOfFiniteType f

/-- The relative normalization map of a morphism is quasi-affine. -/
def IsQuasiAffineNormalization {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∃ hqc : QuasiCompact f, ∃ hqs : QuasiSeparated f,
    let _ : QuasiCompact f := hqc
    let _ : QuasiSeparated f := hqs
    (∃ e : Y ≅ f.normalization, e.hom ≫ f.fromNormalization = f) ∧
      Scheme.IsQuasiAffine f.normalization

def IsExampleQuotientMorphism (k : Type u) [Field k] {X : Scheme.{u}}
    (π : examplePuncturedAffinePlane k ⟶ X) : Prop :=
  IsFinite π ∧ Surjective π ∧
    Scheme.Birational (examplePuncturedAffinePlane k) X ∧
      IsSchemeCoequalizer (exampleCurveOneAndTwoToY k)
        (exampleCurveOneViaInversionToY k) π

/-- The exact finite, surjective, birational morphism asserted in the example. -/
structure ExampleFiniteBirationalData (k : Type u) [Field k] where
  morphism : examplePuncturedAffinePlane k ⟶ exampleGluedScheme k
  finite : IsFinite morphism
  surjective : Surjective morphism
  birational : Scheme.Birational (examplePuncturedAffinePlane k) (exampleGluedScheme k)
  coequalizer : IsSchemeCoequalizer
    (exampleCurveOneAndTwoToY k) (exampleCurveOneViaInversionToY k) morphism
  variety : IsVarietyOver k (exampleGluedScheme k)
  not_quasi_affine : ¬ Scheme.IsQuasiAffine (exampleGluedScheme k)
  normalization_quasi_affine : IsQuasiAffineNormalization morphism
  source_normalization_is_quasi_affine :
    Scheme.IsQuasiAffine (examplePuncturedAffinePlane k)

theorem example_finite_birational_data_exists (k : Type u) [Field k] :
    Nonempty (ExampleFiniteBirationalData k) := by
  sorry

noncomputable def exampleFiniteBirationalData (k : Type u) [Field k] :
    ExampleFiniteBirationalData k :=
  Classical.choice (example_finite_birational_data_exists k)

abbrev exampleMorphism (k : Type u) [Field k] :
    examplePuncturedAffinePlane k ⟶ exampleGluedScheme k :=
  (exampleFiniteBirationalData k).morphism

theorem exampleMorphism_is_finite (k : Type u) [Field k] :
    IsFinite (exampleMorphism k) :=
  (exampleFiniteBirationalData k).finite

theorem exampleMorphism_is_surjective (k : Type u) [Field k] :
    Surjective (exampleMorphism k) :=
  (exampleFiniteBirationalData k).surjective

theorem exampleMorphism_is_birational (k : Type u) [Field k] :
    Scheme.Birational (examplePuncturedAffinePlane k) (exampleGluedScheme k) :=
  (exampleFiniteBirationalData k).birational

theorem exampleMorphism_is_coequalizer (k : Type u) [Field k] :
    IsSchemeCoequalizer
      (exampleCurveOneAndTwoToY k) (exampleCurveOneViaInversionToY k) (exampleMorphism k) :=
  (exampleFiniteBirationalData k).coequalizer

theorem exampleMorphism_is_given_by_chart_maps (k : Type u) [Field k] :
    ∃ fA : exampleSumOpenScheme k ⟶ exampleAChart k,
      ∃ fB : exampleXYOpenScheme k ⟶ exampleBChart k,
        IsFinite fA ∧ IsFinite fB ∧
          fA ≫ exampleAChartIntoGlued k =
            exampleSumOpen_toPuncturedAffinePlane k ≫ exampleMorphism k ∧
          fB ≫ exampleBChartIntoGlued k =
            exampleXYOpen_toPuncturedAffinePlane k ≫ exampleMorphism k := by
  sorry

theorem exampleMorphism_unique_up_to_unique_isomorphism (k : Type u) [Field k]
    {X : Scheme.{u}} (π : examplePuncturedAffinePlane k ⟶ X)
    (hπ : IsExampleQuotientMorphism k π) :
    ∃! e : exampleGluedScheme k ≅ X,
      exampleMorphism k ≫ e.hom = π := by
  sorry

theorem exampleGluedScheme_is_variety (k : Type u) [Field k] :
    IsVarietyOver k (exampleGluedScheme k) :=
  (exampleFiniteBirationalData k).variety

theorem exampleGluedScheme_not_quasi_affine (k : Type u) [Field k] :
    ¬ Scheme.IsQuasiAffine (exampleGluedScheme k) :=
  (exampleFiniteBirationalData k).not_quasi_affine

theorem exampleNormalization_is_quasi_affine (k : Type u) [Field k] :
    IsQuasiAffineNormalization (exampleMorphism k) :=
  (exampleFiniteBirationalData k).normalization_quasi_affine

theorem examplePuncturedAffinePlane_is_quasi_affine (k : Type u) [Field k] :
    Scheme.IsQuasiAffine (examplePuncturedAffinePlane k) :=
  (exampleFiniteBirationalData k).source_normalization_is_quasi_affine

/-! ## Coordinate points used in the separation argument -/

/-- The point `(a,b)` of the affine plane, represented by the closed point of `k`. -/
def exampleAffineCoordinatePoint (k : Type u) [Field k] (a b : k) :
    exampleAffinePlane k :=
  PrimeSpectrum.comap
    (MvPolynomial.eval₂AlgHom k
      (fun i => if i = (0 : Fin 2) then a else b)).toRingHom
    (IsLocalRing.closedPoint k)

theorem exampleAffineCoordinatePoint_toPuncturedAffinePlane_exists
    (k : Type u) [Field k] (a b : k) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ p : examplePuncturedAffinePlane k,
      (examplePuncturedAffinePlaneOpen k).ι p =
        exampleAffineCoordinatePoint k a b := by
  sorry

noncomputable def exampleAffineCoordinatePointToPuncturedAffinePlane
    (k : Type u) [Field k] (a b : k) (h : a ≠ 0 ∨ b ≠ 0) :
    examplePuncturedAffinePlane k :=
  Classical.choose (exampleAffineCoordinatePoint_toPuncturedAffinePlane_exists k a b h)

theorem exampleAffineCoordinatePointToPuncturedAffinePlane_fac
    (k : Type u) [Field k] (a b : k) (h : a ≠ 0 ∨ b ≠ 0) :
    (examplePuncturedAffinePlaneOpen k).ι
        (exampleAffineCoordinatePointToPuncturedAffinePlane k a b h) =
      exampleAffineCoordinatePoint k a b :=
  Classical.choose_spec (exampleAffineCoordinatePoint_toPuncturedAffinePlane_exists k a b h)

def examplePointOneInY (k : Type u) [Field k] : examplePuncturedAffinePlane k :=
  exampleAffineCoordinatePointToPuncturedAffinePlane k 1 0 (by simp)

def examplePointNegOneInY (k : Type u) [Field k] : examplePuncturedAffinePlane k :=
  exampleAffineCoordinatePointToPuncturedAffinePlane k (-1) 0 (by simp)

/-! ## Global functions and failure of point separation -/

def exampleConstantPlusXYSubalgebra (k : Type u) [Field k] :
    Subalgebra k (examplePlaneRing k) :=
  examplePolynomialInvariantSubalgebra k

theorem exampleGlobalSections_equiv_constant_plus_xy (k : Type u) [Field k] :
    Nonempty (Γ(exampleGluedScheme k, ⊤) ≃+*
      (↥(exampleConstantPlusXYSubalgebra k))) := by
  sorry

/-- The rational function `(x+y³)/(x+y)²` used to distinguish two points. -/
def exampleSeparatingFunctionValue (k : Type u) [Field k] (a b : k) : k :=
  (a + b ^ 3) * (a + b)⁻¹ ^ 2

theorem exampleSeparatingFunctionValue_one (k : Type u) [Field k] :
    exampleSeparatingFunctionValue k 1 0 = 1 := by
  sorry

theorem exampleSeparatingFunctionValue_neg_one (k : Type u) [Field k] :
    exampleSeparatingFunctionValue k (-1) 0 = -1 := by
  sorry

structure ExamplePointSeparationData (k : Type u) [Field k] where
  pointOne : exampleGluedScheme k
  pointNegOne : exampleGluedScheme k
  distinct : pointOne ≠ pointNegOne
  pointOne_is_image : pointOne = exampleMorphism k (examplePointOneInY k)
  pointNegOne_is_image : pointNegOne = exampleMorphism k (examplePointNegOneInY k)
  global_sections_agree :
    (exampleGluedScheme k).toSpecΓ pointOne =
      (exampleGluedScheme k).toSpecΓ pointNegOne

theorem examplePointSeparationData_exists (k : Type u) [Field k]
    (hchar : (1 : k) ≠ (-1 : k)) :
    Nonempty (ExamplePointSeparationData k) := by
  sorry

noncomputable def examplePointSeparationData (k : Type u) [Field k]
    (hchar : (1 : k) ≠ (-1 : k)) : ExamplePointSeparationData k :=
  Classical.choice (examplePointSeparationData_exists k hchar)

def IsSeparatedByGlobalSections (X : Scheme.{u}) : Prop :=
  Function.Injective (fun x : X => (X.toSpecΓ) x)

theorem exampleGlobalSections_do_not_separate (k : Type u) [Field k]
    (hchar : (1 : k) ≠ (-1 : k)) :
    ¬ IsSeparatedByGlobalSections (exampleGluedScheme k) := by
  intro hinj
  let d := examplePointSeparationData k hchar
  exact d.distinct (hinj d.global_sections_agree)

/-! ## The chapter's final existence statement -/

theorem exists_variety_with_quasi_affine_normalization_not_quasi_affine :
    ∀ (k : Type u), ∀ (_ : Field k),
      ∃ (X Y : Scheme.{u}) (π : Y ⟶ X),
        IsVarietyOver k X ∧ IsQuasiAffineNormalization π ∧
          ¬ Scheme.IsQuasiAffine X := by
  intro k _
  exact ⟨exampleGluedScheme k, examplePuncturedAffinePlane k, exampleMorphism k,
    exampleGluedScheme_is_variety k, exampleNormalization_is_quasi_affine k,
    exampleGluedScheme_not_quasi_affine k⟩

end Formalization.«Books.Examples».Unit23
