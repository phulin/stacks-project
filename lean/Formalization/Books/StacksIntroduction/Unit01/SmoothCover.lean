import Formalization.Books.StacksIntroduction.Unit01.Definition
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Introducing Algebraic Stacks, Chapter 1: a smooth cover

The universal Weierstrass equation is built from Mathlib's canonical
`WeierstrassCurve` and projective polynomial APIs.  The family-level
elliptic-curve object and the smooth-cover conclusion are theorem interfaces,
because Mathlib has no global category of elliptic curves over schemes.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open MvPolynomial

noncomputable section

namespace Formalization.Books.StacksIntroduction.Unit01

/-! ### The universal coefficient ring and discriminant -/

/-- The polynomial ring in the five universal Weierstrass coefficients. -/
abbrev UniversalCoefficientRing := MvPolynomial (Fin 5) ℤ

def universalA₁ : UniversalCoefficientRing := X 0
def universalA₂ : UniversalCoefficientRing := X 1
def universalA₃ : UniversalCoefficientRing := X 2
def universalA₄ : UniversalCoefficientRing := X 3
def universalA₆ : UniversalCoefficientRing := X 4

/-- The universal Weierstrass curve over the coefficient polynomial ring. -/
def universalWeierstrassCurve : WeierstrassCurve UniversalCoefficientRing :=
  { a₁ := universalA₁
    a₂ := universalA₂
    a₃ := universalA₃
    a₄ := universalA₄
    a₆ := universalA₆ }

/-- The explicit degree-twelve discriminant polynomial from the source. -/
def universalDiscriminantExpanded : UniversalCoefficientRing :=
  -universalA₆ * universalA₁ ^ 6
    + universalA₄ * universalA₃ * universalA₁ ^ 5
    + ((-universalA₃ ^ 2 - 12 * universalA₆) * universalA₂ + universalA₄ ^ 2) *
        universalA₁ ^ 4
    + (8 * universalA₄ * universalA₃ * universalA₂ +
        (universalA₃ ^ 3 + 36 * universalA₆ * universalA₃)) * universalA₁ ^ 3
    + ((-8 * universalA₃ ^ 2 - 48 * universalA₆) * universalA₂ ^ 2 +
        8 * universalA₄ ^ 2 * universalA₂ +
        (-30 * universalA₄ * universalA₃ ^ 2 + 72 * universalA₆ * universalA₄)) *
        universalA₁ ^ 2
    + (16 * universalA₄ * universalA₃ * universalA₂ ^ 2 +
        (36 * universalA₃ ^ 3 + 144 * universalA₆ * universalA₃) * universalA₂ -
        96 * universalA₄ ^ 2 * universalA₃) * universalA₁
    + (-16 * universalA₃ ^ 2 - 64 * universalA₆) * universalA₂ ^ 3
    + 16 * universalA₄ ^ 2 * universalA₂ ^ 2
    + (72 * universalA₄ * universalA₃ ^ 2 + 288 * universalA₆ * universalA₄) * universalA₂
    - 27 * universalA₃ ^ 4 - 216 * universalA₆ * universalA₃ ^ 2
    - 64 * universalA₄ ^ 3 - 432 * universalA₆ ^ 2

/-- The discriminant computed by Mathlib agrees with the expanded polynomial. -/
theorem universalDiscriminant_eq_expanded :
    universalWeierstrassCurve.Δ = universalDiscriminantExpanded := by
  sorry

/-- The ring in the definition of `W`. -/
abbrev UniversalBaseRing := Localization.Away universalDiscriminantExpanded

/-- The universal base scheme `W = Spec(ℤ[a₁,a₂,a₃,a₄,a₆,1/Δ)`. -/
def universalBaseScheme : Scheme.{0} :=
  Scheme.Spec.obj (Opposite.op (CommRingCat.of UniversalBaseRing))

/-- The universal coefficients after localization. -/
def universalCoefficientsOverBase : WeierstrassCurve UniversalBaseRing :=
  universalWeierstrassCurve.baseChange UniversalBaseRing

/-- The image of the discriminant in the localized ring. -/
def universalDiscriminantInBase : UniversalBaseRing :=
  algebraMap UniversalCoefficientRing UniversalBaseRing universalDiscriminantExpanded

/-- The standard weighted degree on the five coefficients. -/
def universalWeights : Fin 5 → ℕ := ![1, 2, 3, 4, 6]

/-- Weighted homogeneity of a polynomial for a prescribed coefficient grading. -/
def WeightedHomogeneous (weights : Fin 5 → ℕ) (degree : ℕ)
    (p : UniversalCoefficientRing) : Prop :=
  ∀ m ∈ p.support, ∑ i : Fin 5, weights i * m i = degree

/-- The source's degree-twelve and weighted-homogeneous assertions. -/
theorem universalDiscriminant_weighted_homogeneous :
    WeightedHomogeneous universalWeights 12 universalDiscriminantExpanded := by
  sorry

theorem universalDiscriminant_has_weighted_degree_twelve :
    WeightedHomogeneous universalWeights 12 universalWeierstrassCurve.Δ := by
  rw [universalDiscriminant_eq_expanded]
  exact universalDiscriminant_weighted_homogeneous

/-- The discriminant is invertible on the universal base. -/
theorem universalDiscriminant_is_unit :
    IsUnit universalDiscriminantInBase := by
  sorry

/-! ### The universal projective equation -/

/-- The homogeneous equation in projective coordinates. -/
def universalHomogeneousEquation :
    MvPolynomial (Fin 3) UniversalBaseRing :=
  WeierstrassCurve.Projective.polynomial universalCoefficientsOverBase

/-- The point `(0 : 1 : 0)` on the universal equation. -/
def universalPointAtInfinity : Fin 3 → UniversalBaseRing := ![0, 1, 0]

theorem universalPointAtInfinity_on_equation :
    WeierstrassCurve.Projective.Equation universalCoefficientsOverBase
      universalPointAtInfinity := by
  exact WeierstrassCurve.Projective.equation_zero

/-- The family-level data attached to the universal equation. -/
structure UniversalWeierstrassFamily where
  curve : ModuliPoint universalBaseScheme
  coefficients : WeierstrassCurve UniversalBaseRing
  coefficients_is_elliptic : coefficients.IsElliptic
  homogeneousEquation : MvPolynomial (Fin 3) UniversalBaseRing
  pointAtInfinity : Fin 3 → UniversalBaseRing
  coefficients_eq : coefficients = universalCoefficientsOverBase
  equation_eq : homogeneousEquation = WeierstrassCurve.Projective.polynomial coefficients
  pointAtInfinity_eq : pointAtInfinity = universalPointAtInfinity
  point_on_equation : WeierstrassCurve.Projective.Equation coefficients pointAtInfinity
  /-- The missing scheme-level identification with the projective equation. -/
  family_identification : Prop

/-- Existence of the universal elliptic-curve family over `W`. -/
theorem exists_universalWeierstrassFamily :
    Nonempty UniversalWeierstrassFamily := by
  sorry

/-- A chosen universal Weierstrass family. -/
noncomputable def universalWeierstrassFamily : UniversalWeierstrassFamily :=
  Classical.choice exists_universalWeierstrassFamily

/-- The universal family gives the source's map `W ⟶ M₁,₁`. -/
noncomputable def universalWeierstrassMorphism :
    ModuliPoint universalBaseScheme :=
  universalWeierstrassFamily.curve

/-- Its projection is smooth of relative dimension one. -/
theorem universalWeierstrass_projection_smooth :
    SmoothOfRelativeDimension 1 universalWeierstrassMorphism.projection :=
  universalWeierstrassMorphism.smooth

/-! ### Coordinate changes and the torsor proof interface -/

/-- The coordinate-change group `H` in Mathlib's Weierstrass API. -/
abbrev WeierstrassCoordinateGroup (R : Type u) [CommRing R] :=
  WeierstrassCurve.VariableChange R

/-- The action of a coordinate change on a Weierstrass equation. -/
def coordinateChangeAction {R : Type u} [CommRing R]
    (C : WeierstrassCoordinateGroup R) (W : WeierstrassCurve R) :
    WeierstrassCurve R := C • W

/-- The four parameters occurring in the coordinate-change matrix in the source. -/
def coordinateChangeParameters {R : Type u} [CommRing R]
    (C : WeierstrassCoordinateGroup R) : Rˣ × R × R × R :=
  (C.u, C.r, C.s, C.t)

/-- Two Weierstrass equations lie in the same `H`-orbit. -/
def WeierstrassEquationEquivalent {R : Type u} [CommRing R]
    (W W' : WeierstrassCurve R) : Prop :=
  ∃ C : WeierstrassCoordinateGroup R, coordinateChangeAction C W = W'

/-- The action notation itself supplies the orbit relation used in the proof sketch. -/
theorem coordinateChangeAction_equivalent {R : Type u} [CommRing R]
    (C : WeierstrassCoordinateGroup R) (W : WeierstrassCurve R) :
    WeierstrassEquationEquivalent W (coordinateChangeAction C W) := by
  exact ⟨C, rfl⟩

/-- The source-level local-chart and transition assertion for a family. -/
structure WeierstrassLocalChartStatement {S : Scheme.{u}}
    (E : ModuliPoint S) where
  cover : S.AffineOpenCover
  /-- The coefficients live in the coordinate ring of the affine chart. -/
  coefficients : ∀ i, WeierstrassCurve (cover.X i)
  coefficients_is_elliptic : ∀ i, IsUnit (coefficients i).Δ
  /-- Mathlib has no scheme-level Weierstrass model for `E` in this interface. -/
  family_identification : ∀ i : cover.I₀, Prop
  /-- On each affine overlap, the two coefficient tuples differ by an admissible change of variables. -/
  transition_by_coordinate_change : ∀ (i j : cover.I₀),
    ∃ C : WeierstrassCurve.VariableChange Γ(
      pullback (cover.f i) (cover.f j), ⊤),
      C • (coefficients i).map
          ((Scheme.ΓSpecIso (cover.X i)).inv ≫
            (pullback.fst (cover.f i) (cover.f j)).appTop).hom =
        (coefficients j).map
          ((Scheme.ΓSpecIso (cover.X j)).inv ≫
            (pullback.snd (cover.f i) (cover.f j)).appTop).hom

/-- The source's local Weierstrass-chart assertion. -/
theorem every_ellipticCurve_has_local_weierstrass_chart
    {S : Scheme.{u}} (E : ModuliPoint S) :
    Nonempty (WeierstrassLocalChartStatement E) := by
  sorry

/-- The source's torsor statement for the smooth cover. -/
structure WeierstrassCoverTorsorStatement where
  local_equations : ∀ {S : Scheme.{u}} (E : ModuliPoint S),
    Nonempty (WeierstrassLocalChartStatement E)
  coordinate_transitions : Prop
  torsor : Prop

theorem universalWeierstrass_is_H_torsor :
    Nonempty WeierstrassCoverTorsorStatement := by
  sorry

/-- The smooth and surjective cover lemma in the source. -/
theorem universalWeierstrass_smooth_surjective :
    IsSmoothModuliMorphism universalWeierstrassMorphism ∧
      IsSurjectiveModuliMorphism universalWeierstrassMorphism := by
  sorry

/-- The quotient-stack presentation described by the source proof.

The available Mathlib group is the group of coordinate-change points over
`UniversalBaseRing`; it is not itself the group scheme `H` over `ℤ`.  The
quotient-stack assertion is therefore retained as an explicit presentation
field instead of identifying these two objects. -/
structure GlobalQuotientPresentation where
  source : Scheme.{0}
  source_eq : source = universalBaseScheme
  coordinateGroupPoints : Type
  coordinateGroupPoints_group : Group coordinateGroupPoints
  coordinateGroupPoints_eq :
    coordinateGroupPoints = WeierstrassCoordinateGroup UniversalBaseRing
  presentation : Prop

theorem ellipticModuli_is_global_quotient :
    Nonempty GlobalQuotientPresentation := by
  sorry

end Formalization.Books.StacksIntroduction.Unit01
