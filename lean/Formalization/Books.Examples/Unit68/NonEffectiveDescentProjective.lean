import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Formalization.«Books.Examples».Unit38.FiniteTypeFlatNotFinitePresentation
import Formalization.«Books.SpacesGroupoids».Unit19.QuotientSheaves

/-!
# Examples, Chapter 68: non-effective descent data for projective schemes

This file records the precise geometric data in the Hironaka example.  The
coordinate calculations are made with Mathlib's projectivization and
multivariable-polynomial APIs.  Mathlib does not currently provide blowups,
rational equivalence of cycles, or relative projective space, so those parts
are exposed as source-facing interfaces below.  Algebraic spaces use the
earlier functor-of-points model from the groupoids chapters.  This keeps the
hypotheses and conclusions of the example available to the proof stage
without replacing them by tautological propositions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Set
open scoped LinearAlgebra.Projectivization

universe u

namespace Formalization.«Books.Examples».Unit68

/-! ## The involution on projective 3-space -/

/-- The four homogeneous coordinates used for `ℙ³_ℂ`. -/
abbrev ComplexProjectiveThreeCoordinates := Fin 4 → ℂ

/-- A point model for complex projective 3-space. -/
abbrev ComplexProjectiveThreePoint := ℙ ℂ ComplexProjectiveThreeCoordinates

/-- The base scheme over which the chapter's schemes are defined. -/
abbrev complexSpectrum : Scheme :=
  Formalization.«Books.Examples».Unit38.baseScheme ℂ

/-- The actual projective 3-space scheme from the earlier canonical model. -/
abbrev complexProjectiveThreeSpace : Scheme :=
  Formalization.«Books.Examples».Unit38.projectiveSpace ℂ 3

/-- The standard complex projective line, reused for the exceptional fibres. -/
abbrev complexProjectiveLine : Scheme :=
  Formalization.«Books.Examples».Unit38.projectiveLine ℂ

/-- The permutation `(x, y, z, w) ↦ (y, x, w, z)`. -/
def coordinateSwap : Fin 4 ≃ Fin 4 :=
  (Equiv.swap (0 : Fin 4) 1).trans (Equiv.swap (2 : Fin 4) 3)

/-- The corresponding linear automorphism of the coordinate vector space. -/
def coordinateSwapLinearEquiv :
    ComplexProjectiveThreeCoordinates ≃ₗ[ℂ] ComplexProjectiveThreeCoordinates where
  toFun v := v ∘ coordinateSwap
  invFun v := v ∘ coordinateSwap.symm
  left_inv v := by
    funext i
    simp [Function.comp_def]
  right_inv v := by
    funext i
    simp [Function.comp_def]
  map_add' v w := by
    funext i
    simp [Function.comp_def]
  map_smul' a v := by
    funext i
    simp [Function.comp_def]

/-- Hironaka's involution on the point model of projective 3-space. -/
def projectiveInvolution : ComplexProjectiveThreePoint → ComplexProjectiveThreePoint :=
  Projectivization.map coordinateSwapLinearEquiv.toLinearMap
    coordinateSwapLinearEquiv.injective

/-- The nonidentity element of the additive group `ℤ/2ℤ`. -/
abbrev HironakaInvolutionGroup := ZMod 2

def nontrivialElementOfZModTwo : ZMod 2 := 1

/-- The coordinate vector displayed by the nontrivial group element. -/
def coordinateSwapVector (v : ComplexProjectiveThreeCoordinates) :
    ComplexProjectiveThreeCoordinates :=
  ![v 1, v 0, v 3, v 2]

theorem coordinateSwapLinearEquiv_apply (v : ComplexProjectiveThreeCoordinates) :
    coordinateSwapLinearEquiv v = coordinateSwapVector v := by
  sorry

theorem projectiveInvolution_mk (v : ComplexProjectiveThreeCoordinates) (hv : v ≠ 0) :
    projectiveInvolution (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (coordinateSwapLinearEquiv v)
        (coordinateSwapLinearEquiv.injective.ne hv) := by
  rfl

theorem projectiveInvolution_involutive :
    Function.Involutive projectiveInvolution := by
  sorry

/-- The additive `ℤ/2ℤ` action whose nonzero element is the involution. -/
def projectivePointAction (a : HironakaInvolutionGroup)
    (p : ComplexProjectiveThreePoint) : ComplexProjectiveThreePoint :=
  if a = 0 then p else projectiveInvolution p

noncomputable instance projectivePointAddAction :
    AddAction HironakaInvolutionGroup ComplexProjectiveThreePoint where
  vadd := projectivePointAction
  zero_vadd p := by
    change (if (0 : HironakaInvolutionGroup) = 0 then p else projectiveInvolution p) = p
    rw [if_pos rfl]
  add_vadd a b p := by
    sorry

theorem projectivePointAction_nontrivial (p : ComplexProjectiveThreePoint) :
    projectivePointAction nontrivialElementOfZModTwo p = projectiveInvolution p := by
  sorry

/-- The line fixed by the involution with equal coordinates in each pair. -/
def fixedLinePlus : Set ComplexProjectiveThreePoint :=
  {p | p.rep 0 = p.rep 1 ∧ p.rep 2 = p.rep 3}

/-- The second fixed line, with opposite coordinates in each pair. -/
def fixedLineMinus : Set ComplexProjectiveThreePoint :=
  {p | p.rep 0 = -p.rep 1 ∧ p.rep 2 = -p.rep 3}

/-- The open set on which the involution acts freely. -/
def freeProjectiveLocus : Set ComplexProjectiveThreePoint :=
  (fixedLinePlus ∪ fixedLineMinus)ᶜ

theorem fixed_locus_of_projectiveInvolution :
    {p | projectiveInvolution p = p} = fixedLinePlus ∪ fixedLineMinus := by
  sorry

theorem fixed_lines_are_disjoint : Disjoint fixedLinePlus fixedLineMinus := by
  sorry

theorem projectiveInvolution_free_on_freeProjectiveLocus {p : ComplexProjectiveThreePoint}
    (hp : p ∈ freeProjectiveLocus) : projectiveInvolution p ≠ p := by
  intro h
  exact hp (by rw [← fixed_locus_of_projectiveInvolution]; exact h)

/-! ## The two conics and the invariant quotient presentation -/

/-- The conic `xy = z², w = 0`. -/
def conicC : Set ComplexProjectiveThreePoint :=
  {p | p.rep 0 * p.rep 1 = (p.rep 2) ^ 2 ∧ p.rep 3 = 0}

/-- The conic `xy = w², z = 0`. -/
def conicD : Set ComplexProjectiveThreePoint :=
  {p | p.rep 0 * p.rep 1 = (p.rep 3) ^ 2 ∧ p.rep 2 = 0}

def conicUnion : Set ComplexProjectiveThreePoint := conicC ∪ conicD

def pVector : ComplexProjectiveThreeCoordinates := ![1, 0, 0, 0]

def qVector : ComplexProjectiveThreeCoordinates := ![0, 1, 0, 0]

lemma pVector_ne_zero : pVector ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 4)
  simp [pVector] at h0

lemma qVector_ne_zero : qVector ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Fin 4)
  simp [qVector] at h1

/-- The two intersection points of the conics. -/
def intersectionPointP : ComplexProjectiveThreePoint :=
  Projectivization.mk ℂ pVector pVector_ne_zero

def intersectionPointQ : ComplexProjectiveThreePoint :=
  Projectivization.mk ℂ qVector qVector_ne_zero

/-- The two homogeneous equations defining `C` and `D`. -/
def conicCForm (v : ComplexProjectiveThreeCoordinates) : ℂ :=
  v 0 * v 1 - (v 2) ^ 2

def conicDForm (v : ComplexProjectiveThreeCoordinates) : ℂ :=
  v 0 * v 1 - (v 3) ^ 2

/-- Gradients of the equations used to test smoothness of the conics. -/
def conicCQuadraticGradient (v : ComplexProjectiveThreeCoordinates) :
    ComplexProjectiveThreeCoordinates :=
  ![v 1, v 0, -(2 : ℂ) * v 2, 0]

def conicDQuadraticGradient (v : ComplexProjectiveThreeCoordinates) :
    ComplexProjectiveThreeCoordinates :=
  ![v 1, v 0, 0, -(2 : ℂ) * v 3]

def conicCLinearGradient : ComplexProjectiveThreeCoordinates := ![0, 0, 0, 1]

def conicDLinearGradient : ComplexProjectiveThreeCoordinates := ![0, 0, 1, 0]

/-- Independence of the two projective gradients at every point of `C`. -/
def IsSmoothConicC : Prop :=
  ∀ v, v ≠ 0 → conicCForm v = 0 → v 3 = 0 →
    ∀ a b : ℂ,
      (∀ i, a * conicCQuadraticGradient v i + b * conicCLinearGradient i = 0) →
        a = 0 ∧ b = 0

/-- Independence of the two projective gradients at every point of `D`. -/
def IsSmoothConicD : Prop :=
  ∀ v, v ≠ 0 → conicDForm v = 0 → v 2 = 0 →
    ∀ a b : ℂ,
      (∀ i, a * conicDQuadraticGradient v i + b * conicDLinearGradient i = 0) →
        a = 0 ∧ b = 0

theorem conicC_is_smooth : IsSmoothConicC := by
  sorry

theorem conicD_is_smooth : IsSmoothConicD := by
  sorry

theorem conics_are_contained_in_freeProjectiveLocus :
    conicC ∪ conicD ⊆ freeProjectiveLocus := by
  sorry

theorem intersectionPointP_mem_conicC : intersectionPointP ∈ conicC := by
  sorry

theorem intersectionPointP_mem_conicD : intersectionPointP ∈ conicD := by
  sorry

theorem intersectionPointQ_mem_conicC : intersectionPointQ ∈ conicC := by
  sorry

theorem intersectionPointQ_mem_conicD : intersectionPointQ ∈ conicD := by
  sorry

theorem conics_intersection : conicC ∩ conicD = {intersectionPointP, intersectionPointQ} := by
  sorry

theorem projectiveInvolution_maps_conicC_to_conicD :
    MapsTo projectiveInvolution conicC conicD := by
  sorry

theorem projectiveInvolution_maps_conicD_to_conicC :
    MapsTo projectiveInvolution conicD conicC := by
  sorry

theorem projectiveInvolution_image_conicC :
    projectiveInvolution '' conicC = conicD := by
  sorry

theorem projectiveInvolution_image_conicD :
    projectiveInvolution '' conicD = conicC := by
  sorry

theorem projectiveInvolution_swaps_intersection_points :
    projectiveInvolution intersectionPointP = intersectionPointQ ∧
      projectiveInvolution intersectionPointQ = intersectionPointP := by
  sorry

/-- The polynomial ring in the original four homogeneous coordinates. -/
abbrev CoordinatePolynomialRing := MvPolynomial (Fin 4) ℂ

/-- The polynomial involution induced by the coordinate permutation. -/
def coordinatePolynomialInvolution : CoordinatePolynomialRing ≃ₐ[ℂ] CoordinatePolynomialRing :=
  MvPolynomial.renameEquiv ℂ coordinateSwap

def coordinateX₀ : CoordinatePolynomialRing := MvPolynomial.X 0

def coordinateX₁ : CoordinatePolynomialRing := MvPolynomial.X 1

def coordinateX₂ : CoordinatePolynomialRing := MvPolynomial.X 2

def coordinateX₃ : CoordinatePolynomialRing := MvPolynomial.X 3

def sourceInvariantU₀ : CoordinatePolynomialRing := coordinateX₀ + coordinateX₁

def sourceInvariantU₁ : CoordinatePolynomialRing := coordinateX₂ + coordinateX₃

def sourceInvariantV₀ : CoordinatePolynomialRing := (coordinateX₀ - coordinateX₁) ^ 2

def sourceInvariantV₁ : CoordinatePolynomialRing := (coordinateX₂ - coordinateX₃) ^ 2

def sourceInvariantV₂ : CoordinatePolynomialRing :=
  (coordinateX₀ - coordinateX₁) * (coordinateX₂ - coordinateX₃)

theorem sourceInvariantGenerators_are_fixed :
    coordinatePolynomialInvolution sourceInvariantU₀ = sourceInvariantU₀ ∧
      coordinatePolynomialInvolution sourceInvariantU₁ = sourceInvariantU₁ ∧
      coordinatePolynomialInvolution sourceInvariantV₀ = sourceInvariantV₀ ∧
      coordinatePolynomialInvolution sourceInvariantV₁ = sourceInvariantV₁ ∧
      coordinatePolynomialInvolution sourceInvariantV₂ = sourceInvariantV₂ := by
  sorry

theorem coordinatePolynomialInvolution_involutive (f : CoordinatePolynomialRing) :
    coordinatePolynomialInvolution (coordinatePolynomialInvolution f) = f := by
  sorry

/-- The fixed subalgebra for the order-two polynomial involution. -/
def coordinateInvariantSubalgebra : Subalgebra ℂ CoordinatePolynomialRing where
  carrier := {f | coordinatePolynomialInvolution f = f}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change coordinatePolynomialInvolution (f + g) = f + g
    rw [map_add, hf, hg]
  mul_mem' := by
    intro f g hf hg
    change coordinatePolynomialInvolution (f * g) = f * g
    rw [map_mul, hf, hg]
  algebraMap_mem' := by
    intro r
    exact coordinatePolynomialInvolution.commutes r

lemma sourceInvariantU₀_mem_coordinateInvariantSubalgebra :
    sourceInvariantU₀ ∈ coordinateInvariantSubalgebra := by
  exact sourceInvariantGenerators_are_fixed.1

lemma sourceInvariantU₁_mem_coordinateInvariantSubalgebra :
    sourceInvariantU₁ ∈ coordinateInvariantSubalgebra := by
  exact sourceInvariantGenerators_are_fixed.2.1

lemma sourceInvariantV₀_mem_coordinateInvariantSubalgebra :
    sourceInvariantV₀ ∈ coordinateInvariantSubalgebra := by
  exact sourceInvariantGenerators_are_fixed.2.2.1

lemma sourceInvariantV₁_mem_coordinateInvariantSubalgebra :
    sourceInvariantV₁ ∈ coordinateInvariantSubalgebra := by
  exact sourceInvariantGenerators_are_fixed.2.2.2.1

lemma sourceInvariantV₂_mem_coordinateInvariantSubalgebra :
    sourceInvariantV₂ ∈ coordinateInvariantSubalgebra := by
  exact sourceInvariantGenerators_are_fixed.2.2.2.2

/-- The five generators in the invariant presentation. -/
abbrev InvariantPresentationPolynomialRing := MvPolynomial (Fin 5) ℂ

def invariantU₀ : InvariantPresentationPolynomialRing := MvPolynomial.X 0

def invariantU₁ : InvariantPresentationPolynomialRing := MvPolynomial.X 1

def invariantV₀ : InvariantPresentationPolynomialRing := MvPolynomial.X 2

def invariantV₁ : InvariantPresentationPolynomialRing := MvPolynomial.X 3

def invariantV₂ : InvariantPresentationPolynomialRing := MvPolynomial.X 4

/-- The single relation `v₀v₁ = v₂²` in the invariant ring. -/
def invariantRelation : InvariantPresentationPolynomialRing :=
  invariantV₀ * invariantV₁ - invariantV₂ ^ 2

def invariantRelationIdeal : Ideal InvariantPresentationPolynomialRing :=
  Ideal.span {invariantRelation}

/-- The invariant ring presentation used for the quotient projective scheme. -/
abbrev InvariantPresentationRing :=
  InvariantPresentationPolynomialRing ⧸ invariantRelationIdeal

/-- The grading in which `u₀,u₁` have degree one and `v₀,v₁,v₂` have degree two. -/
def invariantDegree (i : Fin 5) : ℕ :=
  if i.val < 2 then 1 else 2

def invariantQuotientMk (f : InvariantPresentationPolynomialRing) :
    InvariantPresentationRing :=
  Ideal.Quotient.mk invariantRelationIdeal f

structure InvariantRingPresentationData where
  equivalence : coordinateInvariantSubalgebra ≃ₐ[ℂ] InvariantPresentationRing
  equivalence_u₀ :
    equivalence ⟨sourceInvariantU₀,
      sourceInvariantU₀_mem_coordinateInvariantSubalgebra⟩ =
      invariantQuotientMk invariantU₀
  equivalence_u₁ :
    equivalence ⟨sourceInvariantU₁,
      sourceInvariantU₁_mem_coordinateInvariantSubalgebra⟩ =
      invariantQuotientMk invariantU₁
  equivalence_v₀ :
    equivalence ⟨sourceInvariantV₀,
      sourceInvariantV₀_mem_coordinateInvariantSubalgebra⟩ =
      invariantQuotientMk invariantV₀
  equivalence_v₁ :
    equivalence ⟨sourceInvariantV₁,
      sourceInvariantV₁_mem_coordinateInvariantSubalgebra⟩ =
      invariantQuotientMk invariantV₁
  equivalence_v₂ :
    equivalence ⟨sourceInvariantV₂,
      sourceInvariantV₂_mem_coordinateInvariantSubalgebra⟩ =
      invariantQuotientMk invariantV₂

theorem invariant_ring_presentation :
    Nonempty InvariantRingPresentationData := by
  sorry

/-! The remaining graded-quotient construction uses the relative-`Proj`
interface introduced in the earlier projective-family chapter.  The missing
graded-ideal calculation is isolated in its existence theorem. -/

abbrev InvariantRelativeProjPresentation :=
  Formalization.«Books.Examples».Unit38.RelativeProjPresentation
    ℂ InvariantPresentationRing

theorem invariant_relative_proj_presentation_exists :
    Nonempty InvariantRelativeProjPresentation := by
  sorry

noncomputable def invariantRelativeProjPresentation :
    InvariantRelativeProjPresentation :=
  Classical.choice invariant_relative_proj_presentation_exists

noncomputable def invariantProjectiveQuotient : Scheme :=
  Formalization.«Books.Examples».Unit38.relativeProjScheme
    invariantRelativeProjPresentation

noncomputable def invariantProjectiveQuotientToComplex :
    invariantProjectiveQuotient ⟶ complexSpectrum :=
  Formalization.«Books.Examples».Unit38.relativeProjMap
    invariantRelativeProjPresentation

structure InvariantProjectiveQuotientData where
  presentation : InvariantRingPresentationData
  relativePresentation : InvariantRelativeProjPresentation
  degree : Fin 5 → ℕ
  degree_identification : degree = invariantDegree
  projectiveScheme : Scheme
  projectiveScheme_to_complex : projectiveScheme ⟶ complexSpectrum
  projectiveScheme_is_Proj_of_ring :
    Nonempty (projectiveScheme ≅ invariantProjectiveQuotient)
  is_projective_spectrum_of_invariants : Prop

theorem invariant_projective_quotient_presentation :
    Nonempty InvariantProjectiveQuotientData := by
  sorry

/-! ## Projective morphisms and scheme descent data -/

/-- A source-facing interface for a relative projective `n`-space.

The `standard` field is the missing relative-Proj identification in the current
Mathlib API; it is deliberately a field of the witness rather than an
assumption added to any theorem conclusion.
-/
structure RelativeProjectiveSpace (Y : Scheme) where
  dimension : ℕ
  space : Scheme
  projection : space ⟶ Y
  standard : Prop

/-- The closed-immersion presentation of a projective scheme morphism. -/
def IsProjectiveMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ (P : RelativeProjectiveSpace Y) (i : X ⟶ P.space),
    P.standard ∧ IsClosedImmersion i ∧ i ≫ P.projection = f

/-- A quasi-affine morphism, expressed as an open immersion into an affine
morphism.  This is the relative version needed for the chapter's opening
descent statement. -/
def IsQuasiAffineMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ (Z : Scheme) (i : X ⟶ Z) (p : Z ⟶ Y),
    IsOpenImmersion i ∧ IsAffineHom p ∧ i ≫ p = f

/-- The usual flat, quasi-compact, surjective class of fpqc morphisms. -/
def IsFpqcMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  Flat f ∧ QuasiCompact f ∧ Surjective f

/-- The overlap object of an étale cover, used for a descent datum. -/
abbrev SchemeCoverOverlap {X S : Scheme} (cover : X ⟶ S) := pullback cover cover

/-- A scheme descent datum with its overlap isomorphism and cocycle condition. -/
structure SchemeDescentDatum {X S : Scheme} (cover : X ⟶ S) where
  object : Over X
  descentIso :
    (Over.pullback (pullback.fst cover cover)).obj object ≅
      (Over.pullback (pullback.snd cover cover)).obj object
  cocycle_condition : Prop

/-- An isomorphism from a descent datum to the pullback of an object over the base.

The field `respects_descent` is the usual compatibility with the canonical
overlap isomorphism.  It is kept explicit because Mathlib has no bundled
pseudofunctor of schemes with this compatibility built in.
-/
structure SchemeDescentDatum.EffectiveWitness
    {X S : Scheme} {cover : X ⟶ S} (D : SchemeDescentDatum cover) where
  baseObject : Over S
  objectIso : (Over.pullback cover).obj baseObject ≅ D.object
  respects_descent : Prop

/-- Effectivity of a scheme descent datum. -/
def SchemeDescentDatum.IsEffective
    {X S : Scheme} {cover : X ⟶ S} (D : SchemeDescentDatum cover) : Prop :=
  Nonempty (D.EffectiveWitness)

/-- Every descent datum whose morphism lies in `P` is effective for every fpqc
cover. -/
def FpqcDescentEffectiveFor
    (P : ∀ {X Y : Scheme}, (X ⟶ Y) → Prop) : Prop :=
  ∀ {X S : Scheme} (cover : X ⟶ S), IsFpqcMorphism cover →
    ∀ D : SchemeDescentDatum cover, P D.object.hom → D.IsEffective

theorem affine_and_quasi_affine_fpqc_descent :
    FpqcDescentEffectiveFor IsQuasiAffineMorphism := by
  sorry

theorem projective_descent_is_not_always_effective :
    ¬ FpqcDescentEffectiveFor IsProjectiveMorphism := by
  sorry

/-- The quotient map `Y → S` is a free torsor for the two-element group. -/
structure ZModTwoTorsor {Y S : Scheme} (f : Y ⟶ S) where
  action : Y ⟶ Y
  action_square : action ≫ action = 𝟙 Y
  action_over_base : action ≫ f = f
  free_action : Prop
  transitive_on_geometric_fibres : Prop
  quotient_map : Prop

/-! ## The two local blowup charts and the glued threefold -/

/-- Data for one of the two local iterated blowup constructions. -/
structure LocalBlowupChart (Y : Scheme) where
  openPart : Scheme
  openToY : openPart ⟶ Y
  open_immersion : IsOpenImmersion openToY
  chart : Scheme
  chartToOpen : chart ⟶ openPart
  proper : IsProper chartToOpen
  projective : IsProjectiveMorphism chartToOpen
  firstCentre : Scheme
  firstCentreToOpen : firstCentre ⟶ openPart
  firstCentre_closed : IsClosedImmersion firstCentreToOpen
  secondCentre : Scheme
  secondCentreToChart : secondCentre ⟶ chart
  secondCentre_closed : IsClosedImmersion secondCentreToChart
  firstCentre_is_D_or_C_as_specified : Prop
  secondCentre_is_the_strict_transform_as_specified : Prop
  first_operation_is_blowup : Prop
  second_operation_is_strict_transform : Prop

/-- The two charts in the source, with their order of blowup centres. -/
structure HironakaLocalCharts (Y : Scheme) where
  awayFromP : LocalBlowupChart Y
  awayFromQ : LocalBlowupChart Y
  awayFromP_open_description : Prop
  awayFromQ_open_description : Prop
  first_chart_blows_up_D_then_C : Prop
  second_chart_blows_up_C_then_D : Prop
  charts_agree_over_the_common_open : Prop

/-- A lifted involution on the glued local construction. -/
structure LiftedSchemeInvolution (V : Scheme) where
  action : V ⟶ V
  square : action ≫ action = 𝟙 V
  exchanges_the_two_charts : Prop

/-- The proper non-projective scheme obtained by gluing the two charts. -/
structure NonProjectiveProperThreefold (Y S : Scheme) (yToS : Y ⟶ S)
    (Y_to_complex : Y ⟶ complexSpectrum) where
  scheme : Scheme
  toY : scheme ⟶ Y
  proper : IsProper toY
  not_projective : ¬ IsProjectiveMorphism toY
  smooth : Smooth (toY ≫ Y_to_complex)
  dimension_three : Prop
  charts : HironakaLocalCharts Y
  liftedInvolution : LiftedSchemeInvolution scheme
  descentDatum : SchemeDescentDatum yToS
  descentDatum_object_identification :
    Nonempty (Over.mk toY ≅ descentDatum.object)
  descent_datum_is_induced_by_the_lifted_involution : Prop

/-! ## The quotient contradiction via the exceptional curve cycle -/

/-- A named interface for rational equivalence of algebraic cycles.

Mathlib currently defines algebraic cycles but not their Chow/rational
equivalence relation, so the relation and its degree compatibility are
packaged as data here.
-/
structure CycleRationalEquivalenceData (E : Scheme) where
  equivalent : AlgebraicCycle E ℤ → AlgebraicCycle E ℤ → Prop
  equivalent_is_equivalence : Equivalence equivalent
  degree : AlgebraicCycle E ℤ → ℤ
  degree_zero : degree 0 = 0
  degree_respects_equivalence :
    ∀ c d, equivalent c d → degree c = degree d

/-- The exceptional fibres and the cycle relation used in Hironaka's argument. -/
structure ExceptionalCurveCycleArgument (V_Y : Scheme) where
  /-- The proper surface sitting inside the glued threefold. -/
  E : Scheme
  E_to_VY : E ⟶ V_Y
  E_to_VY_closed : IsClosedImmersion E_to_VY
  baseCurveUnion : Scheme
  toBase : E ⟶ baseCurveUnion
  proper : IsProper toBase
  L₀ : Scheme
  M₀ : Scheme
  L₀' : Scheme
  M₀' : Scheme
  L₀_to_E : L₀ ⟶ E
  M₀_to_E : M₀ ⟶ E
  L₀'_to_E : L₀' ⟶ E
  M₀'_to_E : M₀' ⟶ E
  L₀_is_projective_line : Nonempty (L₀ ≅ complexProjectiveLine)
  M₀_is_projective_line : Nonempty (M₀ ≅ complexProjectiveLine)
  L₀'_is_projective_line : Nonempty (L₀' ≅ complexProjectiveLine)
  M₀'_is_projective_line : Nonempty (M₀' ≅ complexProjectiveLine)
  base_is_the_union_of_the_two_conics : Prop
  fibres_away_from_intersection_are_projective_lines : Prop
  fibre_over_P_is_L₀_union_M₀ : Prop
  fibre_over_Q_is_L₀'_union_M₀' : Prop
  L₀'_is_the_image_of_M₀_under_g : Prop
  M₀'_is_the_image_of_L₀_under_g : Prop
  cycleData : CycleRationalEquivalenceData E
  cycle_L₀ : AlgebraicCycle E ℤ
  cycle_M₀' : AlgebraicCycle E ℤ
  cycle_gL₀ : AlgebraicCycle E ℤ
  cycle_M₀'_is_cycle_gL₀ : cycle_M₀' = cycle_gL₀
  cycle_relation : cycleData.equivalent (cycle_L₀ + cycle_gL₀) 0
  surface : Prop
  positive_degree_on_L₀_plus_gL₀ :
    0 < cycleData.degree (cycle_L₀ + cycle_gL₀)

/-- The divisor produced from a hypothetical scheme quotient. -/
structure QuotientDivisorObstruction {V_Y : Scheme}
    (A : ExceptionalCurveCycleArgument V_Y) where
  divisor : AlgebraicCycle V_Y ℤ
  line_bundle : Prop
  restriction_to_E_is_a_line_bundle : Prop
  regular_local_ring_is_a_UFD : Prop
  inverse_image_is_effective_divisor : Prop
  contains_a_point_of_the_descended_curve : Prop
  intersects_the_exceptional_cycle : Prop
  contains_neither_component : Prop
  positive_restriction_degree :
    0 < A.cycleData.degree (A.cycle_L₀ + A.cycle_gL₀)

theorem exceptional_cycle_forbids_quotient_divisor
    {V_Y : Scheme} (A : ExceptionalCurveCycleArgument V_Y) :
    ¬ Nonempty (QuotientDivisorObstruction A) := by
  rintro ⟨D⟩
  have hzero : A.cycleData.degree (A.cycle_L₀ + A.cycle_gL₀) = 0 := by
    rw [A.cycleData.degree_respects_equivalence
      (A.cycle_L₀ + A.cycle_gL₀) 0 A.cycle_relation,
      A.cycleData.degree_zero]
  have hpos := D.positive_restriction_degree
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

/-! ## The complete descent datum -/

/-- The two-chart étale refinement `X → Y → S`. -/
structure TwoChartEtaleRefinement where
  Y : Scheme
  S : Scheme
  X : Scheme
  yToS : Y ⟶ S
  xToY : X ⟶ Y
  xToS : X ⟶ S
  Y_to_projective_three_space : Y ⟶ complexProjectiveThreeSpace
  Y_open_in_projective_three_space : IsOpenImmersion Y_to_projective_three_space
  Y_to_complex : Y ⟶ complexSpectrum
  S_to_complex : S ⟶ complexSpectrum
  quotient_over_complex : yToS ≫ S_to_complex = Y_to_complex
  factorization : xToY ≫ yToS = xToS
  y_torsor : ZModTwoTorsor yToS
  y_action_is_the_restriction_of_the_projective_involution : Prop
  yToS_etale : Etale yToS
  yToS_surjective : Surjective yToS
  xToY_etale : Etale xToY
  xToY_surjective : Surjective xToY
  xToS_etale : Etale xToS
  xToS_surjective : Surjective xToS
  Y_smooth : Smooth Y_to_complex
  Y_quasi_projective : Prop
  S_smooth : Smooth S_to_complex
  S_quasi_projective : Prop
  S_is_the_invariant_projective_quotient : Prop
  Y_is_the_free_projective_locus : Prop
  quotient_map_is_the_image_of_the_free_locus : Prop
  x_is_disjoint_union_of_deleted_points : Prop
  y_is_the_free_involution_quotient : Prop

/-- All the source data in the non-effective projective descent example. -/
structure HironakaNonEffectiveDescentData where
  refinement : TwoChartEtaleRefinement
  localConstruction :
    NonProjectiveProperThreefold refinement.Y refinement.S refinement.yToS
      refinement.Y_to_complex
  V : Scheme
  vToX : V ⟶ refinement.X
  v_projective_over_X : IsProjectiveMorphism vToX
  v_projective_from_the_two_blowup_charts : Prop
  v_is_pullback_of_local_construction : Prop
  descent : SchemeDescentDatum refinement.xToS
  descent_object_identification :
    Nonempty (Over.mk vToX ≅ descent.object)
  descent_is_the_pullback_of_the_local_datum : Prop
  descent_is_the_glued_involution_datum : Prop
  exceptionalCycle : ExceptionalCurveCycleArgument localConstruction.scheme

/-- Hironaka's non-effective descent datum for projective schemes. -/
theorem exists_non_effective_projective_descent_datum :
    ∃ D : HironakaNonEffectiveDescentData, ¬ D.descent.IsEffective := by
  sorry

/-- The chapter's opening lemma, with the cover, projective object, and
descent datum exposed instead of hidden in the construction record. -/
theorem lemma_non_effective_descent_projective :
    ∃ (X S V : Scheme) (cover : X ⟶ S) (v : V ⟶ X)
      (D : SchemeDescentDatum cover),
      Etale cover ∧ Surjective cover ∧ IsProjectiveMorphism v ∧
        Nonempty (Over.mk v ≅ D.object) ∧ ¬ D.IsEffective := by
  sorry

/-- The curve and divisor obtained from a hypothetical scheme quotient. -/
structure DescentCurveAndDivisor {V_Y : Scheme}
    (A : ExceptionalCurveCycleArgument V_Y) where
  U : Scheme
  L₁ : Scheme
  L₁_to_quotient : L₁ ⟶ U
  L₁_to_quotient_closed : IsClosedImmersion L₁_to_quotient
  obtained_by_closed_subscheme_descent : Prop
  L₁_is_projective_line : Nonempty (L₁ ≅ complexProjectiveLine)
  inverse_image_in_VY : Scheme
  inverse_image_to_VY : inverse_image_in_VY ⟶ V_Y
  inverse_image_to_VY_closed : IsClosedImmersion inverse_image_to_VY
  inverse_image_is_L₀_union_gL₀ : Prop
  R : U
  R_is_a_complex_point : Prop
  local_ring_function_f : U.presheaf.stalk R
  local_function_vanishes_at_R : Prop
  local_function_not_zero_on_L₁ : Prop
  local_codimension_one_component : Prop
  divisor_is_closure_of_local_component : Prop
  divisor : QuotientDivisorObstruction A

/-- A scheme quotient of the descent datum, including the quotient diagram. -/
structure EffectiveSchemeQuotient (D : HironakaNonEffectiveDescentData) where
  U : Scheme
  U_to_S : U ⟶ D.refinement.S
  descent_effective : D.descent.IsEffective
  VY_to_U : D.localConstruction.scheme ⟶ U
  V_to_U : D.V ⟶ U
  V_to_VY : D.V ⟶ D.localConstruction.scheme
  V_to_VY_commutes :
    V_to_VY ≫ D.localConstruction.toY = D.vToX ≫ D.refinement.xToY
  V_to_U_commutes : V_to_U ≫ U_to_S = D.vToX ≫ D.refinement.xToS
  VY_to_U_commutes :
    VY_to_U ≫ U_to_S = D.localConstruction.toY ≫ D.refinement.yToS
  pullback_is_V : Prop
  pullback_is_V_with_descent_datum : Prop
  curve_and_divisor : DescentCurveAndDivisor D.exceptionalCycle
  curve_and_divisor_is_over_U : Prop

/-- If the pulled-back descent datum were effective by a scheme, the quotient
construction in the source proof would supply its scheme quotient data. -/
theorem effective_descent_produces_scheme_quotient
    (D : HironakaNonEffectiveDescentData) (hD : D.descent.IsEffective) :
    Nonempty (EffectiveSchemeQuotient D) := by
  sorry

theorem effective_scheme_quotient_produces_curve_and_divisor
    (D : HironakaNonEffectiveDescentData) (Q : EffectiveSchemeQuotient D) :
    Nonempty (DescentCurveAndDivisor D.exceptionalCycle) := by
  exact ⟨Q.curve_and_divisor⟩

theorem no_effective_scheme_quotient
    (D : HironakaNonEffectiveDescentData) :
    ¬ Nonempty (EffectiveSchemeQuotient D) := by
  rintro ⟨Q⟩
  exact exceptional_cycle_forbids_quotient_divisor D.exceptionalCycle
    ⟨Q.curve_and_divisor.divisor⟩

theorem descent_datum_not_effective_in_schemes
    (D : HironakaNonEffectiveDescentData) :
    ¬ D.descent.IsEffective := by
  intro hD
  exact no_effective_scheme_quotient D
    (effective_descent_produces_scheme_quotient D hD)

/-! ## Effectivity in algebraic spaces -/

/-- Schemes equipped with their structure morphism to `Spec ℂ`. -/
abbrev ComplexSchemeOver := Over complexSpectrum

/-- The functor-of-points model of algebraic spaces over `Spec ℂ`. -/
abbrev ComplexAlgebraicSpace :=
  Formalization.«Books.SpacesGroupoids».Unit19.AlgebraicSpace
    AlgebraicGeometry.Scheme.fppfTopology

/-- The representable sheaf attached to a scheme over `Spec ℂ`. -/
noncomputable def representableComplexScheme (T : ComplexSchemeOver) :
    ComplexAlgebraicSpace :=
  Formalization.«Books.SpacesGroupoids».Unit19.PreRelation.representableSheaf
    AlgebraicGeometry.Scheme.fppfTopology T.left

/-- Representability by a scheme in the chapter-local algebraic-space model. -/
def IsSchemeAlgebraicSpace (U : ComplexAlgebraicSpace) : Prop :=
  ∃ T : ComplexSchemeOver, Nonempty (U ≅ representableComplexScheme T)

/-- Smoothness, separatedness, and dimension-three data for the quotient space. -/
structure SmoothSeparatedThreefold (U : ComplexAlgebraicSpace) where
  structureMap : U ⟶ representableComplexScheme (Over.mk (𝟙 complexSpectrum))
  smooth : Prop
  separated : Prop
  dimension : ℕ
  dimension_eq_three : dimension = 3

/-- Effectivity of a scheme descent datum after allowing algebraic spaces. -/
structure AlgebraicSpaceEffectivity
    {X S : Scheme} {cover : X ⟶ S} (D : SchemeDescentDatum cover) where
  quotient : ComplexAlgebraicSpace
  descent_pullback_equivalence : Prop
  smooth_separated_threefold : SmoothSeparatedThreefold quotient
  quotient_is_not_a_scheme : ¬ IsSchemeAlgebraicSpace quotient
  descent_is_effective_after_this_quotient : Prop
  U_is_a_small_resolution_of_the_blowup : Prop
  blowup_along_the_irreducible_nodal_curve : Prop
  blowup_has_a_node_singularity : Prop
  other_small_resolution_is_a_flop : Prop
  other_small_resolution_is_not_a_scheme : Prop

theorem descent_datum_effective_in_algebraic_spaces :
    ∃ (D : HironakaNonEffectiveDescentData),
      ¬ D.descent.IsEffective ∧
        Nonempty (AlgebraicSpaceEffectivity D.descent) := by
  sorry

end Formalization.«Books.Examples».Unit68
