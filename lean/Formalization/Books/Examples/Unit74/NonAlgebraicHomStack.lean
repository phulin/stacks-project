import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Formalization.Books.SpacesGroupoids.Unit20.QuotientStacks

/-!
# Examples, Chapter 74: an example of a non-algebraic Hom-stack

This file records the definitions and theorem interfaces in the chapter's
example.  The project already has the fibred-category and quotient-stack
interfaces, so the Hom-stack is expressed using those interfaces.  Fppf
cohomology and the geometric properties of the displayed surface are kept as
named data when the current Mathlib snapshot does not provide the relevant
moduli object.
-/

noncomputable section

namespace Formalization.Books.Examples.Unit74

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

open Formalization.Books.Stacks.Unit01
open Formalization.Books.SpacesGroupoids.Unit20

universe u v w

abbrev Scheme := AlgebraicGeometry.Scheme

/-- Schemes over the base, in the same convention as the earlier stack chapters. -/
abbrev SchemeOver (S : Scheme.{u}) := CategoryTheory.Over S

/-- The fppf topology on the big site of schemes over `S`. -/
abbrev FppfTopology (S : Scheme.{u}) : GrothendieckTopology (SchemeOver S) :=
  AlgebraicGeometry.Scheme.fppfTopology.over S

/-- A stack in groupoids over a fixed base scheme. -/
structure RelativeStack (S : Scheme.{u}) where
  value : FiberedCategory (SchemeOver S)
  isStackInGroupoids : StackInGroupoids value (FppfTopology S)

/-- The source-facing algebraicity interface for a relative stack.

The project has no native algebraic-stack object.  This is the established
presentation-level marker used by the preceding stack formalizations. -/
structure AlgebraicStackPresentation (S : Scheme.{u}) where
  stack : RelativeStack S
  isAlgebraic : Prop

def IsAlgebraicRelativeStack {S : Scheme.{u}} (F : RelativeStack S) : Prop :=
  ∃ A : AlgebraicStackPresentation S, A.stack.value = F.value ∧ A.isAlgebraic

/-- A relative 1-morphism of stacks. -/
abbrev RelativeStackMorphism {S : Scheme.{u}}
    (Y Z : RelativeStack S) := FiberedMorphism Y.value Z.value

/-- A pointwise 2-morphism of relative stack morphisms. -/
def RelativeTwoMorphism {S : Scheme.{u}}
    {Y Z : RelativeStack S} (f g : RelativeStackMorphism Y Z) : Prop :=
  ∀ T : SchemeOver S,
    Nonempty ((f.app (.mk (op T))).toFunctor ⟶
      (g.app (.mk (op T))).toFunctor)

/-- The category of 1-morphisms `Y_T ⟶ Z_T` in the fibre over `T`. -/
abbrev RelativeHomFiber {S : Scheme.{u}}
    (Y Z : RelativeStack S) (T : SchemeOver S) :=
  Fiber Y.value T ⥤ Fiber Z.value T

/-- The fibrewise presentation of the Hom-stack. -/
structure HomStackPresentation {S : Scheme.{u}}
    (Y Z : RelativeStack S) where
  stack : RelativeStack S
  fiberDescription : ∀ T : SchemeOver S,
    Nonempty (Fiber stack.value T ≌ RelativeHomFiber Y Z T)

/-- The omitted stack-theoretic construction of the Hom-stack. -/
theorem homStack_exists {S : Scheme.{u}}
    (Y Z : RelativeStack S) : Nonempty (HomStackPresentation Y Z) := by
  sorry

noncomputable def homStackPresentation {S : Scheme.{u}}
    (Y Z : RelativeStack S) : HomStackPresentation Y Z :=
  Classical.choice (homStack_exists Y Z)

/-- `Mor_S(Y,Z)`, with objects and arrows described fibrewise by functors and
natural transformations. -/
noncomputable def homStack {S : Scheme.{u}}
    (Y Z : RelativeStack S) : RelativeStack S :=
  (homStackPresentation Y Z).stack

theorem homStack_is_stack_in_groupoids {S : Scheme.{u}}
    (Y Z : RelativeStack S) :
    StackInGroupoids (homStack Y Z).value (FppfTopology S) :=
  (homStackPresentation Y Z).stack.isStackInGroupoids

theorem homStack_fiber_description {S : Scheme.{u}}
    (Y Z : RelativeStack S) (T : SchemeOver S) :
    Nonempty (Fiber (homStack Y Z).value T ≌ RelativeHomFiber Y Z T) := by
  exact (homStackPresentation Y Z).fiberDescription T

/-- The Hom-stack construction restricted to the algebraic-stack inputs in the
opening statement. -/
noncomputable def homStackOfAlgebraicStacks {S : Scheme.{u}}
    (Y Z : AlgebraicStackPresentation S) : RelativeStack S :=
  homStack Y.stack Z.stack

/-! ## The base and its infinitesimal thickenings -/

/-- The field hypotheses made at the start of the example. -/
structure Chapter74FieldData (k : Type u) [Field k] where
  algebraicallyClosed : IsAlgClosed k
  notAlgebraicClosureOfFiniteField : Prop

/-- `Spec(k[[t]])`. -/
def powerSeriesBase (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (CommRingCat.of (PowerSeries k))

/-- The ideal `(t^(n+1))`; the shift makes `n = 0` the closed fibre. -/
def infinitesimalIdeal (k : Type u) [CommRing k] (n : ℕ) : Ideal (Polynomial k) :=
  Ideal.span {Polynomial.X ^ (n + 1)}

/-- The coordinate ring of the corrected `n`th thickening. -/
abbrev infinitesimalRing (k : Type u) [CommRing k] (n : ℕ) :=
  Polynomial k ⧸ infinitesimalIdeal k n

/-- The corrected `S_n = Spec(k[t]/(t^(n+1)))`. -/
def infinitesimalBase (k : Type u) [CommRing k] (n : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (infinitesimalRing k n))

/-- Truncation followed by passage to `k[t]/(t^(n+1))`.

The multiplicativity of truncation modulo `t^(n+1)` is the elementary ring
calculation used by the construction; its proof belongs to the prove stage. -/
def powerSeriesToInfinitesimalRing (k : Type u) [CommRing k] (n : ℕ) :
    PowerSeries k →+* infinitesimalRing k n :=
  { toFun := fun f =>
      Ideal.Quotient.mk (infinitesimalIdeal k n)
        (PowerSeries.trunc (n + 1) f)
    map_one' := by sorry
    map_mul' := by sorry
    map_zero' := by sorry
    map_add' := by sorry }

/-- The closed point `Spec(k) ⟶ Spec(k[[t]])`. -/
def closedBaseMap (k : Type u) [CommRing k] :
    Spec (CommRingCat.of k) ⟶ powerSeriesBase k :=
  Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))

/-- The structure morphism `Spec(k[[t]]) ⟶ Spec(k)`. -/
def baseToClosedMap (k : Type u) [CommRing k] :
    powerSeriesBase k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (PowerSeries.C (R := k)))

/-- The closed immersion `S_n ⟶ S`. -/
def infinitesimalBaseMap (k : Type u) [CommRing k] (n : ℕ) :
    infinitesimalBase k n ⟶ powerSeriesBase k :=
  Spec.map (CommRingCat.ofHom (powerSeriesToInfinitesimalRing k n))

theorem infinitesimalBaseMap_is_closed_immersion
    (k : Type u) [Field k] (n : ℕ) :
    IsClosedImmersion (infinitesimalBaseMap k n) := by
  sorry

theorem closedBaseMap_is_closed_immersion (k : Type u) [Field k] :
    IsClosedImmersion (closedBaseMap k) := by
  sorry

/-- The quotient map from the `(n+1)`st coordinate ring to the `n`th one. -/
noncomputable def infinitesimalRingRestriction (k : Type u) [CommRing k] (n : ℕ) :
    infinitesimalRing k (n + 1) →+* infinitesimalRing k n :=
  Ideal.Quotient.lift (infinitesimalIdeal k (n + 1))
    (Ideal.Quotient.mk (infinitesimalIdeal k n)) (by sorry)

/-- The inclusion of the `n`th closed thickening into the next one. -/
def infinitesimalBaseRestriction (k : Type u) [CommRing k] (n : ℕ) :
    infinitesimalBase k n ⟶ infinitesimalBase k (n + 1) :=
  Spec.map (CommRingCat.ofHom (infinitesimalRingRestriction k n))

theorem infinitesimalBase_restriction_commutes (k : Type u) [CommRing k]
    (n : ℕ) :
    infinitesimalBaseRestriction k n ≫ infinitesimalBaseMap k (n + 1) =
      infinitesimalBaseMap k n := by
  sorry

/-- The base-changed family `X_n`. -/
def familyThickening {k : Type u} [CommRing k]
    (X : Scheme.{u}) (f : X ⟶ powerSeriesBase k) (n : ℕ) : Scheme.{u} :=
  pullback f (infinitesimalBaseMap k n)

/-- The special fibre `X_0`. -/
abbrev familyClosedFiber {k : Type u} [CommRing k]
    (X : Scheme.{u}) (f : X ⟶ powerSeriesBase k) : Scheme.{u} :=
  pullback f (closedBaseMap k)

/-- The projection from a thickening to the total space. -/
def familyThickeningToTotal {k : Type u} [CommRing k]
    (X : Scheme.{u}) (f : X ⟶ powerSeriesBase k) (n : ℕ) :
    familyThickening X f n ⟶ X :=
  pullback.fst f (infinitesimalBaseMap k n)

/-- The transition map `X_n ⟶ X_(n+1)`. -/
theorem familyThickening_map_exists {k : Type u} [CommRing k]
    (X : Scheme.{u}) (f : X ⟶ powerSeriesBase k) (n : ℕ) :
    Nonempty (familyThickening X f n ⟶ familyThickening X f (n + 1)) := by
  sorry

noncomputable def familyThickeningMap {k : Type u} [CommRing k]
    (X : Scheme.{u}) (f : X ⟶ powerSeriesBase k) (n : ℕ) :
    familyThickening X f n ⟶ familyThickening X f (n + 1) :=
  Classical.choice (familyThickening_map_exists X f n)

theorem familyThickeningMap_toTotal_commutes {k : Type u} [CommRing k]
    (X : Scheme.{u}) (f : X ⟶ powerSeriesBase k) (n : ℕ) :
    familyThickeningMap X f n ≫ familyThickeningToTotal X f (n + 1) =
      familyThickeningToTotal X f n := by
  sorry

/-! ## The curve and the displayed surface -/

/-- The geometric properties of a nodal curve used in the example. -/
structure NodalCurveData (C : Scheme.{u}) where
  isCurve : Prop
  componentsSmoothIrreducible : Prop
  isNodal : Prop
  dualGraphHasLoopOfRationalCurves : Prop

/-- A projective flat family of geometrically connected curves over `k[[t]]`. -/
structure CurveFamilyOverPowerSeries (k : Type u) [Field k] where
  fieldData : Chapter74FieldData k
  totalSpace : Scheme.{u}
  toBase : totalSpace ⟶ powerSeriesBase k
  projective : Prop
  proper : Prop
  flat : Prop
  geometricallyConnectedCurveFibers : Prop
  specialFiberGeometry : NodalCurveData (familyClosedFiber totalSpace toBase)
  regular : Prop

theorem curveFamily_base_field_is_algebraically_closed
    {k : Type u} [Field k] (X : CurveFamilyOverPowerSeries k) :
    IsAlgClosed k :=
  X.fieldData.algebraicallyClosed

abbrev CurveFamilySpecialFiber {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k) : Scheme.{u} :=
  familyClosedFiber X.totalSpace X.toBase

/-- The homogeneous equation
`T₀*T₁*T₂ - t*(T₀^3+T₁^3+T₂^3)`. -/
def exampleSurfaceEquation (k : Type u) [Field k] :
    MvPolynomial (Fin 3) (PowerSeries k) :=
  MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 -
    MvPolynomial.C (PowerSeries.X) *
      (MvPolynomial.X 0 ^ 3 + MvPolynomial.X 1 ^ 3 + MvPolynomial.X 2 ^ 3)

/-- The displayed equation presents a family having the listed properties. -/
structure ExplicitSurfaceFamilyData (k : Type u) [Field k] where
  family : CurveFamilyOverPowerSeries k
  equation : MvPolynomial (Fin 3) (PowerSeries k)
  equation_is_the_displayed_cubic : equation = exampleSurfaceEquation k
  equation_defines_the_family : Prop

theorem exampleSurfaceEquation_realizes_curve_family (k : Type u) [Field k] :
    Nonempty (ExplicitSurfaceFamilyData k) := by
  sorry

/-! ## Abelian varieties, constant abelian schemes, and classifying stacks -/

/-- A source-facing presentation of a nonzero abelian variety over `k`. -/
structure AbelianVarietyData (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (CommRingCat.of k)
  pointType : Type u
  pointGroup : AddCommGroup pointType
  dimension : ℕ
  dimension_pos : 0 < dimension
  isAbelianVariety : Prop

/-- Translation by a point of an abelian variety. -/
def translationBy {k : Type u} [Field k]
    (A₀ : AbelianVarietyData k) (a₀ : A₀.pointType) :
    A₀.pointType → A₀.pointType := by
  letI := A₀.pointGroup
  exact fun x => x + a₀

/-- A point is nontorsion in the additive group of points. -/
def IsNontorsionPoint {k : Type u} [Field k]
    (A₀ : AbelianVarietyData k) (a₀ : A₀.pointType) : Prop := by
  letI := A₀.pointGroup
  exact ∀ n : ℕ, 0 < n → n • a₀ ≠ 0

/-- The source-facing abelian-scheme data over a scheme. -/
structure AbelianSchemeData (S : Scheme.{u}) where
  carrier : Scheme.{u}
  projection : carrier ⟶ S
  pointType : Type u
  pointGroup : AddCommGroup pointType
  smooth : Prop
  flat : Prop
  proper : Prop
  finitePresentation : Prop
  fibersAreAbelianVarieties : Prop

/-- The definition recorded in the footnote for an abelian scheme. -/
def IsAbelianScheme {S : Scheme.{u}} (A : AbelianSchemeData S) : Prop :=
  Flat A.projection ∧ IsProper A.projection ∧
    LocallyOfFinitePresentation A.projection ∧ A.fibersAreAbelianVarieties

/-- The constant abelian scheme `A₀ × Spec(k) S`. -/
def constantAbelianScheme {k : Type u} [Field k]
    (A₀ : AbelianVarietyData k) (S : Scheme.{u})
    (baseMap : S ⟶ Spec (CommRingCat.of k)) : AbelianSchemeData S :=
  { carrier := pullback A₀.structureMap baseMap
    projection := pullback.snd A₀.structureMap baseMap
    pointType := A₀.pointType
    pointGroup := A₀.pointGroup
    smooth := Smooth (pullback.snd A₀.structureMap baseMap)
    flat := Flat (pullback.snd A₀.structureMap baseMap)
    proper := IsProper (pullback.snd A₀.structureMap baseMap)
    finitePresentation := LocallyOfFinitePresentation
      (pullback.snd A₀.structureMap baseMap)
    fibersAreAbelianVarieties := A₀.isAbelianVariety }

theorem constantAbelianScheme_is_abelianScheme {k : Type u} [Field k]
    (A₀ : AbelianVarietyData k) (S : Scheme.{u})
    (baseMap : S ⟶ Spec (CommRingCat.of k))
    (hflat : Flat (pullback.snd A₀.structureMap baseMap))
    (hproper : IsProper (pullback.snd A₀.structureMap baseMap))
    (hfinite : LocallyOfFinitePresentation
      (pullback.snd A₀.structureMap baseMap)) :
    IsAbelianScheme (constantAbelianScheme A₀ S baseMap) := by
  sorry

/-- A groupoid of fppf torsors of a fixed coefficient object. -/
structure FppfTorsorGroupoid {S : Scheme.{u}}
    (A : AbelianSchemeData S) where
  fiber : SchemeOver S → Cat
  isGroupoid : ∀ T, IsGroupoid (fiber T)
  objectsAreFppfTorsors : Prop

/-- The classifying stack `[S/A]` and its torsor description. -/
structure ClassifyingStackPresentation {S : Scheme.{u}}
    (A : AbelianSchemeData S) where
  stack : RelativeStack S
  torsors : FppfTorsorGroupoid A
  fiberEquivalence : ∀ T : SchemeOver S,
    Nonempty (Fiber stack.value T ≌ torsors.fiber T)
  quotientOfTrivialAction : Prop
  isBaseChangeOfTheClassifyingStackOverTheField : Prop
  isSeparated : Prop

theorem classifyingStack_exists {S : Scheme.{u}}
    (A : AbelianSchemeData S) : Nonempty (ClassifyingStackPresentation A) := by
  sorry

noncomputable def classifyingStackPresentation {S : Scheme.{u}}
    (A : AbelianSchemeData S) : ClassifyingStackPresentation A :=
  Classical.choice (classifyingStack_exists A)

/-- The quotient/classifying stack notation `[S/A]`. -/
noncomputable def quotientStack {S : Scheme.{u}}
    (A : AbelianSchemeData S) : RelativeStack S :=
  (classifyingStackPresentation A).stack

theorem quotientStack_fiber_is_fppf_torsors {S : Scheme.{u}}
    (A : AbelianSchemeData S) (T : SchemeOver S) :
    Nonempty (Fiber (quotientStack A).value T ≌
      (classifyingStackPresentation A).torsors.fiber T) := by
  exact (classifyingStackPresentation A).fiberEquivalence T

theorem quotientStack_is_classifying_fppf_torsors {S : Scheme.{u}}
    (A : AbelianSchemeData S) :
    (classifyingStackPresentation A).quotientOfTrivialAction ∧
      (classifyingStackPresentation A).torsors.objectsAreFppfTorsors := by
  sorry

theorem quotientStack_is_base_change {S : Scheme.{u}}
    (A : AbelianSchemeData S) :
    (classifyingStackPresentation A).isBaseChangeOfTheClassifyingStackOverTheField :=
  by sorry

def IsSeparatedRelativeStack {S : Scheme.{u}} (F : RelativeStack S) : Prop :=
  ∃ (A : AbelianSchemeData S) (P : ClassifyingStackPresentation A),
    P.stack.value = F.value ∧ P.isSeparated

theorem quotientStack_is_separated {S : Scheme.{u}}
    (A : AbelianSchemeData S) : IsSeparatedRelativeStack (quotientStack A) := by
  refine ⟨A, classifyingStackPresentation A, rfl, ?_⟩
  sorry

theorem quotientStack_is_algebraic {S : Scheme.{u}}
    (A : AbelianSchemeData S) :
    IsAlgebraicRelativeStack (quotientStack A) := by
  sorry

/-! ## The particular Hom-stack -/

/-- A representable stack presentation for the scheme `X`. -/
structure RepresentableStackPresentation {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k) where
  stack : RelativeStack (powerSeriesBase k)
  representsTheScheme : Prop

theorem representableStack_exists {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k) :
    Nonempty (RepresentableStackPresentation X) := by
  sorry

noncomputable def representableStackPresentation {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k) : RepresentableStackPresentation X :=
  Classical.choice (representableStack_exists X)

noncomputable def representableStack {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k) : RelativeStack (powerSeriesBase k) :=
  (representableStackPresentation X).stack

theorem representableStack_is_algebraic {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k) :
    IsAlgebraicRelativeStack (representableStack X) := by
  sorry

/-- The stack in the example, `Hom_S(X,[S/A])`. -/
noncomputable def exampleHomStack {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k) (A : AbelianSchemeData (powerSeriesBase k)) :
    RelativeStack (powerSeriesBase k) :=
  homStack (representableStack X) (quotientStack A)

theorem exampleHomStack_has_algebraic_inputs {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k)) :
    IsAlgebraicRelativeStack (representableStack X) ∧
      IsAlgebraicRelativeStack (quotientStack A) := by
  exact ⟨representableStack_is_algebraic X, quotientStack_is_algebraic A⟩

/-- The base change `X ×_S T` appearing in the fibrewise torsor description. -/
def familyBaseChange {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (T : SchemeOver (powerSeriesBase k)) : Scheme.{u} :=
  pullback X.toBase T.hom

/-- A fibrewise presentation by fppf torsors on `X ×_S T`. -/
structure FamilyTorsorPresentation {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k)) where
  fiber : SchemeOver (powerSeriesBase k) → Cat
  isGroupoid : ∀ T, IsGroupoid (fiber T)
  fiberDescription : ∀ T,
    Nonempty (Fiber (exampleHomStack X A).value T ≌ fiber T)
  objectsAreFppfTorsorsOnBaseChange : SchemeOver (powerSeriesBase k) → Prop

theorem familyTorsorPresentation_exists {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k)) :
    Nonempty (FamilyTorsorPresentation X A) := by
  sorry

noncomputable def familyTorsorPresentation {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k)) :
    FamilyTorsorPresentation X A :=
  Classical.choice (familyTorsorPresentation_exists X A)

theorem exampleHomStack_fiber_is_fppf_torsors {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (T : SchemeOver (powerSeriesBase k)) :
    Nonempty (Fiber (exampleHomStack X A).value T ≌
      (familyTorsorPresentation X A).fiber T) := by
  exact (familyTorsorPresentation X A).fiberDescription T

theorem exampleHomStack_torsors_are_on_base_change {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (T : SchemeOver (powerSeriesBase k)) :
    (familyTorsorPresentation X A).objectsAreFppfTorsorsOnBaseChange T := by
  sorry

/-! ## Fppf H¹ and the two torsion lemmas -/

/-- An explicit coefficient-indexed interface for fppf `H¹`.

The cohomology groups are represented by the existing additive-group category;
the missing construction of fppf torsor cohomology is isolated in this
interface rather than replaced by a parallel group definition. -/
structure FppfH1Theory {G : Type v} (coefficient : G) where
  H1 : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u}

abbrev FppfH1 {G : Type v} {coefficient : G} (H : FppfH1Theory coefficient)
    (X : Scheme.{u}) :=
  H.H1.obj (op X)

def fppfH1Restriction {G : Type v} {coefficient : G}
    (H : FppfH1Theory coefficient)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : FppfH1 H Y → FppfH1 H X :=
  H.H1.map f.op

def IsTorsionAddCommGroup (G : AddCommGrpCat.{u}) : Prop :=
  ∀ x : G, ∃ n : ℕ, 0 < n ∧ n • x = 0

def IsNonTorsionAddCommGroup (G : AddCommGrpCat.{u}) : Prop :=
  ∃ x : G, ∀ n : ℕ, 0 < n → n • x ≠ 0

def IsZeroAddCommGroup (G : AddCommGrpCat.{u}) : Prop :=
  ∀ x : G, x = 0

/-- The function-field morphism `Spec(K) ⟶ W`. -/
noncomputable def genericPointFunctionFieldMap (W : Scheme.{u})
    [IsIntegral W] : Spec W.functionField ⟶ W :=
  W.fromSpecStalk (genericPoint W)

/-- The source's two-dimensional regular surface hypothesis. -/
structure TwoDimensionalRegularScheme (W : Scheme.{u}) where
  dimension_two : Prop
  regular : Prop

/-- The no-dimension hypothesis used in the generalization. -/
structure RegularIntegralScheme (W : Scheme.{u}) where
  regular : Prop

/-- Injectivity of torsor classes on a two-dimensional regular integral
Noetherian scheme after restriction to its function field. -/
theorem torsor_h1_restriction_injective
    (W : Scheme.{u}) [IsIntegral W] [IsNoetherian W]
    (hW : TwoDimensionalRegularScheme W)
    (G : AbelianSchemeData W) (H : FppfH1Theory G) :
    Function.Injective (fppfH1Restriction H (genericPointFunctionFieldMap W)) := by
  sorry

/-! ## The generalization in the remark -/

/-- The section restriction data of a torsor. -/
structure FppfTorsorSectionData (W : Scheme.{u})
    {G : Type v} (coefficient : G) where
  sections : Scheme.{u} → Type u
  restrict : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → sections Y → sections X
  restrict_id : ∀ (X : Scheme.{u}) (s : sections X), restrict (𝟙 X) s = s
  restrict_comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : sections Z), restrict (f ≫ g) s = restrict f (restrict g s)

/-- The section-extension assertion for every torsor. -/
theorem torsor_sections_bijective_to_function_field
    (W : Scheme.{u}) [IsIntegral W] [IsNoetherian W]
    (hW : RegularIntegralScheme W)
    (G : Type v) (coefficient : G) (P : FppfTorsorSectionData W coefficient) :
    Function.Bijective (P.restrict (genericPointFunctionFieldMap W)) := by
  sorry

/-- The general regular integral version of the H¹ injectivity statement. -/
theorem torsor_h1_restriction_injective_of_sections
    (W : Scheme.{u}) [IsIntegral W] [IsNoetherian W]
    (hW : RegularIntegralScheme W)
    (G : AbelianSchemeData W) (H : FppfH1Theory G)
    (hsections : ∀ P : FppfTorsorSectionData W G,
      Function.Bijective (P.restrict (genericPointFunctionFieldMap W))) :
    Function.Injective (fppfH1Restriction H (genericPointFunctionFieldMap W)) := by
  sorry

/-- The weaker factoriality hypothesis mentioned in the remark. -/
structure SmoothSchemesLocallyFactorial (W : Scheme.{u}) where
  everySmoothSchemeIsLocallyFactorial : Prop

theorem torsor_h1_restriction_injective_of_local_factoriality
    (W : Scheme.{u}) [IsIntegral W] [IsNoetherian W]
    (hW : SmoothSchemesLocallyFactorial W)
    (G : AbelianSchemeData W) (H : FppfH1Theory G) :
    Function.Injective (fppfH1Restriction H (genericPointFunctionFieldMap W)) := by
  sorry

/-- The torsor group on the regular projective surface in the example is
torsion, by the two preceding H¹ interfaces. -/
theorem example_h1_totalSpace_is_torsion
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A)
    [IsIntegral X.totalSpace] [IsNoetherian X.totalSpace]
    (hW : TwoDimensionalRegularScheme X.totalSpace)
    (hdimension : hW.dimension_two) (hregular : hW.regular)
    (hprojective : X.projective) (hproper : X.proper) (hflat : X.flat)
    (hA : IsAbelianScheme A) :
    IsTorsionAddCommGroup (FppfH1 H X.totalSpace) := by
  sorry

/-- Smooth commutative group algebraic-space data over a field. -/
structure SmoothCommutativeGroupAlgebraicSpace (K : Type u) [Field K] where
  space : AlgebraicSpace (Spec (CommRingCat.of K))
  smooth : Prop
  commutativeGroup : Prop

/-! The field-valued H¹ torsion argument. -/
theorem fppf_h1_torsion_over_field
    (K : Type u) [Field K]
    (G : SmoothCommutativeGroupAlgebraicSpace K)
    (H : FppfH1Theory G) :
    IsTorsionAddCommGroup (FppfH1 H (Spec (CommRingCat.of K))) := by
  sorry

/-! ## The nontorsion torsor on the nodal special fibre -/

/-- Normalization data at the node of the rational loop. -/
structure NodalCurveNormalization (C : Scheme.{u}) where
  normalization : Scheme.{u}
  map : normalization ⟶ C
  node : C
  firstPoint : normalization
  secondPoint : normalization
  firstPoint_maps_to_node : map firstPoint = node
  secondPoint_maps_to_node : map secondPoint = node
  points_distinct : firstPoint ≠ secondPoint
  rationalLoop : Prop

/-- The gluing identification of the two fibres at the node. -/
structure GluedTorsorData {k : Type u} [Field k]
    (C : Scheme.{u}) (A₀ : AbelianVarietyData k) where
  normalization : NodalCurveNormalization C
  gluingPoint : A₀.pointType
  identification : A₀.pointType → A₀.pointType
  identification_is_translation : identification = translationBy A₀ gluingPoint

def gluingData {k : Type u} [Field k]
    (C : Scheme.{u}) (A₀ : AbelianVarietyData k)
    (N : NodalCurveNormalization C) (a₀ : A₀.pointType) :
    GluedTorsorData C A₀ :=
  { normalization := N
    gluingPoint := a₀
    identification := translationBy A₀ a₀
    identification_is_translation := rfl }

theorem glued_torsor_class_is_nontorsion
    {k : Type u} [Field k]
    (C : Scheme.{u}) (A₀ : AbelianVarietyData k)
    (H : FppfH1Theory A₀)
    (D : GluedTorsorData C A₀)
    (hloop : D.normalization.rationalLoop)
    (ha₀ : IsNontorsionPoint A₀ D.gluingPoint) :
    ∃ p : FppfH1 H C,
      ∀ n : ℕ, 0 < n → n • p ≠ 0 := by
  sorry

theorem h1_specialFiber_is_nontorsion
    {k : Type u} [Field k]
    (C : Scheme.{u}) (A₀ : AbelianVarietyData k)
    (H : FppfH1Theory A₀)
    (geometry : NodalCurveData C)
    (N : NodalCurveNormalization C)
    (a₀ : A₀.pointType)
    (hcurve : geometry.isCurve)
    (hcomponents : geometry.componentsSmoothIrreducible)
    (hnodal : geometry.isNodal)
    (hloop : geometry.dualGraphHasLoopOfRationalCurves)
    (hnormalizationLoop : N.rationalLoop)
    (ha₀ : IsNontorsionPoint A₀ a₀) :
    IsNonTorsionAddCommGroup (FppfH1 H C) := by
  sorry

/-! ## Deformation obstruction and the formal inverse limit -/

/-- A vector bundle together with the property needed in the obstruction
group. -/
structure VectorBundleData (C : Scheme.{u}) where
  fiber : Type u
  isVectorBundle : Prop

structure CurveObstructionTheory (C : Scheme.{u}) where
  H2 : VectorBundleData C → AddCommGrpCat.{u}

/-- Dimension-one data used for the vanishing of `H²` on the special fibre. -/
structure CurveDimensionData (C : Scheme.{u}) where
  dimension_one : Prop

theorem h2_vector_bundle_vanishes_on_curve
    (C : Scheme.{u}) (hC : CurveDimensionData C)
    (hdimension : hC.dimension_one)
    (Θ : CurveObstructionTheory C) (ω : VectorBundleData C) :
    IsZeroAddCommGroup (Θ.H2 ω) := by
  sorry

def h1TowerLevel {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A) (n : ℕ) : AddCommGrpCat.{u} :=
  FppfH1 H (familyThickening X.totalSpace X.toBase n)

def h1TowerRestriction {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A) (n : ℕ) :
    h1TowerLevel X A H (n + 1) → h1TowerLevel X A H n :=
  fppfH1Restriction H (familyThickeningMap X.totalSpace X.toBase n)

theorem h1TowerRestriction_surjective_of_h2_vanishing
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A) (n : ℕ)
    (Θ : CurveObstructionTheory (CurveFamilySpecialFiber X))
    (ω : VectorBundleData (CurveFamilySpecialFiber X))
    (hω : IsZeroAddCommGroup (Θ.H2 ω)) :
    Function.Surjective (h1TowerRestriction X A H n) := by
  sorry

/-- The compatible inverse limit of the `H¹(X_n,A)` groups. -/
def compatibleH1Limit {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A) : Type u :=
  {x : ∀ n : ℕ, h1TowerLevel X A H n //
    ∀ n : ℕ, h1TowerRestriction X A H n (x (n + 1)) = x n}

def globalH1ToLevel {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A) (n : ℕ) :
    FppfH1 H X.totalSpace → h1TowerLevel X A H n :=
  fppfH1Restriction H (familyThickeningToTotal X.totalSpace X.toBase n)

/-- The canonical restriction map to the compatible formal `H¹` limit. -/
def globalH1ToCompatibleLimit {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A) :
    FppfH1 H X.totalSpace → compatibleH1Limit X A H :=
  fun x =>
    ⟨fun n => globalH1ToLevel X A H n x, by
      intro n
      sorry⟩

theorem globalH1ToCompatibleLimit_not_surjective
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A)
    (hglobal : IsTorsionAddCommGroup (FppfH1 H X.totalSpace))
    (hspecial : IsNonTorsionAddCommGroup
      (FppfH1 H (CurveFamilySpecialFiber X)))
    (hsurjective : ∀ n : ℕ, Function.Surjective (h1TowerRestriction X A H n)) :
    ¬ Function.Surjective (globalH1ToCompatibleLimit X A H) := by
  sorry

/-! ## The Artin-axiom obstruction -/

/-- The base fibre of the Hom-stack, i.e. the groupoid `X(S)`. -/
def homStackBaseFiber {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k)) : Cat :=
  Fiber (exampleHomStack X A).value (CategoryTheory.Over.mk
    (𝟙 (powerSeriesBase k)))

/-- A category placeholder for the compatible formal objects. -/
def formalLimitCategory {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A) : Cat :=
  Cat.of (Discrete (compatibleH1Limit X A H))

/-- The source/target presentation of the formal completion map. -/
structure FormalCompletionData (source target : Cat) where
  map : source ⥤ target
  targetIsTheInverseLimit : Prop
  mapIsTheCanonicalRestriction : Prop

theorem homStackFormalCompletion_exists
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A) :
    Nonempty (FormalCompletionData (homStackBaseFiber X A)
      (formalLimitCategory X A H)) := by
  sorry

noncomputable def homStackFormalCompletion
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A) :
    FormalCompletionData (homStackBaseFiber X A) (formalLimitCategory X A H) :=
  Classical.choice (homStackFormalCompletion_exists X A H)

def canonicalHomStackCompletionMap
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A) :
    homStackBaseFiber X A ⥤ formalLimitCategory X A H :=
  (homStackFormalCompletion X A H).map

theorem lemma_not_essentially_surjective
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A)
    (hnot : ¬ Function.Surjective (globalH1ToCompatibleLimit X A H)) :
    ¬ (canonicalHomStackCompletionMap X A H).EssSurj := by
  sorry

theorem lemma_not_essentially_surjective_from_the_two_steps
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A)
    (hglobal : IsTorsionAddCommGroup (FppfH1 H X.totalSpace))
    (hspecial : IsNonTorsionAddCommGroup
      (FppfH1 H (CurveFamilySpecialFiber X)))
    (hsurjective : ∀ n : ℕ, Function.Surjective (h1TowerRestriction X A H n)) :
    ¬ (canonicalHomStackCompletionMap X A H).EssSurj := by
  apply lemma_not_essentially_surjective X A H
  exact globalH1ToCompatibleLimit_not_surjective X A H
    hglobal hspecial hsurjective

/-- The main proposition: this Hom-stack is not algebraic. -/
theorem proposition_nonalghomstack
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A)
    (hfield : X.fieldData.notAlgebraicClosureOfFiniteField)
    (hnot : ¬ (canonicalHomStackCompletionMap X A H).EssSurj) :
    ¬ IsAlgebraicRelativeStack (exampleHomStack X A) := by
  sorry

/-! ## The non-effectivity and separated-target remarks -/

theorem example_homStack_formal_objects_not_effective
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A)
    (hnot : ¬ Function.Surjective (globalH1ToCompatibleLimit X A H)) :
    ¬ (canonicalHomStackCompletionMap X A H).EssSurj :=
  lemma_not_essentially_surjective X A H hnot

theorem example_quotient_target_is_separated
    {k : Type u} [Field k]
      (A₀ : AbelianVarietyData k) :
    IsSeparatedRelativeStack
      (quotientStack (constantAbelianScheme A₀ (powerSeriesBase k)
        (baseToClosedMap k))) := by
  exact quotientStack_is_separated _

theorem separated_target_counterexample
    {k : Type u} [Field k]
    (X : CurveFamilyOverPowerSeries k)
    (A : AbelianSchemeData (powerSeriesBase k))
    (H : FppfH1Theory A)
    (hfield : X.fieldData.notAlgebraicClosureOfFiniteField)
    (hnot : ¬ (canonicalHomStackCompletionMap X A H).EssSurj)
    (hseparated : IsSeparatedRelativeStack (quotientStack A)) :
    IsSeparatedRelativeStack (quotientStack A) ∧
      ¬ IsAlgebraicRelativeStack (exampleHomStack X A) := by
  exact ⟨hseparated, proposition_nonalghomstack X A H hfield hnot⟩

end Formalization.Books.Examples.Unit74
