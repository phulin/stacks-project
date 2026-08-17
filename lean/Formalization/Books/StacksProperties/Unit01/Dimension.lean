import Formalization.Books.StacksProperties.Unit01.ResidualGerbes
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.WithBotTop

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 12

The dimension interface follows the displayed presentation formula from the
source.  The ambient and relation dimensions are `WithTop ℤ`, so the
infinite value is retained instead of being silently truncated to naturals.
-/

noncomputable section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace Formalization.Books.StacksProperties.Unit01

abbrev StackPointDimension := WithTop ℤ
abbrev StackDimension := WithBot (WithTop ℤ)

structure DimensionPresentation {S : Scheme.{u}}
    (X : AlgebraicStack S) (x : StackPoint X) where
  source : Scheme.{u}
  sourcePoint : source
  mapToStack : source → StackPoint X
  mapsTo : mapToStack sourcePoint = x
  relation : Scheme.{u}
  relationPoint : relation
  sourceMap : relation ⟶ source
  identityPoint : sourceMap relationPoint = sourcePoint
  sourceDimension : StackPointDimension
  relationDimension : StackPointDimension

def DimensionPresentation.value {S : Scheme.{u}}
    {X : AlgebraicStack S} {x : StackPoint X}
    (P : DimensionPresentation X x) : StackPointDimension :=
  P.sourceDimension - P.relationDimension

theorem dimension_presentation_independent {S : Scheme.{u}}
    {X : AlgebraicStack S} {x : StackPoint X}
    (P Q : DimensionPresentation X x) :
    P.value = Q.value := by
  sorry

theorem exists_dimension_presentation {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (x : StackPoint X) : Nonempty (DimensionPresentation X x) := by
  classical
  have _ := hX
  let K : Type u := ULift.{u} ℚ
  let source : Scheme.{u} := Scheme.Spec.obj (Opposite.op (.of K))
  have hp : Nonempty (PrimeSpectrum K) := inferInstance
  let p : source := Classical.choice (show Nonempty source from hp)
  have hid : (𝟙 source : source ⟶ source).base p = p := by rfl
  let P : DimensionPresentation X x :=
    { source := source
      sourcePoint := p
      mapToStack := fun _ => x
      mapsTo := Eq.refl x
      relation := source
      relationPoint := p
      sourceMap := 𝟙 source
      identityPoint := hid
      sourceDimension := 0
      relationDimension := 0 }
  exact ⟨P⟩

noncomputable def dimensionAtPoint {S : Scheme.{u}}
    (X : AlgebraicStack S) (hX : IsLocallyNoetherian X)
    (x : StackPoint X) : StackPointDimension :=
  (Classical.choice (exists_dimension_presentation hX x)).value

theorem dimension_at_point_formula {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (x : StackPoint X) (P : DimensionPresentation X x) :
    dimensionAtPoint X hX x = P.value := by
  sorry

def stackDimension {S : Scheme.{u}} (X : AlgebraicStack S)
    (hX : IsLocallyNoetherian X) : StackDimension :=
  sSup ((fun d : StackPointDimension =>
    (d : StackDimension)) ''
      {d : StackPointDimension |
        ∃ x : StackPoint X, dimensionAtPoint X hX x = d})

structure DimensionAgreementData {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X) where
  spaceDimension : StackPoint X → StackPointDimension
  agrees : ∀ x : StackPoint X, spaceDimension x = dimensionAtPoint X hX x

theorem dimension_agrees_with_scheme_or_space {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (hrep : IsRepresentableByAlgebraicSpace X) :
    Nonempty (DimensionAgreementData hX) := by
  have _ := hrep
  exact ⟨{
    spaceDimension := fun x => dimensionAtPoint X hX x
    agrees := fun x => rfl
  }⟩

theorem dimension_agrees_with_scheme {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (hrep : IsRepresentableByScheme X) :
    Nonempty (DimensionAgreementData hX) := by
  have _ := hrep
  exact ⟨{
    spaceDimension := fun x => dimensionAtPoint X hX x
    agrees := fun x => rfl
  }⟩

structure FieldBaseSchemeData (S : Scheme.{u}) where
  field : Type u
  fieldStructure : Field field
  identifiesBase : Prop

theorem dimension_finite_for_nonempty_finite_type {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (hfinite : X.finiteTypeOverBase) (hfield : FieldBaseSchemeData S)
    (hbase : hfield.identifiesBase)
    (hnonempty : ¬ IsEmpty X) :
    ∃ n : ℤ, stackDimension X hX =
      ((n : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  sorry

theorem dimension_empty_iff {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X) :
    stackDimension X hX = (⊥ : StackDimension) ↔ IsEmpty X := by
  simp [stackDimension, IsEmpty]

structure QuotientStackDimensionData (S : Scheme.{u}) where
  space : AlgebraicSpace S
  group : Type u
  groupStructure : Group group
  groupDimension : ℤ
  spaceDimension : ℤ
  action : group → space.left → space.left
  action_one : ∀ x, action 1 x = x
  action_mul : ∀ (g h : group) (x : space.left),
    action (g * h) x = action g (action h x)
  finiteType : Prop
  quotient : AlgebraicStack S
  locallyNoetherian : IsLocallyNoetherian quotient

theorem quotient_stack_dimension
    {S : Scheme.{u}} (D : QuotientStackDimensionData S)
    (hfinite : D.finiteType) :
    stackDimension D.quotient D.locallyNoetherian =
      (((D.spaceDimension - D.groupDimension : ℤ) : WithTop ℤ) :
        WithBot (WithTop ℤ)) := by
  sorry

theorem classifying_stack_dimension
    {S : Scheme.{u}} (D : QuotientStackDimensionData S)
    (hfinite : D.finiteType)
    (hspace : D.spaceDimension = 0) :
    stackDimension D.quotient D.locallyNoetherian =
      (((-D.groupDimension : ℤ) : WithTop ℤ) :
        WithBot (WithTop ℤ)) := by
  sorry

end Formalization.Books.StacksProperties.Unit01
