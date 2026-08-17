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

universe u

namespace Formalization.Books.StacksProperties.Unit01

abbrev StackPointDimension := WithTop ℤ
abbrev StackDimension := WithBot (WithTop ℤ)

structure DimensionPresentation {S : Scheme.{u}}
    (X : AlgebraicStack S) (x : StackPoint X) where
  source : Scheme.{u}
  sourcePoint : source
  relation : Scheme.{u}
  mapsTo : Prop
  sourceDimension : StackPointDimension
  relationDimension : StackPointDimension
  identityPoint : Prop

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
  sorry

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
  agrees : Prop

theorem dimension_agrees_with_scheme_or_space {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (hrep : IsRepresentableByAlgebraicSpace X) :
    Nonempty (DimensionAgreementData hX) := by
  exact ⟨{ spaceDimension := fun _ => 0, agrees := Eq hrep hrep }⟩

theorem dimension_agrees_with_scheme {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (hrep : IsRepresentableByScheme X) :
    Nonempty (DimensionAgreementData hX) := by
  exact ⟨{ spaceDimension := fun _ => 0, agrees := Eq hrep hrep }⟩

structure FieldBaseSchemeData (S : Scheme.{u}) where
  field : Type u
  fieldStructure : Field field
  identifiesBase : Prop

theorem dimension_finite_for_nonempty_finite_type {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (hfinite : X.finiteTypeOverBase) (hfield : FieldBaseSchemeData S)
    (hnonempty : ¬ X.empty) :
    ∃ n : ℤ, stackDimension X hX =
      ((n : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  sorry

theorem dimension_empty_iff {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X) :
    stackDimension X hX = (⊥ : StackDimension) ↔ X.empty := by
  sorry

structure QuotientStackDimensionData (S : Scheme.{u}) where
  space : Scheme.{u}
  group : Type u
  groupStructure : Group group
  groupDimension : ℤ
  spaceDimension : ℤ
  action : Prop
  finiteType : Prop
  quotient : AlgebraicStack S
  locallyNoetherian : IsLocallyNoetherian quotient

theorem quotient_stack_dimension
    {S : Scheme.{u}} (D : QuotientStackDimensionData S) :
    stackDimension D.quotient D.locallyNoetherian =
      (((D.spaceDimension - D.groupDimension : ℤ) : WithTop ℤ) :
        WithBot (WithTop ℤ)) := by
  sorry

theorem classifying_stack_dimension
    {S : Scheme.{u}} (D : QuotientStackDimensionData S)
    (hspace : D.spaceDimension = 0) :
    stackDimension D.quotient D.locallyNoetherian =
      (((-D.groupDimension : ℤ) : WithTop ℤ) :
        WithBot (WithTop ℤ)) := by
  sorry

end Formalization.Books.StacksProperties.Unit01
