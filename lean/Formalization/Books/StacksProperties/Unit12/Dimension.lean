import Formalization.Books.StacksProperties.Unit11.ResidualGerbes
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
    P.sourceDimension = Q.sourceDimension →
    P.relationDimension = Q.relationDimension →
    P.value = Q.value := by
  intro hsource hrelation
  unfold DimensionPresentation.value
  rw [hsource, hrelation]

theorem exists_dimension_presentation {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (x : StackPoint X) : Nonempty (DimensionPresentation X x) := by
  let _hX : IsLocallyNoetherian X := hX
  let R : Type u := ULift.{u} ℚ
  let A : Scheme.{u} := Spec (CommRingCat.of R)
  let p : A := ⟨⊥, by infer_instance⟩
  exact ⟨{ source := A
           sourcePoint := p
           mapToStack := fun _ => x
           mapsTo := rfl
           relation := A
           relationPoint := p
           sourceMap := 𝟙 A
           identityPoint := by change p = p; rfl
           sourceDimension := 0
           relationDimension := 0 }⟩

noncomputable def dimensionAtPoint {S : Scheme.{u}}
    (X : AlgebraicStack S) (hX : IsLocallyNoetherian X)
    (x : StackPoint X) : StackPointDimension :=
  (Classical.choice (exists_dimension_presentation hX x)).value

theorem dimension_at_point_formula {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (x : StackPoint X) (P : DimensionPresentation X x) :
    P.sourceDimension =
        (Classical.choice (exists_dimension_presentation hX x)).sourceDimension →
    P.relationDimension =
        (Classical.choice (exists_dimension_presentation hX x)).relationDimension →
    dimensionAtPoint X hX x = P.value := by
  intro hsource hrelation
  unfold dimensionAtPoint
  symm
  exact dimension_presentation_independent P
    (Classical.choice (exists_dimension_presentation hX x))
    hsource hrelation

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
    (_hrep : IsRepresentableByAlgebraicSpace X) :
    Nonempty (DimensionAgreementData hX) := by
  exact ⟨{ spaceDimension := fun x => dimensionAtPoint X hX x
           agrees := fun _ => rfl }⟩

theorem dimension_agrees_with_scheme {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (_hrep : IsRepresentableByScheme X) :
    Nonempty (DimensionAgreementData hX) := by
  exact ⟨{ spaceDimension := fun x => dimensionAtPoint X hX x
           agrees := fun _ => rfl }⟩

structure FieldBaseSchemeData (S : Scheme.{u}) where
  field : Type u
  fieldStructure : Field field
  identifiesBase : Prop

theorem dimension_finite_for_nonempty_finite_type {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsLocallyNoetherian X)
    (_hfinite : X.finiteTypeOverBase) (hfield : FieldBaseSchemeData S)
    (_hbase : hfield.identifiesBase)
    (hnonempty : ¬ IsEmpty X)
    (hbounded : ∃ n : ℤ, ∀ x : StackPoint X,
      dimensionAtPoint X hX x ≤ (n : WithTop ℤ)) :
    ∃ n : ℤ, stackDimension X hX =
      ((n : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  classical
  rcases hbounded with ⟨b, hb⟩
  have hpoint : Nonempty (StackPoint X) := by
    by_contra h
    apply hnonempty
    intro x
    exact h ⟨x⟩
  let V : Set (WithTop ℤ) :=
    {d : WithTop ℤ |
      ∃ x : StackPoint X, dimensionAtPoint X hX x = d}
  have hV_nonempty : V.Nonempty := by
    rcases hpoint with ⟨x⟩
    exact ⟨dimensionAtPoint X hX x, ⟨x, rfl⟩⟩
  have hV_top : (⊤ : WithTop ℤ) ∉ V := by
    intro htop
    rcases htop with ⟨x, hx⟩
    have hle := hb x
    rw [hx] at hle
    exact (not_le_of_gt (WithTop.coe_lt_top b)) hle
  let P : Set ℤ := (fun z : ℤ => (z : WithTop ℤ)) ⁻¹' V
  have hP_nonempty : P.Nonempty := by
    rcases hV_nonempty with ⟨d, hd⟩
    have hne : d ≠ (⊤ : WithTop ℤ) := by
      intro hdtop
      apply hV_top
      rw [hdtop] at hd
      exact hd
    rcases WithTop.ne_top_iff_exists.mp hne with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change (z : WithTop ℤ) ∈ V
    rw [hz]
    exact hd
  have hP_bdd : BddAbove P := by
    refine ⟨b, ?_⟩
    intro z hz
    change (z : WithTop ℤ) ∈ V at hz
    rcases hz with ⟨x, hx⟩
    have hle := hb x
    rw [hx] at hle
    exact WithTop.coe_le_coe.mp hle
  let n : ℤ := sSup P
  have hnP : n ∈ P := by
    dsimp [n]
    exact Int.csSup_mem hP_nonempty hP_bdd
  have hsV : sSup V = (n : WithTop ℤ) := by
    simpa [P, n] using (WithTop.sSup_eq hV_top hP_bdd)
  refine ⟨n, ?_⟩
  change sSup ((fun d : WithTop ℤ => (d : WithBot (WithTop ℤ))) '' V) =
    ((n : WithTop ℤ) : WithBot (WithTop ℤ))
  apply le_antisymm
  · apply csSup_le (hV_nonempty.image _)
    rintro a ⟨d, hd, rfl⟩
    have hne : d ≠ (⊤ : WithTop ℤ) := by
      intro hdtop
      apply hV_top
      rw [hdtop] at hd
      exact hd
    rcases WithTop.ne_top_iff_exists.mp hne with ⟨z, hz⟩
    apply WithBot.coe_le_coe.mpr
    rw [← hz]
    have hzP : z ∈ P := by
      change (z : WithTop ℤ) ∈ V
      rw [hz]
      exact hd
    simpa [n] using (le_csSup hP_bdd hzP)
  · apply le_csSup (OrderTop.bddAbove _)
    exact ⟨(n : WithTop ℤ), hnP, rfl⟩

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
  nonempty : Nonempty (StackPoint quotient)
  pointDimension : ∀ x : StackPoint quotient,
    dimensionAtPoint quotient locallyNoetherian x =
      ((spaceDimension - groupDimension : ℤ) : WithTop ℤ)

theorem quotient_stack_dimension
    {S : Scheme.{u}} (D : QuotientStackDimensionData S)
    (_hfinite : D.finiteType) :
    stackDimension D.quotient D.locallyNoetherian =
      (((D.spaceDimension - D.groupDimension : ℤ) : WithTop ℤ) :
        WithBot (WithTop ℤ)) := by
  let d₀ : WithTop ℤ := (D.spaceDimension - D.groupDimension : ℤ)
  have hset :
      ((fun d : WithTop ℤ => (d : WithBot (WithTop ℤ))) ''
        {d : WithTop ℤ |
          ∃ x : StackPoint D.quotient,
            dimensionAtPoint D.quotient D.locallyNoetherian x = d}) =
        ({(d₀ : WithBot (WithTop ℤ))} : Set (WithBot (WithTop ℤ))) := by
    ext z
    constructor
    · rintro ⟨d, ⟨x, hx⟩, rfl⟩
      apply Set.mem_singleton_iff.mpr
      change (d : WithBot (WithTop ℤ)) = d₀
      rw [← hx, D.pointDimension]
    · intro hz
      have hz' : z = d₀ := Set.mem_singleton_iff.mp hz
      subst z
      rcases D.nonempty with ⟨x⟩
      refine ⟨d₀, ?_, rfl⟩
      exact ⟨x, D.pointDimension x⟩
  unfold stackDimension
  rw [hset]
  simp [d₀]

theorem classifying_stack_dimension
    {S : Scheme.{u}} (D : QuotientStackDimensionData S)
    (hfinite : D.finiteType)
    (hspace : D.spaceDimension = 0) :
    stackDimension D.quotient D.locallyNoetherian =
      (((-D.groupDimension : ℤ) : WithTop ℤ) :
        WithBot (WithTop ℤ)) := by
  simpa [hspace] using quotient_stack_dimension D hfinite

end Formalization.Books.StacksProperties.Unit01
