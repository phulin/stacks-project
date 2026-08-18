import Formalization.Books.Duality.Unit01.RightAdjointPushforward

/-!
# Restriction to opens

Open restriction is expressed by the Cartesian-square and base-change data
from `Core`; the hypotheses that the lower horizontal map is flat or Tor
independent are retained in the theorem interfaces.
-/

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def equation_base_change (square : CartesianSquare Scheme) : Prop :=
  IsPullback square.g' square.f' square.f square.g

def RestrictionComparison {S : Type u} [CategoryTheory.Category.{u, u} S]
    [CategoryTheory.Limits.HasPullbacks S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] {square : CartesianSquare S}
    {a : RightAdjointData square.f} {a' : RightAdjointData square.f'}
    (b : BaseChangeData square a a') (K : DerivedObject square.Y) :=
  BaseChangeMap b K

def equation_sheafy {S : Type u} [CategoryTheory.Category.{u, u} S]
    [CategoryTheory.Limits.HasPullbacks S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] {square : CartesianSquare S}
    {a : RightAdjointData square.f} {a' : RightAdjointData square.f'}
    (b : BaseChangeData square a a') (K : DerivedObject square.Y) :=
  RestrictionComparison b K

def SupportedAwayFrom {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : RightAdjointData f)
    (T : SchemeDerivedContext.supportLabel Y)
    (U : SchemeDerivedContext.supportLabel X) : Prop :=
  ∀ Q : DerivedObject Y, IsSupportedOn T Q → IsSupportedOn U (a.rightAdjoint.obj Q)

def SheafyOnAllObjects {S : Type u} [CategoryTheory.Category.{u, u} S]
    [CategoryTheory.Limits.HasPullbacks S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] : Prop :=
  ∀ (square : CartesianSquare S) (a : RightAdjointData square.f)
    (a' : RightAdjointData square.f') (b : BaseChangeData square a a')
    (K : DerivedObject square.Y), IsIso (RestrictionComparison b K)

theorem lemma_flat_precompose_pus {S : Type u} [CategoryTheory.Category.{u, u} S]
    [CategoryTheory.Limits.HasPullbacks S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] (square : CartesianSquare S)
    (a : RightAdjointData square.f) (a' : RightAdjointData square.f')
    (b : BaseChangeData square a a')
    (hflat : Prop) (hTor : Prop) :
    IsIsoBaseChange b := by
  sorry

theorem example_not_supported_on_inverse_image {S : Type u}
    [CategoryTheory.Category.{u, u} S] [CategoryTheory.Limits.HasPullbacks S]
    [SchemeDerivedContext S] [SchemeDerivedOperations S] :
    ∃ (square : CartesianSquare S) (a : RightAdjointData square.f)
      (a' : RightAdjointData square.f') (b : BaseChangeData square a a'),
      ¬ IsIsoBaseChange b := by
  sorry

theorem lemma_when_sheafy {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (T : SchemeDerivedContext.supportLabel Y)
    (U : SchemeDerivedContext.supportLabel X) :
    SupportedAwayFrom a T U ↔
      ∀ Q : DerivedObject Y, IsSupportedOn T Q →
        IsSupportedOn U (a.rightAdjoint.obj Q) := by
  sorry

theorem lemma_proper_noetherian {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hproper : IsProperMorphism f)
    (hX : IsNoetherianScheme X) (hY : IsNoetherianScheme Y) :
    PreservesBoundedBelow a := by
  sorry

end

end Formalization.Books.Duality.Unit01
