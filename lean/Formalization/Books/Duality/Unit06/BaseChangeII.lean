import Formalization.Books.Duality.Unit05.BaseChangeComposition

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def AffineBaseChangeComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    (_a : RightAdjointData f) (α β : DerivedObject X) : Prop :=
  Isomorphic α β

theorem remark_check_over_affines {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (α β : DerivedObject X) (hαβ : Prop) :
    AffineBaseChangeComparison a α β := by
  sorry

def MoreBaseChangeIsomorphism {S : Type u} [Category.{u, u} S]
    [CategoryTheory.Limits.HasPullbacks S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] {square : CartesianSquare S}
    {a : RightAdjointData square.f} {a' : RightAdjointData square.f'}
    (b : BaseChangeData square a a') : Prop :=
  IsIsoBaseChange b

theorem lemma_more_base_change {S : Type u} [Category.{u, u} S]
    [CategoryTheory.Limits.HasPullbacks S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] (square : CartesianSquare S)
    (a : RightAdjointData square.f) (a' : RightAdjointData square.f')
    (b : BaseChangeData square a a') (hTor : Prop) :
    MoreBaseChangeIsomorphism b := by
  sorry

def EquationIso {S : Type u} [Category.{u, u} S]
    [CategoryTheory.Limits.HasPullbacks S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] {square : CartesianSquare S}
    {a : RightAdjointData square.f} {a' : RightAdjointData square.f'}
    (b : BaseChangeData square a a') : Prop :=
  IsIsoBaseChange b

def equation_iso {S : Type u} [Category.{u, u} S]
    [CategoryTheory.Limits.HasPullbacks S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] {square : CartesianSquare S}
    {a : RightAdjointData square.f} {a' : RightAdjointData square.f'}
    (b : BaseChangeData square a a') : Prop :=
  EquationIso b

end

end Formalization.Books.Duality.Unit01
