import Formalization.Books.Duality.Unit01.UpperShriekBaseChange

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure FiniteTypeSeparatedOver (S : Scheme.{u}) where
  scheme : Scheme.{u}
  structuralMap : scheme ⟶ S
  finiteTypeSeparated : Prop

def DualObject {X : Scheme.{u}} (ω K : DerivedObject X) : DerivedObject X :=
  InternalHom K ω

structure ProperDualityData {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) where
  sourceDualizing : DerivedObject Y
  targetDualizing : DerivedObject X
  targetIsDualizing : IsDualizingComplexOn targetDualizing
  shriekFormula : ∀ K : DerivedObject Y,
    Isomorphic (a.rightAdjoint.obj K) (DualObject targetDualizing ((LPullback f).obj (DualObject sourceDualizing K)))

structure DualityTheoryData (S : Scheme.{u}) where
  pseudoFunctor : UpperShriekPseudoFunctorData
  properDuality : Prop
  closedImmersionFormula : Prop
  finiteFormula : Prop
  CartierFormula : Prop
  regularImmersionFormula : Prop
  smoothProperFormula : Prop

theorem lemma_duality_theory (S : Scheme.{u}) : Nonempty (DualityTheoryData S) := by
  sorry

theorem lemma_duality_theory_proper {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (d : ProperDualityData f a) :
    ∀ K : DerivedObject X, Isomorphic
      ((RPushforward f).obj (InternalHom K d.targetDualizing))
      (InternalHom ((RPushforward f).obj K) d.sourceDualizing) := by
  sorry

theorem lemma_duality_theory_involution {X : Scheme.{u}} (ω K : DerivedObject X)
    (hdualizing : IsDualizingComplexOn ω) :
    Isomorphic K (DualObject ω (DualObject ω K)) := by
  sorry

end

end Formalization.Books.Duality.Unit01
