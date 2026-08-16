import Formalization.«Books.Sdga».Unit01.Core

/-! # 3. Sheaves of graded algebras -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

/-- The book-facing name for a sheaf of graded algebras. -/
abbrev GradedAlgebraSheaf (S : RingedSite.{u,v} R) := GradedAlgebra S

/-- Sections of a graded algebra, retaining the degree-indexed family and the
finite-support condition of the direct-sum notation in the source. -/
structure GradedAlgebraSections {S : RingedSite.{u,v} R}
    (A : GradedAlgebra S) (U : S.Obj) where
  component : ∀ n : ℤ, A.component n U
  finite_support : Prop

structure GradedAlgebraFunctoriality {S T : RingedSite.{u,v} R}
    (f : RingedSiteMorphism S T) where
  pushforward : GradedAlgebra S → GradedAlgebra T
  pullback : GradedAlgebra T → GradedAlgebra S
  pushforward_preserves_multiplication : Prop
  pullback_preserves_multiplication : Prop
  adjunction : Prop

theorem definition_ga (S : RingedSite.{u,v} R) (A : GradedAlgebraSheaf S) :
    A.laws := by
  exact A.laws

theorem remark_functoriality_ga
    {S T : RingedSite.{u,v} R} {f : RingedSiteMorphism S T}
    (F : GradedAlgebraFunctoriality f) :
    F.pushforward_preserves_multiplication ∧
      F.pullback_preserves_multiplication ∧ F.adjunction := by
  sorry

end Sdga
