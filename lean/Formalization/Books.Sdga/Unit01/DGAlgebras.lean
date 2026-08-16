import Formalization.«Books.Sdga».Unit01.Core

/-! # 12. Sheaves of differential graded algebras -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

abbrev DGAlgebraSheaf (S : RingedSite.{u,v} R) := DGAlgebra S

structure DGAlgebraFunctoriality {S T : RingedSite.{u,v} R}
    (f : RingedSiteMorphism S T) where
  pushforward : DGAlgebra S → DGAlgebra T
  pullback : DGAlgebra T → DGAlgebra S
  pushforward_preserves_differential : Prop
  pullback_preserves_differential : Prop
  adjunction : Prop

theorem definition_dga (S : RingedSite.{u,v} R) (A : DGAlgebraSheaf S) :
    A.graded_laws ∧ A.differential_squared ∧ A.leibniz := by
  sorry

theorem remark_functoriality_dga
    {S T : RingedSite.{u,v} R} {f : RingedSiteMorphism S T}
    (F : DGAlgebraFunctoriality f) :
    F.pushforward_preserves_differential ∧
      F.pullback_preserves_differential ∧ F.adjunction := by
  sorry

end Sdga
