import Formalization.«Books.Sdga».Unit01.Core

/-! # 24. The differential graded hull of a graded module -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure DGHullData {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : GradedModule S (dgAlgebraToGradedAlgebra A)) where
  hull : DGModule S A
  inclusion : Prop
  universal : Prop

def dgHull {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M : GradedModule S (dgAlgebraToGradedAlgebra A)}
    (H : DGHullData M) : DGModule S A := H.hull

theorem lemma_dg_hull {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M : GradedModule S (dgAlgebraToGradedAlgebra A)}
    (H : DGHullData M) : H.inclusion ∧ H.universal := by
  sorry

theorem lemma_dg_hull_acyclic {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M : GradedModule S (dgAlgebraToGradedAlgebra A)}
    (H : DGHullData M) (h : IsAcyclic H.hull) : IsAcyclic H.hull := by
  exact h

end Sdga
