import Formalization.Books.Sdga.Unit01.Core

/-! # 24. The differential graded hull of a graded module -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure DGHullData {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : GradedModule S (dgAlgebraToGradedAlgebra A)) where
  hull : DGModule S A
  counit : GradedModuleHom M (dgModuleToGradedModule hull)
  counit_injective : Prop
  counit_cokernel_differential_iso : Prop
  universal : Prop

structure DGHullAdjunction {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  hull : GradedModule S (dgAlgebraToGradedAlgebra A) → DGModule S A
  unit : Prop
  hom_equivalence : Prop

def dgHull {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M : GradedModule S (dgAlgebraToGradedAlgebra A)}
    (H : DGHullData M) : DGModule S A := H.hull

theorem lemma_dg_hull {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (DGHullAdjunction A) := by
  sorry

theorem lemma_dg_hull_acyclic {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M : GradedModule S (dgAlgebraToGradedAlgebra A)}
    (H : DGHullData M) :
    H.counit_injective ∧ H.counit_cokernel_differential_iso ∧ IsAcyclic H.hull := by
  sorry

end Sdga
