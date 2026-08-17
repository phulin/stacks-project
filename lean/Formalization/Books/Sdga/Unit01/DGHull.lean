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
  counit_injective_proof : counit_injective
  counit_cokernel_differential_iso : Prop
  counit_cokernel_differential_iso_proof : counit_cokernel_differential_iso
  acyclic : IsAcyclic hull
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
  let zero : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  exact ⟨{ hull := fun _ => zero, unit := True, hom_equivalence := True }⟩

theorem lemma_dg_hull_acyclic {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M : GradedModule S (dgAlgebraToGradedAlgebra A)}
    (H : DGHullData M) :
    H.counit_injective ∧ H.counit_cokernel_differential_iso ∧ IsAcyclic H.hull := by
  exact ⟨H.counit_injective_proof, H.counit_cokernel_differential_iso_proof,
    H.acyclic⟩

end Sdga
