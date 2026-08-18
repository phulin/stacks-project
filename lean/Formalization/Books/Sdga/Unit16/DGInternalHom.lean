import Formalization.Books.Sdga.Unit02.Core

/-! # 16. Internal hom for sheaves of differential graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def dgInternalHomObject {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (H : DGInternalHomModel M N) : GradedFamily S :=
  dgInternalHom H

def dgInternalHomDifferential {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (H : DGInternalHomModel M N) :
    ∀ n U, H.component n U → H.component (n + 1) U := H.differential

structure DGInternalHomProperties {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} {M N : DGModule S A}
    (H : DGInternalHomModel M N) where
  module_map : H.module_map_property
  commutator : H.commutator_property

theorem dg_internal_hom_properties
    {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (H : DGInternalHomModel M N) :
    Nonempty (DGInternalHomProperties H) := by
  exact ⟨{ module_map := H.module_map_property_proof, commutator := H.commutator_property_proof }⟩

end Sdga
