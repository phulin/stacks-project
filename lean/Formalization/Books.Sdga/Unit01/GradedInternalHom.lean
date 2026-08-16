import Formalization.«Books.Sdga».Unit01.Core

/-! # 7. Internal hom for sheaves of graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def gradedInternalHomObject {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N : GradedModule S A} (H : InternalHomModel M N) : GradedFamily S :=
  internalHom H

structure GradedInternalHomProperties {S : RingedSite.{u,v} R}
    {A : GradedAlgebra S} {M N : GradedModule S A}
    (H : InternalHomModel M N) where
  module_map : H.module_map_property
  composition : H.composition_property

theorem graded_internal_hom_properties
    {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N : GradedModule S A} (H : InternalHomModel M N) :
    Nonempty (GradedInternalHomProperties H) := by
  sorry

end Sdga
