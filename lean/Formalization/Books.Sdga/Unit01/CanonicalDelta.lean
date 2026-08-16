import Formalization.«Books.Sdga».Unit01.Core

/-! # 27. The canonical delta-functor -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure CanonicalDeltaFunctorData {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  degree_zero : DGModule S A → Prop
  connecting_morphism : Prop
  exactness : Prop
  universality : Prop

structure HomotopyColimitData {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  diagram : Type (max u v)
  colimit : DGModule S A → Prop
  comparison : Prop

theorem lemma_derived_canonical_delta_functor {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (D : CanonicalDeltaFunctorData A) :
    D.exactness ∧ D.universality := by
  sorry

theorem lemma_homotopy_colimit {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (D : HomotopyColimitData A) : D.comparison := by
  exact D.comparison

end Sdga
