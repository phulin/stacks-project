import Formalization.«Books.Sdga».Unit01.Core

/-! # 27. The canonical delta-functor -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure CanonicalDeltaFunctorData {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  degree_zero : DGModule S A → Prop
  connecting_morphism : ShortExactSequence (A := A) → Prop
  connecting_formula : Prop
  exactness : Prop
  universality : Prop

structure HomotopyColimitData {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  sequence : ℕ → DGModule S A
  transition : ∀ n, DGModuleHom (sequence n) (sequence (n + 1))
  colimit : DGModule S A
  comparison : Prop

theorem lemma_derived_canonical_delta_functor {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (D : CanonicalDeltaFunctorData A) :
    D.connecting_formula ∧ D.exactness ∧ D.universality := by
  sorry

theorem lemma_homotopy_colimit {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (D : HomotopyColimitData A) : D.comparison := by
  sorry

end Sdga
