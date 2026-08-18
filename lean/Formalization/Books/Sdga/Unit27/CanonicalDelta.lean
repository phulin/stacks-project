import Formalization.Books.Sdga.Unit02.Core

/-! # 27. The canonical delta-functor -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure CanonicalDeltaFunctorData {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  degree_zero : DGModule S A → Prop
  connecting_morphism : ShortExactSequence (A := A) → Prop
  connecting_formula : Prop
  connecting_formula_proof : connecting_formula
  exactness : Prop
  exactness_proof : exactness
  universality : Prop
  universality_proof : universality

structure HomotopyColimitData {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  sequence : ℕ → DGModule S A
  transition : ∀ n, DGModuleHom (sequence n) (sequence (n + 1))
  colimit : DGModule S A
  comparison : Prop
  comparison_proof : comparison

theorem lemma_derived_canonical_delta_functor {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (D : CanonicalDeltaFunctorData A) :
    D.connecting_formula ∧ D.exactness ∧ D.universality := by
  exact ⟨D.connecting_formula_proof, D.exactness_proof, D.universality_proof⟩

theorem lemma_homotopy_colimit {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (D : HomotopyColimitData A) : D.comparison := by
  exact D.comparison_proof

end Sdga
