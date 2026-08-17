import Formalization.Books.MoreAlgebra.Unit36.TopologicalRings
import Formalization.Books.Topology.Unit29.TopologicalModules
import Mathlib.Topology.Algebra.LinearTopology

namespace Formalization.Books.MoreAlgebra.Unit36

open Filter Set

universe u v

noncomputable section

/-- The source's unbundled topological-module condition. -/
abbrev IsTopologicalModule (R : Type u) (M : Type v) [CommRing R]
    [TopologicalSpace R] [TopologicalSpace M] [AddCommGroup M] [Module R M] :=
  ContinuousAdd M ∧ ContinuousSMul R M

/-- The source's continuous module maps, reusing the earlier canonical declaration. -/
abbrev TopologicalModuleHom (R : Type u) (M N : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] [AddCommGroup N] [Module R N] [TopologicalSpace N]
    [ContinuousAdd N] [ContinuousSMul R N] :=
  Formalization.Books.Topology.Unit29.TopologicalModuleHom R M N

theorem topologicalModuleHom_continuous
    (R : Type u) (M N : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] [AddCommGroup N] [Module R N] [TopologicalSpace N]
    [ContinuousAdd N] [ContinuousSMul R N] (f : TopologicalModuleHom R M N) :
    Continuous f := by
  exact f.continuous

theorem topologicalModule_additive_group
    (R : Type u) (M : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] :
    IsTopologicalAddGroup M := by
  exact Formalization.Books.Topology.Unit29.topologicalModule_additive_group (R := R) (M := M)

theorem linearlyTopologized_iff_hasBasis_submodule
    (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [TopologicalSpace R] [TopologicalSpace M] :
    IsLinearTopology R M ↔
      (nhds (0 : M)).HasBasis
        (fun N : Submodule R M => (N : Set M) ∈ nhds (0 : M))
        (fun N : Submodule R M => (N : Set M)) := by
  exact isLinearTopology_iff_hasBasis_submodule

end

end Formalization.Books.MoreAlgebra.Unit36
