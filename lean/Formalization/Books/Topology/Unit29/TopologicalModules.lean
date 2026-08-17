import Formalization.Books.Topology.Unit29.TopologicalRings
import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

/-!
# Topology, Chapter 29: Topological modules

Mathlib's `TopModuleCat R` is the canonical bundled category of topological modules over a
topological ring.  Its objects use `ContinuousAdd` and `ContinuousSMul`, and its morphisms are
`ContinuousLinearMap`s, so it directly supplies the source definitions and category interfaces.
-/

namespace Formalization.Books.Topology.Unit29

open CategoryTheory CategoryTheory.Limits
open Set TopologicalSpace

universe u v

noncomputable section

section Basic

variable {R : Type u} {M N : Type v}

/-- A bundled topological module from the unbundled data in the source definition. -/
def topologicalModuleObject (R : Type u) (M : Type v) [Ring R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] : TopModuleCat.{v} R :=
  TopModuleCat.of R M

/-- A homomorphism of topological modules, using Mathlib's continuous linear map. -/
abbrev TopologicalModuleHom (R : Type u) (M N : Type v) [Ring R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] [AddCommGroup N] [Module R N] [TopologicalSpace N] [ContinuousAdd N]
    [ContinuousSMul R N] :=
  M →L[R] N

/-- The quotient topology on the target of a linear map. -/
@[instance_reducible]
def quotientModuleTopology [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : TopologicalSpace N :=
  TopologicalSpace.coinduced f inferInstance

/-- The additive group of a topological module is a topological additive group. -/
theorem topologicalModule_additive_group [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] : IsTopologicalAddGroup M := by
  sorry

/-- A submodule with its induced topology is a topological module. -/
theorem topologicalModule_submodule [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] (S : Submodule R M) :
    ContinuousAdd S ∧ ContinuousSMul R S := by
  sorry

/-- A submodule quotient has the canonical quotient topology and is a topological module. -/
theorem topologicalModule_submodule_quotient [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousSMul R M] (S : Submodule R M) :
    ContinuousAdd (M ⧸ S) ∧ ContinuousSMul R (M ⧸ S) := by
  sorry

/-- A surjective module quotient with its quotient topology is a topological module. -/
theorem topologicalModule_surjective_quotient [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousSMul R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    letI : TopologicalSpace N := quotientModuleTopology f
    ContinuousAdd N ∧ ContinuousSMul R N := by
  sorry

end Basic

section Category

variable (R : Type u) [CommRing R] [TopologicalSpace R]

theorem topological_modules_have_limits : HasLimits (TopModuleCat.{v} R) := by
  infer_instance

theorem topological_module_limits_commute_with_topological_spaces :
    PreservesLimits (forget₂ (TopModuleCat.{v} R) TopCat.{v}) := by
  infer_instance

theorem topological_module_limits_commute_with_modules :
    PreservesLimits (forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)) := by
  sorry

theorem topological_modules_have_colimits : HasColimits (TopModuleCat.{v} R) := by
  infer_instance

theorem topological_module_colimits_commute_with_modules :
    PreservesColimits (forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)) := by
  sorry

end Category

end

end Formalization.Books.Topology.Unit29
