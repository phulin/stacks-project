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
def topologicalModuleObject (R : Type u) (M : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] : TopModuleCat.{v} R :=
  TopModuleCat.of R M

/-- A homomorphism of topological modules, using Mathlib's continuous linear map. -/
abbrev TopologicalModuleHom (R : Type u) (M N : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] [AddCommGroup N] [Module R N] [TopologicalSpace N] [ContinuousAdd N]
    [ContinuousSMul R N] :=
  M →L[R] N

/-- The quotient topology on the target of a linear map. -/
@[instance_reducible]
def quotientModuleTopology [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : TopologicalSpace N :=
  TopologicalSpace.coinduced f inferInstance

/-- The additive group of a topological module is a topological additive group. -/
theorem topologicalModule_additive_group [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] : IsTopologicalAddGroup M := by
  refine { toContinuousAdd := ?_, toContinuousNeg := ?_ }
  · exact inferInstance
  · exact ContinuousNeg.of_continuousConstSMul R M

/-- A submodule with its induced topology is a topological module. -/
theorem topologicalModule_submodule [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] (S : Submodule R M) :
    ContinuousAdd S ∧ ContinuousSMul R S := by
  exact ⟨
    ⟨(continuous_subtype_val.comp continuous_fst).add
        (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _⟩,
    ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk
        (fun p => S.smul_mem p.1 p.2.2)⟩
  ⟩

/-- A submodule quotient has the canonical quotient topology and is a topological module. -/
theorem topologicalModule_submodule_quotient [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousSMul R M] (S : Submodule R M) :
    ContinuousAdd (M ⧸ S) ∧ ContinuousSMul R (M ⧸ S) := by
  let _ : IsTopologicalAddGroup M :=
    topologicalModule_additive_group (R := R) (M := M)
  exact ⟨inferInstance, inferInstance⟩

/-- A surjective module quotient with its quotient topology is a topological module. -/
theorem topologicalModule_surjective_quotient [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousSMul R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    letI : TopologicalSpace N := quotientModuleTopology f
    ContinuousAdd N ∧ ContinuousSMul R N := by
  let _ : TopologicalSpace N := quotientModuleTopology f
  have hq : Topology.IsQuotientMap f.toAddMonoidHom := ⟨⟨rfl⟩, hf⟩
  have hoq : IsOpenQuotientMap f.toAddMonoidHom :=
    AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hq
  refine ⟨?_, ?_⟩
  · apply ContinuousAdd.mk
    rw [← (hoq.prodMap hoq).continuous_comp_iff]
    convert hoq.continuous.comp continuous_add using 1
    ext p
    simp
  · apply ContinuousSMul.mk
    rw [← (IsOpenQuotientMap.id.prodMap hoq).continuous_comp_iff]
    have hsmul : Continuous (fun p : R × M => p.1 • p.2) := continuous_smul
    convert hoq.continuous.comp hsmul using 1
    ext p
    simp

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
  infer_instance

theorem topological_modules_have_colimits : HasColimits (TopModuleCat.{v} R) := by
  infer_instance

theorem topological_module_colimits_commute_with_modules :
    PreservesColimits (forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)) := by
  infer_instance

end Category

end

end Formalization.Books.Topology.Unit29
