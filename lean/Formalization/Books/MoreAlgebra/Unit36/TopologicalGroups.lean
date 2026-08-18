import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.LinearTopology

namespace Formalization.Books.MoreAlgebra.Unit36

open CategoryTheory
open CategoryTheory.Limits
open Filter Set

universe u v

noncomputable section

/-- Continuous homomorphisms of topological abelian groups.

This is the canonical Mathlib continuous additive homomorphism, with no parallel
homomorphism structure introduced for the chapter. -/
abbrev TopologicalAbelianGroupHom (G : Type u) (H : Type v)
    [AddCommGroup G] [AddCommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] :=
  G →ₜ+ H

/-- The source's topological abelian group structure, using Mathlib's canonical class. -/
abbrev TopologicalAbelianGroup (M : Type u) [AddCommGroup M] [TopologicalSpace M] :=
  IsTopologicalAddGroup M

/-- The additive category of topological abelian groups. -/
abbrev TopologicalAbelianGroupCat := TopModuleCat.{u} ℤ

abbrev topologicalAbelianGroupCat_preadditive :
    Preadditive (TopologicalAbelianGroupCat.{u}) := by
  infer_instance

theorem topologicalAbelianGroupCat_has_kernels :
    HasKernels (TopologicalAbelianGroupCat.{u}) := by
  infer_instance

theorem topologicalAbelianGroupCat_has_cokernels :
    HasCokernels (TopologicalAbelianGroupCat.{u}) := by
  infer_instance

private structure BottomModuleTopologyData (X : Type u) [Add X] [SMul ℤ X] where
  topology : TopologicalSpace X
  continuousSMul : @ContinuousSMul ℤ X _ _ (⊥ : TopologicalSpace X)
  continuousAdd : @ContinuousAdd X (⊥ : TopologicalSpace X) _

private def bottom_module_topology_data
    (X : Type u) [Add X] [SMul ℤ X] : BottomModuleTopologyData X := by
  letI : TopologicalSpace X := ⊥
  letI : DiscreteTopology X := discreteTopology_bot _
  exact ⟨⊥, ⟨continuous_of_discreteTopology⟩, ⟨continuous_of_discreteTopology⟩⟩

private theorem topologicalAbelianGroupCat_not_abelian_aux
    [P : Preadditive (TopologicalAbelianGroupCat.{u})]
    [N : IsNormalMonoCategory (TopologicalAbelianGroupCat.{u})] : False := by
  let A : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let D : TopologicalAbelianGroupCat.{u} := (TopModuleCat.withModuleTopology ℤ).obj A
  let I : TopologicalAbelianGroupCat.{u} :=
    (TopModuleCat.indiscrete ℤ).obj ((forget₂ _ (ModuleCat ℤ)).obj D)
  let f : D ⟶ I := (TopModuleCat.indiscreteAdj ℤ).unit.app D
  let hfmono : Mono f := ConcreteCategory.mono_of_injective f (by
    intro x y hxy
    exact hxy)
  let hfepi : Epi f := ConcreteCategory.epi_of_surjective f (by
    intro y
    exact ⟨y, rfl⟩)
  have hnormal : NormalMono f :=
    (IsNormalMonoCategory.normalMonoOfMono f).some
  have hzero : hnormal.g = 0 := by
    apply hfepi.left_cancellation
    simpa using hnormal.w
  obtain ⟨g, hgf⟩ := KernelFork.IsLimit.lift' hnormal.isLimit (𝟙 I) (by simp [hzero])
  have hgf' : g ≫ f = 𝟙 I := hgf
  have hfg : f ≫ g = 𝟙 D := by
    apply hfmono.right_cancellation
    simp [Category.assoc, hgf']
  have hgid : ∀ x : I, g.hom x = x := by
    intro x
    have h := ConcreteCategory.congr_hom hgf' x
    change g.hom x = x at h
    exact h
  have hDtop : D.topologicalSpace = ⊥ := by
    change moduleTopology ℤ (ULift.{u} ℤ) = ⊥
    let hdata := bottom_module_topology_data (ULift.{u} ℤ)
    have hle : moduleTopology ℤ (ULift.{u} ℤ) ≤ hdata.topology := by
      exact @moduleTopology_le ℤ _ (ULift.{u} ℤ) _ _ hdata.topology
        hdata.continuousSMul hdata.continuousAdd
    exact le_antisymm hle bot_le
  have hopen : @IsOpen D D.topologicalSpace ({(0 : D)} : Set D) := by
    rw [hDtop]
    exact @isOpen_discrete (D : Type u) ⊥ (discreteTopology_bot _) _
  have hpreopen : @IsOpen I I.topologicalSpace
      (g.hom ⁻¹' ({(0 : D)} : Set D)) := g.hom.continuous.isOpen_preimage _ hopen
  have hpre : g.hom ⁻¹' ({(0 : D)} : Set D) = ({(0 : I)} : Set I) := by
    ext x
    change g.hom x ∈ ({(0 : D)} : Set D) ↔ x ∈ ({(0 : I)} : Set I)
    rw [hgid x]
    exact Set.mem_singleton_iff
  rw [hpre] at hpreopen
  have hnot : ¬@IsOpen (I : Type u) I.topologicalSpace
      ({(0 : I)} : Set I) := by
    intro h
    rcases (@IndiscreteTopology.isOpen_iff (I : Type u) I.topologicalSpace ⟨by rfl⟩ _).1 h with h | h
    · have hz : (0 : I) ∈ (∅ : Set I) := h ▸ Set.mem_singleton (0 : I)
      exact hz
    · have hone : (ULift.up (1 : ℤ) : I) ∈ ({(0 : I)} : Set I) := by
        rw [h]
        trivial
      have hne : (ULift.up (1 : ℤ) : I) ≠ 0 := by
        intro hz
        have hz' := congrArg ULift.down hz
        change (1 : ℤ) = 0 at hz'
        exact one_ne_zero hz'
      exact hne (Set.mem_singleton_iff.mp hone)
  exact hnot hpreopen

/-- Topological abelian groups do not form an abelian category in general. -/
theorem topologicalAbelianGroupCat_not_abelian :
    ¬ Nonempty (Abelian (TopologicalAbelianGroupCat.{u})) := by
  rintro ⟨hA⟩
  exact @topologicalAbelianGroupCat_not_abelian_aux
    hA.toPreadditive hA.toIsNormalMonoCategory

/-- An open subgroup has discrete quotient topology. -/
theorem quotient_add_group_is_discrete_of_open
    {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (N : AddSubgroup G)
    (hN : IsOpen (N : Set G)) :
    DiscreteTopology (G ⧸ N) := by
  exact QuotientAddGroup.discreteTopology hN

theorem topologicalAbelianGroup_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (N : AddSubgroup G) :
    IsTopologicalAddGroup N := by
  infer_instance

theorem linearTopology_neighborhood_subgroup_isOpen
    {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [IsLinearTopology ℤ G]
    (N : AddSubgroup G) (hN : (N : Set G) ∈ nhds (0 : G)) :
    IsOpen (N : Set G) := by
  sorry

theorem quotient_add_group_projection_isQuotientMap
    {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    (N : AddSubgroup G) :
    Topology.IsQuotientMap (QuotientAddGroup.mk : G → G ⧸ N) := by
  exact QuotientAddGroup.isQuotientMap_mk N

/-- A countable basis at zero, written in the form used by the Baire statements. -/
def HasCountableNeighborhoodBasisAtZero (M : Type u) [Zero M] [TopologicalSpace M] : Prop :=
  ∃ b : ℕ → Set M, (nhds (0 : M)).HasBasis (fun _ : ℕ => True) b

/-- Completeness for a topological additive group, with separatedness included. -/
def IsCompleteTopologicalAddGroup (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] : Prop :=
  @CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M) ∧ T2Space M

/-- Complete separated additive-group topology, with its uniformity made explicit.

This form is useful when a canonical topology is being described before it is installed as an
instance. -/
def IsCompleteSeparatedTopologicalAddGroupFor (M : Type u) (t : TopologicalSpace M)
    [AddCommGroup M] : Prop :=
  ∃ u : UniformSpace M,
    u.toTopologicalSpace = t ∧ @IsUniformAddGroup M u (inferInstance : AddGroup M) ∧
      @CompleteSpace M u ∧ @T2Space M t

/-- A discrete inverse system of topological abelian groups. -/
structure DiscreteInverseSystem (I : Type u) [Preorder I] where
  diagram : Iᵒᵖ ⥤ TopologicalAbelianGroupCat.{u}
  directed : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k
  nonempty : Nonempty I
  discrete : ∀ i : Iᵒᵖ, DiscreteTopology (diagram.obj i)

/-- The topological group underlying the inverse limit of an inverse system. -/
noncomputable def inverseLimit {I : Type u} [Preorder I]
    (F : DiscreteInverseSystem I) :
    TopologicalAbelianGroupCat.{u} :=
  limit F.diagram

/-- The kernel of the projection from an inverse limit to one of its discrete terms. -/
def inverseLimitKernel {I : Type u} [Preorder I]
    (F : DiscreteInverseSystem I) (i : Iᵒᵖ) :
    Submodule ℤ (inverseLimit F) :=
  (limit.π F.diagram i).hom.toLinearMap.ker

theorem inverseLimit_is_linearly_topologized {I : Type u} [Preorder I]
    (F : DiscreteInverseSystem I) :
    IsLinearTopology ℤ (inverseLimit F) := by
  sorry

theorem inverseLimit_kernels_form_fundamental_system
    {I : Type u} [Preorder I] (F : DiscreteInverseSystem I) :
    (nhds (0 : inverseLimit F)).HasBasis
      (fun _ : Iᵒᵖ => True)
      (fun i => (inverseLimitKernel F i : Set (inverseLimit F))) := by
  sorry

theorem inverseLimit_is_complete {I : Type u} [Preorder I]
    (F : DiscreteInverseSystem I) :
    IsCompleteTopologicalAddGroup (inverseLimit F) := by
  sorry

/-- A chosen fundamental system of open subgroup neighborhoods of zero. -/
structure LinearNeighborhoodBasis (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] where
  Index : Type u
  [preorder : Preorder Index]
  U : Index → AddSubgroup M
  antitone : Antitone U
  directed : ∀ i j : Index, ∃ k : Index, i ≤ k ∧ j ≤ k
  fundamental :
    (nhds (0 : M)).HasBasis (fun _ : Index => True)
      (fun i => (U i : Set M))
  isOpen : ∀ i, IsOpen (U i : Set M)

theorem exists_linearNeighborhoodBasis (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [IsLinearTopology ℤ M] :
    Nonempty (LinearNeighborhoodBasis M) := by
  sorry

theorem linearNeighborhoodBasis_completion_map
    (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [IsLinearTopology ℤ M]
    (B : LinearNeighborhoodBasis M) :
    let _ : Preorder B.Index := B.preorder
    ∃ (F : DiscreteInverseSystem B.Index)
      (c : M →ₜ+ inverseLimit F),
      (∀ i : B.Index,
        Nonempty (F.diagram.obj (Opposite.op i) ≃ₜ+ (M ⧸ B.U i))) ∧
        (Function.Injective c ↔ T2Space M) ∧
        (IsCompleteTopologicalAddGroup M ↔ Function.Bijective c) := by
  sorry

/-- The completion associated to the canonical uniformity of a topological additive group. -/
abbrev LinearTopologicalCompletion (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] :=
  @UniformSpace.Completion M (IsTopologicalAddGroup.rightUniformSpace M)

/- The basis-independence assertion in the source is represented by this basis-free completion
   type: it is built from the canonical uniformity, rather than from a chosen neighborhood basis. -/

/-- The canonical map into the completion. -/
noncomputable def linearCompletionMap (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] :
    (let _ : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
     let _ : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
     M →ₜ+ UniformSpace.Completion M) := by
  letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  letI : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  dsimp
  exact { UniformSpace.Completion.toCompl with
    continuous_toFun := UniformSpace.Completion.continuous_toCompl }

theorem linearCompletion_completeSpace (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] :
    CompleteSpace (LinearTopologicalCompletion M) := by
  let _ : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  infer_instance

theorem linearCompletion_t2Space (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] :
    T2Space (LinearTopologicalCompletion M) := by
  sorry

theorem linearCompletionMap_injective_iff_separated
    (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] :
    Function.Injective (linearCompletionMap M) ↔ T2Space M := by
  sorry

theorem isCompleteTopologicalAddGroup_iff_linearCompletionMap_bijective
    (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] :
    IsCompleteTopologicalAddGroup M ↔
      Function.Bijective (linearCompletionMap M) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit36
