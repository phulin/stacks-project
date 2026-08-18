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
  exact N.isOpen_of_mem_nhds hN

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
  classical
  unfold inverseLimit at *
  have htop : (inferInstance : TopologicalSpace ((limit F.diagram).toModuleCat)) =
      ⨅ i : Iᵒᵖ, (F.diagram.obj i).topologicalSpace.induced ((limit.π F.diagram i).hom) := by
    exact TopCat.induced_of_isLimit
      ((forget₂ (TopologicalAbelianGroupCat) TopCat).mapCone (limit.cone F.diagram))
      (isLimitOfPreserves (forget₂ (TopologicalAbelianGroupCat) TopCat)
        (limit.isLimit F.diagram))
  have hnhds :
      @nhds _ (inferInstance : TopologicalSpace ((limit F.diagram).toModuleCat))
          (0 : (limit F.diagram).toModuleCat) =
        @nhds _ (⨅ i : Iᵒᵖ, (F.diagram.obj i).topologicalSpace.induced
          ((limit.π F.diagram i).hom)) (0 : (limit F.diagram).toModuleCat) := by
    exact congrArg (fun t : TopologicalSpace ((limit F.diagram).toModuleCat) =>
      @nhds _ t (0 : (limit F.diagram).toModuleCat)) htop
  have hi : ∀ i : Iᵒᵖ,
      @nhds _ (F.diagram.obj i).topologicalSpace (0 : F.diagram.obj i) = pure 0 := by
    intro i
    let _ : DiscreteTopology (F.diagram.obj i) := F.discrete i
    rw [nhds_discrete]
  let K : Iᵒᵖ → Submodule ℤ ((limit F.diagram).toModuleCat) :=
    fun i => (limit.π F.diagram i).hom.toLinearMap.ker
  let S : Iᵒᵖ → Set ((limit F.diagram).toModuleCat) :=
    fun i => (K i : Set ((limit F.diagram).toModuleCat))
  refine IsLinearTopology.mk_of_hasBasis' ℤ
    (S := Submodule ℤ ((limit F.diagram).toModuleCat))
    (s := fun s : Set Iᵒᵖ => ⨅ i : s, K i)
    (p := fun s : Set Iᵒᵖ => s.Finite) ?_
    (by intro s r m hm; exact s.smul_mem r hm)
  rw [hnhds]
  have hnhds_i :
      @nhds _ (⨅ i : Iᵒᵖ, (F.diagram.obj i).topologicalSpace.induced
          ((limit.π F.diagram i).hom)) (0 : (limit F.diagram).toModuleCat) =
        ⨅ i : Iᵒᵖ, Filter.comap ((limit.π F.diagram i).hom)
          (@nhds _ (F.diagram.obj i).topologicalSpace (0 : F.diagram.obj i)) := by
    rw [nhds_iInf]
    apply iInf_congr
    intro i
    rw [nhds_induced]
    rw [map_zero]
  rw [hnhds_i]
  have hcomp : ∀ i : Iᵒᵖ,
      Filter.comap ((limit.π F.diagram i).hom)
          (nhds (0 : F.diagram.obj i)) =
        𝓟 (S i) := by
    intro i
    rw [hi i, Filter.comap_pure]
    congr 1
  have hfilter : (⨅ i : Iᵒᵖ, Filter.comap ((limit.π F.diagram i).hom)
      (nhds (0 : F.diagram.obj i))) = ⨅ i : Iᵒᵖ, 𝓟 (S i) := by
    apply iInf_congr
    intro i
    exact hcomp i
  rw [hfilter]
  have hb := Filter.hasBasis_iInf_principal_finite S
  refine hb.congr ?_ ?_
  · intro s
    exact Iff.rfl
  · intro s hs
    ext x
    simpa [S, K]

theorem inverseLimit_kernels_form_fundamental_system
    {I : Type u} [Preorder I] (F : DiscreteInverseSystem I) :
    (nhds (0 : inverseLimit F)).HasBasis
      (fun _ : Iᵒᵖ => True)
      (fun i => (inverseLimitKernel F i : Set (inverseLimit F))) := by
  classical
  unfold inverseLimit at *
  let K : Iᵒᵖ → Submodule ℤ ((limit F.diagram).toModuleCat) :=
    fun i => (limit.π F.diagram i).hom.toLinearMap.ker
  let S : Iᵒᵖ → Set ((limit F.diagram).toModuleCat) :=
    fun i => (K i : Set ((limit F.diagram).toModuleCat))
  have htop : (inferInstance : TopologicalSpace ((limit F.diagram).toModuleCat)) =
      ⨅ i : Iᵒᵖ, (F.diagram.obj i).topologicalSpace.induced ((limit.π F.diagram i).hom) := by
    exact TopCat.induced_of_isLimit
      ((forget₂ (TopologicalAbelianGroupCat) TopCat).mapCone (limit.cone F.diagram))
      (isLimitOfPreserves (forget₂ (TopologicalAbelianGroupCat) TopCat)
        (limit.isLimit F.diagram))
  have hnhds :
      @nhds _ (inferInstance : TopologicalSpace ((limit F.diagram).toModuleCat))
          (0 : (limit F.diagram).toModuleCat) =
        @nhds _ (⨅ i : Iᵒᵖ, (F.diagram.obj i).topologicalSpace.induced
          ((limit.π F.diagram i).hom)) (0 : (limit F.diagram).toModuleCat) := by
    exact congrArg (fun t : TopologicalSpace ((limit F.diagram).toModuleCat) =>
      @nhds _ t (0 : (limit F.diagram).toModuleCat)) htop
  have hi : ∀ i : Iᵒᵖ,
      @nhds _ (F.diagram.obj i).topologicalSpace (0 : F.diagram.obj i) = pure 0 := by
    intro i
    let _ : DiscreteTopology (F.diagram.obj i) := F.discrete i
    rw [nhds_discrete]
  have hnhds_i :
      @nhds _ (⨅ i : Iᵒᵖ, (F.diagram.obj i).topologicalSpace.induced
          ((limit.π F.diagram i).hom)) (0 : (limit F.diagram).toModuleCat) =
        ⨅ i : Iᵒᵖ, Filter.comap ((limit.π F.diagram i).hom)
          (@nhds _ (F.diagram.obj i).topologicalSpace (0 : F.diagram.obj i)) := by
    rw [nhds_iInf]
    apply iInf_congr
    intro i
    rw [nhds_induced]
    rw [map_zero]
  have hcomp : ∀ i : Iᵒᵖ,
      Filter.comap ((limit.π F.diagram i).hom)
          (nhds (0 : F.diagram.obj i)) =
        𝓟 (S i) := by
    intro i
    rw [hi i, Filter.comap_pure]
    congr 1
  have hfilter : (⨅ i : Iᵒᵖ, Filter.comap ((limit.π F.diagram i).hom)
      (nhds (0 : F.diagram.obj i))) = ⨅ i : Iᵒᵖ, 𝓟 (S i) := by
    apply iInf_congr
    intro i
    exact hcomp i
  have hker : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), K i ≤ K j := by
    intro i j f
    dsimp [K]
    have hcomp' := limit.w F.diagram f
    have heq :
        (F.diagram.map f).hom.toLinearMap.comp
            (limit.π F.diagram i).hom.toLinearMap =
          (limit.π F.diagram j).hom.toLinearMap := by
      ext x
      exact congrArg (fun q => q.hom x) hcomp'
    rw [← heq]
    exact LinearMap.ker_le_ker_comp
      (limit.π F.diagram i).hom.toLinearMap
      (F.diagram.map f).hom.toLinearMap
  let _ : Nonempty Iᵒᵖ := F.nonempty.map Opposite.op
  have hdir : Directed (· ≥ ·) (fun i : Iᵒᵖ => S i) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := F.directed i.unop j.unop
    let f_i : Opposite.op k ⟶ i := (homOfLE hik).op
    let f_j : Opposite.op k ⟶ j := (homOfLE hjk).op
    refine ⟨Opposite.op k, ?_, ?_⟩
    · intro x hx
      exact (hker f_i) hx
    · intro x hx
      exact (hker f_j) hx
  rw [hnhds, hnhds_i, hfilter]
  simpa [S, K, inverseLimitKernel] using
    (Filter.hasBasis_iInf_principal hdir)

theorem inverseLimit_is_complete {I : Type u} [Preorder I]
    (F : DiscreteInverseSystem I) :
    IsCompleteTopologicalAddGroup (inverseLimit F) := by
  classical
  unfold inverseLimit at *
  have hcomplete_i : ∀ i : Iᵒᵖ,
      @CompleteSpace (F.diagram.obj i)
        (IsTopologicalAddGroup.rightUniformSpace (F.diagram.obj i)) := by
    intro i
    let _ : DiscreteTopology (F.diagram.obj i) := F.discrete i
    let u := IsTopologicalAddGroup.rightUniformSpace (F.diagram.obj i)
    let _ : UniformSpace (F.diagram.obj i) := u
    have hdisc : @DiscreteUniformity (F.diagram.obj i) u := by
      refine ⟨?_⟩
      apply @UniformSpace.ext (F.diagram.obj i) u (⊥ : UniformSpace (F.diagram.obj i))
      change @uniformity (F.diagram.obj i) u =
        @uniformity (F.diagram.obj i) (⊥ : UniformSpace (F.diagram.obj i))
      change comap (fun x : (F.diagram.obj i) × (F.diagram.obj i) => x.2 + (-x.1))
          (@nhds (F.diagram.obj i) (F.diagram.obj i).2 (0 : F.diagram.obj i)) =
        𝓟 SetRel.id
      rw [nhds_discrete, Filter.comap_pure]
      congr 1
      ext p
      change p.2 + -p.1 = 0 ↔ p.1 = p.2
      constructor
      · intro h
        have hp : p.2 - p.1 = 0 := by simpa [sub_eq_add_neg] using h
        exact (sub_eq_zero.mp hp).symm
      · intro h
        have hp : p.2 - p.1 = 0 := sub_eq_zero.mpr h.symm
        simpa [sub_eq_add_neg] using hp
    let _ : DiscreteUniformity (F.diagram.obj i) := hdisc
    change @CompleteSpace (F.diagram.obj i) u
    refine ⟨?_⟩
    intro f hf
    obtain ⟨x, hfx⟩ := DiscreteUniformity.eq_pure_of_cauchy hf
    refine ⟨x, ?_⟩
    rw [hfx]
    exact pure_le_nhds x
  let g : (limit F.diagram).toModuleCat →+ ∀ i : Iᵒᵖ, F.diagram.obj i :=
    { toFun := fun x i => (limit.π F.diagram i).hom x
      map_zero' := by
        ext i
        exact map_zero _
      map_add' := by
        intro x y
        ext i
        exact map_add _ _ _ }
  letI : ∀ i : Iᵒᵖ, TopologicalSpace (F.diagram.obj i) :=
    fun i => (F.diagram.obj i).topologicalSpace
  have htop : (inferInstance : TopologicalSpace ((limit F.diagram).toModuleCat)) =
      ⨅ i : Iᵒᵖ, (F.diagram.obj i).topologicalSpace.induced ((limit.π F.diagram i).hom) := by
    exact TopCat.induced_of_isLimit
      ((forget₂ (TopologicalAbelianGroupCat) TopCat).mapCone (limit.cone F.diagram))
      (isLimitOfPreserves (forget₂ (TopologicalAbelianGroupCat) TopCat)
        (limit.isLimit F.diagram))
  have hind : Topology.IsInducing (g : (limit F.diagram).toModuleCat →
      ∀ i : Iᵒᵖ, F.diagram.obj i) := by
    refine ⟨?_⟩
    calc
      _ = ⨅ i, (F.diagram.obj i).topologicalSpace.induced
          ((limit.π F.diagram i).hom) := htop
      _ = TopologicalSpace.induced (g : (limit F.diagram).toModuleCat →
          ∀ i : Iᵒᵖ, F.diagram.obj i) Pi.topologicalSpace := by
        change _ = TopologicalSpace.induced
          (fun x i => (limit.π F.diagram i).hom x)
          (@Pi.topologicalSpace Iᵒᵖ (fun i => F.diagram.obj i)
            (fun i => (F.diagram.obj i).topologicalSpace))
        rw [@induced_to_pi (ι := Iᵒᵖ) (A := fun i => F.diagram.obj i)
          (T := fun i => (F.diagram.obj i).topologicalSpace)
          (X := (limit F.diagram).toModuleCat)]
  let _ : ∀ i : Iᵒᵖ, DiscreteTopology (F.diagram.obj i) :=
    fun i => F.discrete i
  have hD : IsLimit ((forget TopCat).mapCone
      ((forget₂ (TopologicalAbelianGroupCat) TopCat).mapCone
        (limit.cone F.diagram))) :=
    isLimitOfPreserves (forget TopCat)
      (isLimitOfPreserves (forget₂ (TopologicalAbelianGroupCat) TopCat)
        (limit.isLimit F.diagram))
  have hinj : Function.Injective (g : (limit F.diagram).toModuleCat →
      ∀ i : Iᵒᵖ, F.diagram.obj i) := by
    intro x y hxy
    apply (Types.isLimitEquivSections hD).injective
    ext i
    exact congrFun hxy i
  have hT2 : T2Space ((limit F.diagram).toModuleCat) :=
    T2Space.of_injective_continuous hinj hind.continuous
  have hSclosed : IsClosed (⋂ (i : Iᵒᵖ) (j : Iᵒᵖ) (f : i ⟶ j),
      { z : ∀ i : Iᵒᵖ, F.diagram.obj i |
        (F.diagram.map f).hom (z i) = z j }) := by
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro f
    apply isClosed_eq
    · exact ((F.diagram.map f).hom.continuous).comp (continuous_apply i)
    · exact continuous_apply j
  have hgrange : Set.range (g : (limit F.diagram).toModuleCat →
      ∀ i : Iᵒᵖ, F.diagram.obj i) =
      ⋂ (i : Iᵒᵖ) (j : Iᵒᵖ) (f : i ⟶ j),
        { z : ∀ i : Iᵒᵖ, F.diagram.obj i |
          (F.diagram.map f).hom (z i) = z j } := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      simp only [Set.mem_iInter]
      intro i j f
      exact congrArg (fun q => q.hom x) (limit.w F.diagram f)
    · intro hz
      have hz' : ∀ (i j : Iᵒᵖ) (f : i ⟶ j),
          (F.diagram.map f).hom (z i) = z j := by
        intro i j f
        have hi := Set.mem_iInter.1 hz i
        have hij := Set.mem_iInter.1 hi j
        simpa using Set.mem_iInter.1 hij f
      let c : Cone (F.diagram ⋙ forget₂ (TopologicalAbelianGroupCat) TopCat ⋙
          forget TopCat) :=
        { pt := PUnit.{u + 1}
          π := { app := fun i =>
                   TypeCat.ofHom
                     (fun _ : ((Functor.const Iᵒᵖ).obj PUnit.{u + 1}).obj i => z i)
                 naturality := by
                   intro i j f
                   ext x
                   exact (hz' i j f).symm } }
      refine ⟨hD.lift c (PUnit.unit : PUnit.{u + 1}), ?_⟩
      funext i
      simpa [g, c] using congrArg (fun q => q (PUnit.unit : PUnit.{u + 1}))
        (hD.fac c i)
  letI : ∀ i : Iᵒᵖ, UniformSpace (F.diagram.obj i) :=
    fun i => IsTopologicalAddGroup.rightUniformSpace (F.diagram.obj i)
  letI : ∀ i : Iᵒᵖ, IsUniformAddGroup (F.diagram.obj i) :=
    fun i => isUniformAddGroup_of_addCommGroup
  letI : ∀ i : Iᵒᵖ, CompleteSpace (F.diagram.obj i) :=
    fun i => hcomplete_i i
  have hprod : CompleteSpace (∀ i : Iᵒᵖ, F.diagram.obj i) := by
    infer_instance
  letI : CompleteSpace (∀ i : Iᵒᵖ, F.diagram.obj i) := hprod
  letI : UniformSpace ((limit F.diagram).toModuleCat) :=
    IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup ((limit F.diagram).toModuleCat) :=
    isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup (∀ i : Iᵒᵖ, F.diagram.obj i) := by
    refine { uniformContinuous_sub := ?_ }
    rw [uniformContinuous_pi]
    intro i
    exact IsUniformAddGroup.uniformContinuous_sub.comp
      (((Pi.uniformContinuous_proj _ i).comp uniformContinuous_fst).prodMk
        ((Pi.uniformContinuous_proj _ i).comp uniformContinuous_snd))
  have huind : IsUniformInducing (g : (limit F.diagram).toModuleCat →
      ∀ i : Iᵒᵖ, F.diagram.obj i) :=
    AddMonoidHom.isUniformInducing_of_isInducing hind
  have hrange : IsComplete (Set.range (g : (limit F.diagram).toModuleCat →
      ∀ i : Iᵒᵖ, F.diagram.obj i)) := by
    rw [hgrange]
    exact hSclosed.isComplete
  have hcomplete : @CompleteSpace ((limit F.diagram).toModuleCat)
      (IsTopologicalAddGroup.rightUniformSpace _) :=
    (completeSpace_iff_isComplete_range huind).2 hrange
  exact ⟨hcomplete, hT2⟩

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
