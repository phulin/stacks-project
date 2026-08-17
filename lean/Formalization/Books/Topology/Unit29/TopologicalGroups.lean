import Formalization.Books.Topology.Unit22.ProfiniteSpaces
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Topology, Chapter 29: Topological groups

The source's topological-group structure is Mathlib's `IsTopologicalGroup`, and its continuous
homomorphisms are `ContinuousMonoidHom`.  This file adds the bundled category and records the
source-facing constructions and interfaces that are not already bundled by Mathlib.
-/

namespace Formalization.Books.Topology.Unit29

open CategoryTheory CategoryTheory.Limits
open Set Filter _root_.Topology TopologicalSpace

universe u v

noncomputable section

section Basic

variable {G H : Type u}

/- The source definition is exactly Mathlib's `IsTopologicalGroup`: it extends continuity of
  multiplication and inversion. -/

/-- A homomorphism of topological groups, using Mathlib's canonical continuous monoid hom. -/
abbrev TopologicalGroupHom [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] :=
  G →ₜ* H

/-- The quotient topology on the target of a group homomorphism. -/
@[instance_reducible]
def quotientGroupTopology [Group G] [Group H] [TopologicalSpace G]
    (f : G →* H) : TopologicalSpace H :=
  TopologicalSpace.coinduced f inferInstance

/-- A subgroup of a topological group, with its induced topology, is a topological group. -/
theorem topologicalGroup_subgroup [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Subgroup G) : IsTopologicalGroup S := by
  infer_instance

/-- A surjective group quotient with its quotient topology is a topological group. -/
theorem topologicalGroup_surjective_quotient [Group G] [Group H] [TopologicalSpace G]
    [IsTopologicalGroup G] (f : G →* H) (hf : Function.Surjective f) :
    letI : TopologicalSpace H := quotientGroupTopology f
    IsTopologicalGroup H := by
  let _ : TopologicalSpace H := quotientGroupTopology f
  have hq : IsQuotientMap f := ⟨⟨rfl⟩, hf⟩
  have hoq : IsOpenQuotientMap f :=
    MonoidHom.isOpenQuotientMap_of_isQuotientMap hq
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · rw [← (hoq.prodMap hoq).continuous_comp_iff]
    convert hoq.continuous.comp continuous_mul using 1
    ext p
    simp
  · rw [← hoq.continuous_comp_iff]
    exact (show Continuous ((fun a : H => a⁻¹) ∘ f) from by
      convert hoq.continuous.comp continuous_inv using 1
      ext x
      simp)

end Basic

section Automorphisms

variable (E : Type u) [TopologicalSpace E] [DiscreteTopology E]

/-- The compact-open topology on self-maps of a discrete set, presented by its finite-point
topology.  For a discrete domain, this is the canonical Pi topology. -/
@[instance_reducible]
def selfMapTopology : TopologicalSpace (E → E) :=
  let _ := ‹DiscreteTopology E›
  Pi.topologicalSpace

/-- The source's basic neighborhood `U_S(f) = {f' | f'|_S = f|_S}`. -/
def selfMapNeighborhood (f : E → E) (S : Set E) : Set (E → E) :=
  {f' | Set.EqOn f' f S}

/-- The finite-point neighborhoods form a neighborhood basis for the compact-open topology. -/
theorem selfMap_nhds_hasBasis (f : E → E) :
    (𝓝 f).HasBasis (fun S : Set E => S.Finite) (selfMapNeighborhood E f) := by
  change (𝓝 f).HasBasis (fun S : Set E => S.Finite)
    (fun S => {f' | ∀ ⦃x⦄, x ∈ S → f' x = f x})
  rw [nhds_pi, nhds_discrete]
  exact Filter.hasBasis_pi_pure f

/-- Evaluation of self-maps on a discrete set is continuous. -/
theorem selfMap_evaluation_continuous :
    Continuous (fun p : (E → E) × E => p.1 p.2) := by
  refine continuous_def.2 fun U hU => ?_
  change IsOpen {p : (E → E) × E | p.1 p.2 ∈ U}
  rw [show {p : (E → E) × E | p.1 p.2 ∈ U} =
      ⋃ e : E, ((fun f : E → E => f e) ⁻¹' U) ×ˢ ({e} : Set E) by
        ext ⟨f, e'⟩
        simp]
  exact isOpen_iUnion fun e =>
    (hU.preimage (continuous_apply e)).prod (isOpen_discrete _)

omit [DiscreteTopology E] in
/-- A continuous family of maps into a discrete set gives a continuous map into the self-map
space. -/
lemma selfMap_curry_continuous {X : Type v} [TopologicalSpace X]
    (g : X × E → E) (hg : Continuous g) :
    Continuous (fun x : X => fun e : E => g (x, e)) := by
  exact continuous_pi fun e => hg.comp (continuous_id.prodMk continuous_const)

/-- The Pi/compact-open topology is the coarsest topology making evaluation continuous. -/
theorem selfMapTopology_is_coarsest_action_continuous (t : TopologicalSpace (E → E)) :
    @Continuous ((E → E) × E) E
        (@instTopologicalSpaceProd (E → E) E t inferInstance)
        inferInstance (fun p => p.1 p.2) →
      t ≤ selfMapTopology E := by
  sorry

/-- Composition of self-maps is continuous for the compact-open topology. -/
theorem selfMap_composition_continuous :
    Continuous (fun p : (E → E) × (E → E) => p.1 ∘ p.2) := by
  apply continuous_pi
  intro e
  exact (selfMap_evaluation_continuous E).comp
    (continuous_fst.prodMk ((continuous_apply e).comp continuous_snd))

/-- The topology induced on the invertible self-maps from the self-map topology. -/
@[instance_reducible]
def automorphismTopology : TopologicalSpace (Equiv.Perm E) :=
  TopologicalSpace.induced (fun f : Equiv.Perm E => (f : E → E)) (selfMapTopology E)

/-- The source's basic neighborhood restricted to `Aut(E)`. -/
def automorphismNeighborhood (f : Equiv.Perm E) (S : Set E) : Set (Equiv.Perm E) :=
  {f' | Set.EqOn f' f S}

/-- Inversion on `Aut(E)` is continuous. -/
theorem automorphism_inverse_continuous :
    @Continuous (Equiv.Perm E) (Equiv.Perm E)
      (automorphismTopology E) (automorphismTopology E) (fun f => f.symm) := by
  let _ : TopologicalSpace (Equiv.Perm E) := automorphismTopology E
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro e
  rw [continuous_discrete_rng]
  intro a
  have hopen : IsOpen ((fun g : Equiv.Perm E => (g : E → E) a) ⁻¹' ({e} : Set E)) :=
    (isOpen_discrete _).preimage
      ((continuous_apply a).comp (continuous_induced_dom :
        Continuous (fun g : Equiv.Perm E => (g : E → E))))
  convert hopen using 1
  ext g
  exact (Equiv.symm_apply_eq g).trans eq_comm

omit [TopologicalSpace E] [DiscreteTopology E] in
/-- The neighborhood formula for inversion on `Aut(E)`. -/
lemma automorphism_inverse_preimage_neighborhood (f : Equiv.Perm E) (S : Set E) :
    (fun g : Equiv.Perm E => g.symm) ⁻¹' automorphismNeighborhood E f.symm S =
      automorphismNeighborhood E f (f ⁻¹' S) := by
  ext g
  change (∀ ⦃x⦄, x ∈ S → g.symm x = f.symm x) ↔
    (∀ ⦃y⦄, y ∈ f ⁻¹' S → g y = f y)
  constructor
  · intro h y hy
    have h' := h (show f y ∈ S by exact hy)
    simpa using (congrArg g h').symm
  · intro h x hx
    have h' := h (show f (f.symm x) ∈ S by simpa using hx)
    simpa using (congrArg g.symm h').symm

/-- `Aut(E)` with the induced compact-open topology is a topological group. -/
theorem automorphism_is_topological_group :
    @IsTopologicalGroup (Equiv.Perm E) (automorphismTopology E) inferInstance := by
  let _ : TopologicalSpace (Equiv.Perm E) := automorphismTopology E
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply (continuous_induced_rng (f := fun f : Equiv.Perm E => (f : E → E))).2
    have hcoe : @Continuous (Equiv.Perm E) (E → E)
        (automorphismTopology E) (selfMapTopology E)
        (fun f => (f : E → E)) := continuous_induced_dom
    have hmul := (selfMap_composition_continuous E).comp
      ((hcoe.comp continuous_fst).prodMk (hcoe.comp continuous_snd))
    simpa only [Function.comp_def, Equiv.Perm.coe_mul] using hmul
  · exact automorphism_inverse_continuous E

end Automorphisms

section Category

/- There is no generic bundled category of all topological groups in the imported Mathlib API, so
  this is the minimal source-facing bundle. -/

/-- Bundled topological groups and their continuous group homomorphisms. -/
structure TopGroupCat where
  of ::
  α : Type u
  [isGroup : Group α]
  [isTopologicalSpace : TopologicalSpace α]
  [isTopologicalGroup : IsTopologicalGroup α]

namespace TopGroupCat

instance : CoeSort TopGroupCat (Type u) := ⟨TopGroupCat.α⟩

attribute [instance] isGroup isTopologicalSpace isTopologicalGroup

structure Hom (A B : TopGroupCat.{u}) where
  hom' : A →ₜ* B

instance : Category TopGroupCat.{u} where
  Hom A B := Hom A B
  id A := ⟨ContinuousMonoidHom.id A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory TopGroupCat (fun A B => A →ₜ* B) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying continuous monoid homomorphism of a bundled morphism. -/
abbrev Hom.hom {A B : TopGroupCat.{u}} (f : A ⟶ B) : A →ₜ* B :=
  ConcreteCategory.hom (C := TopGroupCat) f

@[simp]
theorem coe_of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (TopGroupCat.of G : Type u) = G := rfl

end TopGroupCat

/-- The forgetful functor from topological groups to topological spaces. -/
def topologicalGroupForgetToTopCat : TopGroupCat.{u} ⥤ TopCat.{u} where
  obj G := TopCat.of G
  map f := TopCat.ofHom ⟨f.hom, f.hom.continuous_toFun⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The forgetful functor from topological groups to groups. -/
def topologicalGroupForgetToGrpCat : TopGroupCat.{u} ⥤ GrpCat.{u} where
  obj G := GrpCat.of G
  map f := GrpCat.ofHom f.hom.toMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

theorem topological_groups_have_limits : HasLimits (TopGroupCat.{u}) := by
  sorry

theorem topological_group_limits_commute_with_topological_spaces :
    PreservesLimits (topologicalGroupForgetToTopCat.{u}) := by
  sorry

theorem topological_group_limits_commute_with_groups :
    PreservesLimits (topologicalGroupForgetToGrpCat.{u}) := by
  sorry

theorem topological_groups_have_colimits : HasColimits (TopGroupCat.{u}) := by
  sorry

theorem topological_group_colimits_commute_with_groups :
    PreservesColimits (topologicalGroupForgetToGrpCat.{u}) := by
  sorry

/-- For a sequential diagram, the source's underlying-set comparison between the topological-group
colimit and the topological-space colimit.  The source warns that the induced topologies need not
agree; this declaration records the carrier comparison without asserting a false equality of
topologies. -/
theorem topological_group_sequence_colimit_carrier_comparison
    (F : ℕ ⥤ TopGroupCat.{u}) [HasColimit F]
    [HasColimit (F ⋙ topologicalGroupForgetToTopCat.{u})] :
    Nonempty (((colimit F : TopGroupCat.{u}) : Type u) ≃
      ((colimit (F ⋙ topologicalGroupForgetToTopCat) : TopCat.{u}) : Type u)) := by
  sorry

end Category

section Profinite

/-- The source's profinite-group predicate, using the canonical profinite-space predicate from
Chapter 22. -/
def IsProfiniteGroup {G : Type u} [Group G] [TopologicalSpace G]
    [hG : IsTopologicalGroup G] : Prop :=
  let _ := hG
  Formalization.Books.Topology.Unit22.IsProfiniteSpace G

/-- A source-facing presentation of a topological group as a limit of finite discrete topological
groups. -/
structure FiniteDiscreteTopologicalGroupLimitPresentation
    {G : Type u} [Group G] [TopologicalSpace G]
    [hG : IsTopologicalGroup G] where
  index : Type u
  [category : SmallCategory index]
  diagram : index ⥤ TopGroupCat.{u}
  cone : Cone diagram
  finite_discrete : ∀ j, Finite (diagram.obj j) ∧ DiscreteTopology (diagram.obj j)
  comparison : Nonempty (let _ := hG; G ≃ₜ* (cone.pt : Type u))
  is_limit : IsLimit cone

/-- A source-facing cofiltered finite-discrete limit presentation. -/
structure CofilteredFiniteDiscreteTopologicalGroupLimitPresentation
    {G : Type u} [Group G] [TopologicalSpace G]
    [hG : IsTopologicalGroup G] where
  index : Type u
  [category : SmallCategory index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ TopGroupCat.{u}
  cone : Cone diagram
  finite_discrete : ∀ j, Finite (diagram.obj j) ∧ DiscreteTopology (diagram.obj j)
  comparison : Nonempty (let _ := hG; G ≃ₜ* (cone.pt : Type u))
  is_limit : IsLimit cone

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def IsLimitOfFiniteDiscreteTopologicalGroups : Prop :=
  Nonempty (FiniteDiscreteTopologicalGroupLimitPresentation (G := G))

def IsCofilteredLimitOfFiniteDiscreteTopologicalGroups : Prop :=
  Nonempty (CofilteredFiniteDiscreteTopologicalGroupLimitPresentation (G := G))

theorem profiniteGroup_iff_finite_discrete_limit :
    IsProfiniteGroup (G := G) ↔ IsLimitOfFiniteDiscreteTopologicalGroups (G := G) := by
  sorry

theorem profiniteGroup_iff_cofiltered_finite_discrete_limit :
    IsProfiniteGroup (G := G) ↔ IsCofilteredLimitOfFiniteDiscreteTopologicalGroups (G := G) := by
  sorry

theorem profiniteGroup_exists_open_subgroup_subset_nhds_one
    (hG : IsProfiniteGroup (G := G)) {E : Set G} (hE : E ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, (H : Set G) ⊆ E := by
  have hprops :=
    Formalization.Books.Topology.Unit22.isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mp
      hG
  let _ : T2Space G := hprops.1
  let _ : CompactSpace G := hprops.2.1
  let _ : TotallyDisconnectedSpace G := hprops.2.2
  rcases mem_nhds_iff.mp hE with ⟨U, hUE, hUopen, h1U⟩
  obtain ⟨N, hN⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUopen h1U
  exact ⟨N.toOpenSubgroup, hN.trans hUE⟩

theorem profiniteGroup_open_subgroup_finite_index
    (hG : IsProfiniteGroup (G := G)) (H : Subgroup G)
    (hH : IsOpen (H : Set G)) : H.FiniteIndex := by
  have hprops :=
    Formalization.Books.Topology.Unit22.isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mp
      hG
  let _ : CompactSpace G := hprops.2.1
  let _ : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
  exact Subgroup.finiteIndex_of_finite_quotient

theorem profiniteGroup_exists_open_normal_subgroup_subset
    (hG : IsProfiniteGroup (G := G)) (H : OpenSubgroup G) :
    ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ H := by
  have hprops :=
    Formalization.Books.Topology.Unit22.isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mp
      hG
  let _ : CompactSpace G := hprops.2.1
  let _ : TotallyDisconnectedSpace G := hprops.2.2
  exact ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one H.isOpen H.one_mem

theorem profiniteGroup_open_normal_subgroup_finite_index
    (hG : IsProfiniteGroup (G := G)) (N : OpenNormalSubgroup G) :
    (N : Subgroup G).FiniteIndex := by
  exact profiniteGroup_open_subgroup_finite_index hG (N : Subgroup G) N.isOpen

theorem profiniteGroup_open_normal_quotient_finite_discrete
    (hG : IsProfiniteGroup (G := G)) (N : OpenNormalSubgroup G) :
    Finite (G ⧸ (N : Subgroup G)) ∧ DiscreteTopology (G ⧸ (N : Subgroup G)) := by
  have hprops :=
    Formalization.Books.Topology.Unit22.isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mp
      hG
  let _ : CompactSpace G := hprops.2.1
  have hfinite : Finite (G ⧸ (N : Subgroup G)) :=
    (N : Subgroup G).quotient_finite_of_isOpen N.isOpen
  let _ : DiscreteTopology (G ⧸ (N : Subgroup G)) :=
    QuotientGroup.discreteTopology N.isOpen
  exact ⟨hfinite, inferInstance⟩

theorem profiniteGroup_open_normal_quotient_finite_discrete_topological_group
    (hG : IsProfiniteGroup (G := G)) (N : OpenNormalSubgroup G) :
    Finite (G ⧸ (N : Subgroup G)) ∧ DiscreteTopology (G ⧸ (N : Subgroup G)) ∧
      IsTopologicalGroup (G ⧸ (N : Subgroup G)) ∧
        Function.Surjective (QuotientGroup.mk : G → G ⧸ (N : Subgroup G)) := by
  have hfinite_discrete := profiniteGroup_open_normal_quotient_finite_discrete hG N
  refine ⟨hfinite_discrete.1, hfinite_discrete.2, inferInstance, ?_⟩
  exact QuotientGroup.mk_surjective

omit [IsTopologicalGroup G] in
/- Intersections of open normal subgroups are again open normal and give lower bounds, the
cofilteredness assertion used by the source. -/
lemma open_normal_subgroup_intersection
    (H K : OpenNormalSubgroup G) :
    ∃ N : OpenNormalSubgroup G, N ≤ H ∧ N ≤ K := by
  exact ⟨H ⊓ K, inf_le_left, inf_le_right⟩

/-- The canonical finite-quotient limit cone for a bundled profinite group. -/
noncomputable def profiniteGroup_finite_quotient_limit_cone (P : ProfiniteGrp.{u}) :
    Cone (ProfiniteGrp.diagram P) :=
  ProfiniteGrp.cone P

/-- The canonical quotient projection occurring in the finite-quotient diagram. -/
def profiniteGroup_finite_quotient_projection (P : ProfiniteGrp.{u})
    (N : OpenNormalSubgroup P) : P ⟶ (ProfiniteGrp.diagram P).obj N :=
  ProfiniteGrp.proj N

theorem profiniteGroup_finite_quotient_projection_continuous (P : ProfiniteGrp.{u})
    (N : OpenNormalSubgroup P) :
    Continuous (profiniteGroup_finite_quotient_projection P N).hom := by
  exact (profiniteGroup_finite_quotient_projection P N).hom.continuous_toFun

/-- The canonical map from a profinite group to its finite-quotient limit is a topological-group
isomorphism.  The `ContinuousMulEquiv` packages continuity, injectivity, surjectivity, and the
homeomorphism asserted in the source proof. -/
noncomputable def profiniteGroup_finite_quotient_limit_equiv (P : ProfiniteGrp.{u}) :
    (P : Type u) ≃ₜ* (ProfiniteGrp.limit (ProfiniteGrp.diagram P) : Type u) :=
  ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P

noncomputable def profiniteGroup_finite_quotient_limit_is_limit (P : ProfiniteGrp.{u}) :
    IsLimit (profiniteGroup_finite_quotient_limit_cone P) :=
  ProfiniteGrp.isLimitCone P

theorem profiniteGroup_finite_quotient_limit_map_continuous (P : ProfiniteGrp.{u}) :
    Continuous (profiniteGroup_finite_quotient_limit_equiv P) := by
  exact (profiniteGroup_finite_quotient_limit_equiv P).continuous_toFun

theorem profiniteGroup_finite_quotient_limit_map_injective (P : ProfiniteGrp.{u}) :
    Function.Injective (profiniteGroup_finite_quotient_limit_equiv P) := by
  exact (profiniteGroup_finite_quotient_limit_equiv P).injective

theorem profiniteGroup_finite_quotient_limit_map_surjective (P : ProfiniteGrp.{u}) :
    Function.Surjective (profiniteGroup_finite_quotient_limit_equiv P) := by
  exact (profiniteGroup_finite_quotient_limit_equiv P).surjective

end Profinite

end

end Formalization.Books.Topology.Unit29
