import Formalization.Books.Topology.Unit22.ProfiniteSpaces
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.CoprodI
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.GroupTopology
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Adjunction.Limits

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
  intro h
  change t ≤ ⨅ e : E, TopologicalSpace.induced (fun f : E → E => f e) inferInstance
  refine le_iInf fun e => ?_
  apply continuous_iff_le_induced.mp
  exact h.comp (continuous_id.prodMk continuous_const)

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

private noncomputable def topGroupLimitCone {J : Type u} [Category.{u} J]
    (F : J ⥤ TopGroupCat.{u}) : Cone F := by
  let G := F ⋙ topologicalGroupForgetToGrpCat
  let c := GrpCat.limitCone G
  letI : TopologicalSpace (c.pt : Type u) :=
    ⨅ j, (F.obj j).isTopologicalSpace.induced (c.π.app j).hom
  letI : IsTopologicalGroup (c.pt : Type u) :=
    topologicalGroup_iInf fun j =>
      letI : Group (G.obj j) := (F.obj j).isGroup
      letI : TopologicalSpace (G.obj j) := (F.obj j).isTopologicalSpace
      letI : IsTopologicalGroup (G.obj j) := (F.obj j).isTopologicalGroup
      topologicalGroup_induced (c.π.app j).hom
  let L : TopGroupCat.{u} := TopGroupCat.of (c.pt : Type u)
  let p (j : J) : L ⟶ F.obj j :=
    ⟨⟨(c.π.app j).hom, continuous_iff_le_induced.mpr (iInf_le _ j)⟩⟩
  exact
    { pt := L
      π :=
        { app := p
          naturality := fun X Y f => by
            ext x
            exact congr($(c.π.naturality f).hom x) } }

private noncomputable def topGroupLimitConeIsLimit {J : Type u} [Category.{u} J]
    (F : J ⥤ TopGroupCat.{u}) : IsLimit (topGroupLimitCone F) := by
  let G := F ⋙ topologicalGroupForgetToGrpCat
  let c := GrpCat.limitCone G
  letI : TopologicalSpace (c.pt : Type u) :=
    ⨅ j, (F.obj j).isTopologicalSpace.induced (c.π.app j).hom
  letI : IsTopologicalGroup (c.pt : Type u) :=
    topologicalGroup_iInf fun j =>
      letI : Group (G.obj j) := (F.obj j).isGroup
      letI : TopologicalSpace (G.obj j) := (F.obj j).isTopologicalSpace
      letI : IsTopologicalGroup (G.obj j) := (F.obj j).isTopologicalGroup
      topologicalGroup_induced (c.π.app j).hom
  letI : topologicalGroupForgetToGrpCat.Faithful :=
    ⟨fun {_ _} f g h => by
      cases f with
      | mk f =>
        cases g with
        | mk g =>
          congr
          apply ContinuousMonoidHom.ext
          intro x
          exact congrArg (fun q => q.hom x) h⟩
  let hcone : GrpCat.limitCone G ≅
      topologicalGroupForgetToGrpCat.mapCone (topGroupLimitCone F) :=
    Cone.ext (Iso.refl _) (fun j => by
      ext x
      rfl)
  refine IsLimit.ofFaithful topologicalGroupForgetToGrpCat
    (ht := (GrpCat.limitConeIsLimit G).ofIsoLimit hcone)
    (lift := fun s => by
      let sG : Cone G :=
        { pt := GrpCat.of (s.pt : Type u)
          π :=
            { app := fun j => GrpCat.ofHom (s.π.app j).hom.toMonoidHom
              naturality := fun X Y f => by
                ext x
                exact congr($(s.π.naturality f).hom x) } }
      let q := (GrpCat.limitConeIsLimit G).lift
        sG
      refine { hom' := ?_ }
      refine { toMonoidHom := q.hom, continuous_toFun := ?_ }
      rw [continuous_iff_le_induced]
      change s.pt.isTopologicalSpace ≤
        TopologicalSpace.induced q.hom
          (⨅ j, (F.obj j).isTopologicalSpace.induced (c.π.app j).hom)
      rw [induced_iInf]
      refine le_iInf fun j => ?_
      let tj : TopologicalSpace (G.obj j) := (F.obj j).isTopologicalSpace
      change s.pt.isTopologicalSpace ≤
        TopologicalSpace.induced q.hom
          (TopologicalSpace.induced (c.π.app j).hom
            tj)
      rw [induced_compose (f := q.hom) (g := (c.π.app j).hom),
        ← continuous_iff_le_induced]
      change Continuous
        ((GrpCat.limitConeIsLimit G).lift
          sG ≫ c.π.app j).hom
      rw [(GrpCat.limitConeIsLimit G).fac]
      change Continuous (s.π.app j).hom
      exact (s.π.app j).hom.continuous_toFun) ?_
  intro s
  ext x
  rfl

private noncomputable def topGroupLimitConeForgetGrpIsLimit {J : Type u} [Category.{u} J]
    (F : J ⥤ TopGroupCat.{u}) :
    IsLimit (topologicalGroupForgetToGrpCat.mapCone (topGroupLimitCone F)) := by
  let G := F ⋙ topologicalGroupForgetToGrpCat
  let hcone : GrpCat.limitCone G ≅
      topologicalGroupForgetToGrpCat.mapCone (topGroupLimitCone F) :=
    Cone.ext (Iso.refl _) (fun j => by
      ext x
      rfl)
  exact (GrpCat.limitConeIsLimit G).ofIsoLimit hcone

private noncomputable def topGroupLimitConeForgetTopIsLimit {J : Type u} [Category.{u} J]
    (F : J ⥤ TopGroupCat.{u}) :
    IsLimit (topologicalGroupForgetToTopCat.mapCone (topGroupLimitCone F)) := by
  let hgrp := topGroupLimitConeForgetGrpIsLimit F
  let hset : IsLimit ((CategoryTheory.forget (GrpCat.{u})).mapCone
      (topologicalGroupForgetToGrpCat.mapCone (topGroupLimitCone F))) :=
    isLimitOfPreserves (CategoryTheory.forget (GrpCat.{u})) hgrp
  let hcone : ((CategoryTheory.forget (GrpCat.{u})).mapCone
      (topologicalGroupForgetToGrpCat.mapCone (topGroupLimitCone F))) ≅
      ((CategoryTheory.forget (TopCat.{u})).mapCone
        (topologicalGroupForgetToTopCat.mapCone (topGroupLimitCone F))) :=
    Cone.ext (Iso.refl _) (fun j => by rfl)
  let hset' := hset.ofIsoLimit hcone
  exact Classical.choice ((TopCat.nonempty_isLimit_iff_eq_induced
    (topologicalGroupForgetToTopCat.mapCone (topGroupLimitCone F)) hset').2 (by
      rfl))

theorem topological_groups_have_limits : HasLimits (TopGroupCat.{u}) := by
  refine { has_limits_of_shape := fun J _ => ?_ }
  exact { has_limit := fun F => ⟨⟨topGroupLimitCone F, topGroupLimitConeIsLimit F⟩⟩ }

theorem topological_group_limits_commute_with_topological_spaces :
    PreservesLimits (topologicalGroupForgetToTopCat.{u}) := by
  refine { preservesLimitsOfShape := fun {J} _ => ?_ }
  refine { preservesLimit := fun {F} => ?_ }
  exact preservesLimit_of_preserves_limit_cone (topGroupLimitConeIsLimit F)
    (topGroupLimitConeForgetTopIsLimit F)

theorem topological_group_limits_commute_with_groups :
    PreservesLimits (topologicalGroupForgetToGrpCat.{u}) := by
  refine { preservesLimitsOfShape := fun {J} _ => ?_ }
  refine { preservesLimit := fun {F} => ?_ }
  exact preservesLimit_of_preserves_limit_cone (topGroupLimitConeIsLimit F)
    (topGroupLimitConeForgetGrpIsLimit F)

private noncomputable def topGroupCoproductCarrier {ι : Type u}
    (X : ι → TopGroupCat.{u}) : Type u :=
  Monoid.CoprodI fun i => (X i : Type u)

private noncomputable def topGroupCoproductGroup {ι : Type u}
    (X : ι → TopGroupCat.{u}) : Group (topGroupCoproductCarrier X) := by
  letI : ∀ i, Group (X i : Type u) := fun i => (X i).isGroup
  change Group (Monoid.CoprodI (fun i => (X i : Type u)))
  exact inferInstance

private noncomputable instance topGroupCoproductGroupInstance {ι : Type u}
    (X : ι → TopGroupCat.{u}) : Group (topGroupCoproductCarrier X) :=
  topGroupCoproductGroup X

private noncomputable def topGroupCoproductInjection {ι : Type u}
    (X : ι → TopGroupCat.{u}) (i : ι) :
    (X i : Type u) →* topGroupCoproductCarrier X := by
  letI : ∀ i, Group (X i : Type u) := fun i => (X i).isGroup
  change (X i : Type u) →* Monoid.CoprodI (fun i => (X i : Type u))
  exact Monoid.CoprodI.of (M := fun i => (X i : Type u)) (i := i)

private noncomputable def topGroupCoproductGroupTopology {ι : Type u}
  (X : ι → TopGroupCat.{u}) : GroupTopology (topGroupCoproductCarrier X) := by
  letI : ∀ i, Group (X i : Type u) := fun i => (X i).isGroup
  exact GroupTopology.coinduced (fun x : Σ i, X i =>
    topGroupCoproductInjection X x.1 x.2)

private noncomputable def topGroupCoproductCocone {ι : Type u}
    (X : ι → TopGroupCat.{u}) : Cocone (Discrete.functor X) := by
  let A := topGroupCoproductCarrier X
  let T := topGroupCoproductGroupTopology X
  letI : Group A := topGroupCoproductGroup X
  letI : TopologicalSpace A := T.toTopologicalSpace
  letI : IsTopologicalGroup A := T.toIsTopologicalGroup
  let L : TopGroupCat.{u} := TopGroupCat.of A
  let p (i : ι) : X i ⟶ L :=
    ⟨⟨topGroupCoproductInjection X i, by
      change Continuous ((fun x : Σ i, X i =>
        topGroupCoproductInjection X x.1 x.2) ∘ Sigma.mk i)
      exact (GroupTopology.coinduced_continuous _).comp continuous_sigmaMk⟩⟩
  exact
    { pt := L
      ι :=
        { app := fun i => p i.as
          naturality := by
            rintro ⟨i⟩ ⟨j⟩ ⟨⟨h⟩⟩
            cases h
            rfl } }

private noncomputable def topGroupCoproductCoconeIsColimit {ι : Type u}
    (X : ι → TopGroupCat.{u}) : IsColimit (topGroupCoproductCocone X) := by
  let A := topGroupCoproductCarrier X
  let f : (Σ i, X i) → A := fun x => topGroupCoproductInjection X x.1 x.2
  let T := topGroupCoproductGroupTopology X
  letI : Group A := topGroupCoproductGroup X
  letI : TopologicalSpace A := T.toTopologicalSpace
  letI : IsTopologicalGroup A := T.toIsTopologicalGroup
  let qi (s : Cocone (Discrete.functor X)) (i : ι) : X i ⟶ s.pt :=
    eqToHom (Discrete.functor_obj X i).symm ≫ s.ι.app (Discrete.mk i)
  let q (s : Cocone (Discrete.functor X)) : A →* (s.pt : Type u) :=
    Monoid.CoprodI.lift (M := fun i => (X i : Type u))
      (fun i => (qi s i).hom.toMonoidHom)
  let qContinuous (s : Cocone (Discrete.functor X)) :
      Continuous (q s) := by
    rw [continuous_iff_le_induced]
    have hgroup : @IsTopologicalGroup A (TopologicalSpace.induced (q s)
        s.pt.isTopologicalSpace) _ := topologicalGroup_induced (q s)
    have hcomp : Continuous (q s ∘ f) := by
      apply continuous_sigma
      intro i
      change Continuous (fun a : (X i : Type u) =>
        q s (topGroupCoproductInjection X i a))
      have hi := (qi s i).hom.continuous_toFun
      rw [show (fun a : (X i : Type u) =>
          q s (topGroupCoproductInjection X i a)) =
          fun a => (qi s i).hom a by
        funext a
        change (Monoid.CoprodI.lift
          (M := fun i => (X i : Type u))
          (fun i => (qi s i).hom.toMonoidHom)
          (Monoid.CoprodI.of a)) = _
        rw [Monoid.CoprodI.lift_of]
        rfl]
      exact hi
    have hle : TopologicalSpace.coinduced f inferInstance ≤
        TopologicalSpace.induced (q s) s.pt.isTopologicalSpace := by
      exact continuous_iff_coinduced_le.mp
        (continuous_induced_rng.mpr hcomp)
    change (topGroupCoproductGroupTopology X).toTopologicalSpace ≤
      TopologicalSpace.induced (q s) s.pt.isTopologicalSpace
    exact (show topGroupCoproductGroupTopology X ≤
        ⟨TopologicalSpace.induced (q s) s.pt.isTopologicalSpace, hgroup⟩ from
      by
        unfold topGroupCoproductGroupTopology
        exact sInf_le hle)
  refine
    { desc := fun s => ⟨⟨q s, qContinuous s⟩⟩
      fac := fun s i => by
        ext x
        cases i with
        | mk i =>
          change q s (topGroupCoproductInjection X i x) = _
          change (Monoid.CoprodI.lift
            (M := fun i => (X i : Type u))
            (fun i => (qi s i).hom.toMonoidHom)
            (Monoid.CoprodI.of x)) = _
          rw [Monoid.CoprodI.lift_of]
          simp [qi]
      uniq := fun s m hm => by
        cases m with
        | mk m =>
          have hmon : m.toMonoidHom = q s := by
            apply Monoid.CoprodI.ext_hom
            intro i
            ext x
            have hi := congrArg (fun k => k.hom x) (hm (Discrete.mk i))
            change m (topGroupCoproductInjection X i x) =
              (s.ι.app (Discrete.mk i)).hom x at hi
            change m (topGroupCoproductInjection X i x) =
              q s (topGroupCoproductInjection X i x)
            change m (Monoid.CoprodI.of x) =
              (Monoid.CoprodI.lift
                (M := fun i => (X i : Type u))
                (fun i => (qi s i).hom.toMonoidHom)
                (Monoid.CoprodI.of x))
            rw [Monoid.CoprodI.lift_of]
            change m (topGroupCoproductInjection X i x) = (qi s i).hom x
            simpa [qi] using hi
          congr
          apply ContinuousMonoidHom.toMonoidHom_injective
          exact hmon }

private noncomputable def topGroupCoequalizerNormal {A B : TopGroupCat.{u}}
    (f g : A ⟶ B) : Subgroup (B : Type u) :=
  Subgroup.normalClosure (Set.range (fun a : (A : Type u) => f.hom a / g.hom a))

private noncomputable instance topGroupCoequalizerNormalNormal {A B : TopGroupCat.{u}}
    (f g : A ⟶ B) : (topGroupCoequalizerNormal f g).Normal :=
  Subgroup.normalClosure_normal

private noncomputable def topGroupCoequalizerGroupTopology {A B : TopGroupCat.{u}}
    (f g : A ⟶ B) : GroupTopology
      ((B : Type u) ⧸ topGroupCoequalizerNormal f g) := by
  exact GroupTopology.coinduced (QuotientGroup.mk' (topGroupCoequalizerNormal f g))

private noncomputable def topGroupCoequalizerCofork {A B : TopGroupCat.{u}}
    (f g : A ⟶ B) : Cofork f g := by
  let N := topGroupCoequalizerNormal f g
  let Q := (B : Type u) ⧸ N
  let T := topGroupCoequalizerGroupTopology f g
  letI : TopologicalSpace Q := T.toTopologicalSpace
  letI : IsTopologicalGroup Q := T.toIsTopologicalGroup
  let q : (B : Type u) →* Q := QuotientGroup.mk' N
  let p : B ⟶ TopGroupCat.of Q :=
    ⟨⟨q, by
      exact GroupTopology.coinduced_continuous q⟩⟩
  exact Cofork.ofπ p (by
    ext x
    apply (QuotientGroup.eq_iff_div_mem).2
    change f.hom x / g.hom x ∈ N
    exact Subgroup.subset_normalClosure ⟨x, rfl⟩)

private theorem topGroupCoequalizerNormal_le_ker {A B : TopGroupCat.{u}}
    (f g : A ⟶ B) (s : Cofork f g) :
    topGroupCoequalizerNormal f g ≤ s.π.hom.toMonoidHom.ker := by
  apply Subgroup.normalClosure_le_normal
  intro x hx
  rcases hx with ⟨a, rfl⟩
  apply MonoidHom.mem_ker.mpr
  have hc := congrArg (fun k => k.hom a) s.condition
  have hc' : s.π.hom.toMonoidHom (f.hom a) =
      s.π.hom.toMonoidHom (g.hom a) := by
    simpa using hc
  rw [map_div, hc']
  simp

private noncomputable def topGroupCoequalizerDesc {A B : TopGroupCat.{u}}
    (f g : A ⟶ B) (s : Cofork f g) :
    (topGroupCoequalizerCofork f g).pt ⟶ s.pt := by
  let N := topGroupCoequalizerNormal f g
  let Q := (B : Type u) ⧸ N
  let T := topGroupCoequalizerGroupTopology f g
  letI : TopologicalSpace Q := T.toTopologicalSpace
  letI : IsTopologicalGroup Q := T.toIsTopologicalGroup
  let h : (B : Type u) →* (s.pt : Type u) := s.π.hom.toMonoidHom
  have hN : N ≤ h.ker := topGroupCoequalizerNormal_le_ker f g s
  let l : Q →* (s.pt : Type u) := QuotientGroup.lift N h hN
  have hlcomp : Continuous (l ∘ QuotientGroup.mk' N) := by
    have heq : l ∘ QuotientGroup.mk' N = h := by
      funext x
      exact QuotientGroup.lift_mk' N hN x
    rw [heq]
    exact s.π.hom.continuous_toFun
  have hl : Continuous l := by
    rw [continuous_iff_le_induced]
    have hgroup : @IsTopologicalGroup Q (TopologicalSpace.induced l
        s.pt.isTopologicalSpace) _ := topologicalGroup_induced l
    have hle : TopologicalSpace.coinduced (QuotientGroup.mk' N) inferInstance ≤
        TopologicalSpace.induced l s.pt.isTopologicalSpace :=
      continuous_iff_coinduced_le.mp (continuous_induced_rng.mpr hlcomp)
    change T.toTopologicalSpace ≤ TopologicalSpace.induced l s.pt.isTopologicalSpace
    exact (show T ≤ ⟨TopologicalSpace.induced l s.pt.isTopologicalSpace, hgroup⟩ from by
      dsimp [T, topGroupCoequalizerGroupTopology]
      exact sInf_le hle)
  exact ⟨⟨l, hl⟩⟩

private noncomputable def topGroupCoequalizerCoforkIsColimit {A B : TopGroupCat.{u}}
    (f g : A ⟶ B) : IsColimit (topGroupCoequalizerCofork f g) := by
  let N := topGroupCoequalizerNormal f g
  let t := topGroupCoequalizerCofork f g
  refine Cofork.IsColimit.mk t (fun s => topGroupCoequalizerDesc f g s) ?_ ?_
  · intro s
    ext x
    change (QuotientGroup.lift N s.π.hom.toMonoidHom
      (topGroupCoequalizerNormal_le_ker f g s))
        (QuotientGroup.mk' N x) = s.π.hom.toMonoidHom x
    exact QuotientGroup.lift_mk' N
      (topGroupCoequalizerNormal_le_ker f g s) x
  · intro s m hm
    cases m with
    | mk m =>
      congr
      apply ContinuousMonoidHom.ext
      intro x
      refine QuotientGroup.induction_on x ?_
      intro b
      have hm' := congrArg (fun k => k.hom b) hm
      change m (QuotientGroup.mk' (topGroupCoequalizerNormal f g) b) =
        (QuotientGroup.lift (topGroupCoequalizerNormal f g)
          s.π.hom.toMonoidHom (topGroupCoequalizerNormal_le_ker f g s))
          (QuotientGroup.mk' (topGroupCoequalizerNormal f g) b)
      change m (b : (B : Type u) ⧸ topGroupCoequalizerNormal f g) =
        (QuotientGroup.lift (topGroupCoequalizerNormal f g)
          s.π.hom.toMonoidHom (topGroupCoequalizerNormal_le_ker f g s))
          (b : (B : Type u) ⧸ topGroupCoequalizerNormal f g)
      rw [QuotientGroup.lift_mk]
      change m (QuotientGroup.mk' (topGroupCoequalizerNormal f g) b) =
        s.π.hom.toMonoidHom b at hm'
      exact hm'

private theorem topological_groups_have_coproducts :
    HasCoproducts.{u} (TopGroupCat.{u}) := by
  intro ι
  refine { has_colimit := fun F => ?_ }
  let X : ι → TopGroupCat.{u} := fun i => F.obj (Discrete.mk i)
  have hF : Discrete.functor X = F := Discrete.functor_ext (fun i => rfl)
  rw [← hF]
  exact ⟨topGroupCoproductCocone X, topGroupCoproductCoconeIsColimit X⟩

private theorem topological_groups_have_coequalizers :
    HasCoequalizers (TopGroupCat.{u}) := by
  refine { has_colimit := fun F => ?_ }
  let : HasColimit (parallelPair (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)) :=
    ⟨topGroupCoequalizerCofork (F.map WalkingParallelPairHom.left)
        (F.map WalkingParallelPairHom.right),
      topGroupCoequalizerCoforkIsColimit (F.map WalkingParallelPairHom.left)
        (F.map WalkingParallelPairHom.right)⟩
  exact hasColimit_of_iso (diagramIsoParallelPair F)

theorem topological_groups_have_colimits : HasColimits (TopGroupCat.{u}) := by
  let : HasCoproducts.{u} (TopGroupCat.{u}) := topological_groups_have_coproducts
  let : HasCoequalizers (TopGroupCat.{u}) := topological_groups_have_coequalizers
  exact has_colimits_of_hasCoequalizers_and_coproducts

private noncomputable def topologicalGroupIndiscrete : GrpCat.{u} ⥤ TopGroupCat.{u} where
  obj G := by
    letI : TopologicalSpace (G : Type u) := ⊤
    exact TopGroupCat.of (G : Type u)
  map f := ⟨⟨f.hom, continuous_of_indiscreteTopology⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable def topologicalGroupForgetIndiscreteAdjunction :
    topologicalGroupForgetToGrpCat.{u} ⊣ topologicalGroupIndiscrete :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun := fun f =>
            letI : IndiscreteTopology (topologicalGroupIndiscrete.obj Y).α := ⟨rfl⟩
            ⟨⟨f.hom, continuous_of_indiscreteTopology⟩⟩
          invFun := fun f => GrpCat.ofHom f.hom.toMonoidHom
          left_inv := by
            intro f
            rfl
          right_inv := by
            intro f
            rfl }
      homEquiv_naturality_left_symm := by
        intros
        ext x
        rfl }

theorem topological_group_colimits_commute_with_groups :
    PreservesColimits (topologicalGroupForgetToGrpCat.{u}) := by
  exact topologicalGroupForgetIndiscreteAdjunction.leftAdjoint_preservesColimits

/-- For a sequential diagram, the source's underlying-set comparison between the topological-group
colimit and the topological-space colimit.  The source warns that the induced topologies need not
agree; this declaration records the carrier comparison without asserting a false equality of
topologies. -/
theorem topological_group_sequence_colimit_carrier_comparison
    (F : ℕ ⥤ TopGroupCat.{u}) [HasColimit F]
    [HasColimit (F ⋙ topologicalGroupForgetToTopCat.{u})] :
    Nonempty (((colimit F : TopGroupCat.{u}) : Type u) ≃
      ((colimit (F ⋙ topologicalGroupForgetToTopCat) : TopCat.{u}) : Type u)) := by
  let : PreservesColimits (topologicalGroupForgetToGrpCat.{u}) :=
    topological_group_colimits_commute_with_groups
  let : PreservesColimitsOfSize.{0, 0} (topologicalGroupForgetToGrpCat.{u}) :=
    preservesSmallestColimits_of_preservesColimits _
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget GrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let Fg := F ⋙ topologicalGroupForgetToGrpCat
  let Ft := F ⋙ topologicalGroupForgetToTopCat
  have hgroup : IsColimit
      (topologicalGroupForgetToGrpCat.mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves topologicalGroupForgetToGrpCat (colimit.isColimit F)
  have htype_group : IsColimit
      ((forget GrpCat.{u}).mapCocone
        (topologicalGroupForgetToGrpCat.mapCocone (colimit.cocone F))) :=
    isColimitOfPreserves (forget GrpCat.{u}) hgroup
  have htype_top : IsColimit
      ((forget TopCat.{u}).mapCocone (colimit.cocone Ft)) :=
    isColimitOfPreserves (forget TopCat.{u}) (colimit.isColimit Ft)
  exact ⟨(htype_group.coconePointUniqueUpToIso htype_top).toEquiv⟩

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

private def profiniteGrpToTopGroup : ProfiniteGrp.{u} ⥤ TopGroupCat.{u} where
  obj P := TopGroupCat.of P
  map f := ⟨f.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem test_profiniteGrp_toLimit_coordinate (P : ProfiniteGrp.{u})
    (N : OpenNormalSubgroup P) (x : P) :
    (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P x).val N =
      (ProfiniteGrp.proj N) x := by
  rfl

private noncomputable def profiniteGrpFiniteQuotientLift {P : ProfiniteGrp.{u}}
    (s : Cone (ProfiniteGrp.diagram P ⋙ profiniteGrpToTopGroup)) :
    (s.pt : Type u) →* ProfiniteGrp.limit (ProfiniteGrp.diagram P) := by
  refine {
    toFun := fun x => ⟨fun j => (s.π.app j).hom x, ?_⟩
    map_one' := ?_
    map_mul' := ?_ }
  · intro i j f
    change (P.diagram.map f).hom ((s.π.app i).hom x) = (s.π.app j).hom x
    have hn := congrArg (fun q => q x) (s.π.naturality f)
    change (s.π.app j).hom x = (P.diagram.map f).hom ((s.π.app i).hom x) at hn
    exact hn.symm
  · apply ProfiniteGrp.limit_ext
    intro j
    exact (s.π.app j).hom.map_one
  · intro x y
    apply ProfiniteGrp.limit_ext
    intro j
    exact (s.π.app j).hom.map_mul x y

private theorem profiniteGrpFiniteQuotientLift_continuous {P : ProfiniteGrp.{u}}
    (s : Cone (ProfiniteGrp.diagram P ⋙ profiniteGrpToTopGroup)) :
    Continuous (profiniteGrpFiniteQuotientLift s) := by
  apply continuous_induced_rng.mpr (continuous_pi _)
  intro j
  exact (s.π.app j).hom.continuous_toFun

private noncomputable def profiniteGrpFiniteQuotientTopGroupLift (P : ProfiniteGrp.{u})
    (s : Cone (ProfiniteGrp.diagram P ⋙ profiniteGrpToTopGroup)) :
    s.pt ⟶ profiniteGrpToTopGroup.obj P := by
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  let qL : (s.pt : Type u) →ₜ* ProfiniteGrp.limit (ProfiniteGrp.diagram P) := {
    toMonoidHom := profiniteGrpFiniteQuotientLift s
    continuous_toFun := profiniteGrpFiniteQuotientLift_continuous s }
  let eHom : ProfiniteGrp.limit (ProfiniteGrp.diagram P) →ₜ* P := {
    toMonoidHom := e.symm.toMulEquiv.toMonoidHom
    continuous_toFun := e.symm.continuous_toFun }
  exact ⟨eHom.comp qL⟩

private noncomputable def profiniteGrpFiniteQuotientConeIsLimit (P : ProfiniteGrp.{u}) :
    IsLimit (profiniteGrpToTopGroup.mapCone (ProfiniteGrp.cone P)) := by
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  refine {
    lift := fun s => profiniteGrpFiniteQuotientTopGroupLift P s
    fac := fun s j => by
      let qL := profiniteGrpFiniteQuotientLift s
      ext x
      change (P.proj j) (e.symm (qL x)) = (s.π.app j).hom x
      have h₁ : (P.proj j) (e.symm (qL x)) = (e (e.symm (qL x))).val j :=
        (test_profiniteGrp_toLimit_coordinate P j (e.symm (qL x))).symm
      have h₂ : (e (e.symm (qL x))).val j = (qL x).val j :=
        congrArg (fun z => z.val j) (e.apply_symm_apply (qL x))
      have h₃ : (qL x).val j = (s.π.app j).hom x := by
        change (profiniteGrpFiniteQuotientLift s x).val j = (s.π.app j).hom x
        rfl
      simpa [profiniteGrpToTopGroup] using h₁.trans (h₂.trans h₃)
    uniq := fun s m hm => by
      ext x
      let qL := profiniteGrpFiniteQuotientLift s
      change m.hom x = e.symm (qL x)
      apply e.injective
      apply ProfiniteGrp.limit_ext
      intro j
      have h₁ : (e (m.hom x)).val j = (P.proj j) (m.hom x) :=
        test_profiniteGrp_toLimit_coordinate P j (m.hom x)
      have h₂ : (P.proj j) (m.hom x) = (s.π.app j).hom x := by
        have h := congrArg (fun q => q.hom x) (hm j)
        change (P.proj j) (m.hom x) = (s.π.app j).hom x at h
        exact h
      have h₃ : (s.π.app j).hom x = (qL x).val j := by
        change (s.π.app j).hom x = (profiniteGrpFiniteQuotientLift s x).val j
        rfl
      have h₄ : (qL x).val j = (e (e.symm (qL x))).val j :=
        (congrArg (fun z => z.val j) (e.apply_symm_apply (qL x))).symm
      simpa [profiniteGrpToTopGroup] using h₁.trans (h₂.trans (h₃.trans h₄)) }

private theorem isProfiniteSpace_of_finite_discrete_topological_limit
    {J : Type u} [SmallCategory J] (D : J ⥤ TopCat.{u})
    (hfinite : ∀ j, Finite (D.obj j) ∧ DiscreteTopology (D.obj j))
    (c : Cone D) (hc : IsLimit c) :
    Formalization.Books.Topology.Unit22.IsProfiniteSpace (c.pt : Type u) := by
  let Dp : J ⥤ Profinite.{u} := {
    obj := fun j => by
      letI : Finite (D.obj j) := (hfinite j).1
      letI : DiscreteTopology (D.obj j) := (hfinite j).2
      letI : CompactSpace (D.obj j) := Finite.compactSpace
      letI : T2Space (D.obj j) := DiscreteTopology.toT2Space
      letI : TotallySeparatedSpace (D.obj j) := TotallySeparatedSpace.of_discrete _
      exact Profinite.of (D.obj j)
    map := fun {X Y} f => by
      letI : Finite (D.obj X) := (hfinite X).1
      letI : DiscreteTopology (D.obj X) := (hfinite X).2
      letI : CompactSpace (D.obj X) := Finite.compactSpace
      letI : T2Space (D.obj X) := DiscreteTopology.toT2Space
      letI : TotallySeparatedSpace (D.obj X) := TotallySeparatedSpace.of_discrete _
      letI : Finite (D.obj Y) := (hfinite Y).1
      letI : DiscreteTopology (D.obj Y) := (hfinite Y).2
      letI : CompactSpace (D.obj Y) := Finite.compactSpace
      letI : T2Space (D.obj Y) := DiscreteTopology.toT2Space
      letI : TotallySeparatedSpace (D.obj Y) := TotallySeparatedSpace.of_discrete _
      exact CompHausLike.ofHom (fun X => TotallyDisconnectedSpace X) (D.map f).hom
    map_id := by
      intro X
      ext x
      change (D.map (𝟙 X)).hom x = x
      simp
    map_comp := by
      intro X Y Z f g
      ext x
      change (D.map (f ≫ g)).hom x = (D.map g).hom ((D.map f).hom x)
      rw [D.map_comp]
      rfl }
  have hp : IsLimit (Profinite.toTopCat.mapCone (Profinite.limitCone Dp)) :=
    isLimitOfPreserves Profinite.toTopCat (Profinite.limitConeIsLimit Dp)
  have hD : Dp ⋙ Profinite.toTopCat = D := by
    apply CategoryTheory.Functor.ext (fun j => by rfl)
  cases hD
  let e : c.pt ≅ (Profinite.toTopCat.obj (Profinite.limitCone Dp).pt) :=
    hc.conePointUniqueUpToIso hp
  refine ⟨(Profinite.limitCone Dp).pt, ?_⟩
  exact ⟨{
    toEquiv := {
      toFun := e.hom
      invFun := e.inv
      left_inv := by intro x; exact congrArg (fun f => f x) e.hom_inv_id
      right_inv := by intro x; exact congrArg (fun f => f x) e.inv_hom_id }
    continuous_toFun := e.hom.hom.continuous
    continuous_invFun := e.inv.hom.continuous }⟩

theorem profiniteGroup_iff_finite_discrete_limit :
    IsProfiniteGroup (G := G) ↔ IsLimitOfFiniteDiscreteTopologicalGroups (G := G) := by
  constructor
  · intro hG
    have hprops :=
      Formalization.Books.Topology.Unit22.isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mp
        hG
    let _ : CompactSpace G := hprops.2.1
    let _ : TotallyDisconnectedSpace G := hprops.2.2
    let P : ProfiniteGrp.{u} := ProfiniteGrp.of G
    let D := ProfiniteGrp.diagram P ⋙ profiniteGrpToTopGroup
    let c := profiniteGrpToTopGroup.mapCone (ProfiniteGrp.cone P)
    refine ⟨{
      index := OpenNormalSubgroup P
      diagram := D
      cone := c
      finite_discrete := by
        intro j
        constructor
        · change Finite ((P : Type u) ⧸ j.toSubgroup)
          infer_instance
        · refine ⟨?_⟩
          rfl
      comparison := by
        exact ⟨ContinuousMulEquiv.refl G⟩
      is_limit := by
        exact profiniteGrpFiniteQuotientConeIsLimit P }⟩
  · rintro ⟨p⟩
    let : SmallCategory p.index := p.category
    let : PreservesLimits (topologicalGroupForgetToTopCat.{u}) :=
      topological_group_limits_commute_with_topological_spaces
    let : PreservesLimitsOfSize.{0, u} (topologicalGroupForgetToTopCat.{u}) :=
      preservesLimitsOfSize_shrink _
    have hcone : IsLimit
        (topologicalGroupForgetToTopCat.mapCone p.cone) :=
      isLimitOfPreserves topologicalGroupForgetToTopCat p.is_limit
    have hspace := isProfiniteSpace_of_finite_discrete_topological_limit
      (p.diagram ⋙ topologicalGroupForgetToTopCat)
      (fun j => p.finite_discrete j)
      (topologicalGroupForgetToTopCat.mapCone p.cone) hcone
    rcases hspace with ⟨Q, ⟨eQ⟩⟩
    rcases p.comparison with ⟨eG⟩
    change Formalization.Books.Topology.Unit22.IsProfiniteSpace G
    exact ⟨Q, ⟨eG.toHomeomorph.trans eQ⟩⟩

theorem profiniteGroup_iff_cofiltered_finite_discrete_limit :
    IsProfiniteGroup (G := G) ↔ IsCofilteredLimitOfFiniteDiscreteTopologicalGroups (G := G) := by
  constructor
  · intro hG
    have hprops :=
      Formalization.Books.Topology.Unit22.isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mp
        hG
    let _ : CompactSpace G := hprops.2.1
    let _ : TotallyDisconnectedSpace G := hprops.2.2
    let P : ProfiniteGrp.{u} := ProfiniteGrp.of G
    let : IsCofiltered (OpenNormalSubgroup P) := {
      cone_objs X Y :=
        ⟨X ⊓ Y, homOfLE inf_le_left, homOfLE inf_le_right, trivial⟩
      cone_maps := by
        intro X Y f g
        refine ⟨X, 𝟙 _, ?_⟩
        apply ULift.ext
        subsingleton
      nonempty :=
        ⟨{ toOpenSubgroup := ⊤,
            isNormal' := by
              change (⊤ : Subgroup (P : Type u)).Normal
              infer_instance }⟩ }
    let D := ProfiniteGrp.diagram P ⋙ profiniteGrpToTopGroup
    let c := profiniteGrpToTopGroup.mapCone (ProfiniteGrp.cone P)
    refine ⟨{
      index := OpenNormalSubgroup P
      cofiltered := inferInstance
      diagram := D
      cone := c
      finite_discrete := by
        intro j
        constructor
        · change Finite ((P : Type u) ⧸ j.toSubgroup)
          infer_instance
        · refine ⟨?_⟩
          rfl
      comparison := by
        exact ⟨ContinuousMulEquiv.refl G⟩
      is_limit := by
        exact profiniteGrpFiniteQuotientConeIsLimit P }⟩
  · rintro ⟨p⟩
    let : SmallCategory p.index := p.category
    apply (profiniteGroup_iff_finite_discrete_limit (G := G)).2
    exact ⟨{
      index := p.index
      diagram := p.diagram
      cone := p.cone
      finite_discrete := p.finite_discrete
      comparison := p.comparison
      is_limit := p.is_limit }⟩

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
