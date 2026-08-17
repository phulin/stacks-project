import Formalization.Books.Topology.Unit29.TopologicalGroups
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Category.TopCommRingCat

/-!
# Topology, Chapter 29: Topological rings

The source uses commutative rings with `1`.  Mathlib's `IsTopologicalRing` and
`TopCommRingCat` are therefore the canonical interfaces for the definitions and category
statements in this part of the chapter.
-/

namespace Formalization.Books.Topology.Unit29

open CategoryTheory CategoryTheory.Limits
open Set TopologicalSpace

universe u v

noncomputable section

section Basic

variable {R S : Type u}

/-- A bundled topological commutative ring from the unbundled data in the source definition. -/
def topologicalRingObject (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : TopCommRingCat.{u} :=
  TopCommRingCat.of R

/-- A homomorphism of topological rings, in the underlying form used by `TopCommRingCat`. -/
abbrev TopologicalRingHom [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] :=
  { f : R →+* S // Continuous f }

/-- The quotient topology on the target of a ring homomorphism. -/
@[instance_reducible]
def quotientRingTopology [CommRing R] [CommRing S] [TopologicalSpace R]
    (f : R →+* S) : TopologicalSpace S :=
  TopologicalSpace.coinduced f inferInstance

/-- The additive group of a topological ring is a topological additive group. -/
theorem topologicalRing_additive_group [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : IsTopologicalAddGroup R := by
  exact IsTopologicalRing.to_topologicalAddGroup

/-- A subring with its induced topology is a topological ring. -/
theorem topologicalRing_subring [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (S : Subring R) : IsTopologicalRing S := by
  infer_instance

/-- A surjective ring quotient with its quotient topology is a topological ring. -/
theorem topologicalRing_surjective_quotient [CommRing R] [CommRing S] [TopologicalSpace R]
    [IsTopologicalRing R] (f : R →+* S) (hf : Function.Surjective f) :
    letI : TopologicalSpace S := quotientRingTopology f
    IsTopologicalRing S := by
  let _ : TopologicalSpace S := quotientRingTopology f
  have hq : Topology.IsQuotientMap f.toAddMonoidHom := ⟨⟨rfl⟩, hf⟩
  have hoq : IsOpenQuotientMap f.toAddMonoidHom :=
    AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hq
  refine { toIsTopologicalSemiring := ?_, continuous_neg := ?_ }
  · refine { continuous_add := ?_, continuous_mul := ?_ }
    · rw [← (hoq.prodMap hoq).continuous_comp_iff]
      convert hoq.continuous.comp continuous_add using 1
      ext p
      simp
    · rw [← (hoq.prodMap hoq).continuous_comp_iff]
      convert hoq.continuous.comp continuous_mul using 1
      ext p
      simp
  · rw [← hoq.continuous_comp_iff]
    exact (show Continuous ((fun a : S => -a) ∘ f) from by
      convert hoq.continuous.comp continuous_neg using 1
      ext x
      simp)

end Basic

private theorem topologicalRing_induced
    {A B : Type u} [CommRing A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] (f : A →+* B) :
    @IsTopologicalRing A (TopologicalSpace.induced f inferInstance) inferInstance := by
  let : TopologicalSpace A := TopologicalSpace.induced f inferInstance
  exact IsTopologicalSemiring.toIsTopologicalRing {
    continuous_add := (continuousAdd_induced f).continuous_add
    continuous_mul := (continuousMul_induced f).continuous_mul }

section Category

private noncomputable def topRingLimitCone {J : Type u} [Category.{u} J]
    (F : J ⥤ TopCommRingCat.{u}) : Cone F := by
  let G := F ⋙ (forget₂ TopCommRingCat CommRingCat)
  let c := CommRingCat.limitCone G
  letI : TopologicalSpace (c.pt : Type u) :=
    ⨅ j, (F.obj j).isTopologicalSpace.induced (c.π.app j).hom
  letI : IsTopologicalRing (c.pt : Type u) :=
    IsTopologicalSemiring.toIsTopologicalRing {
      toContinuousAdd := continuousAdd_iInf fun j => by
        let tj : TopologicalSpace (G.obj j) := (F.obj j).isTopologicalSpace
        let : TopologicalSpace (G.obj j) := tj
        let : IsTopologicalRing (G.obj j) := (F.obj j).isTopologicalRing
        exact continuousAdd_induced (c.π.app j).hom
      toContinuousMul := continuousMul_iInf fun j => by
        let tj : TopologicalSpace (G.obj j) := (F.obj j).isTopologicalSpace
        let : TopologicalSpace (G.obj j) := tj
        let : IsTopologicalRing (G.obj j) := (F.obj j).isTopologicalRing
        exact continuousMul_induced (c.π.app j).hom }
  let L : TopCommRingCat.{u} := TopCommRingCat.of (c.pt : Type u)
  let p (j : J) : L ⟶ F.obj j :=
    ⟨(c.π.app j).hom, continuous_iff_le_induced.mpr (iInf_le _ j)⟩
  exact
    { pt := L
      π :=
        { app := p
          naturality := fun X Y f => by
            ext x
            exact congr($(c.π.naturality f).hom x) } }

private noncomputable def topRingLimitConeIsLimit {J : Type u} [Category.{u} J]
    (F : J ⥤ TopCommRingCat.{u}) : IsLimit (topRingLimitCone F) := by
  let G := F ⋙ (forget₂ TopCommRingCat CommRingCat)
  let c := CommRingCat.limitCone G
  letI : TopologicalSpace (c.pt : Type u) :=
    ⨅ j, (F.obj j).isTopologicalSpace.induced (c.π.app j).hom
  letI : IsTopologicalRing (c.pt : Type u) :=
    IsTopologicalSemiring.toIsTopologicalRing {
      toContinuousAdd := continuousAdd_iInf fun j => by
        let tj : TopologicalSpace (G.obj j) := (F.obj j).isTopologicalSpace
        let : TopologicalSpace (G.obj j) := tj
        let : IsTopologicalRing (G.obj j) := (F.obj j).isTopologicalRing
        exact continuousAdd_induced (c.π.app j).hom
      toContinuousMul := continuousMul_iInf fun j => by
        let tj : TopologicalSpace (G.obj j) := (F.obj j).isTopologicalSpace
        let : TopologicalSpace (G.obj j) := tj
        let : IsTopologicalRing (G.obj j) := (F.obj j).isTopologicalRing
        exact continuousMul_induced (c.π.app j).hom }
  letI : (forget₂ TopCommRingCat CommRingCat).Faithful :=
    ⟨fun {_ _} f g h => by
      apply Subtype.ext
      exact congrArg (fun k => k.hom) h⟩
  let hcone : CommRingCat.limitCone G ≅
      (forget₂ TopCommRingCat CommRingCat).mapCone (topRingLimitCone F) :=
    Cone.ext (Iso.refl _) (fun j => by
      ext x
      rfl)
  refine IsLimit.ofFaithful (forget₂ TopCommRingCat CommRingCat)
    (ht := (CommRingCat.limitConeIsLimit G).ofIsoLimit hcone)
    (lift := fun s => by
      let sG : Cone G :=
        { pt := CommRingCat.of (s.pt : Type u)
          π :=
            { app := fun j => CommRingCat.ofHom (s.π.app j).val
              naturality := fun X Y f => by
                ext x
                exact congr($(s.π.naturality f).val x) } }
      let q := (CommRingCat.limitConeIsLimit G).lift sG
      refine ⟨q.hom, ?_⟩
      rw [continuous_iff_le_induced]
      change s.pt.isTopologicalSpace ≤
        TopologicalSpace.induced q.hom
          (⨅ j, (F.obj j).isTopologicalSpace.induced (c.π.app j).hom)
      rw [induced_iInf]
      refine le_iInf fun j => ?_
      let tj : TopologicalSpace (G.obj j) := (F.obj j).isTopologicalSpace
      change s.pt.isTopologicalSpace ≤
        TopologicalSpace.induced q.hom
          (TopologicalSpace.induced (c.π.app j).hom tj)
      rw [induced_compose (f := q.hom) (g := (c.π.app j).hom),
        ← continuous_iff_le_induced]
      change Continuous
        ((CommRingCat.limitConeIsLimit G).lift sG ≫ c.π.app j).hom
      rw [(CommRingCat.limitConeIsLimit G).fac]
      change Continuous (s.π.app j).val
      exact (s.π.app j).property) ?_
  intro s
  ext x
  rfl

private noncomputable def topRingLimitConeForgetCommRingIsLimit {J : Type u}
    [Category.{u} J] (F : J ⥤ TopCommRingCat.{u}) :
    IsLimit ((forget₂ TopCommRingCat CommRingCat).mapCone (topRingLimitCone F)) := by
  let G := F ⋙ (forget₂ TopCommRingCat CommRingCat)
  let hcone : CommRingCat.limitCone G ≅
      (forget₂ TopCommRingCat CommRingCat).mapCone (topRingLimitCone F) :=
    Cone.ext (Iso.refl _) (fun j => by
      ext x
      rfl)
  exact (CommRingCat.limitConeIsLimit G).ofIsoLimit hcone

private noncomputable def topRingLimitConeForgetTopIsLimit {J : Type u}
    [Category.{u} J] (F : J ⥤ TopCommRingCat.{u}) :
    IsLimit ((forget₂ TopCommRingCat TopCat).mapCone (topRingLimitCone F)) := by
  let hcomm := topRingLimitConeForgetCommRingIsLimit F
  let hset : IsLimit ((forget CommRingCat).mapCone
      ((forget₂ TopCommRingCat CommRingCat).mapCone (topRingLimitCone F))) :=
    isLimitOfPreserves (forget CommRingCat) hcomm
  let hcone : ((forget CommRingCat).mapCone
      ((forget₂ TopCommRingCat CommRingCat).mapCone (topRingLimitCone F))) ≅
      ((forget TopCat).mapCone
        ((forget₂ TopCommRingCat TopCat).mapCone (topRingLimitCone F))) :=
    Cone.ext (Iso.refl _) (fun j => by rfl)
  let hset' := hset.ofIsoLimit hcone
  exact Classical.choice ((TopCat.nonempty_isLimit_iff_eq_induced
    ((forget₂ TopCommRingCat TopCat).mapCone (topRingLimitCone F)) hset').2 (by
      rfl))

theorem topological_rings_have_limits : HasLimits (TopCommRingCat.{u}) := by
  refine { has_limits_of_shape := fun J _ => ?_ }
  exact { has_limit := fun F => ⟨⟨topRingLimitCone F, topRingLimitConeIsLimit F⟩⟩ }

theorem topological_ring_limits_commute_with_topological_spaces :
    PreservesLimits (forget₂ TopCommRingCat.{u} TopCat.{u}) := by
  refine { preservesLimitsOfShape := fun {J} _ => ?_ }
  refine { preservesLimit := fun {F} => ?_ }
  exact preservesLimit_of_preserves_limit_cone (topRingLimitConeIsLimit F)
    (topRingLimitConeForgetTopIsLimit F)

theorem topological_ring_limits_commute_with_commutative_rings :
    PreservesLimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) := by
  refine { preservesLimitsOfShape := fun {J} _ => ?_ }
  refine { preservesLimit := fun {F} => ?_ }
  exact preservesLimit_of_preserves_limit_cone (topRingLimitConeIsLimit F)
    (topRingLimitConeForgetCommRingIsLimit F)

private noncomputable def topRingCoproductCocone {ι : Type u}
    (X : ι → TopCommRingCat.{u}) : Cocone (Discrete.functor X) := by
  let G := (Discrete.functor X) ⋙ (forget₂ TopCommRingCat CommRingCat)
  let c := colimit.cocone G
  let A := c.pt
  let f : (Σ i, X i) → A := fun x => (c.ι.app (Discrete.mk x.1)).hom x.2
  let T := RingTopology.coinduced f
  letI : TopologicalSpace A := T.toTopologicalSpace
  letI : IsTopologicalRing A := T.toIsTopologicalRing
  let L : TopCommRingCat.{u} := TopCommRingCat.of A
  let p (i : ι) : X i ⟶ L :=
    ⟨(c.ι.app (Discrete.mk i)).hom, by
      change Continuous ((fun x : Σ i, X i => f x) ∘ Sigma.mk i)
      exact (RingTopology.coinduced_continuous f).comp continuous_sigmaMk⟩
  exact
    { pt := L
      ι :=
        { app := fun i => p i.as
          naturality := by
            rintro ⟨i⟩ ⟨j⟩ ⟨⟨h⟩⟩
            cases h
            rfl } }

private noncomputable def topRingCoproductCoconeIsColimit {ι : Type u}
    (X : ι → TopCommRingCat.{u}) : IsColimit (topRingCoproductCocone X) := by
  let G := (Discrete.functor X) ⋙ (forget₂ TopCommRingCat CommRingCat)
  let c := colimit.cocone G
  let A := c.pt
  let f : (Σ i, X i) → A := fun x => (c.ι.app (Discrete.mk x.1)).hom x.2
  let T := RingTopology.coinduced f
  letI : TopologicalSpace A := T.toTopologicalSpace
  letI : IsTopologicalRing A := T.toIsTopologicalRing
  let q (s : Cocone (Discrete.functor X)) : A →+* (s.pt : Type u) :=
    ((colimit.isColimit G).desc
      ((forget₂ TopCommRingCat CommRingCat).mapCocone s)).hom
  let qContinuous (s : Cocone (Discrete.functor X)) : Continuous (q s) := by
    rw [continuous_iff_le_induced]
    have hcomp : Continuous (q s ∘ f) := by
      apply continuous_sigma
      intro i
      change Continuous (fun a : (X i : Type u) =>
        q s ((c.ι.app (Discrete.mk i)).hom a))
      have hi := (colimit.isColimit G).fac
        ((forget₂ TopCommRingCat CommRingCat).mapCocone s) (Discrete.mk i)
      rw [show (fun a : (X i : Type u) =>
          q s ((c.ι.app (Discrete.mk i)).hom a)) =
          fun a => (s.ι.app (Discrete.mk i)).val a by
        funext a
        exact congrArg (fun k => k.hom a) hi]
      exact (s.ι.app (Discrete.mk i)).property
    have hle : TopologicalSpace.coinduced f inferInstance ≤
        TopologicalSpace.induced (q s) s.pt.isTopologicalSpace :=
      continuous_iff_coinduced_le.mp (continuous_induced_rng.mpr hcomp)
    change T.toTopologicalSpace ≤
      TopologicalSpace.induced (q s) s.pt.isTopologicalSpace
    exact (show T ≤ ⟨TopologicalSpace.induced (q s) s.pt.isTopologicalSpace,
        topologicalRing_induced (q s)⟩ from by
      dsimp [T, RingTopology.coinduced]
      exact sInf_le hle)
  refine
    { desc := fun s => ⟨q s, qContinuous s⟩
      fac := fun s i => by
        cases i with
        | mk i =>
          ext x
          change q s ((c.ι.app (Discrete.mk i)).hom x) =
            (s.ι.app (Discrete.mk i)).val x
          have hi := (colimit.isColimit G).fac
            ((forget₂ TopCommRingCat CommRingCat).mapCocone s) (Discrete.mk i)
          exact congrArg (fun k => k.hom x) hi
      uniq := fun s m hm => by
        dsimp [topRingCoproductCocone] at m hm ⊢
        apply Subtype.ext
        have hring : CommRingCat.ofHom m.val = CommRingCat.ofHom (q s) := by
          apply (colimit.isColimit G).hom_ext
          intro i
          have hm' := congrArg (fun k =>
            (forget₂ TopCommRingCat CommRingCat).map k) (hm i)
          have hfac := (colimit.isColimit G).fac
            ((forget₂ TopCommRingCat CommRingCat).mapCocone s) i
          change c.ι.app i ≫ CommRingCat.ofHom m.val =
            c.ι.app i ≫ CommRingCat.ofHom (q s)
          change c.ι.app i ≫ CommRingCat.ofHom m.val =
            (forget₂ TopCommRingCat CommRingCat).map (s.ι.app i) at hm'
          have hfac' := hfac.symm
          change (forget₂ TopCommRingCat CommRingCat).map (s.ι.app i) =
            c.ι.app i ≫ CommRingCat.ofHom (q s) at hfac'
          exact hm'.trans hfac'
        exact congrArg (fun k => k.hom) hring }

private noncomputable def topRingCoequalizerCofork {A B : TopCommRingCat.{u}}
    (f g : A ⟶ B) : Cofork f g := by
  let G := parallelPair
    ((forget₂ TopCommRingCat CommRingCat).map f)
    ((forget₂ TopCommRingCat CommRingCat).map g)
  let c := colimit.cocone G
  let Q := c.pt
  let q := c.ι.app WalkingParallelPair.one
  letI : TopologicalSpace (G.obj WalkingParallelPair.one) := B.isTopologicalSpace
  let T := RingTopology.coinduced q.hom
  letI : TopologicalSpace Q := T.toTopologicalSpace
  letI : IsTopologicalRing Q := T.toIsTopologicalRing
  let p : B ⟶ TopCommRingCat.of Q :=
    ⟨q.hom, RingTopology.coinduced_continuous q.hom⟩
  have hq :
      (forget₂ TopCommRingCat CommRingCat).map f ≫ q =
        (forget₂ TopCommRingCat CommRingCat).map g ≫ q := by
    exact (c.ι.naturality WalkingParallelPairHom.left).trans
      (c.ι.naturality WalkingParallelPairHom.right).symm
  exact Cofork.ofπ p (by
    apply Subtype.ext
    exact congrArg (fun k => k.hom) hq)

private noncomputable def topRingCoequalizerDesc {A B : TopCommRingCat.{u}}
    (f g : A ⟶ B) (s : Cofork f g) :
    (topRingCoequalizerCofork f g).pt ⟶ s.pt := by
  let G := parallelPair
    ((forget₂ TopCommRingCat CommRingCat).map f)
    ((forget₂ TopCommRingCat CommRingCat).map g)
  let c := colimit.cocone G
  let Q := c.pt
  let q := c.ι.app WalkingParallelPair.one
  letI : TopologicalSpace (G.obj WalkingParallelPair.one) := B.isTopologicalSpace
  let T := RingTopology.coinduced q.hom
  letI : TopologicalSpace Q := T.toTopologicalSpace
  letI : IsTopologicalRing Q := T.toIsTopologicalRing
  let sG : Cocone G :=
    Cofork.ofπ ((forget₂ TopCommRingCat CommRingCat).map s.π) (by
      simpa only [Functor.map_comp] using congrArg
        (fun k => (forget₂ TopCommRingCat CommRingCat).map k) s.condition)
  let l : Q →+* (s.pt : Type u) :=
    ((colimit.isColimit G).desc sG).hom
  have hlcomp : Continuous (l ∘ q.hom) := by
    have heq : l ∘ q.hom = fun x => s.π.val x := by
      funext x
      have hfac := (colimit.isColimit G).fac sG WalkingParallelPair.one
      exact congrArg (fun k => k.hom x) hfac
    rw [heq]
    exact s.π.property
  have hl : Continuous l := by
    rw [continuous_iff_le_induced]
    have hle : TopologicalSpace.coinduced q.hom inferInstance ≤
        TopologicalSpace.induced l s.pt.isTopologicalSpace :=
      continuous_iff_coinduced_le.mp (continuous_induced_rng.mpr hlcomp)
    change T.toTopologicalSpace ≤ TopologicalSpace.induced l s.pt.isTopologicalSpace
    exact (show T ≤ ⟨TopologicalSpace.induced l s.pt.isTopologicalSpace,
        topologicalRing_induced l⟩ from by
      dsimp [T, RingTopology.coinduced]
      exact sInf_le hle)
  exact ⟨l, hl⟩

private noncomputable def topRingCoequalizerCoforkIsColimit {A B : TopCommRingCat.{u}}
    (f g : A ⟶ B) : IsColimit (topRingCoequalizerCofork f g) := by
  let G := parallelPair
    ((forget₂ TopCommRingCat CommRingCat).map f)
    ((forget₂ TopCommRingCat CommRingCat).map g)
  let c := colimit.cocone G
  let s0 := topRingCoequalizerCofork f g
  refine Cofork.IsColimit.mk s0 (fun s => topRingCoequalizerDesc f g s) ?_ ?_
  · intro s
    let sG : Cocone G :=
      Cofork.ofπ ((forget₂ TopCommRingCat CommRingCat).map s.π) (by
        simpa only [Functor.map_comp] using congrArg
          (fun k => (forget₂ TopCommRingCat CommRingCat).map k) s.condition)
    dsimp [s0, topRingCoequalizerCofork, topRingCoequalizerDesc]
    ext x
    have hfac := (colimit.isColimit G).fac
      sG WalkingParallelPair.one
    exact congrArg (fun k => k.hom x) hfac
  · intro s m hm
    let sG : Cocone G :=
      Cofork.ofπ ((forget₂ TopCommRingCat CommRingCat).map s.π) (by
        simpa only [Functor.map_comp] using congrArg
          (fun k => (forget₂ TopCommRingCat CommRingCat).map k) s.condition)
    apply Subtype.ext
    dsimp [topRingCoequalizerDesc]
    have hring :
        CommRingCat.ofHom m.val =
          CommRingCat.ofHom (topRingCoequalizerDesc f g s).val := by
      apply (colimit.isColimit G).hom_ext
      have hm' := congrArg (fun k =>
        (forget₂ TopCommRingCat CommRingCat).map k) (hm)
      dsimp [s0, topRingCoequalizerCofork] at hm'
      have hfac := (colimit.isColimit G).fac
        sG WalkingParallelPair.one
      have hone :
          c.ι.app WalkingParallelPair.one ≫ CommRingCat.ofHom m.val =
            c.ι.app WalkingParallelPair.one ≫
              (colimit.isColimit G).desc sG := by
        exact hm'.trans hfac.symm
      intro j
      cases j with
      | zero =>
          change c.ι.app WalkingParallelPair.zero ≫ CommRingCat.ofHom m.val =
            c.ι.app WalkingParallelPair.zero ≫ (colimit.isColimit G).desc sG
          have hnat : G.map WalkingParallelPairHom.left ≫
              c.ι.app WalkingParallelPair.one = c.ι.app WalkingParallelPair.zero := by
            simpa using c.ι.naturality WalkingParallelPairHom.left
          have hzero := congrArg (fun k => G.map WalkingParallelPairHom.left ≫ k) hone
          have hzero' :
              (G.map WalkingParallelPairHom.left ≫ c.ι.app WalkingParallelPair.one) ≫
                  CommRingCat.ofHom m.val =
                (G.map WalkingParallelPairHom.left ≫ c.ι.app WalkingParallelPair.one) ≫
                  (colimit.isColimit G).desc sG := by
            rw [Category.assoc, Category.assoc]
            exact hzero
          rw [hnat] at hzero'
          exact hzero'
      | one =>
          exact hone
    exact congrArg (fun k => k.hom) hring

private theorem topological_rings_have_coproducts :
    HasCoproducts.{u} (TopCommRingCat.{u}) := by
  intro ι
  refine { has_colimit := fun F => ?_ }
  let X : ι → TopCommRingCat.{u} := fun i => F.obj (Discrete.mk i)
  have hF : Discrete.functor X = F := Discrete.functor_ext (fun i => rfl)
  rw [← hF]
  exact ⟨topRingCoproductCocone X, topRingCoproductCoconeIsColimit X⟩

private theorem topological_rings_have_coequalizers :
    HasCoequalizers (TopCommRingCat.{u}) := by
  refine { has_colimit := fun F => ?_ }
  let : HasColimit (parallelPair (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)) :=
    ⟨topRingCoequalizerCofork (F.map WalkingParallelPairHom.left)
        (F.map WalkingParallelPairHom.right),
      topRingCoequalizerCoforkIsColimit (F.map WalkingParallelPairHom.left)
        (F.map WalkingParallelPairHom.right)⟩
  exact hasColimit_of_iso (diagramIsoParallelPair F)

theorem topological_rings_have_colimits : HasColimits (TopCommRingCat.{u}) := by
  let : HasCoproducts.{u} (TopCommRingCat.{u}) := topological_rings_have_coproducts
  let : HasCoequalizers (TopCommRingCat.{u}) := topological_rings_have_coequalizers
  exact has_colimits_of_hasCoequalizers_and_coproducts

private noncomputable def topologicalRingIndiscrete :
    CommRingCat.{u} ⥤ TopCommRingCat.{u} where
  obj R := by
    letI : TopologicalSpace (R : Type u) := ⊤
    letI : IsTopologicalRing (R : Type u) :=
      { continuous_add := continuous_of_indiscreteTopology
        continuous_mul := continuous_of_indiscreteTopology
        continuous_neg := continuous_of_indiscreteTopology }
    exact TopCommRingCat.of (R : Type u)
  map f := ⟨f.hom, continuous_of_indiscreteTopology⟩
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable def topologicalRingForgetIndiscreteAdjunction :
    (forget₂ TopCommRingCat CommRingCat) ⊣ topologicalRingIndiscrete :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun := fun f =>
            letI : IndiscreteTopology (topologicalRingIndiscrete.obj Y).α := ⟨rfl⟩
            ⟨f.hom, continuous_of_indiscreteTopology⟩
          invFun := fun f => CommRingCat.ofHom f.val
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

theorem topological_ring_colimits_commute_with_commutative_rings :
    PreservesColimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) := by
  exact topologicalRingForgetIndiscreteAdjunction.leftAdjoint_preservesColimits

end Category

end

end Formalization.Books.Topology.Unit29
