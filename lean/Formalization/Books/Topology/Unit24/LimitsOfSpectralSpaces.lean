import Formalization.Books.Topology.Unit23.SpectralSpaces
import Formalization.Books.Topology.Unit15.ConstructibleSets
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Topology, Chapter 24: Limits of spectral spaces

The chapter uses Mathlib's `TopCat` limits, `SpectralSpace`, `IsSpectralMap`,
`IsConstructible`, and the constructible topology.  The source-facing
`inverseLimitSet` and directed-family predicates below make the subset and
intersection descriptions explicit while retaining those canonical APIs.
-/

namespace Formalization.Books.Topology.Unit24

open Set Function CategoryTheory CategoryTheory.Limits _root_.Topology TopologicalSpace
open Formalization.Books.Topology.Unit23

universe u v

noncomputable section

section IntroductoryFacts

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/- The first introductory assertion is already recorded in Unit 23 as
  `spectralSpace_iff_directed_inverse_limit_finite_sober`. -/

/-- A finite sober topological space is spectral.

Sobriety is expressed canonically as `QuasiSober` together with `T0Space`.
-/
theorem spectralSpace_of_finite_sober [Finite X] [QuasiSober X] [T0Space X] :
    SpectralSpace X := by
  exact spectralSpace_iff_source_conditions.mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Every continuous map between finite sober spaces is spectral. -/
theorem isSpectralMap_of_continuous_of_finite_sober
    [Finite X] [Finite Y] [QuasiSober X] [T0Space X]
    [QuasiSober Y] [T0Space Y] (f : X → Y) (hf : Continuous f) :
    IsSpectralMap f := by
  exact ⟨hf, fun _ _ _ => NoetherianSpace.isCompact _⟩

end IntroductoryFacts

section InverseLimitInterfaces

variable {J : Type v} [SmallCategory J]

/-- A diagram of spectral spaces and spectral transition maps. -/
def IsSpectralDiagram (F : J ⥤ TopCat.{max v u}) : Prop :=
  (∀ j : J, SpectralSpace (F.obj j)) ∧
    ∀ (j i : J) (f : j ⟶ i), IsSpectralMap (F.map f)

/-- The subset of the underlying `TopCat` limit whose `j`-component lies in
the prescribed subset `Z j` for every object `j`. -/
def inverseLimitSet (F : J ⥤ TopCat.{max v u}) (Z : ∀ j, Set (F.obj j)) :
    Set ((limit F : TopCat.{max v u}) : Type (max v u)) :=
  {x | ∀ j, (limit.π F j) x ∈ Z j}

/-- Compatibility of a family of subsets with the transition maps of a
diagram. -/
def CompatibleSetFamily (F : J ⥤ TopCat.{max v u})
    (Z : ∀ j, Set (F.obj j)) : Prop :=
  ∀ (j i : J) (f : j ⟶ i), (F.map f) '' Z j ⊆ Z i

end InverseLimitInterfaces

section QuasiCompactness

variable {J : Type v} [SmallCategory J] [IsCofiltered J]

/- Constructibly closed compatible subsets in a cofiltered spectral diagram
have quasi-compact inverse limit. -/
omit [IsCofiltered J] in
theorem inverseLimitSet_isCompact_of_constructibleClosed
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (Z : ∀ j, Set (F.obj j))
    (hZ : ∀ j, IsClosed[constructibleTopology (F.obj j)] (Z j))
    (hZmap : CompatibleSetFamily F Z) :
    IsCompact (inverseLimitSet F Z) := by
  classical
  let (j : J) : SpectralSpace (F.obj j) := hF.1 j
  let hK (j : J) : @CompactSpace (F.obj j) (constructibleTopology (F.obj j)) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := F.obj j)).2.2
  let hT (j : J) : @T2Space (F.obj j) (constructibleTopology (F.obj j)) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := F.obj j)).1
  let tZ (j : J) : TopologicalSpace (Z j) :=
    TopologicalSpace.induced (Subtype.val : Z j → F.obj j)
      (@constructibleTopology (F.obj j) (F.obj j).str)
  let Z' (j : J) := WithTopology (Z j) (tZ j)
  let hKsub (j : J) : @CompactSpace (Z j) (tZ j) := by
    have hcompact : @IsCompact (F.obj j) (constructibleTopology (F.obj j)) (Z j) :=
      @IsClosed.isCompact (F.obj j) (constructibleTopology (F.obj j)) (Z j) (hK j) (hZ j)
    exact (@isCompact_iff_compactSpace (F.obj j)
      (constructibleTopology (F.obj j)) (Z j)).mp hcompact
  let hTsub (j : J) : @T2Space (Z j) (tZ j) := by
    constructor
    intro x y hxy
    obtain ⟨u, v, hu, hv, hxu, hyv, hd⟩ :=
      @T2Space.t2 (F.obj j) (constructibleTopology (F.obj j)) (hT j)
        x.val y.val (by
          intro h
          apply hxy
          exact Subtype.ext h)
    refine ⟨Subtype.val ⁻¹' u, Subtype.val ⁻¹' v, ?_, ?_, ?_, ?_, ?_⟩
    · change IsOpen[TopologicalSpace.induced (Subtype.val : Z j → F.obj j)
        (@constructibleTopology (F.obj j) (F.obj j).str)] (Subtype.val ⁻¹' u)
      exact ⟨u, hu, rfl⟩
    · change IsOpen[TopologicalSpace.induced (Subtype.val : Z j → F.obj j)
        (@constructibleTopology (F.obj j) (F.obj j).str)] (Subtype.val ⁻¹' v)
      exact ⟨v, hv, rfl⟩
    · exact hxu
    · exact hyv
    · rw [Set.disjoint_left]
      intro z hzu hzv
      exact (Set.disjoint_left.1 hd) hzu hzv
  let FZ : J ⥤ TopCat.{max v u} :=
    { obj := fun j => TopCat.of (Z' j)
      map := fun {j i} f => TopCat.ofHom
        { toFun := fun x =>
            WithTopology.toTopology (tZ i)
              ⟨F.map f (WithTopology.ofTopology (t := tZ j) x).val,
                hZmap j i f ⟨(WithTopology.ofTopology (t := tZ j) x).val,
                  (WithTopology.ofTopology (t := tZ j) x).property, rfl⟩⟩
          continuous_toFun := by
            have hcont : @Continuous (F.obj j) (F.obj i)
                (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i)) (F.map f) :=
              (isSpectralMap_iff_continuous_constructibleTopology
                (X := F.obj j) (Y := F.obj i) (f := F.map f)
                (hF.2 j i f).continuous).mp (hF.2 j i f)
            have hmap : @Continuous (Z j) (Z i) (tZ j) (tZ i)
                (fun x =>
                  ⟨F.map f x.val, hZmap j i f ⟨x.val, x.property, rfl⟩⟩) := by
              refine continuous_induced_rng.2 ?_
              have hsub : @Continuous (Z j) (F.obj j) (tZ j)
                  (@constructibleTopology (F.obj j) (F.obj j).str) Subtype.val := by
                change @Continuous (Z j) (F.obj j)
                  (TopologicalSpace.induced Subtype.val
                    (@constructibleTopology (F.obj j) (F.obj j).str))
                  (@constructibleTopology (F.obj j) (F.obj j).str) Subtype.val
                exact continuous_induced_dom
              have hcomp : @Continuous (Z j) (F.obj i) (tZ j)
                  (@constructibleTopology (F.obj i) (F.obj i).str)
                  (F.map f ∘ Subtype.val) :=
                @Continuous.comp (Z j) (F.obj j) (F.obj i)
                  (tZ j) (@constructibleTopology (F.obj j) (F.obj j).str)
                  (@constructibleTopology (F.obj i) (F.obj i).str)
                  Subtype.val (F.map f) hcont hsub
              simpa [Function.comp_def] using hcomp
            have hsource : @Continuous (Z' j) (Z j)
                (WithTopology.instTopologicalSpace (Z j) (tZ j)) (tZ j)
                (WithTopology.ofTopology : Z' j → Z j) :=
              WithTopology.continuous_ofTopology (X := Z j) (t := tZ j)
            have htarget : @Continuous (Z i) (Z' i) (tZ i)
                (WithTopology.instTopologicalSpace (Z i) (tZ i))
                (WithTopology.toTopology (tZ i)) :=
              WithTopology.continuous_toTopology (X := Z i) (t := tZ i)
            have hcomp' : @Continuous (Z' j) (Z i)
                (WithTopology.instTopologicalSpace (Z j) (tZ j)) (tZ i)
                ((fun x : Z j =>
                  ⟨F.map f x.val, hZmap j i f ⟨x.val, x.property, rfl⟩⟩) ∘
                  (WithTopology.ofTopology : Z' j → Z j)) :=
              @Continuous.comp (Z' j) (Z j) (Z i)
                (WithTopology.instTopologicalSpace (Z j) (tZ j)) (tZ j) (tZ i)
                (WithTopology.ofTopology : Z' j → Z j)
                (fun x : Z j =>
                  ⟨F.map f x.val, hZmap j i f ⟨x.val, x.property, rfl⟩⟩)
                hmap hsource
            simpa [Function.comp_def, Z'] using
              (@Continuous.comp (Z' j) (Z i) (Z' i)
                (WithTopology.instTopologicalSpace (Z j) (tZ j)) (tZ i)
                (WithTopology.instTopologicalSpace (Z i) (tZ i))
                ((fun x : Z j =>
                  ⟨F.map f x.val, hZmap j i f ⟨x.val, x.property, rfl⟩⟩) ∘
                  (WithTopology.ofTopology : Z' j → Z j))
                (WithTopology.toTopology (tZ i)) htarget hcomp')
        }
      map_id := by
        intro j
        apply TopCat.ext
        intro x
        apply WithTopology.ext
        apply Subtype.ext
        simp
      map_comp := by
        intro j i k f g
        apply TopCat.ext
        intro x
        apply WithTopology.ext
        apply Subtype.ext
        have hcomp := congrArg (fun r => r x.ofTopology) (F.map_comp f g)
        convert hcomp using 1 <;> simp }
  let : ∀ j, CompactSpace (FZ.obj j) := fun j => by
    change CompactSpace (Z' j)
    exact @Function.Surjective.compactSpace (Z j) (Z' j) (tZ j)
      (WithTopology.instTopologicalSpace (Z j) (tZ j))
      (WithTopology.toTopology (tZ j))
      (WithTopology.continuous_toTopology (X := Z j) (t := tZ j))
      (hKsub j) (WithTopology.toTopology_surjective (tZ j))
  let : ∀ j, T2Space (FZ.obj j) := fun j => by
    change T2Space (Z' j)
    constructor
    intro x y hxy
    have hxy' : x.ofTopology ≠ y.ofTopology := by
      intro h
      apply hxy
      exact WithTopology.ext h
    obtain ⟨u, v, hu, hv, hxu, hyv, hd⟩ :=
      @T2Space.t2 (Z j) (tZ j) (hTsub j) x.ofTopology y.ofTopology hxy'
    refine ⟨WithTopology.ofTopology ⁻¹' u, WithTopology.ofTopology ⁻¹' v, ?_, ?_, ?_, ?_, ?_⟩
    · rw [WithTopology.isOpen_iff]
      change IsOpen[tZ j] u
      exact hu
    · rw [WithTopology.isOpen_iff]
      change IsOpen[tZ j] v
      exact hv
    · exact hxu
    · exact hyv
    · rw [Set.disjoint_left]
      intro z hzu hzv
      exact (Set.disjoint_left.1 hd) hzu hzv
  let : CompactSpace ((limit FZ : TopCat.{max v u}) : Type (max v u)) :=
    Formalization.Books.Topology.Unit14.compactSpace_limit_of_compact_Hausdorff FZ
  have hval (j : J) : @Continuous (Z j) (F.obj j) (tZ j) _ Subtype.val := by
    have hid : @Continuous (F.obj j) (F.obj j)
        (constructibleTopology (F.obj j)) _ id := by
      refine continuous_def.2 ?_
      intro U hU
      simpa using (isOpen_constructibleTopology_of_isOpen (X := F.obj j) hU)
    simpa [Function.comp_def] using
      (@Continuous.comp (Z j) (F.obj j) (F.obj j)
        (tZ j) (constructibleTopology (F.obj j)) _
        Subtype.val id hid continuous_induced_dom)
  have hval' (j : J) : @Continuous (Z' j) (F.obj j)
      (WithTopology.instTopologicalSpace (Z j) (tZ j)) _
      (fun x => (WithTopology.ofTopology (t := tZ j) x).val) := by
    simpa [Function.comp_def, Z'] using
      (@Continuous.comp (Z' j) (Z j) (F.obj j)
        (WithTopology.instTopologicalSpace (Z j) (tZ j)) (tZ j) _
        (WithTopology.ofTopology : Z' j → Z j) Subtype.val (hval j)
        (WithTopology.continuous_ofTopology (X := Z j) (t := tZ j)))
  let cone : Cone F :=
    { pt := limit FZ
      π :=
        { app := fun j => TopCat.ofHom
            { toFun := fun x =>
                (WithTopology.ofTopology (t := tZ j) ((limit.π FZ j) x)).val
              continuous_toFun := hval' j |>.comp (limit.π FZ j).hom.2 }
          naturality := by
            intro j i f
            apply TopCat.ext
            intro z
            have hw := congrArg
              (fun q : (limit FZ : TopCat.{max v u}) ⟶ FZ.obj i =>
                (WithTopology.ofTopology (t := tZ i) (q z)).val)
              (limit.w FZ f)
            simpa [FZ, Z', CategoryTheory.comp_apply] using hw.symm } }
  let g : ((limit FZ : TopCat.{max v u}) : Type (max v u)) →
      ((limit F : TopCat.{max v u}) : Type (max v u)) :=
    (limit.isLimit F).lift cone
  have hg : Continuous g := (limit.isLimit F).lift cone |>.hom.2
  have hgrange : IsCompact (Set.range g) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image hg
  have hsubset : Set.range g ⊆ inverseLimitSet F Z := by
    rintro y ⟨x, rfl⟩
    intro j
    have hfac := congrArg (fun q => q x) ((limit.isLimit F).fac cone j)
    have hfac' : (limit.π F j) (g x) = (cone.π.app j) x := by
      change (limit.cone F).π.app j ((limit.isLimit F).lift cone x) = (cone.π.app j) x
      exact hfac
    rw [hfac']
    exact (WithTopology.ofTopology (t := tZ j) ((limit.π FZ j) x)).property
  have hsupset : inverseLimitSet F Z ⊆ Set.range g := by
    intro y hy
    let S : Cone FZ :=
      { pt := TopCat.of PUnit
        π :=
          { app := fun j => TopCat.ofHom
              { toFun := fun _ =>
                  WithTopology.toTopology (tZ j)
                    ⟨(limit.π F j) y, hy j⟩
                continuous_toFun := continuous_const }
            naturality := by
              intro j i f
              apply TopCat.ext
              intro z
              apply WithTopology.ext
              apply Subtype.ext
              convert congrArg (fun q => q y) (limit.w F f) using 1 <;>
                simp [FZ, Z'] } }
    let x := (limit.isLimit FZ).lift S PUnit.unit
    refine ⟨x, ?_⟩
    apply Concrete.limit_ext F
    intro j
    have hfacg := congrArg (fun q => q x) ((limit.isLimit F).fac cone j)
    have hfacg' : (limit.π F j) (g x) = (cone.π.app j) x := by
      change (limit.cone F).π.app j ((limit.isLimit F).lift cone x) =
        (cone.π.app j) x
      exact hfacg
    change (limit.π F j) (g x) = (limit.π F j) y
    rw [hfacg']
    change (WithTopology.ofTopology (t := tZ j) ((limit.π FZ j) x)).val =
      (limit.π F j) y
    have hfacS := congrArg (fun q => q PUnit.unit) ((limit.isLimit FZ).fac S j)
    have hfacS' := congrArg
      (fun z => (WithTopology.ofTopology (t := tZ j) z).val) hfacS
    change (WithTopology.ofTopology (t := tZ j) ((limit.π FZ j) x)).val =
      (limit.π F j) y at hfacS'
    exact hfacS'
  have hrange : Set.range g = inverseLimitSet F Z :=
    le_antisymm hsubset hsupset
  rw [← hrange]
  exact hgrange

omit [IsCofiltered J] in
/-- The inverse limit of a cofiltered diagram of spectral spaces is
quasi-compact. -/
theorem inverseLimit_spectralDiagram_isCompact
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F) :
    CompactSpace ((limit F : TopCat.{max v u}) : Type (max v u)) := by
  let (j : J) : SpectralSpace (F.obj j) := hF.1 j
  let F' : J ⥤ TopCat.{max v u} :=
    { obj := fun j => TopCat.of (WithConstructibleTopology (F.obj j))
      map := fun {j i} f => TopCat.ofHom
        { toFun := fun x => WithTopology.toTopology _ (F.map f (WithTopology.ofTopology x))
          continuous_toFun := by
            have hcont : @Continuous (F.obj j) (F.obj i)
                (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i)) (F.map f) :=
              (isSpectralMap_iff_continuous_constructibleTopology
                (X := F.obj j) (Y := F.obj i) (f := F.map f)
                (hF.2 j i f).continuous).mp (hF.2 j i f)
            have hsource : @Continuous (WithConstructibleTopology (F.obj j)) (F.obj j)
                (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
                (constructibleTopology (F.obj j))
                (WithTopology.ofTopology : WithConstructibleTopology (F.obj j) → F.obj j) :=
              WithTopology.continuous_ofTopology (X := F.obj j)
                (t := constructibleTopology (F.obj j))
            have htarget : @Continuous (F.obj i) (WithConstructibleTopology (F.obj i))
                (constructibleTopology (F.obj i))
                (WithTopology.instTopologicalSpace (F.obj i) (constructibleTopology (F.obj i)))
                (WithTopology.toTopology (constructibleTopology (F.obj i))) :=
              WithTopology.continuous_toTopology (X := F.obj i)
                (t := constructibleTopology (F.obj i))
            have hcomp : @Continuous (WithConstructibleTopology (F.obj j)) (F.obj i)
                (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
                (constructibleTopology (F.obj i))
                (F.map f ∘ WithTopology.ofTopology) :=
              @Continuous.comp (WithConstructibleTopology (F.obj j)) (F.obj j) (F.obj i)
                (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
                (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i))
                (WithTopology.ofTopology) (F.map f) hcont hsource
            simpa [Function.comp_def] using
              (@Continuous.comp (WithConstructibleTopology (F.obj j)) (F.obj i)
                (WithConstructibleTopology (F.obj i))
                (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
                (constructibleTopology (F.obj i))
                (WithTopology.instTopologicalSpace (F.obj i) (constructibleTopology (F.obj i)))
                (F.map f ∘ WithTopology.ofTopology)
                (WithTopology.toTopology (constructibleTopology (F.obj i))) htarget hcomp)
        }
      map_id := by
        intro j
        apply TopCat.ext
        intro x
        simp
      map_comp := by
        intro j i k f g
        apply TopCat.ext
        intro x
        simp }
  let hK (j : J) : @CompactSpace (F.obj j) (constructibleTopology (F.obj j)) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := F.obj j)).2.2
  let hT (j : J) : @T2Space (F.obj j) (constructibleTopology (F.obj j)) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := F.obj j)).1
  let : ∀ j, CompactSpace (F'.obj j) := fun j => by
    change CompactSpace (WithConstructibleTopology (F.obj j))
    exact @Function.Surjective.compactSpace (F.obj j)
      (WithConstructibleTopology (F.obj j))
      (constructibleTopology (F.obj j))
      (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
      (WithTopology.toTopology (constructibleTopology (F.obj j)))
      (WithTopology.continuous_toTopology (X := F.obj j)
        (t := constructibleTopology (F.obj j)))
      (hK j)
      (WithTopology.toTopology_surjective (constructibleTopology (F.obj j)))
  let : ∀ j, T2Space (F'.obj j) := fun j => by
    change T2Space (WithConstructibleTopology (F.obj j))
    constructor
    intro x y hxy
    have hxy' : x.ofTopology ≠ y.ofTopology := by
      intro h
      apply hxy
      exact WithTopology.ext h
    obtain ⟨u, v, hu, hv, hxu, hyv, hd⟩ :=
      @T2Space.t2 (F.obj j) (constructibleTopology (F.obj j)) (hT j) x.ofTopology y.ofTopology hxy'
    refine ⟨WithTopology.ofTopology ⁻¹' u, WithTopology.ofTopology ⁻¹' v, ?_, ?_, ?_, ?_, ?_⟩
    · rw [WithTopology.isOpen_iff]
      change IsOpen[constructibleTopology (F.obj j)] u
      exact hu
    · rw [WithTopology.isOpen_iff]
      change IsOpen[constructibleTopology (F.obj j)] v
      exact hv
    · exact hxu
    · exact hyv
    · rw [Set.disjoint_left]
      intro z hzu hzv
      exact (Set.disjoint_left.1 hd) hzu hzv
  let : CompactSpace ((limit F' : TopCat.{max v u}) : Type (max v u)) :=
    Formalization.Books.Topology.Unit14.compactSpace_limit_of_compact_Hausdorff F'
  have hsource (j : J) : @Continuous (WithConstructibleTopology (F.obj j)) (F.obj j)
      (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
      _ (WithTopology.ofTopology : WithConstructibleTopology (F.obj j) → F.obj j) := by
    have hid : @Continuous (F.obj j) (F.obj j)
        (constructibleTopology (F.obj j)) _ id := by
      refine continuous_def.2 ?_
      intro U hU
      simpa using (isOpen_constructibleTopology_of_isOpen (X := F.obj j) hU)
    simpa [Function.comp_def] using
      (@Continuous.comp (WithConstructibleTopology (F.obj j)) (F.obj j) (F.obj j)
        (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
        (constructibleTopology (F.obj j)) _
        (WithTopology.ofTopology : WithConstructibleTopology (F.obj j) → F.obj j) id hid
        (WithTopology.continuous_ofTopology (X := F.obj j)
          (t := constructibleTopology (F.obj j))))
  let cone : Cone F :=
    { pt := limit F'
      π :=
        { app := fun j => TopCat.ofHom
            { toFun := fun x => WithTopology.ofTopology ((limit.π F' j) x)
              continuous_toFun :=
                (hsource j).comp (limit.π F' j).hom.2 }
          naturality := by
            intro j i f
            apply TopCat.ext
            intro x
            have hw := congrArg
              (fun q : (limit F' : TopCat.{max v u}) ⟶ F'.obj i =>
                WithTopology.ofTopology (t := constructibleTopology (F.obj i)) (q x))
              (limit.w F' f)
            simpa [F', CategoryTheory.comp_apply] using hw.symm }
      }
  let g : ((limit F' : TopCat.{max v u}) : Type (max v u)) →
      ((limit F : TopCat.{max v u}) : Type (max v u)) :=
    (limit.isLimit F).lift cone
  have hg : Continuous g := by
    exact (limit.isLimit F).lift cone |>.hom.2
  have hgsurj : Function.Surjective g := by
    intro y
    let S : Cone F' :=
      { pt := TopCat.of PUnit
        π :=
          { app := fun j => TopCat.ofHom
              { toFun := fun _ => WithTopology.toTopology _ ((limit.π F j) y)
                continuous_toFun := continuous_const }
            naturality := by
              intro j i f
              apply TopCat.ext
              intro z
              change WithTopology.toTopology (constructibleTopology (F.obj i)) ((limit.π F i) y) =
                WithTopology.toTopology (constructibleTopology (F.obj i))
                  (F.map f ((limit.π F j) y))
              exact congrArg (WithTopology.toTopology (constructibleTopology (F.obj i)))
                (congrArg (fun q => q y) (limit.w F f)).symm } }
    let y' := (limit.isLimit F').lift S PUnit.unit
    refine ⟨y', ?_⟩
    apply Concrete.limit_ext F
    intro j
    have hfac := congrArg (fun q => q PUnit.unit) ((limit.isLimit F').fac S j)
    change (limit.π F j) (g y') = (limit.π F j) y
    have hfacg := congrArg (fun q => q y') ((limit.isLimit F).fac cone j)
    have hfacg' : (limit.π F j) (g y') = (cone.π.app j) y' := by
      change (limit.cone F).π.app j ((limit.isLimit F).lift cone y') = (cone.π.app j) y'
      exact hfacg
    rw [hfacg']
    change WithTopology.ofTopology ((limit.π F' j) y') = (limit.π F j) y
    convert hfac using 1; simp [S, y']
  exact Function.Surjective.compactSpace hg hgsurj

end QuasiCompactness

section Nonemptiness

variable {J : Type v} [SmallCategory J] [IsCofiltered J]

/- Nonempty constructibly closed compatible subsets in a cofiltered spectral
diagram have nonempty inverse limit. -/
theorem inverseLimitSet_isNonempty_of_constructibleClosed
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (Z : ∀ j, Set (F.obj j))
    (hZnonempty : ∀ j, (Z j).Nonempty)
    (hZ : ∀ j, IsClosed[constructibleTopology (F.obj j)] (Z j))
    (hZmap : CompatibleSetFamily F Z) :
    (inverseLimitSet F Z).Nonempty := by
  classical
  let (j : J) : SpectralSpace (F.obj j) := hF.1 j
  let hK (j : J) : @CompactSpace (F.obj j) (constructibleTopology (F.obj j)) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := F.obj j)).2.2
  let hT (j : J) : @T2Space (F.obj j) (constructibleTopology (F.obj j)) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := F.obj j)).1
  let tZ (j : J) : TopologicalSpace (Z j) :=
    TopologicalSpace.induced (Subtype.val : Z j → F.obj j)
      (@constructibleTopology (F.obj j) (F.obj j).str)
  let Z' (j : J) := WithTopology (Z j) (tZ j)
  let hKsub (j : J) : @CompactSpace (Z j) (tZ j) := by
    have hcompact : @IsCompact (F.obj j) (constructibleTopology (F.obj j)) (Z j) :=
      @IsClosed.isCompact (F.obj j) (constructibleTopology (F.obj j)) (Z j) (hK j) (hZ j)
    exact (@isCompact_iff_compactSpace (F.obj j)
      (constructibleTopology (F.obj j)) (Z j)).mp hcompact
  let hTsub (j : J) : @T2Space (Z j) (tZ j) := by
    constructor
    intro x y hxy
    obtain ⟨u, v, hu, hv, hxu, hyv, hd⟩ :=
      @T2Space.t2 (F.obj j) (constructibleTopology (F.obj j)) (hT j)
        x.val y.val (by
          intro h
          apply hxy
          exact Subtype.ext h)
    refine ⟨Subtype.val ⁻¹' u, Subtype.val ⁻¹' v, ?_, ?_, ?_, ?_, ?_⟩
    · change IsOpen[TopologicalSpace.induced (Subtype.val : Z j → F.obj j)
        (@constructibleTopology (F.obj j) (F.obj j).str)] (Subtype.val ⁻¹' u)
      exact ⟨u, hu, rfl⟩
    · change IsOpen[TopologicalSpace.induced (Subtype.val : Z j → F.obj j)
        (@constructibleTopology (F.obj j) (F.obj j).str)] (Subtype.val ⁻¹' v)
      exact ⟨v, hv, rfl⟩
    · exact hxu
    · exact hyv
    · rw [Set.disjoint_left]
      intro z hzu hzv
      exact (Set.disjoint_left.1 hd) hzu hzv
  let FZ : J ⥤ TopCat.{max v u} :=
    { obj := fun j => TopCat.of (Z' j)
      map := fun {j i} f => TopCat.ofHom
        { toFun := fun x =>
            WithTopology.toTopology (tZ i)
              ⟨F.map f (WithTopology.ofTopology (t := tZ j) x).val,
                hZmap j i f ⟨(WithTopology.ofTopology (t := tZ j) x).val,
                  (WithTopology.ofTopology (t := tZ j) x).property, rfl⟩⟩
          continuous_toFun := by
            have hcont : @Continuous (F.obj j) (F.obj i)
                (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i)) (F.map f) :=
              (isSpectralMap_iff_continuous_constructibleTopology
                (X := F.obj j) (Y := F.obj i) (f := F.map f)
                (hF.2 j i f).continuous).mp (hF.2 j i f)
            have hmap : @Continuous (Z j) (Z i) (tZ j) (tZ i)
                (fun x =>
                  ⟨F.map f x.val, hZmap j i f ⟨x.val, x.property, rfl⟩⟩) :=
              by
                refine continuous_induced_rng.2 ?_
                have hsub : @Continuous (Z j) (F.obj j) (tZ j)
                    (@constructibleTopology (F.obj j) (F.obj j).str) Subtype.val := by
                  change @Continuous (Z j) (F.obj j)
                    (TopologicalSpace.induced Subtype.val
                      (@constructibleTopology (F.obj j) (F.obj j).str))
                    (@constructibleTopology (F.obj j) (F.obj j).str) Subtype.val
                  exact continuous_induced_dom
                have hcomp0 : @Continuous (Z j) (F.obj i) (tZ j)
                    (@constructibleTopology (F.obj i) (F.obj i).str)
                    (F.map f ∘ Subtype.val) :=
                  @Continuous.comp (Z j) (F.obj j) (F.obj i)
                    (tZ j) (@constructibleTopology (F.obj j) (F.obj j).str)
                    (@constructibleTopology (F.obj i) (F.obj i).str)
                    Subtype.val (F.map f) hcont hsub
                simpa [Function.comp_def] using hcomp0
            have hsource : @Continuous (Z' j) (Z j)
                (WithTopology.instTopologicalSpace (Z j) (tZ j)) (tZ j)
                (WithTopology.ofTopology : Z' j → Z j) :=
              WithTopology.continuous_ofTopology (X := Z j) (t := tZ j)
            have htarget : @Continuous (Z i) (Z' i) (tZ i)
                (WithTopology.instTopologicalSpace (Z i) (tZ i))
                (WithTopology.toTopology (tZ i)) :=
              WithTopology.continuous_toTopology (X := Z i) (t := tZ i)
            have hcomp : @Continuous (Z' j) (Z i)
                (WithTopology.instTopologicalSpace (Z j) (tZ j)) (tZ i)
                ((fun x =>
                  ⟨F.map f x.val, hZmap j i f ⟨x.val, x.property, rfl⟩⟩) ∘
                  (WithTopology.ofTopology : Z' j → Z j)) :=
              @Continuous.comp (Z' j) (Z j) (Z i)
                (WithTopology.instTopologicalSpace (Z j) (tZ j)) (tZ j) (tZ i)
                (WithTopology.ofTopology : Z' j → Z j)
                (fun x : Z j =>
                  ⟨F.map f x.val, hZmap j i f ⟨x.val, x.property, rfl⟩⟩)
                hmap hsource
            simpa [Function.comp_def, Z'] using
              (@Continuous.comp (Z' j) (Z i) (Z' i)
                (WithTopology.instTopologicalSpace (Z j) (tZ j)) (tZ i)
                (WithTopology.instTopologicalSpace (Z i) (tZ i))
                ((fun x : Z j =>
                  ⟨F.map f x.val, hZmap j i f ⟨x.val, x.property, rfl⟩⟩) ∘
                  (WithTopology.ofTopology : Z' j → Z j))
                (WithTopology.toTopology (tZ i)) htarget hcomp)
        }
      map_id := by
        intro j
        apply TopCat.ext
        intro x
        apply WithTopology.ext
        apply Subtype.ext
        simp
      map_comp := by
        intro j i k f g
        apply TopCat.ext
        intro x
        apply WithTopology.ext
        apply Subtype.ext
        simp }
  let : ∀ j, Nonempty (FZ.obj j) := fun j => by
    change Nonempty (WithTopology (Z j) (tZ j))
    rcases hZnonempty j with ⟨x, hx⟩
    exact ⟨WithTopology.toTopology (tZ j) ⟨x, hx⟩⟩
  let : ∀ j, CompactSpace (FZ.obj j) := fun j => by
    change CompactSpace (Z' j)
    exact @Function.Surjective.compactSpace (Z j) (Z' j) (tZ j)
      (WithTopology.instTopologicalSpace (Z j) (tZ j))
      (WithTopology.toTopology (tZ j))
      (WithTopology.continuous_toTopology (X := Z j) (t := tZ j))
      (hKsub j) (WithTopology.toTopology_surjective (tZ j))
  let : ∀ j, T2Space (FZ.obj j) := fun j => by
    change T2Space (Z' j)
    constructor
    intro x y hxy
    have hxy' : x.ofTopology ≠ y.ofTopology := by
      intro h
      apply hxy
      exact WithTopology.ext h
    obtain ⟨u, v, hu, hv, hxu, hyv, hd⟩ :=
      @T2Space.t2 (Z j) (tZ j) (hTsub j) x.ofTopology y.ofTopology hxy'
    refine ⟨WithTopology.ofTopology ⁻¹' u, WithTopology.ofTopology ⁻¹' v, ?_, ?_, ?_, ?_, ?_⟩
    · rw [WithTopology.isOpen_iff]
      change IsOpen[tZ j] u
      exact hu
    · rw [WithTopology.isOpen_iff]
      change IsOpen[tZ j] v
      exact hv
    · exact hxu
    · exact hyv
    · rw [Set.disjoint_left]
      intro z hzu hzv
      exact (Set.disjoint_left.1 hd) hzu hzv
  obtain ⟨x⟩ := Formalization.Books.Topology.Unit14.nonempty_cofiltered_limit_of_compact_Hausdorff FZ
  have hval (j : J) : @Continuous (Z j) (F.obj j) (tZ j)
      _ (Subtype.val) := by
    have hid : @Continuous (F.obj j) (F.obj j)
        (constructibleTopology (F.obj j)) _ id := by
      refine continuous_def.2 ?_
      intro U hU
      simpa using (isOpen_constructibleTopology_of_isOpen (X := F.obj j) hU)
    simpa [Function.comp_def] using
      (@Continuous.comp (Z j) (F.obj j) (F.obj j)
        (tZ j) (constructibleTopology (F.obj j)) _
        (Subtype.val) id hid continuous_induced_dom)
  have hval' (j : J) : @Continuous (Z' j) (F.obj j)
      (WithTopology.instTopologicalSpace (Z j) (tZ j))
      _
      (fun x => (WithTopology.ofTopology (t := tZ j) x).val) := by
    simpa [Function.comp_def, Z'] using
      (@Continuous.comp (Z' j) (Z j) (F.obj j)
        (WithTopology.instTopologicalSpace (Z j) (tZ j)) (tZ j) _
        (WithTopology.ofTopology : Z' j → Z j) Subtype.val (hval j)
        (WithTopology.continuous_ofTopology (X := Z j) (t := tZ j)))
  let cone : Cone F :=
    { pt := limit FZ
      π :=
        { app := fun j => TopCat.ofHom
            { toFun := fun x => (WithTopology.ofTopology (t := tZ j) ((limit.π FZ j) x)).val
              continuous_toFun := hval' j |>.comp (limit.π FZ j).hom.2 }
          naturality := by
            intro j i f
            apply TopCat.ext
            intro z
            have hw := congrArg
              (fun q : (limit FZ : TopCat.{max v u}) ⟶ FZ.obj i =>
                (WithTopology.ofTopology (t := tZ i) (q z)).val)
              (limit.w FZ f)
            simpa [FZ, Z', CategoryTheory.comp_apply] using hw.symm } }
  let y := (limit.isLimit F).lift cone x
  refine ⟨y, ?_⟩
  intro j
  have hfac := congrArg (fun q => q x) ((limit.isLimit F).fac cone j)
  have hfac' : (limit.π F j) y = (cone.π.app j) x := by
    change (limit.cone F).π.app j ((limit.isLimit F).lift cone x) = (cone.π.app j) x
    exact hfac
  rw [hfac']
  exact (WithTopology.ofTopology (t := tZ j) ((limit.π FZ j) x)).property

/-- The inverse limit of a cofiltered diagram of nonempty spectral spaces is
nonempty. -/
theorem inverseLimit_spectralDiagram_isNonempty
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (hXnonempty : ∀ j, Nonempty (F.obj j)) :
    Nonempty ((limit F : TopCat.{max v u}) : Type (max v u)) := by
  let (j : J) : SpectralSpace (F.obj j) := hF.1 j
  let F' : J ⥤ TopCat.{max v u} :=
    { obj := fun j => TopCat.of (WithConstructibleTopology (F.obj j))
      map := fun {j i} f => TopCat.ofHom
        { toFun := fun x => WithTopology.toTopology _ (F.map f (WithTopology.ofTopology x))
          continuous_toFun := by
            have hcont : @Continuous (F.obj j) (F.obj i)
                (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i)) (F.map f) :=
              (isSpectralMap_iff_continuous_constructibleTopology
                (X := F.obj j) (Y := F.obj i) (f := F.map f)
                (hF.2 j i f).continuous).mp (hF.2 j i f)
            have hsource : @Continuous (WithConstructibleTopology (F.obj j)) (F.obj j)
                (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
                (constructibleTopology (F.obj j))
                (WithTopology.ofTopology : WithConstructibleTopology (F.obj j) → F.obj j) :=
              WithTopology.continuous_ofTopology (X := F.obj j)
                (t := constructibleTopology (F.obj j))
            have htarget : @Continuous (F.obj i) (WithConstructibleTopology (F.obj i))
                (constructibleTopology (F.obj i))
                (WithTopology.instTopologicalSpace (F.obj i) (constructibleTopology (F.obj i)))
                (WithTopology.toTopology (constructibleTopology (F.obj i))) :=
              WithTopology.continuous_toTopology (X := F.obj i)
                (t := constructibleTopology (F.obj i))
            have hcomp : @Continuous (WithConstructibleTopology (F.obj j)) (F.obj i)
                (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
                (constructibleTopology (F.obj i))
                (F.map f ∘ WithTopology.ofTopology) :=
              @Continuous.comp (WithConstructibleTopology (F.obj j)) (F.obj j) (F.obj i)
                (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
                (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i))
                (WithTopology.ofTopology) (F.map f) hcont hsource
            simpa [Function.comp_def] using
              (@Continuous.comp (WithConstructibleTopology (F.obj j)) (F.obj i)
                (WithConstructibleTopology (F.obj i))
                (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
                (constructibleTopology (F.obj i))
                (WithTopology.instTopologicalSpace (F.obj i) (constructibleTopology (F.obj i)))
                (F.map f ∘ WithTopology.ofTopology)
                (WithTopology.toTopology (constructibleTopology (F.obj i))) htarget hcomp)
        }
      map_id := by
        intro j
        apply TopCat.ext
        intro x
        simp
      map_comp := by
        intro j i k f g
        apply TopCat.ext
        intro x
        simp }
  let hK (j : J) : @CompactSpace (F.obj j) (constructibleTopology (F.obj j)) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := F.obj j)).2.2
  let hT (j : J) : @T2Space (F.obj j) (constructibleTopology (F.obj j)) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := F.obj j)).1
  let : ∀ j, Nonempty (F'.obj j) := fun j => by
    change Nonempty (WithConstructibleTopology (F.obj j))
    rcases hXnonempty j with ⟨x⟩
    exact ⟨WithTopology.toTopology _ x⟩
  let : ∀ j, CompactSpace (F'.obj j) := fun j => by
    change CompactSpace (WithConstructibleTopology (F.obj j))
    exact @Function.Surjective.compactSpace (F.obj j)
      (WithConstructibleTopology (F.obj j))
      (constructibleTopology (F.obj j))
      (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
      (WithTopology.toTopology (constructibleTopology (F.obj j)))
      (WithTopology.continuous_toTopology (X := F.obj j)
        (t := constructibleTopology (F.obj j)))
      (hK j)
      (WithTopology.toTopology_surjective (constructibleTopology (F.obj j)))
  let : ∀ j, T2Space (F'.obj j) := fun j => by
    change T2Space (WithConstructibleTopology (F.obj j))
    constructor
    intro x y hxy
    have hxy' : x.ofTopology ≠ y.ofTopology := by
      intro h
      apply hxy
      exact WithTopology.ext h
    obtain ⟨u, v, hu, hv, hxu, hyv, hd⟩ :=
      @T2Space.t2 (F.obj j) (constructibleTopology (F.obj j)) (hT j) x.ofTopology y.ofTopology hxy'
    refine ⟨WithTopology.ofTopology ⁻¹' u, WithTopology.ofTopology ⁻¹' v, ?_, ?_, ?_, ?_, ?_⟩
    · rw [WithTopology.isOpen_iff]
      change IsOpen[constructibleTopology (F.obj j)] u
      exact hu
    · rw [WithTopology.isOpen_iff]
      change IsOpen[constructibleTopology (F.obj j)] v
      exact hv
    · exact hxu
    · exact hyv
    · rw [Set.disjoint_left]
      intro z hzu hzv
      exact (Set.disjoint_left.1 hd) hzu hzv
  obtain ⟨x⟩ := Formalization.Books.Topology.Unit14.nonempty_cofiltered_limit_of_compact_Hausdorff F'
  have hsource (j : J) : @Continuous (WithConstructibleTopology (F.obj j)) (F.obj j)
      (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
      _ (WithTopology.ofTopology : WithConstructibleTopology (F.obj j) → F.obj j) := by
    have hid : @Continuous (F.obj j) (F.obj j)
        (constructibleTopology (F.obj j)) _ id := by
      refine continuous_def.2 ?_
      intro U hU
      simpa using (isOpen_constructibleTopology_of_isOpen (X := F.obj j) hU)
    simpa [Function.comp_def] using
      (@Continuous.comp (WithConstructibleTopology (F.obj j)) (F.obj j) (F.obj j)
        (WithTopology.instTopologicalSpace (F.obj j) (constructibleTopology (F.obj j)))
        (constructibleTopology (F.obj j)) _
        (WithTopology.ofTopology : WithConstructibleTopology (F.obj j) → F.obj j) id hid
        (WithTopology.continuous_ofTopology (X := F.obj j)
          (t := constructibleTopology (F.obj j))))
  let cone : Cone F :=
    { pt := limit F'
      π :=
        { app := fun j => TopCat.ofHom
            { toFun := fun x => WithTopology.ofTopology ((limit.π F' j) x)
              continuous_toFun := (hsource j).comp (limit.π F' j).hom.2 }
          naturality := by
            intro j i f
            apply TopCat.ext
            intro z
            have hw := congrArg
              (fun q : (limit F' : TopCat.{max v u}) ⟶ F'.obj i =>
                WithTopology.ofTopology (t := constructibleTopology (F.obj i)) (q z))
              (limit.w F' f)
            simpa [F', CategoryTheory.comp_apply] using hw.symm } }
  exact ⟨(limit.isLimit F).lift cone x⟩

end Nonemptiness

section ConstructibleInclusions

variable {J : Type v} [SmallCategory J] [IsCofiltered J]

/-- An inclusion between inverse-image subsets at one stage is witnessed at a
single stage of a cofiltered spectral diagram. -/
theorem inverseLimit_preimage_subset_iff
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (i : J) {E G : Set (F.obj i)}
    (hE : IsClosed[constructibleTopology (F.obj i)] E)
    (hG : IsOpen[constructibleTopology (F.obj i)] G) :
    (limit.π F i) ⁻¹' E ⊆ (limit.π F i) ⁻¹' G ↔
      ∃ (j : J) (f : j ⟶ i), (F.map f) ⁻¹' E ⊆ (F.map f) ⁻¹' G := by
  classical
  let (j : J) : SpectralSpace (F.obj j) := hF.1 j
  let K := CategoryTheory.Over i
  let : IsCofiltered K := inferInstance
  let bad (a : K) : Set (F.obj a.left) :=
    (F.map a.hom) ⁻¹' E \ (F.map a.hom) ⁻¹' G
  have hbadclosed (a : K) :
      IsClosed[constructibleTopology (F.obj a.left)] (bad a) := by
    have hcont : @Continuous (F.obj a.left) (F.obj i)
        (constructibleTopology (F.obj a.left)) (constructibleTopology (F.obj i))
        (F.map a.hom) :=
      (isSpectralMap_iff_continuous_constructibleTopology
        (X := F.obj a.left) (Y := F.obj i) (f := F.map a.hom)
        (hF.2 a.left i a.hom).continuous).mp (hF.2 a.left i a.hom)
    have h1 : IsClosed[constructibleTopology (F.obj a.left)]
        ((F.map a.hom) ⁻¹' E) :=
      @IsClosed.preimage (F.obj a.left) (F.obj i)
        (constructibleTopology (F.obj a.left)) (constructibleTopology (F.obj i))
        (F.map a.hom) hcont E hE
    have hGc : IsClosed[constructibleTopology (F.obj i)] Gᶜ :=
      (@isClosed_compl_iff (F.obj i) (constructibleTopology (F.obj i)) G).2 hG
    have h2 : IsClosed[constructibleTopology (F.obj a.left)]
        ((F.map a.hom) ⁻¹' G)ᶜ :=
      @IsClosed.preimage (F.obj a.left) (F.obj i)
        (constructibleTopology (F.obj a.left)) (constructibleTopology (F.obj i))
        (F.map a.hom) hcont Gᶜ hGc
    simpa [bad, Set.sdiff_eq] using
      @IsClosed.inter (F.obj a.left) ((F.map a.hom) ⁻¹' E)
        ((F.map a.hom) ⁻¹' G)ᶜ (constructibleTopology (F.obj a.left)) h1 h2
  have hbadmap (a b : K) (q : a ⟶ b) :
      MapsTo (F.map q.left) (bad a) (bad b) := by
    intro x hx
    change F.map a.hom x ∈ E ∧ F.map a.hom x ∉ G at hx
    change F.map b.hom (F.map q.left x) ∈ E ∧ F.map b.hom (F.map q.left x) ∉ G
    have hq : F.map b.hom (F.map q.left x) = F.map a.hom x := by
      have hq' := congrArg (fun r => r x) (F.map_comp q.left b.hom)
      simpa [CategoryTheory.comp_apply, Over.w q] using hq'.symm
    rw [hq]
    exact hx
  let tbad (a : K) : TopologicalSpace (bad a) :=
    TopologicalSpace.induced (Subtype.val : bad a → F.obj a.left)
      (constructibleTopology (F.obj a.left))
  let HObj (a : K) := WithTopology (bad a) (tbad a)
  have hmap (a b : K) (q : a ⟶ b) :
      @Continuous (bad a) (bad b) (tbad a) (tbad b)
        (fun x => ⟨F.map q.left x.val, hbadmap a b q x.property⟩) := by
    refine continuous_induced_rng.2 ?_
    have hcont : @Continuous (F.obj a.left) (F.obj b.left)
        (constructibleTopology (F.obj a.left)) (constructibleTopology (F.obj b.left))
        (F.map q.left) :=
      (isSpectralMap_iff_continuous_constructibleTopology
        (X := F.obj a.left) (Y := F.obj b.left) (f := F.map q.left)
        (hF.2 a.left b.left q.left).continuous).mp (hF.2 a.left b.left q.left)
    have hsub : @Continuous (bad a) (F.obj a.left) (tbad a)
        (constructibleTopology (F.obj a.left)) Subtype.val := by
      change @Continuous (bad a) (F.obj a.left)
        (TopologicalSpace.induced (Subtype.val : bad a → F.obj a.left)
          (constructibleTopology (F.obj a.left)))
        (constructibleTopology (F.obj a.left)) Subtype.val
      exact continuous_induced_dom
    have hcomp : @Continuous (bad a) (F.obj b.left) (tbad a)
        (constructibleTopology (F.obj b.left))
        (F.map q.left ∘ Subtype.val) :=
      @Continuous.comp (bad a) (F.obj a.left) (F.obj b.left)
        (tbad a) (constructibleTopology (F.obj a.left))
        (constructibleTopology (F.obj b.left))
        Subtype.val (F.map q.left) hcont hsub
    simpa [Function.comp_def] using hcomp
  let H : K ⥤ TopCat.{max v u} :=
    { obj := fun a => TopCat.of (HObj a)
      map := fun {a b} q => TopCat.ofHom
        { toFun := fun x =>
            WithTopology.toTopology (tbad b)
              ⟨F.map q.left (WithTopology.ofTopology (t := tbad a) x).val,
                hbadmap a b q (WithTopology.ofTopology (t := tbad a) x).property⟩
          continuous_toFun := by
            have hsource : @Continuous (HObj a) (bad a)
                (WithTopology.instTopologicalSpace (bad a) (tbad a)) (tbad a)
                (WithTopology.ofTopology : HObj a → bad a) :=
              WithTopology.continuous_ofTopology (X := bad a) (t := tbad a)
            have htarget : @Continuous (bad b) (HObj b) (tbad b)
                (WithTopology.instTopologicalSpace (bad b) (tbad b))
                (WithTopology.toTopology (tbad b)) :=
              WithTopology.continuous_toTopology (X := bad b) (t := tbad b)
            have hcomp : @Continuous (HObj a) (bad b)
                (WithTopology.instTopologicalSpace (bad a) (tbad a)) (tbad b)
                ((fun x : bad a =>
                  ⟨F.map q.left x.val, hbadmap a b q x.property⟩) ∘
                  (WithTopology.ofTopology : HObj a → bad a)) := by
              simpa [Function.comp_def] using (hmap a b q).comp hsource
            simpa [Function.comp_def, HObj] using
              (@Continuous.comp (HObj a) (bad b) (HObj b)
                (WithTopology.instTopologicalSpace (bad a) (tbad a)) (tbad b)
                (WithTopology.instTopologicalSpace (bad b) (tbad b))
                ((fun x : bad a =>
                  ⟨F.map q.left x.val, hbadmap a b q x.property⟩) ∘
                  (WithTopology.ofTopology : HObj a → bad a))
                (WithTopology.toTopology (tbad b)) htarget hcomp) }
      map_id := by
        intro a
        apply TopCat.ext
        intro x
        apply WithTopology.ext
        apply Subtype.ext
        change F.map (𝟙 a.left) x.ofTopology = x.ofTopology
        simp
      map_comp := by
        intro a b c f g
        apply TopCat.ext
        intro x
        apply WithTopology.ext
        apply Subtype.ext
        change F.map (f.left ≫ g.left) x.ofTopology =
          F.map g.left (F.map f.left x.ofTopology)
        have hcomp := congrArg (fun r => r x.ofTopology) (F.map_comp f.left g.left)
        convert hcomp using 1; simp }
  let hK (a : K) : @CompactSpace (F.obj a.left)
      (constructibleTopology (F.obj a.left)) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact
      (X := F.obj a.left)).2.2
  let hT (a : K) : @T2Space (F.obj a.left)
      (constructibleTopology (F.obj a.left)) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact
      (X := F.obj a.left)).1
  let hKsub (a : K) : @CompactSpace (bad a) (tbad a) := by
    have hcompact : @IsCompact (F.obj a.left)
        (constructibleTopology (F.obj a.left)) (bad a) :=
      @IsClosed.isCompact (F.obj a.left) (constructibleTopology (F.obj a.left))
        (bad a) (hK a) (hbadclosed a)
    exact (@isCompact_iff_compactSpace (F.obj a.left)
      (constructibleTopology (F.obj a.left)) (bad a)).mp hcompact
  let hTsub (a : K) : @T2Space (bad a) (tbad a) := by
    constructor
    intro x y hxy
    obtain ⟨u, v, hu, hv, hxu, hyv, hd⟩ :=
      @T2Space.t2 (F.obj a.left) (constructibleTopology (F.obj a.left)) (hT a)
        x.val y.val (by
          intro h
          apply hxy
          exact Subtype.ext h)
    refine ⟨Subtype.val ⁻¹' u, Subtype.val ⁻¹' v, ?_, ?_, ?_, ?_, ?_⟩
    · change IsOpen[TopologicalSpace.induced (Subtype.val : bad a → F.obj a.left)
        (constructibleTopology (F.obj a.left))] (Subtype.val ⁻¹' u)
      exact ⟨u, hu, rfl⟩
    · change IsOpen[TopologicalSpace.induced (Subtype.val : bad a → F.obj a.left)
        (constructibleTopology (F.obj a.left))] (Subtype.val ⁻¹' v)
      exact ⟨v, hv, rfl⟩
    · exact hxu
    · exact hyv
    · rw [Set.disjoint_left]
      intro z hzu hzv
      exact (Set.disjoint_left.1 hd) hzu hzv
  let : ∀ a, CompactSpace (H.obj a) := fun a => by
    change CompactSpace (HObj a)
    exact @Function.Surjective.compactSpace (bad a) (HObj a) (tbad a)
      (WithTopology.instTopologicalSpace (bad a) (tbad a))
      (WithTopology.toTopology (tbad a))
      (WithTopology.continuous_toTopology (X := bad a) (t := tbad a))
      (hKsub a) (WithTopology.toTopology_surjective (tbad a))
  let : ∀ a, T2Space (H.obj a) := fun a => by
    change T2Space (HObj a)
    constructor
    intro x y hxy
    have hxy' : x.ofTopology ≠ y.ofTopology := by
      intro h
      apply hxy
      exact WithTopology.ext h
    obtain ⟨u, v, hu, hv, hxu, hyv, hd⟩ :=
      @T2Space.t2 (bad a) (tbad a) (hTsub a) x.ofTopology y.ofTopology hxy'
    refine ⟨WithTopology.ofTopology ⁻¹' u, WithTopology.ofTopology ⁻¹' v, ?_, ?_, ?_, ?_, ?_⟩
    · rw [WithTopology.isOpen_iff]
      change IsOpen[tbad a] u
      exact hu
    · rw [WithTopology.isOpen_iff]
      change IsOpen[tbad a] v
      exact hv
    · exact hxu
    · exact hyv
    · rw [Set.disjoint_left]
      intro z hzu hzv
      exact (Set.disjoint_left.1 hd) hzu hzv
  constructor
  · intro hsubset
    classical
    by_contra hno
    have hbadnonempty (a : K) : (bad a).Nonempty := by
      have hnot : ¬ (F.map a.hom) ⁻¹' E ⊆ (F.map a.hom) ⁻¹' G := by
        intro hsub
        exact hno ⟨a.left, a.hom, hsub⟩
      obtain ⟨x, hxE, hxG⟩ := Set.not_subset.mp hnot
      exact ⟨x, ⟨hxE, hxG⟩⟩
    let : ∀ a, Nonempty (H.obj a) := fun a => by
      change Nonempty (HObj a)
      obtain ⟨x, hx⟩ := hbadnonempty a
      exact ⟨WithTopology.toTopology (tbad a) ⟨x, hx⟩⟩
    obtain ⟨z⟩ := Formalization.Books.Topology.Unit14.nonempty_cofiltered_limit_of_compact_Hausdorff H
    let P : K ⥤ J := CategoryTheory.Over.forget i
    let hval (a : K) : @Continuous (HObj a) (F.obj a.left)
        (WithTopology.instTopologicalSpace (bad a) (tbad a))
        _
        (fun x => (WithTopology.ofTopology (t := tbad a) x).val) := by
      have hvalc : @Continuous (HObj a) (F.obj a.left)
          (WithTopology.instTopologicalSpace (bad a) (tbad a))
          (constructibleTopology (F.obj a.left))
          (fun x => (WithTopology.ofTopology (t := tbad a) x).val) := by
        have hsub : @Continuous (bad a) (F.obj a.left) (tbad a)
          (constructibleTopology (F.obj a.left)) Subtype.val := by
          change @Continuous (bad a) (F.obj a.left)
            (TopologicalSpace.induced (Subtype.val : bad a → F.obj a.left)
              (constructibleTopology (F.obj a.left)))
            (constructibleTopology (F.obj a.left)) Subtype.val
          exact continuous_induced_dom
        simpa [Function.comp_def, HObj] using
          (@Continuous.comp (HObj a) (bad a) (F.obj a.left)
            (WithTopology.instTopologicalSpace (bad a) (tbad a)) (tbad a)
            (constructibleTopology (F.obj a.left))
            (WithTopology.ofTopology : HObj a → bad a) Subtype.val hsub
            (WithTopology.continuous_ofTopology (X := bad a) (t := tbad a)))
      have hid : @Continuous (F.obj a.left) (F.obj a.left)
          (constructibleTopology (F.obj a.left)) _ id := by
        refine continuous_def.2 ?_
        intro U hU
        change IsOpen[constructibleTopology (F.obj a.left)] U
        exact isOpen_constructibleTopology_of_isOpen (X := F.obj a.left) hU
      simpa [Function.comp_def] using
        (@Continuous.comp (HObj a) (F.obj a.left) (F.obj a.left)
          (WithTopology.instTopologicalSpace (bad a) (tbad a))
          (constructibleTopology (F.obj a.left)) _
          (fun x => (WithTopology.ofTopology (t := tbad a) x).val) id hid hvalc)
    let conePF : Cone (P ⋙ F) :=
      { pt := limit H
        π :=
          { app := fun a => TopCat.ofHom
              { toFun := fun x =>
                  (WithTopology.ofTopology (t := tbad a) ((limit.π H a) x)).val
                continuous_toFun := by
                  change @Continuous ((limit H : TopCat.{max v u}) : Type (max v u))
                    (F.obj a.left) _ _
                    (fun x => (WithTopology.ofTopology (t := tbad a)
                      ((limit.π H a) x)).val)
                  simpa [Function.comp_def, P] using
                    (@Continuous.comp ((limit H : TopCat.{max v u}) : Type (max v u))
                      (HObj a) (F.obj a.left)
                      _ (WithTopology.instTopologicalSpace (bad a) (tbad a)) _
                      (limit.π H a).hom
                      (fun x : HObj a =>
                        (WithTopology.ofTopology (t := tbad a) x).val)
                      (hval a) (limit.π H a).hom.2) }
            naturality := by
              intro a b q
              apply TopCat.ext
              intro x
              change (WithTopology.ofTopology (t := tbad b) ((limit.π H b) x)).val =
                (F.map q.left)
                  ((WithTopology.ofTopology (t := tbad a) ((limit.π H a) x)).val)
              have hw := congrArg
                (fun r : (limit H : TopCat.{max v u}) ⟶ H.obj b =>
                  (WithTopology.ofTopology (t := tbad b) (r x)).val)
                (limit.w H q)
              have hw' :
                  (WithTopology.ofTopology (t := tbad b)
                    ((H.map q) ((limit.π H a) x))).val =
                    (WithTopology.ofTopology (t := tbad b) ((limit.π H b) x)).val := by
                convert hw using 1; simp
              change (F.map q.left)
                  ((WithTopology.ofTopology (t := tbad a) ((limit.π H a) x)).val) =
                (WithTopology.ofTopology (t := tbad b) ((limit.π H b) x)).val at hw'
              exact hw'.symm } }
    let g0 : limit H ⟶ limit (P ⋙ F) := (limit.isLimit (P ⋙ F)).lift conePF
    let g : limit H ⟶ limit F := g0 ≫ inv (limit.pre F P)
    let a₀ : K := CategoryTheory.Over.mk (𝟙 i)
    let za : bad a₀ :=
      WithTopology.ofTopology (t := tbad a₀) ((limit.π H a₀) z)
    have hza : F.map a₀.hom za.val ∈ E ∧ F.map a₀.hom za.val ∉ G := za.property
    have hcat : g ≫ limit.π F (P.obj a₀) =
        g0 ≫ limit.π (P ⋙ F) a₀ := by
      dsimp [g]
      rw [Category.assoc]
      have hpre : inv (limit.pre F P) ≫ limit.π F (P.obj a₀) =
          limit.π (P ⋙ F) a₀ := by
        rw [← limit.pre_π F P a₀]
        simp
      rw [hpre]
    have hfac0 := congrArg (fun q => q z)
      ((limit.isLimit (P ⋙ F)).fac conePF a₀)
    have hfac := congrArg (fun q => q z) hcat
    have hcoord : (limit.π F i) (g z) = za.val := by
      have hfac' : (limit.π F (P.obj a₀)) (g z) =
          (limit.π (P ⋙ F) a₀) (g0 z) := by
        simpa [CategoryTheory.comp_apply] using hfac
      change (limit.π F (P.obj a₀)) (g z) = za.val
      rw [hfac']
      change (limit.π (P ⋙ F) a₀) (g0 z) =
        (conePF.π.app a₀) z at hfac0
      rw [hfac0]
      rfl
    have hxE : (limit.π F i) (g z) ∈ E := by
      rw [hcoord]
      simpa [a₀] using hza.1
    have hxG : (limit.π F i) (g z) ∉ G := by
      rw [hcoord]
      simpa [a₀] using hza.2
    exact hxG (hsubset hxE)
  · rintro ⟨j, f, hfg⟩ x hxE
    have hfac := congrArg (fun q => q x) (limit.w F f)
    have hxj : (F.map f) ((limit.π F j) x) ∈ E := by
      change (limit.π F i) x ∈ E at hxE
      simpa [CategoryTheory.comp_apply] using hxE
    have hxjG := hfg hxj
    change (F.map f) ((limit.π F j) x) ∈ G at hxjG
    simpa [CategoryTheory.comp_apply] using hfac.symm ▸ hxjG

/-- Every constructible subset of a cofiltered inverse limit descends to one
stage; source-open and source-closed subsets descend to an open and closed
subset, respectively. -/
theorem inverseLimit_constructibleSet_descends
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    {E : Set ((limit F : TopCat.{max v u}) : Type (max v u))}
    (hE : IsConstructible E) :
    ∃ (i : J) (E_i : Set (F.obj i)),
      IsConstructible E_i ∧
        ((IsOpen E → IsOpen E_i) ∧ (IsClosed E → IsClosed E_i)) ∧
          (limit.π F i) ⁻¹' E_i = E := by
  classical
  let (j : J) : SpectralSpace (F.obj j) := hF.1 j
  let : CompactSpace ((limit F : TopCat.{max v u}) : Type (max v u)) :=
    inverseLimit_spectralDiagram_isCompact F hF
  have hdesc_open {U : Set ((limit F : TopCat.{max v u}) : Type (max v u))}
      (hUopen : IsOpen U) (hUconstructible : IsConstructible U) :
      ∃ (i : J) (U_i : Set (F.obj i)),
        IsOpen U_i ∧ IsCompact U_i ∧ (limit.π F i) ⁻¹' U_i = U := by
    have hUcompact : IsCompact U := by
      have hUretro : IsRetrocompact U :=
        Formalization.Books.Topology.Unit15.isRetrocompact_of_isConstructible
          hUconstructible
      simpa [Set.inter_univ] using hUretro isCompact_univ isOpen_univ
    obtain ⟨j, V, hVopen, hUV⟩ :=
      Formalization.Books.Topology.Unit14.cofiltered_limit_quasiCompact_open_eq_preimage
        F hUopen hUcompact
    let B : Set (Set (F.obj j)) :=
      {W | IsOpen W ∧ IsCompact W ∧ W ⊆ V}
    let I₀ := {W : Set (F.obj j) // W ∈ B}
    let A : I₀ → Set ((limit F : TopCat.{max v u}) : Type (max v u)) := fun W =>
      (limit.π F j) ⁻¹' (W : Set (F.obj j))
    have hAopen : ∀ W, IsOpen (A W) := by
      intro W
      exact W.property.1.preimage (limit.π F j).hom.2
    have hcover : U ⊆ ⋃ W, A W := by
      intro x hx
      have hxV : (limit.π F j) x ∈ V := by
        simpa [hUV] using hx
      obtain ⟨W, hW, hxW, hWV⟩ :=
        (PrespectralSpace.isTopologicalBasis (X := F.obj j)).exists_subset_of_mem_open
          hxV hVopen
      exact mem_iUnion.2 ⟨⟨W, hW.1, hW.2, hWV⟩, hxW⟩
    obtain ⟨t, ht⟩ := hUcompact.elim_finite_subcover A hAopen hcover
    let Q : Set (F.obj j) := ⋃ W ∈ t, (W : Set (F.obj j))
    have hQopen : IsOpen Q := by
      dsimp [Q]
      exact isOpen_iUnion fun W => isOpen_iUnion fun _ => W.property.1
    have hQcompact : IsCompact Q := by
      dsimp [Q]
      exact t.isCompact_biUnion (fun W _ => W.property.2.1)
    have hQV : Q ⊆ V := by
      intro x hx
      obtain ⟨W, hW, hxW⟩ := mem_iUnion₂.1 hx
      exact W.property.2.2 hxW
    refine ⟨j, Q, hQopen, hQcompact, ?_⟩
    ext x
    constructor
    · intro hx
      have hx' : x ∈ U := by
        rw [hUV]
        exact hQV (by simpa [Q] using hx)
      exact hx'
    · intro hx
      have hx' := ht hx
      simpa [A, Q] using hx'

  have hdesc_generic :
      ∃ (i : J) (E_i : Set (F.obj i)),
        IsConstructible E_i ∧ (limit.π F i) ⁻¹' E_i = E := by
    obtain ⟨n, U, V, hU, hV, hEeq⟩ :=
      _root_.Formalization.Books.Topology.Unit15.isConstructible_iff_finite_union_open_retrocompact_sdiff.mp hE
    choose i Ui hUiopen hUicomp hUiEq using fun l =>
      hdesc_open (hU l).1 ((hU l).2.isConstructible (hU l).1)
    choose j Vj hVjopen hVjcomp hVjEq using fun l =>
      hdesc_open (hV l).1 ((hV l).2.isConstructible (hV l).1)
    let s : Finset J := Finset.univ.image i ∪ Finset.univ.image j
    obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists s
    have hki (l : Fin n) : k ⟶ i l :=
      (hk (show i l ∈ Finset.univ.image i ∪ Finset.univ.image j from
        Finset.mem_union_left _
          (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩))).some
    have hkj (l : Fin n) : k ⟶ j l :=
      (hk (show j l ∈ Finset.univ.image i ∪ Finset.univ.image j from
        Finset.mem_union_right _
          (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩))).some
    let E_k : Set (F.obj k) :=
      ⋃ l, (F.map (hki l)) ⁻¹' (Ui l) ∩ ((F.map (hkj l)) ⁻¹' (Vj l))ᶜ
    have hE_k : IsConstructible E_k := by
      dsimp [E_k]
      apply IsConstructible.iUnion
      intro l
      have hUopen' : IsOpen ((F.map (hki l)) ⁻¹' Ui l) :=
        hUiopen l |>.preimage (F.map (hki l)).hom.2
      have hUcompact' : IsCompact ((F.map (hki l)) ⁻¹' Ui l) :=
        (hF.2 k (i l) (hki l)).isCompact_preimage_of_isOpen
          (hUiopen l) (hUicomp l)
      have hVopen' : IsOpen ((F.map (hkj l)) ⁻¹' Vj l) :=
        hVjopen l |>.preimage (F.map (hkj l)).hom.2
      have hVcompact' : IsCompact ((F.map (hkj l)) ⁻¹' Vj l) :=
        (hF.2 k (j l) (hkj l)).isCompact_preimage_of_isOpen
          (hVjopen l) (hVjcomp l)
      exact (hUcompact'.isConstructible hUopen').inter
        ((hVcompact'.isConstructible hVopen').compl)
    have hpreU (l : Fin n) :
        (limit.π F k) ⁻¹' ((F.map (hki l)) ⁻¹' Ui l) = U l := by
      ext x
      have hcoord : (limit.π F (i l)) x =
          (F.map (hki l)) ((limit.π F k) x) := by
        rw [← ConcreteCategory.comp_apply, limit.w F (hki l)]
      change (F.map (hki l)) ((limit.π F k) x) ∈ Ui l ↔ x ∈ U l
      rw [← hcoord]
      change x ∈ (limit.π F (i l)) ⁻¹' Ui l ↔ x ∈ U l
      rw [hUiEq l]
    have hpreV (l : Fin n) :
        (limit.π F k) ⁻¹' ((F.map (hkj l)) ⁻¹' Vj l) = V l := by
      ext x
      have hcoord : (limit.π F (j l)) x =
          (F.map (hkj l)) ((limit.π F k) x) := by
        rw [← ConcreteCategory.comp_apply, limit.w F (hkj l)]
      change (F.map (hkj l)) ((limit.π F k) x) ∈ Vj l ↔ x ∈ V l
      rw [← hcoord]
      change x ∈ (limit.π F (j l)) ⁻¹' Vj l ↔ x ∈ V l
      rw [hVjEq l]
    have hpreterm (l : Fin n) :
        (limit.π F k) ⁻¹'
            ((F.map (hki l)) ⁻¹' Ui l ∩ ((F.map (hkj l)) ⁻¹' Vj l)ᶜ) =
          U l ∩ (V l)ᶜ := by
      rw [preimage_inter, preimage_compl, hpreU l, hpreV l]
    refine ⟨k, E_k, hE_k, ?_⟩
    calc
      (limit.π F k) ⁻¹' E_k =
          ⋃ l, (limit.π F k) ⁻¹'
            ((F.map (hki l)) ⁻¹' Ui l ∩ ((F.map (hkj l)) ⁻¹' Vj l)ᶜ) := by
              dsimp [E_k]
              rw [preimage_iUnion]
              apply iUnion_congr
              intro l
              rw [preimage_inter, preimage_compl]
      _ = ⋃ l, U l ∩ (V l)ᶜ := by
            apply iUnion_congr
            intro l
            exact hpreterm l
      _ = E := hEeq.symm

  have hpull {i k : J} (a : k ⟶ i) {S : Set (F.obj i)}
      {T : Set ((limit F : TopCat.{max v u}) : Type (max v u))}
      (hST : (limit.π F i) ⁻¹' S = T) :
      (limit.π F k) ⁻¹' ((F.map a) ⁻¹' S) = T := by
    ext x
    have hcoord : (limit.π F i) x = (F.map a) ((limit.π F k) x) := by
      rw [← ConcreteCategory.comp_apply, limit.w F a]
    change (F.map a) ((limit.π F k) x) ∈ S ↔ x ∈ T
    rw [← hcoord]
    change x ∈ (limit.π F i) ⁻¹' S ↔ x ∈ T
    rw [hST]

  have hcommon (i j : J) :
      ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j), True := by
    let s : Finset J := {i, j}
    obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists s
    have hi : i ∈ s := by simp [s]
    have hj : j ∈ s := by simp [s]
    exact ⟨k, (hk hi).some, (hk hj).some, trivial⟩

  have hclopen_props {i : J} {Q : Set (F.obj i)}
      (hQopen : IsOpen Q) (hQcompact : IsCompact Q) :
      IsOpen[constructibleTopology (F.obj i)] Q ∧
        IsClosed[constructibleTopology (F.obj i)] Q := by
    exact isConstructible_isOpen_isClosed_constructibleTopology
      (hQcompact.isConstructible hQopen)

  have hdesc_clopen (hEopen : IsOpen E) (hEclosed : IsClosed E) :
      ∃ (i : J) (E_i : Set (F.obj i)),
        IsOpen E_i ∧ IsClosed E_i ∧ IsCompact E_i ∧
          (limit.π F i) ⁻¹' E_i = E := by
    obtain ⟨i, A, hAopen, hAcompact, hAEq⟩ := hdesc_open hEopen hE
    obtain ⟨j, Q, hQopen, hQcompact, hQEq⟩ :=
      hdesc_open hEclosed.isOpen_compl hE.compl
    obtain ⟨k, a, b, -⟩ := hcommon i j
    let A₀ : Set (F.obj k) := (F.map a) ⁻¹' A
    let Q₀ : Set (F.obj k) := (F.map b) ⁻¹' Q
    have hA₀open : IsOpen A₀ := by
      exact hAopen.preimage (F.map a).hom.2
    have hA₀compact : IsCompact A₀ := by
      exact (hF.2 k i a).isCompact_preimage_of_isOpen hAopen hAcompact
    have hQ₀open : IsOpen Q₀ := by
      exact hQopen.preimage (F.map b).hom.2
    have hQ₀compact : IsCompact Q₀ := by
      exact (hF.2 k j b).isCompact_preimage_of_isOpen hQopen hQcompact
    have hA₀Eq : (limit.π F k) ⁻¹' A₀ = E := by
      exact hpull a hAEq
    have hQ₀Eq : (limit.π F k) ⁻¹' Q₀ = Eᶜ := by
      exact hpull b hQEq
    have hA₀ct :
        IsOpen[constructibleTopology (F.obj k)] A₀ ∧
          IsClosed[constructibleTopology (F.obj k)] A₀ :=
      hclopen_props hA₀open hA₀compact
    have hQ₀ct :
        IsOpen[constructibleTopology (F.obj k)] Q₀ ∧
          IsClosed[constructibleTopology (F.obj k)] Q₀ :=
      hclopen_props hQ₀open hQ₀compact
    have hunivclosed :
        IsClosed[constructibleTopology (F.obj k)] (Set.univ : Set (F.obj k)) :=
      @isClosed_univ (F.obj k) (constructibleTopology (F.obj k))
    have hunionopen :
        IsOpen[constructibleTopology (F.obj k)] (A₀ ∪ Q₀) :=
      @IsOpen.union (F.obj k) A₀ Q₀ (constructibleTopology (F.obj k))
        hA₀ct.1 hQ₀ct.1
    have hcover_limit :
        (limit.π F k) ⁻¹' (Set.univ : Set (F.obj k)) ⊆
          (limit.π F k) ⁻¹' (A₀ ∪ Q₀) := by
      rw [preimage_univ, preimage_union, hA₀Eq, hQ₀Eq]
      intro x hx
      by_cases hxE : x ∈ E
      · exact Or.inl hxE
      · exact Or.inr hxE
    obtain ⟨l, c, hcover⟩ :=
      (inverseLimit_preimage_subset_iff F hF k
        (E := Set.univ) (G := A₀ ∪ Q₀) hunivclosed hunionopen).mp hcover_limit
    let A₁ : Set (F.obj l) := (F.map c) ⁻¹' A₀
    let Q₁ : Set (F.obj l) := (F.map c) ⁻¹' Q₀
    have hA₁open : IsOpen A₁ := by
      exact hA₀open.preimage (F.map c).hom.2
    have hA₁compact : IsCompact A₁ := by
      exact (hF.2 l k c).isCompact_preimage_of_isOpen hA₀open hA₀compact
    have hQ₁open : IsOpen Q₁ := by
      exact hQ₀open.preimage (F.map c).hom.2
    have hQ₁compact : IsCompact Q₁ := by
      exact (hF.2 l k c).isCompact_preimage_of_isOpen hQ₀open hQ₀compact
    have hA₁Eq : (limit.π F l) ⁻¹' A₁ = E := by
      exact hpull c hA₀Eq
    have hQ₁Eq : (limit.π F l) ⁻¹' Q₁ = Eᶜ := by
      exact hpull c hQ₀Eq
    have hA₁ct :
        IsOpen[constructibleTopology (F.obj l)] A₁ ∧
          IsClosed[constructibleTopology (F.obj l)] A₁ :=
      hclopen_props hA₁open hA₁compact
    have hQ₁ct :
        IsOpen[constructibleTopology (F.obj l)] Q₁ ∧
          IsClosed[constructibleTopology (F.obj l)] Q₁ :=
      hclopen_props hQ₁open hQ₁compact
    have hdisjoint_limit :
        (limit.π F l) ⁻¹' A₁ ⊆ (limit.π F l) ⁻¹' Q₁ᶜ := by
      rw [hA₁Eq, preimage_compl, hQ₁Eq]
      intro x hxE hxEc
      exact hxEc hxE
    obtain ⟨m, d, hdisjoint⟩ :=
      (inverseLimit_preimage_subset_iff F hF l
        (E := A₁) (G := Q₁ᶜ) hA₁ct.2 hQ₁ct.2.isOpen_compl).mp
        hdisjoint_limit
    let A₂ : Set (F.obj m) := (F.map d) ⁻¹' A₁
    let Q₂ : Set (F.obj m) := (F.map d) ⁻¹' Q₁
    have hA₂open : IsOpen A₂ := by
      exact hA₁open.preimage (F.map d).hom.2
    have hA₂compact : IsCompact A₂ := by
      exact (hF.2 m l d).isCompact_preimage_of_isOpen hA₁open hA₁compact
    have hQ₂open : IsOpen Q₂ := by
      exact hQ₁open.preimage (F.map d).hom.2
    have hQ₂compact : IsCompact Q₂ := by
      exact (hF.2 m l d).isCompact_preimage_of_isOpen hQ₁open hQ₁compact
    have hcover₂ : (Set.univ : Set (F.obj m)) ⊆ A₂ ∪ Q₂ := by
      intro x hx
      have hx' := hcover (show F.map d x ∈ (F.map c) ⁻¹' (Set.univ : Set (F.obj k)) by simp)
      change F.map d x ∈ (F.map c) ⁻¹' (A₀ ∪ Q₀) at hx'
      simpa [A₂, Q₂, A₁, Q₁, preimage_union] using hx'
    have hdisjoint₂ : A₂ ⊆ Q₂ᶜ := by
      simpa [A₂, Q₂, preimage_compl] using hdisjoint
    have hA₂Eq : A₂ = Q₂ᶜ := by
      ext x
      constructor
      · exact fun hx => hdisjoint₂ hx
      · intro hx
        change x ∉ Q₂ at hx
        have h := hcover₂ (Set.mem_univ x)
        rcases h with hA | hQ
        · exact hA
        · exact (hx hQ).elim
    have hA₂closed : IsClosed A₂ := by
      rw [hA₂Eq]
      exact hQ₂open.isClosed_compl
    have hA₂Eq_limit : (limit.π F m) ⁻¹' A₂ = E := by
      exact hpull d hA₁Eq
    exact ⟨m, A₂, hA₂open, hA₂closed, hA₂compact, hA₂Eq_limit⟩

  by_cases hEopen : IsOpen E
  · by_cases hEclosed : IsClosed E
    · obtain ⟨i, E_i, hE_i_open, hE_i_closed, hE_i_compact, hE_i_eq⟩ :=
        hdesc_clopen hEopen hEclosed
      exact ⟨i, E_i, hE_i_compact.isConstructible hE_i_open,
        ⟨⟨fun _ => hE_i_open, fun _ => hE_i_closed⟩, hE_i_eq⟩⟩
    · obtain ⟨i, E_i, hE_i_open, hE_i_compact, hE_i_eq⟩ :=
        hdesc_open hEopen hE
      exact ⟨i, E_i, hE_i_compact.isConstructible hE_i_open,
        ⟨⟨fun _ => hE_i_open, fun h => (hEclosed h).elim⟩, hE_i_eq⟩⟩
  · by_cases hEclosed : IsClosed E
    · obtain ⟨i, Q, hQopen, hQcompact, hQeq⟩ :=
        hdesc_open hEclosed.isOpen_compl hE.compl
      let E_i : Set (F.obj i) := Qᶜ
      have hE_i_closed : IsClosed E_i := by
        exact hQopen.isClosed_compl
      have hE_i_eq : (limit.π F i) ⁻¹' E_i = E := by
        dsimp [E_i]
        rw [hQeq, compl_compl]
      exact ⟨i, E_i, hQcompact.isConstructible hQopen |>.compl,
        ⟨⟨fun h => (hEopen h).elim, fun _ => hE_i_closed⟩, hE_i_eq⟩⟩
    · obtain ⟨i, E_i, hE_i_constructible, hE_i_eq⟩ := hdesc_generic
      exact ⟨i, E_i, hE_i_constructible,
        ⟨⟨fun h => (hEopen h).elim, fun h => (hEclosed h).elim⟩, hE_i_eq⟩⟩

end ConstructibleInclusions

section SpectralInverseLimits

variable {J : Type v} [SmallCategory J] [IsCofiltered J]

/-- A cofiltered inverse limit of spectral spaces along spectral maps is
spectral, and all its projections are spectral maps. -/
theorem spectralSpace_of_inverseLimit_spectralDiagram
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F) :
      SpectralSpace ((limit F : TopCat.{max v u}) : Type (max v u)) ∧
      ∀ i : J, IsSpectralMap (limit.π F i) := by
  classical
  let (j : J) : SpectralSpace (F.obj j) := hF.1 j
  have hpreimagecompact : ∀ (i : J) (U : Set (F.obj i)), IsOpen U → IsCompact U →
      IsCompact ((limit.π F i) ⁻¹' U) := by
    intro i U hUopen hUcompact
    let Z : ∀ j : J, Set (F.obj j) := fun j =>
      ⋂ f : (j ⟶ i), (F.map f) ⁻¹' U
    have hUclosed : IsClosed[constructibleTopology (F.obj i)] U :=
      (isConstructible_isOpen_isClosed_constructibleTopology
        (hUcompact.isConstructible hUopen)).2
    have hZclosed : ∀ j : J, IsClosed[constructibleTopology (F.obj j)] (Z j) := by
      intro j
      dsimp [Z]
      exact @isClosed_iInter (F.obj j) (j ⟶ i) (constructibleTopology (F.obj j)) _
        (fun f => by
        have hcont : @Continuous (F.obj j) (F.obj i)
            (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i))
            (F.map f) :=
          (isSpectralMap_iff_continuous_constructibleTopology
            (X := F.obj j) (Y := F.obj i) (f := F.map f)
            (hF.2 j i f).continuous).mp (hF.2 j i f)
        exact @IsClosed.preimage (F.obj j) (F.obj i)
          (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i))
          (F.map f) hcont U hUclosed)
    have hZmap : CompatibleSetFamily F Z := by
      intro j k g
      rintro x ⟨y, hy, rfl⟩
      dsimp [Z]
      have hy' : ∀ f : (j ⟶ i), F.map f y ∈ U := by
        intro f
        have hyf := mem_iInter.1 (show y ∈ ⋂ f : (j ⟶ i), (F.map f) ⁻¹' U from hy) f
        exact hyf
      refine mem_iInter.2 ?_
      intro f
      have hy'' := hy' (g ≫ f)
      change F.map (g ≫ f) y ∈ U at hy''
      rw [F.map_comp] at hy''
      exact hy''
    have hcompact : IsCompact (inverseLimitSet F Z) :=
      inverseLimitSet_isCompact_of_constructibleClosed F hF Z hZclosed hZmap
    have hEq : inverseLimitSet F Z = (limit.π F i) ⁻¹' U := by
      ext x
      constructor
      · intro hx
        change ∀ j, (limit.π F j) x ∈ Z j at hx
        have hxi := hx i
        have hxi' := mem_iInter.1
          (show (limit.π F i) x ∈ ⋂ f : (i ⟶ i), (F.map f) ⁻¹' U from hxi) (𝟙 i)
        simpa using hxi'
      · intro hx
        change (limit.π F i) x ∈ U at hx
        change ∀ j, (limit.π F j) x ∈ Z j
        intro j
        dsimp [Z]
        refine mem_iInter.2 ?_
        intro f
        have hfac := congrArg (fun q => q x) (limit.w F f)
        change F.map f ((limit.π F j) x) = (limit.π F i) x at hfac
        change F.map f ((limit.π F j) x) ∈ U
        rw [hfac]
        exact hx
    rw [hEq] at hcompact
    exact hcompact
  let ι := Σ j : J, {U : Set (F.obj j) // IsOpen U ∧ IsCompact U}
  let b : ι → Set ((limit F : TopCat.{max v u}) : Type (max v u)) := fun k =>
    (limit.π F k.1) ⁻¹' (k.2 : Set (F.obj k.1))
  have hb : IsTopologicalBasis (Set.range b) := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨⟨j, U⟩, rfl⟩
      exact U.property.1.preimage (limit.π F j).hom.2
    · intro x V hx hV
      obtain ⟨T, hT, hxT, hTV⟩ :=
        (Formalization.Books.Topology.Unit14.cofiltered_limit_open_preimage_basis F).isOpen_iff.mp
          hV x hx
      rcases hT with ⟨j, U, hUopen, rfl⟩
      obtain ⟨K, hK, hxK, hKU⟩ :=
        (PrespectralSpace.isTopologicalBasis (X := F.obj j)).exists_subset_of_mem_open
          hxT hUopen
      refine ⟨b ⟨j, ⟨K, hK.1, hK.2⟩⟩, ?_, ?_, ?_⟩
      · exact ⟨⟨j, ⟨K, hK.1, hK.2⟩⟩, rfl⟩
      · exact hxK
      · intro z hz
        change (limit.π F j) z ∈ K at hz
        apply hTV
        change (limit.π F j) z ∈ U
        exact hKU hz
  have hbcompact : ∀ k : ι, IsCompact (b k) := by
    rintro ⟨j, U⟩
    exact hpreimagecompact j U U.property.1 U.property.2
  have hintercompact : ∀ k l : ι, IsCompact (b k ∩ b l) := by
    intro k l
    obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists ({k.1, l.1} : Finset J)
    have hk : k.1 ∈ ({k.1, l.1} : Finset J) := by simp
    have hl : l.1 ∈ ({k.1, l.1} : Finset J) := by simp
    let f : m ⟶ k.1 := (hm hk).some
    let g : m ⟶ l.1 := (hm hl).some
    let C : Set (F.obj m) := (F.map f) ⁻¹' (k.2 : Set (F.obj k.1)) ∩
      (F.map g) ⁻¹' (l.2 : Set (F.obj l.1))
    have hCopen : IsOpen C := by
      exact k.2.property.1.preimage (F.map f).hom.2 |>.inter
        (l.2.property.1.preimage (F.map g).hom.2)
    have hCcompact : IsCompact C := by
      exact QuasiSeparatedSpace.inter_isCompact _ _
        (k.2.property.1.preimage (F.map f).hom.2)
        ((hF.2 m k.1 f).isCompact_preimage_of_isOpen
          k.2.property.1 k.2.property.2)
        (l.2.property.1.preimage (F.map g).hom.2)
        ((hF.2 m l.1 g).isCompact_preimage_of_isOpen
          l.2.property.1 l.2.property.2)
    have hcompact := hpreimagecompact m C hCopen hCcompact
    have hEq : b k ∩ b l = (limit.π F m) ⁻¹' C := by
      ext x
      constructor
      · rintro ⟨hxk, hxl⟩
        change F.map f ((limit.π F m) x) ∈ (k.2 : Set (F.obj k.1)) ∧
          F.map g ((limit.π F m) x) ∈ (l.2 : Set (F.obj l.1))
        constructor
        · have hfac := congrArg (fun q => q x) (limit.w F f)
          change F.map f ((limit.π F m) x) = (limit.π F k.1) x at hfac
          rw [hfac]
          exact hxk
        · have hfac := congrArg (fun q => q x) (limit.w F g)
          change F.map g ((limit.π F m) x) = (limit.π F l.1) x at hfac
          rw [hfac]
          exact hxl
      · intro hx
        change F.map f ((limit.π F m) x) ∈ (k.2 : Set (F.obj k.1)) ∧
          F.map g ((limit.π F m) x) ∈ (l.2 : Set (F.obj l.1)) at hx
        constructor
        · change (limit.π F k.1) x ∈ (k.2 : Set (F.obj k.1))
          have hfac := congrArg (fun q => q x) (limit.w F f)
          change F.map f ((limit.π F m) x) = (limit.π F k.1) x at hfac
          rw [← hfac]
          exact hx.1
        · change (limit.π F l.1) x ∈ (l.2 : Set (F.obj l.1))
          have hfac := congrArg (fun q => q x) (limit.w F g)
          change F.map g ((limit.π F m) x) = (limit.π F l.1) x at hfac
          rw [← hfac]
          exact hx.2
    rw [hEq]
    exact hcompact
  have hT0 : T0Space ((limit F : TopCat.{max v u}) : Type (max v u)) := by
    constructor
    intro x y hxy
    apply Concrete.limit_ext F
    intro i
    exact (hxy.map (limit.π F i).hom.2).eq
  have hPrespectral : PrespectralSpace
      ((limit F : TopCat.{max v u}) : Type (max v u)) :=
    PrespectralSpace.of_isTopologicalBasis' hb hbcompact
  have hQuasiSeparated : QuasiSeparatedSpace
      ((limit F : TopCat.{max v u}) : Type (max v u)) :=
    QuasiSeparatedSpace.of_isTopologicalBasis hb hintercompact
  have hQuasiSober : QuasiSober
      ((limit F : TopCat.{max v u}) : Type (max v u)) := by
    let hBasis : IsTopologicalBasis
        {U : Set ((limit F : TopCat.{max v u}) : Type (max v u)) |
          IsOpen U ∧ IsCompact U} :=
      @PrespectralSpace.isTopologicalBasis
        ((limit F : TopCat.{max v u}) : Type (max v u)) _ hPrespectral
    refine { sober := ?_ }
    intro Z hZ hZclosed
    let Zi : ∀ i : J, Set (F.obj i) := fun i =>
      closure ((limit.π F i) '' Z)
    have hZi : ∀ i : J, IsIrreducible (Zi i) := by
      intro i
      dsimp [Zi]
      exact (hZ.image (limit.π F i) (limit.π F i).hom.2.continuousOn).closure
    let ξ : ∀ i : J, F.obj i := fun i =>
      Classical.choose (QuasiSober.sober (hZi i) isClosed_closure)
    have hξ : ∀ i : J, IsGenericPoint (ξ i) (Zi i) := by
      intro i
      exact Classical.choose_spec (QuasiSober.sober (hZi i) isClosed_closure)
    have hcoord (j i : J) (f : j ⟶ i)
        (z : ((limit F : TopCat.{max v u}) : Type (max v u))) :
        F.map f ((limit.π F j) z) = (limit.π F i) z := by
      have hfac := congrArg (fun q => q z) (limit.w F f)
      change F.map f ((limit.π F j) z) = (limit.π F i) z at hfac
      exact hfac
    have himage (j i : J) (f : j ⟶ i) :
        (F.map f) '' ((limit.π F j) '' Z) = (limit.π F i) '' Z := by
      ext y
      constructor
      · rintro ⟨y', ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, (hcoord j i f z).symm⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(limit.π F j) z, ⟨z, hz, rfl⟩, hcoord j i f z⟩
    have hclosure (j i : J) (f : j ⟶ i) :
        closure ((F.map f) '' Zi j) = Zi i := by
      dsimp [Zi]
      rw [closure_image_closure (hF.2 j i f).continuous, himage j i f]
    have hξmap (j i : J) (f : j ⟶ i) : F.map f (ξ j) = ξ i := by
      have hgen := (hξ j).image (hF.2 j i f).continuous
      rw [hclosure j i f] at hgen
      exact ((hξ i).eq hgen).symm
    let cone : Cone F :=
      { pt := TopCat.of PUnit
        π :=
          { app := fun i => TopCat.ofHom
              { toFun := fun _ => ξ i
                continuous_toFun := continuous_const }
            naturality := by
              intro j i f
              apply TopCat.ext
              intro z
              change ξ i = F.map f (ξ j)
              exact (hξmap j i f).symm } }
    let x := (limit.isLimit F).lift cone PUnit.unit
    have hxZ : x ∈ Z := by
      by_contra hx
      have hxopen : x ∈ Zᶜ := by simpa only [mem_compl_iff] using hx
      obtain ⟨B, hB, hxB, hBZ⟩ :=
        hb.exists_subset_of_mem_open hxopen hZclosed.isOpen_compl
      rcases hB with ⟨⟨i, U⟩, rfl⟩
      change (limit.π F i) x ∈ (U : Set (F.obj i)) at hxB
      have hfac := congrArg (fun q => q PUnit.unit)
        ((limit.isLimit F).fac cone i)
      change (limit.π F i) x = ξ i at hfac
      have hξU : ξ i ∈ (U : Set (F.obj i)) := by
        rw [← hfac]
        exact hxB
      obtain ⟨y, hyZi, hyU⟩ :=
        (hξ i).mem_open_set_iff U.property.1 |>.mp hξU
      change y ∈ closure ((limit.π F i) '' Z) at hyZi
      obtain ⟨z, hzU, hzimage⟩ :=
        mem_closure_iff.mp hyZi (U : Set (F.obj i)) U.property.1 hyU
      rcases hzimage with ⟨z', hzZ, rfl⟩
      exact (hBZ hzU) hzZ
    refine ⟨x, ?_⟩
    apply Set.Subset.antisymm
    · exact closure_minimal (singleton_subset_iff.mpr hxZ) hZclosed
    · intro z hz
      apply hBasis.mem_closure_iff.mpr
      intro U hU hzU
      obtain ⟨B, hB, hzB, hBU⟩ := hb.exists_subset_of_mem_open hzU hU.1
      rcases hB with ⟨⟨i, V⟩, rfl⟩
      change (limit.π F i) z ∈ (V : Set (F.obj i)) at hzB
      have hξV : ξ i ∈ (V : Set (F.obj i)) := by
        apply (hξ i).mem_open_set_iff V.property.1 |>.mpr
        refine ⟨(limit.π F i) z, ?_, hzB⟩
        change (limit.π F i) z ∈ closure ((limit.π F i) '' Z)
        exact subset_closure ⟨z, hz, rfl⟩
      refine ⟨x, hBU ?_, by simp⟩
      change (limit.π F i) x ∈ (V : Set (F.obj i))
      have hfac := congrArg (fun q => q PUnit.unit)
        ((limit.isLimit F).fac cone i)
      change (limit.π F i) x = ξ i at hfac
      rw [hfac]
      exact hξV
  refine ⟨?_, ?_⟩
  · exact spectralSpace_iff_source_conditions.mpr
      ⟨hT0, inverseLimit_spectralDiagram_isCompact F hF, hQuasiSober,
        hQuasiSeparated, hPrespectral⟩
  · intro i
    refine ⟨(limit.π F i).hom.2, ?_⟩
    intro U hUopen hUcompact
    exact hpreimagecompact i U hUopen hUcompact

end SpectralInverseLimits

section DescendQuasiCompactOpens

variable {J : Type v} [SmallCategory J] [IsCofiltered J]

/-- A quasi-compact open of an inverse limit descends to a quasi-compact
open at one stage. -/
theorem inverseLimit_quasiCompactOpen_descends
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    {U : Set ((limit F : TopCat.{max v u}) : Type (max v u))}
    (hUopen : IsOpen U) (hUcompact : IsCompact U) :
    ∃ (i : J) (U_i : Set (F.obj i)),
      IsOpen U_i ∧ IsCompact U_i ∧ (limit.π F i) ⁻¹' U_i = U := by
  classical
  let (j : J) : SpectralSpace (F.obj j) := hF.1 j
  obtain ⟨j, V, hVopen, hUV⟩ :=
    Formalization.Books.Topology.Unit14.cofiltered_limit_quasiCompact_open_eq_preimage
      F hUopen hUcompact
  let B : Set (Set (F.obj j)) :=
    {W | IsOpen W ∧ IsCompact W ∧ W ⊆ V}
  let I₀ := {W : Set (F.obj j) // W ∈ B}
  let A : I₀ → Set ((limit F : TopCat.{max v u}) : Type (max v u)) := fun W =>
    (limit.π F j) ⁻¹' (W : Set (F.obj j))
  have hAopen : ∀ W, IsOpen (A W) := by
    intro W
    exact W.property.1.preimage (limit.π F j).hom.2
  have hcover : U ⊆ ⋃ W, A W := by
    intro x hx
    have hxV : (limit.π F j) x ∈ V := by
      simpa [hUV] using hx
    obtain ⟨W, hW, hxW, hWV⟩ :=
      (PrespectralSpace.isTopologicalBasis (X := F.obj j)).exists_subset_of_mem_open
        hxV hVopen
    exact mem_iUnion.2 ⟨⟨W, hW.1, hW.2, hWV⟩, hxW⟩
  obtain ⟨t, ht⟩ := hUcompact.elim_finite_subcover A hAopen hcover
  let Q : Set (F.obj j) := ⋃ W ∈ t, (W : Set (F.obj j))
  have hQopen : IsOpen Q := by
    dsimp [Q]
    exact isOpen_iUnion fun W => isOpen_iUnion fun _ => W.property.1
  have hQcompact : IsCompact Q := by
    dsimp [Q]
    exact t.isCompact_biUnion (fun W _ => W.property.2.1)
  have hQV : Q ⊆ V := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := mem_iUnion₂.1 hx
    exact W.property.2.2 hxW
  refine ⟨j, Q, hQopen, hQcompact, ?_⟩
  ext x
  constructor
  · intro hx
    rw [hUV]
    exact hQV (by simpa [Q] using hx)
  · intro hx
    have hx' := ht hx
    simpa [A, Q] using hx'

/-- An inclusion between quasi-compact opens at two stages descends to a
common stage. -/
theorem inverseLimit_quasiCompactOpen_subset_descends
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (i j : J) {U_i : Set (F.obj i)} {U_j : Set (F.obj j)}
    (hU_i_open : IsOpen U_i) (hU_i_compact : IsCompact U_i)
    (hU_j_open : IsOpen U_j) (hU_j_compact : IsCompact U_j)
    (hU : (limit.π F i) ⁻¹' U_i ⊆ (limit.π F j) ⁻¹' U_j) :
    ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j),
      (F.map a) ⁻¹' U_i ⊆ (F.map b) ⁻¹' U_j := by
  classical
  let (r : J) : SpectralSpace (F.obj r) := hF.1 r
  have hcommon (i j : J) :
      ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j), True := by
    let s : Finset J := {i, j}
    obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists s
    have hi : i ∈ s := by simp [s]
    have hj : j ∈ s := by simp [s]
    exact ⟨k, (hk hi).some, (hk hj).some, trivial⟩
  obtain ⟨k, a, b, -⟩ := hcommon i j
  let A : Set (F.obj k) := (F.map a) ⁻¹' U_i
  let B : Set (F.obj k) := (F.map b) ⁻¹' U_j
  have hAopen : IsOpen A := by
    exact hU_i_open.preimage (F.map a).hom.2
  have hAcompact : IsCompact A := by
    exact (hF.2 k i a).isCompact_preimage_of_isOpen hU_i_open hU_i_compact
  have hBopen : IsOpen B := by
    exact hU_j_open.preimage (F.map b).hom.2
  have hBcompact : IsCompact B := by
    exact (hF.2 k j b).isCompact_preimage_of_isOpen hU_j_open hU_j_compact
  have hAct : IsClosed[constructibleTopology (F.obj k)] A := by
    exact (isConstructible_isOpen_isClosed_constructibleTopology
      (hAcompact.isConstructible hAopen)).2
  have hBct : IsOpen[constructibleTopology (F.obj k)] B := by
    exact (isConstructible_isOpen_isClosed_constructibleTopology
      (hBcompact.isConstructible hBopen)).1
  have hlimit : (limit.π F k) ⁻¹' A ⊆ (limit.π F k) ⁻¹' B := by
    intro x hx
    have hxi : (limit.π F i) x ∈ U_i := by
      have hcoord : (limit.π F i) x = (F.map a) ((limit.π F k) x) := by
        rw [← ConcreteCategory.comp_apply, limit.w F a]
      rw [hcoord]
      exact hx
    have hxj := hU hxi
    have hcoord : (limit.π F j) x = (F.map b) ((limit.π F k) x) := by
      rw [← ConcreteCategory.comp_apply, limit.w F b]
    change (F.map b) ((limit.π F k) x) ∈ U_j
    rw [← hcoord]
    exact hxj
  obtain ⟨l, f, hsmall⟩ :=
    (inverseLimit_preimage_subset_iff F hF k (E := A) (G := B) hAct hBct).mp hlimit
  refine ⟨l, f ≫ a, f ≫ b, ?_⟩
  intro x hx
  change (F.map (f ≫ a)) x ∈ U_i at hx
  rw [F.map_comp] at hx
  change (F.map a) ((F.map f) x) ∈ U_i at hx
  have hx' : (F.map f) x ∈ A := by
    change (F.map a) ((F.map f) x) ∈ U_i
    exact hx
  have hy' := hsmall hx'
  change (F.map b) ((F.map f) x) ∈ U_j at hy'
  change (F.map (f ≫ b)) x ∈ U_j
  rw [F.map_comp]
  change (F.map b) ((F.map f) x) ∈ U_j
  exact hy'

/-- A finite union equality between quasi-compact opens at a stage descends
to an equality at a later stage. -/
theorem inverseLimit_quasiCompactOpen_union_descends
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (i : J) (n : ℕ) {U_i : Set (F.obj i)} (U_ι : Fin n → Set (F.obj i))
    (hU_i_open : IsOpen U_i) (hU_i_compact : IsCompact U_i)
    (hU_ι_open : ∀ l, IsOpen (U_ι l))
    (hU_ι_compact : ∀ l, IsCompact (U_ι l))
    (hU : (limit.π F i) ⁻¹' U_i = ⋃ l, (limit.π F i) ⁻¹' (U_ι l)) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' U_i = ⋃ l, (F.map a) ⁻¹' (U_ι l) := by
  classical
  let (r : J) : SpectralSpace (F.obj r) := hF.1 r
  let C : Set (F.obj i) := ⋃ l, U_ι l
  have hCopen : IsOpen C := by
    dsimp [C]
    exact isOpen_iUnion hU_ι_open
  have hCcompact : IsCompact C := by
    dsimp [C]
    exact isCompact_iUnion hU_ι_compact
  have hUiclosed : IsClosed[constructibleTopology (F.obj i)] U_i := by
    exact (isConstructible_isOpen_isClosed_constructibleTopology
      (hU_i_compact.isConstructible hU_i_open)).2
  have hCconstructible : IsConstructible C := by
    exact hCcompact.isConstructible hCopen
  have hCopen_ct : IsOpen[constructibleTopology (F.obj i)] C :=
    (isConstructible_isOpen_isClosed_constructibleTopology hCconstructible).1
  have hforward_limit :
      (limit.π F i) ⁻¹' U_i ⊆ (limit.π F i) ⁻¹' C := by
    rw [hU, preimage_iUnion]
  obtain ⟨j, f, hforward⟩ :=
    (inverseLimit_preimage_subset_iff F hF i (E := U_i) (G := C)
      hUiclosed hCopen_ct).mp hforward_limit
  let A : Set (F.obj j) := (F.map f) ⁻¹' U_i
  let D : Set (F.obj j) := (F.map f) ⁻¹' C
  have hAopen : IsOpen A := by
    exact hU_i_open.preimage (F.map f).hom.2
  have hAcompact : IsCompact A := by
    exact (hF.2 j i f).isCompact_preimage_of_isOpen hU_i_open hU_i_compact
  have hDopen : IsOpen D := by
    exact hCopen.preimage (F.map f).hom.2
  have hDcompact : IsCompact D := by
    exact (hF.2 j i f).isCompact_preimage_of_isOpen hCopen hCcompact
  have hDclosed : IsClosed[constructibleTopology (F.obj j)] D := by
    exact (isConstructible_isOpen_isClosed_constructibleTopology
      (hDcompact.isConstructible hDopen)).2
  have hAopen_ct : IsOpen[constructibleTopology (F.obj j)] A :=
    (isConstructible_isOpen_isClosed_constructibleTopology
      (hAcompact.isConstructible hAopen)).1
  have hAlimit : (limit.π F j) ⁻¹' A = (limit.π F i) ⁻¹' U_i := by
    ext x
    change (F.map f) ((limit.π F j) x) ∈ U_i ↔ (limit.π F i) x ∈ U_i
    have hcoord : (limit.π F i) x = (F.map f) ((limit.π F j) x) := by
      rw [← ConcreteCategory.comp_apply, limit.w F f]
    rw [← hcoord]
  have hDlimit : (limit.π F j) ⁻¹' D = (limit.π F i) ⁻¹' C := by
    ext x
    change (F.map f) ((limit.π F j) x) ∈ C ↔ (limit.π F i) x ∈ C
    have hcoord : (limit.π F i) x = (F.map f) ((limit.π F j) x) := by
      rw [← ConcreteCategory.comp_apply, limit.w F f]
    rw [← hcoord]
  have hreverse_limit : (limit.π F j) ⁻¹' D ⊆ (limit.π F j) ⁻¹' A := by
    rw [hDlimit, hAlimit, hU]
    dsimp [C]
    rw [preimage_iUnion]
  obtain ⟨k, g, hreverse⟩ :=
    (inverseLimit_preimage_subset_iff F hF j (E := D) (G := A)
      hDclosed hAopen_ct).mp hreverse_limit
  have hforward' : (F.map g) ⁻¹' A ⊆ (F.map g) ⁻¹' D := by
    intro x hx
    exact hforward hx
  have heq : (F.map g) ⁻¹' A = (F.map g) ⁻¹' D :=
    le_antisymm hforward' hreverse
  refine ⟨k, g ≫ f, ?_⟩
  have hcompU : (F.map (g ≫ f)) ⁻¹' U_i = (F.map g) ⁻¹' A := by
    ext x
    change (F.map (g ≫ f)) x ∈ U_i ↔ (F.map g) x ∈ A
    rw [F.map_comp]
    rfl
  have hcompC : (F.map g) ⁻¹' D =
      ⋃ l, (F.map (g ≫ f)) ⁻¹' (U_ι l) := by
    calc
      (F.map g) ⁻¹' D =
          ⋃ l, (F.map g) ⁻¹' ((F.map f) ⁻¹' (U_ι l)) := by
            dsimp [D, C]
            rw [preimage_iUnion]
            rw [preimage_iUnion]
      _ = ⋃ l, (F.map (g ≫ f)) ⁻¹' (U_ι l) := by
            apply iUnion_congr
            intro l
            ext x
            change (F.map g) x ∈ (F.map f) ⁻¹' (U_ι l) ↔
              (F.map (g ≫ f)) x ∈ U_ι l
            rw [F.map_comp]
            rfl
  rw [hcompU, heq, hcompC]

/-- The intersection analogue of `inverseLimit_quasiCompactOpen_union_descends`. -/
theorem inverseLimit_quasiCompactOpen_inter_descends
    (F : J ⥤ TopCat.{max v u}) (hF : IsSpectralDiagram F)
    (i : J) (n : ℕ) {U_i : Set (F.obj i)} (U_ι : Fin n → Set (F.obj i))
    (hU_i_open : IsOpen U_i) (hU_i_compact : IsCompact U_i)
    (hU_ι_open : ∀ l, IsOpen (U_ι l))
    (hU_ι_compact : ∀ l, IsCompact (U_ι l))
    (hU : (limit.π F i) ⁻¹' U_i = ⋂ l, (limit.π F i) ⁻¹' (U_ι l)) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' U_i = ⋂ l, (F.map a) ⁻¹' (U_ι l) := by
  classical
  let (r : J) : SpectralSpace (F.obj r) := hF.1 r
  let C : Set (F.obj i) := ⋂ l, U_ι l
  have hCopen : IsOpen C := by
    dsimp [C]
    exact isOpen_iInter_of_finite hU_ι_open
  have hCcompact : IsCompact C := by
    by_cases hn : n = 0
    · subst n
      simpa [C] using (isCompact_univ : IsCompact (Set.univ : Set (F.obj i)))
    · let S : Set (Set (F.obj i)) := Set.range U_ι
      have hSfinite : S.Finite := by
        exact Set.finite_range U_ι
      have hSne : S.Nonempty := by
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        exact ⟨U_ι ⟨0, hnpos⟩, ⟨⟨0, hnpos⟩, rfl⟩⟩
      have hSo : ∀ T ∈ S, IsOpen T ∨ IsClosed T := by
        intro T hT
        obtain ⟨l, rfl⟩ := hT
        exact Or.inl (hU_ι_open l)
      have hSc : ∀ T ∈ S, IsCompact T := by
        intro T hT
        obtain ⟨l, rfl⟩ := hT
        exact hU_ι_compact l
      simpa [C, S] using
        (QuasiSeparatedSpace.isCompact_sInter_of_nonempty hSfinite hSne hSo hSc)
  have hUiclosed : IsClosed[constructibleTopology (F.obj i)] U_i := by
    exact (isConstructible_isOpen_isClosed_constructibleTopology
      (hU_i_compact.isConstructible hU_i_open)).2
  have hCconstructible : IsConstructible C :=
    hCcompact.isConstructible hCopen
  have hCopen_ct : IsOpen[constructibleTopology (F.obj i)] C :=
    (isConstructible_isOpen_isClosed_constructibleTopology hCconstructible).1
  have hforward_limit :
      (limit.π F i) ⁻¹' U_i ⊆ (limit.π F i) ⁻¹' C := by
    rw [hU]
    dsimp [C]
    rw [preimage_iInter]
  obtain ⟨j, f, hforward⟩ :=
    (inverseLimit_preimage_subset_iff F hF i (E := U_i) (G := C)
      hUiclosed hCopen_ct).mp hforward_limit
  let A : Set (F.obj j) := (F.map f) ⁻¹' U_i
  let D : Set (F.obj j) := (F.map f) ⁻¹' C
  have hAopen : IsOpen A := by
    exact hU_i_open.preimage (F.map f).hom.2
  have hAcompact : IsCompact A := by
    exact (hF.2 j i f).isCompact_preimage_of_isOpen hU_i_open hU_i_compact
  have hDopen : IsOpen D := by
    exact hCopen.preimage (F.map f).hom.2
  have hDcompact : IsCompact D := by
    exact (hF.2 j i f).isCompact_preimage_of_isOpen hCopen hCcompact
  have hDclosed : IsClosed[constructibleTopology (F.obj j)] D := by
    exact (isConstructible_isOpen_isClosed_constructibleTopology
      (hDcompact.isConstructible hDopen)).2
  have hAopen_ct : IsOpen[constructibleTopology (F.obj j)] A :=
    (isConstructible_isOpen_isClosed_constructibleTopology
      (hAcompact.isConstructible hAopen)).1
  have hAlimit : (limit.π F j) ⁻¹' A = (limit.π F i) ⁻¹' U_i := by
    ext x
    change (F.map f) ((limit.π F j) x) ∈ U_i ↔ (limit.π F i) x ∈ U_i
    have hcoord : (limit.π F i) x = (F.map f) ((limit.π F j) x) := by
      rw [← ConcreteCategory.comp_apply, limit.w F f]
    rw [← hcoord]
  have hDlimit : (limit.π F j) ⁻¹' D = (limit.π F i) ⁻¹' C := by
    ext x
    change (F.map f) ((limit.π F j) x) ∈ C ↔ (limit.π F i) x ∈ C
    have hcoord : (limit.π F i) x = (F.map f) ((limit.π F j) x) := by
      rw [← ConcreteCategory.comp_apply, limit.w F f]
    rw [← hcoord]
  have hreverse_limit : (limit.π F j) ⁻¹' D ⊆ (limit.π F j) ⁻¹' A := by
    rw [hDlimit, hAlimit]
    dsimp [C]
    rw [preimage_iInter, ← hU]
  obtain ⟨k, g, hreverse⟩ :=
    (inverseLimit_preimage_subset_iff F hF j (E := D) (G := A)
      hDclosed hAopen_ct).mp hreverse_limit
  have hforward' : (F.map g) ⁻¹' A ⊆ (F.map g) ⁻¹' D := by
    intro x hx
    exact hforward hx
  have heq : (F.map g) ⁻¹' A = (F.map g) ⁻¹' D :=
    le_antisymm hforward' hreverse
  refine ⟨k, g ≫ f, ?_⟩
  have hcompU : (F.map (g ≫ f)) ⁻¹' U_i = (F.map g) ⁻¹' A := by
    ext x
    change (F.map (g ≫ f)) x ∈ U_i ↔ (F.map g) x ∈ A
    rw [F.map_comp]
    rfl
  have hcompC : (F.map g) ⁻¹' D =
      ⋂ l, (F.map (g ≫ f)) ⁻¹' (U_ι l) := by
    calc
      (F.map g) ⁻¹' D =
          ⋂ l, (F.map g) ⁻¹' ((F.map f) ⁻¹' (U_ι l)) := by
            dsimp [D, C]
            rw [preimage_iInter]
            rw [preimage_iInter]
      _ = ⋂ l, (F.map (g ≫ f)) ⁻¹' (U_ι l) := by
            apply iInter_congr
            intro l
            ext x
            change (F.map g) x ∈ (F.map f) ⁻¹' (U_ι l) ↔
              (F.map (g ≫ f)) x ∈ U_ι l
            rw [F.map_comp]
            rfl
  rw [hcompU, heq, hcompC]

end DescendQuasiCompactOpens

section GeneralizationStableIntersections

variable {X : Type u} [TopologicalSpace X]

/-- The set of points which specialize to a point of `E`. -/
def pointsSpecializingTo (E : Set X) : Set X :=
  {x | ∃ y ∈ E, x ⤳ y}

/-- A subset which is an intersection of constructible subsets. -/
def IsIntersectionOfConstructibleSets (W : Set X) : Prop :=
  ∃ S : Set (Set X), W = ⋂₀ S ∧ ∀ E ∈ S, IsConstructible E

/-- A subset which is an intersection of quasi-compact open subsets. -/
def IsIntersectionOfQuasiCompactOpens (W : Set X) : Prop :=
  ∃ S : Set (Set X), W = ⋂₀ S ∧ ∀ U ∈ S, IsOpen U ∧ IsCompact U

/-- A nonempty directed family of quasi-compact opens, ordered by refinement. -/
def IsDirectedFamilyOfQuasiCompactOpens (I : Set (Set X)) : Prop :=
  I.Nonempty ∧
    (∀ U ∈ I, IsOpen U ∧ IsCompact U) ∧
      ∀ U ∈ I, ∀ V ∈ I, ∃ W ∈ I, W ⊆ U ∩ V

/-- A subset represented by a nonempty directed intersection of quasi-compact
opens. -/
def IsDirectedIntersectionOfQuasiCompactOpens (W : Set X) : Prop :=
  ∃ I : Set (Set X), IsDirectedFamilyOfQuasiCompactOpens I ∧ W = ⋂₀ I

/-- The five equivalent descriptions of generalization-stable intersections
in a spectral space. -/
theorem isIntersectionOfConstructibleSets_iff_isCompact_iff_pointsSpecializingTo
    [SpectralSpace X] {W : Set X} :
    (IsIntersectionOfConstructibleSets W ∧ StableUnderGeneralization W ↔
        IsCompact W ∧ StableUnderGeneralization W) ∧
      (IsCompact W ∧ StableUnderGeneralization W ↔
        ∃ E : Set X, IsCompact E ∧ W = pointsSpecializingTo E) ∧
        ((∃ E : Set X, IsCompact E ∧ W = pointsSpecializingTo E) ↔
          IsIntersectionOfQuasiCompactOpens W) ∧
          (IsIntersectionOfQuasiCompactOpens W ↔
            IsDirectedIntersectionOfQuasiCompactOpens W) := by
  have hAtoB (hA : IsIntersectionOfConstructibleSets W) : IsCompact W := by
    rcases hA with ⟨S, hWS, hS⟩
    have hWclosed : IsClosed[constructibleTopology X] W := by
      rw [hWS]
      exact @isClosed_sInter X (constructibleTopology X) S (fun E hE =>
        (isConstructible_isOpen_isClosed_constructibleTopology (hS E hE)).2)
    have hWcompactCT : @IsCompact X (constructibleTopology X) W :=
      @IsClosed.isCompact X (constructibleTopology X) W
        (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := X)).2.2
        hWclosed
    apply isCompact_iff_finite_subcover.mpr
    intro ι U hUopen hWcover
    obtain ⟨s, hs⟩ :=
      (@isCompact_iff_finite_subcover X (constructibleTopology X) W).mp hWcompactCT U
        (fun i => isOpen_constructibleTopology_of_isOpen (hUopen i)) hWcover
    exact ⟨s, hs⟩
  have hpointsStable (E : Set X) :
      StableUnderGeneralization (pointsSpecializingTo E) := by
    intro x y hyx hx
    rcases hx with ⟨z, hz, hxz⟩
    exact ⟨z, hz, hyx.trans hxz⟩
  have hpointsCompact (E : Set X) (hEcompact : IsCompact E) :
      IsCompact (pointsSpecializingTo E) := by
    apply isCompact_iff_finite_subcover.mpr
    intro ι U hUopen hcover
    have hEcover : E ⊆ ⋃ i, U i := by
      intro x hx
      exact hcover ⟨x, hx, specializes_rfl⟩
    obtain ⟨s, hs⟩ := hEcompact.elim_finite_subcover U hUopen hEcover
    refine ⟨s, ?_⟩
    intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    rcases mem_iUnion₂.mp (hs hy) with ⟨i, hi, hyi⟩
    exact mem_iUnion₂.mpr ⟨i, hi, (hUopen i).stableUnderGeneralization hxy hyi⟩
  have hBC :
      (IsCompact W ∧ StableUnderGeneralization W ↔
        ∃ E : Set X, IsCompact E ∧ W = pointsSpecializingTo E) := by
    constructor
    · rintro ⟨hWcompact, hWstable⟩
      refine ⟨W, hWcompact, ?_⟩
      ext x
      constructor
      · intro hx
        exact ⟨x, hx, specializes_rfl⟩
      · rintro ⟨y, hy, hxy⟩
        exact hWstable hxy hy
    · rintro ⟨E, hEcompact, hWE⟩
      refine ⟨?_, ?_⟩
      · rw [hWE]
        exact hpointsCompact E hEcompact
      · rw [hWE]
        exact hpointsStable E
  have hCtoQ :
      (∃ E : Set X, IsCompact E ∧ W = pointsSpecializingTo E) →
        IsIntersectionOfQuasiCompactOpens W := by
    rintro ⟨E, hEcompact, hWE⟩
    have hWcompact : IsCompact W := by
      rw [hWE]
      exact hpointsCompact E hEcompact
    let I : Set (Set X) :=
      {U | IsOpen U ∧ IsCompact U ∧ W ⊆ U}
    have hWI : W = ⋂₀ I := by
      apply Set.Subset.antisymm
      · intro x hx
        exact Set.mem_sInter.2 (fun U hU => hU.2.2 hx)
      · intro x hx
        by_contra hxW
        have hdisjoint : W ⊆ (closure ({x} : Set X))ᶜ := by
          intro y hyW hycl
          have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hycl
          rw [hWE] at hyW
          rcases hyW with ⟨z, hz, hyz⟩
          apply hxW
          rw [hWE]
          exact ⟨z, hz, hxy.trans hyz⟩
        obtain ⟨U, hUcompact, hUopen, hWU, hUZ⟩ :=
          PrespectralSpace.exists_isCompact_and_isOpen_between hWcompact
            isClosed_closure.isOpen_compl hdisjoint
        have hUmem : U ∈ I := ⟨hUopen, hUcompact, hWU⟩
        have hxU := Set.mem_sInter.1 hx U hUmem
        exact (hUZ hxU) (subset_closure (by simp))
    refine ⟨I, hWI, ?_⟩
    intro U hU
    exact ⟨hU.1, hU.2.1⟩
  have hQtoD :
      IsIntersectionOfQuasiCompactOpens W →
        IsDirectedIntersectionOfQuasiCompactOpens W := by
    rintro ⟨S, hWS, hS⟩
    let I : Set (Set X) :=
      {U | IsOpen U ∧ IsCompact U ∧ W ⊆ U}
    have hI : IsDirectedFamilyOfQuasiCompactOpens I := by
      refine ⟨?_, ?_, ?_⟩
      · exact ⟨Set.univ, ⟨isOpen_univ, isCompact_univ, subset_univ _⟩⟩
      · intro U hU
        exact ⟨hU.1, hU.2.1⟩
      · intro U hU V hV
        refine ⟨U ∩ V, ?_, ?_⟩
        · exact ⟨hU.1.inter hV.1,
            QuasiSeparatedSpace.inter_isCompact _ _ hU.1 hU.2.1 hV.1 hV.2.1,
            fun x hx => ⟨hU.2.2 hx, hV.2.2 hx⟩⟩
        · exact subset_rfl
    have hWI : W = ⋂₀ I := by
      apply Set.Subset.antisymm
      · intro x hx
        exact Set.mem_sInter.2 (fun U hU => hU.2.2 hx)
      · intro x hx
        rw [hWS]
        exact Set.mem_sInter.2 (fun U hU =>
          Set.mem_sInter.1 hx U
            ⟨(hS U hU).1, (hS U hU).2, by
              rw [hWS]
              exact Set.sInter_subset_of_mem hU⟩)
    exact ⟨I, hI, hWI⟩
  have hDtoA :
      IsDirectedIntersectionOfQuasiCompactOpens W →
        IsIntersectionOfConstructibleSets W ∧ StableUnderGeneralization W := by
    rintro ⟨I, hI, hWI⟩
    refine ⟨⟨I, hWI, ?_⟩, ?_⟩
    · intro U hU
      exact (hI.2.1 U hU).2.isConstructible (hI.2.1 U hU).1
    · rw [hWI]
      exact stableUnderGeneralization_sInter I
        (fun U hU => (hI.2.1 U hU).1.stableUnderGeneralization)
  have hfirst :
      (IsIntersectionOfConstructibleSets W ∧ StableUnderGeneralization W ↔
        IsCompact W ∧ StableUnderGeneralization W) := by
    constructor
    · rintro ⟨hA, hstable⟩
      exact ⟨hAtoB hA, hstable⟩
    · intro hB
      exact hDtoA (hQtoD (hCtoQ (hBC.mp hB)))
  refine ⟨hfirst, hBC, ?_, ?_⟩
  · constructor
    · exact hCtoQ
    · intro hQ
      exact hBC.mp (hfirst.mp (hDtoA (hQtoD hQ)))
  · constructor
    · exact hQtoD
    · intro hD
      exact hCtoQ (hBC.mp (hfirst.mp (hDtoA hD)))

/-- A directed intersection of quasi-compact opens in a spectral space is
spectral for its induced topology. -/
theorem spectralSpace_of_isDirectedIntersectionOfQuasiCompactOpens
    [SpectralSpace X] {W : Set X}
    (hW : IsDirectedIntersectionOfQuasiCompactOpens W) :
    SpectralSpace W := by
  rcases hW with ⟨I, hI, hWI⟩
  subst W
  apply spectralSpace_subtype_of_constructible_closed
  exact @isClosed_sInter X (constructibleTopology X) I (fun U hU =>
    (isConstructible_isOpen_isClosed_constructibleTopology
      ((hI.2.1 U hU).2.isConstructible (hI.2.1 U hU).1)).2)

/-- The diagram of inclusions of a family of subsets ordered by inclusion. -/
def directedIntersectionDiagram (I : Set (Set X)) : I ⥤ TopCat.{u} where
  obj U := TopCat.of (U : Set X)
  map {U V} f :=
    TopCat.ofHom
      ⟨(fun x : (U : Set X) =>
          (⟨x.1, f.le x.2⟩ : (V : Set X))),
        continuous_subtype_val.subtype_mk (fun x => f.le x.2)⟩
  map_id U := by
    apply TopCat.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp := by
    intro U V W f g
    apply TopCat.ext
    intro x
    apply Subtype.ext
    rfl

/-- The limit of the inclusion diagram is the intersection, as a topological
space. -/
theorem isDirectedIntersectionOfQuasiCompactOpens_isLimit
    [SpectralSpace X] {W : Set X} {I : Set (Set X)}
    (hI : IsDirectedFamilyOfQuasiCompactOpens I) (hW : W = ⋂₀ I) :
    Nonempty
      (W ≃ₜ ((limit (directedIntersectionDiagram I) : TopCat.{u}) : Type u)) := by
  classical
  subst W
  let D := directedIntersectionDiagram I
  let U₀ : I := ⟨Classical.choose hI.1, Classical.choose_spec hI.1⟩
  have hU₀ : (U₀ : Set X) ∈ I := U₀.property
  have hcoord (x : ((limit D : TopCat.{u}) : Type u)) (U V : I) :
      ((limit.π D U) x).val = ((limit.π D V) x).val := by
    obtain ⟨T, hT, hTU⟩ := hI.2.2 U U.property V V.property
    let T' : I := ⟨T, hT⟩
    let a : T' ⟶ U :=
      CategoryTheory.homOfLE (show T' ≤ U from by
        intro z hz
        exact (hTU hz).1)
    let b : T' ⟶ V :=
      CategoryTheory.homOfLE (show T' ≤ V from by
        intro z hz
        exact (hTU hz).2)
    have ha := congrArg (fun q => q x) (limit.w D a)
    have hb := congrArg (fun q => q x) (limit.w D b)
    change (D.map a) ((limit.π D T') x) = (limit.π D U) x at ha
    change (D.map b) ((limit.π D T') x) = (limit.π D V) x at hb
    have ha' : ((limit.π D T') x).val = ((limit.π D U) x).val := by
      have ha'' := congrArg (fun z => z.val) ha
      change ((limit.π D T') x).val = ((limit.π D U) x).val at ha''
      exact ha''
    have hb' : ((limit.π D T') x).val = ((limit.π D V) x).val := by
      have hb'' := congrArg (fun z => z.val) hb
      change ((limit.π D T') x).val = ((limit.π D V) x).val at hb''
      exact hb''
    exact ha'.symm.trans hb'
  have hmem (x : ((limit D : TopCat.{u}) : Type u)) :
      ((limit.π D U₀) x).val ∈ ⋂₀ I := by
    refine Set.mem_sInter.2 ?_
    intro V hV
    let V' : I := ⟨V, hV⟩
    rw [hcoord x U₀ V']
    exact ((limit.π D V') x).property
  let C : Cone D :=
    { pt := TopCat.of (⋂₀ I : Set X)
      π :=
        { app := fun U => TopCat.ofHom
            { toFun := fun x =>
                ⟨x.1, Set.mem_sInter.1 x.property U U.property⟩
              continuous_toFun :=
                continuous_subtype_val.subtype_mk (fun x =>
                  Set.mem_sInter.1 x.property U U.property) }
          naturality := by
            intro U V f
            apply TopCat.ext
            intro x
            apply Subtype.ext
            rfl } }
  let f : TopCat.of (⋂₀ I : Set X) ⟶ limit D := (limit.isLimit D).lift C
  let g : limit D ⟶ TopCat.of (⋂₀ I : Set X) :=
    TopCat.ofHom
      { toFun := fun x => ⟨((limit.π D U₀) x).val, hmem x⟩
        continuous_toFun := by
          exact (continuous_subtype_val.comp (limit.π D U₀).hom.2).subtype_mk hmem }
  let e : (⋂₀ I : Set X) ≃ ((limit D : TopCat.{u}) : Type u) :=
    { toFun := f.hom
      invFun := g.hom
      left_inv := by
        intro x
        apply Subtype.ext
        change ((limit.π D U₀) (f.hom x)).val = x.val
        have hfac := congrArg (fun q => q x) ((limit.isLimit D).fac C U₀)
        change (limit.π D U₀) (f.hom x) = (C.π.app U₀) x at hfac
        have hfac' := congrArg (fun z => z.val) hfac
        change ((limit.π D U₀) (f.hom x)).val = ((C.π.app U₀) x).val at hfac'
        calc
          ((limit.π D U₀) (f.hom x)).val = ((C.π.app U₀) x).val := hfac'
          _ = x.val := by rfl
      right_inv := by
        intro x
        apply Concrete.limit_ext D
        intro U
        apply Subtype.ext
        change ((limit.π D U) (f.hom (g.hom x))).val = ((limit.π D U) x).val
        have hfac := congrArg (fun q => q (g.hom x)) ((limit.isLimit D).fac C U)
        change (limit.π D U) (f.hom (g.hom x)) = (C.π.app U) (g.hom x) at hfac
        have hfac' := congrArg (fun z => z.val) hfac
        change ((limit.π D U) (f.hom (g.hom x))).val =
          ((C.π.app U) (g.hom x)).val at hfac'
        rw [hfac']
        change ((limit.π D U₀) x).val = ((limit.π D U) x).val
        exact hcoord x U₀ U }
  exact ⟨Homeomorph.mk e f.hom.2 g.hom.2⟩

/-- An open neighbourhood of a directed intersection contains one member of
the directed family. -/
theorem exists_member_of_isDirectedFamilyOfQuasiCompactOpens_subset_of_open
    [SpectralSpace X] {W : Set X} {I : Set (Set X)}
    (hI : IsDirectedFamilyOfQuasiCompactOpens I) (hW : W = ⋂₀ I)
    {U : Set X} (hUopen : IsOpen U) (hWU : W ⊆ U) :
    ∃ V ∈ I, V ⊆ U := by
  classical
  let U₀ : I := ⟨Classical.choose hI.1, Classical.choose_spec hI.1⟩
  have hUopen' : IsOpen[constructibleTopology X] U :=
    isOpen_constructibleTopology_of_isOpen hUopen
  have hUclosed : IsClosed[constructibleTopology X] Uᶜ :=
    (@isClosed_compl_iff X (constructibleTopology X) U).2 hUopen'
  let hK : @CompactSpace X (constructibleTopology X) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := X)).2.2
  have hcompact : @IsCompact X (constructibleTopology X) Uᶜ :=
    @IsClosed.isCompact X (constructibleTopology X) Uᶜ hK hUclosed
  have hAclosed (V : I) : IsClosed[constructibleTopology X] ((V : Set X) \ U) := by
    have hVopen : IsOpen (V : Set X) := (hI.2.1 V V.property).1
    have hVcompact : IsCompact (V : Set X) := (hI.2.1 V V.property).2
    have hVclosed : IsClosed[constructibleTopology X] (V : Set X) :=
      (isConstructible_isOpen_isClosed_constructibleTopology
        (hVcompact.isConstructible hVopen)).2
    simpa [Set.sdiff_eq] using
      (@IsClosed.inter X (V : Set X) Uᶜ (constructibleTopology X) hVclosed hUclosed)
  by_contra hnot
  have hno (V : I) : ¬ (V : Set X) ⊆ U := by
    intro hVU
    apply hnot
    exact ⟨V, V.property, hVU⟩
  have hcommon : ∀ s : Finset I, ∃ V : I,
      ∀ T ∈ s, (V : Set X) ⊆ (T : Set X) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨U₀, ?_⟩
        intro T hT
        simp at hT
    | @insert T s hTs ih =>
        obtain ⟨V, hVs⟩ := ih
        obtain ⟨R, hR, hRT⟩ := hI.2.2 T T.property V V.property
        refine ⟨⟨R, hR⟩, ?_⟩
        intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · intro z hz
          exact (hRT hz).1
        · intro z hz
          exact (hVs Q hQ) ((hRT hz).2)
  have hfinite : ∀ s : Finset I,
      (Uᶜ ∩ ⋂ V ∈ s, ((V : Set X) \ U)).Nonempty := by
    intro s
    obtain ⟨V, hVs⟩ := hcommon s
    obtain ⟨x, hxV, hxU⟩ := Set.not_subset.mp (hno V)
    refine ⟨x, hxU, ?_⟩
    refine mem_iInter.2 (fun T => mem_iInter.2 (fun hT => ?_))
    exact ⟨hVs T hT hxV, hxU⟩
  obtain ⟨x, hxU, hxall⟩ :=
    @IsCompact.inter_iInter_nonempty X (constructibleTopology X) Uᶜ I hcompact
      (fun V : I => (V : Set X) \ U) hAclosed hfinite
  apply hxU
  have hxW : x ∈ W := by
    rw [hW]
    exact Set.mem_sInter.2 (fun V hV =>
      (mem_iInter.1 hxall ⟨V, hV⟩).1)
  exact hWU hxW

end GeneralizationStableIntersections

section DifferenceByConstructibleSets

variable {X : Type u} [TopologicalSpace X]

/-- The diagram of the differences `U \ E` for a family of subsets ordered by
inclusion. -/
def directedIntersectionDifferenceDiagram (I : Set (Set X)) (E : Set X) : I ⥤ TopCat.{u} where
  obj U := TopCat.of (Set.diff (U : Set X) E)
  map {U V} f :=
    TopCat.ofHom
      ⟨(fun x : (Set.diff (U : Set X) E) =>
          (⟨x.1, f.le x.2.1, x.2.2⟩ : (Set.diff (V : Set X) E))),
        continuous_subtype_val.subtype_mk (fun x => ⟨f.le x.2.1, x.2.2⟩)⟩
  map_id U := by
    apply TopCat.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp := by
    intro U V W f g
    apply TopCat.ext
    intro x
    apply Subtype.ext
    rfl

/-- Removing a constructible subset from the set of points specializing to
that subset leaves a spectral space. -/
theorem spectralSpace_pointsSpecializingTo_diff_constructible
    [SpectralSpace X] {E : Set X} (hE : IsConstructible E) :
    SpectralSpace (Set.diff (pointsSpecializingTo E) E) := by
  have hEclosed : IsClosed[constructibleTopology X] E :=
    (isConstructible_isOpen_isClosed_constructibleTopology hE).2
  have hEcompactCT : @IsCompact X (constructibleTopology X) E :=
    @IsClosed.isCompact X (constructibleTopology X) E
      (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := X)).2.2
      hEclosed
  have hEcompact : IsCompact E := by
    apply isCompact_iff_finite_subcover.mpr
    intro ι U hUopen hEcover
    obtain ⟨s, hs⟩ :=
      (@isCompact_iff_finite_subcover X (constructibleTopology X) E).mp hEcompactCT U
        (fun i => isOpen_constructibleTopology_of_isOpen (hUopen i)) hEcover
    exact ⟨s, hs⟩
  have hchar :=
    isIntersectionOfConstructibleSets_iff_isCompact_iff_pointsSpecializingTo
      (X := X) (W := pointsSpecializingTo E)
  have hQ : IsIntersectionOfQuasiCompactOpens (pointsSpecializingTo E) :=
    hchar.2.2.1.mp ⟨E, hEcompact, rfl⟩
  have hD : IsDirectedIntersectionOfQuasiCompactOpens (pointsSpecializingTo E) :=
    hchar.2.2.2.mp hQ
  rcases hD with ⟨I, hI, hWI⟩
  apply spectralSpace_subtype_of_constructible_closed
  rw [hWI]
  have hEopen : IsOpen[constructibleTopology X] E :=
    (isConstructible_isOpen_isClosed_constructibleTopology hE).1
  have hEcompclosed : IsClosed[constructibleTopology X] Eᶜ :=
    (@isClosed_compl_iff X (constructibleTopology X) E).mpr hEopen
  have hWclosed : IsClosed[constructibleTopology X] (⋂₀ I) :=
    @isClosed_sInter X (constructibleTopology X) I (fun U hU =>
      (isConstructible_isOpen_isClosed_constructibleTopology
        ((hI.2.1 U hU).2.isConstructible (hI.2.1 U hU).1)).2)
  have hinter : IsClosed[constructibleTopology X] ((⋂₀ I) ∩ Eᶜ) :=
    @IsClosed.inter X (⋂₀ I) Eᶜ (constructibleTopology X) hWclosed hEcompclosed
  have hdiff : (⋂₀ I).diff E = (⋂₀ I) ∩ Eᶜ := by
    ext x
    constructor
    · intro hx
      exact ⟨Set.mem_sInter.1 hx.1, hx.2⟩
    · rintro ⟨hxI, hxE⟩
      exact ⟨hxI, hxE⟩
  rw [hdiff]
  exact hinter

/-- The difference of the points specializing to a constructible subset
is the limit of the corresponding differences of a directed quasi-compact-open
presentation. -/
theorem pointsSpecializingTo_diff_constructible_isLimit
    [SpectralSpace X] {E : Set X} {I : Set (Set X)} (_hE : IsConstructible E)
    (hI : IsDirectedFamilyOfQuasiCompactOpens I)
    (hW : pointsSpecializingTo E = ⋂₀ I) :
    Nonempty
      ((Set.diff (pointsSpecializingTo E) E) ≃ₜ
        ((limit (directedIntersectionDifferenceDiagram I E) : TopCat.{u}) : Type u)) := by
  classical
  let D := directedIntersectionDifferenceDiagram I E
  let U₀ : I := ⟨Classical.choose hI.1, Classical.choose_spec hI.1⟩
  have hcoord (x : ((limit D : TopCat.{u}) : Type u)) (U V : I) :
      ((limit.π D U) x).val = ((limit.π D V) x).val := by
    obtain ⟨T, hT, hTU⟩ := hI.2.2 U U.property V V.property
    let T' : I := ⟨T, hT⟩
    let a : T' ⟶ U :=
      CategoryTheory.homOfLE (show T' ≤ U from by
        intro z hz
        exact (hTU hz).1)
    let b : T' ⟶ V :=
      CategoryTheory.homOfLE (show T' ≤ V from by
        intro z hz
        exact (hTU hz).2)
    have ha := congrArg (fun q => q x) (limit.w D a)
    have hb := congrArg (fun q => q x) (limit.w D b)
    change (D.map a) ((limit.π D T') x) = (limit.π D U) x at ha
    change (D.map b) ((limit.π D T') x) = (limit.π D V) x at hb
    have ha' : ((limit.π D T') x).val = ((limit.π D U) x).val := by
      have ha'' := congrArg (fun z => z.val) ha
      change ((limit.π D T') x).val = ((limit.π D U) x).val at ha''
      exact ha''
    have hb' : ((limit.π D T') x).val = ((limit.π D V) x).val := by
      have hb'' := congrArg (fun z => z.val) hb
      change ((limit.π D T') x).val = ((limit.π D V) x).val at hb''
      exact hb''
    exact ha'.symm.trans hb'
  have hmem (x : ((limit D : TopCat.{u}) : Type u)) :
      ((limit.π D U₀) x).val ∈ Set.diff (pointsSpecializingTo E) E := by
    refine ⟨?_, (limit.π D U₀ x).property.2⟩
    rw [hW]
    exact Set.mem_sInter.2 (fun V hV => by
      let V' : I := ⟨V, hV⟩
      rw [hcoord x U₀ V']
      exact (limit.π D V' x).property.1)
  have hA_U (x : Set.diff (pointsSpecializingTo E) E) (U : I) :
      x.val ∈ Set.diff (U : Set X) E := by
    refine ⟨?_, x.property.2⟩
    have hx : x.val ∈ pointsSpecializingTo E := x.property.1
    have hx' : x.val ∈ ⋂₀ I := hW ▸ hx
    exact Set.mem_sInter.1 hx' U U.property
  let C : Cone D :=
    { pt := TopCat.of (Set.diff (pointsSpecializingTo E) E)
      π :=
        { app := fun U => TopCat.ofHom
            { toFun := fun x => ⟨x.1, hA_U x U⟩
              continuous_toFun :=
                continuous_subtype_val.subtype_mk (fun x =>
                  ⟨(hA_U x U).1, (hA_U x U).2⟩) }
          naturality := by
            intro U V f
            apply TopCat.ext
            intro x
            apply Subtype.ext
            rfl } }
  let f : TopCat.of (Set.diff (pointsSpecializingTo E) E) ⟶ limit D :=
    (limit.isLimit D).lift C
  let g : limit D ⟶ TopCat.of (Set.diff (pointsSpecializingTo E) E) :=
    TopCat.ofHom
      { toFun := fun x => ⟨((limit.π D U₀) x).val, hmem x⟩
        continuous_toFun := by
          exact (continuous_subtype_val.comp (limit.π D U₀).hom.2).subtype_mk hmem }
  let e : (Set.diff (pointsSpecializingTo E) E) ≃
      ((limit D : TopCat.{u}) : Type u) :=
    { toFun := f.hom
      invFun := g.hom
      left_inv := by
        intro x
        apply Subtype.ext
        change ((limit.π D U₀) (f.hom x)).val = x.val
        have hfac := congrArg (fun q => q x) ((limit.isLimit D).fac C U₀)
        change (limit.π D U₀) (f.hom x) = (C.π.app U₀) x at hfac
        have hfac' := congrArg (fun z => z.val) hfac
        change ((limit.π D U₀) (f.hom x)).val = ((C.π.app U₀) x).val at hfac'
        calc
          ((limit.π D U₀) (f.hom x)).val = ((C.π.app U₀) x).val := hfac'
          _ = x.val := by rfl
      right_inv := by
        intro x
        apply Concrete.limit_ext D
        intro U
        apply Subtype.ext
        change ((limit.π D U) (f.hom (g.hom x))).val = ((limit.π D U) x).val
        have hfac := congrArg (fun q => q (g.hom x)) ((limit.isLimit D).fac C U)
        change (limit.π D U) (f.hom (g.hom x)) = (C.π.app U) (g.hom x) at hfac
        have hfac' := congrArg (fun z => z.val) hfac
        change ((limit.π D U) (f.hom (g.hom x))).val =
          ((C.π.app U) (g.hom x)).val at hfac'
        rw [hfac']
        change ((limit.π D U₀) x).val = ((limit.π D U) x).val
        exact hcoord x U₀ U }
  exact ⟨Homeomorph.mk e f.hom.2 g.hom.2⟩

end DifferenceByConstructibleSets

end

end Formalization.Books.Topology.Unit24
