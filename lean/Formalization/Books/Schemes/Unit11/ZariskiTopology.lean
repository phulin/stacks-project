import Formalization.Books.Schemes.Unit09.Schemes
import Mathlib.Algebra.Field.ULift
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.Topology.Sober

/-!
# Schemes, Chapter 11: Zariski topology of schemes

This file records the topological statements in the chapter.  Scheme-specific affine opens,
basic opens, and the affine Zariski site are Mathlib's canonical constructions; the source-facing
interfaces below keep the chapter's statements available in its own namespace.
-/

namespace Formalization.Books.Schemes.Unit11

open CategoryTheory
open AlgebraicGeometry
open Opposite
open TopologicalSpace

universe u v

noncomputable section

/-! ## Generic points and affine-open topology -/

/-- Every irreducible closed subset of a scheme has a unique generic point. -/
theorem scheme_is_sober (X : Scheme.{u}) :
    ∀ {Z : Set X}, IsIrreducible Z → IsClosed Z →
      ∃! x : X, IsGenericPoint x Z := by
  intro Z hZ hZc
  obtain ⟨x, hx⟩ := QuasiSober.sober hZ hZc
  exact ⟨x, hx, fun y hy => (hx.eq hy).symm⟩

/-- The affine opens form the topological basis asserted in the chapter. -/
theorem affine_opens_form_basis (X : Scheme.{u}) :
    Opens.IsBasis X.affineOpens :=
  X.isBasis_affineOpens

private theorem no_three_distinct_bool
    (i j k : ULift.{u} Bool) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  cases i with
  | up i =>
    cases j with
    | up j =>
      cases k with
      | up k => cases i <;> cases j <;> cases k <;> simp_all

private def doubled_origin_glueData' : CategoryTheory.GlueData' (Scheme.{u}) := {
  J := ULift.{u} Bool
  U := fun _ => Formalization.Books.Schemes.Unit09.affinePlane (ULift.{u} ℚ)
  V := fun _ _ _ => Formalization.Books.Schemes.Unit09.puncturedAffinePlane (ULift.{u} ℚ)
  f := by
    intro _ _ _
    exact (Formalization.Books.Schemes.Unit09.affinePlanePuncturedOpen
      (ULift.{u} ℚ)).ι
  f_mono := by
    intro i j h
    infer_instance
  f_hasPullback := by
    intro i j k hij hik
    infer_instance
  t := by
    intro i j h
    exact 𝟙 _
  t' := by
    intro i j k hij hik hjk
    exact (no_three_distinct_bool i j k hij hik hjk).elim
  t_fac := by
    intro i j k hij hik hjk
    exact (no_three_distinct_bool i j k hij hik hjk).elim
  t_inv := by
    intro i j h
    simp
  cocycle := by
    intro i j k hij hik hjk
    exact (no_three_distinct_bool i j k hij hik hjk).elim }

private def doubled_origin_glueData : Scheme.GlueData.{u} := {
  toGlueData := CategoryTheory.GlueData.ofGlueData' doubled_origin_glueData'
  f_open := by
    intro i j
    dsimp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      doubled_origin_glueData']
    split_ifs <;> infer_instance }

/-- There are schemes with two affine opens whose intersection is not affine. -/
theorem exists_nonaffine_intersection_of_affine_opens :
    ∃ (X : Scheme.{u}) (U V : X.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ ¬ IsAffineOpen (U ⊓ V) := by
  let D := doubled_origin_glueData
  let X := D.glued
  let : IsOpenImmersion (D.ι (ULift.up false)) :=
    Scheme.GlueData.ι_isOpenImmersion D (ULift.up false)
  let : IsOpenImmersion (D.ι (ULift.up true)) :=
    Scheme.GlueData.ι_isOpenImmersion D (ULift.up true)
  let : IsAffine (D.U (ULift.up false)) := by
    change IsAffine (Formalization.Books.Schemes.Unit09.affinePlane (ULift.{u} ℚ))
    infer_instance
  let : IsAffine (D.U (ULift.up true)) := by
    change IsAffine (Formalization.Books.Schemes.Unit09.affinePlane (ULift.{u} ℚ))
    infer_instance
  let U : X.Opens := (D.ι (ULift.up false)).opensRange
  let V : X.Opens := (D.ι (ULift.up true)).opensRange
  refine ⟨X, U, V, ?_, ?_, ?_⟩
  · change IsAffineOpen (D.ι (ULift.up false)).opensRange
    exact isAffineOpen_opensRange _
  · change IsAffineOpen (D.ι (ULift.up true)).opensRange
    exact isAffineOpen_opensRange _
  · intro hInt
    have hpre : IsAffineOpen ((D.ι (ULift.up false)) ⁻¹ᵁ (U ⊓ V)) :=
      hInt.preimage_of_isOpenImmersion (D.ι (ULift.up false)) inf_le_left
    have hpreV : IsAffineOpen ((D.ι (ULift.up false)) ⁻¹ᵁ V) := by
      convert hpre using 1
      rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange]
      simp
    let : IsOpenImmersion
        (D.vPullbackCone (ULift.up false) (ULift.up true)).fst := by
      change IsOpenImmersion (D.f (ULift.up false) (ULift.up true))
      exact D.f_open _ _
    let : IsOpenImmersion (D.f (ULift.up false) (ULift.up true)) := D.f_open _ _
    let H := (IsPullback.of_isLimit (D.vPullbackConeIsLimit
      (ULift.up false) (ULift.up true))).flip
    have hleft : IsAffineOpen
        ((D.vPullbackCone (ULift.up false) (ULift.up true)).fst ''ᵁ
          ((D.vPullbackCone (ULift.up false) (ULift.up true)).snd ⁻¹ᵁ
            (⊤ : (D.U (ULift.up true)).Opens))) := by
      rw [IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H]
      simpa [V] using hpreV
    have hsourceRange : IsAffineOpen
        (D.vPullbackCone (ULift.up false) (ULift.up true)).fst.opensRange := by
      simpa using hleft
    have hsourceRange' : IsAffineOpen
        (D.f (ULift.up false) (ULift.up true)).opensRange := by
      change IsAffineOpen
        (D.vPullbackCone (ULift.up false) (ULift.up true)).fst.opensRange
      exact hsourceRange
    have hsourceTop : IsAffineOpen
        (⊤ : (D.V (ULift.up false, ULift.up true)).Opens) := by
      exact (AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion
        (D.f (ULift.up false) (ULift.up true))
        (U := (⊤ : (D.V (ULift.up false, ULift.up true)).Opens))).mp
        (by simpa using hsourceRange')
    have hsource : IsAffine (D.V (ULift.up false, ULift.up true)) := by
      exact (IsAffine.iff_of_isIso
        (Scheme.topIso _).hom).mp hsourceTop
    have hsource' : IsAffine (Formalization.Books.Schemes.Unit09.puncturedAffinePlane
        (ULift.{u} ℚ)) := by
      simpa [D, doubled_origin_glueData, CategoryTheory.GlueData.ofGlueData',
        doubled_origin_glueData'] using hsource
    exact Formalization.Books.Schemes.Unit09.puncturedAffinePlane_not_affine
      (ULift.{u} ℚ) hsource'

/-- The underlying space of a scheme is locally quasi-compact. -/
theorem scheme_is_locally_quasi_compact (X : Scheme.{u}) :
    LocallyCompactSpace X := by
  apply LocallyCompactSpace.of_hasBasis
    (ι := fun _ : X => X.affineOpens)
    (p := fun x W => x ∈ (W : Set X))
    (s := fun _ W => (W : Set X))
  · intro x
    refine ⟨fun t => ?_⟩
    constructor
    · intro ht
      obtain ⟨O, hOt, hO, hxO⟩ := mem_nhds_iff.mp ht
      obtain ⟨W, hW, hxW, hWO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxO hO
      rcases hW with ⟨W, hW, rfl⟩
      exact ⟨⟨W, hW⟩, hxW, hWO.trans hOt⟩
    · rintro ⟨W, hxW, hWt⟩
      exact Filter.mem_of_superset (IsOpen.mem_nhds W.1.isOpen hxW) hWt
  · intro x W hW
    exact W.property.isCompact

/-! ## Basic opens on overlapping affine charts -/

/-- A point in the intersection of two affine opens has an affine basic-open neighborhood which
is basic in both charts. -/
theorem exists_affine_basicOpen_neighborhood
    {X : Scheme.{u}} {U V : X.affineOpens} {x : X}
    (hx : x ∈ (U : X.Opens) ⊓ (V : X.Opens)) :
    ∃ (W : X.affineOpens)
      (f : Γ(X, (U : X.Opens))) (g : Γ(X, (V : X.Opens))),
      x ∈ (W : X.Opens) ∧
        (W : X.Opens) = X.basicOpen f ∧
        (W : X.Opens) = X.basicOpen g := by
  obtain ⟨f, g, hfg, hxfg⟩ :=
    exists_basicOpen_le_affine_inter U.property V.property x hx
  refine ⟨⟨X.basicOpen f, U.property.basicOpen f⟩, f, g, hxfg, rfl, hfg⟩

/-- A finite affine-basic-open refinement of an affine open inside an affine-open cover. -/
theorem exists_finite_affineBasicOpen_cover
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⨆ i, (U i : X.Opens)) = ⊤) (V : X.affineOpens) :
    ∃ n : ℕ, ∃ W : Fin n → X.affineOpens,
      (⨆ j, (W j : X.Opens)) = (V : X.Opens) ∧
        ∀ j, ∃ i : ι, ∃ f : Γ(X, (U i : X.Opens)),
          (W j : X.Opens) = X.basicOpen f := by
  let A := Σ i : ι, {f : Γ(X, (U i : X.Opens)) //
    X.basicOpen f ≤ (V : X.Opens)}
  let S : A → Set X := fun p => (X.basicOpen p.2.1 : Set X)
  have hcover : (V : Set X) ⊆ ⋃ p : A, S p := by
    intro x hx
    have hxTop : x ∈ (⨆ i, (U i : X.Opens)) := by
      rw [hU]
      exact Set.mem_univ x
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxTop
    obtain ⟨f, g, hfg, hxf⟩ :=
      exists_basicOpen_le_affine_inter (U i).property V.property x ⟨hxi, hx⟩
    have hle : X.basicOpen f ≤ (V : X.Opens) := by
      rw [hfg]
      exact Scheme.basicOpen_le X g
    refine Set.mem_iUnion.2 ⟨⟨i, f, hle⟩, ?_⟩
    exact hxf
  obtain ⟨t, ht⟩ :=
    V.property.isCompact.elim_finite_subcover S
      (fun p => (X.basicOpen p.2.1).isOpen) hcover
  let e : Fin t.card ≃ t := t.equivFin.symm
  let W : Fin t.card → X.affineOpens := fun j =>
    ⟨X.basicOpen (e j).1.2.1, (U (e j).1.1).property.basicOpen _⟩
  refine ⟨t.card, W, ?_, ?_⟩
  · apply le_antisymm
    · apply iSup_le
      intro j
      simpa [W] using (e j).1.2.2
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (ht hx)
      let j : Fin t.card := e.symm ⟨p, hp⟩
      have hj : (e j).1 = p := by
        simp [j]
      apply Opens.mem_iSup.mpr
      refine ⟨j, ?_⟩
      change x ∈ X.basicOpen (e j).1.2.1
      rw [hj]
      exact hxp
  · intro j
    exact ⟨(e j).1.1, (e j).1.2.1, rfl⟩

/-! ## Sheaves on the affine basis -/

/-- A presheaf on the small affine Zariski site of `X`. -/
abbrev AffineOpenPresheaf (X : Scheme.{u}) :=
  (Scheme.AffineZariskiSite X)ᵒᵖ ⥤ Type u

/-- The presheaf on affine opens obtained by restricting a sheaf on the underlying space. -/
noncomputable def affineOpenPresheafOfSchemeSheaf
    (X : Scheme.{u}) (F : TopCat.Sheaf (Type u) X) : AffineOpenPresheaf X :=
  ((Scheme.AffineZariskiSite.sheafEquiv (X := X) (A := Type u)).inverse.obj F).obj

/-- A presheaf on affine opens is the restriction of a sheaf on `X`. -/
def IsRestrictionOfSchemeSheaf
    {X : Scheme.{u}} (F : AffineOpenPresheaf X) : Prop :=
  ∃ G : TopCat.Sheaf (Type u) X,
    Nonempty (F ≅ affineOpenPresheafOfSchemeSheaf X G)

/-- The sheaf condition for a presheaf on the small affine Zariski site. -/
def IsAffineSiteSheaf {X : Scheme.{u}} (F : AffineOpenPresheaf X) : Prop :=
  CategoryTheory.Presheaf.IsSheaf
    (Scheme.AffineZariskiSite.grothendieckTopology X) F

/-- The affine-basis two-open gluing condition from the source.

The site order records precisely that an affine open is a basic open in a larger affine open.
The auxiliary object `T` is the affine basic-open representative of the intersection, so the
compatibility equation and the restriction maps are expressed using the canonical site arrows.
-/
noncomputable def affineEmpty (X : Scheme.{u}) : Scheme.AffineZariskiSite X :=
  ⟨⊥, isAffineOpen_bot X⟩

def HasBinaryStandardOpenGluing
    {X : Scheme.{u}} (F : AffineOpenPresheaf X) : Prop :=
  (Nonempty (F.obj (op (affineEmpty X))) ∧
      Subsingleton (F.obj (op (affineEmpty X)))) ∧
    ∀ (U V W : Scheme.AffineZariskiSite X)
      (hVU : V ≤ U) (hWU : W ≤ U)
      (_hcover : U.toOpens = V.toOpens ⊔ W.toOpens),
      ∃ (T : Scheme.AffineZariskiSite X) (hTV : T ≤ V) (hTW : T ≤ W),
        T.toOpens = V.toOpens ⊓ W.toOpens ∧
        Function.Injective (fun s : F.obj (op U) =>
          (F.map (homOfLE hVU).op s, F.map (homOfLE hWU).op s)) ∧
        ∀ (sV : F.obj (op V)) (sW : F.obj (op W)),
          (F.map (homOfLE hTV).op sV = F.map (homOfLE hTW).op sW ↔
            ∃ sU : F.obj (op U),
              F.map (homOfLE hVU).op sU = sV ∧
                F.map (homOfLE hWU).op sU = sW)

/-- A presheaf on affine opens extends to a sheaf exactly when it is a sheaf on that basis, and
exactly when the empty-open and binary standard-open gluing tests hold. -/
theorem affine_open_presheaf_sheaf_criterion
    {X : Scheme.{u}} (F : AffineOpenPresheaf X) :
    (IsRestrictionOfSchemeSheaf F ↔ IsAffineSiteSheaf F) ∧
      (IsAffineSiteSheaf F ↔ HasBinaryStandardOpenGluing F) := by
  constructor
  · constructor
    · rintro ⟨G, ⟨e⟩⟩
      change Presheaf.IsSheaf (Scheme.AffineZariskiSite.grothendieckTopology X) F
      exact (Presheaf.isSheaf_of_iso_iff e).mpr
        ((Scheme.AffineZariskiSite.sheafEquiv (X := X) (A := Type u)).inverse.obj G).property
    · intro hF
      let E := Scheme.AffineZariskiSite.sheafEquiv (X := X) (A := Type u)
      let G := E.functor.obj ⟨F, hF⟩
      refine ⟨G, ?_⟩
      change Nonempty (F ≅ (E.inverse.obj G).obj)
      let e := E.unitIso.app ⟨F, hF⟩
      exact ⟨Iso.mk e.hom.hom e.inv.hom
        (ObjectProperty.isoHom_inv_id_hom e) (ObjectProperty.isoInv_hom_id_hom e)⟩
  · sorry

/-! ## Finite discrete schemes and closed points -/

/-- The underlying space is finite and discrete. -/
def IsFiniteDiscreteScheme (X : Scheme.{u}) : Prop :=
  Finite X ∧ DiscreteTopology X

/-- A scheme with finite discrete underlying space is affine. -/
theorem finite_discrete_scheme_is_affine
    (X : Scheme.{u}) (hX : IsFiniteDiscreteScheme X) : IsAffine X := by
  sorry

/-- A scheme has a closed point when one of its points is a closed singleton. -/
def HasClosedPoint (X : Scheme.{u}) : Prop :=
  ∃ x : X, IsClosed ({x} : Set X)

/-- There exists a scheme without closed points. -/
theorem exists_scheme_without_closed_points :
    ∃ X : Scheme.{u}, ¬ HasClosedPoint X := by
  sorry

end

end Formalization.Books.Schemes.Unit11
