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

private theorem affine_site_intersection
    {X : Scheme.{u}} {U V W : Scheme.AffineZariskiSite X}
    (hVU : V ≤ U) (hWU : W ≤ U) :
    ∃ (T : Scheme.AffineZariskiSite X) (hTV : T ≤ V) (hTW : T ≤ W),
      T.toOpens = V.toOpens ⊓ W.toOpens := by
  rcases hVU with ⟨f, hf⟩
  rcases hWU with ⟨g, hg⟩
  have hVU' : V ≤ U := ⟨f, hf⟩
  have hWU' : W ≤ U := ⟨g, hg⟩
  let T : Scheme.AffineZariskiSite X := U.basicOpen (f * g)
  have hTV : T ≤ V := by
    refine ⟨X.presheaf.map
      (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hVU')).op g, ?_⟩
    dsimp [T]
    change X.basicOpen (X.presheaf.map
      (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hVU')).op g) =
      X.basicOpen (f * g)
    rw [Scheme.basicOpen_res, Scheme.basicOpen_mul, hf, hg]
  have hTW : T ≤ W := by
    refine ⟨X.presheaf.map
      (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hWU')).op f, ?_⟩
    dsimp [T]
    change X.basicOpen (X.presheaf.map
      (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hWU')).op f) =
      X.basicOpen (f * g)
    rw [Scheme.basicOpen_res, Scheme.basicOpen_mul, hf, hg, inf_comm]
  refine ⟨T, hTV, hTW, ?_⟩
  change X.basicOpen (f * g) = V.toOpens ⊓ W.toOpens
  rw [Scheme.basicOpen_mul, hf, hg]

private theorem binary_standard_compatible_of_match
    {X : Scheme.{u}} {F : AffineOpenPresheaf X}
    {U V W T : Scheme.AffineZariskiSite X}
    (hVU : V ≤ U) (hWU : W ≤ U)
    (hTV : T ≤ V) (hTW : T ≤ W)
    (hT : T.toOpens = V.toOpens ⊓ W.toOpens)
    (s : (b : Bool) → F.obj (op (if b then V else W)))
    (hmatch : F.map (homOfLE hTV).op (s true) =
      F.map (homOfLE hTW).op (s false)) :
    Presieve.Arrows.Compatible F
      (fun b : Bool => match b with
        | false => homOfLE hWU
        | true => homOfLE hVU) s := by
  intro i j Z gi gj hcomm
  cases i <;> cases j
  · have hEq : gi = gj := Subsingleton.elim _ _
    rw [hEq]
  · have hZV : Z.toOpens ≤ V.toOpens :=
      Scheme.AffineZariskiSite.toOpens_mono gj.le
    have hZW : Z.toOpens ≤ W.toOpens :=
      Scheme.AffineZariskiSite.toOpens_mono gi.le
    have hZTopen : Z.toOpens ≤ T.toOpens := by
      rw [hT]
      exact le_inf hZV hZW
    rcases (gi ≫ homOfLE hWU).le with ⟨k, hk⟩
    have hTU : T ≤ U := hTW.trans hWU
    have hZT : Z ≤ T := by
      refine ⟨X.presheaf.map
        (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hTU)).op k, ?_⟩
      rw [Scheme.basicOpen_res, hk]
      exact inf_eq_right.mpr hZTopen
    have hfactorW : gi = homOfLE hZT ≫ homOfLE hTW := Subsingleton.elim _ _
    have hfactorV : gj = homOfLE hZT ≫ homOfLE hTV := Subsingleton.elim _ _
    rw [hfactorW, hfactorV]
    simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
      congrArg (fun z => F.map (homOfLE hZT).op z) hmatch.symm
  · have hZW : Z.toOpens ≤ W.toOpens :=
      Scheme.AffineZariskiSite.toOpens_mono gj.le
    have hZV : Z.toOpens ≤ V.toOpens :=
      Scheme.AffineZariskiSite.toOpens_mono gi.le
    have hZTopen : Z.toOpens ≤ T.toOpens := by
      rw [hT]
      exact le_inf hZV hZW
    rcases (gi ≫ homOfLE hVU).le with ⟨k, hk⟩
    have hTU : T ≤ U := hTV.trans hVU
    have hZT : Z ≤ T := by
      refine ⟨X.presheaf.map
        (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hTU)).op k, ?_⟩
      rw [Scheme.basicOpen_res, hk]
      exact inf_eq_right.mpr hZTopen
    have hfactorV : gi = homOfLE hZT ≫ homOfLE hTV := Subsingleton.elim _ _
    have hfactorW : gj = homOfLE hZT ≫ homOfLE hTW := Subsingleton.elim _ _
    rw [hfactorV, hfactorW]
    simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
      congrArg (fun z => F.map (homOfLE hZT).op z) hmatch
  · have hEq : gi = gj := Subsingleton.elim _ _
    rw [hEq]

private theorem hasBinaryStandardOpenGluing_isSheafFor
    {X : Scheme.{u}} {F : AffineOpenPresheaf X}
    (hF : HasBinaryStandardOpenGluing F)
    {U V W : Scheme.AffineZariskiSite X}
    (hVU : V ≤ U) (hWU : W ≤ U)
    (hcover : U.toOpens = V.toOpens ⊔ W.toOpens) :
    Presieve.IsSheafFor F
      (Presieve.ofArrows (fun b : Bool => if b then V else W)
        (fun b => match b with
          | false => homOfLE hWU
          | true => homOfLE hVU)) := by
  obtain ⟨T, hTV, hTW, hT, hinj, hglue⟩ := hF.2 U V W hVU hWU hcover
  rw [Presieve.isSheafFor_arrows_iff]
  intro s hs
  obtain ⟨sU, hsU_V, hsU_W⟩ := hglue (s true) (s false)
    |>.mp (hs true false T (homOfLE hTV) (homOfLE hTW) (Subsingleton.elim _ _))
  · refine ⟨sU, ?_, ?_⟩
    · intro b
      cases b
      · exact hsU_W
      · exact hsU_V
    · intro t ht
      apply hinj
      apply Prod.ext
      · simpa using (hsU_V.trans (ht true).symm).symm
      · simpa using (hsU_W.trans (ht false).symm).symm

private theorem binary_standard_gluing_of_isSheafFor
    {X : Scheme.{u}} {F : AffineOpenPresheaf X}
    {U V W : Scheme.AffineZariskiSite X}
    (hVU : V ≤ U) (hWU : W ≤ U)
    (hcover : U.toOpens = V.toOpens ⊔ W.toOpens)
    (hR : Presieve.IsSheafFor F
      (Presieve.ofArrows (fun b : Bool => if b then V else W)
        (fun b => match b with
          | false => homOfLE hWU
          | true => homOfLE hVU))) :
    ∃ (T : Scheme.AffineZariskiSite X) (hTV : T ≤ V) (hTW : T ≤ W),
      T.toOpens = V.toOpens ⊓ W.toOpens ∧
        Function.Injective (fun s : F.obj (op U) =>
          (F.map (homOfLE hVU).op s, F.map (homOfLE hWU).op s)) ∧
        ∀ (sV : F.obj (op V)) (sW : F.obj (op W)),
          (F.map (homOfLE hTV).op sV = F.map (homOfLE hTW).op sW ↔
            ∃ sU : F.obj (op U),
              F.map (homOfLE hVU).op sU = sV ∧
                F.map (homOfLE hWU).op sU = sW) := by
  obtain ⟨T, hTV, hTW, hT⟩ := affine_site_intersection hVU hWU
  refine ⟨T, hTV, hTW, hT, ?_, ?_⟩
  · intro s₁ s₂ h12
    let π : ∀ b : Bool, (if b then V else W) ⟶ U := fun b => match b with
      | false => homOfLE hWU
      | true => homOfLE hVU
    let x₁ := Presieve.Arrows.toCompatible (P := F) (π := π) s₁
    have hx₁ := (Presieve.isSheafFor_arrows_iff F π).mp hR x₁.1 x₁.2
    apply hx₁.unique
    · intro b
      rfl
    · intro b
      cases b
      · simpa [x₁, π] using (congrArg Prod.snd h12).symm
      · simpa [x₁, π] using (congrArg Prod.fst h12).symm
  · intro sV sW
    constructor
    · intro hmatch
      let π : ∀ b : Bool, (if b then V else W) ⟶ U := fun b => match b with
        | false => homOfLE hWU
        | true => homOfLE hVU
      let s : (b : Bool) → F.obj (op (if b then V else W)) := fun b => match b with
        | false => sW
        | true => sV
      have hs := binary_standard_compatible_of_match hVU hWU hTV hTW hT s hmatch
      obtain ⟨sU, hsU, _⟩ := (Presieve.isSheafFor_arrows_iff F π).mp hR s hs
      refine ⟨sU, ?_, ?_⟩
      · simpa [s] using hsU true
      · simpa [s] using hsU false
    · rintro ⟨sU, rfl, rfl⟩
      simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
        congrArg (fun z => F.map z.op sU)
          (Subsingleton.elim (homOfLE hTV ≫ homOfLE hVU)
            (homOfLE hTW ≫ homOfLE hWU))

private theorem affine_basicOpen_sum_le
    {X : Scheme.{u}} {U : X.Opens} (n : ℕ) (f : Fin n → Γ(X, U)) :
    X.basicOpen (∑ i, f i) ≤ ⨆ i, X.basicOpen (f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    refine (Scheme.basicOpen_add_le X (f 0) (∑ i : Fin n, f i.succ)).trans ?_
    refine sup_le (le_iSup (fun i : Fin (n + 1) => X.basicOpen (f i)) 0) ?_
    refine (ih (fun i : Fin n => f i.succ)).trans ?_
    exact iSup_le fun i : Fin n => le_iSup (fun j : Fin (n + 1) => X.basicOpen (f j)) i.succ

private theorem affine_binary_standard_split
    {X : Scheme.{u}} {U : Scheme.AffineZariskiSite X} {n : ℕ}
    (a : Fin (n + 1) → Γ(X, U.toOpens))
    (hcover : U.toOpens = ⨆ i, X.basicOpen (a i)) :
    ∃ c : Fin (n + 1) → Γ(X, U.toOpens),
      U.toOpens = X.basicOpen (a 0) ⊔
        X.basicOpen (∑ i : Fin n, c i.succ * a i.succ) := by
  have hspan : Ideal.span (Set.range a) = ⊤ := by
    apply (U.2.iSup_basicOpen_eq_self_iff (s := Set.range a)).mp
    simpa using hcover.symm
  have hmem : (1 : Γ(X, U.toOpens)) ∈ Ideal.span (Set.range a) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hmem
  refine ⟨c, ?_⟩
  let g : Γ(X, U.toOpens) := ∑ i : Fin n, c i.succ * a i.succ
  have hspan' : Ideal.span (Set.range (fun b : Bool => if b then a 0 else g)) = ⊤ := by
    apply (Ideal.span (Set.range (fun b : Bool => if b then a 0 else g))).eq_top_iff_one.mpr
    rw [Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun b : Bool => if b then c 0 else 1, ?_⟩
    simpa [g, Fin.sum_univ_succ] using hc
  have hle : X.basicOpen (a 0) ⊔ X.basicOpen g ≤ U.toOpens := by
    exact sup_le (Scheme.basicOpen_le X _) (Scheme.basicOpen_le X _)
  have hge : U.toOpens ≤ X.basicOpen (a 0) ⊔ X.basicOpen g := by
    have hb := (U.2.iSup_basicOpen_eq_self_iff
      (s := Set.range (fun b : Bool => if b then a 0 else g))).mpr hspan'
    have hb' : (⨆ f : Set.range (fun b : Bool => if b then a 0 else g),
        X.basicOpen (f : Γ(X, U.toOpens))) = U.toOpens := by
      simpa only [Scheme.AffineZariskiSite.toOpens] using hb
    refine hb'.ge.trans ?_
    refine iSup_le fun f => ?_
    rcases f.property with ⟨b, hb⟩
    rw [← hb]
    cases b <;> simp
  simpa [g] using (show U.toOpens = X.basicOpen (a 0) ⊔ X.basicOpen g from
    (le_antisymm hle hge).symm)

private theorem affine_single_standard_isSheafFor
    {X : Scheme.{u}} {F : AffineOpenPresheaf X}
    {U : Scheme.AffineZariskiSite X}
    (a : Fin 1 → Γ(X, U.toOpens))
    (hcover : U.toOpens = ⨆ i, X.basicOpen (a i)) :
    Presieve.IsSheafFor F
      (Presieve.ofArrows (fun i : Fin 1 => U.basicOpen (a i))
        (fun i => homOfLE (U.basicOpen_le (a i)))) := by
  let V : Scheme.AffineZariskiSite X := U.basicOpen (a 0)
  have hVU : V = U := by
    apply Scheme.AffineZariskiSite.toOpens_injective
    simpa [V] using hcover.symm
  have he : (eqToHom hVU : V ⟶ U) = homOfLE (U.basicOpen_le (a 0)) :=
    Subsingleton.elim _ _
  letI : IsIso (homOfLE (U.basicOpen_le (a 0))) := by
    rw [← he]
    infer_instance
  rw [Presieve.isSheafFor_arrows_iff]
  intro s hs
  refine ⟨F.map (inv (homOfLE (U.basicOpen_le (a 0)))).op (s 0), ?_, ?_⟩
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp
  · intro t ht
    have h0 := ht 0
    simpa using congrArg (fun z => F.map (inv (homOfLE (U.basicOpen_le (a 0)))).op z) h0

private theorem affine_empty_standard_isSheafFor
    {X : Scheme.{u}} {F : AffineOpenPresheaf X}
    (hB : HasBinaryStandardOpenGluing F)
    {U : Scheme.AffineZariskiSite X} (a : Fin 0 → Γ(X, U.toOpens))
    (hcover : U.toOpens = ⨆ i, X.basicOpen (a i)) :
    Presieve.IsSheafFor F
      (Presieve.ofArrows (fun i : Fin 0 => U.basicOpen (a i))
        (fun i => homOfLE (U.basicOpen_le (a i)))) := by
  have hU : U = affineEmpty X := by
    apply Scheme.AffineZariskiSite.toOpens_injective
    simpa [affineEmpty] using hcover
  subst U
  rw [Presieve.isSheafFor_arrows_iff]
  intro s hs
  letI : Subsingleton (F.obj (op (affineEmpty X))) := hB.1.2
  refine ⟨Classical.choice hB.1.1, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro t ht
    exact Subsingleton.elim _ _

private theorem affine_basicOpen_restricted_cover
    {X : Scheme.{u}} {U : Scheme.AffineZariskiSite X}
    (g : Γ(X, U.toOpens)) {ι : Type v}
    (a : ι → Γ(X, U.toOpens))
    (hcover : U.toOpens = ⨆ i, X.basicOpen (a i)) :
    (U.basicOpen g).toOpens =
      ⨆ i, X.basicOpen
        (X.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono
          (U.basicOpen_le g))).op (a i)) := by
  have hle : (U.basicOpen g).toOpens ≤ U.toOpens :=
    Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le g)
  calc
    (U.basicOpen g).toOpens = (U.basicOpen g).toOpens ⊓ U.toOpens :=
      (inf_eq_left.mpr hle).symm
    _ = (U.basicOpen g).toOpens ⊓ ⨆ i, X.basicOpen (a i) :=
      congrArg ((U.basicOpen g).toOpens ⊓ ·) hcover
    _ = ⨆ i, (U.basicOpen g).toOpens ⊓ X.basicOpen (a i) := by
      simpa [inf_comm] using (iSup_inf_eq (fun i => X.basicOpen (a i))
        (U.basicOpen g).toOpens)
    _ = ⨆ i, X.basicOpen
        (X.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono
          (U.basicOpen_le g))).op (a i)) := by
      apply iSup_congr
      intro i
      change X.basicOpen g ⊓ X.basicOpen (a i) = _
      rw [Scheme.basicOpen_res]
      rfl

private theorem affine_basicOpen_restricted_sum_cover
    {X : Scheme.{u}} {U : Scheme.AffineZariskiSite X} {n : ℕ}
    (c a : Fin n → Γ(X, U.toOpens)) :
    (U.basicOpen (∑ i, c i * a i)).toOpens =
      ⨆ i, X.basicOpen
        (X.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono
          (U.basicOpen_le (∑ i, c i * a i)))).op (a i)) := by
  have hle : X.basicOpen (∑ i, c i * a i) ≤ ⨆ i, X.basicOpen (a i) := by
    refine (affine_basicOpen_sum_le n (fun i => c i * a i)).trans ?_
    refine iSup_le fun i => le_iSup_of_le i ?_
    rw [Scheme.basicOpen_mul]
    exact inf_le_right
  calc
    (U.basicOpen (∑ i, c i * a i)).toOpens =
        (U.basicOpen (∑ i, c i * a i)).toOpens ⊓
          ⨆ i, X.basicOpen (a i) := by
      change X.basicOpen (∑ i, c i * a i) = _
      exact (inf_eq_left.mpr hle).symm
    _ = ⨆ i, (U.basicOpen (∑ i, c i * a i)).toOpens ⊓ X.basicOpen (a i) := by
      simpa [inf_comm] using (iSup_inf_eq (fun i => X.basicOpen (a i))
        (U.basicOpen (∑ i, c i * a i)).toOpens)
    _ = ⨆ i, X.basicOpen
        (X.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono
          (U.basicOpen_le (∑ i, c i * a i)))).op (a i)) := by
      apply iSup_congr
      intro i
      change X.basicOpen (∑ i, c i * a i) ⊓ X.basicOpen (a i) = _
      rw [Scheme.basicOpen_res]
      rfl

private theorem finite_affine_standard_isSheafFor
    {X : Scheme.{u}} {F : AffineOpenPresheaf X}
    (hB : HasBinaryStandardOpenGluing F) :
    ∀ n : ℕ, ∀ {U : Scheme.AffineZariskiSite X}
      (a : Fin n → Γ(X, U.toOpens)),
      U.toOpens = ⨆ i, X.basicOpen (a i) →
      Presieve.IsSheafFor F
        (Presieve.ofArrows (fun i : Fin n => U.basicOpen (a i))
          (fun i => homOfLE (U.basicOpen_le (a i)))) := by
  classical
  intro n
  induction n with
  | zero =>
      intro U a hcover
      exact affine_empty_standard_isSheafFor hB a hcover
  | succ n ih =>
      intro U a hcover
      cases n with
      | zero =>
          exact affine_single_standard_isSheafFor a hcover
      | succ n =>
          obtain ⟨c, hsplit⟩ := affine_binary_standard_split a hcover
          let g : Γ(X, U.toOpens) := ∑ i : Fin (n + 1), c i.succ * a i.succ
          let V : Scheme.AffineZariskiSite X := U.basicOpen (a 0)
          let W : Scheme.AffineZariskiSite X := U.basicOpen g
          have hVU : V ≤ U := U.basicOpen_le (a 0)
          have hWU : W ≤ U := U.basicOpen_le g
          have hcoverVW : U.toOpens = V.toOpens ⊔ W.toOpens := by
            simpa [V, W, g] using hsplit
          have hrestcover : W.toOpens = ⨆ i : Fin (n + 1),
              X.basicOpen
                (X.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hWU)).op
                  (a i.succ)) := by
            simpa [W, g] using
              (affine_basicOpen_restricted_sum_cover
                (U := U) (c := fun i : Fin (n + 1) => c i.succ)
                (a := fun i : Fin (n + 1) => a i.succ))
          let b : Fin (n + 1) → Γ(X, W.toOpens) := fun i =>
            X.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hWU)).op
              (a i.succ)
          have hrest := ih (U := W) b (by simpa [b] using hrestcover)
          rw [Presieve.isSheafFor_arrows_iff]
          intro s hs
          obtain ⟨T, hTV, hTW, hT, hinj, hglue⟩ :=
            hB.2 U V W hVU hWU hcoverVW
          have hWiAi (i : Fin (n + 1)) :
              W.basicOpen (b i) ≤ U.basicOpen (a i.succ) := by
            let q := X.presheaf.map
              (homOfLE (Scheme.AffineZariskiSite.toOpens_mono
                (U.basicOpen_le (a i.succ)))).op g
            refine ⟨q, ?_⟩
            change X.basicOpen q = X.basicOpen (b i)
            rw [Scheme.basicOpen_res, Scheme.basicOpen_res, inf_comm]
            change X.basicOpen g ⊓ X.basicOpen (a i.succ) =
              X.basicOpen g ⊓ X.basicOpen (a i.succ)
            rfl
          have hst : Presieve.Arrows.Compatible F
              (fun i : Fin (n + 1) => homOfLE (W.basicOpen_le (b i)))
              (fun i => F.map (homOfLE (hWiAi i)).op (s i.succ)) := by
            intro i j Z gi gj hcomm
            have hAiU : U.basicOpen (a i.succ) ≤ U := U.basicOpen_le _
            have hAjU : U.basicOpen (a j.succ) ≤ U := U.basicOpen_le _
            have hcomm' :
                (gi ≫ homOfLE (hWiAi i)) ≫ homOfLE hAiU =
                  (gj ≫ homOfLE (hWiAi j)) ≫ homOfLE hAjU := by
              apply Subsingleton.elim
            have hsij := hs i.succ j.succ Z
              (gi ≫ homOfLE (hWiAi i)) (gj ≫ homOfLE (hWiAi j)) hcomm'
            simpa only [← comp_apply, ← F.map_comp, ← op_comp] using hsij
          obtain ⟨sW, hsW, _⟩ :=
            (Presieve.isSheafFor_arrows_iff F _).mp hrest
              (fun i => F.map (homOfLE (hWiAi i)).op (s i.succ)) hst
          let k : Γ(X, W.toOpens) := Classical.choose hTW
          have hk : X.basicOpen k = T.toOpens := Classical.choose_spec hTW
          let d : Fin (n + 1) → Γ(X, T.toOpens) := fun i =>
            X.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hTW)).op (b i)
          have hTcover : T.toOpens = ⨆ i, X.basicOpen (d i) := by
            have hTc := affine_basicOpen_restricted_cover k b hrestcover
            calc
              T.toOpens = X.basicOpen k := hk.symm
              _ = ⨆ i, X.basicOpen
                  (X.presheaf.map (homOfLE
                    (Scheme.AffineZariskiSite.toOpens_mono
                      (W.basicOpen_le k))).op (b i)) := hTc
              _ = ⨆ i, X.basicOpen (d i) := by
                apply iSup_congr
                intro i
                change X.basicOpen
                    (X.presheaf.map (homOfLE
                      (Scheme.AffineZariskiSite.toOpens_mono
                        (W.basicOpen_le k))).op (b i)) =
                  X.basicOpen
                    (X.presheaf.map (homOfLE
                      (Scheme.AffineZariskiSite.toOpens_mono hTW)).op (b i))
                rw [Scheme.basicOpen_res]
                nth_rewrite 2 [Scheme.basicOpen_res]
                change (W.basicOpen k).toOpens ⊓ X.basicOpen (b i) =
                  T.toOpens ⊓ X.basicOpen (b i)
                change X.basicOpen k ⊓ X.basicOpen (b i) =
                  T.toOpens ⊓ X.basicOpen (b i)
                rw [hk]
          have hTiWi (i : Fin (n + 1)) :
              T.basicOpen (d i) ≤ W.basicOpen (b i) := by
            let r := X.presheaf.map
              (homOfLE (Scheme.AffineZariskiSite.toOpens_mono
                (W.basicOpen_le (b i)))).op k
            refine ⟨r, ?_⟩
            change X.basicOpen r = X.basicOpen (d i)
            rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
            change X.basicOpen (b i) ⊓ X.basicOpen k =
              T.toOpens ⊓ X.basicOpen (b i)
            rw [← hk, inf_comm]
          have hTsep := (ih (U := T) d hTcover).isSeparatedFor
          let qV := F.map (homOfLE hTV).op (s 0)
          let qW := F.map (homOfLE hTW).op sW
          have hmatch : qV = qW := by
            apply hTsep.ext
            intro Y f hf
            rcases hf with ⟨i⟩
            let hTi : T.basicOpen (d i) ≤ T := T.basicOpen_le (d i)
            have hcompat := hs 0 i.succ (T.basicOpen (d i))
              (homOfLE (hTi.trans hTV))
              (homOfLE ((hTiWi i).trans (hWiAi i))) (Subsingleton.elim _ _)
            have hleft : F.map (homOfLE hTi).op qV =
                F.map (homOfLE (hTi.trans hTV)).op (s 0) := by
              simpa only [qV, ← comp_apply, ← F.map_comp, ← op_comp] using
                congrArg (fun z => F.map z.op (s 0))
                  (Subsingleton.elim
                    (homOfLE hTi ≫ homOfLE hTV)
                    (homOfLE (hTi.trans hTV)))
            have hright : F.map (homOfLE hTi).op qW =
                F.map (homOfLE ((hTiWi i).trans (hWiAi i))).op (s i.succ) := by
              calc
                F.map (homOfLE hTi).op qW =
                    F.map (homOfLE (hTi.trans hTW)).op sW := by
                  simpa only [qW, ← comp_apply, ← F.map_comp, ← op_comp] using
                    congrArg (fun z => F.map z.op sW)
                      (Subsingleton.elim
                        (homOfLE hTi ≫ homOfLE hTW)
                        (homOfLE (hTi.trans hTW)))
                _ = F.map (homOfLE (hTiWi i)).op
                    (F.map (homOfLE (W.basicOpen_le (b i))).op sW) := by
                  simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
                    congrArg (fun z => F.map z.op sW)
                      (Subsingleton.elim
                        (homOfLE (hTi.trans hTW))
                        (homOfLE (hTiWi i) ≫ homOfLE (W.basicOpen_le (b i))))
                _ = F.map (homOfLE (hTiWi i)).op
                    (F.map (homOfLE (hWiAi i)).op (s i.succ)) := by
                  rw [hsW i]
                _ = F.map (homOfLE ((hTiWi i).trans (hWiAi i))).op (s i.succ) := by
                  simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
                    congrArg (fun z => F.map z.op (s i.succ))
                      (Subsingleton.elim
                        (homOfLE (hTiWi i) ≫ homOfLE (hWiAi i))
                        (homOfLE ((hTiWi i).trans (hWiAi i))))
            simpa only [hleft, hright] using hcompat
          obtain ⟨sU, hsU_V, hsU_W⟩ := (hglue (s 0) sW).mp (by
            simpa only [qV, qW] using hmatch)
          refine ⟨sU, ?_, ?_⟩
          · intro i
            refine Fin.cases hsU_V (fun j => ?_) i
            let Ai : Scheme.AffineZariskiSite X := U.basicOpen (a j.succ)
            let p := X.presheaf.map
              (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hVU)).op (a j.succ)
            let P : Scheme.AffineZariskiSite X := V.basicOpen p
            let Q : Scheme.AffineZariskiSite X := W.basicOpen (b j)
            have hVopen : V.toOpens = X.basicOpen (a 0) := by rfl
            have hAiopen : Ai.toOpens = X.basicOpen (a j.succ) := by rfl
            have hAiU : Ai ≤ U := U.basicOpen_le (a j.succ)
            have hPV : P ≤ V := V.basicOpen_le p
            have hQW : Q ≤ W := W.basicOpen_le (b j)
            have hPA : P ≤ Ai := by
              let q := X.presheaf.map
                (homOfLE (Scheme.AffineZariskiSite.toOpens_mono hAiU)).op (a 0)
              refine ⟨q, ?_⟩
              change X.basicOpen q = X.basicOpen p
              rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
              rw [hAiopen, hVopen, inf_comm]
            have hQA : Q ≤ Ai := hWiAi j
            have hPopen : P.toOpens = V.toOpens ⊓ Ai.toOpens := by
              change X.basicOpen p = _
              rw [Scheme.basicOpen_res]
              rw [hVopen, hAiopen]
            have hQopen : Q.toOpens = W.toOpens ⊓ Ai.toOpens := by
              change X.basicOpen (b j) = _
              rw [Scheme.basicOpen_res]
              rw [hAiopen]
            have hcoverAi : Ai.toOpens = P.toOpens ⊔ Q.toOpens := by
              calc
                Ai.toOpens = Ai.toOpens ⊓ U.toOpens := by
                  exact (inf_eq_left.mpr
                    (Scheme.AffineZariskiSite.toOpens_mono hAiU)).symm
                _ = Ai.toOpens ⊓ (V.toOpens ⊔ W.toOpens) :=
                  congrArg (Ai.toOpens ⊓ ·) hcoverVW
                _ = (Ai.toOpens ⊓ V.toOpens) ⊔
                    (Ai.toOpens ⊓ W.toOpens) := by
                  apply inf_sup_left
                _ = P.toOpens ⊔ Q.toOpens := by
                  rw [hPopen, hQopen]
                  simp [inf_comm]
            obtain ⟨R, hRP, hRQ, hRopen, hAi_inj, _⟩ :=
              hB.2 Ai P Q hPA hQA hcoverAi
            apply hAi_inj
            apply Prod.ext
            · have hPcompat := hs 0 j.succ P (homOfLE hPV) (homOfLE hPA)
                (Subsingleton.elim _ _)
              calc
                F.map (homOfLE hPA).op
                    (F.map (homOfLE hAiU).op sU) =
                    F.map (homOfLE (hPA.trans hAiU)).op sU := by
                  simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
                    congrArg (fun z => F.map z.op sU)
                      (Subsingleton.elim
                        (homOfLE hPA ≫ homOfLE hAiU)
                        (homOfLE (hPA.trans hAiU)))
                _ = F.map (homOfLE (hPV.trans hVU)).op sU := by
                  simpa using congrArg (fun z => F.map z.op sU)
                    (Subsingleton.elim
                      (homOfLE (hPA.trans hAiU))
                      (homOfLE (hPV.trans hVU)))
                _ = F.map (homOfLE hPV).op
                    (F.map (homOfLE hVU).op sU) := by
                  simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
                    congrArg (fun z => F.map z.op sU)
                      (Subsingleton.elim
                        (homOfLE (hPV.trans hVU))
                        (homOfLE hPV ≫ homOfLE hVU))
                _ = F.map (homOfLE hPV).op (s 0) := by rw [hsU_V]
                _ = F.map (homOfLE hPA).op (s j.succ) := hPcompat
            · calc
                F.map (homOfLE hQA).op
                    (F.map (homOfLE hAiU).op sU) =
                    F.map (homOfLE (hQA.trans hAiU)).op sU := by
                  simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
                    congrArg (fun z => F.map z.op sU)
                      (Subsingleton.elim
                        (homOfLE hQA ≫ homOfLE hAiU)
                        (homOfLE (hQA.trans hAiU)))
                _ = F.map (homOfLE (hQW.trans hWU)).op sU := by
                  simpa using congrArg (fun z => F.map z.op sU)
                    (Subsingleton.elim
                      (homOfLE (hQA.trans hAiU))
                      (homOfLE (hQW.trans hWU)))
                _ = F.map (homOfLE hQW).op
                    (F.map (homOfLE hWU).op sU) := by
                  simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
                    congrArg (fun z => F.map z.op sU)
                      (Subsingleton.elim
                        (homOfLE (hQW.trans hWU))
                        (homOfLE hQW ≫ homOfLE hWU))
                _ = F.map (homOfLE hQW).op sW := by rw [hsU_W]
                _ = F.map (homOfLE hQA).op (s j.succ) := by
                  simpa [Q, hQA] using hsW j
          · intro t ht
            have htW : F.map (homOfLE hWU).op t = sW := by
              refine hrest.isSeparatedFor.ext (fun Y f hf => ?_)
              let f0 := f
              rcases hf with ⟨j⟩
              have htj := ht j.succ
              calc
                F.map f0.op (F.map (homOfLE hWU).op t) =
                    F.map (homOfLE ((W.basicOpen_le (b j)).trans hWU)).op t := by
                  simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
                    congrArg (fun z => F.map z.op t)
                      (Subsingleton.elim
                        (f0 ≫ homOfLE hWU)
                        (homOfLE ((W.basicOpen_le (b j)).trans hWU)))
                _ = F.map (homOfLE ((hWiAi j).trans (U.basicOpen_le (a j.succ)))).op t := by
                  simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
                    congrArg (fun z => F.map z.op t)
                      (Subsingleton.elim
                        (f0 ≫ homOfLE hWU)
                        (homOfLE ((hWiAi j).trans (U.basicOpen_le (a j.succ)))))
                _ = F.map (homOfLE (hWiAi j)).op
                    (F.map (homOfLE (U.basicOpen_le (a j.succ))).op t) := by
                  simpa only [← comp_apply, ← F.map_comp, ← op_comp] using
                    congrArg (fun z => F.map z.op t)
                      (Subsingleton.elim
                        (homOfLE ((hWiAi j).trans (U.basicOpen_le (a j.succ))))
                        (homOfLE (hWiAi j) ≫
                          homOfLE (U.basicOpen_le (a j.succ))))
                _ = F.map (homOfLE (hWiAi j)).op (s j.succ) := by
                  rw [htj]
                _ = F.map f0.op sW := (hsW j).symm
            apply hinj
            apply Prod.ext
            · change F.map (homOfLE hVU).op t = F.map (homOfLE hVU).op sU
              rw [ht 0, hsU_V]
            · change F.map (homOfLE hWU).op t = F.map (homOfLE hWU).op sU
              rw [htW, hsU_W]

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
  · constructor
    · intro hF
      unfold IsAffineSiteSheaf at hF
      refine ⟨?_, ?_⟩
      · let R : Presieve (affineEmpty X) :=
          Presieve.ofArrows (fun _ : Empty => affineEmpty X) (fun i => i.elim)
        let S : Sieve (affineEmpty X) := Sieve.generate R
        have hmem : S ∈
            Scheme.AffineZariskiSite.grothendieckTopology X (affineEmpty X) := by
          apply (Scheme.AffineZariskiSite.mem_grothendieckTopology
            (X := X) (U := affineEmpty X) (S := S)).2
          intro x hx
          change x ∈ (⊥ : X.Opens) at hx
          exact False.elim (by simpa using hx)
        have hS := hF.isSheafFor (X := affineEmpty X) (S := S) hmem
        have hR : Presieve.IsSheafFor F R :=
          (Presieve.isSheafFor_iff_generate R).mpr hS
        have hR' := (Presieve.isSheafFor_arrows_iff F _).mp hR
        let x : (i : Empty) → F.obj (op (affineEmpty X)) := fun i => i.elim
        have hx : Presieve.Arrows.Compatible F (B := affineEmpty X)
            (fun i : Empty => (i.elim : affineEmpty X ⟶ affineEmpty X)) x := by
          intro i
          exact isEmptyElim i
        obtain ⟨s, _, _⟩ := hR' x hx
        refine ⟨⟨s⟩, ?_⟩
        refine ⟨?_⟩
        intro a b
        apply (hR' x hx).unique
        · intro i
          exact isEmptyElim i
        · intro i
          exact isEmptyElim i
      · intro U V W hVU hWU hcover
        let R : Presieve U :=
          Presieve.ofArrows (fun b : Bool => if b then V else W)
            (fun b => match b with
              | false => homOfLE hWU
              | true => homOfLE hVU)
        let S : Sieve U := Sieve.generate R
        have hmem : S ∈ Scheme.AffineZariskiSite.grothendieckTopology X U := by
          apply (Scheme.AffineZariskiSite.mem_grothendieckTopology
            (X := X) (U := U) (S := S)).2
          intro x hx
          rw [hcover] at hx
          rcases Opens.mem_sup.mp hx with hxV | hxW
          · refine ⟨V, homOfLE hVU, ?_, hxV⟩
            exact (Sieve.le_generate R) V (homOfLE hVU)
              (Presieve.ofArrows.mk true)
          · refine ⟨W, homOfLE hWU, ?_, hxW⟩
            exact (Sieve.le_generate R) W (homOfLE hWU)
              (Presieve.ofArrows.mk false)
        have hS := hF.isSheafFor (X := U) (S := S) hmem
        have hR : Presieve.IsSheafFor F R :=
          (Presieve.isSheafFor_iff_generate R).mpr hS
        exact binary_standard_gluing_of_isSheafFor hVU hWU hcover hR
    · intro hB
      unfold IsAffineSiteSheaf
      rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
      intro U S hS
      let A : Set Γ(X, U.toOpens) :=
        Scheme.AffineZariskiSite.sectionsOfPresieve S.arrows
      have hspan : Ideal.span A = ⊤ := by
        exact (Scheme.AffineZariskiSite.mem_grothendieckTopology_iff_sectionsOfPresieve).mp hS
      have hAcover : (⨆ f : A, X.basicOpen (f : Γ(X, U.toOpens))) = U.toOpens := by
        have h := (U.2.iSup_basicOpen_eq_self_iff (s := A)).mpr hspan
        simpa only [Scheme.AffineZariskiSite.toOpens] using h
      let cover : A → Set X := fun f => (X.basicOpen (f : Γ(X, U.toOpens)) : Set X)
      have hcover : (U.toOpens : Set X) ⊆ ⋃ f : A, cover f := by
        intro x hx
        have hx' : x ∈ (⨆ f : A, X.basicOpen (f : Γ(X, U.toOpens))) := by
          rw [hAcover]
          exact hx
        obtain ⟨f, hxf⟩ := Opens.mem_iSup.mp hx'
        exact Set.mem_iUnion.2 ⟨f, hxf⟩
      obtain ⟨t, ht⟩ := U.2.isCompact.elim_finite_subcover cover
        (fun f => (X.basicOpen (f : Γ(X, U.toOpens))).isOpen) hcover
      let e : Fin t.card ≃ t := t.equivFin.symm
      let r : Fin t.card → Γ(X, U.toOpens) := fun j => (e j).1.1
      have hrc : (⨆ j, X.basicOpen (r j)) = U.toOpens := by
        apply le_antisymm
        · refine iSup_le fun j => ?_
          exact Scheme.basicOpen_le X (r j)
        · intro x hx
          obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.mp (ht hx)
          let j : Fin t.card := e.symm ⟨f, hf⟩
          have hj : (e j).1 = f := by simp [j]
          apply Opens.mem_iSup.mpr
          refine ⟨j, ?_⟩
          change x ∈ X.basicOpen (e j).1.1
          rw [hj]
          exact hxf
      let R : Presieve U :=
        Presieve.ofArrows (fun j : Fin t.card => U.basicOpen (r j))
          (fun j => homOfLE (U.basicOpen_le (r j)))
      have hR : Presieve.IsSheafFor F R :=
        finite_affine_standard_isSheafFor hB t.card r hrc.symm
      have hRle : R ≤ (S : Presieve U) := by
        intro Y f hf
        rcases hf with ⟨j⟩
        change S.arrows (homOfLE (U.basicOpen_le (r j)))
        exact (e j).1.2
      let S₀ : Sieve U := Sieve.generate R
      have hS₀le : S₀ ≤ S := by
        apply (Sieve.generate_le_iff R S).2
        exact hRle
      have hS₀ : Presieve.IsSheafFor F (S₀ : Presieve U) :=
        (Presieve.isSheafFor_iff_generate R).mp hR
      apply Presieve.isSheafFor_subsieve_aux F hS₀le hS₀
      intro V f hf
      let k : Γ(X, U.toOpens) := Classical.choose f.le
      have hk : X.basicOpen k = V.toOpens := Classical.choose_spec f.le
      let aV : Fin t.card → Γ(X, V.toOpens) := fun j =>
        X.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono f.le)).op (r j)
      have hVc : (⨆ j, X.basicOpen (aV j)) = V.toOpens := by
        simpa [aV, hk] using
          (affine_basicOpen_restricted_cover (U := U) k r hrc.symm).symm
      have hYsep :=
        (finite_affine_standard_isSheafFor hB t.card aV hVc.symm).isSeparatedFor
      intro x t₁ t₂ ht₁ ht₂
      refine hYsep.ext (fun Z g hg => ?_)
      let g₀ := g
      rcases hg with ⟨j⟩
      have hVjW : V.basicOpen (aV j) ≤ U.basicOpen (r j) := by
        let q := X.presheaf.map
          (homOfLE (Scheme.AffineZariskiSite.toOpens_mono
            (U.basicOpen_le (r j)))).op k
        refine ⟨q, ?_⟩
        change X.basicOpen q = X.basicOpen (aV j)
        rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
        change X.basicOpen (r j) ⊓ X.basicOpen k =
          V.toOpens ⊓ X.basicOpen (r j)
        rw [hk, inf_comm]
      have hbase : S₀.arrows (homOfLE (U.basicOpen_le (r j))) := by
        exact (Sieve.le_generate R) (U.basicOpen (r j))
          (homOfLE (U.basicOpen_le (r j))) (Presieve.ofArrows.mk j)
      have hmem : S₀.pullback f g₀ := by
        change S₀ (g₀ ≫ f)
        have hdown := S₀.downward_closed hbase (homOfLE hVjW)
        have hEq :
            homOfLE hVjW ≫ homOfLE (U.basicOpen_le (r j)) = g₀ ≫ f :=
          Subsingleton.elim _ _
        rw [← hEq]
        exact hdown
      exact (ht₁ _ hmem).trans (ht₂ _ hmem).symm

/-! ## Finite discrete schemes and closed points -/

/-- The underlying space is finite and discrete. -/
def IsFiniteDiscreteScheme (X : Scheme.{u}) : Prop :=
  Finite X ∧ DiscreteTopology X

/-- A scheme with finite discrete underlying space is affine. -/
theorem finite_discrete_scheme_is_affine
    (X : Scheme.{u}) (hX : IsFiniteDiscreteScheme X) : IsAffine X := by
  let _ : Finite X := hX.1
  let _ : DiscreteTopology X := hX.2
  infer_instance

/-- A scheme has a closed point when one of its points is a closed singleton. -/
def HasClosedPoint (X : Scheme.{u}) : Prop :=
  ∃ x : X, IsClosed ({x} : Set X)

/-- There exists a scheme without closed points. -/
theorem exists_scheme_without_closed_points :
    ∃ X : Scheme.{u}, ¬ HasClosedPoint X := by
  refine ⟨(∅ : Scheme), ?_⟩
  rintro ⟨x, _⟩
  exact isEmptyElim x

end

end Formalization.Books.Schemes.Unit11
