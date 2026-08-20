import Formalization.Books.Schemes.Unit06.AffineSchemes
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Schemes, Chapter 9: Schemes

This file records the definition of schemes, the affine-open basis, and the punctured affine
plane example.  The canonical scheme and open-subscheme constructions are Mathlib's `Scheme` and
`Scheme.Opens.toScheme`; the proposition proofs are deferred to the proof stage.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

namespace Formalization.Books.Schemes.Unit09

universe u

/-! ## The definition and local nature of schemes -/

/-- The source definition is Mathlib's `Scheme` structure and its `local_affine` field. -/
theorem scheme_local_affine (X : Scheme.{u}) :
    ∀ x : X,
      ∃ (U : OpenNhds x) (R : CommRingCat),
        Nonempty
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅
            Spec.toLocallyRingedSpace.obj (Opposite.op R)) :=
  X.local_affine

/-- A locally ringed space is a scheme up to isomorphism when it is the underlying space of a
scheme.  This is the source-facing proposition needed for the open-immersion lemma. -/
def IsSchemeLocallyRingedSpace (X : LocallyRingedSpace.{u}) : Prop :=
  ∃ Y : Scheme.{u}, Nonempty (X ≅ Y.toLocallyRingedSpace)

/-- An open immersion into a scheme has a source which is a scheme up to locally-ringed-space
isomorphism. -/
theorem openImmersion_source_is_scheme
    (U : LocallyRingedSpace.{u}) (X : Scheme.{u})
    (j : U ⟶ X.toLocallyRingedSpace)
    (hj : LocallyRingedSpace.IsOpenImmersion j) :
    IsSchemeLocallyRingedSpace U := by
  let _ := hj
  exact ⟨X.restrict hj.base_open,
    ⟨AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict j⟩⟩

/-- The scheme structure on an open subspace is the canonical restricted scheme. -/
abbrev openSubspaceScheme (X : Scheme.{u}) (U : X.Opens) : Scheme.{u} :=
  U.toScheme

theorem openSubspace_is_scheme
    (X : Scheme.{u}) (U : X.Opens) :
    IsSchemeLocallyRingedSpace
      (X.toLocallyRingedSpace.restrict U.isOpenEmbedding) := by
  exact ⟨U.toScheme, ⟨Iso.refl _⟩⟩

/-! ## Affine opens -/

/-- Mathlib's affine-open predicate is the chapter's notion of an affine open. -/
abbrev affineOpen (X : Scheme.{u}) := X.affineOpens

theorem affineOpen_is_open {X : Scheme.{u}} (U : X.affineOpens) :
    IsOpen (U.1 : Set X) :=
  U.1.2

/-- The affine opens form a basis for the topology of every scheme. -/
theorem affineOpen_is_basis (X : Scheme.{u}) :
    Opens.IsBasis X.affineOpens :=
  X.isBasis_affineOpens

/-! ## The punctured affine plane -/

/-- The polynomial ring in two variables over a field. -/
abbrev affinePlaneRing (k : Type u) [Field k] := MvPolynomial (Fin 2) k

/-- The affine plane `Spec(k[x, y])`. -/
abbrev affinePlane (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (affinePlaneRing k))

/-- The two coordinate functions. -/
def affinePlaneX (k : Type u) [Field k] : affinePlaneRing k :=
  MvPolynomial.X 0

def affinePlaneY (k : Type u) [Field k] : affinePlaneRing k :=
  MvPolynomial.X 1

/-- Evaluation at the origin. -/
def affinePlaneOriginEvaluation (k : Type u) [Field k] : affinePlaneRing k →+* k :=
  (MvPolynomial.aeval (R := k) (fun _ : Fin 2 => (0 : k))).toRingHom

/-- The origin of the affine plane. -/
def affinePlaneOrigin (k : Type u) [Field k] : affinePlane k :=
  ⟨RingHom.ker (affinePlaneOriginEvaluation k),
    RingHom.ker_isPrime (affinePlaneOriginEvaluation k)⟩

/-- The ideal `(x, y)` at the origin. -/
def affinePlaneOriginIdeal (k : Type u) [Field k] : Ideal (affinePlaneRing k) :=
  Ideal.span ({affinePlaneX k, affinePlaneY k} : Set (affinePlaneRing k))

theorem affinePlaneOriginIdeal_eq_kernel (k : Type u) [Field k] :
    affinePlaneOriginIdeal k = RingHom.ker (affinePlaneOriginEvaluation k) := by
  have hdecomp : ∀ p : affinePlaneRing k,
      p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ affinePlaneOriginIdeal k := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        simp
    | add p q hp hq =>
        simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          Ideal.add_mem _ hp hq
    | mul_X p i hp =>
        have hconst : MvPolynomial.constantCoeff (p * MvPolynomial.X i) = 0 := by
          simp
        rw [hconst, map_zero, sub_zero]
        have hi : MvPolynomial.X i ∈ affinePlaneOriginIdeal k := by
          unfold affinePlaneOriginIdeal
          fin_cases i <;> exact Ideal.subset_span (by simp [affinePlaneX, affinePlaneY])
        exact Ideal.mul_mem_left _ _ hi
  have hJ : affinePlaneOriginIdeal k ≤ RingHom.ker (affinePlaneOriginEvaluation k) := by
    refine Ideal.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simp [affinePlaneOriginEvaluation, affinePlaneX]
    · simp [affinePlaneOriginEvaluation, affinePlaneY]
  apply le_antisymm hJ
  intro p hp
  rw [RingHom.mem_ker] at hp
  have hconst : MvPolynomial.constantCoeff p = 0 := by
    simpa [affinePlaneOriginEvaluation] using hp
  have hd := hdecomp p
  simpa [hconst] using hd

/-- The standard opens `D(x)`, `D(y)`, and `D(xy)`. -/
abbrev affinePlaneDX (k : Type u) [Field k] : (affinePlane k).Opens :=
  PrimeSpectrum.basicOpen (affinePlaneX k)

abbrev affinePlaneDY (k : Type u) [Field k] : (affinePlane k).Opens :=
  PrimeSpectrum.basicOpen (affinePlaneY k)

abbrev affinePlaneDXY (k : Type u) [Field k] : (affinePlane k).Opens :=
  PrimeSpectrum.basicOpen (affinePlaneX k * affinePlaneY k)

theorem affinePlaneDXY_eq_inter (k : Type u) [Field k] :
    affinePlaneDXY k = affinePlaneDX k ⊓ affinePlaneDY k := by
  exact PrimeSpectrum.basicOpen_mul _ _

theorem affinePlaneDX_is_affine (k : Type u) [Field k] :
    IsAffine (affinePlaneDX k).toScheme := by
  change IsAffineOpen (affinePlaneDX k)
  exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (affinePlaneRing k)) (affinePlaneX k)

theorem affinePlaneDY_is_affine (k : Type u) [Field k] :
    IsAffine (affinePlaneDY k).toScheme := by
  change IsAffineOpen (affinePlaneDY k)
  exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (affinePlaneRing k)) (affinePlaneY k)

theorem affinePlaneDXY_is_affine (k : Type u) [Field k] :
    IsAffine (affinePlaneDXY k).toScheme := by
  change IsAffineOpen (affinePlaneDXY k)
  exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (affinePlaneRing k))
    (affinePlaneX k * affinePlaneY k)

/-- The localization descriptions of the two affine charts. -/
noncomputable def affinePlaneDX_iso (k : Type u) [Field k] :
    (affinePlaneDX k).toScheme ≅
      Spec (CommRingCat.of (Localization.Away (affinePlaneX k))) := by
  exact AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of (affinePlaneRing k))
    (affinePlaneX k)

noncomputable def affinePlaneDY_iso (k : Type u) [Field k] :
    (affinePlaneDY k).toScheme ≅
      Spec (CommRingCat.of (Localization.Away (affinePlaneY k))) := by
  exact AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of (affinePlaneRing k))
    (affinePlaneY k)

noncomputable def affinePlaneDXY_iso (k : Type u) [Field k] :
    (affinePlaneDXY k).toScheme ≅
      Spec (CommRingCat.of (Localization.Away (affinePlaneX k * affinePlaneY k))) := by
  exact AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of (affinePlaneRing k))
    (affinePlaneX k * affinePlaneY k)

/-! ## The punctured open and its Cech sequence -/

/-- The punctured plane, defined as the union `D(x) ∪ D(y)`. -/
abbrev affinePlanePuncturedOpen (k : Type u) [Field k] : (affinePlane k).Opens :=
  affinePlaneDX k ⊔ affinePlaneDY k

abbrev puncturedAffinePlane (k : Type u) [Field k] : Scheme.{u} :=
  (affinePlanePuncturedOpen k).toScheme

abbrev puncturedAffinePlaneInclusion (k : Type u) [Field k] :
    puncturedAffinePlane k ⟶ affinePlane k :=
  (affinePlanePuncturedOpen k).ι

/-- The two standard opens viewed as opens of the punctured plane. -/
abbrev puncturedAffinePlaneDX (k : Type u) [Field k] :
    (puncturedAffinePlane k).Opens :=
  puncturedAffinePlaneInclusion k ⁻¹ᵁ affinePlaneDX k

abbrev puncturedAffinePlaneDY (k : Type u) [Field k] :
    (puncturedAffinePlane k).Opens :=
  puncturedAffinePlaneInclusion k ⁻¹ᵁ affinePlaneDY k

abbrev puncturedAffinePlaneDXY (k : Type u) [Field k] :
    (puncturedAffinePlane k).Opens :=
  puncturedAffinePlaneInclusion k ⁻¹ᵁ affinePlaneDXY k

theorem puncturedAffinePlane_open_cover (k : Type u) [Field k] :
    puncturedAffinePlaneDX k ⊔ puncturedAffinePlaneDY k = ⊤ := by
  change (puncturedAffinePlaneInclusion k ⁻¹ᵁ affinePlaneDX k) ⊔
    (puncturedAffinePlaneInclusion k ⁻¹ᵁ affinePlaneDY k) = ⊤
  rw [← Scheme.Hom.preimage_sup]
  simp [affinePlanePuncturedOpen]

theorem puncturedAffinePlaneDX_is_affine (k : Type u) [Field k] :
    IsAffine (puncturedAffinePlaneDX k).toScheme := by
  let e := Scheme.Opens.isoOfLE (X := affinePlane k)
    (U := affinePlaneDX k) (V := affinePlanePuncturedOpen k) le_sup_left
  exact @AlgebraicGeometry.IsAffine.of_isIso _ _ e.hom (by infer_instance)
    (affinePlaneDX_is_affine k)

theorem puncturedAffinePlaneDY_is_affine (k : Type u) [Field k] :
    IsAffine (puncturedAffinePlaneDY k).toScheme := by
  let e := Scheme.Opens.isoOfLE (X := affinePlane k)
    (U := affinePlaneDY k) (V := affinePlanePuncturedOpen k) le_sup_right
  exact @AlgebraicGeometry.IsAffine.of_isIso _ _ e.hom (by infer_instance)
    (affinePlaneDY_is_affine k)

theorem puncturedAffinePlaneDXY_is_affine (k : Type u) [Field k] :
    IsAffine (puncturedAffinePlaneDXY k).toScheme := by
  have h : affinePlaneDXY k ≤ affinePlanePuncturedOpen k := by
    rw [affinePlaneDXY_eq_inter]
    exact le_trans inf_le_left le_sup_left
  let e := Scheme.Opens.isoOfLE (X := affinePlane k)
    (U := affinePlaneDXY k) (V := affinePlanePuncturedOpen k) h
  exact @AlgebraicGeometry.IsAffine.of_isIso _ _ e.hom (by infer_instance)
    (affinePlaneDXY_is_affine k)

theorem puncturedAffinePlaneDXY_eq_inter (k : Type u) [Field k] :
    puncturedAffinePlaneDXY k =
      puncturedAffinePlaneDX k ⊓ puncturedAffinePlaneDY k := by
  dsimp only [puncturedAffinePlaneDXY, puncturedAffinePlaneDX, puncturedAffinePlaneDY]
  rw [affinePlaneDXY_eq_inter, Scheme.Hom.preimage_inf]

theorem puncturedAffinePlaneDX_localization (k : Type u) [Field k] :
    Nonempty
      ((puncturedAffinePlaneDX k).toScheme ≅
        Spec (CommRingCat.of (Localization.Away (affinePlaneX k)))) := by
  let e := Scheme.Opens.isoOfLE (X := affinePlane k)
    (U := affinePlaneDX k) (V := affinePlanePuncturedOpen k) le_sup_left
  exact ⟨e ≪≫ affinePlaneDX_iso k⟩

theorem puncturedAffinePlaneDY_localization (k : Type u) [Field k] :
    Nonempty
      ((puncturedAffinePlaneDY k).toScheme ≅
        Spec (CommRingCat.of (Localization.Away (affinePlaneY k)))) := by
  let e := Scheme.Opens.isoOfLE (X := affinePlane k)
    (U := affinePlaneDY k) (V := affinePlanePuncturedOpen k) le_sup_right
  exact ⟨e ≪≫ affinePlaneDY_iso k⟩

theorem puncturedAffinePlaneDXY_localization (k : Type u) [Field k] :
    Nonempty
      ((puncturedAffinePlaneDXY k).toScheme ≅
        Spec (CommRingCat.of (Localization.Away
          (affinePlaneX k * affinePlaneY k)))) := by
  have h : affinePlaneDXY k ≤ affinePlanePuncturedOpen k := by
    rw [affinePlaneDXY_eq_inter]
    exact le_trans inf_le_left le_sup_left
  let e := Scheme.Opens.isoOfLE (X := affinePlane k)
    (U := affinePlaneDXY k) (V := affinePlanePuncturedOpen k) h
  exact ⟨e ≪≫ affinePlaneDXY_iso k⟩

theorem affinePlanePuncturedOpen_eq_union (k : Type u) [Field k] :
    affinePlanePuncturedOpen k = affinePlaneDX k ⊔ affinePlaneDY k :=
  rfl

theorem affinePlanePuncturedOpen_eq_complement_origin (k : Type u) [Field k] :
    (affinePlanePuncturedOpen k : Set (affinePlane k)) =
      ({affinePlaneOrigin k} : Set (affinePlane k))ᶜ := by
  ext x
  simp only [affinePlanePuncturedOpen, affinePlaneDX, affinePlaneDY,
    Set.mem_compl_iff, Set.mem_singleton_iff]
  change (affinePlaneX k ∉ x.asIdeal ∨ affinePlaneY k ∉ x.asIdeal) ↔
    x ≠ affinePlaneOrigin k
  have hsurj : Function.Surjective (affinePlaneOriginEvaluation k) := by
    intro a
    refine ⟨MvPolynomial.C a, ?_⟩
    simp [affinePlaneOriginEvaluation]
  have hmax : (affinePlaneOriginIdeal k).IsMaximal := by
    rw [affinePlaneOriginIdeal_eq_kernel]
    exact RingHom.ker_isMaximal_of_surjective _ hsurj
  constructor
  · rintro (hX | hY) hEq
    · subst hEq
      exact hX (by simp [affinePlaneOrigin, affinePlaneOriginEvaluation,
        affinePlaneX])
    · subst hEq
      exact hY (by simp [affinePlaneOrigin, affinePlaneOriginEvaluation,
        affinePlaneY])
  · intro hne
    by_contra h
    have hX : affinePlaneX k ∈ x.asIdeal := by
      by_contra hx
      exact h (Or.inl hx)
    have hY : affinePlaneY k ∈ x.asIdeal := by
      by_contra hy
      exact h (Or.inr hy)
    apply hne
    apply PrimeSpectrum.ext
    have hEqIdeal : affinePlaneOriginIdeal k = x.asIdeal := by
      apply hmax.eq_of_le x.2.ne_top
      unfold affinePlaneOriginIdeal
      exact Ideal.span_le.2 (by
        intro z hz
        rcases hz with rfl | rfl
        · exact hX
        · exact hY)
    simpa [affinePlaneOrigin, affinePlaneOriginIdeal_eq_kernel] using hEqIdeal.symm

noncomputable def affinePlaneSectionRestriction
    (k : Type u) [Field k] {V W : (affinePlane k).Opens} (h : V ≤ W) :
    Γ(affinePlane k, W) →+ Γ(affinePlane k, V) :=
  ((affinePlane k).presheaf.map (homOfLE h).op).hom.toAddMonoidHom

noncomputable def puncturedPlaneCechFirst (k : Type u) [Field k] :
    Γ(affinePlane k, affinePlanePuncturedOpen k) →+
      (Γ(affinePlane k, affinePlaneDX k) × Γ(affinePlane k, affinePlaneDY k)) :=
  AddMonoidHom.mk'
    (fun s =>
      (affinePlaneSectionRestriction k le_sup_left s,
        affinePlaneSectionRestriction k le_sup_right s))
    (by
      intro s t
      simp [affinePlaneSectionRestriction])

noncomputable def puncturedPlaneCechSecond (k : Type u) [Field k] :
    (Γ(affinePlane k, affinePlaneDX k) × Γ(affinePlane k, affinePlaneDY k)) →+
      Γ(affinePlane k, affinePlaneDXY k) :=
  AddMonoidHom.mk'
    (fun s =>
      affinePlaneSectionRestriction k
          (show affinePlaneDXY k ≤ affinePlaneDX k from by
            rw [affinePlaneDXY_eq_inter]
            exact inf_le_left) s.1 -
        affinePlaneSectionRestriction k
          (show affinePlaneDXY k ≤ affinePlaneDY k from by
            rw [affinePlaneDXY_eq_inter]
            exact inf_le_right) s.2)
    (by
      intro s t
      change
        affinePlaneSectionRestriction k _ (s.1 + t.1) -
            affinePlaneSectionRestriction k _ (s.2 + t.2) =
          (affinePlaneSectionRestriction k _ s.1 - affinePlaneSectionRestriction k _ s.2) +
            (affinePlaneSectionRestriction k _ t.1 - affinePlaneSectionRestriction k _ t.2)
      rw [map_add, map_add]
      abel)

/-- The displayed Cech sequence is exact (with injectivity at the left). -/
theorem puncturedPlaneCech_exact (k : Type u) [Field k] :
    Function.Injective (puncturedPlaneCechFirst k) ∧
      Function.Exact (puncturedPlaneCechFirst k) (puncturedPlaneCechSecond k) := by
  let hX : affinePlaneDXY k ≤ affinePlaneDX k := by
    rw [affinePlaneDXY_eq_inter]
    exact inf_le_left
  let hY : affinePlaneDXY k ≤ affinePlaneDY k := by
    rw [affinePlaneDXY_eq_inter]
    exact inf_le_right
  have hmap (U V : (affinePlane k).Opens) (h : U ≤ V) :
      (affinePlane k).presheaf.map (homOfLE h).op =
        (affinePlane k).𝒪.obj.map (homOfLE h).op := by
    rfl
  have transport (W : (affinePlane k).Opens) (hW : W = affinePlaneDXY k)
      (h1 : W ≤ affinePlaneDX k) (h2 : W ≤ affinePlaneDY k)
      (z1 : (affinePlane k).𝒪.1.obj (Opposite.op (affinePlaneDX k)))
      (z2 : (affinePlane k).𝒪.1.obj (Opposite.op (affinePlaneDY k))) :
      ((affinePlane k).𝒪.obj.map (homOfLE h1).op).hom z1 =
          ((affinePlane k).𝒪.obj.map (homOfLE h2).op).hom z2 ↔
        ((affinePlane k).𝒪.obj.map (homOfLE hX).op).hom z1 =
          ((affinePlane k).𝒪.obj.map (homOfLE hY).op).hom z2 := by
    subst W
    rfl
  have hsecond_apply (s :
      Γ(affinePlane k, affinePlaneDX k) × Γ(affinePlane k, affinePlaneDY k)) :
      puncturedPlaneCechSecond k s =
        affinePlaneSectionRestriction k hX s.1 -
          affinePlaneSectionRestriction k hY s.2 := by
    rfl
  have hfirst_apply (s : Γ(affinePlane k, affinePlanePuncturedOpen k)) :
      puncturedPlaneCechFirst k s =
        (affinePlaneSectionRestriction k le_sup_left s,
          affinePlaneSectionRestriction k le_sup_right s) := by
    rfl
  have hinj : Function.Injective (puncturedPlaneCechFirst k) := by
    intro s t hst
    apply (affinePlane k).toLocallyRingedSpace.𝒪.eq_of_locally_eq₂
      (homOfLE le_sup_left) (homOfLE le_sup_right) le_rfl s t
    · change ((affinePlane k).presheaf.map (homOfLE le_sup_left).op).hom s =
        ((affinePlane k).presheaf.map (homOfLE le_sup_left).op).hom t
      exact congrArg Prod.fst hst
    · change ((affinePlane k).presheaf.map (homOfLE le_sup_right).op).hom s =
        ((affinePlane k).presheaf.map (homOfLE le_sup_right).op).hom t
      exact congrArg Prod.snd hst
  constructor
  · exact hinj
  · unfold Function.Exact
    intro y
    constructor
    · intro hz
      let y' :
          (affinePlane k).𝒪.1.obj (Opposite.op (affinePlaneDX k)) ×
            (affinePlane k).𝒪.1.obj (Opposite.op (affinePlaneDY k)) :=
        ⟨y.1, y.2⟩
      let e := (affinePlane k).toLocallyRingedSpace.𝒪.objSupIsoProdEqLocus
        (affinePlaneDX k) (affinePlaneDY k)
      refine ⟨e.inv ⟨y', ?_⟩, ?_⟩
      · simp only [RingHom.mem_eqLocus, RingHom.comp_apply,
          RingHom.coe_fst, RingHom.coe_snd]
        have hsub := sub_eq_zero.mp ((hsecond_apply y).symm ▸ hz)
        dsimp [affinePlaneSectionRestriction] at hsub
        rw [hmap _ _ hX, hmap _ _ hY] at hsub
        change
          ((affinePlane k).𝒪.1.map (homOfLE hX).op).hom y.1 =
            ((affinePlane k).𝒪.1.map (homOfLE hY).op).hom y.2 at hsub
        apply (transport (affinePlaneDX k ⊓ affinePlaneDY k)
          (affinePlaneDXY_eq_inter k).symm inf_le_left inf_le_right y'.1 y'.2).mpr
        simpa [y'] using hsub
      · apply Prod.ext
        · change (affinePlane k).𝒪.1.map (homOfLE le_sup_left).op
            (e.inv ⟨y', ?_⟩) = y'.1
          exact TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst
            (affinePlane k).𝒪 (affinePlaneDX k) (affinePlaneDY k) _
        · change (affinePlane k).𝒪.1.map (homOfLE le_sup_right).op
            (e.inv ⟨y', ?_⟩) = y'.2
          exact TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd
            (affinePlane k).𝒪 (affinePlaneDX k) (affinePlaneDY k) _
    · rintro ⟨s, rfl⟩
      rw [hfirst_apply, hsecond_apply]
      change
        ((affinePlane k).presheaf.map (homOfLE hX).op).hom
            (((affinePlane k).presheaf.map (homOfLE le_sup_left).op).hom s) -
          ((affinePlane k).presheaf.map (homOfLE hY).op).hom
            (((affinePlane k).presheaf.map (homOfLE le_sup_right).op).hom s) = 0
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp, sub_self]

/-! ## Global sections and non-affineness -/

/-- The map from the polynomial ring to ambient sections on the punctured open. -/
noncomputable def puncturedPlaneAmbientGlobalSectionsMap (k : Type u) [Field k] :
    CommRingCat.of (affinePlaneRing k) ⟶
      Γ(affinePlane k, affinePlanePuncturedOpen k) :=
  (Scheme.ΓSpecIso (CommRingCat.of (affinePlaneRing k))).inv ≫
    (affinePlane k).presheaf.map (homOfLE (show affinePlanePuncturedOpen k ≤ ⊤ from le_top)).op

/-- The same map, with the target written as the global sections of the open subscheme. -/
noncomputable def puncturedPlaneGlobalSectionsMap (k : Type u) [Field k] :
    CommRingCat.of (affinePlaneRing k) ⟶ Γ(puncturedAffinePlane k, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (affinePlaneRing k))).inv ≫
    (puncturedAffinePlaneInclusion k).appTop

theorem puncturedPlaneGlobalSectionsMap_transport (k : Type u) [Field k] :
    puncturedPlaneGlobalSectionsMap k ≫ (affinePlanePuncturedOpen k).topIso.hom =
      puncturedPlaneAmbientGlobalSectionsMap k := by
  rw [puncturedPlaneGlobalSectionsMap, puncturedPlaneAmbientGlobalSectionsMap, Category.assoc,
    Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  rfl

/-- The map from `k[x, y]` to the global sections of the punctured plane is an isomorphism. -/
theorem puncturedPlane_global_sections_isIso (k : Type u) [Field k] :
    IsIso (puncturedPlaneGlobalSectionsMap k) := by
  let hX : affinePlaneDXY k ≤ affinePlaneDX k := by
    rw [affinePlaneDXY_eq_inter]
    exact inf_le_left
  let hY : affinePlaneDXY k ≤ affinePlaneDY k := by
    rw [affinePlaneDXY_eq_inter]
    exact inf_le_right
  let hUX : affinePlaneDX k ≤ affinePlanePuncturedOpen k := le_sup_left
  let hUY : affinePlaneDY k ≤ affinePlanePuncturedOpen k := le_sup_right
  let htopX : affinePlaneDX k ≤ (⊤ : (affinePlane k).Opens) := le_top
  let htopY : affinePlaneDY k ≤ (⊤ : (affinePlane k).Opens) := le_top
  let htopXY : affinePlaneDXY k ≤ (⊤ : (affinePlane k).Opens) := le_top
  let htopU : affinePlanePuncturedOpen k ≤ (⊤ : (affinePlane k).Opens) := le_top
  let hopX : (homOfLE htopX).op ≫ (homOfLE hX).op = (homOfLE htopXY).op :=
    Subsingleton.elim _ _
  let hopY : (homOfLE htopY).op ≫ (homOfLE hY).op = (homOfLE htopXY).op :=
    Subsingleton.elim _ _
  let hopUX : (homOfLE htopU).op ≫ (homOfLE hUX).op = (homOfLE htopX).op :=
    Subsingleton.elim _ _
  let hopUY : (homOfLE htopU).op ≫ (homOfLE hUY).op = (homOfLE htopY).op :=
    Subsingleton.elim _ _
  have hmapX :
      (affinePlane k).presheaf.map (homOfLE htopX).op ≫
          (affinePlane k).presheaf.map (homOfLE hX).op =
        (affinePlane k).presheaf.map (homOfLE htopXY).op := by
    rw [← Functor.map_comp, hopX]
  have hmapY :
      (affinePlane k).presheaf.map (homOfLE htopY).op ≫
          (affinePlane k).presheaf.map (homOfLE hY).op =
        (affinePlane k).presheaf.map (homOfLE htopXY).op := by
    rw [← Functor.map_comp, hopY]
  have hmapUX :
      (affinePlane k).presheaf.map (homOfLE htopU).op ≫
          (affinePlane k).presheaf.map (homOfLE hUX).op =
        (affinePlane k).presheaf.map (homOfLE htopX).op := by
    rw [← Functor.map_comp, hopUX]
  have hmapUY :
      (affinePlane k).presheaf.map (homOfLE htopU).op ≫
          (affinePlane k).presheaf.map (homOfLE hUY).op =
        (affinePlane k).presheaf.map (homOfLE htopY).op := by
    rw [← Functor.map_comp, hopUY]
  let fTopX : Γ(affinePlane k, ⊤) →+* Γ(affinePlane k, affinePlaneDX k) :=
    ((affinePlane k).presheaf.map (homOfLE htopX).op).hom
  let fTopY : Γ(affinePlane k, ⊤) →+* Γ(affinePlane k, affinePlaneDY k) :=
    ((affinePlane k).presheaf.map (homOfLE htopY).op).hom
  let fTopXY : Γ(affinePlane k, ⊤) →+* Γ(affinePlane k, affinePlaneDXY k) :=
    ((affinePlane k).presheaf.map (homOfLE htopXY).op).hom
  let fTopU : Γ(affinePlane k, ⊤) →+* Γ(affinePlane k, affinePlanePuncturedOpen k) :=
    ((affinePlane k).presheaf.map (homOfLE htopU).op).hom
  let fX : Γ(affinePlane k, affinePlaneDX k) →+*
      Γ(affinePlane k, affinePlaneDXY k) :=
    ((affinePlane k).presheaf.map (homOfLE hX).op).hom
  let fY : Γ(affinePlane k, affinePlaneDY k) →+*
      Γ(affinePlane k, affinePlaneDXY k) :=
    ((affinePlane k).presheaf.map (homOfLE hY).op).hom
  let fUX : Γ(affinePlane k, affinePlanePuncturedOpen k) →+*
      Γ(affinePlane k, affinePlaneDX k) :=
    ((affinePlane k).presheaf.map (homOfLE hUX).op).hom
  let fUY : Γ(affinePlane k, affinePlanePuncturedOpen k) →+*
      Γ(affinePlane k, affinePlaneDY k) :=
    ((affinePlane k).presheaf.map (homOfLE hUY).op).hom
  have hmapX_apply (z : Γ(affinePlane k, ⊤)) :
      fX (fTopX z) = fTopXY z := by
    exact congrArg (fun f => f.hom z) hmapX
  have hmapY_apply (z : Γ(affinePlane k, ⊤)) :
      fY (fTopY z) = fTopXY z := by
    exact congrArg (fun f => f.hom z) hmapY
  have hmapUX_apply (z : Γ(affinePlane k, ⊤)) :
      fUX (fTopU z) = fTopX z := by
    exact congrArg (fun f => f.hom z) hmapUX
  have hmapUY_apply (z : Γ(affinePlane k, ⊤)) :
      fUY (fTopU z) = fTopY z := by
    exact congrArg (fun f => f.hom z) hmapUY
  let algX : Algebra (affinePlaneRing k) Γ(affinePlane k, affinePlaneDX k) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra (R := affinePlaneRing k)
      (Opposite.op (affinePlaneDX k))
  let algY : Algebra (affinePlaneRing k) Γ(affinePlane k, affinePlaneDY k) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra (R := affinePlaneRing k)
      (Opposite.op (affinePlaneDY k))
  let algXY : Algebra (affinePlaneRing k) Γ(affinePlane k, affinePlaneDXY k) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra (R := affinePlaneRing k)
      (Opposite.op (affinePlaneDXY k))
  let locX : @IsLocalization.Away (affinePlaneRing k) _ (affinePlaneX k)
      Γ(affinePlane k, affinePlaneDX k) _ algX :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
      (R := affinePlaneRing k) (affinePlaneX k)
  let locY : @IsLocalization.Away (affinePlaneRing k) _ (affinePlaneY k)
      Γ(affinePlane k, affinePlaneDY k) _ algY :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
      (R := affinePlaneRing k) (affinePlaneY k)
  let locXY : @IsLocalization.Away (affinePlaneRing k) _
      (affinePlaneX k * affinePlaneY k)
      Γ(affinePlane k, affinePlaneDXY k) _ algXY :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
      (R := affinePlaneRing k) (affinePlaneX k * affinePlaneY k)
  let i : affinePlaneRing k →+* Γ(affinePlane k, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (affinePlaneRing k))).inv.hom
  let algXMap : affinePlaneRing k →+* Γ(affinePlane k, affinePlaneDX k) :=
    @algebraMap (affinePlaneRing k) Γ(affinePlane k, affinePlaneDX k) _ _ algX
  let algYMap : affinePlaneRing k →+* Γ(affinePlane k, affinePlaneDY k) :=
    @algebraMap (affinePlaneRing k) Γ(affinePlane k, affinePlaneDY k) _ _ algY
  let algXYMap : affinePlaneRing k →+* Γ(affinePlane k, affinePlaneDXY k) :=
    @algebraMap (affinePlaneRing k) Γ(affinePlane k, affinePlaneDXY k) _ _ algXY
  have halgX (p : affinePlaneRing k) : algXMap p = fTopX (i p) := by
    rfl
  have halgY (p : affinePlaneRing k) : algYMap p = fTopY (i p) := by
    rfl
  have halgXY (p : affinePlaneRing k) : algXYMap p = fTopXY (i p) := by
    rfl
  have hmapAlgX (p : affinePlaneRing k) : fX (algXMap p) = algXYMap p := by
    calc
      fX (algXMap p) = fX (fTopX (i p)) := congrArg fX (halgX p)
      _ = fTopXY (i p) := hmapX_apply _
      _ = algXYMap p := (halgXY p).symm
  have hmapAlgY (p : affinePlaneRing k) : fY (algYMap p) = algXYMap p := by
    calc
      fY (algYMap p) = fY (fTopY (i p)) := congrArg fY (halgY p)
      _ = fTopXY (i p) := hmapY_apply _
      _ = algXYMap p := (halgXY p).symm
  have hreprX (a : Γ(affinePlane k, affinePlaneDX k)) :
      ∃ (p : affinePlaneRing k) (m : ℕ),
        a * algXMap ((affinePlaneX k)^m) = algXMap p := by
    obtain ⟨⟨p, xm⟩, ha⟩ :=
      @IsLocalization.surj (affinePlaneRing k) _ (Submonoid.powers (affinePlaneX k))
        Γ(affinePlane k, affinePlaneDX k) _ algX locX a
    obtain ⟨m, hm⟩ := xm.property
    refine ⟨p, m, ?_⟩
    simpa [hm] using ha
  have hreprY (b : Γ(affinePlane k, affinePlaneDY k)) :
      ∃ (q : affinePlaneRing k) (n : ℕ),
        b * algYMap ((affinePlaneY k)^n) = algYMap q := by
    obtain ⟨⟨q, yn⟩, hb⟩ :=
      @IsLocalization.surj (affinePlaneRing k) _ (Submonoid.powers (affinePlaneY k))
        Γ(affinePlane k, affinePlaneDY k) _ algY locY b
    obtain ⟨n, hn⟩ := yn.property
    refine ⟨q, n, ?_⟩
    simpa [hn] using hb
  have hx : Prime (affinePlaneX k) := by
    apply (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv k 1)).mp
    change Prime ((MvPolynomial.finSuccEquiv k 1)
      (MvPolynomial.X (R := k) (0 : Fin (1 + 1))))
    rw [MvPolynomial.finSuccEquiv_X_zero]
    exact Polynomial.prime_X
  have hnot : ¬ affinePlaneX k ∣ affinePlaneY k := by
    intro h
    change MvPolynomial.X (R := k) (0 : Fin 2) ∣
        MvPolynomial.X (R := k) (1 : Fin 2) at h
    obtain ⟨c, hc⟩ := h
    have hp : (MvPolynomial.finSuccEquiv k 1) (MvPolynomial.X (R := k) (0 : Fin 2)) ∣
        (MvPolynomial.finSuccEquiv k 1) (MvPolynomial.X (R := k) (1 : Fin 2)) := by
      refine ⟨(MvPolynomial.finSuccEquiv k 1) c, ?_⟩
      rw [← map_mul]
      exact congrArg (MvPolynomial.finSuccEquiv k 1) hc
    rw [MvPolynomial.finSuccEquiv_X_zero] at hp
    change Polynomial.X ∣ (MvPolynomial.finSuccEquiv k 1)
      (MvPolynomial.X (Fin.succ (0 : Fin 1))) at hp
    rw [MvPolynomial.finSuccEquiv_X_succ] at hp
    rw [Polynomial.X_dvd_iff] at hp
    rw [Polynomial.coeff_C_zero] at hp
    exact MvPolynomial.X_ne_zero _ hp
  have hpoly : ∀ (p q : affinePlaneRing k) (m n : ℕ),
      p * (affinePlaneY k)^n = q * (affinePlaneX k)^m →
        ∃ r, p = (affinePlaneX k)^m * r ∧ q = (affinePlaneY k)^n * r := by
    intro p q m n h
    have hnotpow : ¬ affinePlaneX k ∣ (affinePlaneY k)^n := by
      intro h'
      exact hnot (hx.dvd_of_dvd_pow h')
    have hdiv : (affinePlaneX k)^m ∣ p := by
      apply Prime.pow_dvd_of_dvd_mul_right hx m hnotpow
      exact ⟨q, by simpa [mul_comm] using h⟩
    obtain ⟨r, hr⟩ := hdiv
    refine ⟨r, hr, ?_⟩
    have hc : (affinePlaneX k)^m * q =
        (affinePlaneX k)^m * ((affinePlaneY k)^n * r) := by
      simpa [hr, mul_comm, mul_left_comm, mul_assoc] using h.symm
    exact mul_left_cancel₀ (pow_ne_zero m (MvPolynomial.X_ne_zero _)) hc
  have hab (s : Γ(affinePlane k, affinePlanePuncturedOpen k)) :
      fX (puncturedPlaneCechFirst k s).1 =
        fY (puncturedPlaneCechFirst k s).2 := by
    have hz := ((puncturedPlaneCech_exact k).2
      (puncturedPlaneCechFirst k s)).mpr ⟨s, rfl⟩
    change fX (puncturedPlaneCechFirst k s).1 -
        fY (puncturedPlaneCechFirst k s).2 = 0 at hz
    exact sub_eq_zero.mp hz
  have hpowersX : Submonoid.powers (affinePlaneX k) ≤
      nonZeroDivisors (affinePlaneRing k) := by
    intro z hz
    obtain ⟨m, hm⟩ := hz
    rw [← hm]
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (pow_ne_zero m (MvPolynomial.X_ne_zero _))
  have hinjAlgX : Function.Injective algXMap := by
    exact @IsLocalization.injective (affinePlaneRing k) _
      (Submonoid.powers (affinePlaneX k)) Γ(affinePlane k, affinePlaneDX k) _ algX locX
      hpowersX
  have hambX (r : affinePlaneRing k) :
      fUX ((puncturedPlaneAmbientGlobalSectionsMap k).hom r) = algXMap r := by
    have h := hmapUX_apply (i r)
    change fUX (fTopU (i r)) = fTopX (i r) at h
    change fUX (fTopU (i r)) = algXMap r
    exact h.trans (halgX r).symm
  have hambY (r : affinePlaneRing k) :
      fUY ((puncturedPlaneAmbientGlobalSectionsMap k).hom r) = algYMap r := by
    have h := hmapUY_apply (i r)
    change fUY (fTopU (i r)) = fTopY (i r) at h
    change fUY (fTopU (i r)) = algYMap r
    exact h.trans (halgY r).symm
  have hamb_surj : Function.Surjective (puncturedPlaneAmbientGlobalSectionsMap k) := by
    intro s
    let a := (puncturedPlaneCechFirst k s).1
    let b := (puncturedPlaneCechFirst k s).2
    obtain ⟨p, m, ha⟩ := hreprX a
    obtain ⟨q, n, hb⟩ := hreprY b
    have hab' : fX a = fY b := by
      exact hab s
    have haC : fX a * algXYMap ((affinePlaneX k)^m) = algXYMap p := by
      calc
        fX a * algXYMap ((affinePlaneX k)^m) =
            fX a * fX (algXMap ((affinePlaneX k)^m)) := by
              rw [hmapAlgX]
        _ = fX (a * algXMap ((affinePlaneX k)^m)) :=
          (map_mul fX _ _).symm
        _ = fX (algXMap p) := congrArg fX ha
        _ = algXYMap p := hmapAlgX p
    have hbC : fY b * algXYMap ((affinePlaneY k)^n) = algXYMap q := by
      calc
        fY b * algXYMap ((affinePlaneY k)^n) =
            fY b * fY (algYMap ((affinePlaneY k)^n)) := by
              rw [hmapAlgY]
        _ = fY (b * algYMap ((affinePlaneY k)^n)) :=
          (map_mul fY _ _).symm
        _ = fY (algYMap q) := congrArg fY hb
        _ = algXYMap q := hmapAlgY q
    have hprod : algXYMap (p * (affinePlaneY k)^n) =
        algXYMap (q * (affinePlaneX k)^m) := by
      calc
        algXYMap (p * (affinePlaneY k)^n) =
            algXYMap p * algXYMap ((affinePlaneY k)^n) := map_mul _ _ _
        _ = (fX a * algXYMap ((affinePlaneX k)^m)) *
            algXYMap ((affinePlaneY k)^n) := by rw [haC]
        _ = fX a * (algXYMap ((affinePlaneX k)^m) *
            algXYMap ((affinePlaneY k)^n)) := by ac_rfl
        _ = fY b * (algXYMap ((affinePlaneY k)^n) *
            algXYMap ((affinePlaneX k)^m)) := by rw [hab']; ac_rfl
        _ = (fY b * algXYMap ((affinePlaneY k)^n)) *
            algXYMap ((affinePlaneX k)^m) := by ac_rfl
        _ = algXYMap q * algXYMap ((affinePlaneX k)^m) := by rw [hbC]
        _ = algXYMap (q * (affinePlaneX k)^m) := (map_mul _ _ _).symm
    have hclear : ∃ c : Submonoid.powers (affinePlaneX k * affinePlaneY k),
        c * (p * (affinePlaneY k)^n) = c * (q * (affinePlaneX k)^m) :=
      @IsLocalization.exists_of_eq (affinePlaneRing k) _
        (Submonoid.powers (affinePlaneX k * affinePlaneY k))
        Γ(affinePlane k, affinePlaneDXY k) _ algXY locXY
        (p * (affinePlaneY k)^n) (q * (affinePlaneX k)^m) hprod
    obtain ⟨c, hc⟩ := hclear
    obtain ⟨l, hl⟩ := c.property
    rw [← hl] at hc
    have hcancel : p * (affinePlaneY k)^n = q * (affinePlaneX k)^m := by
      exact mul_left_cancel₀
        (pow_ne_zero l (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))) hc
    obtain ⟨r, hrp, hrq⟩ := hpoly p q m n hcancel
    have haeq : a = algXMap r := by
      have hmul : a * algXMap ((affinePlaneX k)^m) =
          algXMap r * algXMap ((affinePlaneX k)^m) := by
        calc
          a * algXMap ((affinePlaneX k)^m) = algXMap p := ha
          _ = algXMap ((affinePlaneX k)^m * r) := by rw [hrp]
          _ = algXMap r * algXMap ((affinePlaneX k)^m) := by
            rw [map_mul]
            ac_rfl
      exact (@IsLocalization.map_units (affinePlaneRing k) _
        (Submonoid.powers (affinePlaneX k)) Γ(affinePlane k, affinePlaneDX k) _ algX locX
        ⟨(affinePlaneX k)^m, ⟨m, rfl⟩⟩).mul_right_cancel hmul
    have hbeq : b = algYMap r := by
      have hmul : b * algYMap ((affinePlaneY k)^n) =
          algYMap r * algYMap ((affinePlaneY k)^n) := by
        calc
          b * algYMap ((affinePlaneY k)^n) = algYMap q := hb
          _ = algYMap ((affinePlaneY k)^n * r) := by rw [hrq]
          _ = algYMap r * algYMap ((affinePlaneY k)^n) := by
            rw [map_mul]
            ac_rfl
      exact (@IsLocalization.map_units (affinePlaneRing k) _
        (Submonoid.powers (affinePlaneY k)) Γ(affinePlane k, affinePlaneDY k) _ algY locY
        ⟨(affinePlaneY k)^n, ⟨n, rfl⟩⟩).mul_right_cancel hmul
    refine ⟨r, ?_⟩
    apply (puncturedPlaneCech_exact k).1
    apply Prod.ext
    · change fUX ((puncturedPlaneAmbientGlobalSectionsMap k).hom r) = a
      exact (hambX r).trans haeq.symm
    · change fUY ((puncturedPlaneAmbientGlobalSectionsMap k).hom r) = b
      exact (hambY r).trans hbeq.symm
  have hamb_inj : Function.Injective (puncturedPlaneAmbientGlobalSectionsMap k) := by
    intro r t hrt
    apply hinjAlgX
    calc
      algXMap r = fUX ((puncturedPlaneAmbientGlobalSectionsMap k).hom r) := (hambX r).symm
      _ = fUX ((puncturedPlaneAmbientGlobalSectionsMap k).hom t) := congrArg fUX hrt
      _ = algXMap t := hambX t
  have hamb : IsIso (puncturedPlaneAmbientGlobalSectionsMap k) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact ⟨hamb_inj, hamb_surj⟩
  have hcomp : IsIso
      (puncturedPlaneGlobalSectionsMap k ≫ (affinePlanePuncturedOpen k).topIso.hom) := by
    rw [puncturedPlaneGlobalSectionsMap_transport]
    exact hamb
  exact IsIso.of_isIso_comp_right (puncturedPlaneGlobalSectionsMap k)
    (affinePlanePuncturedOpen k).topIso.hom

/-- The punctured affine plane is not affine. -/
theorem puncturedAffinePlane_not_affine (k : Type u) [Field k] :
    ¬ IsAffine (puncturedAffinePlane k) := by
  intro hA
  let hU : IsAffineOpen (affinePlanePuncturedOpen k) := hA
  have hfrom :
      Scheme.Spec.map (puncturedPlaneAmbientGlobalSectionsMap k).op = hU.fromSpec := by
    apply (cancel_mono (affinePlane k).toSpecΓ).1
    rw [hU.fromSpec_toSpecΓ]
    simp [puncturedPlaneAmbientGlobalSectionsMap]
  have : IsIso (puncturedPlaneGlobalSectionsMap k) :=
    puncturedPlane_global_sections_isIso k
  have : IsIso (puncturedPlaneAmbientGlobalSectionsMap k) := by
    rw [← puncturedPlaneGlobalSectionsMap_transport]
    infer_instance
  have : IsIso (Scheme.Spec.map (puncturedPlaneAmbientGlobalSectionsMap k).op) := by
    infer_instance
  have hsurj : Function.Surjective
      (Scheme.Spec.map (puncturedPlaneAmbientGlobalSectionsMap k).op) :=
    (ConcreteCategory.bijective_of_isIso _).2
  have hUall : (affinePlanePuncturedOpen k : Set (affinePlane k)) = Set.univ := by
    rw [← hU.range_fromSpec, ← hfrom]
    exact Set.range_eq_univ.mpr hsurj
  have horigin : affinePlaneOrigin k ∈ affinePlanePuncturedOpen k := by
    change affinePlaneOrigin k ∈ (affinePlanePuncturedOpen k : Set (affinePlane k))
    rw [hUall]
    trivial
  have hnotorigin : affinePlaneOrigin k ∉ affinePlanePuncturedOpen k := by
    change affinePlaneOrigin k ∉ (affinePlanePuncturedOpen k : Set (affinePlane k))
    rw [affinePlanePuncturedOpen_eq_complement_origin]
    simp
  exact hnotorigin horigin

end Formalization.Books.Schemes.Unit09
