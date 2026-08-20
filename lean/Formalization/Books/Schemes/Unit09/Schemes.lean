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
  sorry

theorem affinePlanePuncturedOpen_eq_union (k : Type u) [Field k] :
    affinePlanePuncturedOpen k = affinePlaneDX k ⊔ affinePlaneDY k :=
  rfl

theorem affinePlanePuncturedOpen_eq_complement_origin (k : Type u) [Field k] :
    (affinePlanePuncturedOpen k : Set (affinePlane k)) =
      ({affinePlaneOrigin k} : Set (affinePlane k))ᶜ := by
  sorry

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
  sorry

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
  sorry

/-- The map from `k[x, y]` to the global sections of the punctured plane is an isomorphism. -/
theorem puncturedPlane_global_sections_isIso (k : Type u) [Field k] :
    IsIso (puncturedPlaneGlobalSectionsMap k) := by
  sorry

/-- The punctured affine plane is not affine. -/
theorem puncturedAffinePlane_not_affine (k : Type u) [Field k] :
    ¬ IsAffine (puncturedAffinePlane k) := by
  sorry

end Formalization.Books.Schemes.Unit09
