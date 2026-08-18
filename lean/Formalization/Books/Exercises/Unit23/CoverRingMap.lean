import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sets.OpenCover

/-!
# Exercises, Chapter 23: Glueing

This file records the ring-map locality exercise.  The map from `A_a` to
`B_{φ(a)b}` is the canonical localization map induced by the ring homomorphism
`φ : A →+* B`; its body is built from the universal property of localization.
-/

namespace Formalization.Books.Exercises.Unit23

universe u v w z

noncomputable section

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ## Exercise `cover-ring-map` -/

/-- The canonical map `A_a → B_{φ(a)b}`. -/
noncomputable def baseLocalizationToProductLocalization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : A) (b : B) :
    Localization.Away a →+* Localization.Away (φ a * b) :=
  IsLocalization.Away.lift (R := A) (S := Localization.Away a)
    (P := Localization.Away (φ a * b))
    (g := (algebraMap B (Localization.Away (φ a * b))).comp φ) a
    (IsLocalization.Away.isUnit_of_dvd
      (S := Localization.Away (φ a * b))
      (x := φ a * b)
      (r := φ a)
      (dvd_mul_right (φ a) b))

/-- Finite type of a ring map can be checked on basic-open covers of source
and target, using the maps `A_{f_i} → B_{f_i g_j}`. -/
theorem finiteType_ringHom_of_basicOpenCovers
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B)
    {ι : Type w} {κ : Type z} (f : ι → A) (g : κ → B)
    (hA : TopologicalSpace.IsOpenCover
      (fun i : ι => PrimeSpectrum.basicOpen (f i)))
    (hB : TopologicalSpace.IsOpenCover
      (fun j : κ => PrimeSpectrum.basicOpen (g j)))
    (hlocal : ∀ (i : ι) (j : κ),
      RingHom.FiniteType
        (baseLocalizationToProductLocalization φ (f i) (g j))) :
    RingHom.FiniteType φ := by
  algebraize [φ]
  have hspanA : Ideal.span (Set.range f) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hA.iSup_eq_top
  have hspanB : Ideal.span (Set.range g) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hB.iSup_eq_top
  apply Algebra.FiniteType.of_span_eq_top_target (Set.range g) hspanB
  rintro y ⟨j, rfl⟩
  let B' := Localization.Away (g j)
  apply Algebra.FiniteType.of_span_eq_top_source (Set.range f) hspanA
  rintro x ⟨i, rfl⟩
  let R' := Localization.Away (f i)
  let T := R' ⊗[A] B'
  let L := Localization.Away (φ (f i) * g j)
  let U := Localization.Away (algebraMap A B' (f i))
  let H := baseLocalizationToProductLocalization φ (f i) (g j)
  let gAU : A →+* U := (algebraMap B' U).comp (algebraMap A B')
  have hunit : IsUnit (gAU (f i)) := by
    exact IsLocalization.Away.algebraMap_isUnit
      (R := B') (S := U) (algebraMap A B' (f i))
  let G : R' →+* U :=
    IsLocalization.Away.lift (R := A) (S := R') (P := U)
      (g := gAU) (f i) hunit
  let eTensor : T ≃ₐ[B'] U :=
    IsLocalization.Away.tensorRightEquiv B' (f i) R'
  haveI : IsLocalization.Away (φ (f i) * g j) U := by
    simpa [U, B', mul_comm] using
      (IsLocalization.Away.mul' B' U (g j) (φ (f i)))
  let e : L ≃ₐ[B] U :=
    IsLocalization.algEquiv (Submonoid.powers (φ (f i) * g j)) L U
  have hH : H.comp (algebraMap A R') = (algebraMap B L).comp φ := by
    dsimp [H, baseLocalizationToProductLocalization]
    apply IsLocalization.Away.lift_comp
  have hG : G.comp (algebraMap A R') = gAU := by
    simp [G, IsLocalization.Away.lift_comp]
  have hBU : gAU = (algebraMap B U).comp φ := by
    rfl
  have hcomp : e.toRingHom.comp H = G := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f i))
    ext a
    change e (H (algebraMap A R' a)) = G (algebraMap A R' a)
    have hHa : H (algebraMap A R' a) = algebraMap B L (φ a) := by
      simpa only [RingHom.comp_apply] using congrArg (fun k : A →+* L => k a) hH
    have hGa : G (algebraMap A R' a) = gAU a := by
      simpa only [RingHom.comp_apply] using congrArg (fun k : A →+* U => k a) hG
    rw [hHa, hGa, e.commutes, congrArg (fun k : A →+* U => k a) hBU]
    simp only [RingHom.comp_apply]
  letI : Algebra R' L := H.toAlgebra
  letI : Algebra R' U := G.toAlgebra
  let eA : L ≃ₐ[R'] U :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (by
      intro r
      change e (H r) = G r
      exact congrArg (fun k : R' →+* U => k r) hcomp)
  have hL : Algebra.FiniteType R' L := by
    exact hlocal i j
  have hU : Algebra.FiniteType R' U := hL.equiv eA
  have hTensorMap : eTensor.toRingHom.comp (algebraMap R' T) = G := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f i))
    ext a
    change eTensor (algebraMap R' T (algebraMap A R' a)) =
      G (algebraMap A R' a)
    rw [← IsScalarTower.algebraMap_apply A R' T,
      IsScalarTower.algebraMap_apply A B' T, eTensor.commutes]
    change gAU a = G (algebraMap A R' a)
    have hGa : G (algebraMap A R' a) = gAU a := by
      simpa only [RingHom.comp_apply] using congrArg (fun k : A →+* U => k a) hG
    exact hGa.symm
  let eTensorA : T ≃ₐ[R'] U :=
    AlgEquiv.ofRingEquiv (f := eTensor.toRingEquiv) (by
      intro r
      change eTensor (algebraMap R' T r) = G r
      exact congrArg (fun k : R' →+* U => k r) hTensorMap)
  exact hU.equiv eTensorA.symm

end

end Formalization.Books.Exercises.Unit23
