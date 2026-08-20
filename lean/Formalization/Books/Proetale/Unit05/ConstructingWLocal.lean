import Formalization.Books.Proetale.Unit02.SomeTopology
import Formalization.Books.Proetale.Unit04.IndZariski
import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Unramified.Basic

/-!
# Pro-étale Cohomology, Chapter 5: Constructing w-local affine schemes

This file records the construction of the w-localization of an affine scheme.
The topological pieces are represented by subsets of `PrimeSpectrum`; the
affine rings and their filtered colimit use Mathlib's `CommRingCat` limits and
colimits.
-/

namespace Formalization.Books.Proetale.Unit05

open Set Function CategoryTheory CategoryTheory.Limits
open Formalization.Books.Proetale.Unit02
open Formalization.Books.Proetale.Unit03
open Formalization.Books.Proetale.Unit04
open Formalization.Books.Topology.Unit22
open Formalization.Books.Topology.Unit24
open _root_.Topology
open scoped BigOperators

universe u v

noncomputable section
section
attribute [local instance] Classical.propDecidable
local instance instDecidableEq (A : Type u) : DecidableEq A := Classical.decEq A

/-! ## Affine w-locality and locally closed pieces -/

/-- An affine scheme is w-local when its spectrum is a w-local space. -/
def IsWLocalAffine {A : Type u} [CommRing A] : Prop :=
  IsWLocalSpace (PrimeSpectrum A)

def IsWLocalRingMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  IsWLocalMap (PrimeSpectrum.comap f)

/-- The ordinary unramified ring-map condition, with the canonical algebra
structure induced by a bare ring homomorphism. -/
def IsUnramifiedRingMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  letI := f.toAlgebra
  Algebra.Unramified A B

/-- A locally closed piece of an affine spectrum in the form `D(f) ∩ V(I)`. -/
structure LocallyClosedPiece (A : Type u) [CommRing A] where
  f : A
  I : Ideal A

/-- The underlying set of a locally closed piece. -/
def LocallyClosedPiece.carrier {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Set (PrimeSpectrum A) :=
  (PrimeSpectrum.basicOpen Z.f : Set (PrimeSpectrum A)) ∩
    PrimeSpectrum.zeroLocus (Z.I : Set A)

/-- The multiplicative set of elements which are units on `(A/I)_f`. -/
def LocallyClosedPiece.units {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Submonoid A where
  carrier := {a |
    IsUnit (algebraMap (A ⧸ Z.I)
      (Localization.Away (Ideal.Quotient.mk Z.I Z.f))
      (Ideal.Quotient.mk Z.I a))}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simpa [map_mul] using ha.mul hb

/-- The source's ring `A_Z^~`. -/
abbrev localizedPieceRing {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Type u :=
  Localization Z.units

instance localizedPieceRing.commRing {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : CommRing (localizedPieceRing Z) := by
  dsimp [localizedPieceRing]
  infer_instance

def localizedPieceRingHom {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : A →+* localizedPieceRing Z :=
  algebraMap A (localizedPieceRing Z)

instance localizedPieceRing.algebra {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Algebra A (localizedPieceRing Z) :=
  (localizedPieceRingHom Z).toAlgebra

/-- The points of `Spec(A)` specializing to a subset. -/
def pointsSpecializingToPiece {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Set (PrimeSpectrum A) :=
  pointsSpecializingTo Z.carrier

abbrev LocallyClosedPointSpace {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) :=
  {x : PrimeSpectrum A // x ∈ pointsSpecializingToPiece Z}

instance locallyClosedPointSpace.topologicalSpace
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    TopologicalSpace (LocallyClosedPointSpace Z) :=
  TopologicalSpace.induced Subtype.val inferInstance

def localizedPieceSpectrumMap {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) :
    PrimeSpectrum (localizedPieceRing Z) → PrimeSpectrum A :=
  PrimeSpectrum.comap (localizedPieceRingHom Z)

theorem localizedPieceRing_quotient_equiv_localizedQuotient
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    Nonempty
      ((localizedPieceRing Z ⧸
          Ideal.map (localizedPieceRingHom Z) Z.I) ≃+*
        Localization (Z.units.map (Ideal.Quotient.mk Z.I))) := by
  exact Formalization.Books.Algebra.Unit03.localized_ideal_quotient_equiv
    Z.units Z.I

theorem localizedPieceRing_closedQuotient_equiv_away
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    Nonempty
      ((localizedPieceRing Z ⧸
          Ideal.map (localizedPieceRingHom Z) Z.I) ≃+*
        Localization.Away (Ideal.Quotient.mk Z.I Z.f)) := by
  let Q := A ⧸ Z.I
  let qf : Q := Ideal.Quotient.mk Z.I Z.f
  have hloc : IsLocalization (Z.units.map (Ideal.Quotient.mk Z.I))
      (Localization.Away qf) := by
    apply IsLocalization.of_le_of_exists_dvd (Submonoid.powers qf)
      (Z.units.map (Ideal.Quotient.mk Z.I))
    · intro s hs
      obtain ⟨n, rfl⟩ := hs
      refine Submonoid.mem_map.mpr ?_
      refine ⟨Z.f ^ n, ?_, ?_⟩
      · change IsUnit
          (algebraMap Q (Localization.Away qf)
            (Ideal.Quotient.mk Z.I (Z.f ^ n)))
        simpa [qf, map_pow] using
          IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit qf)
      · simp [qf]
    · intro s hs
      rcases hs with ⟨a, ha, rfl⟩
      change IsUnit
        (algebraMap Q (Localization.Away qf) (Ideal.Quotient.mk Z.I a)) at ha
      obtain ⟨n, hn⟩ :=
        (IsLocalization.Away.algebraMap_isUnit_iff qf).mp ha
      exact ⟨qf ^ n, ⟨n, rfl⟩, hn⟩
  rcases localizedPieceRing_quotient_equiv_localizedQuotient Z with ⟨e⟩
  let e' := @IsLocalization.algEquiv Q _
    (Z.units.map (Ideal.Quotient.mk Z.I))
    (Localization (Z.units.map (Ideal.Quotient.mk Z.I))) _ _ _
    (Localization.Away qf) _ _ hloc
  refine ⟨?_⟩
  exact e.trans e'.toRingEquiv

private theorem localizedPieceSpectrumMap_range_eq_disjoint
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    Set.range (localizedPieceSpectrumMap Z) =
      {p | Disjoint (Z.units : Set A) p.asIdeal} := by
  have hmap :
      localizedPieceRingHom Z =
        algebraMap A (Localization Z.units) := by
    rfl
  have hrange :
      Set.range
          (PrimeSpectrum.comap
            (algebraMap A (Localization Z.units))) =
        {p | Disjoint (Z.units : Set A) p.asIdeal} :=
    @PrimeSpectrum.localization_comap_range A (Localization Z.units)
      _ _ OreLocalization.instAlgebra Z.units
      (@Localization.isLocalization A _ Z.units)
  change Set.range (PrimeSpectrum.comap (localizedPieceRingHom Z)) =
    {p | Disjoint (Z.units : Set A) p.asIdeal}
  rw [hmap, hrange]

private theorem localizedPieceSpectrumMap_range_eq_pointsSpecializingTo
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    Set.range (localizedPieceSpectrumMap Z) =
      pointsSpecializingToPiece Z := by
  rw [localizedPieceSpectrumMap_range_eq_disjoint]
  ext p
  constructor
  · intro hp
    change Disjoint (Z.units : Set A) p.asIdeal at hp
    have hdisj : Disjoint (↑(p.asIdeal ⊔ Z.I) : Set A)
        (Submonoid.powers Z.f) := by
      rw [Set.disjoint_left]
      intro a ha hs
      obtain ⟨n, rfl⟩ := hs
      obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp ha
      have hmk :
          Ideal.Quotient.mk Z.I b =
            Ideal.Quotient.mk Z.I (Z.f ^ n) := by
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
        change b - (fun x => Z.f ^ x) n ∈ Z.I
        rw [← hbc]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          Z.I.neg_mem hc
      have hunit : b ∈ Z.units := by
        change IsUnit
          (algebraMap (A ⧸ Z.I)
            (Localization.Away (Ideal.Quotient.mk Z.I Z.f))
            (Ideal.Quotient.mk Z.I b))
        rw [hmk]
        simpa [map_pow] using
          IsLocalization.Away.algebraMap_pow_isUnit
            (Ideal.Quotient.mk Z.I Z.f) n
      exact (Set.disjoint_left.mp hp) hunit hb
    obtain ⟨q, hqprime, hqle, hqdisj⟩ :=
      Ideal.exists_le_prime_disjoint (p.asIdeal ⊔ Z.I)
        (Submonoid.powers Z.f) hdisj
    let y : PrimeSpectrum A := ⟨q, hqprime⟩
    refine ⟨y, ?_, ?_⟩
    · constructor
      · apply (PrimeSpectrum.mem_basicOpen Z.f y).mpr
        intro hf
        exact (Set.disjoint_left.mp hqdisj) hf
          (Submonoid.mem_powers Z.f)
      · apply (PrimeSpectrum.mem_zeroLocus y (Z.I : Set A)).mpr
        intro b hb
        exact hqle (Ideal.mem_sup_right hb)
    · exact (PrimeSpectrum.le_iff_specializes p y).mp
        (show p.asIdeal ≤ q from le_trans le_sup_left hqle)
  · rintro ⟨q, hq, hspec⟩
    change Disjoint (Z.units : Set A) p.asIdeal
    rw [Set.disjoint_left]
    intro a ha hunit
    change IsUnit
      (algebraMap (A ⧸ Z.I)
        (Localization.Away (Ideal.Quotient.mk Z.I Z.f))
        (Ideal.Quotient.mk Z.I a)) at ha
    obtain ⟨n, hn⟩ :=
        (IsLocalization.Away.algebraMap_isUnit_iff
        (Ideal.Quotient.mk Z.I Z.f)).mp ha
    obtain ⟨b, hb⟩ := hn
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hmk :
        Ideal.Quotient.mk Z.I (Z.f ^ n) =
          Ideal.Quotient.mk Z.I (a * c) := by
      simpa [map_mul] using hb
    have hdiff : Z.f ^ n - a * c ∈ Z.I :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hmk
    have hap : a ∈ q.asIdeal :=
      (PrimeSpectrum.le_iff_specializes p q).mpr hspec hunit
    have hab : a * c ∈ q.asIdeal := by
      simpa [mul_comm] using q.asIdeal.mul_mem_left c hap
    have hpow : Z.f ^ n ∈ q.asIdeal := by
      have hdiff' : Z.f ^ n - a * c ∈ q.asIdeal :=
        hq.2 hdiff
      have hadd := q.asIdeal.add_mem hdiff' hab
      simpa [sub_add_cancel] using hadd
    have hf : Z.f ∈ q.asIdeal := q.2.mem_of_pow_mem _ hpow
    exact (PrimeSpectrum.mem_basicOpen Z.f q).mp hq.1 hf

/-! ## The localization lemma -/

/-- The localization identifies its spectrum with the points specializing to
the chosen locally closed piece, and the piece becomes closed. -/
theorem localization_piece_properties
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    ∃ e : PrimeSpectrum (Localization Z.units) ≃ₜ
        LocallyClosedPointSpace Z,
      (∀ x, (e x : PrimeSpectrum A) = localizedPieceSpectrumMap Z x) ∧
        IsClosed
          (localizedPieceSpectrumMap Z ⁻¹' Z.carrier) := by
  have hrange := localizedPieceSpectrumMap_range_eq_pointsSpecializingTo Z
  have hmap :
      localizedPieceRingHom Z =
        algebraMap A (Localization Z.units) := by
    rfl
  have hemb' :
      IsEmbedding
        (PrimeSpectrum.comap
          (algebraMap A (Localization Z.units))) :=
    @PrimeSpectrum.localization_comap_isEmbedding A
      (Localization Z.units) _ _ OreLocalization.instAlgebra Z.units
      (@Localization.isLocalization A _ Z.units)
  have hemb : IsEmbedding (localizedPieceSpectrumMap Z) := by
    simpa [localizedPieceSpectrumMap, hmap] using hemb'
  have hpre :
      localizedPieceSpectrumMap Z ⁻¹' pointsSpecializingToPiece Z =
        Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [← hrange]
    exact ⟨x, rfl⟩
  let e0 := hemb.homeomorphOfSubsetRange
    (s := pointsSpecializingToPiece Z) (by
      simpa only [hrange] using
        (show pointsSpecializingToPiece Z ⊆ pointsSpecializingToPiece Z from
          subset_rfl))
  let e : PrimeSpectrum (Localization Z.units) ≃ₜ
      LocallyClosedPointSpace Z :=
    (Homeomorph.Set.univ _).symm.trans
      ((Homeomorph.setCongr hpre.symm).trans e0)
  refine ⟨e, ?_, ?_⟩
  · intro x
    rfl
  · have hf : Z.f ∈ Z.units := by
      change IsUnit
        (algebraMap (A ⧸ Z.I)
          (Localization.Away (Ideal.Quotient.mk Z.I Z.f))
          (Ideal.Quotient.mk Z.I Z.f))
      exact IsLocalization.Away.algebraMap_isUnit
        (Ideal.Quotient.mk Z.I Z.f)
    have hbasic :
        localizedPieceSpectrumMap Z ⁻¹'
            (PrimeSpectrum.basicOpen Z.f : Set (PrimeSpectrum A)) =
          Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      apply (PrimeSpectrum.mem_basicOpen Z.f _).mpr
      intro hfx
      have hx : Disjoint (Z.units : Set A)
          (localizedPieceSpectrumMap Z x).asIdeal := by
        have hx' : localizedPieceSpectrumMap Z x ∈
            Set.range (localizedPieceSpectrumMap Z) := ⟨x, rfl⟩
        rw [localizedPieceSpectrumMap_range_eq_disjoint] at hx'
        exact hx'
      exact (Set.disjoint_left.mp hx) hf hfx
    rw [LocallyClosedPiece.carrier, Set.preimage_inter, hbasic,
      univ_inter]
    exact (PrimeSpectrum.isClosed_zeroLocus
      (Z.I : Set A)).preimage (PrimeSpectrum.continuous_comap _)

theorem localization_piece_has_closed_subscheme
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    ∃ Y : AlgebraicGeometry.Scheme,
      ∃ i : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of (localizedPieceRing Z)),
        AlgebraicGeometry.IsClosedImmersion i ∧
          Set.range i.base =
            (localizedPieceSpectrumMap Z ⁻¹' Z.carrier) := by
  let B := localizedPieceRing Z
  let J : Ideal B := Ideal.map (localizedPieceRingHom Z) Z.I
  let Y : AlgebraicGeometry.Scheme :=
    AlgebraicGeometry.Spec (CommRingCat.of (B ⧸ J))
  let i : Y ⟶
      AlgebraicGeometry.Spec (CommRingCat.of B) :=
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk J))
  refine ⟨Y, i, ?_, ?_⟩
  · change AlgebraicGeometry.IsClosedImmersion
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    exact AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
      Ideal.Quotient.mk_surjective
  · change Set.range
      (PrimeSpectrum.comap (Ideal.Quotient.mk J)) =
        (localizedPieceSpectrumMap Z ⁻¹' Z.carrier)
    rw [range_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective]
    have hJ :
        Ideal.map (localizedPieceRingHom Z) Z.I =
          Ideal.span (localizedPieceRingHom Z '' (Z.I : Set A)) := by
      calc
        Ideal.map (localizedPieceRingHom Z) Z.I =
            Ideal.map (localizedPieceRingHom Z)
              (Ideal.span (Z.I : Set A)) := by rw [Z.I.span_eq]
        _ = Ideal.span (localizedPieceRingHom Z '' (Z.I : Set A)) := by
          rw [Ideal.map_span]
    have hf : Z.f ∈ Z.units := by
      change IsUnit
        (algebraMap (A ⧸ Z.I)
          (Localization.Away (Ideal.Quotient.mk Z.I Z.f))
          (Ideal.Quotient.mk Z.I Z.f))
      exact IsLocalization.Away.algebraMap_isUnit
        (Ideal.Quotient.mk Z.I Z.f)
    have hbasic :
        localizedPieceSpectrumMap Z ⁻¹'
            (PrimeSpectrum.basicOpen Z.f : Set (PrimeSpectrum A)) =
          Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      apply (PrimeSpectrum.mem_basicOpen Z.f _).mpr
      intro hfx
      have hx : Disjoint (Z.units : Set A)
          (localizedPieceSpectrumMap Z x).asIdeal := by
        have hx' : localizedPieceSpectrumMap Z x ∈
            Set.range (localizedPieceSpectrumMap Z) := ⟨x, rfl⟩
        rw [localizedPieceSpectrumMap_range_eq_disjoint] at hx'
        exact hx'
      exact (Set.disjoint_left.mp hx) hf hfx
    rw [LocallyClosedPiece.carrier, Set.preimage_inter, hbasic,
      univ_inter]
    change PrimeSpectrum.zeroLocus
        (RingHom.ker (Ideal.Quotient.mk J) : Set B) =
      (PrimeSpectrum.comap (localizedPieceRingHom Z) ⁻¹'
        PrimeSpectrum.zeroLocus (Z.I : Set A))
    rw [Ideal.mk_ker]
    change PrimeSpectrum.zeroLocus
        (Ideal.map (localizedPieceRingHom Z) Z.I : Set B) =
      (PrimeSpectrum.comap (localizedPieceRingHom Z) ⁻¹'
        PrimeSpectrum.zeroLocus (Z.I : Set A))
    rw [hJ, PrimeSpectrum.preimage_comap_zeroLocus,
      PrimeSpectrum.zeroLocus_span]

private theorem localizedPiece_units_eq_of_carrier_eq
    {A : Type u} [CommRing A] (Z Z' : LocallyClosedPiece A)
    (h : Z.carrier = Z'.carrier) :
    Z.units = Z'.units := by
  ext a
  constructor
  · intro ha
    by_contra ha'
    have hdisj : Disjoint (Ideal.span ({a} : Set A) : Set A)
        (Z'.units : Set A) := by
      rw [Set.disjoint_left]
      intro b hb hbunit
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hb
      apply ha'
      change IsUnit
        (algebraMap (A ⧸ Z'.I)
          (Localization.Away (Ideal.Quotient.mk Z'.I Z'.f))
          (Ideal.Quotient.mk Z'.I a))
      apply isUnit_of_mul_isUnit_right
      change IsUnit
        (algebraMap (A ⧸ Z'.I)
          (Localization.Away (Ideal.Quotient.mk Z'.I Z'.f))
          (Ideal.Quotient.mk Z'.I b)) at hbunit
      simpa [← hc, map_mul] using hbunit
    obtain ⟨q, hqprime, hqle, hqdisj⟩ :=
      Ideal.exists_le_prime_disjoint (Ideal.span ({a} : Set A))
        Z'.units hdisj
    let qx : PrimeSpectrum A := ⟨q, hqprime⟩
    have hqpoints' : qx ∈ pointsSpecializingToPiece Z' := by
      rw [← localizedPieceSpectrumMap_range_eq_pointsSpecializingTo Z',
        localizedPieceSpectrumMap_range_eq_disjoint]
      change Disjoint (Z'.units : Set A) qx.asIdeal
      exact hqdisj.symm
    have hqpoints : qx ∈ pointsSpecializingToPiece Z := by
      simpa [pointsSpecializingToPiece, h] using hqpoints'
    have hqrange : qx ∈ Set.range (localizedPieceSpectrumMap Z) := by
      rw [localizedPieceSpectrumMap_range_eq_pointsSpecializingTo Z]
      exact hqpoints
    obtain ⟨p, hp⟩ := hqrange
    have hdisjZ : Disjoint (Z.units : Set A) qx.asIdeal := by
      have hp' : qx ∈ Set.range (localizedPieceSpectrumMap Z) :=
        ⟨p, hp⟩
      rw [localizedPieceSpectrumMap_range_eq_disjoint] at hp'
      exact hp'
    exact (Set.disjoint_left.mp hdisjZ) ha
      (hqle (Ideal.mem_span_singleton_self a))
  · intro ha
    by_contra ha'
    have hdisj : Disjoint (Ideal.span ({a} : Set A) : Set A)
        (Z.units : Set A) := by
      rw [Set.disjoint_left]
      intro b hb hbunit
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hb
      apply ha'
      change IsUnit
        (algebraMap (A ⧸ Z.I)
          (Localization.Away (Ideal.Quotient.mk Z.I Z.f))
          (Ideal.Quotient.mk Z.I a))
      apply isUnit_of_mul_isUnit_right
      change IsUnit
        (algebraMap (A ⧸ Z.I)
          (Localization.Away (Ideal.Quotient.mk Z.I Z.f))
          (Ideal.Quotient.mk Z.I b)) at hbunit
      simpa [← hc, map_mul] using hbunit
    obtain ⟨q, hqprime, hqle, hqdisj⟩ :=
      Ideal.exists_le_prime_disjoint (Ideal.span ({a} : Set A))
        Z.units hdisj
    let qx : PrimeSpectrum A := ⟨q, hqprime⟩
    have hqpoints : qx ∈ pointsSpecializingToPiece Z := by
      rw [← localizedPieceSpectrumMap_range_eq_pointsSpecializingTo Z,
        localizedPieceSpectrumMap_range_eq_disjoint]
      change Disjoint (Z.units : Set A) qx.asIdeal
      exact hqdisj.symm
    have hqpoints' : qx ∈ pointsSpecializingToPiece Z' := by
      simpa [pointsSpecializingToPiece, h] using hqpoints
    have hqrange' : qx ∈ Set.range (localizedPieceSpectrumMap Z') := by
      rw [localizedPieceSpectrumMap_range_eq_pointsSpecializingTo Z']
      exact hqpoints'
    obtain ⟨p, hp⟩ := hqrange'
    have hdisjZ' : Disjoint (Z'.units : Set A) qx.asIdeal := by
      have hp' : qx ∈ Set.range (localizedPieceSpectrumMap Z') :=
        ⟨p, hp⟩
      rw [localizedPieceSpectrumMap_range_eq_disjoint] at hp'
      exact hp'
    exact (Set.disjoint_left.mp hdisjZ') ha
      (hqle (Ideal.mem_span_singleton_self a))

private theorem localizedPieceRing_algEquiv_of_units_eq
    {A : Type u} [CommRing A] (Z Z' : LocallyClosedPiece A)
    (hu : Z.units = Z'.units) :
    Nonempty (localizedPieceRing Z ≃ₐ[A] localizedPieceRing Z') := by
  have hAlgZ :
      localizedPieceRing.algebra Z =
        OreLocalization.instAlgebra := by
    apply Algebra.algebra_ext
    intro a
    rfl
  have hAlgZ' :
      localizedPieceRing.algebra Z' =
        OreLocalization.instAlgebra := by
    apply Algebra.algebra_ext
    intro a
    rfl
  have hloc' :
      @IsLocalization A _ Z.units (Localization Z'.units)
        OreLocalization.instCommSemiring OreLocalization.instAlgebra := by
    rw [hu]
    exact @Localization.isLocalization A _ Z'.units
  let e :=
    @IsLocalization.algEquiv A _ Z.units (Localization Z.units)
      OreLocalization.instCommSemiring OreLocalization.instAlgebra
      (@Localization.isLocalization A _ Z.units)
      (Localization Z'.units) OreLocalization.instCommSemiring
      OreLocalization.instAlgebra hloc'
  rw [hAlgZ, hAlgZ']
  exact ⟨e⟩

/-- The ring `A_Z^~` depends only on the underlying locally closed subset. -/
theorem localizedPieceRing_depends_only_on_carrier
    {A : Type u} [CommRing A] (Z Z' : LocallyClosedPiece A)
    (h : Z.carrier = Z'.carrier) :
    Nonempty (localizedPieceRing Z ≃ₐ[A] localizedPieceRing Z') := by
  have hu := localizedPiece_units_eq_of_carrier_eq Z Z' h
  exact localizedPieceRing_algEquiv_of_units_eq Z Z' hu

/-- Functoriality of the localization along locally closed pieces. -/
def MapsIntoLocallyClosedPiece
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (Z : LocallyClosedPiece A) (Z' : LocallyClosedPiece B) : Prop :=
  ∀ y : PrimeSpectrum B, y ∈ Z'.carrier →
    PrimeSpectrum.comap f y ∈ Z.carrier

private theorem localizedPiece_units_map_mem
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (Z : LocallyClosedPiece A) (Z' : LocallyClosedPiece B)
    (h : MapsIntoLocallyClosedPiece f Z Z') :
    ∀ a ∈ Z.units, f a ∈ Z'.units := by
  intro a ha
  by_contra ha'
  have hdisj : Disjoint (Ideal.span ({f a} : Set B) : Set B)
      (Z'.units : Set B) := by
    rw [Set.disjoint_left]
    intro b hb hbunit
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hb
    apply ha'
    change IsUnit
      (algebraMap (B ⧸ Z'.I)
        (Localization.Away (Ideal.Quotient.mk Z'.I Z'.f))
        (Ideal.Quotient.mk Z'.I (f a)))
    apply isUnit_of_mul_isUnit_right
    change IsUnit
      (algebraMap (B ⧸ Z'.I)
        (Localization.Away (Ideal.Quotient.mk Z'.I Z'.f))
        (Ideal.Quotient.mk Z'.I b)) at hbunit
    simpa [← hc, map_mul] using hbunit
  obtain ⟨q, hqprime, hqle, hqdisj⟩ :=
    Ideal.exists_le_prime_disjoint (Ideal.span ({f a} : Set B))
      Z'.units hdisj
  let qx : PrimeSpectrum B := ⟨q, hqprime⟩
  have hqpoints : qx ∈ pointsSpecializingToPiece Z' := by
    rw [← localizedPieceSpectrumMap_range_eq_pointsSpecializingTo Z',
      localizedPieceSpectrumMap_range_eq_disjoint]
    change Disjoint (Z'.units : Set B) qx.asIdeal
    exact hqdisj.symm
  obtain ⟨y, hy, hxy⟩ := hqpoints
  have hsource : PrimeSpectrum.comap f qx ∈
      pointsSpecializingToPiece Z := by
    refine ⟨PrimeSpectrum.comap f y, h y hy, ?_⟩
    exact hxy.map (PrimeSpectrum.continuous_comap f)
  have hrange : PrimeSpectrum.comap f qx ∈
      Set.range (localizedPieceSpectrumMap Z) := by
    rw [localizedPieceSpectrumMap_range_eq_pointsSpecializingTo Z]
    exact hsource
  obtain ⟨p, hp⟩ := hrange
  have hdisjZ : Disjoint (Z.units : Set A)
      (PrimeSpectrum.comap f qx).asIdeal := by
    have hp' : PrimeSpectrum.comap f qx ∈
        Set.range (localizedPieceSpectrumMap Z) := ⟨p, hp⟩
    rw [localizedPieceSpectrumMap_range_eq_disjoint] at hp'
    exact hp'
  exact (Set.disjoint_left.mp hdisjZ) ha
    (show f a ∈ qx.asIdeal from
      hqle (Ideal.mem_span_singleton_self (f a)))

private theorem localizedPieceRing_isLocalization
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    @IsLocalization A _ Z.units (localizedPieceRing Z) _
      (localizedPieceRing.algebra Z) := by
  have hAlg :
      localizedPieceRing.algebra Z =
        OreLocalization.instAlgebra := by
    apply Algebra.algebra_ext
    intro a
    rfl
  rw [hAlg]
  exact @Localization.isLocalization A _ Z.units

theorem exists_localizedPieceRingHom
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (Z : LocallyClosedPiece A) (Z' : LocallyClosedPiece B)
    (h : MapsIntoLocallyClosedPiece f Z Z') :
    letI : Algebra A (localizedPieceRing Z') :=
      ((localizedPieceRingHom Z').comp f).toAlgebra
    ∃! g : localizedPieceRing Z →ₐ[A] localizedPieceRing Z',
      g.toRingHom.comp (localizedPieceRingHom Z) =
        (localizedPieceRingHom Z').comp f := by
  let algP : Algebra A (localizedPieceRing Z') :=
    ((localizedPieceRingHom Z').comp f).toAlgebra
  let F := @Algebra.ofId A (localizedPieceRing Z') _ _ algP
  let hscalar :=
    @IsScalarTower.of_algebraMap_eq' A A (localizedPieceRing Z)
      _ _ _ _ (localizedPieceRing.algebra Z)
      (localizedPieceRing.algebra Z) (by
        apply RingHom.ext
        intro a
        rfl)
  have hlocZ := localizedPieceRing_isLocalization Z
  have hlocZ' := localizedPieceRing_isLocalization Z'
  have hF : ∀ y : Z.units, IsUnit (F y) := by
    intro y
    change IsUnit
      (algebraMap B (localizedPieceRing Z') (f y))
    exact @IsLocalization.map_units B _ Z'.units
      (localizedPieceRing Z') _ (localizedPieceRing.algebra Z') hlocZ'
      ⟨f y, localizedPiece_units_map_mem f Z Z' h y y.property⟩
  let g :=
    @IsLocalization.liftAlgHom A _ A _ _ Z.units
      (localizedPieceRing Z) _ (localizedPieceRing.algebra Z)
      (localizedPieceRing.algebra Z) hscalar
      (localizedPieceRing Z') _ algP hlocZ F hF
  have hg :
      g.toRingHom.comp (localizedPieceRingHom Z) =
        (localizedPieceRingHom Z').comp f := by
    ext a
    change g (algebraMap A (localizedPieceRing Z) a) =
      algebraMap A (localizedPieceRing Z') a
    exact g.commutes a
  refine ⟨g, hg, ?_⟩
  rintro g' hg'
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext Z.units
  exact hg'.trans hg.symm

/-! ## Finite vanishing-pattern stratifications -/

/-- A decomposition `E = E' ⊔ E''` of a finite set. -/
structure StratumPartition {A : Type u} (E : Finset A) where
  nonvanishing : Finset A
  vanishing : Finset A
  disjoint : Disjoint nonvanishing vanishing
  union_eq : nonvanishing ∪ vanishing = E

def stratumPiece {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : LocallyClosedPiece A where
  f := p.nonvanishing.prod id
  I := Ideal.span (↑p.vanishing : Set A)

/-- The stratum with the prescribed vanishing pattern. -/
def stratum {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : Set (PrimeSpectrum A) :=
  (stratumPiece p).carrier

theorem mem_stratum_iff_vanishing_pattern
    {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) (x : PrimeSpectrum A) :
    x ∈ stratum p ↔
      (∀ f ∈ p.nonvanishing, f ∉ x.asIdeal) ∧
        (∀ f ∈ p.vanishing, f ∈ x.asIdeal) := by
  change
    (x ∈ (PrimeSpectrum.basicOpen (p.nonvanishing.prod id) :
        Set (PrimeSpectrum A)) ∧
      x ∈ PrimeSpectrum.zeroLocus
        (Ideal.span (↑p.vanishing : Set A) : Set A)) ↔
      (∀ f ∈ p.nonvanishing, f ∉ x.asIdeal) ∧
        (∀ f ∈ p.vanishing, f ∈ x.asIdeal)
  simp only [PrimeSpectrum.mem_zeroLocus]
  constructor
  · rintro ⟨hprod, hvan⟩
    refine ⟨?_, ?_⟩
    · intro f hf hfx
      exact hprod (Ideal.prod_mem x.asIdeal hf hfx)
    · intro f hf
      exact hvan (Ideal.subset_span hf)
  · rintro ⟨hnv, hvan⟩
    refine ⟨?_, Ideal.span_le.mpr ?_⟩
    · intro hprod
      obtain ⟨f, hf, hfx⟩ :=
        (x.2.prod_mem_iff_exists_mem p.nonvanishing).mp hprod
      exact hnv f hf hfx
    · intro f hf
      exact hvan f hf

/-- The displayed description of a stratum as `D(∏ E') ∩ V((E''))`. -/
theorem stratum_eq_basicOpen_inter_zeroLocus
    {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) :
    stratum p =
      (PrimeSpectrum.basicOpen (p.nonvanishing.prod id) :
        Set (PrimeSpectrum A)) ∩
        PrimeSpectrum.zeroLocus (Ideal.span (↑p.vanishing : Set A) : Set A) := by
  rfl

theorem stratum_isConstructible
    {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : IsConstructible (stratum p) := by
  rw [stratum_eq_basicOpen_inter_zeroLocus]
  exact Topology.IsConstructible.inter
    (PrimeSpectrum.isConstructible_basicOpen (R := A)) (by
      rw [← Topology.isConstructible_compl]
      exact (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg
        (Submodule.fg_span p.vanishing.finite_toSet)).isConstructible
        (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl)

theorem stratum_isLocallyClosed
    {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : IsLocallyClosed (stratum p) := by
  rw [stratum_eq_basicOpen_inter_zeroLocus]
  exact (PrimeSpectrum.basicOpen (p.nonvanishing.prod id)).isOpen.isLocallyClosed.inter
    (PrimeSpectrum.isClosed_zeroLocus _).isLocallyClosed

/-- The vanishing-pattern strata are pairwise disjoint and cover the spectrum. -/
theorem strata_pairwise_disjoint_and_cover
    {A : Type u} [CommRing A] (E : Finset A) :
    (Pairwise (fun p q : StratumPartition E =>
        Disjoint (stratum p) (stratum q))) ∧
      (⋃ p : StratumPartition E, stratum p) = Set.univ := by
  constructor
  · intro p q hpq
    rw [Set.disjoint_left]
    intro x hxp hxq
    have hp := (mem_stratum_iff_vanishing_pattern p x).mp hxp
    have hq := (mem_stratum_iff_vanishing_pattern q x).mp hxq
    have hpnv : p.nonvanishing = q.nonvanishing := by
      ext f
      constructor
      · intro hf
        have hfE : f ∈ E := by
          rw [← p.union_eq]
          exact Finset.mem_union.mpr (Or.inl hf)
        have hqcases := Finset.mem_union.mp (q.union_eq ▸ hfE)
        rcases hqcases with hqf | hqf
        · exact hqf
        · exact False.elim ((hp.1 f hf) (hq.2 f hqf))
      · intro hf
        have hfE : f ∈ E := by
          rw [← q.union_eq]
          exact Finset.mem_union.mpr (Or.inl hf)
        have hpcases := Finset.mem_union.mp (p.union_eq ▸ hfE)
        rcases hpcases with hpf | hpf
        · exact hpf
        · exact False.elim ((hq.1 f hf) (hp.2 f hpf))
    have hpv : p.vanishing = q.vanishing := by
      ext f
      constructor
      · intro hf
        have hfE : f ∈ E := by
          rw [← p.union_eq]
          exact Finset.mem_union.mpr (Or.inr hf)
        have hqcases := Finset.mem_union.mp (q.union_eq ▸ hfE)
        rcases hqcases with hqf | hqf
        · exact False.elim ((hq.1 f hqf) (hp.2 f hf))
        · exact hqf
      · intro hf
        have hfE : f ∈ E := by
          rw [← q.union_eq]
          exact Finset.mem_union.mpr (Or.inr hf)
        have hpcases := Finset.mem_union.mp (p.union_eq ▸ hfE)
        rcases hpcases with hpf | hpf
        · exact False.elim ((hp.1 f hpf) (hq.2 f hf))
        · exact hpf
    apply hpq
    cases p with
    | mk pnv pv hdisj hunion =>
      cases q with
      | mk qnv qv hdisj' hunion' =>
        simp_all only [hpnv, hpv]
  · ext x
    constructor
    · intro _
      trivial
    · intro _
      let p : StratumPartition E :=
        { nonvanishing := E.filter (fun f => f ∉ x.asIdeal)
          vanishing := E.filter (fun f => f ∈ x.asIdeal)
          disjoint := by
            rw [Finset.disjoint_left]
            intro f hnv hv
            exact (Finset.mem_filter.mp hnv).2 (Finset.mem_filter.mp hv).2
          union_eq := by
            ext f
            by_cases hf : f ∈ x.asIdeal <;> simp [hf] }
      exact Set.mem_iUnion.mpr ⟨p, (mem_stratum_iff_vanishing_pattern p x).mpr
        ⟨fun f hf => (Finset.mem_filter.mp hf).2,
          fun f hf => (Finset.mem_filter.mp hf).2⟩⟩

/-- A finite constructible stratification. -/
structure FiniteConstructibleStratification (X : Type u)
    [TopologicalSpace X] where
  index : Type u
  finite_index : Finite index
  piece : index → Set X
  pairwise_disjoint : Pairwise (fun i j => Disjoint (piece i) (piece j))
  cover : ⋃ i, piece i = Set.univ
  constructible : ∀ i, IsConstructible (piece i)

/-- Every finite constructible stratification of an affine spectrum is
refined by a finite vanishing-pattern stratification. -/
theorem exists_stratum_refinement
    {A : Type u} [CommRing A]
    (S : FiniteConstructibleStratification (PrimeSpectrum A))
    (hS : Nonempty S.index) :
    ∃ E : Finset A, ∀ p : StratumPartition E, ∃ i : S.index,
      stratum p ⊆ S.piece i := by
  sorry

/-! ## The finite stages -/

/-- The localized factor belonging to a stratum. -/
def stratumFactor {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : Type u :=
  localizedPieceRing (stratumPiece p)

instance stratumFactor.commRing {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : CommRing (stratumFactor p) := by
  dsimp [stratumFactor]
  infer_instance

instance stratumFactor.algebra {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : Algebra A (stratumFactor p) := by
  dsimp [stratumFactor]
  infer_instance

def stratumFactorDiagram {A : Type u} [CommRing A] (E : Finset A) :
    Discrete (StratumPartition E) ⥤ CommRingCat :=
  Discrete.functor (fun p : StratumPartition E =>
    CommRingCat.of (stratumFactor p))

/-- The product ring `A_E` of the localized strata. -/
noncomputable def stageRing {A : Type u} [CommRing A] (E : Finset A) : CommRingCat :=
  limit (stratumFactorDiagram E)

/-- The disjoint-union presentation of the spectrum of `A_E`. -/
def stageSpectrum {A : Type u} [CommRing A] (E : Finset A) : Type u :=
  Σ p : StratumPartition E, PrimeSpectrum (stratumFactor p)

instance stageSpectrum.topologicalSpace
    {A : Type u} [CommRing A] (E : Finset A) :
    TopologicalSpace (stageSpectrum E) := by
  unfold stageSpectrum
  infer_instance

def stageClosedLocus {A : Type u} [CommRing A] (E : Finset A) :
    Set (stageSpectrum E) :=
  {x | x.2 ∈
    (localizedPieceSpectrumMap (stratumPiece x.1) ⁻¹'
      (stratumPiece x.1).carrier)}

/-- The spectrum of the product is canonically the disjoint union of the
localized spectra. -/
theorem exists_stageSpectrumEquiv
    {A : Type u} [CommRing A] (E : Finset A) :
    Nonempty (stageSpectrum E ≃ₜ PrimeSpectrum (stageRing E)) := by
  letI : Finite (StratumPartition E) := by
    let encode : StratumPartition E → Set E := fun p =>
      {a | a.1 ∈ p.nonvanishing}
    apply Finite.of_injective encode
    intro p q hpq
    have hnv : p.nonvanishing = q.nonvanishing := by
      ext f
      constructor
      · intro hf
        have hfE : f ∈ E := by
          rw [← p.union_eq]
          exact Finset.mem_union.mpr (Or.inl hf)
        have hf' : (⟨f, hfE⟩ : E) ∈ encode p := by
          exact hf
        rw [hpq] at hf'
        exact hf'
      · intro hf
        have hfE : f ∈ E := by
          rw [← q.union_eq]
          exact Finset.mem_union.mpr (Or.inl hf)
        have hf' : (⟨f, hfE⟩ : E) ∈ encode q := by
          exact hf
        rw [← hpq] at hf'
        exact hf'
    have hpv : p.vanishing = q.vanishing := by
      ext f
      constructor
      · intro hf
        have hfE : f ∈ E := by
          rw [← p.union_eq]
          exact Finset.mem_union.mpr (Or.inr hf)
        have hnot : f ∉ q.nonvanishing := by
          intro hqf
          have hpf : f ∈ p.nonvanishing := by
            rw [hnv]
            exact hqf
          exact (Finset.disjoint_left.mp p.disjoint) hpf hf
        have hqcases := Finset.mem_union.mp (q.union_eq ▸ hfE)
        rcases hqcases with hqf | hqf
        · exact False.elim (hnot hqf)
        · exact hqf
      · intro hf
        have hfE : f ∈ E := by
          rw [← q.union_eq]
          exact Finset.mem_union.mpr (Or.inr hf)
        have hnot : f ∉ p.nonvanishing := by
          intro hpf
          have hqf : f ∈ q.nonvanishing := by
            rw [← hnv]
            exact hpf
          exact (Finset.disjoint_left.mp q.disjoint) hqf hf
        have hpcases := Finset.mem_union.mp (p.union_eq ▸ hfE)
        rcases hpcases with hpf | hpf
        · exact False.elim (hnot hpf)
        · exact hpf
    cases p with
    | mk pnv pv hdisj hunion =>
      cases q with
      | mk qnv qv hdisj' hunion' =>
        simp_all only [hnv, hpv]
  let e : stageRing E ≃+* (∀ p : StratumPartition E, stratumFactor p) :=
    (Pi.isoLimit (stratumFactorDiagram E)).symm.commRingCatIsoToRingEquiv.trans
      (RingEquiv.piEquivPi (fun p : StratumPartition E => stratumFactor p))
  exact ⟨(PrimeSpectrum.sigmaToPiHomeo (fun p : StratumPartition E => stratumFactor p)).trans
    (PrimeSpectrum.homeomorphOfRingEquiv e).symm⟩

noncomputable def stageSpectrumEquiv
    {A : Type u} [CommRing A] (E : Finset A) :
    stageSpectrum E ≃ₜ PrimeSpectrum (stageRing E) :=
  Classical.choice (exists_stageSpectrumEquiv E)

/-- The structure map from the base ring to a finite stage. -/
noncomputable def stageRingMap {A : Type u} [CommRing A] (E : Finset A) :
    A →+* stageRing E :=
  (limit.lift (stratumFactorDiagram E)
    { pt := CommRingCat.of A
      π := Discrete.natTrans
        (fun p => CommRingCat.ofHom (algebraMap A (stratumFactor p.as))) }).hom

instance stageRing.algebra {A : Type u} [CommRing A] (E : Finset A) :
    Algebra A (stageRing E) :=
  (stageRingMap E).toAlgebra

def stageSpectrumMap {A : Type u} [CommRing A] (E : Finset A) :
    PrimeSpectrum (stageRing E) → PrimeSpectrum A :=
  PrimeSpectrum.comap (stageRingMap E)

/-- The closed subscheme `Z_E`, transported to `Spec(A_E)`. -/
def stageClosedLocusOnSpectrum {A : Type u} [CommRing A] (E : Finset A) :
    Set (PrimeSpectrum (stageRing E)) :=
  stageSpectrumEquiv E '' stageClosedLocus E

theorem stageClosedLocus_isClosed
    {A : Type u} [CommRing A] (E : Finset A) :
    IsClosed (stageClosedLocusOnSpectrum E) := by
  apply (stageSpectrumEquiv E).isClosed_image.mpr
  change IsClosed
    ({x : Σ p : StratumPartition E, PrimeSpectrum (stratumFactor p) |
      x.2 ∈ localizedPieceSpectrumMap (stratumPiece x.1) ⁻¹'
        (stratumPiece x.1).carrier} :
      Set (Σ p : StratumPartition E, PrimeSpectrum (stratumFactor p)))
  rw [isClosed_sigma_iff]
  intro p
  change IsClosed
    (localizedPieceSpectrumMap (stratumPiece p) ⁻¹'
      (stratumPiece p).carrier)
  exact (localization_piece_properties (stratumPiece p)).choose_spec.2

theorem stageClosedLocus_has_closed_subscheme
    {A : Type u} [CommRing A] (E : Finset A) :
    ∃ Y : AlgebraicGeometry.Scheme,
      ∃ i : Y ⟶ AlgebraicGeometry.Spec (stageRing E),
        AlgebraicGeometry.IsClosedImmersion i ∧
          Set.range i.base = stageClosedLocusOnSpectrum E := by
  sorry

theorem stageClosedLocus_contains_closedPoints
    {A : Type u} [CommRing A] (E : Finset A) :
    closedPoints (PrimeSpectrum (stageRing E)) ⊆
      stageClosedLocusOnSpectrum E := by
  sorry

theorem stageClosedLocus_every_point_specializes
    {A : Type u} [CommRing A] (E : Finset A) :
    ∀ x : PrimeSpectrum (stageRing E),
      ∃ z ∈ stageClosedLocusOnSpectrum E, x ⤳ z := by
  sorry

/-- The closed locus at a finite stage maps bijectively to the original
spectrum, as in the source's construction. -/
theorem stageClosedLocus_maps_bijectively_to_base
    {A : Type u} [CommRing A] (E : Finset A) :
    Function.Bijective (fun z : stageClosedLocusOnSpectrum E =>
      stageSpectrumMap E z.1) := by
  sorry

/-! ## Transition maps and the w-localization -/

def restrictPartition {A : Type u} {E₁ E₂ : Finset A}
    (h : E₁ ⊆ E₂) (p : StratumPartition E₂) : StratumPartition E₁ where
  nonvanishing := p.nonvanishing.filter (fun a => a ∈ E₁)
  vanishing := p.vanishing.filter (fun a => a ∈ E₁)
  disjoint := by
    exact p.disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  union_eq := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (Finset.mem_filter.mp ha).2
      · exact (Finset.mem_filter.mp ha).2
    · intro ha
      have ha' : a ∈ p.nonvanishing ∪ p.vanishing := by
        rw [p.union_eq]
        exact h ha
      rcases Finset.mem_union.mp ha' with ha' | ha'
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ha', ha⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨ha', ha⟩))

/-- The transition map between the localized factors. -/
theorem exists_stratumTransition
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂)
    (p : StratumPartition E₂) :
    ∃! g : stratumFactor (restrictPartition h p) →+* stratumFactor p,
      g.comp (localizedPieceRingHom (stratumPiece (restrictPartition h p))) =
        (localizedPieceRingHom (stratumPiece p)).comp (RingHom.id A) := by
  sorry

noncomputable def stratumTransition
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂)
    (p : StratumPartition E₂) :
    stratumFactor (restrictPartition h p) →+* stratumFactor p :=
  Classical.choose (exists_stratumTransition h p)

/-- The induced transition map `A_E₁ → A_E₂`. -/
theorem exists_stageRingHom
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    Nonempty (stageRing E₁ ⟶ stageRing E₂) := by
  sorry

noncomputable def stageRingHom
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    stageRing E₁ ⟶ stageRing E₂ :=
  limit.lift (stratumFactorDiagram E₂)
    { pt := stageRing E₁
      π := Discrete.natTrans (fun p =>
        limit.π (stratumFactorDiagram E₁)
            (Discrete.mk (restrictPartition h p.as)) ≫
          CommRingCat.ofHom (stratumTransition h p.as)) }

theorem stageRingHom_commutes_with_base
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    (stageRingHom h).hom.comp (stageRingMap E₁) = stageRingMap E₂ := by
  sorry

def stageScheme {A : Type u} [CommRing A] (E : Finset A) :
    AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (stageRing E)

noncomputable def stageTransitionScheme
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    stageScheme E₂ ⟶ stageScheme E₁ := by
  change AlgebraicGeometry.Spec (stageRing E₂) ⟶
    AlgebraicGeometry.Spec (stageRing E₁)
  exact AlgebraicGeometry.Spec.map (stageRingHom h)

def stageTransitionPoints
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    PrimeSpectrum (stageRing E₂) → PrimeSpectrum (stageRing E₁) :=
  PrimeSpectrum.comap (stageRingHom h).hom

theorem stageTransition_maps_closedLocus
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    MapsTo (stageTransitionPoints h) (stageClosedLocusOnSpectrum E₂)
      (stageClosedLocusOnSpectrum E₁) := by
  sorry

/-- The finite stages form the directed system used in the construction. -/
noncomputable def stageFunctor {A : Type u} [CommRing A] :
    Finset A ⥤ CommRingCat :=
  { obj := stageRing
    map := fun {E₁ E₂} h => stageRingHom (leOfHom h)
    map_id := by sorry
    map_comp := by sorry }

def stageFunctorBaseMap {A : Type u} [CommRing A] (E : Finset A) :
    A →+* stageFunctor (A := A).obj E :=
  stageRingMap E

/- The finite-subset index is the directed poset denoted `I(A)` in the
   source. -/
theorem finiteSubsetIndex_isFiltered {A : Type u} [CommRing A] :
    IsFiltered (Finset A) := by
  infer_instance

/-- The colimit ring `A_w`. -/
noncomputable def wLocalRing {A : Type u} [CommRing A] : CommRingCat :=
  colimit (stageFunctor (A := A))

/-- The affine scheme `X_w = Spec(A_w)`. -/
def wLocalSpectrum {A : Type u} [CommRing A] : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (wLocalRing (A := A))

/-- The inverse system of affine schemes associated to the finite-stage
colimit diagram. -/
noncomputable def stageSchemeDiagram {A : Type u} [CommRing A] :
    (Finset A)ᵒᵖ ⥤ AlgebraicGeometry.Scheme :=
  { obj := fun E => stageScheme E.unop
    map := fun {E F} h => stageTransitionScheme (leOfHom h.unop)
    map_id := by sorry
    map_comp := by sorry }

theorem stageSchemeDiagram_obj_iso
    {A : Type u} [CommRing A] (E : Finset A) :
    Nonempty (stageSchemeDiagram (A := A).obj (Opposite.op E) ≅
      stageScheme E) := by
  change Nonempty (AlgebraicGeometry.Spec (stageRing E) ≅
    AlgebraicGeometry.Spec (stageRing E))
  exact ⟨Iso.refl _⟩

/-- The canonical cone from `Spec(A_w)` to the finite-stage spectra. -/
noncomputable def wLocalSpectrumStageCone {A : Type u} [CommRing A] :
    Cone (stageSchemeDiagram (A := A)) where
  pt := AlgebraicGeometry.Spec (colimit (stageFunctor (A := A)))
  π := { app := fun E =>
      let i : stageRing E.unop ⟶ colimit (stageFunctor (A := A)) :=
        colimit.ι (stageFunctor (A := A)) E.unop
      AlgebraicGeometry.Spec.map i
         naturality := by
           sorry }

theorem wLocalSpectrum_is_limit_of_stage_schemes
    {A : Type u} [CommRing A] :
    Nonempty (IsLimit (wLocalSpectrumStageCone (A := A))) := by
  sorry

noncomputable def wLocalRingMap {A : Type u} [CommRing A] :
    A →+* wLocalRing (A := A) :=
  (colimit.ι (stageFunctor (A := A)) ∅).hom.comp
    (stageFunctorBaseMap (A := A) ∅)

/- The ring map corresponding to the projection from the inverse-limit
   spectrum to the spectrum of a finite stage. -/
noncomputable def wLocalStageRingMap {A : Type u} [CommRing A]
    (E : Finset A) : stageRing E →+* wLocalRing (A := A) :=
  (colimit.ι (stageFunctor (A := A)) E).hom

/-- The closed subscheme locus `Z` in the source's inverse-limit formula. -/
noncomputable def wLocalClosedLocus {A : Type u} [CommRing A] :
    Set (PrimeSpectrum (wLocalRing (A := A))) :=
  {x | ∀ E : Finset A,
    PrimeSpectrum.comap (wLocalStageRingMap (A := A) E) x ∈
      stageClosedLocusOnSpectrum E}

theorem wLocalClosedLocus_eq_closedPoints
    {A : Type u} [CommRing A] :
    wLocalClosedLocus (A := A) =
      closedPoints (PrimeSpectrum (wLocalRing (A := A))) := by
  sorry

theorem exists_wLocalRingMap {A : Type u} [CommRing A] :
    Nonempty (A →+* wLocalRing (A := A)) := by
  exact ⟨wLocalRingMap (A := A)⟩

def wLocalSpectrumMap {A : Type u} [CommRing A] :
    PrimeSpectrum (wLocalRing (A := A)) → PrimeSpectrum A :=
  PrimeSpectrum.comap (wLocalRingMap (A := A))

theorem exists_wLocal_closedLocus_homeomorph
    {A : Type u} [CommRing A] :
    Nonempty
      {e : wLocalClosedLocus (A := A) ≃ₜ PrimeSpectrum A //
        ∀ z, e z = wLocalSpectrumMap (A := A) z} := by
  sorry

theorem wLocalSpectrumMap_bijective_on_closedLocus
    {A : Type u} [CommRing A] :
    Function.Bijective (fun z : wLocalClosedLocus (A := A) =>
      wLocalSpectrumMap (A := A) z) := by
  sorry

theorem wLocalRing_isIndZariski_and_faithfullyFlat
    {A : Type u} [CommRing A] :
    IsIndZariski (wLocalRingMap (A := A)) ∧
      RingHom.FaithfullyFlat (wLocalRingMap (A := A)) := by
  sorry

theorem wLocalConstruction_properties
    {A : Type u} [CommRing A] :
    IsIndZariski (wLocalRingMap (A := A)) ∧
      RingHom.FaithfullyFlat (wLocalRingMap (A := A)) ∧
        IsWLocalAffine (A := wLocalRing (A := A)) ∧
          Nonempty (wLocalClosedLocus (A := A) ≃ₜ PrimeSpectrum A) ∧
            Function.Bijective (fun z : wLocalClosedLocus (A := A) =>
              wLocalSpectrumMap (A := A) z) ∧
              IsClosed (wLocalClosedLocus (A := A)) ∧
                ∀ x : PrimeSpectrum (wLocalRing (A := A)),
                  ∃! z : wLocalClosedLocus (A := A),
                    x ⤳ (z : PrimeSpectrum (wLocalRing (A := A))) := by
  sorry

theorem wLocalClosedLocus_isClosed
    {A : Type u} [CommRing A] :
    IsClosed (wLocalClosedLocus (A := A)) := by
  sorry

theorem wLocal_closedLocus_is_reduced
    {A : Type u} [CommRing A] :
    ∃ Y : AlgebraicGeometry.Scheme,
      ∃ i : Y ⟶ wLocalSpectrum (A := A),
        AlgebraicGeometry.IsClosedImmersion i ∧ AlgebraicGeometry.IsReduced Y ∧
          Set.range i.base = wLocalClosedLocus (A := A) := by
  sorry

/-! ## The size remark and the universal property -/

theorem wLocalRing_cardinal_le
    {A : Type u} [CommRing A] (κ : Cardinal) (hκ : Cardinal.mk A ≤ κ)
    (hinfinite : ℵ₀ ≤ κ) :
    Cardinal.mk (wLocalRing (A := A)) ≤ κ := by
  sorry

theorem wLocalRing_universal
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hB : IsWLocalAffine (A := B)) :
    ∃! g : wLocalRing (A := A) ⟶ CommRingCat.of B,
      CommRingCat.ofHom (wLocalRingMap (A := A)) ≫ g =
        CommRingCat.ofHom f ∧ IsWLocalRingMap g.hom := by
  sorry

/- The source recalls this characterization before applying it to the
   permanence lemma below. -/
theorem profinite_spectrum_iff_all_points_closed
    {A : Type u} [CommRing A] :
    IsProfiniteSpace (PrimeSpectrum A) ↔
      closedPoints (PrimeSpectrum A) = Set.univ := by
  sorry

/-! ## Profinite spectra and permanence -/

def NoSpecializationInFibres
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ q q' : PrimeSpectrum B,
    PrimeSpectrum.comap f q = PrimeSpectrum.comap f q' →
      q ≤ q' → q = q'

theorem profinite_spectrum_of_fibre_condition
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (h : NoSpecializationInFibres f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

def HasAlgebraicResidueExtensions
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ q : PrimeSpectrum B,
    let I := q.asIdeal.comap f
    letI : I.IsPrime := q.isPrime.comap f
    letI : q.asIdeal.IsPrime := q.isPrime
    let g := Ideal.ResidueField.map I q.asIdeal f rfl
    letI := g.toAlgebra
    Algebra.IsAlgebraic I.ResidueField q.asIdeal.ResidueField

theorem profinite_spectrum_of_algebraic_residue_extensions
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hres : HasAlgebraicResidueExtensions f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_local_isomorphism
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : IsLocalIsomorphism f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_identifies_local_rings
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : IdentifiesLocalRings f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_weakly_etale
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : letI := f.toAlgebra; Algebra.WeaklyEtale A B) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_quasiFinite
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : f.QuasiFinite) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  have _ := hA
  sorry

theorem profinite_spectrum_of_unramified
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : IsUnramifiedRingMap f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_etale
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : f.Etale) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

noncomputable def filteredColimitRing
    {F : Type v} [Category.{v} F] (G : F ⥤ CommRingCat) : CommRingCat :=
  colimit G

theorem profinite_spectrum_of_filtered_colimit
    {A : Type u} [CommRing A] (F : Type v) [Category.{v} F]
    [IsFiltered F] (G : F ⥤ CommRingCat)
    (hG : ∀ i, IsProfiniteSpace (PrimeSpectrum (G.obj i))) :
    IsProfiniteSpace (PrimeSpectrum (filteredColimitRing G)) := by
  sorry

/-! ## Localizing along a closed profinite subset -/

theorem exists_indZariski_wLocal_with_closed_points
    {A : Type u} [CommRing A] (I : Ideal A)
    (hV : IsProfiniteSpace {x : PrimeSpectrum A | ∀ a ∈ I, a ∈ x.asIdeal}) :
    ∃ B : CommRingCat, ∃ f : CommRingCat.of A ⟶ B,
      IsIndZariski f.hom ∧
        IsWLocalAffine (A := B) ∧
          closedPoints (PrimeSpectrum B) =
            {x : PrimeSpectrum B | ∀ a ∈ Ideal.map f.hom I, a ∈ x.asIdeal} ∧
            Nonempty (A ⧸ I ≃+* B ⧸ Ideal.map f.hom I) := by
  sorry

/-! ## Algebraic residue-field extensions over a w-local base -/

def wLocalClosedPointIdeal {A : Type u} [CommRing A]
    : Ideal A :=
  PrimeSpectrum.vanishingIdeal (closedPoints (PrimeSpectrum A))

theorem wLocalClosedPointIdeal_isRadical
    {A : Type u} [CommRing A] (hA : IsWLocalAffine (A := A)) :
    (wLocalClosedPointIdeal (A := A)).IsRadical := by
  sorry

theorem wLocalClosedPointIdeal_vanishing
    {A : Type u} [CommRing A] (hA : IsWLocalAffine (A := A)) :
    closedPoints (PrimeSpectrum A) =
      {x : PrimeSpectrum A |
        ∀ a ∈ wLocalClosedPointIdeal (A := A), a ∈ x.asIdeal} := by
  sorry

theorem wLocal_algebraic_residue_extensions
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsWLocalAffine (A := A)) (f : A →+* B)
    (hres : HasAlgebraicResidueExtensions f) :
    ({q : PrimeSpectrum B |
        ∀ a ∈ Ideal.map f (wLocalClosedPointIdeal (A := A)), a ∈ q.asIdeal} ⊆
      closedPoints (PrimeSpectrum B)) ∧
      ∃ C : CommRingCat, ∃ g : CommRingCat.of B ⟶ C,
        IsIndZariski g.hom ∧
          Nonempty (B ⧸ Ideal.map f (wLocalClosedPointIdeal (A := A)) ≃+*
            C ⧸ Ideal.map g.hom (Ideal.map f (wLocalClosedPointIdeal (A := A)))) ∧
          IsWLocalAffine (A := C) ∧
          IsWLocalRingMap (g.hom.comp f) ∧
          PrimeSpectrum.comap (g.hom.comp f) ⁻¹'
              closedPoints (PrimeSpectrum A) =
            closedPoints (PrimeSpectrum C) := by
  sorry

end

end

end Formalization.Books.Proetale.Unit05
