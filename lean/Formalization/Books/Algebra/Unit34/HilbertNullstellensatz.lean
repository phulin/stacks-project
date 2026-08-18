import Formalization.Books.Algebra.Unit30.MoreOnImages
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Commutative Algebra, Chapter 34: Hilbert Nullstellensatz

The source's residue fields are Mathlib's canonical `Ideal.ResidueField`s.
Finite field extensions are expressed by `Module.Finite`, finite-type algebras
by `Algebra.FiniteType`, and the assertion about intersections of maximal
ideals by `IsJacobsonRing` and `Ideal.jacobson`.
-/

namespace Formalization.Books.Algebra.Unit34

universe u v

noncomputable section

/-! ## Hilbert Nullstellensatz -/

/- The source's `κ(m)` is `m.asIdeal.ResidueField` for the canonical maximal
   spectrum point `m`.  This general finite-type statement contains the
   polynomial-ring case as its specialization. -/
theorem hilbert_nullstellensatz_residueField_finite
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (m : MaximalSpectrum A) :
    Module.Finite k m.asIdeal.ResidueField := by
  have hA : RingHom.FiniteType (algebraMap k A) :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hM : RingHom.Finite (algebraMap A m.asIdeal.ResidueField) :=
    RingHom.finite_algebraMap.mpr inferInstance
  have hB : RingHom.FiniteType (algebraMap A m.asIdeal.ResidueField) :=
    RingHom.FiniteType.of_finite hM
  have hcomp := RingHom.FiniteType.comp hB hA
  have hft : RingHom.FiniteType (algebraMap k m.asIdeal.ResidueField) := by
    simpa only [IsScalarTower.algebraMap_eq k A m.asIdeal.ResidueField] using hcomp
  have hfinite : Algebra.FiniteType k m.asIdeal.ResidueField :=
    RingHom.finiteType_algebraMap.mp hft
  exact @finite_of_finite_type_of_isJacobsonRing k m.asIdeal.ResidueField
    _ _ _ _ hfinite

/- The source's intersection assertion is exactly the canonical Jacobson-ring
   predicate. -/
theorem hilbert_nullstellensatz_isJacobsonRing
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    IsJacobsonRing A := by
  exact isJacobsonRing_of_finiteType (A := k) (B := A)

/- This is the source-facing form for an individual radical ideal.  The
   stronger bundled result above also records that all such ideals satisfy it. -/
theorem hilbert_nullstellensatz_radical_ideal_eq_jacobson
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (I : Ideal A) (hI : I.IsRadical) :
    I.jacobson = I := by
  exact IsJacobsonRing.out (hilbert_nullstellensatz_isJacobsonRing (k := k) (A := A)) hI

/- Explicit polynomial-ring specializations of the two source clauses. -/
theorem hilbert_nullstellensatz_polynomial_residueField_finite
    {k : Type*} [Field k] (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) k)) :
    Module.Finite k m.asIdeal.ResidueField := by
  exact hilbert_nullstellensatz_residueField_finite (k := k) (A := MvPolynomial (Fin n) k) m

theorem hilbert_nullstellensatz_polynomial_isJacobsonRing
    {k : Type*} [Field k] (n : ℕ) :
    IsJacobsonRing (MvPolynomial (Fin n) k) := by
  exact hilbert_nullstellensatz_isJacobsonRing (k := k) (A := MvPolynomial (Fin n) k)

/-! ## Finite type over a domain -/

/- The map from `R_f` to `K` used by the final lemma is the localization
   universal property applied to the injective map `R → K`. -/
noncomputable def localizationAwayToField
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (hRK : Function.Injective (algebraMap R K)) (f : R) (hf : f ≠ 0) :
    Localization.Away f →+* K :=
  Localization.awayLift (algebraMap R K) f
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff (algebraMap R K) hRK).2 hf))

/- The source's `R ⊂ K` is represented by an injective algebra map.  The
   final conjunction makes both the field structure on `R_f` and the finite
   module underlying the field extension explicit, together with its canonical
   localization map into `K`. -/
theorem field_finite_type_over_domain
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (hRK : Function.Injective (algebraMap R K)) [Algebra.FiniteType R K] :
    ∃ (f : R) (hf : f ≠ 0),
      IsField (Localization.Away f) ∧
        Function.Injective (localizationAwayToField hRK f hf) ∧
          (letI : Algebra (Localization.Away f) K :=
            (localizationAwayToField hRK f hf).toAlgebra
           Module.Finite (Localization.Away f) K) := by
  let φ : R →+* K := algebraMap R K
  have hφ : RingHom.FiniteType φ := by
    dsimp [φ]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let p : PrimeSpectrum R := ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  let qK : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  have hpimage : p ∈ PrimeSpectrum.comap φ '' (Set.univ : Set (PrimeSpectrum K)) := by
    refine ⟨qK, Set.mem_univ _, ?_⟩
    apply PrimeSpectrum.ext
    dsimp [p, qK]
    rw [RingHom.ker_eq_comap_bot]
  have hE : Topology.IsConstructible (Set.univ : Set (PrimeSpectrum K)) := by simp
  obtain ⟨U, hUopen, hUdense, hUsub⟩ :=
    Formalization.Books.Algebra.Unit30.image_constructible_contains_open_dense_subset_of_finiteType
      φ hφ hE hpimage
  have hpcl : p ∈ closure ({p} : Set (PrimeSpectrum R)) := subset_closure (Set.mem_singleton p)
  let p' : closure ({p} : Set (PrimeSpectrum R)) := ⟨p, hpcl⟩
  obtain ⟨q, hq⟩ := hUdense.nonempty_iff.mpr ⟨p'⟩
  have hpbot : p.asIdeal = ⊥ := by
    dsimp [p]
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_bot_of_injective φ hRK
  have hspec : p' ⤳ q := by
    rw [subtype_specializes_iff]
    rw [← PrimeSpectrum.le_iff_specializes]
    change p.asIdeal ≤ (q : PrimeSpectrum R).asIdeal
    rw [hpbot]
    exact bot_le
  have hpU : p' ∈ U := hspec.mem_open hUopen hq
  obtain ⟨s, hsopen, hsU⟩ := isOpen_induced_iff.mp hUopen
  have hps : p ∈ s := by
    have hpU' : p' ∈ Subtype.val ⁻¹' s := by
      rw [hsU]
      exact hpU
    exact hpU'
  obtain ⟨v, ⟨f, rfl⟩, hpf, hvs⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hps hsopen
  have hf : f ≠ 0 := by
    intro hf
    apply (PrimeSpectrum.mem_basicOpen f p).mp hpf
    simp [p, hf]
  refine ⟨f, hf, ?_⟩
  have hpower : ∀ y : R, y ≠ 0 → ∃ n : ℕ, f ^ n ∈ Ideal.span ({y} : Set R) := by
    intro y hy
    have hyv : f ∈ (Ideal.span ({y} : Set R)).radical := by
      have hbasic : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
          (PrimeSpectrum.basicOpen y : Set (PrimeSpectrum R)) := by
        intro x hx
        have hcl : x ∈ closure ({p} : Set (PrimeSpectrum R)) := by
          rw [PrimeSpectrum.closure_singleton, hpbot]
          simp
        let x' : closure ({p} : Set (PrimeSpectrum R)) := ⟨x, hcl⟩
        have hxU : x' ∈ U := by
          rw [← hsU]
          change x ∈ s
          exact hvs hx
        have hximage := hUsub ⟨x', hxU, rfl⟩
        obtain ⟨qK', -, heq⟩ := hximage
        have hqbot : (qK' : PrimeSpectrum K).asIdeal = ⊥ :=
          @Ideal.eq_bot_of_prime K _ qK'.asIdeal qK'.isPrime
        have hcomap : PrimeSpectrum.comap φ (qK' : PrimeSpectrum K) = p := by
          apply PrimeSpectrum.ext
          dsimp [p]
          rw [hqbot, RingHom.ker_eq_comap_bot]
        have hxp : x = p := heq.symm.trans hcomap
        rw [hxp]
        exact (PrimeSpectrum.mem_basicOpen y p).2 (by
          rw [hpbot]
          exact hy)
      exact (PrimeSpectrum.basicOpen_le_basicOpen_iff f y).mp hbasic
    exact Ideal.mem_radical_iff.mp hyv
  let hRdom : IsDomain R := hRK.isDomain
  let hSdom : IsDomain (Localization.Away f) :=
    @Localization.Away.isDomain R _ hRdom f hf
  have hmap : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f)
      (@powers_le_nonZeroDivisors_of_noZeroDivisors R _ f
        (@IsDomain.to_noZeroDivisors R _ hRdom) hf)
  have hfield : IsField (Localization.Away f) := by
    refine
      { exists_pair_ne := hSdom.exists_pair_ne
        mul_comm := mul_comm
        mul_inv_cancel := ?_ }
    intro a ha
    obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj f a
    have hfu : algebraMap R (Localization.Away f) f ≠ 0 := by
      intro h
      apply hf
      apply hmap
      simpa using h
    have hpow : algebraMap R (Localization.Away f) f ^ n ≠ 0 :=
      @pow_ne_zero (Localization.Away f) _ _
        (@isReduced_of_noZeroDivisors (Localization.Away f) _
          (@IsDomain.to_noZeroDivisors (Localization.Away f) _ hSdom)) n hfu
    have hSNoZero : NoZeroDivisors (Localization.Away f) :=
      @IsDomain.to_noZeroDivisors (Localization.Away f) _ hSdom
    have hr0 : r ≠ 0 := by
      intro hr0
      have hz : a * algebraMap R (Localization.Away f) f ^ n = 0 := by
        rw [hr, hr0, map_zero]
      exact ha (hSNoZero.eq_zero_or_eq_zero_of_mul_eq_zero hz |>.resolve_right hpow)
    have hru : IsUnit (algebraMap R (Localization.Away f) r) := by
      apply (IsLocalization.Away.algebraMap_isUnit_iff f).2
      obtain ⟨m, hm⟩ := hpower r hr0
      exact ⟨m, Ideal.mem_span_singleton.mp hm⟩
    have hav : IsUnit (a * algebraMap R (Localization.Away f) f ^ n) := by
      rw [hr]
      exact hru
    have hac : Commute a (algebraMap R (Localization.Away f) f ^ n) := mul_comm _ _
    have haunit : IsUnit a := hac.isUnit_mul_iff.mp hav |>.1
    exact haunit.exists_right_inv
  have hcomp :
      (localizationAwayToField hRK f hf).comp (algebraMap R (Localization.Away f)) =
        algebraMap R K := by
    ext r
    simp [localizationAwayToField]
  have hlocinj : Function.Injective (localizationAwayToField hRK f hf) := by
    rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers f)]
    intro x y
    constructor
    · intro hxy
      exact congrArg (localizationAwayToField hRK f hf) hxy
    · intro hxy
      exact congrArg (algebraMap R (Localization.Away f))
        (hRK ((RingHom.congr_fun hcomp x).symm.trans
          (hxy.trans (RingHom.congr_fun hcomp y))))
  let _ : Field (Localization.Away f) := hfield.toField
  let _ : Algebra (Localization.Away f) K :=
    (localizationAwayToField hRK f hf).toAlgebra
  let hTower : IsScalarTower R (Localization.Away f) K :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hft : Algebra.FiniteType (Localization.Away f) K :=
    @Algebra.FiniteType.of_restrictScalars_finiteType R (Localization.Away f) K
      _ _ _ inferInstance inferInstance inferInstance hTower inferInstance
  have hfinite : Module.Finite (Localization.Away f) K :=
    @finite_of_finite_type_of_isJacobsonRing (Localization.Away f) K
      _ _ inferInstance inferInstance hft
  exact ⟨hfield, hlocinj, hfinite⟩

end

end Formalization.Books.Algebra.Unit34
