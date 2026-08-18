import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Inseparable

/-!
# Commutative Algebra, Chapter 108: Pure ideals

The source's pure ideals use Mathlib's canonical `Ideal.Pure` predicate.  The
vanishing locus and support statements use `PrimeSpectrum.zeroLocus` and
`Module.support`, and finite locally free modules use the interface from
Chapter 78.
-/

namespace Formalization.Books.Algebra.Unit108

open Set

universe u v

noncomputable section

/-! ## Characterizations of pure ideals -/

/- The multiplicative subset `1 + I` in the source is not a separate Mathlib
   object, so we record its canonical submonoid presentation here. -/

/-- The multiplicative subset consisting of the elements `1 + x` with `x ∈ I`. -/
def onePlusIdealSubmonoid {R : Type u} [CommRing R] (I : Ideal R) : Submonoid R :=
  { carrier := {x : R | ∃ y : R, y ∈ I ∧ x = 1 + y}
    one_mem' := by
      exact ⟨0, I.zero_mem, by simp⟩
    mul_mem' := by
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      refine ⟨a + b + a * b, ?_, ?_⟩
      · exact I.add_mem (I.add_mem ha hb) (I.mul_mem_left a hb)
      · simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm] }

/-- The eleven conditions in the source's characterization of pure ideals.

Ideal products and intersections are written with Mathlib's lattice and ideal
operations.  The finite-family condition uses a function on `Fin n`, and the
source's multiplicative subset `1 + I` is `onePlusIdealSubmonoid I`. -/
def pureIdealConditions {R : Type u} [CommRing R] (I : Ideal R) : List Prop :=
  [ Ideal.Pure I,
    ∀ J : Ideal R, J ⊓ I = I * J,
    ∀ J : Ideal R, J.FG → J ⊓ I = I * J,
    ∀ x : R, Ideal.span ({x} : Set R) ⊓ I = Ideal.span ({x} : Set R) * I,
    ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x,
    ∀ (n : ℕ) (x : Fin n → R),
      (∀ i : Fin n, x i ∈ I) → ∃ y : R, y ∈ I ∧ ∀ i : Fin n, x i = y * x i,
    ∀ p : PrimeSpectrum R,
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ ∨
        I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤,
    Module.support R I = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
    RingHom.ker (algebraMap R (Localization (onePlusIdealSubmonoid I))) = I,
    ∃ S : Submonoid R, Nonempty ((R ⧸ I) ≃ₐ[R] Localization S),
    Nonempty ((R ⧸ I) ≃ₐ[R] Localization (onePlusIdealSubmonoid I)) ]

private lemma pure_fin_common_multiplier
    {R : Type u} [CommRing R] {I : Ideal R}
    (h : ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x) :
    ∀ (n : ℕ) (x : Fin n → R),
      (∀ i : Fin n, x i ∈ I) → ∃ y : R, y ∈ I ∧ ∀ i : Fin n, x i = y * x i := by
  intro n
  induction n with
  | zero =>
      intro x hx
      exact ⟨0, I.zero_mem, fun i => Fin.elim0 i⟩
  | succ n ih =>
      intro x hx
      obtain ⟨y₀, hy₀, h₀⟩ := h (x 0) (hx 0)
      obtain ⟨y, hy, htail⟩ := ih (fun i => x i.succ) (fun i => hx i.succ)
      refine ⟨y₀ + y - y₀ * y, ?_, ?_⟩
      · exact I.sub_mem (I.add_mem hy₀ hy) (I.mul_mem_left y₀ hy)
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change x 0 = (y₀ + y - y₀ * y) * x 0
          calc
            x 0 = y₀ * x 0 := h₀
            _ = (y₀ + y - y₀ * y) * x 0 := by
              linear_combination -y * h₀
        · change x j.succ = (y₀ + y - y₀ * y) * x j.succ
          calc
            x j.succ = y * x j.succ := htail j
            _ = (y₀ + y - y₀ * y) * x j.succ := by
              linear_combination -y₀ * htail j

private lemma pure_to_atPrime_condition
    {R : Type u} [CommRing R] {I : Ideal R} (hI : Ideal.Pure I) :
    ∀ p : PrimeSpectrum R,
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ ∨
        I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤ := by
  intro p
  by_cases hp : I ≤ p.asIdeal
  · left
    rw [Ideal.map_eq_bot_iff_le_ker]
    exact Ideal.le_ker_atPrime_of_forall_exists_eq_mul
      (fun x hx => by
        obtain ⟨y, hy, hxy⟩ := Ideal.exists_eq_mul_of_pure hx
        exact ⟨y, hy, by simpa [mul_comm] using hxy⟩) hp
  · right
    exact IsLocalization.AtPrime.map_eq_top_of_not_le _ hp

private lemma atPrime_condition_to_pure
    {R : Type u} [CommRing R] {I : Ideal R}
    (hI : ∀ p : PrimeSpectrum R,
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ ∨
        I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤) :
    Ideal.Pure I := by
  apply Ideal.Pure.of_inf_eq_mul I
  intro J hJ
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let p : PrimeSpectrum R := ⟨P, hP.isPrime⟩
  obtain hIbot | hItop := hI p
  · have hIbot' : I.map (algebraMap R (Localization.AtPrime P)) = ⊥ := by
      simpa [p] using hIbot
    rw [IsLocalization.map_inf (M := P.primeCompl) (S := Localization.AtPrime P),
      Ideal.map_mul, hIbot']
    simp
  · have hItop' : I.map (algebraMap R (Localization.AtPrime P)) = ⊤ := by
      simpa [p] using hItop
    rw [IsLocalization.map_inf (M := P.primeCompl) (S := Localization.AtPrime P),
      Ideal.map_mul, hItop']
    simp

private lemma atPrime_condition_to_support
    {R : Type u} [CommRing R] {I : Ideal R}
    (hI : ∀ p : PrimeSpectrum R,
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ ∨
        I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤) :
    Module.support R I = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ := by
  ext p
  by_cases hp : I ≤ p.asIdeal
  · have hbot : I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ := by
      obtain hbot | htop := hI p
      · exact hbot
      · exfalso
        have hdisj : Disjoint (p.asIdeal.primeCompl : Set R) (I : Set R) := by
          exact Set.disjoint_left.2 fun r hr hri => hr (hp hri)
        exact ((IsLocalization.map_algebraMap_ne_top_iff_disjoint
          (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal) I).mpr
          hdisj) htop
    have hnot : p ∉ Module.support R I := by
      rw [Module.notMem_support_iff']
      intro m
      have hmzero : algebraMap R (Localization.AtPrime p.asIdeal) (m : R) = 0 := by
        apply Ideal.mem_bot.mp
        rw [← hbot]
        exact Ideal.mem_map_of_mem _ m.property
      obtain ⟨s, hsm⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl
          (Localization.AtPrime p.asIdeal) (m : R)).mp hmzero
      let r : R := s
      have hr : r ∉ p.asIdeal := s.property
      have hrm : r * (m : R) = 0 := by
        simpa [r] using hsm
      refine ⟨r, hr, ?_⟩
      apply Subtype.ext
      simpa [smul_eq_mul] using hrm
    simp [hnot, PrimeSpectrum.mem_zeroLocus, hp]
  · have htop : I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤ := by
      obtain hbot | htop := hI p
      · exfalso
        obtain ⟨r, hri, hrp⟩ := Set.not_subset.mp hp
        have hmapzero : algebraMap R (Localization.AtPrime p.asIdeal) r = 0 := by
          apply Ideal.mem_bot.mp
          rw [← hbot]
          exact Ideal.mem_map_of_mem _ hri
        have hunit := IsLocalization.map_units (Localization.AtPrime p.asIdeal)
          (⟨r, hrp⟩ : p.asIdeal.primeCompl)
        exact hunit.ne_zero hmapzero
      · exact htop
    have hmem : p ∈ Module.support R I := by
      rw [Module.mem_support_iff']
      obtain ⟨x, hxi, hxp⟩ := Set.not_subset.mp hp
      refine ⟨⟨x, hxi⟩, ?_⟩
      intro r hr hrzero
      have hrx : r * x = 0 := by
        simpa [smul_eq_mul] using congrArg Subtype.val hrzero
      exact (p.isPrime.mem_or_mem (by simpa [hrx] using p.asIdeal.zero_mem)).elim hr hxp
    simp [hmem, PrimeSpectrum.mem_zeroLocus, hp]

private lemma pure_multiplier_to_onePlus_kernel
    {R : Type u} [CommRing R] {I : Ideal R}
    (h : ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x) :
    RingHom.ker (algebraMap R (Localization (onePlusIdealSubmonoid I))) = I := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (onePlusIdealSubmonoid I)
      (Localization (onePlusIdealSubmonoid I)) x).mp hx
    obtain ⟨y, hy, hsy⟩ := s.property
    have hzero : (1 + y) * x = 0 := by
      simpa [hsy] using hs
    have hxy : y * x ∈ I := by
      simpa [mul_comm] using I.mul_mem_left x hy
    have hx' : x = -(y * x) := by
      linear_combination hzero
    rw [hx']
    exact I.neg_mem hxy
  · intro x hx
    rw [RingHom.mem_ker]
    obtain ⟨y, hy, hxy⟩ := h x hx
    let s : onePlusIdealSubmonoid I :=
      ⟨1 - y, ⟨-y, I.neg_mem hy, by simp [sub_eq_add_neg]⟩⟩
    apply (IsLocalization.map_eq_zero_iff (onePlusIdealSubmonoid I)
      (Localization (onePlusIdealSubmonoid I)) x).mpr
    refine ⟨s, ?_⟩
    have hzero : (1 - y) * x = 0 := by
      linear_combination hxy
    simpa [s] using hzero

private lemma onePlus_algebraMap_surjective_of_kernel
    {R : Type u} [CommRing R] {I : Ideal R}
    (hker : RingHom.ker (algebraMap R (Localization (onePlusIdealSubmonoid I))) = I) :
    Function.Surjective (algebraMap R (Localization (onePlusIdealSubmonoid I))) := by
  intro z
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (onePlusIdealSubmonoid I) z
  obtain ⟨y, hy, hsy⟩ := s.property
  have hyker : y ∈ RingHom.ker (algebraMap R (Localization (onePlusIdealSubmonoid I))) := by
    rw [hker]
    exact hy
  have hmapy : algebraMap R (Localization (onePlusIdealSubmonoid I)) y = 0 :=
    (RingHom.mem_ker.mp hyker)
  have hmaps : algebraMap R (Localization (onePlusIdealSubmonoid I)) (s : R) = 1 := by
    rw [hsy]
    simp [hmapy]
  have hspec := IsLocalization.mk'_spec'
    (Localization (onePlusIdealSubmonoid I)) 1 s
  rw [hmaps] at hspec
  have hden : IsLocalization.mk' (Localization (onePlusIdealSubmonoid I)) 1 s = 1 := by
    simpa using hspec
  refine ⟨x, ?_⟩
  have hmk : IsLocalization.mk' (Localization (onePlusIdealSubmonoid I)) x s =
      algebraMap R (Localization (onePlusIdealSubmonoid I)) x := by
    rw [IsLocalization.mk'_eq_mul_mk'_one, hden]
    simp
  exact hmk.symm

private lemma onePlus_kernel_to_quotient_localization
    {R : Type u} [CommRing R] {I : Ideal R}
    (hker : RingHom.ker (algebraMap R (Localization (onePlusIdealSubmonoid I))) = I) :
    Nonempty ((R ⧸ I) ≃ₐ[R] Localization (onePlusIdealSubmonoid I)) := by
  let f : R →ₐ[R] Localization (onePlusIdealSubmonoid I) :=
    { algebraMap R (Localization (onePlusIdealSubmonoid I)) with
      commutes' := fun r => by simp }
  have hf : Function.Surjective f := by
    simpa [f] using onePlus_algebraMap_surjective_of_kernel hker
  have hkerf : RingHom.ker f.toRingHom = I := by
    simpa [f] using hker
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := f) hf
  exact ⟨(Ideal.quotientEquivAlgOfEq R hkerf.symm).trans e⟩

private lemma quotient_localization_to_pure
    {R : Type u} [CommRing R] {I : Ideal R} {S : Submonoid R}
    (h : Nonempty ((R ⧸ I) ≃ₐ[R] Localization S)) : Ideal.Pure I := by
  obtain ⟨e⟩ := h
  letI : Module.Flat R (Localization S) := IsLocalization.flat (Localization S) S
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

private lemma support_to_atPrime_condition
    {R : Type u} [CommRing R] {I : Ideal R}
    (hSupport : Module.support R I = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ) :
    ∀ p : PrimeSpectrum R,
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ ∨
        I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤ := by
  intro p
  by_cases hp : I ≤ p.asIdeal
  · left
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker]
    have hz : p ∈ PrimeSpectrum.zeroLocus (I : Set R) :=
      (PrimeSpectrum.mem_zeroLocus p (I : Set R)).mpr hp
    have hnot : p ∉ Module.support R I := by
      rw [hSupport]
      simpa using hz
    rw [Module.notMem_support_iff'] at hnot
    obtain ⟨r, hr, hrx⟩ := hnot ⟨x, hx⟩
    apply (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) x).mpr
    exact ⟨⟨r, hr⟩, by simpa [smul_eq_mul] using congrArg Subtype.val hrx⟩
  · right
    exact IsLocalization.AtPrime.map_eq_top_of_not_le _ hp

/-- The source's eleven equivalent characterizations of a pure ideal. -/
theorem pure_ideal_characterization
    {R : Type u} [CommRing R] (I : Ideal R) :
    List.TFAE (pureIdealConditions I) := by
  change List.TFAE [
    Ideal.Pure I,
    ∀ J : Ideal R, J ⊓ I = I * J,
    ∀ J : Ideal R, J.FG → J ⊓ I = I * J,
    ∀ x : R, Ideal.span ({x} : Set R) ⊓ I = Ideal.span ({x} : Set R) * I,
    ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x,
    ∀ (n : ℕ) (x : Fin n → R),
      (∀ i : Fin n, x i ∈ I) → ∃ y : R, y ∈ I ∧ ∀ i : Fin n, x i = y * x i,
    ∀ p : PrimeSpectrum R,
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ ∨
        I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤,
    Module.support R I = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
    RingHom.ker (algebraMap R (Localization (onePlusIdealSubmonoid I))) = I,
    ∃ S : Submonoid R, Nonempty ((R ⧸ I) ≃ₐ[R] Localization S),
    Nonempty ((R ⧸ I) ≃ₐ[R] Localization (onePlusIdealSubmonoid I))]
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      letI : Ideal.Pure I := h
      intro J
      simpa [inf_comm] using Ideal.inf_eq_mul_of_pure I J
    · intro h
      apply Ideal.Pure.of_inf_eq_mul I
      intro J hJ
      simpa [inf_comm] using h J
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h
      letI : Ideal.Pure I := h
      intro J hJ
      simpa [inf_comm] using Ideal.inf_eq_mul_of_pure I J
    · intro h
      apply Ideal.Pure.of_inf_eq_mul I
      intro J hJ
      simpa [inf_comm] using h J hJ
  tfae_have 1 ↔ 4 := by
    constructor
    · intro h x
      letI : Ideal.Pure I := h
      simpa [inf_comm, mul_comm] using
        Ideal.inf_eq_mul_of_pure I (Ideal.span ({x} : Set R))
    · intro h
      have hmul : ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x := by
        intro x hx
        have hx' : x ∈ Ideal.span ({x} : Set R) ⊓ I :=
          ⟨Ideal.subset_span (by simp), hx⟩
        rw [h x] at hx'
        obtain ⟨y, hy, hxy⟩ := Ideal.mem_span_singleton_mul.mp hx'
        exact ⟨y, hy, by simpa [mul_comm] using hxy.symm⟩
      exact quotient_localization_to_pure
        (onePlus_kernel_to_quotient_localization
          (pure_multiplier_to_onePlus_kernel hmul))
  tfae_have 1 ↔ 5 := by
    constructor
    · intro h x hx
      obtain ⟨y, hy, hxy⟩ := Ideal.exists_eq_mul_of_pure hx
      exact ⟨y, hy, by simpa [mul_comm] using hxy⟩
    · intro h
      exact quotient_localization_to_pure
        (onePlus_kernel_to_quotient_localization
          (pure_multiplier_to_onePlus_kernel h))
  tfae_have 1 ↔ 6 := by
    constructor
    · intro h
      apply pure_fin_common_multiplier
      intro x hx
      obtain ⟨y, hy, hxy⟩ := Ideal.exists_eq_mul_of_pure hx
      exact ⟨y, hy, by simpa [mul_comm] using hxy⟩
    · intro h
      have hmul : ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x := by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := h 1 (fun _ => x) (by intro i; exact hx)
        exact ⟨y, hy, hxy 0⟩
      exact quotient_localization_to_pure
        (onePlus_kernel_to_quotient_localization
          (pure_multiplier_to_onePlus_kernel hmul))
  tfae_have 1 ↔ 7 := by
    constructor
    · exact pure_to_atPrime_condition
    · exact atPrime_condition_to_pure
  tfae_have 1 ↔ 8 := by
    constructor
    · intro h
      exact atPrime_condition_to_support (pure_to_atPrime_condition h)
    · exact fun h => atPrime_condition_to_pure (support_to_atPrime_condition h)
  tfae_have 1 ↔ 9 := by
    constructor
    · intro h
      let hmul : ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x := by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := Ideal.exists_eq_mul_of_pure hx
        exact ⟨y, hy, by simpa [mul_comm] using hxy⟩
      exact pure_multiplier_to_onePlus_kernel hmul
    · intro h
      exact quotient_localization_to_pure
        (onePlus_kernel_to_quotient_localization h)
  tfae_have 1 ↔ 10 := by
    constructor
    · intro h
      let hmul : ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x := by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := Ideal.exists_eq_mul_of_pure hx
        exact ⟨y, hy, by simpa [mul_comm] using hxy⟩
      exact ⟨onePlusIdealSubmonoid I,
        onePlus_kernel_to_quotient_localization
          (pure_multiplier_to_onePlus_kernel hmul)⟩
    · rintro ⟨S, hS⟩
      exact quotient_localization_to_pure hS
  tfae_have 1 ↔ 11 := by
    constructor
    · intro h
      let hmul : ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x := by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := Ideal.exists_eq_mul_of_pure hx
        exact ⟨y, hy, by simpa [mul_comm] using hxy⟩
      exact onePlus_kernel_to_quotient_localization
        (pure_multiplier_to_onePlus_kernel hmul)
    · exact quotient_localization_to_pure
  tfae_finish

/-! ## Vanishing loci and pure ideals -/

/- This is the forward part of the source's bijection, made explicit so the
   source-facing map below has a precise codomain. -/

/-- The vanishing locus of a pure ideal is closed and stable under generalization. -/
theorem pure_ideal_zeroLocus_isClosed_and_stableUnderGeneralization
    {R : Type u} [CommRing R] (I : Ideal R) (hI : Ideal.Pure I) :
    IsClosed (PrimeSpectrum.zeroLocus (I : Set R)) ∧
      StableUnderGeneralization (PrimeSpectrum.zeroLocus (I : Set R)) := by
  constructor
  · exact PrimeSpectrum.isClosed_zeroLocus _
  · letI : Module.Flat R (R ⧸ I) := hI
    have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
        PrimeSpectrum.zeroLocus (I : Set R) := by
      rw [range_comap_of_surjective _ (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    rw [← hrange]
    exact (RingHom.Flat.generalizingMap_comap
      (RingHom.flat_algebraMap_iff.mpr hI)).stableUnderGeneralization_range

/-- The source's assertion that a pure ideal is determined by its vanishing locus. -/
theorem pure_ideal_eq_of_zeroLocus_eq
    {R : Type u} [CommRing R] {I J : Ideal R}
    (hI : Ideal.Pure I) (hJ : Ideal.Pure J)
    (h : PrimeSpectrum.zeroLocus (I : Set R) =
      PrimeSpectrum.zeroLocus (J : Set R)) :
    I = J := by
  exact (@Ideal.zeroLocus_inj_of_pure R _ I J hI hJ).mp h

/- The subtype map records the source's rule `I ↦ V(I)` with the stated
   codomain of closed sets stable under generalization. -/

/-- The vanishing-locus map from pure ideals to closed generalization-stable sets. -/
def pureIdealZeroLocusMap {R : Type u} [CommRing R] :
    {I : Ideal R // Ideal.Pure I} →
      {Z : Set (PrimeSpectrum R) // IsClosed Z ∧ StableUnderGeneralization Z} :=
  fun I =>
    ⟨PrimeSpectrum.zeroLocus (I.1 : Set R),
      pure_ideal_zeroLocus_isClosed_and_stableUnderGeneralization I.1 I.2⟩

/-- The rule `I ↦ V(I)` is a bijection onto closed sets stable under generalization. -/
private def fixedPointIdeal {R : Type u} [CommRing R] (J : Ideal R) : Ideal R where
  carrier := {x : R | ∃ y : R, y ∈ J ∧ x = x * y}
  zero_mem' := ⟨0, J.zero_mem, by simp⟩
  add_mem' := by
    rintro x z ⟨f, hf, hxf⟩ ⟨g, hg, hzg⟩
    refine ⟨f + g - f * g, ?_, ?_⟩
    · exact J.sub_mem (J.add_mem hf hg) (J.mul_mem_left f hg)
    · calc
        x + z = x * f + z * g :=
          (congrArg (fun t => t + z) hxf).trans
            (congrArg (fun t => x * f + t) hzg)
        _ = (x + z) * (f + g - f * g) := by
          linear_combination -g * hxf - f * hzg
  smul_mem' := by
    rintro r x ⟨f, hf, hxf⟩
    refine ⟨f, hf, ?_⟩
    simpa [smul_eq_mul, mul_assoc] using congrArg (fun a => r * a) hxf

private lemma fixedPointIdeal_le
    {R : Type u} [CommRing R] (J : Ideal R) : fixedPointIdeal J ≤ J := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hx
  rw [hxy]
  exact J.mul_mem_left x hy

private lemma fixedPointIdeal_zeroLocus_eq
    {R : Type u} [CommRing R] {Z : Set (PrimeSpectrum R)}
    (hZ : IsClosed Z) (hgen : StableUnderGeneralization Z) :
    let J : Ideal R := Classical.choose
      ((PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal Z).mp hZ)
    let I : Ideal R := fixedPointIdeal J
    PrimeSpectrum.zeroLocus (I : Set R) = Z := by
  let J : Ideal R := Classical.choose
    ((PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal Z).mp hZ)
  have hJrad : J.IsRadical := (Classical.choose_spec
    ((PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal Z).mp hZ)).1
  have hZJ : Z = PrimeSpectrum.zeroLocus (J : Set R) :=
    (Classical.choose_spec
      ((PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal Z).mp hZ)).2
  let I : Ideal R := fixedPointIdeal J
  have hhard : PrimeSpectrum.zeroLocus (I : Set R) ⊆ Z := by
    intro p hp
    have hpI : p ∈ PrimeSpectrum.zeroLocus (I : Set R) := hp
    have hzero : ∀ a : R, a ∈ p.asIdeal.primeCompl →
        ∀ b : R, b ∈ onePlusIdealSubmonoid J → a * b ≠ 0 := by
      intro a ha b hb hab
      obtain ⟨j, hj, hbj⟩ := hb
      have haI : a ∈ I := by
        refine ⟨-j, J.neg_mem hj, ?_⟩
        have hzero' : a * (1 + j) = 0 := by simpa [hbj] using hab
        have hzero'' : a + a * j = 0 := by
          simpa [mul_add] using hzero'
        calc
          a = a + a * j - a * j := by ring
          _ = 0 - a * j := by rw [hzero'']
          _ = a * (-j) := by ring
      exact ha ((PrimeSpectrum.mem_zeroLocus p (I : Set R)).1 hpI haI)
    let S : Submonoid R :=
      { carrier := {x : R | ∃ a : R, a ∈ p.asIdeal.primeCompl ∧
          ∃ b : R, b ∈ onePlusIdealSubmonoid J ∧ x = a * b}
        one_mem' := ⟨1, p.asIdeal.primeCompl.one_mem, 1,
          (onePlusIdealSubmonoid J).one_mem, by simp⟩
        mul_mem' := by
          rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
          refine ⟨a * c, p.asIdeal.primeCompl.mul_mem ha hc,
            b * d, (onePlusIdealSubmonoid J).mul_mem hb hd, ?_⟩
          ring }
    have hS0 : Disjoint (↑(⊥ : Ideal R) : Set R) (S : Set R) := by
      rw [Set.disjoint_left]
      intro x hx hxs
      have hxzero : x = 0 := by simpa using hx
      obtain ⟨a, ha, b, hb, hab⟩ := hxs
      exact hzero a ha b hb (by simpa [← hab] using hxzero)
    obtain ⟨q, hqprime, hqle, hqS⟩ :=
      Ideal.exists_le_prime_disjoint (⊥ : Ideal R) S hS0
    have hq_p : q ≤ p.asIdeal := by
      intro a ha
      by_contra hap
      have haS : a ∈ S := ⟨a, hap, 1, (onePlusIdealSubmonoid J).one_mem, by simp⟩
      exact Set.disjoint_left.1 hqS ha haS
    have hq_onePlus : Disjoint (q : Set R) (onePlusIdealSubmonoid J : Set R) := by
      apply Set.disjoint_left.2
      intro a ha hja
      exact Set.disjoint_left.1 hqS ha
        ⟨1, p.asIdeal.primeCompl.one_mem, a, hja, by simp⟩
    have hqJproper : q + J ≠ ⊤ := by
      intro htop
      have hone : (1 : R) ∈ q + J := (Ideal.eq_top_iff_one _).mp htop
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hone
      have haone : a ∈ onePlusIdealSubmonoid J := by
        refine ⟨-b, J.neg_mem hb, ?_⟩
        linear_combination hab
      exact Set.disjoint_left.1 hq_onePlus ha haone
    obtain ⟨m, hmmax, hqm⟩ := Ideal.exists_le_maximal (q + J) hqJproper
    have hmJ : J ≤ m := le_trans le_sup_right hqm
    let mp : PrimeSpectrum R := ⟨m, hmmax.isPrime⟩
    have hmZ : mp ∈ Z := hZJ.symm ▸
      (PrimeSpectrum.mem_zeroLocus mp (J : Set R)).2 hmJ
    have hq_m : q ≤ m := le_trans le_sup_left hqm
    have hqZ : (⟨q, hqprime⟩ : PrimeSpectrum R) ∈ Z :=
      hgen ((PrimeSpectrum.le_iff_specializes
        (⟨q, hqprime⟩ : PrimeSpectrum R) mp).mp
        ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hq_m)) hmZ
    have hqJ : J ≤ q := (PrimeSpectrum.mem_zeroLocus
      (⟨q, hqprime⟩ : PrimeSpectrum R) (J : Set R)).1 (hZJ ▸ hqZ)
    exact hZJ.symm ▸ (PrimeSpectrum.mem_zeroLocus p (J : Set R)).2
      (le_trans hqJ hq_p)
  have heasy : Z ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
    intro p hp
    apply (PrimeSpectrum.mem_zeroLocus p (I : Set R)).2
    intro x hx
    exact (PrimeSpectrum.mem_zeroLocus p (J : Set R)).1 (hZJ ▸ hp)
      (fixedPointIdeal_le J hx)
  exact Set.Subset.antisymm hhard heasy

theorem pure_ideal_zeroLocus_bijective
    {R : Type u} [CommRing R] :
    Function.Bijective (pureIdealZeroLocusMap (R := R)) := by
  constructor
  · intro A B hAB
    apply Subtype.ext
    apply pure_ideal_eq_of_zeroLocus_eq A.property B.property
    exact congrArg Subtype.val hAB
  · rintro ⟨Z, hZ, hgen⟩
    let J : Ideal R := Classical.choose
      ((PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal Z).mp hZ)
    have hdata := Classical.choose_spec
      ((PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal Z).mp hZ)
    have hJrad : J.IsRadical := by simpa [J] using hdata.1
    have hZJ : Z = PrimeSpectrum.zeroLocus (J : Set R) := by
      simpa [J] using hdata.2
    let I : Ideal R := fixedPointIdeal J
    have hVI : PrimeSpectrum.zeroLocus (I : Set R) = Z := by
      dsimp [I, J]
      exact fixedPointIdeal_zeroLocus_eq hZ hgen
    have hV : PrimeSpectrum.zeroLocus (I : Set R) =
        PrimeSpectrum.zeroLocus (J : Set R) := hVI.trans hZJ
    have hmul : ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x = y * x := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hx
      have hyRad : y ∈ I.radical := by
        rw [show I.radical = J by
          calc
            I.radical = PrimeSpectrum.vanishingIdeal
                (PrimeSpectrum.zeroLocus (I : Set R)) :=
              (PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical I).symm
            _ = PrimeSpectrum.vanishingIdeal
                (PrimeSpectrum.zeroLocus (J : Set R)) := by rw [hV]
            _ = J := by
              rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hJrad.radical]]
        exact hy
      obtain ⟨n, hyn⟩ := Ideal.mem_radical_iff.mp hyRad
      have hpow : ∀ n : ℕ, x = y ^ n * x := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            calc
              x = y * x := by simpa [mul_comm] using hxy
              _ = y * (y ^ n * x) := congrArg (fun t => y * t) ih
              _ = y ^ (n + 1) * x := by rw [pow_succ]; ring
      exact ⟨y ^ n, hyn, hpow n⟩
    have hpure : Ideal.Pure I := by
      exact (pure_ideal_characterization I).out 4 0 |>.mp hmul
    refine ⟨⟨I, hpure⟩, ?_⟩
    apply Subtype.ext
    exact hVI

/-! ## Finitely generated pure ideals -/

/-- The four conditions characterizing finitely generated pure ideals. -/
def finitelyGeneratedPureIdealConditions
    {R : Type u} [CommRing R] (I : Ideal R) : List Prop :=
  [ Ideal.Pure I ∧ I.FG,
    ∃ e : R, IsIdempotentElem e ∧ I = R ∙ e,
    Ideal.Pure I ∧ IsOpen (PrimeSpectrum.zeroLocus (I : Set R)),
    Module.Projective R (R ⧸ I) ]

private lemma ideal_span_smul_singleton_eq
    {R : Type u} [CommRing R] (e : R) :
    Ideal.span ((R ∙ e : Submodule R R) : Set R) = Ideal.span ({e} : Set R) := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro x hx
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hr]
    simpa [smul_eq_mul] using
      ((Ideal.span ({e} : Set R)).mul_mem_left r
        (Ideal.subset_span (show e ∈ ({e} : Set R) by simp)))
  · apply Ideal.span_le.2
    intro x hx
    have hxe : x = e := Set.mem_singleton_iff.mp hx
    rw [hxe]
    exact Ideal.subset_span (Submodule.mem_span_singleton_self e)

/-- The source's four equivalent characterizations of a finitely generated pure ideal. -/
theorem finitely_generated_pure_ideal_characterization
    {R : Type u} [CommRing R] (I : Ideal R) :
    List.TFAE (finitelyGeneratedPureIdealConditions I) := by
  change List.TFAE [
    Ideal.Pure I ∧ I.FG,
    ∃ e : R, IsIdempotentElem e ∧ I = R ∙ e,
    Ideal.Pure I ∧ IsOpen (PrimeSpectrum.zeroLocus (I : Set R)),
    Module.Projective R (R ⧸ I)]
  tfae_have 1 ↔ 2 := by
    constructor
    · rintro ⟨hP, hFG⟩
      letI : Ideal.Pure I := hP
      exact (Ideal.isIdempotentElem_iff_of_fg I hFG).mp
        (Ideal.isIdempotentElem_of_pure I)
    · rintro ⟨e, he, hEq⟩
      have hFG : I.FG := by
        rw [hEq]
        change Submodule.FG (R ∙ e)
        exact Submodule.fg_span_singleton e
      have hId : IsIdempotentElem I := by
        exact (Ideal.isIdempotentElem_iff_of_fg I hFG).mpr ⟨e, he, hEq⟩
      exact ⟨Ideal.Pure.of_isIdempotentElem hFG hId, hFG⟩
  tfae_have 1 ↔ 3 := by
    constructor
    · rintro ⟨hP, hFG⟩
      obtain ⟨e, he, hEq⟩ :=
        (Ideal.isIdempotentElem_iff_of_fg I hFG).mp
          (Ideal.isIdempotentElem_of_pure I)
      refine ⟨hP, ?_⟩
      rw [hEq]
      change IsOpen (PrimeSpectrum.zeroLocus (Ideal.span ({e} : Set R) : Set R))
      rw [PrimeSpectrum.zeroLocus_span]
      rw [PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem e he]
      exact (PrimeSpectrum.basicOpen (1 - e)).2
    · rintro ⟨hP, hopen⟩
      have hclopen : IsClopen (PrimeSpectrum.zeroLocus (I : Set R)) :=
        ⟨PrimeSpectrum.isClosed_zeroLocus _, hopen⟩
      obtain ⟨e, he, hZ⟩ := (PrimeSpectrum.isClopen_iff_zeroLocus.mp hclopen)
      have hFG : (Ideal.span ({e} : Set R)).FG := by
        change Submodule.FG (Ideal.span ({e} : Set R))
        exact Submodule.fg_span_singleton e
      have hId : IsIdempotentElem (Ideal.span ({e} : Set R)) := by
        exact (Ideal.isIdempotentElem_iff_of_fg (Ideal.span ({e} : Set R)) hFG).mpr
          ⟨e, he, rfl⟩
      have hspanP : Ideal.Pure (Ideal.span ({e} : Set R)) :=
        Ideal.Pure.of_isIdempotentElem hFG hId
      have hzero : PrimeSpectrum.zeroLocus (I : Set R) =
          PrimeSpectrum.zeroLocus (Ideal.span ({e} : Set R) : Set R) := by
        rw [hZ, ← PrimeSpectrum.zeroLocus_span]
      have hEq : I = Ideal.span ({e} : Set R) :=
        (@Ideal.zeroLocus_inj_of_pure R _ I (Ideal.span ({e} : Set R)) hP hspanP).mp hzero
      have hFGI : I.FG := by
        rw [hEq]
        change Submodule.FG (Ideal.span ({e} : Set R))
        exact Submodule.fg_span_singleton e
      exact ⟨hP, hFGI⟩
  tfae_have 1 ↔ 4 := by
    constructor
    · rintro ⟨hP, hFG⟩
      letI : Module.Flat R (R ⧸ I) := hP
      letI : Module.FinitePresentation R (R ⧸ I) :=
        Module.finitePresentation_of_surjective (Submodule.mkQ I)
          (Submodule.mkQ_surjective I) (by
            rw [Submodule.ker_mkQ]
            exact hFG)
      exact Module.Flat.projective_of_finitePresentation
    · intro hproj
      letI : Module.Projective R (R ⧸ I) := hproj
      letI : Module.Finite R (R ⧸ I) :=
        Module.Finite.of_surjective (Submodule.mkQ I) (Submodule.mkQ_surjective I)
      letI : Module.FinitePresentation R (R ⧸ I) :=
        Module.finitePresentation_of_projective R (R ⧸ I)
      have hFGker : (LinearMap.ker (Submodule.mkQ I)).FG :=
        Module.FinitePresentation.fg_ker (Submodule.mkQ I) (Submodule.mkQ_surjective I)
      have hFG : I.FG := by
        change Submodule.FG I
        simpa [Submodule.ker_mkQ] using hFGker
      exact ⟨Module.Flat.of_projective, hFG⟩
  tfae_finish

/-! ## Finite flat modules -/

/- `FiniteLocallyFree` is the earlier chapter's source-facing formulation of
   being finite locally free on a standard-open cover. -/

/-- A ring has the source's finite-flat finiteness property exactly when finite
flat modules are finite locally free. -/
theorem finite_flat_module_finiteLocallyFree_characterization
    {R : Type u} [CommRing R] :
    List.TFAE
      [ ∀ Z : Set (PrimeSpectrum R),
          IsClosed Z → StableUnderGeneralization Z → IsOpen Z,
        ∀ (M : Type v) [AddCommGroup M] [Module R M],
          Module.Finite R M → Module.Flat R M →
            Formalization.Books.Algebra.Unit78.FiniteLocallyFree R M ] := by
  sorry

end

end Formalization.Books.Algebra.Unit108
