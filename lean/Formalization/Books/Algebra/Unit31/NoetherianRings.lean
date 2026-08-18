import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.OfPrime
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace

/-!
# Commutative Algebra, Chapter 31: Noetherian rings

The source's Noetherian-ring predicate and its standard consequences are
represented by Mathlib's canonical `IsNoetherianRing`, finite-type,
finite-presentation, spectrum, minimal-prime, and localization interfaces.
The source's localization map `R_f → R_p` is made explicit using the
universal property of `Localization.Away`.
-/

namespace Formalization.Books.Algebra.Unit31

open Set
open scoped TensorProduct

noncomputable section

/-! ## Definition and first criteria -/

/- The definition in the source is Mathlib's `IsNoetherianRing`: every ideal
is finitely generated. -/
theorem noetherian_iff_ideal_fg (R : Type*) [CommRing R] :
    IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG :=
  isNoetherianRing_iff_ideal_fg R

/- The source's ascending-chain condition is the specialization of the
canonical module criterion to the regular module `R`. -/
theorem noetherian_iff_ascending_chain_condition
    (R : Type*) [CommRing R] :
    (∀ f : ℕ →o Ideal R, ∃ n, ∀ m, n ≤ m → f n = f m) ↔
      IsNoetherianRing R :=
  monotone_stabilizes_iff_noetherian

/- Cohen's lemma gives the stated prime-ideal criterion. -/
theorem noetherian_of_prime_ideal_fg
    {R : Type*} [CommRing R]
    (h : ∀ I : Ideal R, I.IsPrime → I.FG) :
    IsNoetherianRing R :=
  IsNoetherianRing.of_prime h

/-! ## Permanence and examples -/

/- A finitely generated algebra over a Noetherian ring is Noetherian. -/
theorem finiteType_algebra_isNoetherian
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] :
    IsNoetherianRing S :=
  Algebra.FiniteType.isNoetherianRing R S

/- Every localization of a Noetherian ring is Noetherian. -/
theorem localization_isNoetherian
    {R : Type*} [CommRing R] [IsNoetherianRing R] (S : Submonoid R) :
    IsNoetherianRing (Localization S) := by
  infer_instance

/- The recursive coefficient identities in the source's proof are proof
scaffolding; the chapter-level assertion is the theorem below. -/
theorem mvPowerSeries_isNoetherian
    {R : Type*} [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  infer_instance

/- The two examples in the source use the canonical Noetherian instances for
fields and for `ℤ`. -/
theorem finiteType_algebra_over_field_isNoetherian
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    IsNoetherianRing A :=
  Algebra.FiniteType.isNoetherianRing k A

theorem finiteType_algebra_over_int_isNoetherian
    {A : Type*} [CommRing A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] :
    IsNoetherianRing A :=
  Algebra.FiniteType.isNoetherianRing ℤ A

/-! ## Finite generation and finite presentation -/

/- A finite module over a Noetherian ring is finitely presented. -/
theorem finite_module_isFinitePresentation
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] :
    Module.FinitePresentation R M :=
  Module.finitePresentation_of_finite R M

/- A submodule of a finite module is finite. -/
theorem submodule_of_finite_module_isFinite
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] (N : Submodule R M) :
    Module.Finite R N := by
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)

/- A finite-type algebra over a Noetherian ring is finitely presented. -/
theorem finiteType_algebra_isFinitePresentation
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FinitePresentation R A :=
  (Algebra.FinitePresentation.of_finiteType (R := R) (A := A)).mp inferInstance

/-! ## Topology and minimal primes -/

/- The prime spectrum of a Noetherian ring is a Noetherian topological space. -/
theorem primeSpectrum_isNoetherianSpace
    {R : Type*} [CommRing R] [IsNoetherianRing R] :
    TopologicalSpace.NoetherianSpace (PrimeSpectrum R) := by
  infer_instance

/- The source states the equivalent finiteness of irreducible components and
minimal primes; both canonical consequences are recorded together. -/
theorem primeSpectrum_finite_irreducibleComponents_and_minimalPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] :
    (irreducibleComponents (PrimeSpectrum R)).Finite ∧
      (minimalPrimes R).Finite := by
  exact ⟨TopologicalSpace.NoetherianSpace.finite_irreducibleComponents,
    minimalPrimes.finite_of_isNoetherianRing R⟩

/-! ## Base change -/

/- The two displayed ring maps in the source are represented by the standard
algebra structures, and finite type by `Algebra.FiniteType`. -/
theorem tensorProduct_isNoetherian_of_finiteType
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.FiniteType R R']
    [IsNoetherianRing S] :
    IsNoetherianRing (R' ⊗[R] S) := by
  let _ : Algebra S (S ⊗[R] R') := Algebra.TensorProduct.leftAlgebra
  let _ : IsNoetherianRing (S ⊗[R] R') :=
    Algebra.FiniteType.isNoetherianRing S (S ⊗[R] R')
  let _ : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  exact isNoetherianRing_of_ringEquiv (S ⊗[R] R')
    (Algebra.TensorProduct.commRight R S R').toRingEquiv

/- A finitely generated field extension preserves Noetherianity after tensoring
with a Noetherian algebra. -/
theorem tensorProduct_isNoetherian_of_finiteType_fieldExtension
    {k R K : Type*} [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra.FiniteType k K]
    [IsNoetherianRing R] :
    IsNoetherianRing (K ⊗[k] R) := by
  exact tensorProduct_isNoetherian_of_finiteType (R := k) (S := R) (R' := K)

/-! ## A subring of a local ring -/

/- The canonical map from `R_f` to `R_p`, for `f ∉ p`, obtained by the
localization universal property. -/
noncomputable def localizationAwayToAtPrime
    {R : Type*} [CommRing R] (p : PrimeSpectrum R) (f : R)
    (hf : f ∉ p.asIdeal) :
    Localization.Away f →+* Localization.AtPrime p.asIdeal :=
  Localization.awayLift
    (algebraMap R (Localization.AtPrime p.asIdeal)) f
    ((IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime p.asIdeal) p.asIdeal f).2 hf)

/- In each of the three cases from the source, some localization away from an
element outside `p` embeds in the localization at `p`. -/
theorem exists_injective_localizationAwayToAtPrime_of_domain
    {R : Type*} [CommRing R] [IsDomain R] (p : PrimeSpectrum R) :
    ∃ f : R, ∃ hf : f ∉ p.asIdeal,
      Function.Injective (localizationAwayToAtPrime p f hf) := by
  refine ⟨(1 : R), p.asIdeal.ne_top_iff_one.mp p.isPrime.ne_top, ?_⟩
  unfold localizationAwayToAtPrime Localization.awayLift IsLocalization.Away.lift
  rw [IsLocalization.lift_injective_iff]
  intro x y
  have hAway : Function.Injective (algebraMap R (Localization.Away (1 : R))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors one_ne_zero)
  have hAtPrime : Function.Injective (algebraMap R (Localization.AtPrime p.asIdeal)) :=
    FaithfulSMul.algebraMap_injective R (Localization.AtPrime p.asIdeal)
  constructor <;> intro h <;> first
    | exact congrArg (algebraMap R (Localization.AtPrime p.asIdeal)) (hAway h)
    | exact congrArg (algebraMap R (Localization.Away (1 : R))) (hAtPrime h)

theorem exists_injective_localizationAwayToAtPrime_of_noetherian
    {R : Type*} [CommRing R] [IsNoetherianRing R] (p : PrimeSpectrum R) :
    ∃ f : R, ∃ hf : f ∉ p.asIdeal,
      Function.Injective (localizationAwayToAtPrime p f hf) := by
  classical
  have hI : (RingHom.ker (algebraMap R (Localization.AtPrime p.asIdeal))).FG :=
    IsNoetherian.noetherian _
  obtain ⟨s, hs_span⟩ := hI
  have hwit : ∀ x ∈ s, ∃ m : p.asIdeal.primeCompl, (m : R) * x = 0 := by
    intro x hx
    have hx0 : algebraMap R (Localization.AtPrime p.asIdeal) x = 0 :=
      RingHom.mem_ker.mp (by
        rw [← hs_span]
        exact Ideal.subset_span hx)
    have hx0' : IsLocalization.mk' (Localization.AtPrime p.asIdeal) x
        (1 : p.asIdeal.primeCompl) = 0 := by
      rw [IsLocalization.mk'_one]
      exact hx0
    exact (IsLocalization.mk'_eq_zero_iff (S := Localization.AtPrime p.asIdeal) x
      (1 : p.asIdeal.primeCompl)).mp hx0'
  have hwit' : ∀ x : s, ∃ m : p.asIdeal.primeCompl, (m : R) * (x : R) = 0 := by
    intro x
    exact hwit x x.property
  choose m hm using hwit'
  let f : R := s.attach.prod (fun x : s => (m x : R))
  have hf : f ∉ p.asIdeal := by
    intro h
    have hprod : ∀ t : Finset s, t.prod (fun x => (m x : R)) ∉ p.asIdeal := by
      intro t
      induction t using Finset.induction_on with
      | empty => exact p.asIdeal.ne_top_iff_one.mp p.isPrime.ne_top
      | @insert x t hx ih =>
          rw [Finset.prod_insert hx]
          intro h
          rcases p.isPrime.mem_or_mem h with h | h
          · exact (m x).property h
          · exact ih h
    apply hprod s.attach
    simpa [f] using h
  have hgen : ∀ x ∈ s, f * x = 0 := by
    intro x hx
    let z : s := ⟨x, hx⟩
    have hdiv : (m z : R) ∣ f := by
      dsimp [f]
      exact Finset.dvd_prod_of_mem (fun x : s => (m x : R)) (by simp [z])
    obtain ⟨c, hc⟩ := hdiv
    calc
      f * x = ((m z : R) * c) * x := by rw [hc]
      _ = (m z : R) * (c * x) := by rw [mul_assoc]
      _ = c * ((m z : R) * (z : R)) := by dsimp [z]; ac_rfl
      _ = 0 := by rw [hm z, mul_zero]
  have hkill : ∀ x ∈ RingHom.ker (algebraMap R (Localization.AtPrime p.asIdeal)),
      f * x = 0 := by
    intro x hx
    rw [← hs_span] at hx
    refine Submodule.span_induction (p := fun z _ => f * z = 0) ?_ ?_ ?_ ?_ hx
    · intro z hz
      exact hgen z hz
    · simp
    · intro x y hx hy hpx hpy
      rw [mul_add, hpx, hpy, add_zero]
    · intro a x hx hpx
      change f * (a * x) = 0
      calc
        f * (a * x) = a * (f * x) := by ac_rfl
        _ = 0 := by rw [hpx, mul_zero]
  refine ⟨f, hf, ?_⟩
  have hcomp :
      (localizationAwayToAtPrime p f hf).comp
          (algebraMap R (Localization.Away f)) =
        algebraMap R (Localization.AtPrime p.asIdeal) := by
    ext r
    simp [localizationAwayToAtPrime]
  rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers f)]
  intro x y
  constructor
  · intro h
    exact congrArg (localizationAwayToAtPrime p f hf) h
  · intro h
    have hxy : algebraMap R (Localization.AtPrime p.asIdeal) x =
        algebraMap R (Localization.AtPrime p.asIdeal) y :=
      (RingHom.congr_fun hcomp x).symm.trans
        (h.trans (RingHom.congr_fun hcomp y))
    have hker : x - y ∈ RingHom.ker (algebraMap R (Localization.AtPrime p.asIdeal)) := by
      rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have hzero : f * (x - y) = 0 := hkill (x - y) hker
    have hzero' :
        IsLocalization.mk' (Localization.Away f) (x - y)
            (1 : (Submonoid.powers f)) = 0 := by
      apply (IsLocalization.mk'_eq_zero_iff
        (S := Localization.Away f) (x - y) (1 : Submonoid.powers f)).2
      exact ⟨⟨f, Submonoid.mem_powers f⟩, hzero⟩
    have hmapzero : algebraMap R (Localization.Away f) (x - y) = 0 := by
      rw [← IsLocalization.mk'_one (M := Submonoid.powers f) (S := Localization.Away f)]
      exact hzero'
    apply sub_eq_zero.mp
    simpa only [map_sub] using hmapzero

theorem exists_injective_localizationAwayToAtPrime_of_reduced
    {R : Type*} [CommRing R] [IsReduced R]
    (hmin : (minimalPrimes R).Finite) (p : PrimeSpectrum R) :
    ∃ f : R, ∃ hf : f ∉ p.asIdeal,
      Function.Injective (localizationAwayToAtPrime p f hf) := by
  classical
  let s : Finset (Ideal R) := hmin.toFinset
  have hs_mem : ∀ q : Ideal R, q ∈ s ↔ q ∈ minimalPrimes R := by
    intro q
    simp [s]
  let a : ∀ q : s, R := fun q =>
    if hq : (q : Ideal R) ≤ p.asIdeal then 1
    else Classical.choose (Set.not_subset.mp hq)
  have ha : ∀ q : s, a q ∉ p.asIdeal := by
    intro q
    dsimp [a]
    split_ifs with hq
    · exact p.asIdeal.ne_top_iff_one.mp p.isPrime.ne_top
    · exact (Classical.choose_spec (Set.not_subset.mp hq)).2
  let f : R := s.attach.prod (fun q : s => a q)
  have hf : f ∉ p.asIdeal := by
    intro h
    have hprod : ∀ t : Finset s, t.prod (fun q => a q) ∉ p.asIdeal := by
      intro t
      induction t using Finset.induction_on with
      | empty => exact p.asIdeal.ne_top_iff_one.mp p.isPrime.ne_top
      | @insert q t hqt ih =>
          rw [Finset.prod_insert hqt]
          intro h
          rcases p.isPrime.mem_or_mem h with h | h
          · exact ha q h
          · exact ih h
    apply hprod s.attach
    simpa [f] using h
  have hkill : ∀ x ∈ RingHom.ker (algebraMap R (Localization.AtPrime p.asIdeal)),
      f * x = 0 := by
    intro x hx
    have hx0 : algebraMap R (Localization.AtPrime p.asIdeal) x = 0 :=
      RingHom.mem_ker.mp hx
    have hx0' : IsLocalization.mk' (Localization.AtPrime p.asIdeal) x
        (1 : p.asIdeal.primeCompl) = 0 := by
      rw [IsLocalization.mk'_one]
      exact hx0
    obtain ⟨m, hmx⟩ :=
      (IsLocalization.mk'_eq_zero_iff (S := Localization.AtPrime p.asIdeal) x
        (1 : p.asIdeal.primeCompl)).mp hx0'
    have hnil : IsNilpotent (f * x) := by
      rw [nilpotent_iff_mem_prime]
      intro I hI
      let _ : I.IsPrime := hI
      obtain ⟨q, hqmin, hqle⟩ :=
        Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := I) bot_le
      have hqs : q ∈ s := hs_mem q |>.mpr hqmin
      let z : s := ⟨q, hqs⟩
      by_cases hqP : q ≤ p.asIdeal
      · have hmq : (m : R) ∉ q := by
          intro hmq
          exact m.property (hqP hmq)
        have hzeroq : (m : R) * x ∈ q := by
          rw [hmx]
          exact q.zero_mem
        have hxq : x ∈ q :=
          (hqmin.isPrime.mem_or_mem hzeroq).resolve_left hmq
        exact hqle (q.mul_mem_left f hxq)
      · have haz : a z ∈ q := by
          dsimp [a]
          rw [dif_neg hqP]
          exact (Classical.choose_spec (Set.not_subset.mp hqP)).1
        have hdiv : a z ∣ f := by
          dsimp [f]
          exact Finset.dvd_prod_of_mem (fun q : s => a q) (by simp [z])
        obtain ⟨c, hc⟩ := hdiv
        have hfq : f ∈ q := by
          rw [hc]
          exact q.mul_mem_right c haz
        exact hqle (by simpa [mul_comm] using q.mul_mem_left x hfq)
    exact isNilpotent_iff_eq_zero.mp hnil
  refine ⟨f, hf, ?_⟩
  have hcomp :
      (localizationAwayToAtPrime p f hf).comp
          (algebraMap R (Localization.Away f)) =
        algebraMap R (Localization.AtPrime p.asIdeal) := by
    ext r
    simp [localizationAwayToAtPrime]
  rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers f)]
  intro x y
  constructor
  · intro h
    exact congrArg (localizationAwayToAtPrime p f hf) h
  · intro h
    have hxy : algebraMap R (Localization.AtPrime p.asIdeal) x =
        algebraMap R (Localization.AtPrime p.asIdeal) y :=
      (RingHom.congr_fun hcomp x).symm.trans
        (h.trans (RingHom.congr_fun hcomp y))
    have hker : x - y ∈ RingHom.ker (algebraMap R (Localization.AtPrime p.asIdeal)) := by
      rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have hzero : f * (x - y) = 0 := hkill (x - y) hker
    have hzero' :
        IsLocalization.mk' (Localization.Away f) (x - y)
            (1 : (Submonoid.powers f)) = 0 := by
      apply (IsLocalization.mk'_eq_zero_iff
        (S := Localization.Away f) (x - y) (1 : Submonoid.powers f)).2
      exact ⟨⟨f, Submonoid.mem_powers f⟩, hzero⟩
    have hmapzero : algebraMap R (Localization.Away f) (x - y) = 0 := by
      rw [← IsLocalization.mk'_one (M := Submonoid.powers f) (S := Localization.Away f)]
      exact hzero'
    apply sub_eq_zero.mp
    simpa only [map_sub] using hmapzero

/-! ## Surjective endomorphisms -/

/- The source calls the conclusion an isomorphism; an explicit ring
equivalence is the corresponding usable Lean interface. -/
theorem surjective_endomorphism_isomorphism
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (f : R →+* R) (hf : Function.Surjective f) :
    ∃ e : R ≃+* R, e.toRingHom = f := by
  let g : Ideal R → Ideal R := fun I => Ideal.comap f I
  have hg : Monotone g := by
    intro I J hIJ
    intro x hx
    change x ∈ Ideal.comap f I at hx
    change x ∈ Ideal.comap f J
    exact hIJ hx
  have hmono : Monotone (fun n : ℕ => (g^[n]) (⊥ : Ideal R)) :=
    Monotone.monotone_iterate_of_le_map hg bot_le
  let F : ℕ →o Ideal R :=
    { toFun := fun n => (g^[n]) (⊥ : Ideal R)
      monotone' := hmono }
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance F
  have hstab : (g^[n]) (⊥ : Ideal R) = (g^[n.succ]) (⊥ : Ideal R) := by
    simpa [F] using hn n.succ (Nat.le_succ n)
  have hcomm : ∀ k (x : R), (f^[k]) (f x) = f ((f^[k]) x) := by
    intro k
    induction k with
    | zero =>
        intro x
        rfl
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply' f k (f x),
          Function.iterate_succ_apply' f k x, ih]
  have hiter : ∀ k (x : R), x ∈ (g^[k]) (⊥ : Ideal R) ↔ (f^[k]) x = 0 := by
    intro k
    induction k with
    | zero =>
        intro x
        simp
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply' g k (⊥ : Ideal R)]
        change f x ∈ (g^[k]) (⊥ : Ideal R) ↔ (f^[k.succ]) x = 0
        rw [ih, Function.iterate_succ_apply' f k x, hcomm]
  have hker : RingHom.ker f = (⊥ : Ideal R) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy⟩ := hf.iterate n x
      have hy' : y ∈ (g^[n.succ]) (⊥ : Ideal R) := by
        apply (hiter n.succ y).2
        rw [Function.iterate_succ_apply' f n y, hy]
        exact RingHom.mem_ker.mp hx
      have hyn : y ∈ (g^[n]) (⊥ : Ideal R) := by
        rw [hstab]
        exact hy'
      have hyn' := (hiter n y).1 hyn
      rw [hy] at hyn'
      exact hyn'
    · exact bot_le
  have hinj : Function.Injective f := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hxy' : x - y ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have hxy'' : x - y ∈ (⊥ : Ideal R) := by
      rw [← hker]
      exact hxy'
    simpa using hxy''
  exact ⟨RingEquiv.ofBijective f ⟨hinj, hf⟩, rfl⟩

end

end Formalization.Books.Algebra.Unit31
