import Formalization.Books.Algebra.Unit09.Localization
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 25: Zerodivisors and total rings of fractions

This file formalizes the definitions and theorem interfaces in the
`Zerodivisors and total rings of fractions` section of `books/algebra.tex`.
The total quotient ring is the canonical localization at `nonZeroDivisors`.
-/

namespace Formalization.Books.Algebra.Unit25

universe u

noncomputable section

/-! ## Zerodivisors and minimal-prime localizations -/

/-- The set of zerodivisors, expressed using Mathlib's canonical submonoid of
non-zero-divisors. -/
def zeroDivisors {R : Type u} [CommRing R] : Set R :=
  {x | x ∉ nonZeroDivisors R}

/-- The minimal prime ideals, packaged as points of the prime spectrum. -/
abbrev MinimalPrimeSpectrum (R : Type u) [CommRing R] :=
  {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R}

/-- The product of the localizations at all minimal primes. -/
abbrev minimalPrimeLocalizations (R : Type u) [CommRing R] :=
  ∀ p : MinimalPrimeSpectrum R, Localization.AtPrime p.1.asIdeal

/-- The canonical map from a ring to the product of its minimal-prime
localizations. -/
def mapToMinimalPrimeLocalizations {R : Type u} [CommRing R] :
    R →+* minimalPrimeLocalizations R :=
  RingHom.pi fun p => algebraMap R (Localization.AtPrime p.1.asIdeal)

/-- The image of the canonical map is a subring of the product. -/
def minimalPrimeLocalizationRange {R : Type u} [CommRing R] :
    Subring (minimalPrimeLocalizations R) :=
  (mapToMinimalPrimeLocalizations (R := R)).range

/-- Every element of the maximal ideal of the localization at a minimal prime
is nilpotent. -/
theorem isNilpotent_mem_maximalIdeal_localizationAt_minimalPrime
    {R : Type u} [CommRing R] (p : MinimalPrimeSpectrum R)
    {x : Localization.AtPrime p.1.asIdeal}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p.1.asIdeal)) :
    IsNilpotent x := by
  have hsub : Subsingleton (PrimeSpectrum (Localization.AtPrime p.1.asIdeal)) :=
    IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes
      p.1.asIdeal p.2 (Localization.AtPrime p.1.asIdeal)
  letI : Subsingleton (PrimeSpectrum (Localization.AtPrime p.1.asIdeal)) := hsub
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  let z : PrimeSpectrum (Localization.AtPrime p.1.asIdeal) := ⟨J, hJ⟩
  have hEq : z = (⟨IsLocalRing.maximalIdeal (Localization.AtPrime p.1.asIdeal), inferInstance⟩ :
      PrimeSpectrum (Localization.AtPrime p.1.asIdeal)) :=
    Subsingleton.elim _ _
  change x ∈ z.asIdeal
  rw [hEq]
  exact hx

/-- If the ring is reduced, each factor in the minimal-prime localization
product is a field. -/
theorem isField_localizationAt_minimalPrime_of_isReduced
    {R : Type u} [CommRing R] [IsReduced R] (p : MinimalPrimeSpectrum R) :
    IsField (Localization.AtPrime p.1.asIdeal) := by
  apply (IsLocalRing.isField_iff_maximalIdeal_eq).2
  apply le_antisymm
  · intro x hx
    exact isNilpotent_iff_eq_zero.mp
      (isNilpotent_mem_maximalIdeal_localizationAt_minimalPrime p hx)
  · exact bot_le

private theorem mapToMinimalPrimeLocalizations_injective_aux
    {R : Type u} [CommRing R] [IsReduced R] :
    Function.Injective (mapToMinimalPrimeLocalizations (R := R)) := by
  intro x y hxy
  have hnil : IsNilpotent (x - y) := by
    rw [nilpotent_iff_mem_prime]
    intro I hI
    letI : I.IsPrime := hI
    obtain ⟨p, hp, hp_le⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := I) bot_le
    letI : p.IsPrime := hp.isPrime
    let q : MinimalPrimeSpectrum R := ⟨⟨p, hp.isPrime⟩, hp⟩
    apply hp_le
    have hcomponent :
        algebraMap R (Localization.AtPrime p) x =
          algebraMap R (Localization.AtPrime p) y := by
      have := congrFun hxy q
      simpa [mapToMinimalPrimeLocalizations] using this
    have hzero : algebraMap R (Localization.AtPrime p) (x - y) = 0 := by
      rw [map_sub, hcomponent, sub_self]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime p) p (x - y)).mp
    rw [hzero]
    exact (IsLocalRing.maximalIdeal (Localization.AtPrime p)).zero_mem
  exact sub_eq_zero.mp (isNilpotent_iff_eq_zero.mp hnil)

/-- A reduced ring is isomorphic to the subring given by its canonical map
into the product of the localizations at its minimal primes. -/
theorem reduced_ring_equiv_minimalPrimeLocalizationRange
    {R : Type u} [CommRing R] [IsReduced R] :
    Nonempty (R ≃+* minimalPrimeLocalizationRange (R := R)) := by
  exact ⟨RingEquiv.ofBijective
    (mapToMinimalPrimeLocalizations (R := R)).rangeRestrict
    ⟨(by
        intro x y hxy
        apply mapToMinimalPrimeLocalizations_injective_aux
        exact congrArg Subtype.val hxy),
      RingHom.rangeRestrict_surjective _⟩⟩

/-- The canonical map into the product of the localizations at the minimal
primes is injective for a reduced ring. -/
theorem mapToMinimalPrimeLocalizations_injective
    {R : Type u} [CommRing R] [IsReduced R] :
    Function.Injective (mapToMinimalPrimeLocalizations (R := R)) := by
  exact mapToMinimalPrimeLocalizations_injective_aux

/-- In a reduced ring, the union of the minimal primes is exactly the set of
zerodivisors. -/
theorem iUnion_minimalPrimeSpectrum_eq_zeroDivisors
    {R : Type u} [CommRing R] [IsReduced R] :
    (⋃ p : MinimalPrimeSpectrum R, (p.1.asIdeal : Set R)) =
      zeroDivisors (R := R) := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    change x ∉ nonZeroDivisors R
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hxp p.2
  · intro hx
    change x ∉ nonZeroDivisors R at hx
    rcases notMem_nonZeroDivisors_iff_right.mp hx with ⟨y, hyx, hyne⟩
    have hex : ∃ p : MinimalPrimeSpectrum R, y ∉ p.1.asIdeal := by
      by_contra hnone
      have hall : ∀ p : MinimalPrimeSpectrum R, y ∈ p.1.asIdeal := by
        intro p
        by_contra hpy
        exact hnone ⟨p, hpy⟩
      have hnil : IsNilpotent y := by
        rw [nilpotent_iff_mem_prime]
        intro I hI
        letI : I.IsPrime := hI
        obtain ⟨p, hp, hpI⟩ :=
          Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := I) bot_le
        let q : MinimalPrimeSpectrum R := ⟨⟨p, hp.isPrime⟩, hp⟩
        exact hpI (hall q)
      exact hyne (isNilpotent_iff_eq_zero.mp hnil)
    obtain ⟨p, hyp⟩ := hex
    letI : p.1.asIdeal.IsPrime := p.1.2
    have hprod : y * x ∈ p.1.asIdeal := by
      rw [hyx]
      exact p.1.asIdeal.zero_mem
    have hxp : x ∈ p.1.asIdeal :=
      (p.1.2.mem_or_mem hprod).resolve_left hyp
    exact Set.mem_iUnion.mpr ⟨p, hxp⟩

/-! ## Total rings of fractions -/

/-- Localizing a ring at a multiplicative set of non-zero-divisors does not
change its total quotient ring, up to ring equivalence. -/
theorem totalQuotientRing_equiv_localization
    {R : Type u} [CommRing R] (S : Submonoid R)
    (hS : S ≤ nonZeroDivisors R) :
    Nonempty (Formalization.Books.Algebra.Unit09.totalQuotientRing R ≃+*
      Formalization.Books.Algebra.Unit09.totalQuotientRing (Localization S)) := by
  letI : Algebra (Localization S)
      (Formalization.Books.Algebra.Unit09.totalQuotientRing R) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization S)
      (Formalization.Books.Algebra.Unit09.totalQuotientRing R)
      S (nonZeroDivisors R) hS
  letI : IsScalarTower R (Localization S)
      (Formalization.Books.Algebra.Unit09.totalQuotientRing R) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization S)
      (Formalization.Books.Algebra.Unit09.totalQuotientRing R)
      S (nonZeroDivisors R) hS
  letI : IsFractionRing (Localization S)
      (Formalization.Books.Algebra.Unit09.totalQuotientRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization S
      (Localization S)
      (Formalization.Books.Algebra.Unit09.totalQuotientRing R) hS
  exact ⟨(IsFractionRing.ringEquivOfRingEquiv
    (RingEquiv.refl (Localization S)) :
      Formalization.Books.Algebra.Unit09.totalQuotientRing (Localization S) ≃+*
        Formalization.Books.Algebra.Unit09.totalQuotientRing R).symm⟩

/-- The total quotient ring is unchanged by forming the total quotient ring
again. -/
theorem totalQuotientRing_equiv_self {R : Type u} [CommRing R] :
    Nonempty (Formalization.Books.Algebra.Unit09.totalQuotientRing R ≃+*
      Formalization.Books.Algebra.Unit09.totalQuotientRing
        (Formalization.Books.Algebra.Unit09.totalQuotientRing R)) := by
  simpa using
    (totalQuotientRing_equiv_localization (R := R)
      (nonZeroDivisors R) le_rfl)

/-- If the distinct finitely many minimal primes are `q i` and their union is
the set of zerodivisors, the total quotient ring is their product of
localizations. -/
theorem totalQuotientRing_equiv_pi_minimalPrime_localizations
    {R : Type u} [CommRing R] (n : ℕ) (q : Fin n → PrimeSpectrum R)
    (hq : Set.range (fun i : Fin n => (q i).asIdeal) = minimalPrimes R)
    (hq_injective : Function.Injective q)
    (hz : (⋃ i : Fin n, ((q i).asIdeal : Set R)) = zeroDivisors (R := R)) :
    Nonempty (Formalization.Books.Algebra.Unit09.totalQuotientRing R ≃+*
      (∀ i : Fin n, Localization.AtPrime (q i).asIdeal)) := by
  classical
  cases n with
  | zero =>
      have hmin : minimalPrimes R = ∅ := by
        rw [← hq]
        simp
      have hR : Subsingleton R := by
        apply not_nontrivial_iff_subsingleton.mp
        intro hR
        letI : Nontrivial R := hR
        obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
        simpa [hmin] using hp
      letI : Subsingleton R := hR
      letI : Subsingleton (Formalization.Books.Algebra.Unit09.totalQuotientRing R) := inferInstance
      let f : Formalization.Books.Algebra.Unit09.totalQuotientRing R →+*
          (∀ i : Fin 0, Localization.AtPrime (q i).asIdeal) :=
        { toFun := fun _ => 0
          map_one' := Subsingleton.elim _ _
          map_mul' := fun _ _ => Subsingleton.elim _ _
          map_zero' := Subsingleton.elim _ _
          map_add' := fun _ _ => Subsingleton.elim _ _ }
      exact ⟨RingEquiv.ofBijective f ⟨by
        intro x y hxy
        exact Subsingleton.elim _ _, by
        intro z
        exact ⟨0, Subsingleton.elim _ _⟩⟩⟩
  | succ n =>
      let A := Formalization.Books.Algebra.Unit09.totalQuotientRing R
      let qi : Fin (Nat.succ n) → Ideal R := fun i => (q i).asIdeal
      have hqi : ∀ i, qi i ∈ minimalPrimes R := by
        intro i
        rw [← hq]
        exact ⟨i, rfl⟩
      have hqdisj : ∀ i, Disjoint (nonZeroDivisors R : Set R) (qi i) := by
        intro i
        exact (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes (hqi i)).symm
      let r : Fin (Nat.succ n) → PrimeSpectrum A := fun i =>
        ⟨(qi i).map (algebraMap R A),
          IsLocalization.isPrime_of_isPrime_disjoint
            (nonZeroDivisors R) A (qi i) (hqi i).isPrime (hqdisj i)⟩
      have r_under : ∀ i, (r i).asIdeal.under R = qi i := by
        intro i
        exact IsLocalization.under_map_of_isPrime_disjoint
          (nonZeroDivisors R) A (hqi i).isPrime (hqdisj i)
      have r_surj : Function.Surjective r := by
        intro p
        let P := p.asIdeal.under R
        have hPprime : P.IsPrime :=
          (IsLocalization.isPrime_iff_isPrime_disjoint
            (nonZeroDivisors R) A p.asIdeal).mp p.2 |>.1
        have hPdisj : Disjoint (nonZeroDivisors R : Set R) P :=
          (IsLocalization.isPrime_iff_isPrime_disjoint
            (nonZeroDivisors R) A p.asIdeal).mp p.2 |>.2
        have hPsub : (P : Set R) ⊆ ⋃ i, qi i := by
          intro x hx
          have hxreg : x ∉ nonZeroDivisors R := by
            intro hxreg
            exact Set.disjoint_left.mp hPdisj hxreg hx
          change x ∈ ⋃ i, ((q i).asIdeal : Set R)
          rw [hz]
          exact hxreg
        have hPsub' : (P : Set R) ⊆
            ⋃ i ∈ (↑(Finset.univ : Finset (Fin (Nat.succ n))) : Set _), qi i := by
          simpa using hPsub
        obtain ⟨i, hi, hPqi⟩ :=
          (Ideal.subset_union_prime (s := Finset.univ) 0 0
            (fun j _ _ _ => (q j).2)).mp hPsub'
        have hqmin : qi i ≤ P := by
          obtain ⟨p', hp', hp'le⟩ :=
            Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := P) bot_le
          have hp'eq : p' = qi i :=
            (minimalPrimes_eq_minimals (R := R) ▸ hqi i).eq_of_le
              hp'.isPrime (by exact hp'le.trans hPqi)
          exact hp'eq ▸ hp'le
        have hPqi_eq : P = qi i := le_antisymm hPqi hqmin
        refine ⟨i, ?_⟩
        apply PrimeSpectrum.ext
        dsimp [r]
        rw [← IsLocalization.map_under (nonZeroDivisors R) A p.asIdeal]
        change Ideal.map (algebraMap R A) (qi i) = Ideal.map (algebraMap R A) P
        rw [hPqi_eq]
      have r_inj : Function.Injective r := by
        intro i j hij
        apply hq_injective
        apply PrimeSpectrum.ext
        have hunder := congrArg
          (fun z : PrimeSpectrum A => z.asIdeal.under R) hij
        rw [r_under i, r_under j] at hunder
        exact hunder
      let e : Fin (Nat.succ n) ≃ PrimeSpectrum A :=
        Equiv.ofBijective r ⟨r_inj, r_surj⟩
      let e_i (i : Fin (Nat.succ n)) :
          Localization.AtPrime (qi i) ≃ₐ[R]
            @Localization.AtPrime A _ (r i).asIdeal (r i).2 := by
        letI : (r i).asIdeal.IsPrime := (r i).2
        have hcomap : Ideal.comap (algebraMap R A) (r i).asIdeal = qi i := by
          exact r_under i
        letI : IsLocalization (qi i).primeCompl
            (@Localization.AtPrime A _ (r i).asIdeal (r i).2) := by
          have hloc :=
            IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
              (M := nonZeroDivisors R) (p := (r i).asIdeal)
              (T := @Localization.AtPrime A _ (r i).asIdeal (r i).2)
          have hprime : (Ideal.comap (algebraMap R A) (r i).asIdeal).primeCompl =
              (qi i).primeCompl := by
            ext x
            simp only [Ideal.mem_primeCompl_iff]
            rw [hcomap]
          change IsLocalization
            ((Ideal.comap (algebraMap R A) (r i).asIdeal).primeCompl)
            (@Localization.AtPrime A _ (r i).asIdeal (r i).2) at hloc
          rw [hprime] at hloc
          exact hloc
        exact IsLocalization.algEquiv (qi i).primeCompl _ _
      let E₁ :
          (∀ i : Fin (Nat.succ n),
            @Localization.AtPrime A _ (r i).asIdeal (r i).2) ≃ₐ[A]
            PrimeSpectrum.PiLocalization A :=
        AlgEquiv.piCongrLeft A (fun p : PrimeSpectrum A =>
          @Localization.AtPrime A _ p.asIdeal p.2) e
      let E₂ :
          (∀ i : Fin (Nat.succ n),
            @Localization.AtPrime A _ (r i).asIdeal (r i).2) ≃ₐ[R]
            (∀ i : Fin (Nat.succ n), Localization.AtPrime (qi i)) :=
        AlgEquiv.piCongrRight (fun i => (e_i i).symm)
      let E :
          (∀ i : Fin (Nat.succ n), Localization.AtPrime (qi i)) ≃+*
            PrimeSpectrum.PiLocalization A :=
        (E₂.symm.toRingEquiv).trans E₁.toRingEquiv
      letI : Finite (PrimeSpectrum A) := Finite.of_surjective r r_surj
      have hmax : ∀ J : Ideal A, J.IsPrime → J.IsMaximal := by
        intro J hJ
        let pJ : PrimeSpectrum A := ⟨J, hJ⟩
        let P : Ideal R := pJ.asIdeal.under R
        have hPprime : P.IsPrime :=
          (IsLocalization.isPrime_iff_isPrime_disjoint
            (nonZeroDivisors R) A pJ.asIdeal).mp pJ.2 |>.1
        have hPdisj : Disjoint (nonZeroDivisors R : Set R) (P : Set R) :=
          (IsLocalization.isPrime_iff_isPrime_disjoint
            (nonZeroDivisors R) A pJ.asIdeal).mp pJ.2 |>.2
        have hPsub : (P : Set R) ⊆ ⋃ i, qi i := by
          intro x hx
          have hxreg : x ∉ nonZeroDivisors R := by
            intro hxreg
            exact Set.disjoint_left.mp hPdisj hxreg hx
          change x ∈ ⋃ i, ((q i).asIdeal : Set R)
          rw [hz]
          exact hxreg
        have hPsub' : (P : Set R) ⊆
            ⋃ i ∈ (↑(Finset.univ : Finset (Fin (Nat.succ n))) : Set _), qi i := by
          simpa using hPsub
        obtain ⟨i, hi, hPqi⟩ :=
          (Ideal.subset_union_prime (s := Finset.univ) 0 0
            (fun j _ _ _ => (q j).2)).mp hPsub'
        have hqmin : qi i ≤ P := by
          obtain ⟨p', hp', hp'le⟩ :=
            Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := P) bot_le
          have hp'eq : p' = qi i :=
            (minimalPrimes_eq_minimals (R := R) ▸ hqi i).eq_of_le
              hp'.isPrime (by exact hp'le.trans hPqi)
          exact hp'eq ▸ hp'le
        have hPqi_eq : P = qi i := le_antisymm hPqi hqmin
        have hJ_eq : J = (r i).asIdeal := by
          rw [← IsLocalization.map_under (nonZeroDivisors R) A J]
          change Ideal.map (algebraMap R A) P = Ideal.map (algebraMap R A) (qi i)
          rw [hPqi_eq]
        rw [hJ_eq]
        rw [Ideal.isMaximal_iff]
        constructor
        · exact (r i).asIdeal.ne_top_iff_one.mp (r i).2.ne_top
        · intro K x hriK hxri hxK
          by_contra h1K
          obtain ⟨M, hM, hKM⟩ := Ideal.exists_le_maximal K
            (K.ne_top_iff_one.mpr h1K)
          let pM : PrimeSpectrum A := ⟨M, hM.isPrime⟩
          obtain ⟨j, hj⟩ := r_surj pM
          have hM_eq : M = (r j).asIdeal := (congrArg PrimeSpectrum.asIdeal hj).symm
          have hrij : (r i).asIdeal ≤ (r j).asIdeal :=
            hriK.trans (hKM.trans_eq hM_eq)
          have hqij : qi i ≤ qi j := by
            rw [← r_under i, ← r_under j]
            exact Ideal.comap_mono hrij
          have hqeq : qi j = qi i :=
            ((minimalPrimes_eq_minimals (R := R) ▸ hqi j).eq_of_le
              (hqi i).isPrime hqij).symm
          have hreq : (r j).asIdeal = (r i).asIdeal := by
            change Ideal.map (algebraMap R A) (qi j) =
              Ideal.map (algebraMap R A) (qi i)
            exact congrArg (Ideal.map (algebraMap R A)) hqeq
          have hKle : K ≤ (r i).asIdeal := hKM.trans_eq (hM_eq.trans hreq)
          have hKeq : K = (r i).asIdeal := le_antisymm hKle hriK
          exact hxri (hKeq ▸ hxK)
      letI : Ring.KrullDimLE 0 A := Ring.KrullDimLE.mk₀ hmax
      let : DiscreteTopology (PrimeSpectrum A) :=
        (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero).2
          ⟨inferInstance, inferInstance⟩
      exact ⟨(PrimeSpectrum.toPiLocalizationEquiv A).toRingEquiv.trans E.symm⟩

end

end Formalization.Books.Algebra.Unit25
