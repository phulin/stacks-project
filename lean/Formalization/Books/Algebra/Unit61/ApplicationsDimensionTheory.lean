import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit35.JacobsonRings
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Jacobson.Artinian

/-!
# Commutative Algebra, Chapter 61: Applications of dimension theory

The source's dimension-zero and Jacobson criteria are stated using Mathlib's
canonical Krull dimension, spectra, finite-dimensional modules, Artinian and
Jacobson predicates, and discrete topologies.  The fourth condition in the
finite-type equivalence is represented by condition (5) of the earlier
"only minimal primes" characterization: there are no nontrivial inclusions
between prime ideals.
-/

namespace Formalization.Books.Algebra.Unit61

open Set

universe u

noncomputable section

private theorem ringKrullDim_quotient_unit61
    {R : Type u} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) =
      Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
  rw [ringKrullDim,
    Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]

private theorem finite_primeSpectrum_of_isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Finite (PrimeSpectrum R) := by
  classical
  obtain ⟨_, P, hP, hPuniq⟩ :=
    (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp
      (inferInstance : IsDiscreteValuationRing R)
  let f : PrimeSpectrum R → Bool :=
    fun p => if p.asIdeal = (⊥ : Ideal R) then false else true
  apply Finite.of_injective f
  intro p q h
  apply PrimeSpectrum.ext
  by_cases hp : p.asIdeal = (⊥ : Ideal R)
  · have hq : q.asIdeal = (⊥ : Ideal R) := by
      by_contra hq
      have hne : f p ≠ f q := by
        change (if p.asIdeal = (⊥ : Ideal R) then false else true) ≠
          (if q.asIdeal = (⊥ : Ideal R) then false else true)
        rw [if_pos hp, if_neg hq]
        decide
      exact hne h
    exact hp.trans hq.symm
  · have hq : q.asIdeal ≠ (⊥ : Ideal R) := by
      intro hq
      have hne : f p ≠ f q := by
        change (if p.asIdeal = (⊥ : Ideal R) then false else true) ≠
          (if q.asIdeal = (⊥ : Ideal R) then false else true)
        rw [if_neg hp, if_pos hq]
        decide
      exact hne h
    exact (hPuniq _ (And.intro hp p.2)).trans (hPuniq _ (And.intro hq q.2)).symm

/-! ## Infinite spectra and finite-prime rings -/

/-- A nonempty open subset of the spectrum of a Noetherian local domain of
dimension at least two is infinite. -/
theorem nonempty_open_primeSpectrum_infinite_of_local_noetherian_domain_dim_ge_two
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] (hdim : 2 ≤ ringKrullDim R)
    {U : Set (PrimeSpectrum R)} (hUopen : IsOpen U)
    (hUnonempty : U.Nonempty) :
    U.Infinite := by
  classical
  obtain ⟨p, hp⟩ := hUnonempty
  have hbot : ringKrullDim R ≠ ⊥ := by
    change Order.krullDim (PrimeSpectrum R) ≠ ⊥
    exact Order.krullDim_ne_bot_iff.mpr ⟨p⟩
  have hle := Formalization.Books.Algebra.Unit60.ringKrullDim_le_maximalIdeal_spanFinrank R
  have htop : ringKrullDim R ≠ ⊤ := by
    intro h
    have hlt : ringKrullDim R < ⊤ := by
      exact lt_of_le_of_lt hle
        (WithBot.coe_lt_coe.mpr
          (WithTop.coe_lt_top (IsLocalRing.maximalIdeal R).spanFinrank))
    exact (ne_of_lt hlt) h
  let dInf : ℕ∞ := (ringKrullDim R).unbot hbot
  have hdInf : (dInf : WithBot ℕ∞) = ringKrullDim R :=
    WithBot.coe_unbot _ _
  have htopInf : dInf ≠ ⊤ := by
    intro hd
    apply htop
    rw [← hdInf, hd]
    rfl
  obtain ⟨d₀, hd₀⟩ := WithTop.ne_top_iff_exists.mp htopInf
  have hdimNat : ringKrullDim R = (d₀ : ℕ) := by
    calc
      ringKrullDim R = (dInf : WithBot ℕ∞) := hdInf.symm
      _ = (d₀ : WithBot ℕ∞) := by rw [← hd₀]; exact WithBot.coe_natCast d₀
  have hd₀ge2 : 2 ≤ d₀ := by
    rw [hdimNat] at hdim
    exact_mod_cast hdim
  by_contra hUinf
  have hUfin : U.Finite := not_not.mp hUinf
  let p₀ : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hp₀U : p₀ ∈ U := by
    apply hUopen.stableUnderGeneralization (show p₀ ⤳ p from by
      rw [← PrimeSpectrum.le_iff_specializes]
      exact bot_le)
    exact hp
  obtain ⟨_, ⟨x, rfl⟩, hpx, hxU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hUopen
  have hxnot : x ∉ p.asIdeal := (PrimeSpectrum.mem_basicOpen x p).mp hpx
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hxnot
    rw [hx0]
    exact Ideal.zero_mem _
  let s : Finset (PrimeSpectrum R) := hUfin.toFinset.erase p₀
  let ι := {q : PrimeSpectrum R // q ∈ s}
  have hqchoice (q : ι) : ∃ a : R, a ∈ q.1.asIdeal ∧ a ≠ 0 := by
    have hqmem : q.1 ∈ hUfin.toFinset.erase p₀ := by
      change q.1 ∈ s
      exact q.2
    have hqne : q.1 ≠ p₀ := (Finset.mem_erase.mp hqmem).1
    have hqbot : q.1.asIdeal ≠ (⊥ : Ideal R) := by
      intro hqbot
      apply hqne
      apply PrimeSpectrum.ext
      exact hqbot
    exact Submodule.exists_mem_ne_zero_of_ne_bot hqbot
  choose g hgmem hgzero using hqchoice
  let z : R := x * ∏ q : ι, g q
  have hzprod : (∏ q : ι, g q) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => hgzero q)
  have hz0 : z ≠ 0 := by
    exact mul_ne_zero hx0 hzprod
  have hzU : (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum R)) ⊆ U := by
    intro q hq
    apply hxU
    apply (PrimeSpectrum.mem_basicOpen x q).mpr
    intro hxq
    apply (PrimeSpectrum.mem_basicOpen z q).mp hq
    change x * ∏ q : ι, g q ∈ q.asIdeal
    exact q.asIdeal.mul_mem_right _ hxq
  have hzsingle : (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum R)) = {p₀} := by
    ext q
    constructor
    · intro hq
      have hqU : q ∈ U := hzU hq
      by_cases hqeq : q = p₀
      · exact Set.mem_singleton_iff.mpr hqeq
      · have hqfin : q ∈ hUfin.toFinset := hUfin.mem_toFinset.mpr hqU
        let q' : ι := ⟨q, by simpa [s] using (Finset.mem_erase.mpr ⟨hqeq, hqfin⟩)⟩
        have hqprod : (∏ r : ι, g r) ∈ q.asIdeal := by
          simpa using Ideal.prod_mem q.asIdeal (Finset.mem_univ q') (hgmem q')
        have hzq : z ∈ q.asIdeal := by
          change x * ∏ r : ι, g r ∈ q.asIdeal
          exact q.asIdeal.mul_mem_left _ hqprod
        exact False.elim ((PrimeSpectrum.mem_basicOpen z q).mp hq hzq)
    · intro hq
      have hqeq : q = p₀ := Set.mem_singleton_iff.mp hq
      subst q
      apply (PrimeSpectrum.mem_basicOpen z p₀).mpr
      simpa [p₀] using hz0
  have hzmax : z ∈ IsLocalRing.maximalIdeal R := by
    let m : PrimeSpectrum R :=
      ⟨IsLocalRing.maximalIdeal R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩
    have hp₀ne : p₀ ≠ m := by
      intro hp₀max
      have hmaxbot : IsLocalRing.maximalIdeal R = (⊥ : Ideal R) := by
        have h := congrArg PrimeSpectrum.asIdeal hp₀max
        simpa [p₀, m] using h.symm
      have hfield : IsField R :=
        IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmaxbot
      have hdimzero : ringKrullDim R = 0 := ringKrullDim_eq_zero_of_isField hfield
      rw [hdimzero] at hdim
      have hdimNat' : (2 : ℕ) ≤ 0 := by exact_mod_cast hdim
      omega
    by_contra hzmax
    have hunit : IsUnit z := (IsLocalRing.notMem_maximalIdeal).mp hzmax
    have htopopen : PrimeSpectrum.basicOpen z = ⊤ := by
      ext q
      change (z ∉ q.asIdeal) ↔ True
      constructor
      · intro _
        trivial
      · intro _ hzq
        exact q.2.ne_top (q.asIdeal.eq_top_of_isUnit_mem hzq hunit)
    have hmaxmem : m ∈ ({p₀} : Set _ ) := by
      rw [← hzsingle, htopopen]
      trivial
    exact hp₀ne (Set.mem_singleton_iff.mp hmaxmem).symm
  let I : Ideal R := Ideal.span ({z} : Set R)
  have hzreg : z ∈ nonZeroDivisors R := (mem_nonZeroDivisors_iff_ne_zero).mpr hz0
  have hdimq : ringKrullDim (R ⧸ I) + 1 = ringKrullDim R := by
    dsimp [I]
    exact (Formalization.Books.Algebra.Unit60.one_equation_dimension_eq_of_nonzerodivisor
      R inferInstance z hzmax hzreg).symm
  have hqbot : ringKrullDim (R ⧸ I) ≠ ⊥ := by
    intro hq
    rw [hq, hdimNat] at hdimq
    have hbad : (⊥ : WithBot ℕ∞) = (d₀ : WithBot ℕ∞) := by
      simp at hdimq
    exact (WithBot.bot_ne_coe) hbad
  let qInf : ℕ∞ := (ringKrullDim (R ⧸ I)).unbot hqbot
  have hqInf : (qInf : WithBot ℕ∞) = ringKrullDim (R ⧸ I) :=
    WithBot.coe_unbot _ _
  have hqInfTop : qInf ≠ ⊤ := by
    intro hqInfTop
    apply htop
    calc
      ringKrullDim R = ringKrullDim (R ⧸ I) + 1 := hdimq.symm
      _ = (qInf : WithBot ℕ∞) + 1 := by rw [hqInf]
      _ = ⊤ := by
        rw [hqInfTop, ← WithBot.coe_one, ← WithBot.coe_add]
        exact congrArg (fun q : ℕ∞ => (q : WithBot ℕ∞))
          (WithTop.top_add (1 : ℕ∞))
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hqInfTop
  have hqInfNat : qInf = (n : ℕ) := by
    exact hn.symm
  have hdimqInf : qInf + 1 = (d₀ : ℕ∞) := by
    have hdimq' : (qInf : WithBot ℕ∞) + 1 = (d₀ : WithBot ℕ∞) := by
      calc
        (qInf : WithBot ℕ∞) + 1 = ringKrullDim (R ⧸ I) + 1 := by rw [hqInf]
        _ = ringKrullDim R := hdimq
        _ = (d₀ : WithBot ℕ∞) := hdimNat
    exact WithBot.coe_eq_coe.mp (by simpa using hdimq')
  have hdimqNat' : n + 1 = d₀ := by
    rw [hqInfNat] at hdimqInf
    exact_mod_cast hdimqInf
  have hdimqNat : ringKrullDim (R ⧸ I) = (d₀ - 1 : ℕ) := by
    calc
      ringKrullDim (R ⧸ I) = (qInf : WithBot ℕ∞) := hqInf.symm
      _ = (n : WithBot ℕ∞) := by
        calc
          (qInf : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) :=
            congrArg (fun q : ℕ∞ => (q : WithBot ℕ∞)) hn.symm
          _ = (n : WithBot ℕ∞) := WithBot.coe_natCast n
      _ = ((d₀ - 1 : ℕ) : WithBot ℕ∞) := by
        rw [show n = d₀ - 1 by omega]
  have hqnontriv : Nontrivial (R ⧸ I) := by
    have hqspec : Nonempty (PrimeSpectrum (R ⧸ I)) := by
      apply Order.krullDim_ne_bot_iff.mp
      change ringKrullDim (R ⧸ I) ≠ ⊥
      exact hqbot
    exact PrimeSpectrum.nonempty_iff_nontrivial.mp hqspec
  let hlocal : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let hlocalhom : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hparamq :=
    letI : Nontrivial (R ⧸ I) := hqnontriv
    letI : IsLocalRing (R ⧸ I) := hlocal
    letI : IsLocalHom (Ideal.Quotient.mk I) := hlocalhom
    ((Formalization.Books.Algebra.Unit60.local_dimension_characterization
      (R ⧸ I) inferInstance (d₀ - 1)).out 0 2).mp hdimqNat
  obtain ⟨w, hw, hdefq⟩ := hparamq.1
  choose v hv using fun i => Ideal.Quotient.mk_surjective (w i)
  let J : Ideal R := Ideal.span (Set.range v)
  have hmap : Ideal.map (Ideal.Quotient.mk I) J =
      Ideal.span (Set.range w) := by
    dsimp [J]
    rw [Ideal.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hv i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, hv i⟩
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) :=
    Ideal.Quotient.mk_surjective
  have hcomap : Ideal.comap (Ideal.Quotient.mk I) (Ideal.span (Set.range w)) =
      I ⊔ J := by
    rw [← hmap, Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) hsurj,
      ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_comm]
  have hdefK : Unit59.IsIdealOfDefinition R (I ⊔ J) :=
    letI : IsLocalRing (R ⧸ I) := hlocal
    letI : IsLocalHom (Ideal.Quotient.mk I) := hlocalhom
    by
      unfold Unit59.IsIdealOfDefinition
      rw [← hcomap, ← Ideal.comap_radical, hdefq,
        IsLocalRing.maximalIdeal_comap]
  have hlen : (d₀ - 1) + 1 = d₀ := by omega
  have htail : (d₀ - 2) + 1 = d₀ - 1 := by omega
  let vzero : R := v ⟨0, by omega⟩
  let a : Fin d₀ → R := fun i =>
    Fin.cases vzero
      (fun k => Fin.cases z (fun l => v (Fin.cast htail l.succ)) (Fin.cast htail.symm k))
      (Fin.cast hlen.symm i)
  have hArange : Set.range a = insert z (Set.range v) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      let j : Fin ((d₀ - 1) + 1) := Fin.cast hlen.symm i
      change Fin.cases vzero
        (fun k => Fin.cases z (fun l => v (Fin.cast htail l.succ))
          (Fin.cast htail.symm k)) j ∈
        insert z (Set.range v)
      refine Fin.cases ?_ (fun k => ?_) j
      · exact Set.mem_insert_iff.mpr
          (Or.inr ⟨(⟨0, by omega⟩ : Fin (d₀ - 1)), by rfl⟩)
      · let k' : Fin ((d₀ - 2) + 1) := Fin.cast htail.symm k
        change Fin.cases z (fun l => v (Fin.cast htail l.succ)) k' ∈
          insert z (Set.range v)
        refine Fin.cases ?_ (fun l => ?_) k'
        · exact Set.mem_insert_iff.mpr (Or.inl rfl)
        · exact Set.mem_insert_iff.mpr
            (Or.inr ⟨Fin.cast htail l.succ, rfl⟩)
    · intro hr
      rcases Set.mem_insert_iff.mp hr with rfl | ⟨k, rfl⟩
      · let zeroTail : Fin (d₀ - 1) := ⟨0, by omega⟩
        have hzero : Fin.cast hlen.symm (Fin.cast hlen (Fin.succ zeroTail)) =
            Fin.succ zeroTail := by
          apply Fin.ext
          simp
        have hzidx : Fin.cast htail.symm zeroTail = 0 := by
          apply Fin.ext
          simp [zeroTail]
        exact ⟨Fin.cast hlen (Fin.succ zeroTail), by simp [a, hzero, hzidx]
          ⟩
      · by_cases hk0 : k.val = 0
        · have hk0' : k = (⟨0, by omega⟩ : Fin (d₀ - 1)) := by
            apply Fin.ext
            simpa using hk0
          rw [hk0']
          exact ⟨Fin.cast hlen 0, by simp [a, vzero]
            ⟩
        · let l : Fin (d₀ - 2) := ⟨k.val - 1, by omega⟩
          have hkl : k = Fin.cast htail l.succ := by
            apply Fin.ext
            dsimp [l]
            omega
          rw [hkl]
          exact ⟨Fin.cast hlen (Fin.succ (Fin.cast htail l.succ)), by
            simp [a]
            ⟩
  have hvmax : ∀ k, v k ∈ IsLocalRing.maximalIdeal R := by
    intro k
    have hk :=
      letI : IsLocalRing (R ⧸ I) := hlocal
      letI : IsLocalHom (Ideal.Quotient.mk I) := hlocalhom
      (show (Ideal.Quotient.mk I) (v k) ∈
          IsLocalRing.maximalIdeal (R ⧸ I) from by
        rw [hv k]
        exact hw k)
    have hk' :=
      letI : IsLocalRing (R ⧸ I) := hlocal
      letI : IsLocalHom (Ideal.Quotient.mk I) := hlocalhom
      (show v k ∈ Ideal.comap (Ideal.Quotient.mk I)
          (IsLocalRing.maximalIdeal (R ⧸ I)) from hk)
    have hk'' :=
      letI : IsLocalRing (R ⧸ I) := hlocal
      letI : IsLocalHom (Ideal.Quotient.mk I) := hlocalhom
      by
        rw [IsLocalRing.maximalIdeal_comap] at hk'
        exact hk'
    exact hk''
  have ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal R := by
    intro i
    let j : Fin ((d₀ - 1) + 1) := Fin.cast hlen.symm i
    change Fin.cases vzero
      (fun k => Fin.cases z (fun l => v (Fin.cast htail l.succ))
        (Fin.cast htail.symm k)) j ∈
      IsLocalRing.maximalIdeal R
    refine Fin.cases ?_ (fun k => ?_) j
    · exact hvmax ⟨0, by omega⟩
    · let k' : Fin ((d₀ - 2) + 1) := Fin.cast htail.symm k
      change Fin.cases z (fun l => v (Fin.cast htail l.succ)) k' ∈
        IsLocalRing.maximalIdeal R
      refine Fin.cases ?_ (fun l => ?_) k'
      · exact hzmax
      · exact hvmax (Fin.cast htail l.succ)
  have hdefa : Unit59.IsIdealOfDefinition R (Ideal.span (Set.range a)) := by
    rw [hArange, Ideal.span_insert]
    exact hdefK
  have hdimseq :=
    Formalization.Books.Algebra.Unit60.dimensions_of_successive_parameter_quotients
      R d₀ a ha hdefa hdimNat
  have hdim1 := hdimseq 1 (by omega) (by omega)
  have hdim2 := hdimseq 2 (by omega) (by omega)
  let b1 : Fin 1 → R := fun j =>
    a ⟨j.1, lt_of_lt_of_le j.2 (by omega)⟩
  let b2 : Fin 2 → R := fun j =>
    a ⟨j.1, lt_of_lt_of_le j.2 (by omega)⟩
  have hdim1' : ringKrullDim (R ⧸ Ideal.span (Set.range b1)) =
      (d₀ - 1 : ℕ) := by
    simpa [b1] using hdim1
  have hdim2' : ringKrullDim (R ⧸ Ideal.span (Set.range b2)) =
      (d₀ - 2 : ℕ) := by
    simpa [b2] using hdim2
  let K1 : Ideal R := Ideal.span (Set.range b1)
  let K2 : Ideal R := Ideal.span (Set.range b2)
  have hK1dim : ringKrullDim (R ⧸ K1) = (d₀ - 1 : ℕ) := hdim1'
  have hK2dim : ringKrullDim (R ⧸ K2) = (d₀ - 2 : ℕ) := hdim2'
  have hK1leK2 : K1 ≤ K2 := by
    dsimp [K1, K2]
    apply Ideal.span_le.mpr
    rintro y ⟨j, rfl⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact Ideal.subset_span ⟨0, by simp [b1, b2, a, vzero]⟩
  have hex : ∃ q : PrimeSpectrum R, K1 ≤ q.asIdeal ∧ z ∉ q.asIdeal := by
    by_contra h
    have hall : ∀ q : PrimeSpectrum R, K1 ≤ q.asIdeal → z ∈ q.asIdeal := by
      intro q hq
      by_contra hzq
      exact h ⟨q, hq, hzq⟩
    have hzero : PrimeSpectrum.zeroLocus (K1 : Set R) =
        PrimeSpectrum.zeroLocus (K2 : Set R) := by
      ext q
      simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
      constructor
      · intro hq
        have hzq : z ∈ q.asIdeal := hall q hq
        apply Ideal.span_le.mpr
        rintro y ⟨j, rfl⟩
        refine Fin.cases ?_ (fun k => ?_) j
        · have hvzeroq : vzero ∈ q.asIdeal :=
            hq (Ideal.subset_span ⟨0, by simp [b1, a, vzero]⟩)
          simpa [b2, a, vzero] using hvzeroq
        · have hk : k = 0 := Subsingleton.elim _ _
          subst k
          simpa [b2, a, z] using hzq
      · exact fun hq => hK1leK2.trans hq
    have hdimEq : ringKrullDim (R ⧸ K1) = ringKrullDim (R ⧸ K2) := by
      rw [ringKrullDim_quotient_unit61, ringKrullDim_quotient_unit61, hzero]
    have hcast : ((d₀ - 1 : ℕ) : WithBot ℕ∞) =
        ((d₀ - 2 : ℕ) : WithBot ℕ∞) := by
      calc
        ((d₀ - 1 : ℕ) : WithBot ℕ∞) = ringKrullDim (R ⧸ K1) := hK1dim.symm
        _ = ringKrullDim (R ⧸ K2) := hdimEq
        _ = ((d₀ - 2 : ℕ) : WithBot ℕ∞) := hK2dim
    have hnat : d₀ - 1 = d₀ - 2 := by
      exact_mod_cast hcast
    omega
  obtain ⟨q, hqK1, hzq⟩ := hex
  have hqp : q = p₀ := by
    apply Set.mem_singleton_iff.mp
    rw [← hzsingle]
    exact (PrimeSpectrum.mem_basicOpen z q).mpr hzq
  have hvzero0 : vzero = 0 := by
    have hvzeroq : vzero ∈ q.asIdeal :=
      hqK1 (Ideal.subset_span ⟨0, by simp [b1, a, vzero]⟩)
    simpa [hqp, p₀] using hvzeroq
  have hK1bot : K1 = (⊥ : Ideal R) := by
    apply le_antisymm
    · dsimp [K1]
      apply Ideal.span_le.mpr
      rintro y ⟨j, rfl⟩
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [b1, a, vzero, hvzero0]
    · exact bot_le
  have hdim1R : ringKrullDim (R ⧸ K1) = ringKrullDim R := by
    rw [hK1bot]
    exact ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)
  have hbad : ((d₀ - 1 : ℕ) : WithBot ℕ∞) =
      (d₀ : WithBot ℕ∞) := by
    calc
      ((d₀ - 1 : ℕ) : WithBot ℕ∞) = ringKrullDim (R ⧸ K1) := hK1dim.symm
      _ = ringKrullDim R := hdim1R
      _ = (d₀ : WithBot ℕ∞) := hdimNat
  have hbadNat : d₀ - 1 = d₀ := by
    exact_mod_cast hbad
  omega

/-- A Noetherian ring with finitely many prime ideals has Krull dimension at
most one. -/
theorem noetherian_ring_with_finite_primeSpectrum_dim_le_one
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [Finite (PrimeSpectrum R)] :
    ringKrullDim R ≤ 1 := by
  by_contra hdimle
  have hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim R := by
    have h := ENat.WithBot.add_one_le_iff.mpr (lt_of_not_ge hdimle)
    norm_num at h ⊢
    exact h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hdim2
  have hl2 : l.length = 2 := hl
  let p₀ : PrimeSpectrum R := l ⟨0, by omega⟩
  let p₁ : PrimeSpectrum R := l ⟨1, by omega⟩
  let p₂ : PrimeSpectrum R := l ⟨2, by omega⟩
  have hp₀₁ : p₀ < p₁ := by
    simpa [p₀, p₁, hl2] using l.step ⟨0, by omega⟩
  have hp₁₂ : p₁ < p₂ := by
    simpa [p₁, p₂, hl2] using l.step ⟨1, by omega⟩
  obtain ⟨m, hm, hmle⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := p₀.asIdeal) bot_le
  let A := R ⧸ m
  let eA := m.primeSpectrumQuotientOrderIsoZeroLocus
  let p₀A : PrimeSpectrum A := eA.symm ⟨p₀, hmle⟩
  let p₁A : PrimeSpectrum A := eA.symm ⟨p₁, hmle.trans hp₀₁.le⟩
  let p₂A : PrimeSpectrum A := eA.symm ⟨p₂, hmle.trans (hp₀₁.trans hp₁₂).le⟩
  have hp₀₁A : p₀A < p₁A := by
    apply eA.symm.lt_iff_lt.mpr
    change p₀ < p₁
    exact hp₀₁
  have hp₁₂A : p₁A < p₂A := by
    apply eA.symm.lt_iff_lt.mpr
    change p₁ < p₂
    exact hp₁₂
  let hmprime : m.IsPrime := hm.1.1
  let T := Localization.AtPrime p₂A.asIdeal
  let eT := IsLocalization.AtPrime.primeSpectrumOrderIso T p₂A.asIdeal
  have hp₀A₂ : p₀A ≤ p₂A := hp₀₁A.le.trans hp₁₂A.le
  have hp₁A₂ : p₁A ≤ p₂A := hp₁₂A.le
  let t₀ : PrimeSpectrum T := eT.symm ⟨p₀A, hp₀A₂⟩
  let t₁ : PrimeSpectrum T := eT.symm ⟨p₁A, hp₁A₂⟩
  let t₂ : PrimeSpectrum T := eT.symm ⟨p₂A, by change p₂A ≤ p₂A; exact le_rfl⟩
  have ht₀₁ : t₀ < t₁ := by
    apply eT.symm.lt_iff_lt.mpr
    change p₀A < p₁A
    exact hp₀₁A
  have ht₁₂ : t₁ < t₂ := by
    apply eT.symm.lt_iff_lt.mpr
    change p₁A < p₂A
    exact hp₁₂A
  let lT : LTSeries (PrimeSpectrum T) :=
    { length := 2
      toFun := fun i =>
        Fin.cases t₀ (fun j => Fin.cases t₁ (fun _ => t₂) j) i
      step := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change t₀ < t₁
          exact ht₀₁
        · have hj : j = 0 := Subsingleton.elim _ _
          subst j
          change t₁ < t₂
          exact ht₁₂ }
  have hTdim : (2 : WithBot ℕ∞) ≤ ringKrullDim T := by
    apply Order.le_krullDim_iff.mpr
    exact ⟨lT, by rfl⟩
  have hAfin : Finite (PrimeSpectrum A) := by
    apply Finite.of_injective (fun p => (eA p).1)
    intro p q h
    apply eA.injective
    exact Subtype.ext h
  have hTfin : Finite (PrimeSpectrum T) :=
    letI : Finite (PrimeSpectrum A) := hAfin
    by
      apply Finite.of_injective (fun p => (eT p).1)
      intro p q h
      apply eT.injective
      exact Subtype.ext h
  have hInf :=
    letI : m.IsPrime := hmprime
    letI : Finite (PrimeSpectrum T) := hTfin
    nonempty_open_primeSpectrum_infinite_of_local_noetherian_domain_dim_ge_two
      (R := T) hTdim (U := Set.univ) isOpen_univ Set.univ_nonempty
  have hInfT : Infinite (PrimeSpectrum T) := Set.infinite_univ_iff.mp hInf
  exact hTfin.not_infinite hInfT

/- The source's examples are the one-variable formal power-series ring over a
   field and the ring of p-adic integers.  The latter is the only p-adic
   interpretation compatible with the stated dimension-one conclusion. -/

/-- Formal power series over a field give a Noetherian dimension-one ring with
finitely many prime ideals. -/
theorem powerSeries_field_is_noetherian_dim_one_finite_primeSpectrum
    (k : Type u) [Field k] :
    IsNoetherianRing (PowerSeries k) ∧
      ringKrullDim (PowerSeries k) = 1 ∧
        Finite (PrimeSpectrum (PowerSeries k)) := by
  constructor
  · infer_instance
  constructor
  · exact IsDiscreteValuationRing.ringKrullDim_eq_one _
  · exact finite_primeSpectrum_of_isDiscreteValuationRing

/-- The p-adic integers give a Noetherian dimension-one ring with finitely
many prime ideals. -/
theorem padicIntegers_is_noetherian_dim_one_finite_primeSpectrum
    (p : ℕ) [Fact p.Prime] :
    IsNoetherianRing ℤ_[p] ∧
      ringKrullDim ℤ_[p] = 1 ∧
        Finite (PrimeSpectrum ℤ_[p]) := by
  constructor
  · infer_instance
  constructor
  · exact IsDiscreteValuationRing.ringKrullDim_eq_one _
  · exact finite_primeSpectrum_of_isDiscreteValuationRing

/-! ## Finite-type algebras of dimension zero -/

/-- For a nonzero finite-type algebra over a field, the seven conditions in
the source are equivalent.  The fourth condition uses the earlier equivalent
formulation that prime ideals have no nontrivial inclusions. -/
theorem finite_type_algebra_finite_nr_primes
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Nontrivial S] :
    List.TFAE
      [ ringKrullDim S = 0
      , Finite (PrimeSpectrum S)
      , Finite (MaximalSpectrum S)
      , ∀ p q : Ideal S, p.IsPrime → q.IsPrime → p ≤ q → p = q
      , FiniteDimensional k S
      , IsArtinianRing S
      , DiscreteTopology (PrimeSpectrum S) ] := by
  classical
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hdim_to_art : ringKrullDim S = 0 → IsArtinianRing S := by
    exact (Formalization.Books.Algebra.Unit60.noetherian_ringKrullDim_eq_zero_iff_artinian
      (R := S)).1
  have hart_to_dim : IsArtinianRing S → ringKrullDim S = 0 := by
    exact (Formalization.Books.Algebra.Unit60.noetherian_ringKrullDim_eq_zero_iff_artinian
      (R := S)).2
  have hart_to_finprime : IsArtinianRing S → Finite (PrimeSpectrum S) := by
    intro h
    have h' : IsNoetherianRing S ∧
        Formalization.Books.Algebra.Unit60.IsFiniteDiscretePrimeSpectrum S :=
      ((Formalization.Books.Algebra.Unit60.dimension_zero_ring_characterization S).out
        0 4).mp h
    exact h'.2.1
  have hfinprime_to_art : Finite (PrimeSpectrum S) → IsArtinianRing S := by
    intro h
    let _ : Finite (PrimeSpectrum S) := h
    let hJ : IsJacobsonRing S :=
      Formalization.Books.Algebra.Unit35.finiteType_algebra_over_field_isJacobson
        (k := k) (A := S)
    let _ : JacobsonSpace (PrimeSpectrum S) :=
      (Formalization.Books.Algebra.Unit35.jacobson_iff_primeSpectrum_isJacobsonSpace
        (R := S)).mp hJ
    have hdisc : DiscreteTopology (PrimeSpectrum S) :=
      Formalization.Books.Topology.Unit18.discreteTopology_of_finite_jacobson
    have hdim : Ring.KrullDimLE 0 S :=
      (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).2
    exact (isArtinianRing_iff_krullDimLE_zero).2 hdim
  have hart_to_finmax : IsArtinianRing S → Finite (MaximalSpectrum S) := by
    intro h
    let _ : Finite (PrimeSpectrum S) := hart_to_finprime h
    exact Finite.of_injective MaximalSpectrum.toPrimeSpectrum
      MaximalSpectrum.toPrimeSpectrum_injective
  have hfinmax_to_art : Finite (MaximalSpectrum S) → IsArtinianRing S := by
    intro h
    let _ : Finite (MaximalSpectrum S) := h
    have hclosed : (closedPoints (PrimeSpectrum S)).Finite := by
      rw [Formalization.Books.Algebra.Unit35.primeSpectrum_closedPoints_eq_maximalIdeals]
      have heq : {p : PrimeSpectrum S | p.asIdeal.IsMaximal} =
          Set.range (@MaximalSpectrum.toPrimeSpectrum S _) := by
        ext p
        constructor
        · intro hp
          exact ⟨⟨p.asIdeal, hp⟩, by apply PrimeSpectrum.ext; rfl⟩
        · rintro ⟨m, rfl⟩
          exact m.isMaximal
      rw [heq]
      exact Set.finite_range _
    let hJ : IsJacobsonRing S :=
      Formalization.Books.Algebra.Unit35.finiteType_algebra_over_field_isJacobson
        (k := k) (A := S)
    let _ : JacobsonSpace (PrimeSpectrum S) :=
      (Formalization.Books.Algebra.Unit35.jacobson_iff_primeSpectrum_isJacobsonSpace
        (R := S)).mp hJ
    have hdisc : DiscreteTopology (PrimeSpectrum S) :=
      Formalization.Books.Topology.Unit18.discreteTopology_of_finite_closedPoints hclosed
    have hdim : Ring.KrullDimLE 0 S :=
      (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).2
    exact (isArtinianRing_iff_krullDimLE_zero).2 hdim
  have hart_to_no_inclusions : IsArtinianRing S →
      ∀ p q : Ideal S, p.IsPrime → q.IsPrime → p ≤ q → p = q := by
    intro h p q hp hq hpq
    let _ : IsArtinianRing S := h
    exact (IsArtinianRing.isMaximal_of_isPrime p).eq_of_le hq.ne_top hpq
  have hno_inclusions_to_art :
      (∀ p q : Ideal S, p.IsPrime → q.IsPrime → p ≤ q → p = q) →
        IsArtinianRing S := by
    intro h
    have hall : ∀ p : Ideal S, p.IsPrime → p.IsMaximal := by
      intro p hp
      obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal hp.ne_top
      exact (h p m hp hm.isPrime hpm) ▸ hm
    exact hdim_to_art ((ringKrullDimZero_iff_ringKrullDim_eq_zero).1
      (Ring.KrullDimLE.mk₀ hall))
  have hfd_to_art : FiniteDimensional k S → IsArtinianRing S := by
    intro h
    let _ : FiniteDimensional k S := h
    exact Formalization.Books.Algebra.Unit53.finiteDimensional_algebra_isArtinian
      (k := k) (R := S)
  have hart_to_fd : IsArtinianRing S → FiniteDimensional k S := by
    intro h
    let _ : IsArtinianRing S := h
    exact Module.finite_of_isArtinianRing k S
  have hdisc_to_art : DiscreteTopology (PrimeSpectrum S) → IsArtinianRing S := by
    intro h
    let _ : DiscreteTopology (PrimeSpectrum S) := h
    let _ : Finite (PrimeSpectrum S) := TopologicalSpace.NoetherianSpace.finite
    have hdim : Ring.KrullDimLE 0 S :=
      (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp h).2
    exact (isArtinianRing_iff_krullDimLE_zero).2 hdim
  have hart_to_disc : IsArtinianRing S → DiscreteTopology (PrimeSpectrum S) := by
    intro h
    have h' : IsNoetherianRing S ∧
        Formalization.Books.Algebra.Unit60.IsFiniteDiscretePrimeSpectrum S :=
      ((Formalization.Books.Algebra.Unit60.dimension_zero_ring_characterization S).out
        0 4).mp h
    exact h'.2.2
  tfae_have 1 → 6 := hdim_to_art
  tfae_have 6 → 1 := hart_to_dim
  tfae_have 6 → 2 := hart_to_finprime
  tfae_have 2 → 6 := hfinprime_to_art
  tfae_have 6 → 3 := hart_to_finmax
  tfae_have 3 → 6 := hfinmax_to_art
  tfae_have 6 → 4 := hart_to_no_inclusions
  tfae_have 4 → 6 := hno_inclusions_to_art
  tfae_have 6 → 5 := hart_to_fd
  tfae_have 5 → 6 := hfd_to_art
  tfae_have 6 → 7 := hart_to_disc
  tfae_have 7 → 6 := hdisc_to_art
  tfae_finish

/-! ## Noetherian Jacobson rings -/

/-- A Noetherian domain of dimension one with infinitely many primes is a
Jacobson ring. -/
theorem noetherian_domain_dim_one_infinite_primes_isJacobson
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (hdim : ringKrullDim R = 1)
    (hinfinite : Infinite (PrimeSpectrum R)) :
    IsJacobsonRing R := by
  let _ : FiniteRingKrullDim R :=
    (finiteRingKrullDim_iff_ne_bot_and_top (R := R)).2
      ⟨by rw [hdim]; simp, by
        rw [hdim]
        exact fun h => ENat.one_ne_top (WithBot.coe_eq_top.mp h)⟩
  have hprime : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → P.IsMaximal := by
    intro P hP hP0
    let _ : P.IsPrime := hP
    apply P.isMaximal_of_height_eq_ringKrullDim
    apply le_antisymm
    · exact Ideal.height_le_ringKrullDim_of_isPrime
    · rw [hdim]
      have hbotlt : (⊥ : Ideal R) < P := bot_lt_iff_ne_bot.mpr hP0
      simpa using
        (Ideal.height_add_one_le_of_lt_of_isPrime hbotlt)
  let _ : Infinite (PrimeSpectrum R) := hinfinite
  have hprime_infinite_subtype : Infinite {P : Ideal R // P.IsPrime} := by
    exact Infinite.of_injective (f := PrimeSpectrum.equivSubtype R)
      (PrimeSpectrum.equivSubtype R).injective
  have hprime_infinite : ({P : Ideal R | P.IsPrime} : Set (Ideal R)).Infinite :=
    Set.infinite_coe_iff.mp hprime_infinite_subtype
  have hnonzero_infinite :
      (({P : Ideal R | P.IsPrime} : Set (Ideal R)) \ {⊥}).Infinite := by
    exact hprime_infinite.sdiff (Set.finite_singleton (⊥ : Ideal R))
  have hmaximal_infinite : ({P : Ideal R | P.IsMaximal} : Set (Ideal R)).Infinite := by
    apply hnonzero_infinite.mono
    intro P hP
    have hP0 : P ≠ ⊥ := by
      intro hP0
      exact hP.2 (by simp [hP0])
    exact hprime P hP.1 hP0
  exact Formalization.Books.Algebra.Unit35.isJacobsonRing_of_domain_noetherian_nonzero_primes_maximal
    hprime hmaximal_infinite

/-- A Noetherian ring is Jacobson when every prime is either maximal or is
contained in infinitely many prime ideals. -/
theorem noetherian_ring_isJacobson_of_prime_maximal_or_infinite_over
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hprime : ∀ p : Ideal R, p.IsPrime →
      p.IsMaximal ∨
        Set.Infinite {q : Ideal R | q.IsPrime ∧ p ≤ q}) :
    IsJacobsonRing R := by
  by_contra hJ
  obtain ⟨p, f, hpmax, hpf, hloc, hfield⟩ :=
    Formalization.Books.Algebra.Unit35.characterize_nonJacobson_ring hJ
  have hinf : Set.Infinite {q : Ideal R | q.IsPrime ∧ p.asIdeal ≤ q} :=
    (hprime p.asIdeal p.2).resolve_left hpmax
  let _ : p.asIdeal.IsPrime := p.2
  let A := R ⧸ p.asIdeal
  let fA : A := Ideal.Quotient.mk p.asIdeal f
  let eA := p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  let pA : PrimeSpectrum A := eA.symm ⟨p, by simp⟩
  have heA_pA : (eA pA).1 = p := by
    simp [pA]
  have hpAbot : pA.asIdeal = (⊥ : Ideal A) := by
    change p.asIdeal.map (Ideal.Quotient.mk p.asIdeal) = ⊥
    rw [Ideal.map_eq_bot_iff_le_ker]
    simp [Ideal.mk_ker]
  have hdim_local : ∀ q : PrimeSpectrum A,
      ringKrullDim (Localization.AtPrime q.asIdeal) ≤ 1 := by
    intro q
    by_contra hdim
    have hdim2 : (2 : WithBot ℕ∞) ≤
        ringKrullDim (Localization.AtPrime q.asIdeal) := by
      have h := ENat.WithBot.add_one_le_iff.mpr (lt_of_not_ge hdim)
      norm_num at h ⊢
      exact h
    let eQ := IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime q.asIdeal) q.asIdeal
    let z₀ : PrimeSpectrum (Localization.AtPrime q.asIdeal) :=
      eQ.symm ⟨pA, by
        change pA.asIdeal ≤ q.asIdeal
        rw [hpAbot]
        exact bot_le⟩
    let U : Set (PrimeSpectrum (Localization.AtPrime q.asIdeal)) :=
      PrimeSpectrum.basicOpen
        (algebraMap A (Localization.AtPrime q.asIdeal) fA)
    have hUopen : IsOpen U := PrimeSpectrum.isOpen_basicOpen
    have hUnonempty : U.Nonempty := by
      refine ⟨z₀, (PrimeSpectrum.mem_basicOpen _ _).mpr ?_⟩
      intro hfz
      have hfq : fA ∈ pA.asIdeal := by
        have hunder : fA ∈ z₀.asIdeal.under A := by
          rw [Ideal.mem_under]
          exact hfz
        change fA ∈ (eQ z₀).1.asIdeal at hunder
        simpa [z₀] using hunder
      apply hpf
      have hfzero : fA = 0 := by simpa [hpAbot] using hfq
      exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [fA] using hfzero)
    have hUinf :=
      nonempty_open_primeSpectrum_infinite_of_local_noetherian_domain_dim_ge_two
        hdim2 hUopen hUnonempty
    have hUsingle : U ⊆ {z₀} := by
      intro z hz
      have hzf : algebraMap A (Localization.AtPrime q.asIdeal) fA ∉ z.asIdeal :=
        (PrimeSpectrum.mem_basicOpen _ _).mp hz
      let zA := (eQ z).1
      have hzAf : fA ∉ zA.asIdeal := by
        intro hfAq
        apply hzf
        rw [← Ideal.mem_under]
        exact hfAq
      have hzR : (eA zA).1 ∈
          Formalization.Books.Algebra.Unit35.primeSpectrumLocallyClosedSet p f := by
        rw [Formalization.Books.Algebra.Unit35.primeSpectrumLocallyClosedSet]
        constructor
        · exact (eA zA).2
        · exact (PrimeSpectrum.mem_basicOpen _ _).mpr hzAf
      have hzRp : (eA zA).1 = p := by
        have : (eA zA).1 ∈ ({p} : Set (PrimeSpectrum R)) := hloc ▸ hzR
        simpa using this
      have hzA : zA = pA := by
        apply eA.injective
        apply Subtype.ext
        exact hzRp.trans heA_pA.symm
      apply eQ.injective
      apply Subtype.ext
      have heQ_z₀ : (eQ z₀).1 = pA := by
        simp [z₀]
      exact hzA.trans heQ_z₀.symm
    exact hUinf.not_finite (Set.Finite.subset (Set.finite_singleton _) hUsingle)
  have hDsingleton :
      (PrimeSpectrum.basicOpen fA : Set (PrimeSpectrum A)) =
        {pA} := by
    ext z
    constructor
    · intro hz
      have hzf : fA ∉ z.asIdeal := (PrimeSpectrum.mem_basicOpen _ _).mp hz
      let zR := (eA z).1
      have hzRf : f ∉ zR.asIdeal := by
        intro hfz
        apply hzf
        change fA ∈ z.asIdeal
        exact hfz
      have hzloc : zR ∈
          Formalization.Books.Algebra.Unit35.primeSpectrumLocallyClosedSet p f := by
        rw [Formalization.Books.Algebra.Unit35.primeSpectrumLocallyClosedSet]
        exact ⟨(eA z).2, (PrimeSpectrum.mem_basicOpen _ _).mpr hzRf⟩
      have hzRp : zR = p := by
        have : zR ∈ ({p} : Set (PrimeSpectrum R)) := hloc ▸ hzloc
        simpa using this
      have : z = pA := by
        apply eA.injective
        apply Subtype.ext
        exact hzRp.trans heA_pA.symm
      exact Set.mem_singleton_iff.mpr this
    · intro hz
      have hz' : z = pA := Set.mem_singleton_iff.mp hz
      subst z
      apply (PrimeSpectrum.mem_basicOpen _ _).mpr
      intro hfz
      apply hpf
      have hfzero : fA = 0 := by simpa [hpAbot] using hfz
      exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [fA] using hfzero)
  have hdim_le : ringKrullDim A ≤ 1 := by
    rw [ringKrullDim_le_iff_isMaximal_height_le]
    intro m hm
    have h := hdim_local (⟨m, hm.isPrime⟩ : PrimeSpectrum A)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m
      (Localization.AtPrime m)] at h
    exact h
  have hinfA : Infinite (PrimeSpectrum A) := by
    let _ : Infinite {q : Ideal R // q.IsPrime ∧ p.asIdeal ≤ q} :=
      hinf.to_subtype
    apply Infinite.of_injective
      (fun q : {q : Ideal R // q.IsPrime ∧ p.asIdeal ≤ q} =>
        eA.symm ⟨⟨q, q.2.1⟩, q.2.2⟩)
    intro q q' hqq'
    apply Subtype.ext
    have hsub :
        (⟨⟨q, q.2.1⟩, q.2.2⟩ : PrimeSpectrum.zeroLocus (R := R) p.asIdeal) =
          ⟨⟨q', q'.2.1⟩, q'.2.2⟩ := eA.symm.injective hqq'
    exact congrArg (fun z : PrimeSpectrum.zeroLocus (R := R) p.asIdeal => z.1.asIdeal) hsub
  have hdim_ge : (1 : WithBot ℕ∞) ≤ ringKrullDim A := by
    obtain ⟨q, hq, hqnot⟩ := hinf.exists_notMem_finite (Set.finite_singleton p.asIdeal)
    let qA : PrimeSpectrum A := eA.symm ⟨⟨q, hq.1⟩, hq.2⟩
    have hqbot : qA.asIdeal ≠ ⊥ := by
      intro hqbot
      apply hqnot
      have hqeq : qA = eA.symm ⟨p, by simp⟩ := by
        apply PrimeSpectrum.ext
        exact hqbot.trans hpAbot.symm
      have hsub :
          (⟨⟨q, hq.1⟩, hq.2⟩ : PrimeSpectrum.zeroLocus (R := R) p.asIdeal) =
            ⟨p, by simp⟩ := by
        calc
          (⟨⟨q, hq.1⟩, hq.2⟩ : PrimeSpectrum.zeroLocus (R := R) p.asIdeal) = eA qA := by
            simp [qA]
          _ = eA pA := congrArg eA hqeq
          _ = (⟨p, by simp⟩ : PrimeSpectrum.zeroLocus (R := R) p.asIdeal) := by
            simp [pA]
      exact congrArg (fun z : PrimeSpectrum.zeroLocus (R := R) p.asIdeal => z.1.asIdeal) hsub
    have hheight : (1 : WithBot ℕ∞) ≤ qA.asIdeal.height := by
      let _ : qA.asIdeal.IsPrime := qA.2
      have hbotlt : (⊥ : Ideal A) < qA.asIdeal := bot_lt_iff_ne_bot.mpr hqbot
      simpa using
        (Ideal.height_add_one_le_of_lt_of_isPrime hbotlt)
    exact hheight.trans Ideal.height_le_ringKrullDim_of_isPrime
  have hdimA : ringKrullDim A = 1 := le_antisymm hdim_le hdim_ge
  let _ : Infinite (PrimeSpectrum A) := hinfA
  let _ : IsJacobsonRing A :=
    noetherian_domain_dim_one_infinite_primes_isJacobson hdimA hinfA
  have hclosed :
      IsClosed ({pA} : Set (PrimeSpectrum A)) := by
    have hbasic_open : IsOpen (PrimeSpectrum.basicOpen fA : Set (PrimeSpectrum A)) :=
      PrimeSpectrum.isOpen_basicOpen
    have hnonempty : (PrimeSpectrum.basicOpen fA : Set (PrimeSpectrum A)).Nonempty := by
      rw [hDsingleton]
      exact Set.singleton_nonempty _
    obtain ⟨z, hz, hzclosed⟩ :=
      PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing
        (PrimeSpectrum.basicOpen fA : Set (PrimeSpectrum A)) hbasic_open hnonempty
    have hz' : z = pA := by
      rw [hDsingleton] at hz
      exact Set.mem_singleton_iff.mp hz
    simpa [hz'] using hzclosed
  have hpAmax : pA.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal pA).mp hclosed
  have hpfield : IsField A :=
    (Ideal.isField_iff_maximal_bot).2 (by simpa [hpAbot] using hpAmax)
  exact hpmax (Ideal.Quotient.maximal_of_isField p.asIdeal hpfield)

end

end Formalization.Books.Algebra.Unit61
