import Formalization.Books.Algebra.Unit30.MoreOnImages
import Formalization.Books.Algebra.Unit31.NoetherianRings
import Formalization.Books.Algebra.Unit34.HilbertNullstellensatz
import Formalization.Books.Topology.Unit18.JacobsonSpaces
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Commutative Algebra, Chapter 35: Jacobson rings

The source's Jacobson-ring predicate, closed points, residue fields,
localizations, constructible sets, and irreducible components use the
canonical Mathlib interfaces.  The long matrix examples retain their
polynomial relations, group actions, rank normal forms, and component
statements as usable declarations; their proofs belong to the proving stage.
-/

namespace Formalization.Books.Algebra.Unit35

open Set
open _root_.Topology
open scoped Polynomial TensorProduct

universe u v w

noncomputable section

/-! ## Definition and first criteria -/

/- The source definition is Mathlib's canonical `IsJacobsonRing` class. -/
theorem jacobsonRing_iff_radical_ideal {R : Type u} [CommRing R] :
    IsJacobsonRing R ↔ ∀ I : Ideal R, I.IsRadical → I.jacobson = I := by
  exact isJacobsonRing_iff

theorem primeSpectrum_closedPoints_eq_maximalIdeals {R : Type u} [CommRing R] :
    closedPoints (PrimeSpectrum R) =
      {p : PrimeSpectrum R | p.asIdeal.IsMaximal} := by
  ext p
  simp [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]

/- A field and the usual finite-type algebras over a field are Jacobson. -/
theorem finiteType_algebra_over_field_isJacobson
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    IsJacobsonRing A := by
  exact isJacobsonRing_of_finiteType (A := k) (B := A)

theorem jacobson_of_prime_ideals_are_jacobson
    {R : Type u} [CommRing R]
    (h : ∀ P : Ideal R, P.IsPrime → P.jacobson = P) :
    IsJacobsonRing R := by
  exact isJacobsonRing_iff_prime_eq.mpr h

theorem jacobson_iff_primeSpectrum_isJacobsonSpace
    {R : Type u} [CommRing R] :
    IsJacobsonRing R ↔ JacobsonSpace (PrimeSpectrum R) := by
  exact PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace

/- The localization and closed-subset notation used in the next criterion. -/
def primeSpectrumLocallyClosedSet {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (f : R) : Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus (p.asIdeal : Set R) ∩
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))

abbrev primeSpectrumLocalizationAtPrimeElement {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (f : R) :=
  Localization.Away (Ideal.Quotient.mk p.asIdeal f)

theorem characterize_nonJacobson_ring
    {R : Type u} [CommRing R] :
    ¬ IsJacobsonRing R →
      ∃ (p : PrimeSpectrum R) (f : R),
        ¬ p.asIdeal.IsMaximal ∧ f ∉ p.asIdeal ∧
          primeSpectrumLocallyClosedSet p f = {p} ∧
          IsField (primeSpectrumLocalizationAtPrimeElement p f) := by
  intro hR
  have hJ : ¬ JacobsonSpace (PrimeSpectrum R) := by
    intro h
    exact hR ((jacobson_iff_primeSpectrum_isJacobsonSpace).2 h)
  rw [jacobsonSpace_iff_locallyClosed] at hJ
  push Not at hJ
  obtain ⟨Z, hZne, hZloc, hZclosed⟩ := hJ
  rcases hZloc with ⟨U, T, hU, hT, hZT⟩
  rcases hZne with ⟨x, hx⟩
  rw [hZT] at hx
  obtain ⟨V, ⟨f, rfl⟩, hxV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx.1 hU
  obtain ⟨I₀, hIT₀⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal T).mp hT
  let I := I₀.radical
  have hIT : T = PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [hIT₀, ← PrimeSpectrum.zeroLocus_radical]
  have hIle : I ≤ x.asIdeal := by
    rw [hIT] at hx
    exact hx.2
  have hIrad : I.IsRadical := Ideal.radical_isRadical _
  have hI_top : I ≠ ⊤ := by
    intro h
    exact x.2.ne_top (top_unique (h ▸ hIle))
  let A := R ⧸ I
  let fA : A := Ideal.Quotient.mk I f
  have hxf : f ∉ x.asIdeal := (PrimeSpectrum.mem_basicOpen f x).mp hxV
  have hfA : fA ≠ 0 := by
    intro hf
    have hmem : f ∈ I := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      simpa [fA] using hf
    exact hxf (hIle hmem)
  have : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hI_top
  have hnot : ¬ Subsingleton (Localization.Away fA) := by
    intro hsub
    have hzero : (0 : A) ∈ Submonoid.powers fA :=
      (IsLocalization.subsingleton_iff (M := Submonoid.powers fA)
        (S := Localization.Away fA)).mp hsub
    rcases hzero with ⟨n, hn⟩
    have hpowA : fA ^ n = 0 := by simpa using hn
    have hpow : f ^ n ∈ x.asIdeal := by
      apply hIle
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      simpa [fA] using hpowA
    exact hxf (x.2.mem_of_pow_mem n hpow)
  have : Nontrivial (Localization.Away fA) :=
    not_subsingleton_iff_nontrivial.mp hnot
  let S := Localization.Away fA
  obtain ⟨M, hM⟩ := Ideal.exists_maximal S
  let J : Ideal A := M.under A
  have hMprime : M.IsPrime := hM.isPrime
  have hdisj : Disjoint (Submonoid.powers fA : Set A) (J : Set A) :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (M := Submonoid.powers fA)
      (S := S) M).mp hMprime |>.2
  have hJprime : J.IsPrime :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (M := Submonoid.powers fA)
      (S := S) M).mp hMprime |>.1
  let p : PrimeSpectrum R :=
    PrimeSpectrum.comap (Ideal.Quotient.mk I) ⟨J, hJprime⟩
  have hpI : I ≤ p.asIdeal := by
    change I ≤ J.comap (Ideal.Quotient.mk I)
    intro a ha
    apply Ideal.ker_le_comap (Ideal.Quotient.mk I)
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hpf : f ∉ p.asIdeal := by
    intro hf
    apply Set.disjoint_left.mp hdisj (Submonoid.mem_powers fA)
    change fA ∈ J
    exact hf
  have hpT : p ∈ T := by
    rw [hIT]
    exact hpI
  have hpU : p ∈ U := hVU ((PrimeSpectrum.mem_basicOpen f p).mpr hpf)
  have hpZ : p ∈ Z := by
    rw [hZT]
    exact ⟨hpU, hpT⟩
  have hpmax : ¬ p.asIdeal.IsMaximal := by
    intro hp
    have hmem : p ∈ Z ∩ closedPoints (PrimeSpectrum R) :=
      ⟨hpZ, mem_closedPoints_iff.mpr
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr hp)⟩
    rw [hZclosed] at hmem
    exact hmem
  have hlocal : primeSpectrumLocallyClosedSet p f = {p} := by
    ext q
    constructor
    · intro hq
      have hqp : p.asIdeal ≤ q.asIdeal := hq.1
      have hqf : f ∉ q.asIdeal :=
        (PrimeSpectrum.mem_basicOpen f q).mp hq.2
      have hqI : I ≤ q.asIdeal := hpI.trans hqp
      let Q : Ideal A := q.asIdeal.map (Ideal.Quotient.mk I)
      have hQprime : Q.IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
          (by
            intro a ha
            exact hqI (Ideal.Quotient.eq_zero_iff_mem.mp ha))
      have hQcomap : Q.comap (Ideal.Quotient.mk I) = q.asIdeal := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
        exact sup_eq_left.mpr (by
          intro a ha
          exact hqI (Ideal.Quotient.eq_zero_iff_mem.mp ha))
      have hQdisj : Disjoint (Submonoid.powers fA : Set A) (Q : Set A) := by
        refine Set.disjoint_left.2 fun z hzpow hzQ => ?_
        rcases hzpow with ⟨n, rfl⟩
        have hzQ' : f ^ n ∈ q.asIdeal := by
          rw [← hQcomap]
          change Ideal.Quotient.mk I (f ^ n) ∈ Q
          simpa [Q, fA] using hzQ
        exact hqf (q.2.mem_of_pow_mem n hzQ')
      let N : Ideal S := Q.map (algebraMap A S)
      have hNprime : N.IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint (M := Submonoid.powers fA)
          (S := S) Q hQprime hQdisj
      have hJQ : J ≤ Q := by
        rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective J]
        rw [Ideal.map_le_iff_le_comap, hQcomap]
        simpa [p] using hqp
      have hMN : M ≤ N := by
        rw [← IsLocalization.map_under (M := Submonoid.powers fA) (S := S) M]
        exact Ideal.map_mono hJQ
      have hMN_eq : M = N := hM.eq_of_le hNprime.ne_top hMN
      have hJQ_eq : J = Q := by
        rw [← IsLocalization.under_map_of_isPrime_disjoint
          (M := Submonoid.powers fA) (S := S) hQprime hQdisj]
        exact congr_arg (Ideal.under A) hMN_eq
      apply PrimeSpectrum.ext
      change q.asIdeal = J.comap (Ideal.Quotient.mk I)
      rw [hJQ_eq, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      symm
      apply sup_eq_left.mpr
      have hker : Ideal.comap (Ideal.Quotient.mk I) (⊥ : Ideal A) = I := by
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      rw [hker]
      exact hqI
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      subst q
      change p.asIdeal ≤ p.asIdeal ∧ f ∉ p.asIdeal
      exact ⟨le_rfl, hpf⟩
  refine ⟨p, f, hpmax, hpf, hlocal, ?_⟩
  let g : A →+* R ⧸ p.asIdeal :=
    Ideal.Quotient.lift I (Ideal.Quotient.mk p.asIdeal) (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hpI ha))
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    exact Ideal.Quotient.lift_mk _ _ _
  have hgf : g fA = Ideal.Quotient.mk p.asIdeal f := by
    exact Ideal.Quotient.lift_mk _ _ _
  have hgker : RingHom.ker g = J := by
    dsimp [g]
    exact Ideal.ker_quotient_lift (Ideal.Quotient.mk p.asIdeal) _ |>.trans (by
      rw [Ideal.mk_ker]
      change p.asIdeal.map (Ideal.Quotient.mk I) = J
      change (J.comap (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk I) = J
      exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective J)
  have hgpowers : (0 : R ⧸ p.asIdeal) ∉ Submonoid.powers (g fA) := by
    intro h
    rcases h with ⟨n, hn⟩
    have : g fA = 0 := by
      exact eq_zero_of_pow_eq_zero hn
    exact hpf (Ideal.Quotient.eq_zero_iff_mem.mp (hgf ▸ this))
  let B := Localization.Away (Ideal.Quotient.mk p.asIdeal f)
  let : IsLocalization (Submonoid.powers (g fA)) B := by
    rw [hgf]
    infer_instance
  let : IsLocalization (Submonoid.map g (Submonoid.powers fA)) B := by
    rw [Submonoid.map_powers]
    infer_instance
  let φ : S →+* B :=
    IsLocalization.map B g (Submonoid.powers fA).le_comap_map
  have hφ : Function.Surjective φ := by
    exact IsLocalization.map_surjective_of_surjective
      (M := Submonoid.powers fA) (S := S) (Q := B) hg
  have : IsDomain (R ⧸ p.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime p.asIdeal).mpr p.2
  have hBdomain : IsDomain B :=
    IsLocalization.Away.isDomain B
      (Ideal.Quotient.eq_zero_iff_mem.not.mpr hpf)
  let : IsDomain B := hBdomain
  have hBinj : Function.Injective (algebraMap (R ⧸ p.asIdeal) B) := by
    exact IsLocalization.injective _ (le_nonZeroDivisors_of_noZeroDivisors hgpowers)
  have hunderK : (RingHom.ker φ).under A = J := by
    ext a
    change φ (algebraMap A S a) = 0 ↔ a ∈ J
    have hφcomp : φ (algebraMap A S a) =
        algebraMap (R ⧸ p.asIdeal) B (g a) := by
      simp [φ]
    rw [hφcomp]
    constructor
    · intro hzero
      have : g a = 0 := by
        apply hBinj
        simpa using hzero
      exact hgker ▸ (RingHom.mem_ker.mpr this)
    · intro ha
      have hga : g a = 0 :=
        RingHom.mem_ker.mp (hgker.symm ▸ ha)
      simp [hga]
  have hkerφ : RingHom.ker φ = M := by
    apply (IsLocalization.orderEmbedding (M := Submonoid.powers fA) (S := S)).injective
    exact hunderK.trans rfl
  have eφ : S ⧸ M ≃+* B := by
    rw [← hkerφ]
    exact RingHom.quotientKerEquivOfSurjective hφ
  have hfieldM : IsField (S ⧸ M) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient M).mp hM
  exact eφ.symm.toMulEquiv.isField hfieldM

theorem jacobson_locally_closed_sets_infinite
    {R : Type u} [CommRing R] [IsJacobsonRing R]
    (p : PrimeSpectrum R) (f : R)
    (hp : ¬ p.asIdeal.IsMaximal) (hf : f ∉ p.asIdeal) :
    (primeSpectrumLocallyClosedSet p f).Infinite := by
  classical
  by_contra hInf
  have hfin : (primeSpectrumLocallyClosedSet p f).Finite := not_not.mp hInf
  have hpS : p ∈ primeSpectrumLocallyClosedSet p f := by
    change p.asIdeal ≤ p.asIdeal ∧ f ∉ p.asIdeal
    exact ⟨le_rfl, hf⟩
  let t : Finset (PrimeSpectrum R) := hfin.toFinset
  let ι := {q : PrimeSpectrum R // q ∈ t.erase p}
  have hchoice (q : ι) : ∃ a : R, a ∈ q.1.asIdeal ∧ a ∉ p.asIdeal := by
    have hqS : q.1 ∈ primeSpectrumLocallyClosedSet p f := by
      apply hfin.mem_toFinset.mp
      exact Finset.mem_of_mem_erase q.2
    have hqp : p.asIdeal ≤ q.1.asIdeal := hqS.1
    have hqne : q.1 ≠ p := by
      intro h
      exact (Finset.mem_erase.mp q.2).1 h
    have hnle : ¬ q.1.asIdeal ≤ p.asIdeal := by
      intro hle
      apply hqne
      apply PrimeSpectrum.ext
      exact le_antisymm hle hqp
    exact SetLike.not_le_iff_exists.mp hnle
  choose g hgq hgp using hchoice
  let G : R := ∏ q : ι, g q
  let : p.asIdeal.IsPrime := p.2
  have hGp : G ∉ p.asIdeal := by
    intro h
    change (∏ q : ι, g q) ∈ p.asIdeal at h
    have h' := (Ideal.IsPrime.prod_mem_iff (s := Finset.univ)
      (x := g) (p := p.asIdeal)).mp h
    obtain ⟨q, hq, hqmem⟩ := h'
    exact hgp q hqmem
  have hGq (q : ι) : G ∈ q.1.asIdeal := by
    exact Ideal.prod_mem q.1.asIdeal (Finset.mem_univ q) (hgq q)
  have hfg : primeSpectrumLocallyClosedSet p (f * G) = {p} := by
    ext q
    constructor
    · intro hq
      have hqfg : f * G ∉ q.asIdeal :=
        (PrimeSpectrum.mem_basicOpen (f * G) q).mp hq.2
      have hqf : f ∉ q.asIdeal := by
        intro hqf
        exact hqfg (by simpa [mul_comm] using q.asIdeal.mul_mem_left G hqf)
      have hqS : q ∈ primeSpectrumLocallyClosedSet p f :=
        ⟨hq.1, (PrimeSpectrum.mem_basicOpen f q).mpr hqf⟩
      by_cases hqp : q = p
      · exact Set.mem_singleton_iff.mpr hqp
      · have hqt : q ∈ t := hfin.mem_toFinset.mpr hqS
        have hqerase : q ∈ t.erase p := Finset.mem_erase.mpr ⟨hqp, hqt⟩
        let q' : ι := ⟨q, hqerase⟩
        have hqG : G ∈ q.asIdeal := by
          simpa [q'] using hGq q'
        exact (hqfg (by simpa [mul_comm] using q.asIdeal.mul_mem_right f hqG)).elim
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      subst q
      change p.asIdeal ≤ p.asIdeal ∧ f * G ∉ p.asIdeal
      exact ⟨le_rfl, p.2.mul_notMem hf hGp⟩
  have hJ : JacobsonSpace (PrimeSpectrum R) :=
    (jacobson_iff_primeSpectrum_isJacobsonSpace).mp inferInstance
  have hloc : IsLocallyClosed (primeSpectrumLocallyClosedSet p (f * G)) :=
    (PrimeSpectrum.isClosed_zeroLocus _).isLocallyClosed.inter
      PrimeSpectrum.isOpen_basicOpen.isLocallyClosed
  have hnonempty : (primeSpectrumLocallyClosedSet p (f * G)).Nonempty := by
    rw [hfg]
    exact Set.singleton_nonempty p
  have hclosed := (jacobsonSpace_iff_locallyClosed.mp hJ)
    (primeSpectrumLocallyClosedSet p (f * G)) hnonempty hloc
  rw [hfg] at hclosed
  obtain ⟨q, hq, hqc⟩ := hclosed
  rw [Set.mem_singleton_iff] at hq
  subst q
  exact hp ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp
    (mem_closedPoints_iff.mp hqc))

/-! ## The PID criterion and elementary examples -/

theorem integer_isJacobson : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rw [Ideal.isPrime_int_iff] at hP
  rcases hP with rfl | ⟨p, hp, rfl⟩
  · rw [Ideal.jacobson_bot]
    apply le_antisymm
    · intro x hx
      rw [← Ideal.jacobson_bot] at hx
      have hx0 : x = 0 := by
        by_contra hx0
        have hu : IsUnit (x * x + 1) := (Ideal.mem_jacobson_bot.mp hx) x
        have habs := Int.isUnit_iff_abs_eq.mp hu
        have hx2 : 0 < x * x := mul_self_pos.mpr hx0
        have hpos : 0 < x * x + 1 := by omega
        rw [abs_of_pos hpos] at habs
        omega
      exact hx0 ▸ Ideal.zero_mem _
    · exact bot_le
  · let : Fact (Nat.Prime p) := ⟨hp⟩
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem isJacobsonRing_of_domain_noetherian_nonzero_primes_maximal
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hprime : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → P.IsMaximal)
    (hinfinite : ({P : Ideal R | P.IsMaximal} : Set (Ideal R)).Infinite) :
    IsJacobsonRing R := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP0 : P = ⊥
  · rw [hP0, Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
    apply le_antisymm
    · intro x hx
      by_contra hx0
      have hfinite :
          ({M : Ideal R | M.IsMaximal ∧ x ∈ M} : Set (Ideal R)).Finite := by
        apply (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {x})).subset
        intro M hM
        let _ : M.IsPrime := hM.1.isPrime
        obtain ⟨Q, hQ, hQM⟩ :=
          Ideal.exists_minimalPrimes_le (I := Ideal.span {x})
            (M.span_singleton_le_iff_mem.mpr hM.2)
        have hQprime : Q.IsPrime := hQ.isPrime
        have hQne : Q ≠ ⊥ := by
          intro hQ0
          exact hx0 (by
            have : x ∈ Q := hQ.le (Ideal.subset_span (by simp))
            simpa [hQ0] using this)
        have hQmax : Q.IsMaximal := hprime Q hQprime hQne
        have hQM_eq : Q = M := hQmax.eq_of_le hM.1.ne_top hQM
        exact hQM_eq ▸ hQ
      have hnot : ∃ M : Ideal R, M.IsMaximal ∧ x ∉ M := by
        by_contra h
        push Not at h
        exact hinfinite (hfinite.subset (by
          intro M hM
          exact ⟨hM, h M hM⟩))
      obtain ⟨M, hM, hMx⟩ := hnot
      exact hMx ((Ideal.mem_sInf.mp hx) hM)
    · exact bot_le
  · let _ : P.IsMaximal := hprime P hP hP0
    exact Ideal.jacobson_eq_self_of_isMaximal

/- The “unit times idempotent” property and the quotient-localization property
   used in the product-of-fields example.  The latter records surjectivity of
   the canonical localization map, not merely an abstract ring equivalence. -/
def IsUnitMulIdempotent {R : Type u} [CommRing R] (f : R) : Prop :=
  ∃ u e : R, IsUnit u ∧ IsIdempotentElem e ∧ f = u * e

def LocalizationAwayIsQuotient (R : Type u) [CommRing R] : Prop :=
  ∀ f : R, Function.Surjective (algebraMap R (Localization.Away f))

theorem isJacobsonRing_of_localizationAwayIsQuotient
    {R : Type u} [CommRing R] (h : LocalizationAwayIsQuotient R) :
    IsJacobsonRing R := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rw [Ideal.eq_jacobson_iff_notMem]
  intro x hx
  let S := Localization.Away x
  let φ : R →+* S := algebraMap R S
  have hsurj : Function.Surjective φ := by
    simpa [φ, S] using h x
  have hsub : ¬ Subsingleton S := by
    intro hs
    have hzero : (0 : R) ∈ Submonoid.powers x :=
      (IsLocalization.subsingleton_iff (M := Submonoid.powers x) (S := S)).mp hs
    rcases hzero with ⟨n, hn⟩
    change x ^ n = 0 at hn
    have hxpow : x ^ n ∈ P := by
      rw [hn]
      exact P.zero_mem
    exact hx (hP.mem_of_pow_mem n hxpow)
  let _ : Nontrivial S := not_subsingleton_iff_nontrivial.mp hsub
  have hdisj : Disjoint (Submonoid.powers x : Set R) (P : Set R) := by
    refine Set.disjoint_left.2 ?_
    intro z hzpow hzP
    rcases hzpow with ⟨n, rfl⟩
    exact hx (hP.mem_of_pow_mem n hzP)
  let Q : Ideal S := P.map φ
  have hQprime : Q.IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (M := Submonoid.powers x) (S := S) P hP hdisj
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q hQprime.ne_top
  have hP_le : P ≤ Ideal.comap φ M := by
    intro y hy
    exact hQM (Ideal.mem_map_of_mem φ hy)
  have hMmax : (Ideal.comap φ M).IsMaximal := by
    let _ : M.IsMaximal := hM
    exact Ideal.comap_isMaximal_of_surjective φ hsurj
  refine ⟨Ideal.comap φ M, ⟨⟨hP_le, hMmax⟩, ?_⟩⟩
  intro hxM
  have hxM' : φ x ∈ M := hxM
  have hunit : IsUnit (φ x) := by
    simpa [φ] using (IsLocalization.Away.algebraMap_isUnit (R := R) (S := S) x)
  exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M hxM' hunit)

abbrev ProductOfFields (A : Type u) (k : A → Type v) := ∀ a, k a

theorem productOfFields_element_unit_mul_idempotent
    (A : Type u) (k : A → Type v) [∀ a, Field (k a)] :
    ∀ f : ProductOfFields A k, IsUnitMulIdempotent f := by
  classical
  intro f
  let e : ProductOfFields A k := fun a => if f a = 0 then 0 else 1
  let u : ProductOfFields A k := fun a => if f a = 0 then 1 else f a
  change ∃ u e : ProductOfFields A k, IsUnit u ∧ IsIdempotentElem e ∧ f = u * e
  refine ⟨u, e, ?_, ?_, ?_⟩
  · rw [isUnit_iff_exists_inv]
    refine ⟨fun a => if f a = 0 then 1 else (f a)⁻¹, ?_⟩
    funext a
    by_cases hfa : f a = 0 <;> simp [u, hfa]
  · rw [isIdempotentElem_iff]
    funext a
    by_cases hfa : f a = 0 <;> simp [e, hfa]
  · funext a
    by_cases hfa : f a = 0 <;> simp [u, e, hfa]

theorem productOfFields_localization_identities
    (A : Type u) (k : A → Type v) [∀ a, Field (k a)]
    (f : ProductOfFields A k) :
    ∃ (u e : ProductOfFields A k),
      IsUnit u ∧ IsIdempotentElem e ∧ f = u * e ∧
      PrimeSpectrum.basicOpen f = PrimeSpectrum.basicOpen e ∧
        Nonempty (Localization.Away f ≃+* Localization.Away e) ∧
        Nonempty
          (Localization.Away e ≃+*
            (ProductOfFields A k ⧸ Ideal.span ({1 - e} : Set (ProductOfFields A k)))) ∧
        Function.Surjective
          (algebraMap (ProductOfFields A k) (Localization.Away f)) := by
  classical
  obtain ⟨u, e, hu, he, hfe⟩ :=
    productOfFields_element_unit_mul_idempotent A k f
  have hassoc : Associated f e := by
    rw [hfe]
    exact associated_unit_mul_left e u hu
  have hbasic :
      PrimeSpectrum.basicOpen f = PrimeSpectrum.basicOpen e := by
    ext p
    change f ∉ p.asIdeal ↔ e ∉ p.asIdeal
    rw [hfe, Ideal.unit_mul_mem_iff_mem _ hu]
  have haway : Nonempty (Localization.Away f ≃+* Localization.Away e) := by
    let : IsLocalization.Away f (Localization.Away e) :=
      IsLocalization.Away.of_associated hassoc.symm
    let awayFE : Localization.Away f ≃+* Localization.Away e :=
      (IsLocalization.algEquiv (Submonoid.powers f)
        (Localization.Away f) (Localization.Away e)).toRingEquiv
    exact ⟨awayFE⟩
  have hquot :
      Nonempty
        (Localization.Away e ≃+*
          (ProductOfFields A k ⧸ Ideal.span ({1 - e} : Set (ProductOfFields A k)))) := by
    let : IsLocalization.Away e
        (ProductOfFields A k ⧸ Ideal.span ({1 - e} : Set (ProductOfFields A k))) :=
      IsLocalization.away_of_isIdempotentElem he Ideal.mk_ker
        Ideal.Quotient.mk_surjective
    let awayE : Localization.Away e ≃+*
        (ProductOfFields A k ⧸ Ideal.span ({1 - e} : Set (ProductOfFields A k))) :=
      (IsLocalization.algEquiv (Submonoid.powers e)
        (Localization.Away e)
        (ProductOfFields A k ⧸ Ideal.span ({1 - e} : Set (ProductOfFields A k)))).toRingEquiv
    exact ⟨awayE⟩
  have hsurj :
      Function.Surjective
        (algebraMap (ProductOfFields A k) (Localization.Away f)) := by
    let : IsLocalization.Away e (Localization.Away f) :=
      IsLocalization.Away.of_associated hassoc
    exact IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he
  exact ⟨u, e, hu, he, hfe, hbasic, haway, hquot, hsurj⟩

theorem productOfFields_isJacobson
    (A : Type u) [Infinite A] (k : A → Type v) [∀ a, Field (k a)] :
    IsJacobsonRing (ProductOfFields A k) := by
  apply isJacobsonRing_of_localizationAwayIsQuotient
  intro f
  obtain ⟨u, e, hu, he, hfe, hbasic, haway, hquot, hsurj⟩ :=
    productOfFields_localization_identities A k f
  exact hsurj

private theorem localRing_with_two_prime_ideals_not_isJacobson_aux
    {R : Type u} [CommRing R] [IsLocalRing R]
    (h : ∃ p q : PrimeSpectrum R, p ≠ q) :
    ¬ IsJacobsonRing R := by
  intro hJ
  rcases h with ⟨p, q, hpq⟩
  have hpmax : p.asIdeal = IsLocalRing.maximalIdeal R := by
    have hpJ : p.asIdeal.jacobson = p.asIdeal :=
      IsJacobsonRing.out hJ p.2.isRadical
    exact hpJ.symm.trans
      (IsLocalRing.jacobson_eq_maximalIdeal p.asIdeal p.2.ne_top)
  have hqmax : q.asIdeal = IsLocalRing.maximalIdeal R := by
    have hqJ : q.asIdeal.jacobson = q.asIdeal :=
      IsJacobsonRing.out hJ q.2.isRadical
    exact hqJ.symm.trans
      (IsLocalRing.jacobson_eq_maximalIdeal q.asIdeal q.2.ne_top)
  apply hpq
  apply PrimeSpectrum.ext
  rw [hpmax, hqmax]

theorem finite_maximal_domain_isJacobson_iff_isField
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)] :
    IsJacobsonRing R ↔ IsField R := by
  classical
  constructor
  · intro hJ
    by_contra hfield
    let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
    let x : MaximalSpectrum R → R := fun m =>
      Classical.choose
        (Submodule.exists_mem_ne_zero_of_ne_bot
          (Ring.ne_bot_of_isMaximal_of_not_isField m.isMaximal hfield))
    have hx_mem (m : MaximalSpectrum R) : x m ∈ m.asIdeal := by
      exact (Classical.choose_spec
        (Submodule.exists_mem_ne_zero_of_ne_bot
          (Ring.ne_bot_of_isMaximal_of_not_isField m.isMaximal hfield))).1
    have hx_ne (m : MaximalSpectrum R) : x m ≠ 0 := by
      exact (Classical.choose_spec
        (Submodule.exists_mem_ne_zero_of_ne_bot
          (Ring.ne_bot_of_isMaximal_of_not_isField m.isMaximal hfield))).2
    let z : R := ∏ m : MaximalSpectrum R, x m
    have hz_ne : z ≠ 0 := by
      dsimp [z]
      exact Finset.prod_ne_zero_iff.mpr fun m _ => hx_ne m
    have hz_mem (M : Ideal R) (hM : M.IsMaximal) : z ∈ M := by
      let m : MaximalSpectrum R := ⟨M, hM⟩
      change (∏ n : MaximalSpectrum R, x n) ∈ m.asIdeal
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ m)]
      exact m.asIdeal.mul_mem_left _ (hx_mem m)
    have hz_jac : z ∈ Ideal.jacobson (⊥ : Ideal R) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      intro M hM
      exact hz_mem M hM.2
    have hz_bot : z ∈ (⊥ : Ideal R) := by
      rw [← IsJacobsonRing.out hJ Ideal.isRadical_bot_of_noZeroDivisors]
      exact hz_jac
    exact hz_ne (by simpa using hz_bot)
  · intro hfield
    let := hfield
    rw [isJacobsonRing_iff_prime_eq]
    intro P hP
    have hbotmax : (⊥ : Ideal R).IsMaximal :=
      (Ring.isField_iff_maximal_bot.mp hfield)
    have hPbot : P = (⊥ : Ideal R) :=
      (hbotmax.eq_of_le hP.ne_top bot_le).symm
    rw [hPbot]
    let : (⊥ : Ideal R).IsMaximal := hbotmax
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem discreteValuationRing_not_isJacobson
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ¬ IsJacobsonRing R := by
  apply localRing_with_two_prime_ideals_not_isJacobson_aux
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, (⊤ : PrimeSpectrum R), ?_⟩
  intro h
  apply IsDiscreteValuationRing.not_a_field R
  have h' := congrArg PrimeSpectrum.asIdeal h
  simpa using h'.symm

theorem localRing_with_two_prime_ideals_not_isJacobson
    {R : Type u} [CommRing R] [IsLocalRing R]
    (h : ∃ p q : PrimeSpectrum R, p ≠ q) :
    ¬ IsJacobsonRing R := by
  exact localRing_with_two_prime_ideals_not_isJacobson_aux h

/-! ## Residue fields and cardinality -/

@[instance_reducible]
noncomputable def residueFieldAlgebraOfBaseAlgebra
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (p : Ideal R) [p.IsPrime] : Algebra k p.ResidueField :=
  Algebra.compHom p.ResidueField (algebraMap k R)

@[instance_reducible]
noncomputable def residueFieldAlgebraOfMap
    {R S : Type*} [CommRing R] [CommRing S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (φ : R →+* S) (h : p = q.comap φ) :
    Algebra p.ResidueField q.ResidueField :=
  (Ideal.ResidueField.map p q φ h).toAlgebra

theorem maximal_residueField_isMaximal_of_algebraic
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (m : MaximalSpectrum R) (q : PrimeSpectrum S)
    (h : m.asIdeal = q.asIdeal.comap φ)
    (halg :
      letI : Algebra m.asIdeal.ResidueField q.asIdeal.ResidueField :=
        residueFieldAlgebraOfMap m.asIdeal q.asIdeal φ h
      Algebra.IsAlgebraic m.asIdeal.ResidueField q.asIdeal.ResidueField) :
    q.asIdeal.IsMaximal := by
  let : Algebra m.asIdeal.ResidueField q.asIdeal.ResidueField :=
    residueFieldAlgebraOfMap m.asIdeal q.asIdeal φ h
  let A : Subalgebra m.asIdeal.ResidueField q.asIdeal.ResidueField :=
    { carrier := Set.range (algebraMap S q.asIdeal.ResidueField)
      zero_mem' := ⟨0, map_zero _⟩
      one_mem' := ⟨1, map_one _⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x * y, by simp⟩
      algebraMap_mem' := by
        intro a
        obtain ⟨r, rfl⟩ := m.asIdeal.algebraMap_residueField_surjective a
        refine ⟨φ r, ?_⟩
        change algebraMap S q.asIdeal.ResidueField (φ r) =
          Ideal.ResidueField.map m.asIdeal q.asIdeal φ h
            (algebraMap R m.asIdeal.ResidueField r)
        exact (Ideal.ResidueField.map_algebraMap m.asIdeal q.asIdeal φ h r).symm }
  have hA : IsField A :=
    @Subalgebra.isField_of_algebraic
      m.asIdeal.ResidueField q.asIdeal.ResidueField _ _ _ A halg
  apply Ideal.Quotient.maximal_of_isField q.asIdeal
  have hnontriv : Nontrivial (S ⧸ q.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr q.2.ne_top
  refine ⟨hnontriv.exists_pair_ne, mul_comm, ?_⟩
  intro a ha
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
  let z : A := ⟨algebraMap S q.asIdeal.ResidueField s, ⟨s, rfl⟩⟩
  have hz : (z : q.asIdeal.ResidueField) ≠ 0 := by
    intro hz
    apply ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.algebraMap_residueField_eq_zero.mp
      (by simpa [z, Ideal.algebraMap_quotient_residueField_mk] using hz)
  have hzA : z ≠ 0 := by
    intro hzero
    apply hz
    exact congrArg Subtype.val hzero
  obtain ⟨b, hb⟩ := hA.mul_inv_cancel hzA
  obtain ⟨t, ht⟩ := b.property
  refine ⟨Ideal.Quotient.mk q.asIdeal t, ?_⟩
  apply Ideal.injective_algebraMap_quotient_residueField
  simpa [z, ht, Ideal.algebraMap_quotient_residueField_mk] using
    congrArg Subtype.val hb

theorem linear_operator_has_noninvertible_monic_polynomial
    {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Nontrivial V]
    (hcard : Module.rank k V < Cardinal.mk k) :
    ∀ T : Module.End k V,
      ∃ P : Polynomial k, P.Monic ∧ ¬ IsUnit (Polynomial.aeval T P) := by
  sorry

theorem uncountable_nullstellensatz
    {k S I : Type u} [Field k] [CommRing S] [Algebra k S]
    (x : I → S) (hgen : Algebra.adjoin k (Set.range x) = ⊤)
    (hcard : Cardinal.mk I < Cardinal.mk k) :
    (∀ m : MaximalSpectrum S,
        letI : Algebra k m.asIdeal.ResidueField :=
          residueFieldAlgebraOfBaseAlgebra (k := k) m.asIdeal
        Algebra.IsAlgebraic k m.asIdeal.ResidueField) ∧
      IsJacobsonRing S := by
  sorry

theorem baseChange_uncountable_nullstellensatz
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Field K] [Algebra k K]
    (hcard : Cardinal.mk S < Cardinal.mk K) :
    (∀ m : MaximalSpectrum (K ⊗[k] S),
        letI : Algebra K m.asIdeal.ResidueField :=
          residueFieldAlgebraOfBaseAlgebra (k := K) m.asIdeal
        Algebra.IsAlgebraic K m.asIdeal.ResidueField) ∧
      IsJacobsonRing (K ⊗[k] S) := by
  sorry

/-! ## The countable-field counterexample -/

abbrev CountableTrickIndex (k : Type u) [Field k] :=
  {f : Polynomial k // f ≠ 0}

abbrev CountableTrickRing (k : Type u) [Field k] :=
  MvPolynomial (CountableTrickIndex k) (Polynomial k)

def countableTrickRelation {k : Type u} [Field k]
    (i : CountableTrickIndex k) : CountableTrickRing k :=
  MvPolynomial.C i.1 * MvPolynomial.X i - 1

def countableTrickIdeal {k : Type u} [Field k] : Ideal (CountableTrickRing k) :=
  Ideal.span (Set.range countableTrickRelation)

theorem countableTrickIdeal_isProper {k : Type u} [Field k] :
    countableTrickIdeal (k := k) ≠ ⊤ := by
  sorry

theorem countableTrick_exists_maximalIdeal {k : Type u} [Field k] :
    ∃ m : MaximalSpectrum (CountableTrickRing k),
      countableTrickIdeal (k := k) ≤ m.asIdeal := by
  sorry

theorem countableTrick_quotient_is_rational_function_field
    {k : Type u} [Field k]
    (m : MaximalSpectrum (CountableTrickRing k))
    (hm : countableTrickIdeal (k := k) ≤ m.asIdeal) :
    Nonempty ((CountableTrickRing k ⧸ m.asIdeal) ≃+* FractionRing (Polynomial k)) ∧
      ¬ Algebra.IsAlgebraic k (CountableTrickRing k ⧸ m.asIdeal) := by
  sorry

/-! ## Localizing, quotienting, and finite-type permanence -/

noncomputable def maximalIdealLocalizationOrderIso
    {R : Type u} [CommRing R] [IsJacobsonRing R] (f : R) :
    {p : Ideal (Localization.Away f) // p.IsMaximal} ≃o
      {p : Ideal R // p.IsMaximal ∧ f ∉ p} :=
  IsLocalization.orderIsoOfMaximal (R := R) (S := Localization.Away f) f

theorem localizationAway_isJacobson_and_maximal_correspondence
    {R : Type u} [CommRing R] [IsJacobsonRing R] (f : R) :
    IsJacobsonRing (Localization.Away f) ∧
      Nonempty
        ({p : Ideal (Localization.Away f) // p.IsMaximal} ≃o
          {p : Ideal R // p.IsMaximal ∧ f ∉ p}) := by
  sorry

def integerTwoIdeal : Ideal ℤ :=
  Ideal.span ({(2 : ℤ)} : Set ℤ)

instance integerTwoIdeal_isMaximal : integerTwoIdeal.IsMaximal := by
  simpa [integerTwoIdeal] using
    (@Int.ideal_span_isMaximal_of_prime 2 ⟨Nat.prime_two⟩)

instance integerTwoIdeal_isPrime : integerTwoIdeal.IsPrime :=
  integerTwoIdeal_isMaximal.isPrime

abbrev ZLocalizedAtTwo :=
  Localization (integerTwoIdeal.primeCompl)

abbrev ZLocalizedAtTwoAtTwo :=
  Localization.Away (algebraMap ℤ ZLocalizedAtTwo (2 : ℤ))

theorem zLocalizedAtTwo_is_rational
    : Nonempty (ZLocalizedAtTwoAtTwo ≃+* ℚ) := by
  sorry

theorem zLocalizedAtTwo_closedPoint_maps_to_generic_point
    : ∃ e : ZLocalizedAtTwoAtTwo ≃+* ℚ,
        PrimeSpectrum.comap
            (e.toRingHom.comp (algebraMap ZLocalizedAtTwo ZLocalizedAtTwoAtTwo))
            (⟨⊥, inferInstance⟩ : PrimeSpectrum ℚ) =
          (⟨⊥, inferInstance⟩ : PrimeSpectrum ZLocalizedAtTwo) := by
  sorry

abbrev RationalLocalizationOfIntegers :=
  Localization (nonZeroDivisors ℤ)

theorem rationalLocalizationOfIntegers_is_rational
    : Nonempty (RationalLocalizationOfIntegers ≃+* ℚ) := by
  sorry

theorem rationalLocalization_closedPoint_maps_to_generic_point
    : ∃ e : RationalLocalizationOfIntegers ≃+* ℚ,
        PrimeSpectrum.comap
            (e.toRingHom.comp (algebraMap ℤ RationalLocalizationOfIntegers))
            (⟨⊥, inferInstance⟩ : PrimeSpectrum ℚ) =
          (⟨⊥, inferInstance⟩ : PrimeSpectrum ℤ) := by
  sorry

theorem quotient_of_isJacobson_isJacobson_with_maximal_correspondence
    {R : Type u} [CommRing R] [IsJacobsonRing R] (I : Ideal R) :
    IsJacobsonRing (R ⧸ I) ∧
      ∃ e :
          {M : Ideal (R ⧸ I) // M.IsMaximal} ≃
            {N : Ideal R // N.IsMaximal ∧ I ≤ N},
        (∀ M, Ideal.map (Ideal.Quotient.mk I) (e M).1 = M.1) ∧
          (∀ N, Ideal.comap (Ideal.Quotient.mk I) (e.symm N).1 = N.1) := by
  sorry

theorem jacobson_subring_of_finiteType_field
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    [IsJacobsonRing R] [Algebra.FiniteType R K]
    (hRK : Function.Injective (algebraMap R K)) :
    IsField R ∧ Module.Finite R K := by
  sorry

theorem finiteType_map_preserves_jacobson_closedPoints_and_residue_finiteness
    {R S : Type u} [CommRing R] [CommRing S] [IsJacobsonRing R]
    (φ : R →+* S) (hφ : RingHom.FiniteType φ) :
    IsJacobsonRing S ∧
      (∀ q : MaximalSpectrum S, (q.asIdeal.comap φ).IsMaximal) ∧
      (∀ q : MaximalSpectrum S,
        let p := q.asIdeal.comap φ
        letI : p.IsPrime := Ideal.comap_isPrime φ q.asIdeal
        letI : Algebra p.ResidueField q.asIdeal.ResidueField :=
          residueFieldAlgebraOfMap p q.asIdeal φ rfl
        Module.Finite p.ResidueField q.asIdeal.ResidueField) := by
  sorry

theorem finiteType_algebra_over_integers_isJacobson
    {A : Type u} [CommRing A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] :
    IsJacobsonRing A := by
  sorry

/-! ## Constructible images and closed points -/

abbrev ConstructibleSet (X : Type u) [TopologicalSpace X] :=
  {E : Set X // IsConstructible E}

def closedPointPart {X : Type u} [TopologicalSpace X] (E : Set X) : Set X :=
  E ∩ closedPoints X

def closedPointsOfSubset {X : Type u} [TopologicalSpace X] (E : Set X) : Set X :=
  Set.range (fun x : closedPoints (↥E) => (x.1 : X))

theorem finiteType_constructible_image_isConstructible
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (φ : R →+* S) (hφ : RingHom.FiniteType φ)
    {E : Set (PrimeSpectrum S)} (hE : IsConstructible E) :
    IsConstructible (PrimeSpectrum.comap φ '' E) := by
  sorry

theorem jacobson_constructible_image_closedPoint_formula
    {R S : Type u} [CommRing R] [CommRing S]
    [IsJacobsonRing R] [IsJacobsonRing S]
    (φ : R →+* S) (hφ : RingHom.FiniteType φ)
    {E : Set (PrimeSpectrum S)} (hE : IsConstructible E) :
    closedPointsOfSubset (PrimeSpectrum.comap φ '' E) =
        PrimeSpectrum.comap φ '' (E ∩ closedPoints (PrimeSpectrum S)) ∧
      PrimeSpectrum.comap φ '' (E ∩ closedPoints (PrimeSpectrum S)) =
        closedPointPart (PrimeSpectrum.comap φ '' E) ∧
      ∀ ξ : PrimeSpectrum R,
        ξ ∈ PrimeSpectrum.comap φ '' E ↔
          closure ({ξ} : Set (PrimeSpectrum R)) =
            closure
              (closure ({ξ} : Set (PrimeSpectrum R)) ∩
                (PrimeSpectrum.comap φ ''
                  (E ∩ closedPoints (PrimeSpectrum S)))) := by
  sorry

theorem noetherian_jacobson_constructible_correspondence_diagram
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsJacobsonRing R]
    (φ : R →+* S) (hφ : RingHom.FiniteType φ) :
    ∃ (imageYX : ConstructibleSet (PrimeSpectrum S) →
          ConstructibleSet (PrimeSpectrum R))
      (imageY₀X₀ : ConstructibleSet (closedPoints (PrimeSpectrum S)) →
          ConstructibleSet (closedPoints (PrimeSpectrum R)))
      (traceX : ConstructibleSet (PrimeSpectrum R) ≃
          ConstructibleSet (closedPoints (PrimeSpectrum R)))
      (traceY : ConstructibleSet (PrimeSpectrum S) ≃
          ConstructibleSet (closedPoints (PrimeSpectrum S))),
      (∀ E, (imageYX E : Set (PrimeSpectrum R)) =
        PrimeSpectrum.comap φ '' (E : Set (PrimeSpectrum S))) ∧
      (∀ E, Set.image (Subtype.val : closedPoints (PrimeSpectrum R) →
          PrimeSpectrum R) (imageY₀X₀ E : Set (closedPoints (PrimeSpectrum R))) =
        PrimeSpectrum.comap φ ''
          Set.image (Subtype.val : closedPoints (PrimeSpectrum S) →
            PrimeSpectrum S) (E : Set (closedPoints (PrimeSpectrum S)))) ∧
      (∀ E, Set.image (Subtype.val : closedPoints (PrimeSpectrum R) →
          PrimeSpectrum R) (traceX E : Set (closedPoints (PrimeSpectrum R))) =
        closedPointPart (E : Set (PrimeSpectrum R))) ∧
      (∀ E, Set.image (Subtype.val : closedPoints (PrimeSpectrum S) →
          PrimeSpectrum S) (traceY E : Set (closedPoints (PrimeSpectrum S))) =
        closedPointPart (E : Set (PrimeSpectrum S))) ∧
      (∀ E, traceX (imageYX E) = imageY₀X₀ (traceY E)) := by
  sorry

/-! ## The two-axis and product-zero matrix examples -/

abbrev ProductZeroPolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

def productZeroRelationIdeal (k : Type u) [Field k] :
    Ideal (ProductZeroPolynomialRing k) :=
  Ideal.span
    {MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1}

abbrev ProductZeroRing (k : Type u) [Field k] :=
  ProductZeroPolynomialRing k ⧸ productZeroRelationIdeal k

def productZeroXAxisIdeal (k : Type u) [Field k] :
    Ideal (ProductZeroPolynomialRing k) :=
  Ideal.span {MvPolynomial.X (R := k) 0}

def productZeroYAxisIdeal (k : Type u) [Field k] :
    Ideal (ProductZeroPolynomialRing k) :=
  Ideal.span {MvPolynomial.X (R := k) 1}

theorem productZero_minimalPrimes_are_the_two_axes
    (k : Type u) [Field k] :
    (productZeroRelationIdeal k).minimalPrimes =
      {productZeroXAxisIdeal k, productZeroYAxisIdeal k} := by
  sorry

theorem productZero_spectrum_has_two_irreducible_components
    (k : Type u) [Field k] :
    Nonempty
      (Fin 2 ≃ irreducibleComponents (PrimeSpectrum (ProductZeroRing k))) := by
  sorry

abbrev ProductZeroSolution (k : Type u) [Field k] :=
  {p : k × k // p.1 * p.2 = 0}

def productZeroXAxis (k : Type u) [Field k] : Set (k × k) :=
  {p | p.1 = 0}

def productZeroYAxis (k : Type u) [Field k] : Set (k × k) :=
  {p | p.2 = 0}

theorem productZero_solution_set_is_union_of_axes
    (k : Type u) [Field k] :
    {p : k × k | p.1 * p.2 = 0} =
      productZeroXAxis k ∪ productZeroYAxis k := by
  ext p
  simp [productZeroXAxis, productZeroYAxis, mul_eq_zero]

theorem productZero_closedPoints_are_algebraic_solutions
    (k : Type u) [Field k] (hk : IsAlgClosed k) :
    Nonempty
      (closedPoints (PrimeSpectrum (ProductZeroRing k)) ≃ ProductZeroSolution k) := by
  sorry

/-! The product-zero matrix example. -/

abbrev Matrix2 (k : Type u) := Matrix (Fin 2) (Fin 2) k
abbrev MatrixPairPolynomial (k : Type u) [CommSemiring k] :=
  MvPolynomial (Fin 8) k

def matrixPairVariable {k : Type u} [Field k] (i : Fin 8) :
    MatrixPairPolynomial k :=
  MvPolynomial.X (R := k) i

def matrixPairX11 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 0
def matrixPairX12 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 1
def matrixPairX21 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 2
def matrixPairX22 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 3
def matrixPairY11 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 4
def matrixPairY12 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 5
def matrixPairY21 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 6
def matrixPairY22 {k : Type u} [Field k] : MatrixPairPolynomial k := matrixPairVariable (k := k) 7

def matrixPairProductEquations {k : Type u} [Field k] :
    Set (MatrixPairPolynomial k) :=
  { matrixPairX11 (k := k) * matrixPairY11 (k := k) + matrixPairX12 (k := k) * matrixPairY21 (k := k),
    matrixPairX11 (k := k) * matrixPairY12 (k := k) + matrixPairX12 (k := k) * matrixPairY22 (k := k),
    matrixPairX21 (k := k) * matrixPairY11 (k := k) + matrixPairX22 (k := k) * matrixPairY21 (k := k),
    matrixPairX21 (k := k) * matrixPairY12 (k := k) + matrixPairX22 (k := k) * matrixPairY22 (k := k) }

def matrixProductIdeal {k : Type u} [Field k] : Ideal (MatrixPairPolynomial k) :=
  Ideal.span (matrixPairProductEquations (k := k))

abbrev MatrixPairRing (k : Type u) [Field k] :=
  MatrixPairPolynomial k ⧸ matrixProductIdeal (k := k)

abbrev MatrixPairSolution (k : Type u) [Field k] :=
  {P : Matrix2 k × Matrix2 k // P.1 * P.2 = 0}

theorem matrixPair_polynomial_closedPoints_are_matrix_pairs
    (k : Type u) [Field k] (hk : IsAlgClosed k) :
    Nonempty
      (closedPoints (PrimeSpectrum (MatrixPairPolynomial k)) ≃
        (Matrix2 k × Matrix2 k)) := by
  sorry

theorem matrixPair_closedPoints_are_product_zero_solutions
    (k : Type u) [Field k] (hk : IsAlgClosed k) :
    Nonempty
      (closedPoints (PrimeSpectrum (MatrixPairRing k)) ≃ MatrixPairSolution k) := by
  sorry

def matrixPairDetX {k : Type u} [Field k] : MatrixPairPolynomial k :=
  matrixPairX11 (k := k) * matrixPairX22 (k := k) -
    matrixPairX12 (k := k) * matrixPairX21 (k := k)

def matrixPairDetY {k : Type u} [Field k] : MatrixPairPolynomial k :=
  matrixPairY11 (k := k) * matrixPairY22 (k := k) -
    matrixPairY12 (k := k) * matrixPairY21 (k := k)

def matrixProductRankTwoComponentIdeal {k : Type u} [Field k] :
    Ideal (MatrixPairPolynomial k) :=
  Ideal.span {matrixPairY11 (k := k), matrixPairY12 (k := k), matrixPairY21 (k := k), matrixPairY22 (k := k)}

def matrixProductRankOneComponentIdeal {k : Type u} [Field k] :
    Ideal (MatrixPairPolynomial k) :=
  Ideal.span
    (matrixPairProductEquations (k := k) ∪
      {matrixPairDetX (k := k), matrixPairDetY (k := k)})

def matrixProductRankZeroComponentIdeal {k : Type u} [Field k] :
    Ideal (MatrixPairPolynomial k) :=
  Ideal.span {matrixPairX11 (k := k), matrixPairX12 (k := k), matrixPairX21 (k := k), matrixPairX22 (k := k)}

def matrixProductDeterminantalIdeal {k : Type u} [Field k] :
    Ideal (MatrixPairPolynomial k) :=
  matrixProductIdeal (k := k) ⊔
    Ideal.span {matrixPairDetX (k := k), matrixPairDetY (k := k)}

theorem matrixProduct_equations_are_matrix_product_entries
    {k : Type u} [Field k] (X Y : Matrix2 k) :
    X * Y = 0 ↔
      (X 0 0 * Y 0 0 + X 0 1 * Y 1 0 = 0) ∧
      (X 0 0 * Y 0 1 + X 0 1 * Y 1 1 = 0) ∧
      (X 1 0 * Y 0 0 + X 1 1 * Y 1 0 = 0) ∧
      (X 1 0 * Y 0 1 + X 1 1 * Y 1 1 = 0) := by
  sorry

def matrixPairAction {k : Type u} [Field k]
    (g : Matrix.GeneralLinearGroup (Fin 2) k ×
      Matrix.GeneralLinearGroup (Fin 2) k × Matrix.GeneralLinearGroup (Fin 2) k)
    (P : Matrix2 k × Matrix2 k) : Matrix2 k × Matrix2 k :=
  let g₁ := g.1
  let g₂ := g.2.1
  let g₃ := g.2.2
  ((g₁ : Matrix2 k) * P.1 * (↑(g₂⁻¹) : Matrix2 k),
    (g₂ : Matrix2 k) * P.2 * (↑(g₃⁻¹) : Matrix2 k))

theorem matrixPairAction_one (k : Type u) [Field k] (P : Matrix2 k × Matrix2 k) :
    matrixPairAction (1, 1, 1) P = P := by
  sorry

theorem matrixPairAction_mul (k : Type u) [Field k]
    (g h : Matrix.GeneralLinearGroup (Fin 2) k ×
      Matrix.GeneralLinearGroup (Fin 2) k × Matrix.GeneralLinearGroup (Fin 2) k)
    (P : Matrix2 k × Matrix2 k) :
    matrixPairAction (g * h) P = matrixPairAction g (matrixPairAction h P) := by
  sorry

instance matrixPairAction_mulAction {k : Type u} [Field k] :
    MulAction
      (Matrix.GeneralLinearGroup (Fin 2) k ×
        Matrix.GeneralLinearGroup (Fin 2) k × Matrix.GeneralLinearGroup (Fin 2) k)
      (Matrix2 k × Matrix2 k) where
  smul := matrixPairAction
  one_smul := matrixPairAction_one k
  mul_smul := matrixPairAction_mul k

theorem matrixProduct_minimalPrime_components
    (k : Type u) [Field k] :
    (matrixProductIdeal (k := k)).minimalPrimes =
      {matrixProductRankTwoComponentIdeal,
        matrixProductRankOneComponentIdeal,
        matrixProductRankZeroComponentIdeal} := by
  sorry

theorem matrixProduct_components_are_prime
    (k : Type u) [Field k] :
    (matrixProductRankTwoComponentIdeal (k := k)).IsPrime ∧
      (matrixProductRankOneComponentIdeal (k := k)).IsPrime ∧
      (matrixProductRankZeroComponentIdeal (k := k)).IsPrime := by
  sorry

theorem matrixProduct_determinantal_component
    (k : Type u) [Field k] :
    matrixProductDeterminantalIdeal (k := k) =
      matrixProductRankOneComponentIdeal (k := k) := by
  sorry

theorem matrixProduct_zero_rank_cases
    {k : Type u} [Field k] (X Y : Matrix2 k) (hXY : X * Y = 0) :
    (X.rank = 2 ∧ Y = 0) ∨ (X.rank = 1 ∧ X.det = 0 ∧ Y.det = 0) ∨ X = 0 := by
  sorry

theorem matrixProduct_rank_normal_forms
    {k : Type u} [Field k] (X : Matrix2 k) :
    (X.rank = 2 →
      ∃ g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) k,
        (g₁ : Matrix2 k) * X * (↑(g₂⁻¹) : Matrix2 k) = 1) ∧
    (X.rank = 1 →
      ∃ g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) k,
        (g₁ : Matrix2 k) * X * (↑(g₂⁻¹) : Matrix2 k) =
          Matrix.diagonal (fun i : Fin 2 => if i = 0 then 1 else 0)) := by
  sorry

abbrev MatrixTriplePolynomial (k : Type u) [CommSemiring k] :=
  MvPolynomial (Fin 12) k

def matrixTripleDetX {k : Type u} [Field k] : MatrixTriplePolynomial k :=
  MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 3 -
    MvPolynomial.X (R := k) 1 * MvPolynomial.X (R := k) 2

def matrixTripleDetY {k : Type u} [Field k] : MatrixTriplePolynomial k :=
  MvPolynomial.X (R := k) 4 * MvPolynomial.X (R := k) 7 -
    MvPolynomial.X (R := k) 5 * MvPolynomial.X (R := k) 6

def matrixTripleDetZ {k : Type u} [Field k] : MatrixTriplePolynomial k :=
  MvPolynomial.X (R := k) 8 * MvPolynomial.X (R := k) 11 -
    MvPolynomial.X (R := k) 9 * MvPolynomial.X (R := k) 10

abbrev GeneralLinearTripleCoordinateRing (k : Type u) [Field k] :=
  Localization (Submonoid.powers
    (matrixTripleDetX (k := k) * matrixTripleDetY (k := k) * matrixTripleDetZ (k := k)))

theorem generalLinearTripleCoordinateRing_isDomain
    (k : Type u) [Field k] :
    IsDomain (GeneralLinearTripleCoordinateRing k) := by
  sorry

theorem generalLinearTriple_spectrum_isIrreducible
    (k : Type u) [Field k] :
    IsIrreducible (Set.univ : Set (PrimeSpectrum (GeneralLinearTripleCoordinateRing k))) := by
  sorry

/-! ## Idempotent matrices -/

abbrev IdempotentMatrixPolynomial (k : Type u) [CommSemiring k] (n : ℕ) :=
  MvPolynomial (Fin n × Fin n) k

def genericIdempotentMatrix {k : Type u} [Field k] (n : ℕ) :
    Matrix (Fin n) (Fin n) (IdempotentMatrixPolynomial k n) :=
  fun i j => MvPolynomial.X (R := k) (i, j)

def idempotentMatrixEquations {k : Type u} [Field k] (n : ℕ) :
    Set (IdempotentMatrixPolynomial k n) :=
  Set.range (fun ij : Fin n × Fin n =>
    (∑ l : Fin n,
      genericIdempotentMatrix (k := k) n ij.1 l * genericIdempotentMatrix (k := k) n l ij.2) -
      genericIdempotentMatrix (k := k) n ij.1 ij.2)

def idempotentMatrixIdeal {k : Type u} [Field k] (n : ℕ) :
    Ideal (IdempotentMatrixPolynomial k n) :=
  Ideal.span (idempotentMatrixEquations (k := k) n)

abbrev IdempotentMatrixRing (k : Type u) [Field k] (n : ℕ) :=
  IdempotentMatrixPolynomial k n ⧸ idempotentMatrixIdeal (k := k) n

def diagonalIdempotent {k : Type u} [Field k] (n r : ℕ) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.diagonal (fun i : Fin n => if i.1 < r then 1 else 0)

def matrixConjugation {k : Type u} [Field k] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (T : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k :=
  (g : Matrix (Fin n) (Fin n) k) * T * (↑(g⁻¹) : Matrix (Fin n) (Fin n) k)

def matrixTrace {k : Type u} [Field k] {n : ℕ}
    (T : Matrix (Fin n) (Fin n) k) : k :=
  ∑ i, T i i

def idempotentMatrixOrbit {k : Type u} [Field k] (n : ℕ)
    (T : Matrix (Fin n) (Fin n) k) : Set (Matrix (Fin n) (Fin n) k) :=
  Set.range (fun g : Matrix.GeneralLinearGroup (Fin n) k => matrixConjugation n g T)

def thirdExteriorPowerTrace {k : Type u} [Field k]
    (T : Matrix (Fin 3) (Fin 3) k) : k :=
  T.det

theorem idempotent_matrix_conjugate_to_diagonal
    {k : Type u} [Field k] (n : ℕ) (T : Matrix (Fin n) (Fin n) k)
    (hT : T * T = T) :
    ∃ r : Fin (n + 1), ∃ g : Matrix.GeneralLinearGroup (Fin n) k,
      T.rank = r.1 ∧
      matrixConjugation n g T =
        Matrix.diagonal (fun i : Fin n => if i.1 < r.1 then 1 else 0) := by
  sorry

theorem idempotent_matrix_rank_orbits_are_components
    (k : Type u) [Field k] (n : ℕ) :
    Nonempty (Fin (n + 1) ≃
      irreducibleComponents (PrimeSpectrum (IdempotentMatrixRing k n))) := by
  sorry

theorem idempotent_matrix_different_rank_orbits_disjoint
    {k : Type u} [Field k] (n r s : ℕ)
    (hr : r ≤ n) (hs : s ≤ n) (hrs : r ≠ s) :
    Disjoint
      (idempotentMatrixOrbit (k := k) n
        (Matrix.diagonal (fun i : Fin n => if i.1 < r then 1 else 0)))
      (idempotentMatrixOrbit (k := k) n
        (Matrix.diagonal (fun i : Fin n => if i.1 < s then 1 else 0))) := by
  sorry

theorem matrixTrace_diagonalIdempotent
    {k : Type u} [Field k] (n r : ℕ) (hr : r ≤ n) :
    matrixTrace (k := k)
        (Matrix.diagonal (fun i : Fin n => if i.1 < r then (1 : k) else 0)) = r := by
  sorry

theorem matrixTrace_separates_idempotent_ranks
    {k : Type u} [Field k] [CharZero k] (n r s : ℕ)
    (hr : r ≤ n) (hs : s ≤ n) (hrs : r ≠ s) :
    matrixTrace (k := k)
        (Matrix.diagonal (fun i : Fin n => if i.1 < r then (1 : k) else 0)) ≠
      matrixTrace (k := k)
        (Matrix.diagonal (fun i : Fin n => if i.1 < s then (1 : k) else 0)) := by
  sorry

theorem characteristic_three_trace_does_not_separate_zero_and_full_rank
    {k : Type u} [Field k] [CharP k 3] :
    matrixTrace (k := k) (Matrix.diagonal (fun i : Fin 3 => (1 : k))) =
      matrixTrace (k := k) (Matrix.diagonal (fun i : Fin 3 => (0 : k))) := by
  sorry

theorem characteristic_three_third_exterior_power_trace_separates_full_rank
    {k : Type u} [Field k] [CharP k 3] :
    thirdExteriorPowerTrace (k := k)
          (Matrix.diagonal (fun i : Fin 3 => (1 : k))) = 1 ∧
      ∀ r : ℕ, r < 3 →
        thirdExteriorPowerTrace (k := k)
          (Matrix.diagonal (fun i : Fin 3 => if i.1 < r then (1 : k) else 0)) = 0 := by
  sorry

end

end Formalization.Books.Algebra.Unit35
