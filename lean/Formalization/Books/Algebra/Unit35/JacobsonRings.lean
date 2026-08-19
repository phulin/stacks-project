import Formalization.Books.Algebra.Unit30.MoreOnImages
import Formalization.Books.Algebra.Unit31.NoetherianRings
import Formalization.Books.Algebra.Unit34.HilbertNullstellensatz
import Formalization.Books.Topology.Unit18.JacobsonSpaces
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.FreeAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Extension.Generators
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
open scoped BigOperators Polynomial TensorProduct

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
  classical
  intro T
  by_contra h
  have hunit : ∀ P : Polynomial k, P.Monic → IsUnit (Polynomial.aeval T P) := by
    intro P hP
    by_contra hP'
    exact h ⟨P, hP, hP'⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let A : k → Module.End k V := fun a =>
    Polynomial.aeval T (Polynomial.X - Polynomial.C a)
  let U : k → Module.End k V := fun a =>
    (hunit (Polynomial.X - Polynomial.C a) (Polynomial.monic_X_sub_C a)).unit.inv
  have hAU (a : k) : A a * U a = 1 := by
    dsimp [A, U]
    exact (hunit (Polynomial.X - Polynomial.C a) (Polynomial.monic_X_sub_C a)).mul_val_inv
  have hunit_of_ne_zero (p : Polynomial k) (hp : p ≠ 0) :
      IsUnit (Polynomial.aeval T p) := by
    have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hmonic : (p * Polynomial.C p.leadingCoeff⁻¹).Monic :=
      Polynomial.monic_mul_leadingCoeff_inv hp
    have hC : IsUnit (Polynomial.aeval T (Polynomial.C p.leadingCoeff)) :=
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc)).map (Polynomial.aeval T)
    have heq : p = (p * Polynomial.C p.leadingCoeff⁻¹) * Polynomial.C p.leadingCoeff := by
      rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hlc, Polynomial.C_1, mul_one]
    rw [heq, map_mul]
    exact (hunit _ hmonic).mul hC
  have hli : LinearIndependent k (fun a : k => U a v) := by
    rw [linearIndependent_iff']
    intro s m hm i hi
    by_contra hmi
    let p : Polynomial k :=
      s.sum fun j => Polynomial.C (m j) *
        (s.erase j).prod fun l => (Polynomial.X - Polynomial.C l)
    have hprod (j : k) (hj : j ∈ s) :
        (Polynomial.aeval T (s.prod fun l => (Polynomial.X - Polynomial.C l))) * U j =
          Polynomial.aeval T ((s.erase j).prod fun l => (Polynomial.X - Polynomial.C l)) := by
      rw [← s.prod_erase_mul _ hj, map_mul, mul_assoc, hAU, mul_one]
    have hpv : (Polynomial.aeval T p) v = 0 := by
      have hm' := congrArg (Polynomial.aeval T (s.prod fun l =>
        (Polynomial.X - Polynomial.C l))) hm
      simp only [map_sum, map_smul, map_zero] at hm'
      have hm'' :
          (s.sum (fun j => m j •
            (Polynomial.aeval T ((s.erase j).prod fun l =>
              (Polynomial.X - Polynomial.C l))) v)) = 0 := by
        calc
          (s.sum (fun j => m j •
              (Polynomial.aeval T ((s.erase j).prod fun l =>
                (Polynomial.X - Polynomial.C l))) v)) =
              (s.sum (fun j => m j •
                ((Polynomial.aeval T (s.prod fun l =>
                  (Polynomial.X - Polynomial.C l)) * U j) v))) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hprod j hj]
          _ = 0 := by
            simpa only [Module.End.mul_apply] using hm'
      calc
        (Polynomial.aeval T p) v =
            s.sum fun j => m j •
              (Polynomial.aeval T ((s.erase j).prod fun l =>
                (Polynomial.X - Polynomial.C l))) v := by
          simp [p, map_sum, map_mul, Module.End.mul_apply]
        _ = 0 := hm''
    have h2 : ∀ j ∈ s.erase i,
        m j * ((s.erase j).prod fun l : k => i - l) = 0 := by
      intro j hj
      have hij : i ∈ s.erase j :=
        Finset.mem_erase_of_ne_of_mem (Finset.ne_of_mem_erase hj).symm hi
      rw [← (s.erase j).prod_erase_mul _ hij]
      rw [sub_self]
      simp only [mul_zero]
    have hpeval : Polynomial.eval i p =
        m i * (s.erase i).prod fun j => (i - j) := by
      simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X]
      rw [← s.sum_erase_add _ hi]
      simp_rw [Finset.sum_eq_zero h2]
      rw [zero_add]
    have hprod_ne : ((s.erase i).prod fun j => (i - j)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hj).symm
    have hp : p ≠ 0 := by
      intro hp
      have := congrArg (Polynomial.eval i) hp
      rw [hpeval] at this
      have this' : m i * (s.erase i).prod (fun j => i - j) = 0 := by
        simpa using this
      exact hmi
        ((eq_zero_or_eq_zero_of_mul_eq_zero this').resolve_right hprod_ne)
    have hpu := hunit_of_ne_zero p hp
    have hp_inj : Function.Injective (Polynomial.aeval T p) :=
      (Module.End.isUnit_iff _).mp hpu |>.1
    apply hv
    apply hp_inj
    simp [hpv]
  exact (not_lt_of_ge hli.cardinal_le_rank) hcard

private theorem algebraic_of_small_generators
    {k L J : Type u} [Field k] [Field L] [Algebra k L]
    (P : Algebra.Generators k L J) (hcard : Cardinal.mk J < Cardinal.mk k) :
    Algebra.IsAlgebraic k L := by
  have hgen : Algebra.adjoin k (Set.range P.val) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).mpr P.aeval_val_surjective
  by_cases hJ : Finite J
  · let _ := hJ
    let _ : Algebra.FiniteType k L := P.finiteType
    let _ : Module.Finite k L := finite_of_finite_type_of_isJacobsonRing k L
    exact Algebra.IsAlgebraic.of_finite k L
  · have hJ' : Infinite J := not_finite_iff_infinite.mp hJ
    let _ := hJ'
    have h0 : Cardinal.aleph0 < Cardinal.mk k :=
      lt_of_le_of_lt (Cardinal.aleph0_le_mk J) hcard
    have hrank : Module.rank k L < Cardinal.mk k := by
      calc
        Module.rank k L = Module.rank k (⊤ : Subalgebra k L) :=
          Subalgebra.rank_top.symm
        _ = Module.rank k (Algebra.adjoin k (Set.range P.val)) := by rw [hgen]
        _ ≤ max (Cardinal.mk (Set.range P.val)) Cardinal.aleph0 :=
          Algebra.rank_adjoin_le _
        _ < Cardinal.mk k :=
          max_lt (Cardinal.mk_range_le.trans_lt hcard) h0
    rw [Algebra.isAlgebraic_def]
    intro T
    by_contra hT
    obtain ⟨Q, hQ, hQunit⟩ :=
      linear_operator_has_noninvertible_monic_polynomial hrank (Algebra.lmul k L T)
    apply hQunit
    rw [Polynomial.aeval_algHom_apply, Algebra.lmul_isUnit_iff]
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    apply hT
    rw [isAlgebraic_iff_not_injective]
    intro hinj
    apply hQ.ne_zero
    apply hinj
    simp [hzero]

private theorem residueField_algebraic_of_small_generators
    {k S I : Type u} [Field k] [CommRing S] [Algebra k S]
    (x : I → S) (hgen : Algebra.adjoin k (Set.range x) = ⊤)
    (hcard : Cardinal.mk I < Cardinal.mk k) :
    ∀ m : MaximalSpectrum S,
      letI : Algebra k m.asIdeal.ResidueField :=
        residueFieldAlgebraOfBaseAlgebra (k := k) m.asIdeal
      Algebra.IsAlgebraic k m.asIdeal.ResidueField := by
  let P : Algebra.Generators k S I := Algebra.Generators.ofSurjective x (by
    apply (AlgHom.range_eq_top _).mp
    rw [← Algebra.adjoin_range_eq_range_aeval, hgen])
  intro m
  let _ : Algebra k m.asIdeal.ResidueField :=
    residueFieldAlgebraOfBaseAlgebra (k := k) m.asIdeal
  let _ : IsScalarTower k S m.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  let y : I → m.asIdeal.ResidueField :=
    fun i => algebraMap S m.asIdeal.ResidueField (x i)
  let Q : Algebra.Generators k m.asIdeal.ResidueField I :=
    Algebra.Generators.ofSurjective y (by
      intro z
      obtain ⟨s, hs⟩ := m.asIdeal.algebraMap_residueField_surjective z
      obtain ⟨p, hp⟩ := P.aeval_val_surjective s
      refine ⟨p, ?_⟩
      rw [← hs, ← hp]
      simpa [y, P, Function.comp_def] using
        (MvPolynomial.comp_aeval_apply (f := P.val)
          (IsScalarTower.toAlgHom k S m.asIdeal.ResidueField) p).symm)
  exact algebraic_of_small_generators Q hcard

private theorem algebraic_of_fraction_ring
    {k A K : Type u} [Field k] [CommRing A] [Field K] [Algebra k A]
    [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsDomain A]
    [IsFractionRing A K] [Algebra.IsAlgebraic k A] :
    Algebra.IsAlgebraic k K := by
  rw [Algebra.isAlgebraic_def]
  intro z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A z
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have ha : IsAlgebraic k (algebraMap A K a) :=
    (isAlgebraic_algebraMap_iff hinj).2 (Algebra.IsAlgebraic.isAlgebraic a)
  have hb' : IsAlgebraic k (algebraMap A K b) :=
    (isAlgebraic_algebraMap_iff hinj).2 (Algebra.IsAlgebraic.isAlgebraic b)
  simpa [div_eq_mul_inv] using ha.mul hb'.inv

private theorem localization_residueField_algebraic_of_small_generators
    {k S I : Type u} [Field k] [CommRing S] [Algebra k S]
    (P : Algebra.Generators k S I) (p : PrimeSpectrum S) (f : S)
    (hpf : f ∉ p.asIdeal) (hfield : IsField
      (Localization.Away (Ideal.Quotient.mk p.asIdeal f)))
    (hcard : Cardinal.mk I < Cardinal.mk k) (hI : Infinite I) :
    letI : Algebra k p.asIdeal.ResidueField :=
      residueFieldAlgebraOfBaseAlgebra (k := k) p.asIdeal
    Algebra.IsAlgebraic k p.asIdeal.ResidueField ∧ p.asIdeal.IsMaximal := by
  let R := S ⧸ p.asIdeal
  let fR : R := Ideal.Quotient.mk p.asIdeal f
  let A := Localization.Away fR
  let _ : Field A := hfield.toField
  let _ : Algebra k R := inferInstance
  let Q : Algebra.Generators k R I :=
    Algebra.Generators.ofSurjective (fun i => Ideal.Quotient.mk p.asIdeal (P.val i)) (by
      intro z
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨q, hq⟩ := P.aeval_val_surjective s
      refine ⟨q, ?_⟩
      rw [← hs, ← hq]
      simpa [Ideal.Quotient.mkₐ_eq_mk] using
        (MvPolynomial.comp_aeval_apply (f := P.val)
          (Ideal.Quotient.mkₐ k p.asIdeal) q).symm)
  let G : Algebra.Generators k A (Unit ⊕ I) :=
    (Algebra.Generators.localizationAway (R := R) (S := A) fR).comp Q
  have hcardG : Cardinal.mk (Unit ⊕ I) < Cardinal.mk k := by
    calc
      Cardinal.mk (Unit ⊕ I) = 1 + Cardinal.mk I := by
        simp [Cardinal.mk_sum]
      _ = Cardinal.mk I := by
        rw [add_comm, Cardinal.add_eq_left (Cardinal.aleph0_le_mk I)]
        exact Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_mk I)
      _ < Cardinal.mk k := hcard
  have hAalg : Algebra.IsAlgebraic k A :=
    algebraic_of_small_generators G hcardG
  let _ : Algebra.IsAlgebraic k A := hAalg
  let _ : Algebra k p.asIdeal.ResidueField :=
    residueFieldAlgebraOfBaseAlgebra (k := k) p.asIdeal
  let _ : IsScalarTower k R p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  have hfκ : algebraMap R p.asIdeal.ResidueField fR ≠ 0 := by
    intro hfκ
    apply hpf
    apply Ideal.algebraMap_residueField_eq_zero.mp
    have hfzero : algebraMap S p.asIdeal.ResidueField f = 0 := by
      rw [← Ideal.algebraMap_quotient_residueField_mk]
      change algebraMap R p.asIdeal.ResidueField fR = 0
      exact hfκ
    exact hfzero
  let e : A →ₐ[R] p.asIdeal.ResidueField :=
    IsLocalization.Away.liftAlgHom (R := R) (S := A)
      (P := p.asIdeal.ResidueField) (f := Algebra.ofId R p.asIdeal.ResidueField)
      fR (isUnit_iff_ne_zero.mpr hfκ)
  let _ : Algebra A p.asIdeal.ResidueField := e.toAlgebra
  let _ : IsScalarTower k A p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change algebraMap R p.asIdeal.ResidueField (algebraMap k R a) =
        e (algebraMap k A a)
      rw [IsScalarTower.algebraMap_apply k R A, e.commutes])
  let _ : IsFractionRing A p.asIdeal.ResidueField :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers fR) A p.asIdeal.ResidueField
  have hκalg : Algebra.IsAlgebraic k p.asIdeal.ResidueField :=
    algebraic_of_fraction_ring (k := k) (A := A)
      (K := p.asIdeal.ResidueField)
  let B : Subalgebra k A :=
    { carrier := Set.range (algebraMap R A)
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
        refine ⟨algebraMap k R a, ?_⟩
        exact (IsScalarTower.algebraMap_apply k R A a).symm }
  have hB : IsField B :=
    @Subalgebra.isField_of_algebraic k A _ _ _ B hAalg
  have hfR : fR ≠ 0 := by
    intro hfR
    apply hpf
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [fR] using hfR
  have hmap : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A
      (powers_le_nonZeroDivisors_of_noZeroDivisors hfR)
  have hpmax : p.asIdeal.IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField p.asIdeal
    have hnontriv : Nontrivial R :=
      Ideal.Quotient.nontrivial_iff.mpr p.2.ne_top
    refine ⟨hnontriv.exists_pair_ne, mul_comm, ?_⟩
    intro a ha
    let z : B := ⟨algebraMap R A a, ⟨a, rfl⟩⟩
    have hzA : (z : A) ≠ 0 := by
      intro hz
      apply ha
      apply hmap
      simpa [z] using hz
    have hzB : z ≠ 0 := by
      intro hz0
      apply hzA
      simpa using congrArg Subtype.val hz0
    obtain ⟨b, hb⟩ := hB.mul_inv_cancel hzB
    obtain ⟨t, ht⟩ := b.property
    refine ⟨t, ?_⟩
    apply hmap
    rw [map_mul, map_one, ht]
    simpa [z] using congrArg Subtype.val hb
  exact ⟨hκalg, hpmax⟩

theorem uncountable_nullstellensatz
    {k S I : Type u} [Field k] [CommRing S] [Algebra k S]
    (x : I → S) (hgen : Algebra.adjoin k (Set.range x) = ⊤)
    (hcard : Cardinal.mk I < Cardinal.mk k) :
    (∀ m : MaximalSpectrum S,
      letI : Algebra k m.asIdeal.ResidueField :=
          residueFieldAlgebraOfBaseAlgebra (k := k) m.asIdeal
      Algebra.IsAlgebraic k m.asIdeal.ResidueField) ∧
      IsJacobsonRing S := by
  let P : Algebra.Generators k S I := Algebra.Generators.ofSurjective x (by
    apply (AlgHom.range_eq_top _).mp
    rw [← Algebra.adjoin_range_eq_range_aeval, hgen])
  refine ⟨residueField_algebraic_of_small_generators x hgen hcard, ?_⟩
  by_cases hI : Finite I
  · let _ := hI
    let _ : Algebra.FiniteType k S := P.finiteType
    exact finiteType_algebra_over_field_isJacobson (k := k) (A := S)
  · have hI' : Infinite I := not_finite_iff_infinite.mp hI
    by_contra hS
    obtain ⟨p, f, hp, hpf, hloc, hfield⟩ := characterize_nonJacobson_ring hS
    have hpmax := localization_residueField_algebraic_of_small_generators
      P p f hpf hfield hcard hI'
    exact hp hpmax.2

theorem baseChange_uncountable_nullstellensatz
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Field K] [Algebra k K]
    (hcard : Cardinal.mk S < Cardinal.mk K) :
    (∀ m : MaximalSpectrum (K ⊗[k] S),
      letI : Algebra K m.asIdeal.ResidueField :=
          residueFieldAlgebraOfBaseAlgebra (k := K) m.asIdeal
      Algebra.IsAlgebraic K m.asIdeal.ResidueField) ∧
      IsJacobsonRing (K ⊗[k] S) := by
  let P : Algebra.Generators K (K ⊗[k] S) S :=
    (Algebra.Generators.self k S).baseChange K
  have hgen : Algebra.adjoin K (Set.range P.val) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).mpr P.aeval_val_surjective
  refine ⟨residueField_algebraic_of_small_generators P.val hgen hcard, ?_⟩
  by_cases hS : Finite S
  · let _ := hS
    let _ : Algebra.FiniteType K (K ⊗[k] S) := P.finiteType
    exact finiteType_algebra_over_field_isJacobson (k := K)
      (A := K ⊗[k] S)
  · have hS' : Infinite S := not_finite_iff_infinite.mp hS
    by_contra hT
    obtain ⟨p, f, hp, hpf, hloc, hfield⟩ := characterize_nonJacobson_ring hT
    have hpmax := localization_residueField_algebraic_of_small_generators
      P p f hpf hfield hcard hS'
    exact hp hpmax.2

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
  let F := FractionRing (Polynomial k)
  let φ : CountableTrickRing k →+* F :=
    MvPolynomial.eval₂Hom (algebraMap (Polynomial k) F)
      (fun i => (algebraMap (Polynomial k) F i.1)⁻¹)
  have hmap : Function.Injective (algebraMap (Polynomial k) F) :=
    IsFractionRing.injective (Polynomial k) F
  have hrel (i : CountableTrickIndex k) :
      φ (countableTrickRelation i) = 0 := by
    have hi : algebraMap (Polynomial k) F i.1 ≠ 0 :=
      fun h => i.2 (hmap (by simpa using h))
    simp [φ, countableTrickRelation, mul_inv_cancel₀ hi]
  intro htop
  have hle : countableTrickIdeal (k := k) ≤ RingHom.ker φ := by
    rw [countableTrickIdeal]
    apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    change φ (countableTrickRelation i) = 0
    exact hrel i
  have hone : (1 : CountableTrickRing k) ∈ countableTrickIdeal (k := k) := by
    rw [htop]
    simp
  have hzero : φ 1 = 0 := hle hone
  rw [map_one] at hzero
  exact one_ne_zero hzero

theorem countableTrick_exists_maximalIdeal {k : Type u} [Field k] :
    ∃ m : MaximalSpectrum (CountableTrickRing k),
      countableTrickIdeal (k := k) ≤ m.asIdeal := by
  obtain ⟨M, hM, hI⟩ := (Ideal.ne_top_iff_exists_maximal).mp
    (countableTrickIdeal_isProper (k := k))
  refine ⟨MaximalSpectrum.mk M hM, ?_⟩
  intro x hx
  exact hI hx

theorem countableTrick_quotient_is_rational_function_field
    {k : Type u} [Field k]
    (m : MaximalSpectrum (CountableTrickRing k))
    (hm : countableTrickIdeal (k := k) ≤ m.asIdeal) :
    Nonempty ((CountableTrickRing k ⧸ m.asIdeal) ≃+* FractionRing (Polynomial k)) ∧
      ¬ Algebra.IsAlgebraic k (CountableTrickRing k ⧸ m.asIdeal) := by
  let _ : Field (CountableTrickRing k ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  let F := FractionRing (Polynomial k)
  let ψ : CountableTrickRing k →+* F :=
    MvPolynomial.eval₂Hom (algebraMap (Polynomial k) F)
      (fun i => (algebraMap (Polynomial k) F i.1)⁻¹)
  have hmap : Function.Injective (algebraMap (Polynomial k) F) :=
    IsFractionRing.injective (Polynomial k) F
  let φ : Polynomial k →+* (CountableTrickRing k ⧸ m.asIdeal) :=
    (Ideal.Quotient.mk m.asIdeal).comp
      (MvPolynomial.C : Polynomial k →+* CountableTrickRing k)
  have hunit (f : Polynomial k) (hf : f ≠ 0) : IsUnit (φ f) := by
    let i : CountableTrickIndex k := ⟨f, hf⟩
    have hmem : countableTrickRelation i ∈ m.asIdeal :=
      hm (Ideal.subset_span ⟨i, rfl⟩)
    have hzero :
        Ideal.Quotient.mk m.asIdeal (countableTrickRelation i) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hmem
    have heq : φ f * Ideal.Quotient.mk m.asIdeal (MvPolynomial.X i) = 1 := by
      have hzero' := hzero
      simp only [countableTrickRelation, map_sub, map_mul, map_one,
        MvPolynomial.C_apply] at hzero'
      exact sub_eq_zero.mp hzero'
    exact IsUnit.of_mul_eq_one _ heq
  let qFromF : F →+* (CountableTrickRing k ⧸ m.asIdeal) :=
    IsLocalization.lift (S := F) (P := (CountableTrickRing k ⧸ m.asIdeal))
      (g := φ)
      (fun y : nonZeroDivisors (Polynomial k) => hunit y.1
        (mem_nonZeroDivisors_iff_ne_zero.mp y.2))
  have hcomp :
      qFromF.comp ψ = Ideal.Quotient.mk m.asIdeal := by
    apply MvPolynomial.ringHom_ext'
    · apply RingHom.ext
      intro f
      simp [qFromF, ψ, φ]
    · intro i
      have hmem : countableTrickRelation i ∈ m.asIdeal :=
        hm (Ideal.subset_span ⟨i, rfl⟩)
      have hzero :
          Ideal.Quotient.mk m.asIdeal (countableTrickRelation i) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).2 hmem
      have heq : φ i.1 * Ideal.Quotient.mk m.asIdeal (MvPolynomial.X i) = 1 := by
        have hzero' := hzero
        simp only [countableTrickRelation, map_sub, map_mul, map_one,
          MvPolynomial.C_apply] at hzero'
        exact sub_eq_zero.mp hzero'
      have hi' : (φ i.1)⁻¹ = Ideal.Quotient.mk m.asIdeal (MvPolynomial.X i) :=
        inv_eq_of_mul_eq_one_right heq
      simp [qFromF, ψ, hi']
  have hsurj : Function.Surjective qFromF := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨ψ r, ?_⟩
    exact congrArg
      (fun f : CountableTrickRing k →+* (CountableTrickRing k ⧸ m.asIdeal) => f r)
      hcomp
  let e : F ≃+* (CountableTrickRing k ⧸ m.asIdeal) :=
    RingEquiv.ofBijective qFromF ⟨RingHom.injective qFromF, hsurj⟩
  constructor
  · exact ⟨e.symm⟩
  · intro hQ
    let _ : Algebra.IsAlgebraic k (CountableTrickRing k ⧸ m.asIdeal) := hQ
    have hcompk :
        (algebraMap k (CountableTrickRing k ⧸ m.asIdeal)).comp (RingHom.id k) =
          qFromF.comp (algebraMap k F) := by
      apply RingHom.ext
      intro c
      change algebraMap k (CountableTrickRing k ⧸ m.asIdeal) c =
        qFromF (algebraMap k F c)
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) F]
      simp [qFromF, φ]
      exact (Ideal.Quotient.mk_algebraMap k m.asIdeal c).symm
    have hF : Algebra.IsAlgebraic k F :=
      Algebra.IsAlgebraic.of_ringHom_of_comp_eq
        (f := RingHom.id k) (g := qFromF) Function.surjective_id
        (RingHom.injective qFromF) hcompk
    have hpoly : Algebra.IsAlgebraic k (Polynomial k) :=
      Algebra.IsAlgebraic.tower_bot_of_injective hmap
    exact (Polynomial.transcendental_X k) (hpoly.isAlgebraic Polynomial.X)

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
  exact ⟨isJacobsonRing_localization f,
    ⟨maximalIdealLocalizationOrderIso f⟩⟩

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
  let _ : IsDiscreteValuationRing ZLocalizedAtTwo :=
    (inferInstance : IsDedekindDomainDvr ℤ).is_dvr_at_nonzero_prime
      integerTwoIdeal
      (by
        change Ideal.span ({(2 : ℤ)} : Set ℤ) ≠ (⊥ : Ideal ℤ)
        exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
      (inferInstance : integerTwoIdeal.IsPrime)
  have hmax :
      IsLocalRing.maximalIdeal ZLocalizedAtTwo =
        Ideal.span {(algebraMap ℤ ZLocalizedAtTwo) (2 : ℤ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal
      (R := ℤ) (I := integerTwoIdeal)]
    change Ideal.map (algebraMap ℤ ZLocalizedAtTwo)
      (Ideal.span ({(2 : ℤ)} : Set ℤ)) =
      Ideal.span {(algebraMap ℤ ZLocalizedAtTwo) (2 : ℤ)}
    rw [Ideal.map_span]
    simp
  have h2irr : Irreducible (algebraMap ℤ ZLocalizedAtTwo (2 : ℤ)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  have hN :
      IsLocalization
        (Submonoid.map (algebraMap ℤ ZLocalizedAtTwo) (nonZeroDivisors ℤ))
        (FractionRing ℤ) :=
    IsLocalization.isLocalization_of_submonoid_le
      ZLocalizedAtTwo (FractionRing ℤ) integerTwoIdeal.primeCompl
        (nonZeroDivisors ℤ) integerTwoIdeal.primeCompl_le_nonZeroDivisors
  have hloc :
      IsLocalization
        (Submonoid.powers (algebraMap ℤ ZLocalizedAtTwo (2 : ℤ)))
        (FractionRing ℤ) := by
    have hi :=
      IsLocalization.iff_of_le_of_exists_dvd
        (M := Submonoid.powers (algebraMap ℤ ZLocalizedAtTwo (2 : ℤ)))
        (S := FractionRing ℤ)
        (N := Submonoid.map (algebraMap ℤ ZLocalizedAtTwo) (nonZeroDivisors ℤ))
        (by
          rintro _ ⟨n, rfl⟩
          refine ⟨(2 : ℤ) ^ n, ?_, ?_⟩
          · exact mem_nonZeroDivisors_of_ne_zero (by norm_num)
          · simp)
        (by
          rintro x ⟨z, hz, rfl⟩
          have hzinj : Function.Injective (algebraMap ℤ ZLocalizedAtTwo) :=
            IsLocalization.injective ZLocalizedAtTwo
              integerTwoIdeal.primeCompl_le_nonZeroDivisors
          have hzS : algebraMap ℤ ZLocalizedAtTwo z ≠ 0 := by
            intro hzS
            apply mem_nonZeroDivisors_iff_ne_zero.mp hz
            apply hzinj
            simpa using hzS
          obtain ⟨r, u, hu⟩ :=
            IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hzS h2irr
          refine ⟨(algebraMap ℤ ZLocalizedAtTwo (2 : ℤ)) ^ r, ⟨r, rfl⟩, ?_⟩
          refine ⟨↑u⁻¹, ?_⟩
          rw [hu]
          simp [mul_comm])
    exact hi.mpr hN
  let _ :
      IsLocalization
        (Submonoid.powers (algebraMap ℤ ZLocalizedAtTwo (2 : ℤ)))
        (FractionRing ℤ) := hloc
  let e₀ :
      ZLocalizedAtTwoAtTwo ≃ₐ[ZLocalizedAtTwo] FractionRing ℤ :=
    IsLocalization.algEquiv
      (Submonoid.powers (algebraMap ℤ ZLocalizedAtTwo (2 : ℤ)))
      ZLocalizedAtTwoAtTwo (FractionRing ℤ)
  exact ⟨e₀.toRingEquiv.trans (FractionRing.algEquiv ℤ ℚ).toRingEquiv⟩

theorem zLocalizedAtTwo_closedPoint_maps_to_generic_point
    : ∃ e : ZLocalizedAtTwoAtTwo ≃+* ℚ,
        PrimeSpectrum.comap
            (e.toRingHom.comp (algebraMap ZLocalizedAtTwo ZLocalizedAtTwoAtTwo))
            (⟨⊥, inferInstance⟩ : PrimeSpectrum ℚ) =
          (⟨⊥, inferInstance⟩ : PrimeSpectrum ZLocalizedAtTwo) := by
  obtain ⟨e⟩ := zLocalizedAtTwo_is_rational
  refine ⟨e, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (e.toRingHom.comp
    (algebraMap ZLocalizedAtTwo ZLocalizedAtTwoAtTwo)) (⊥ : Ideal ℚ) = ⊥
  apply Ideal.comap_bot_of_injective
  apply e.injective.comp
  apply IsLocalization.injective (M :=
    Submonoid.powers (algebraMap ℤ ZLocalizedAtTwo (2 : ℤ)))
    ZLocalizedAtTwoAtTwo
  apply powers_le_nonZeroDivisors_of_noZeroDivisors
  intro h
  have hinj : Function.Injective (algebraMap ℤ ZLocalizedAtTwo) :=
    IsLocalization.injective ZLocalizedAtTwo
      integerTwoIdeal.primeCompl_le_nonZeroDivisors
  have h20 : (2 : ℤ) = 0 := hinj (by simpa using h)
  norm_num at h20

abbrev RationalLocalizationOfIntegers :=
  Localization (nonZeroDivisors ℤ)

theorem rationalLocalizationOfIntegers_is_rational
    : Nonempty (RationalLocalizationOfIntegers ≃+* ℚ) := by
  exact ⟨(FractionRing.algEquiv ℤ ℚ).toRingEquiv⟩

theorem rationalLocalization_closedPoint_maps_to_generic_point
    : ∃ e : RationalLocalizationOfIntegers ≃+* ℚ,
        PrimeSpectrum.comap
            (e.toRingHom.comp (algebraMap ℤ RationalLocalizationOfIntegers))
            (⟨⊥, inferInstance⟩ : PrimeSpectrum ℚ) =
          (⟨⊥, inferInstance⟩ : PrimeSpectrum ℤ) := by
  obtain ⟨e⟩ := rationalLocalizationOfIntegers_is_rational
  refine ⟨e, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (e.toRingHom.comp
    (algebraMap ℤ RationalLocalizationOfIntegers)) (⊥ : Ideal ℚ) = ⊥
  apply Ideal.comap_bot_of_injective
  apply e.injective.comp
  exact IsLocalization.injective (M := nonZeroDivisors ℤ)
    RationalLocalizationOfIntegers le_rfl

theorem quotient_of_isJacobson_isJacobson_with_maximal_correspondence
    {R : Type u} [CommRing R] [IsJacobsonRing R] (I : Ideal R) :
    IsJacobsonRing (R ⧸ I) ∧
      ∃ e :
          {M : Ideal (R ⧸ I) // M.IsMaximal} ≃
            {N : Ideal R // N.IsMaximal ∧ I ≤ N},
        (∀ M, Ideal.map (Ideal.Quotient.mk I) (e M).1 = M.1) ∧
          (∀ N, Ideal.comap (Ideal.Quotient.mk I) (e.symm N).1 = N.1) := by
  constructor
  · infer_instance
  · let f : R →+* R ⧸ I := Ideal.Quotient.mk I
    let e :
        {M : Ideal (R ⧸ I) // M.IsMaximal} ≃
          {N : Ideal R // N.IsMaximal ∧ I ≤ N} :=
      { toFun := fun M =>
          let _ : M.1.IsMaximal := M.2
          ⟨Ideal.comap f M.1,
            ⟨Ideal.comap_isMaximal_of_surjective f Ideal.Quotient.mk_surjective,
              by
                change I ≤ Ideal.comap (Ideal.Quotient.mk I) M.1
                exact (Ideal.mk_ker (I := I)).ge.trans
                  (Ideal.ker_le_comap (Ideal.Quotient.mk I))⟩⟩
        invFun := fun N =>
          let _ : N.1.IsMaximal := N.2.1
          ⟨Ideal.map f N.1,
            Ideal.IsMaximal.map_of_surjective_of_ker_le
              Ideal.Quotient.mk_surjective (by
                exact (Ideal.mk_ker (I := I)).le.trans N.2.2)⟩
        left_inv := fun M =>
          Subtype.ext (Ideal.map_comap_of_surjective f
            Ideal.Quotient.mk_surjective M.1)
        right_inv := fun N => by
          apply Subtype.ext
          change Ideal.comap f (Ideal.map f N.1) = N.1
          rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective]
          change N.1 ⊔ Ideal.comap (Ideal.Quotient.mk I)
              (⊥ : Ideal (R ⧸ I)) = N.1
          rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
          exact sup_eq_left.mpr N.2.2 }
    refine ⟨e, ?_, ?_⟩
    · intro M
      exact Ideal.map_comap_of_surjective f Ideal.Quotient.mk_surjective M.1
    · intro N
      change Ideal.comap f (Ideal.map f N.1) = N.1
      rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective]
      change N.1 ⊔ Ideal.comap (Ideal.Quotient.mk I)
          (⊥ : Ideal (R ⧸ I)) = N.1
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact sup_eq_left.mpr N.2.2

theorem jacobson_subring_of_finiteType_field
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    [IsJacobsonRing R] [Algebra.FiniteType R K]
    (hRK : Function.Injective (algebraMap R K)) :
    IsField R ∧ Module.Finite R K := by
  let : IsDomain R := hRK.isDomain
  obtain ⟨f, hf, hfield, _, _⟩ :=
    Formalization.Books.Algebra.Unit34.field_finite_type_over_domain hRK
  let : Field (Localization.Away f) := hfield.toField
  have halg_inj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective (M := Submonoid.powers f) (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have hmax : (⊥ : Ideal R).IsMaximal := by
    have hm :=
      (maximalIdealLocalizationOrderIso f
        ⟨(⊥ : Ideal (Localization.Away f)), inferInstance⟩).2
    have heq :
        (maximalIdealLocalizationOrderIso f
          ⟨(⊥ : Ideal (Localization.Away f)), inferInstance⟩).1 =
            (⊥ : Ideal R) := by
      change Ideal.comap (algebraMap R (Localization.Away f)) ⊥ = ⊥
      exact Ideal.comap_bot_of_injective _ halg_inj
    rw [heq] at hm
    exact hm.1
  refine ⟨Ring.isField_iff_maximal_bot.mpr hmax, ?_⟩
  exact finite_of_finite_type_of_isJacobsonRing R K

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
  refine ⟨hφ.isJacobsonRing, ?_, ?_⟩
  · intro q
    let p : Ideal R := q.asIdeal.comap φ
    let f : R ⧸ p →+* S ⧸ q.asIdeal :=
      Ideal.quotientMap q.asIdeal φ le_rfl
    have hcomp : ((Ideal.Quotient.mk q.asIdeal).comp φ).FiniteType :=
      RingHom.FiniteType.comp
        (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) hφ
    have hfac : f.comp (Ideal.Quotient.mk p) =
        (Ideal.Quotient.mk q.asIdeal).comp φ := by
      simpa [f] using (Ideal.quotientMap_comp_mk (f := φ) (H := le_rfl))
    have hf : f.FiniteType := by
      exact RingHom.FiniteType.of_comp_finiteType
        (f := Ideal.Quotient.mk p) (g := f) (hfac ▸ hcomp)
    let : Field (S ⧸ q.asIdeal) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient q.asIdeal).mp q.2 |>.toField
    let : Algebra (R ⧸ p) (S ⧸ q.asIdeal) := f.toAlgebra
    let : Algebra.FiniteType (R ⧸ p) (S ⧸ q.asIdeal) := hf
    have hinj : Function.Injective (algebraMap (R ⧸ p) (S ⧸ q.asIdeal)) := by
      rw [RingHom.algebraMap_toAlgebra]
      simpa [p, f] using (Ideal.quotientMap_injective (I := q.asIdeal) (f := φ))
    have hfield := jacobson_subring_of_finiteType_field
      (R := R ⧸ p) (K := S ⧸ q.asIdeal) hinj
    simpa [p] using Ideal.Quotient.maximal_of_isField p hfield.1
  · intro q
    let p := q.asIdeal.comap φ
    let : p.IsPrime := Ideal.comap_isPrime φ q.asIdeal
    let : Algebra p.ResidueField q.asIdeal.ResidueField :=
      residueFieldAlgebraOfMap p q.asIdeal φ rfl
    have hcomp :
        ((algebraMap S q.asIdeal.ResidueField).comp φ).FiniteType :=
      RingHom.FiniteType.comp
        (RingHom.FiniteType.of_finite
          (RingHom.finite_algebraMap.mpr inferInstance)) hφ
    have hfac :
        (Ideal.ResidueField.map p q.asIdeal φ rfl).comp
            (algebraMap R p.ResidueField) =
          (algebraMap S q.asIdeal.ResidueField).comp φ := by
      ext r
      exact Ideal.ResidueField.map_algebraMap p q.asIdeal φ rfl r
    have hft :
        (Ideal.ResidueField.map p q.asIdeal φ rfl).FiniteType := by
      exact RingHom.FiniteType.of_comp_finiteType
        (f := algebraMap R p.ResidueField)
        (g := Ideal.ResidueField.map p q.asIdeal φ rfl) (hfac ▸ hcomp)
    have hft' : Algebra.FiniteType p.ResidueField q.asIdeal.ResidueField :=
      RingHom.finiteType_algebraMap.mp (by
        change (Ideal.ResidueField.map p q.asIdeal φ rfl).FiniteType
        exact hft)
    exact @finite_of_finite_type_of_isJacobsonRing
      p.ResidueField q.asIdeal.ResidueField _ _ _ _ hft'

theorem finiteType_algebra_over_integers_isJacobson
    {A : Type u} [CommRing A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] :
    IsJacobsonRing A := by
  let : IsJacobsonRing ℤ := integer_isJacobson
  exact isJacobsonRing_of_finiteType (A := ℤ) (B := A)

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
  exact PrimeSpectrum.isConstructible_comap_image
    (RingHom.FinitePresentation.of_finiteType.mp hφ) hE

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
  let F : Set (PrimeSpectrum R) := PrimeSpectrum.comap φ '' E
  let G : Set (PrimeSpectrum R) :=
    PrimeSpectrum.comap φ '' (E ∩ closedPoints (PrimeSpectrum S))
  have hpres := finiteType_map_preserves_jacobson_closedPoints_and_residue_finiteness
    φ hφ
  have hmax : ∀ q : MaximalSpectrum S, (q.asIdeal.comap φ).IsMaximal :=
    hpres.2.1
  have hEjac := Formalization.Books.Topology.Unit18.jacobsonSpace_of_isConstructible
    (X := PrimeSpectrum S) hE
  let : JacobsonSpace E := hEjac.1
  let g : E → F := fun z =>
    ⟨PrimeSpectrum.comap φ z.1, ⟨z.1, z.2, rfl⟩⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact PrimeSpectrum.continuous_comap φ |>.comp continuous_subtype_val
  have hclosed : closedPointsOfSubset F = G := by
    apply Set.Subset.antisymm
    · intro x hx
      change ∃ y : closedPoints F, (y.1 : PrimeSpectrum R) = x at hx
      rcases hx with ⟨y, rfl⟩
      obtain ⟨q, hqE, hq⟩ := y.1.2
      let A : Set E := g ⁻¹' ({(y.1 : F)} : Set F)
      have hAne : A.Nonempty := by
        refine ⟨⟨q, hqE⟩, ?_⟩
        exact Set.mem_singleton_iff.mpr (by
          apply Subtype.ext
          exact hq)
      have hyclosedF : IsClosed ({(y.1 : F)} : Set F) :=
        mem_closedPoints_iff.mp y.2
      have hAclosed : IsClosed A := by
        exact hyclosedF.preimage hg
      obtain ⟨z, hzA, hzclosed⟩ := nonempty_inter_closedPoints hAne
        hAclosed.isLocallyClosed
      have hzSclosed : IsClosed ({(z : PrimeSpectrum S)} : Set (PrimeSpectrum S)) :=
        hEjac.2 z hzclosed
      have hzG : PrimeSpectrum.comap φ (z : PrimeSpectrum S) ∈ G := by
        refine ⟨(z : PrimeSpectrum S), ?_, rfl⟩
        exact ⟨z.property, mem_closedPoints_iff.mpr hzSclosed⟩
      have hzx : PrimeSpectrum.comap φ (z : PrimeSpectrum S) = (y.1 : PrimeSpectrum R) := by
        change g z ∈ ({(y.1 : F)} : Set F) at hzA
        exact congrArg Subtype.val (Set.mem_singleton_iff.mp hzA)
      simpa [hzx] using hzG
    · intro x hxG
      change ∃ q : PrimeSpectrum S, q ∈ E ∩ closedPoints (PrimeSpectrum S) ∧
        PrimeSpectrum.comap φ q = x at hxG
      obtain ⟨q, ⟨hqE, hqclosed⟩, hqeq⟩ := hxG
      have hqmax : q.asIdeal.IsMaximal :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp
          (mem_closedPoints_iff.mp hqclosed)
      let qM : MaximalSpectrum S := ⟨q, hqmax⟩
      have hxclosed : IsClosed ({PrimeSpectrum.comap φ q} : Set (PrimeSpectrum R)) := by
        exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal (PrimeSpectrum.comap φ q)).mpr
          (hmax qM)
      refine ⟨⟨⟨PrimeSpectrum.comap φ q, ⟨q, hqE, rfl⟩⟩, ?_⟩, hqeq⟩
      exact preimage_closedPoints_subset Subtype.val_injective continuous_subtype_val
        (mem_closedPoints_iff.mpr hxclosed)
  have hpart : G = closedPointPart F := by
    apply Set.Subset.antisymm
    · intro x hxG
      change ∃ q : PrimeSpectrum S, q ∈ E ∩ closedPoints (PrimeSpectrum S) ∧
        PrimeSpectrum.comap φ q = x at hxG
      obtain ⟨q, ⟨hqE, hqclosed⟩, hqeq⟩ := hxG
      have hqmax : q.asIdeal.IsMaximal :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp
          (mem_closedPoints_iff.mp hqclosed)
      let qM : MaximalSpectrum S := ⟨q, hqmax⟩
      refine ⟨?_, ?_⟩
      · exact hqeq ▸ ⟨q, hqE, rfl⟩
      · exact hqeq ▸ mem_closedPoints_iff.mpr
          ((PrimeSpectrum.isClosed_singleton_iff_isMaximal (PrimeSpectrum.comap φ q)).mpr
            (hmax qM))
    · intro x hx
      change x ∈ F ∩ closedPoints (PrimeSpectrum R) at hx
      rcases hx with ⟨hxF, hxclosed⟩
      have hxsub : (⟨x, hxF⟩ : F) ∈ closedPoints F :=
        preimage_closedPoints_subset Subtype.val_injective continuous_subtype_val
          (mem_closedPoints_iff.mpr hxclosed)
      have hxsub' : x ∈ closedPointsOfSubset F := by
        change ∃ y : closedPoints F, (y.1 : PrimeSpectrum R) = x
        exact ⟨⟨⟨x, hxF⟩, hxsub⟩, rfl⟩
      rw [hclosed] at hxsub'
      exact hxsub'
  refine ⟨?_, ?_, ?_⟩
  · exact hclosed
  · exact hpart
  · intro ξ
    constructor
    · intro hξ
      obtain ⟨U, hUopen, hUdense, hUF⟩ :=
        Formalization.Books.Algebra.Unit30.image_constructible_contains_open_dense_subset_of_finiteType
          φ hφ hE hξ
      apply Set.Subset.antisymm
      · intro x hxC
        by_contra hxnot
        obtain ⟨O, hOopen, hOU⟩ := IsInducing.subtypeVal.isOpen_iff.mp hUopen
        let V : Set (closure ({ξ} : Set (PrimeSpectrum R))) :=
          (Subtype.val : closure ({ξ} : Set (PrimeSpectrum R)) → PrimeSpectrum R) ⁻¹'
            (closure (closure ({ξ} : Set (PrimeSpectrum R)) ∩ G))ᶜ
        have hVopen : IsOpen V := by
          exact isClosed_closure.isOpen_compl.preimage continuous_subtype_val
        have hxV : (⟨x, hxC⟩ : closure ({ξ} : Set (PrimeSpectrum R))) ∈ V := by
          exact hxnot
        obtain ⟨y, hyV, hyU⟩ := hUdense.inter_open_nonempty V hVopen ⟨_, hxV⟩
        let W : Set (PrimeSpectrum R) :=
          closure ({ξ} : Set (PrimeSpectrum R)) ∩ O ∩
            (closure (closure ({ξ} : Set (PrimeSpectrum R)) ∩ G))ᶜ
        have hWne : W.Nonempty := by
          refine ⟨(y : PrimeSpectrum R), ?_⟩
          refine ⟨⟨y.property, ?_⟩, ?_⟩
          · have : y ∈
                (Subtype.val : closure ({ξ} : Set (PrimeSpectrum R)) → PrimeSpectrum R) ⁻¹' O :=
              hOU.symm ▸ hyU
            exact this
          · simpa [V] using hyV
        have hWloc : IsLocallyClosed W := by
          dsimp [W]
          exact (isClosed_closure.isLocallyClosed.inter hOopen.isLocallyClosed).inter
            isClosed_closure.isOpen_compl.isLocallyClosed
        obtain ⟨z, hzW, hzclosed⟩ := nonempty_inter_closedPoints hWne hWloc
        rcases hzW with ⟨⟨hzC, hzO⟩, hznot⟩
        have hzU : (⟨z, hzC⟩ : closure ({ξ} : Set (PrimeSpectrum R))) ∈ U := by
          have hzO' : (⟨z, hzC⟩ : closure ({ξ} : Set (PrimeSpectrum R))) ∈
              (Subtype.val : closure ({ξ} : Set (PrimeSpectrum R)) → PrimeSpectrum R) ⁻¹' O :=
            hzO
          exact hOU ▸ hzO'
        have hzF : z ∈ F := hUF ⟨⟨z, hzC⟩, hzU, rfl⟩
        have hzsub : (⟨z, hzF⟩ : F) ∈ closedPoints F :=
          preimage_closedPoints_subset Subtype.val_injective continuous_subtype_val
            (mem_closedPoints_iff.mpr hzclosed)
        have hzclosedOfSubset : z ∈ closedPointsOfSubset F := by
          change ∃ y : closedPoints F, (y.1 : PrimeSpectrum R) = z
          exact ⟨⟨⟨z, hzF⟩, hzsub⟩, rfl⟩
        have hzG : z ∈ G := by rw [← hclosed]; exact hzclosedOfSubset
        exact hznot (subset_closure ⟨hzC, hzG⟩)
      · exact closure_minimal inter_subset_left isClosed_closure
    · intro hξdense
      change closure ({ξ} : Set (PrimeSpectrum R)) =
        closure (closure ({ξ} : Set (PrimeSpectrum R)) ∩ G) at hξdense
      obtain ⟨T, hTcomm, ψ, hψfp, hψrange⟩ :=
        Formalization.Books.Algebra.Unit29.exists_finitePresentation_ringHom_of_isConstructible
          hE
      let : CommRing T := hTcomm
      let hψft : RingHom.FiniteType ψ := RingHom.FiniteType.of_finitePresentation hψfp
      let : IsJacobsonRing T := hψft.isJacobsonRing
      have hEclosed : E ∩ closedPoints (PrimeSpectrum S) =
          PrimeSpectrum.comap ψ '' closedPoints (PrimeSpectrum T) := by
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨t, ht⟩ : ∃ t : PrimeSpectrum T,
              PrimeSpectrum.comap ψ t = x := by
            have hxrange : x ∈ Set.range (PrimeSpectrum.comap ψ) := by
              rw [hψrange]
              exact hx.1
            exact hxrange
          let A : Set (PrimeSpectrum T) :=
            (PrimeSpectrum.comap ψ ⁻¹' ({x} : Set (PrimeSpectrum S)))
          have hAne : A.Nonempty := ⟨t, ht⟩
          have hAclosed : IsClosed A := by
            exact (mem_closedPoints_iff.mp hx.2).preimage
              (PrimeSpectrum.continuous_comap ψ)
          obtain ⟨u, huA, huclosed⟩ := nonempty_inter_closedPoints hAne
            hAclosed.isLocallyClosed
          have hux : PrimeSpectrum.comap ψ u = x := by
            exact Set.mem_singleton_iff.mp huA
          exact ⟨u, mem_closedPoints_iff.mpr (mem_closedPoints_iff.mp huclosed), hux⟩
        · intro x hx
          change ∃ t : PrimeSpectrum T, t ∈ closedPoints (PrimeSpectrum T) ∧
            PrimeSpectrum.comap ψ t = x at hx
          obtain ⟨t, htclosed, htx⟩ := hx
          have htmax : t.asIdeal.IsMaximal :=
            (PrimeSpectrum.isClosed_singleton_iff_isMaximal t).mp
              (mem_closedPoints_iff.mp htclosed)
          let tM : MaximalSpectrum T := ⟨t, htmax⟩
          refine ⟨?_, ?_⟩
          · rw [← hψrange]
            exact ⟨t, htx⟩
          · rw [← htx]
            exact mem_closedPoints_iff.mpr
              ((PrimeSpectrum.isClosed_singleton_iff_isMaximal
                (PrimeSpectrum.comap ψ t)).mpr
                ((finiteType_map_preserves_jacobson_closedPoints_and_residue_finiteness
                  ψ hψft).2.1 tM))
      have hGθ : G = PrimeSpectrum.comap (ψ.comp φ) '' closedPoints (PrimeSpectrum T) := by
        dsimp [G]
        rw [hEclosed, ← Set.image_comp, ← PrimeSpectrum.comap_comp]
      let θ : R →+* T := ψ.comp φ
      let p : Ideal R := ξ.asIdeal
      let f : R ⧸ p →+* T ⧸ p.map θ :=
        Ideal.quotientMap (p.map θ) θ Ideal.le_comap_map
      have hf_inj : Function.Injective f := by
        apply (injective_iff_map_eq_zero f).2
        intro a ha
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        by_contra hr
        have hξcl : ξ ∈ closure (closure ({ξ} : Set (PrimeSpectrum R)) ∩ G) := by
          rw [← hξdense]
          exact subset_closure (mem_singleton ξ)
        have hrp : r ∉ p := by
          intro hrp
          apply hr
          exact Ideal.Quotient.eq_zero_iff_mem.mpr hrp
        obtain ⟨y, hybasic, hyCG⟩ := mem_closure_iff.mp hξcl
          (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))
          PrimeSpectrum.isOpen_basicOpen
          ((PrimeSpectrum.mem_basicOpen r ξ).mpr (by simpa [p] using hrp))
        have hyθ : y ∈ PrimeSpectrum.comap θ '' closedPoints (PrimeSpectrum T) := by
          rw [← hGθ]
          exact hyCG.2
        obtain ⟨t, htclosed, hty⟩ := hyθ
        have hyt : ξ.asIdeal ≤ (PrimeSpectrum.comap θ t).asIdeal := by
          have hξy : ξ.asIdeal ≤ y.asIdeal :=
            (PrimeSpectrum.asIdeal_le_asIdeal ξ y).mpr
              ((PrimeSpectrum.le_iff_mem_closure ξ y).mpr hyCG.1)
          simpa [hty] using hξy
          
        have hry : r ∉ y.asIdeal := (PrimeSpectrum.mem_basicOpen r y).mp hybasic
        have hrt : r ∉ (PrimeSpectrum.comap θ t).asIdeal := by
          intro hrt
          apply hry
          simpa [hty] using hrt
        have hmaple : p.map θ ≤ t.asIdeal := by
          apply Ideal.map_le_iff_le_comap.mpr
          simpa [p, PrimeSpectrum.comap_asIdeal] using hyt
        have hθr : θ r ∈ p.map θ := by
          rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
          exact ha
        apply hrt
        change θ r ∈ t.asIdeal
        exact hmaple hθr
      obtain ⟨q, hq⟩ :=
        ((Formalization.Books.Algebra.Unit30.domain_injective_dense_spectrum_image_conditions
          f).out 0 2).mp hf_inj
      let qT : PrimeSpectrum T :=
        PrimeSpectrum.comap (Ideal.Quotient.mk (p.map θ)) q
      have hqTcomap : PrimeSpectrum.comap θ qT = ξ := by
        apply PrimeSpectrum.ext
        change Ideal.comap θ
            (Ideal.comap (Ideal.Quotient.mk (p.map θ)) q.asIdeal) = ξ.asIdeal
        rw [Ideal.comap_comap]
        have hcomp :
            (f.comp (Ideal.Quotient.mk p)) =
              (Ideal.Quotient.mk (p.map θ)).comp θ := by
          exact Ideal.quotientMap_comp_mk (f := θ) (H := Ideal.le_comap_map)
        rw [← hcomp]
        rw [← Ideal.comap_comap, hq]
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      change ξ ∈ F
      refine ⟨PrimeSpectrum.comap ψ qT, ?_, ?_⟩
      · rw [← hψrange]
        exact ⟨qT, rfl⟩
      · rw [← PrimeSpectrum.comap_comp_apply]
        exact hqTcomap

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
  let : IsJacobsonRing S := hφ.isJacobsonRing
  let : JacobsonSpace (PrimeSpectrum R) :=
    (jacobson_iff_primeSpectrum_isJacobsonSpace).mp inferInstance
  let : JacobsonSpace (PrimeSpectrum S) :=
    (jacobson_iff_primeSpectrum_isJacobsonSpace).mp inferInstance
  obtain ⟨traceX, htraceX, -, -, -⟩ :=
    Formalization.Books.Topology.Unit18.exists_constructible_closedPoint_correspondence
      (X := PrimeSpectrum R)
  obtain ⟨traceY, htraceY, -, -, -⟩ :=
    Formalization.Books.Topology.Unit18.exists_constructible_closedPoint_correspondence
      (X := PrimeSpectrum S)
  let imageYX : ConstructibleSet (PrimeSpectrum S) →
      ConstructibleSet (PrimeSpectrum R) := fun E =>
    ⟨PrimeSpectrum.comap φ '' (E : Set (PrimeSpectrum S)),
      finiteType_constructible_image_isConstructible φ hφ E.property⟩
  let imageY₀X₀ : ConstructibleSet (closedPoints (PrimeSpectrum S)) →
      ConstructibleSet (closedPoints (PrimeSpectrum R)) := fun E =>
    traceX (imageYX (traceY.symm E))
  refine ⟨imageYX, imageY₀X₀, traceX, traceY, ?_, ?_, ?_, ?_, ?_⟩
  · intro E
    rfl
  · intro E
    let F := traceY.symm E
    have hformula := jacobson_constructible_image_closedPoint_formula
      φ hφ F.property
    have htrace : (traceY F : Set (closedPoints (PrimeSpectrum S))) = E := by
      exact congrArg Subtype.val (traceY.apply_symm_apply E)
    have hclosed :
        (Subtype.val : closedPoints (PrimeSpectrum R) → PrimeSpectrum R) ''
            (imageY₀X₀ E : Set (closedPoints (PrimeSpectrum R))) =
          closedPointPart (imageYX F : Set (PrimeSpectrum R)) := by
      rw [show imageY₀X₀ E = traceX (imageYX F) by rfl]
      rw [htraceX]
      simp [Formalization.Books.Topology.Unit18.closedPointTrace,
        closedPointPart, Set.inter_comm]
    rw [hclosed]
    have htrace_val : (F : Set (PrimeSpectrum S)) ∩ closedPoints (PrimeSpectrum S) =
        Set.image (Subtype.val : closedPoints (PrimeSpectrum S) → PrimeSpectrum S)
          (E : Set (closedPoints (PrimeSpectrum S))) := by
      calc
        (F : Set (PrimeSpectrum S)) ∩ closedPoints (PrimeSpectrum S) =
            Set.image (Subtype.val : closedPoints (PrimeSpectrum S) → PrimeSpectrum S)
              (traceY F : Set (closedPoints (PrimeSpectrum S))) := by
          rw [htraceY]
          simp [Formalization.Books.Topology.Unit18.closedPointTrace,
            Set.inter_comm]
        _ = Set.image (Subtype.val : closedPoints (PrimeSpectrum S) → PrimeSpectrum S)
              (E : Set (closedPoints (PrimeSpectrum S))) := by rw [htrace]
    rw [← hformula.2.1, htrace_val]
  · intro E
    rw [htraceX]
    simp [Formalization.Books.Topology.Unit18.closedPointTrace,
      closedPointPart, Set.inter_comm]
  · intro E
    rw [htraceY]
    simp [Formalization.Books.Topology.Unit18.closedPointTrace,
      closedPointPart, Set.inter_comm]
  · intro E
    change traceX (imageYX E) =
      traceX (imageYX (traceY.symm (traceY E)))
    rw [traceY.symm_apply_apply]

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
  ext p
  constructor
  · intro hp
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hprod : MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1 ∈ p := by
      apply hp.le
      exact Ideal.subset_span (by simp)
    rcases hp.isPrime.mem_or_mem hprod with h₀ | h₁
    · left
      apply le_antisymm
      · apply hp.2
        · refine ⟨Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime, ?_⟩
          apply Ideal.span_le.mpr
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst x
          simpa [productZeroXAxisIdeal, mul_comm] using
            (productZeroXAxisIdeal k).mul_mem_left
              (MvPolynomial.X (R := k) 1) (Ideal.mem_span_singleton_self _)
        · apply Ideal.span_le.mpr
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst x
          exact h₀
      · apply Ideal.span_le.mpr
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact h₀
    · right
      apply le_antisymm
      · apply hp.2
        · refine ⟨Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime, ?_⟩
          apply Ideal.span_le.mpr
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst x
          simpa [productZeroYAxisIdeal, mul_comm] using
            (productZeroYAxisIdeal k).mul_mem_left
              (MvPolynomial.X (R := k) 0) (Ideal.mem_span_singleton_self _)
        · apply Ideal.span_le.mpr
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst x
          exact h₁
      · apply Ideal.span_le.mpr
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact h₁
  · intro hp
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · refine ⟨?_, ?_⟩
      · refine ⟨Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime, ?_⟩
        apply Ideal.span_le.mpr
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        simpa [productZeroXAxisIdeal, mul_comm] using
          (productZeroXAxisIdeal k).mul_mem_left
            (MvPolynomial.X (R := k) 1) (Ideal.mem_span_singleton_self _)
      · intro q hq hqle
        have hprod : MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1 ∈ q := by
          exact hq.2 (Ideal.subset_span (by simp))
        rcases hq.1.mem_or_mem hprod with h₀ | h₁
        · exact q.span_singleton_le_iff_mem.mpr h₀
        · have hnot : MvPolynomial.X (R := k) 1 ∉ productZeroXAxisIdeal k := by
            intro h
            rw [productZeroXAxisIdeal, Ideal.mem_span_singleton'] at h
            obtain ⟨a, ha⟩ := h
            have he := congrArg (MvPolynomial.aeval (R := k) (![0, 1] : Fin 2 → k)) ha
            simp at he
          exact False.elim (hnot (hqle h₁))
    · refine ⟨?_, ?_⟩
      · refine ⟨Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime, ?_⟩
        apply Ideal.span_le.mpr
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        simpa [productZeroYAxisIdeal, mul_comm] using
          (productZeroYAxisIdeal k).mul_mem_left
            (MvPolynomial.X (R := k) 0) (Ideal.mem_span_singleton_self _)
      · intro q hq hqle
        have hprod : MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1 ∈ q := by
          exact hq.2 (Ideal.subset_span (by simp))
        rcases hq.1.mem_or_mem hprod with h₀ | h₁
        · have hnot : MvPolynomial.X (R := k) 0 ∉ productZeroYAxisIdeal k := by
            intro h
            rw [productZeroYAxisIdeal, Ideal.mem_span_singleton'] at h
            obtain ⟨a, ha⟩ := h
            have he := congrArg (MvPolynomial.aeval (R := k) (![1, 0] : Fin 2 → k)) ha
            simp at he
          exact False.elim (hnot (hqle h₀))
        · exact q.span_singleton_le_iff_mem.mpr h₁

theorem productZero_spectrum_has_two_irreducible_components
    (k : Type u) [Field k] :
    Nonempty
      (Fin 2 ≃ irreducibleComponents (PrimeSpectrum (ProductZeroRing k))) := by
  classical
  let I := productZeroRelationIdeal k
  have hmin : I.minimalPrimes =
      {productZeroXAxisIdeal k, productZeroYAxisIdeal k} :=
    productZero_minimalPrimes_are_the_two_axes k
  let f : minimalPrimes (ProductZeroRing k) → I.minimalPrimes := fun p =>
    ⟨Ideal.comap (Ideal.Quotient.mk I) p.1, by
      rw [Ideal.minimalPrimes_eq_comap]
      exact ⟨p.1, p.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
    exact congrArg Subtype.val hpq
  have hf_surj : Function.Surjective f := by
    intro p
    have hp : (p : Ideal (ProductZeroPolynomialRing k)) ∈ I.minimalPrimes := p.2
    have hpimage : (p : Ideal (ProductZeroPolynomialRing k)) ∈
        Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (ProductZeroRing k) := by
      exact (congrArg (fun s : Set (Ideal (ProductZeroPolynomialRing k)) =>
        (p : Ideal (ProductZeroPolynomialRing k)) ∈ s)
        (Ideal.minimalPrimes_eq_comap (I := I))).mp hp
    obtain ⟨q, hq, hqp⟩ := hpimage
    refine ⟨⟨q, hq⟩, ?_⟩
    apply Subtype.ext
    exact hqp
  let eMin : minimalPrimes (ProductZeroRing k) ≃ I.minimalPrimes :=
    Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hax : productZeroXAxisIdeal k ∈ I.minimalPrimes := by
    rw [hmin]
    simp
  have hay : productZeroYAxisIdeal k ∈ I.minimalPrimes := by
    rw [hmin]
    simp
  let ax : I.minimalPrimes := ⟨productZeroXAxisIdeal k, hax⟩
  let ay : I.minimalPrimes := ⟨productZeroYAxisIdeal k, hay⟩
  have hnotXAxis : MvPolynomial.X (R := k) 1 ∉ productZeroXAxisIdeal k := by
    intro h
    rw [productZeroXAxisIdeal, Ideal.mem_span_singleton'] at h
    obtain ⟨a, ha⟩ := h
    have he := congrArg (MvPolynomial.aeval (R := k) (![0, 1] : Fin 2 → k)) ha
    simp at he
  have hne : ax ≠ ay := by
    intro h
    apply hnotXAxis
    have hideal : productZeroXAxisIdeal k = productZeroYAxisIdeal k :=
      congrArg Subtype.val h
    rw [hideal]
    exact Ideal.mem_span_singleton_self _
  let g : Fin 2 → I.minimalPrimes := Fin.cases ax (fun _ => ay)
  have hg_inj : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have haxy := hij
      simp only [g, Fin.cases] at haxy
      exact (hne haxy).elim
    · have hya := hij
      simp only [g, Fin.cases] at hya
      exact (hne hya.symm).elim
    · rfl
  have hg_surj : Function.Surjective g := by
    intro p
    have hp : p.1 = productZeroXAxisIdeal k ∨
        p.1 = productZeroYAxisIdeal k := by
      have hp' : (p : Ideal (ProductZeroPolynomialRing k)) ∈ I.minimalPrimes := p.2
      have hp'' : (p : Ideal (ProductZeroPolynomialRing k)) ∈
          ({productZeroXAxisIdeal k, productZeroYAxisIdeal k} : Set _ ) := by
        exact (congrArg (fun s : Set (Ideal (ProductZeroPolynomialRing k)) =>
          (p : Ideal (ProductZeroPolynomialRing k)) ∈ s) hmin).mp hp'
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp''
    rcases hp with hax' | hay'
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      change productZeroXAxisIdeal k = p.1
      exact hax'.symm
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      change productZeroYAxisIdeal k = p.1
      exact hay'.symm
  let eAxes : Fin 2 ≃ I.minimalPrimes := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  let eComponents :=
    (minimalPrimes.equivIrreducibleComponents (ProductZeroRing k)).toEquiv
  exact ⟨eAxes.trans eMin.symm |>.trans (eComponents.trans OrderDual.ofDual)⟩
/-
  classical
  let I := productZeroRelationIdeal k
  have hmin : I.minimalPrimes =
      {productZeroXAxisIdeal k, productZeroYAxisIdeal k} :=
    productZero_minimalPrimes_are_the_two_axes k
  let f : minimalPrimes (ProductZeroRing k) → I.minimalPrimes := fun p =>
    ⟨Ideal.comap (Ideal.Quotient.mk I) p.1, by
      rw [Ideal.minimalPrimes_eq_comap]
      exact ⟨p.1, p.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
    exact congrArg Subtype.val hpq
  have hf_surj : Function.Surjective f := by
    intro p
    have hp : (p : Ideal (ProductZeroPolynomialRing k)) ∈ I.minimalPrimes := p.2
    have hpimage : (p : Ideal (ProductZeroPolynomialRing k)) ∈
        Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (ProductZeroRing k) := by
      exact (congrArg (fun s : Set (Ideal (ProductZeroPolynomialRing k)) =>
        (p : Ideal (ProductZeroPolynomialRing k)) ∈ s)
        (Ideal.minimalPrimes_eq_comap (I := I))).mp hp
    obtain ⟨q, hq, hqp⟩ := hpimage
    refine ⟨⟨q, hq⟩, ?_⟩
    apply Subtype.ext
    exact hqp
  let eMin : minimalPrimes (ProductZeroRing k) ≃ I.minimalPrimes :=
    Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hax : productZeroXAxisIdeal k ∈ I.minimalPrimes := by
    rw [hmin]
    simp
  have hay : productZeroYAxisIdeal k ∈ I.minimalPrimes := by
    rw [hmin]
    simp
  let ax : I.minimalPrimes := ⟨productZeroXAxisIdeal k, hax⟩
  let ay : I.minimalPrimes := ⟨productZeroYAxisIdeal k, hay⟩
  have hnotXAxis : MvPolynomial.X (R := k) 1 ∉ productZeroXAxisIdeal k := by
    intro h
    rw [productZeroXAxisIdeal, Ideal.mem_span_singleton'] at h
    obtain ⟨a, ha⟩ := h
    have he := congrArg (MvPolynomial.aeval (R := k) (![0, 1] : Fin 2 → k)) ha
    simpa using he
  have hne : ax ≠ ay := by
    intro h
    apply hnotXAxis
    have hideal : productZeroXAxisIdeal k = productZeroYAxisIdeal k :=
      congrArg Subtype.val h
    rw [hideal]
    exact Ideal.mem_span_singleton_self _
  let g : Fin 2 → I.minimalPrimes := Fin.cases ax (fun _ => ay)
  have hg_inj : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g, hne]
  have hg_surj : Function.Surjective g := by
    intro p
    have hp : p.1 = productZeroXAxisIdeal k ∨
        p.1 = productZeroYAxisIdeal k := by
      have hp' : (p : Ideal (ProductZeroPolynomialRing k)) ∈ I.minimalPrimes := p.2
      have hp'' : (p : Ideal (ProductZeroPolynomialRing k)) ∈
          ({productZeroXAxisIdeal k, productZeroYAxisIdeal k} : Set _ ) := by
        exact (congrArg (fun s : Set (Ideal (ProductZeroPolynomialRing k)) =>
          (p : Ideal (ProductZeroPolynomialRing k)) ∈ s) hmin).mp hp'
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp''
    rcases hp with hax' | hay'
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      simpa [g, ax] using hax'.symm
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      simpa [g, ay] using hay'.symm
  let eAxes : Fin 2 ≃ I.minimalPrimes := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  let eComponents :=
    (minimalPrimes.equivIrreducibleComponents (ProductZeroRing k)).toEquiv
  exact ⟨eAxes.trans eMin.symm |>.trans (eComponents.trans OrderDual.ofDual)⟩ -/

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

private theorem closedPoints_mvPolynomial_equiv
    (k : Type u) [Field k] [IsAlgClosed k] (σ : Type v) [Finite σ] :
    Nonempty
      (closedPoints (PrimeSpectrum (MvPolynomial σ k)) ≃ (σ → k)) := by
  classical
  let f : (σ → k) → closedPoints (PrimeSpectrum (MvPolynomial σ k)) := fun x =>
    let hmax : (MvPolynomial.vanishingIdeal k ({x} : Set (σ → k))).IsMaximal :=
      inferInstance
    ⟨MvPolynomial.pointToPoint x,
      mem_closedPoints_iff.mpr
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal
          (MvPolynomial.pointToPoint x)).mpr hmax)⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    funext i
    let p := MvPolynomial.X i - MvPolynomial.C (x i)
    have hpx : p ∈ (f x).1.asIdeal := by
      change p ∈ (MvPolynomial.vanishingIdeal k ({x} : Set (σ → k)))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp [p]
    have hpy : p ∈ (f y).1.asIdeal := by
      rw [← hxy]
      exact hpx
    change p ∈ (MvPolynomial.vanishingIdeal k ({y} : Set (σ → k))) at hpy
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hpy
    exact (sub_eq_zero.mp (by simpa [p] using hpy)).symm
  have hf_surj : Function.Surjective f := by
    intro p
    have hpmax : p.1.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal p.1).mp
        (mem_closedPoints_iff.mp p.2)
    obtain ⟨x, hx⟩ :=
      MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hpmax
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply PrimeSpectrum.ext
    simpa [f, MvPolynomial.pointToPoint] using hx.symm
  exact ⟨(Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm⟩

theorem productZero_closedPoints_are_algebraic_solutions
    (k : Type u) [Field k] (hk : IsAlgClosed k) :
    Nonempty
      (closedPoints (PrimeSpectrum (ProductZeroRing k)) ≃ ProductZeroSolution k) := by
  classical
  let I : Ideal (ProductZeroPolynomialRing k) := productZeroRelationIdeal k
  let mk : ProductZeroPolynomialRing k →+* ProductZeroRing k := Ideal.Quotient.mk I
  let P : closedPoints (PrimeSpectrum (ProductZeroRing k)) →
      Ideal (ProductZeroPolynomialRing k) := fun q =>
    Ideal.comap mk q.1.asIdeal
  have hPmax (q : closedPoints (PrimeSpectrum (ProductZeroRing k))) :
      (P q).IsMaximal := by
    have hqmax : q.1.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q.1).mp
        (mem_closedPoints_iff.mp q.2)
    let : q.1.asIdeal.IsMaximal := hqmax
    dsimp [P]
    exact Ideal.comap_isMaximal_of_surjective mk Ideal.Quotient.mk_surjective
  let x : closedPoints (PrimeSpectrum (ProductZeroRing k)) → Fin 2 → k := fun q =>
    Classical.choose (MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k (hPmax q))
  have hx (q : closedPoints (PrimeSpectrum (ProductZeroRing k))) :
      P q = MvPolynomial.vanishingIdeal k ({x q} : Set (Fin 2 → k)) :=
    Classical.choose_spec
      (MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k (hPmax q))
  have hIP (q : closedPoints (PrimeSpectrum (ProductZeroRing k))) : I ≤ P q := by
    intro r hr
    change mk r ∈ q.1.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact q.1.asIdeal.zero_mem
  have hcoord : ∀ a b : Fin 2 → k,
      MvPolynomial.vanishingIdeal k ({a} : Set (Fin 2 → k)) =
        MvPolynomial.vanishingIdeal k ({b} : Set (Fin 2 → k)) → a = b := by
    intro a b hab
    funext i
    let p := MvPolynomial.X i - MvPolynomial.C (a i)
    have hpb : p ∈ MvPolynomial.vanishingIdeal k ({b} : Set (Fin 2 → k)) := by
      rw [← hab, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp [p]
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hpb
    exact (sub_eq_zero.mp (by simpa [p] using hpb)).symm
  let f : closedPoints (PrimeSpectrum (ProductZeroRing k)) → ProductZeroSolution k :=
    fun q => ⟨(x q 0, x q 1), by
      have hrel : MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1 ∈ P q := by
        apply hIP q
        change MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1 ∈
          productZeroRelationIdeal k
        exact Ideal.subset_span (by simp)
      have hrel' : MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1 ∈
          MvPolynomial.vanishingIdeal k ({x q} : Set (Fin 2 → k)) := by
        rw [← hx q]
        exact hrel
      have heval := (MvPolynomial.mem_vanishingIdeal_singleton_iff (x q)
        (MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1)).mp hrel'
      simpa using heval⟩
  have hf_inj : Function.Injective f := by
    intro q r hqr
    have hxr : x q = x r := by
      funext i
      fin_cases i
      · exact congrArg (fun z : ProductZeroSolution k => z.1.1) hqr
      · exact congrArg (fun z : ProductZeroSolution k => z.1.2) hqr
    apply Subtype.ext
    apply PrimeSpectrum.ext
    apply Ideal.comap_injective_of_surjective mk Ideal.Quotient.mk_surjective
    change P q = P r
    rw [hx q, hx r, hxr]
  have hf_surj : Function.Surjective f := by
    intro z
    let zfun : Fin 2 → k := ![z.1.1, z.1.2]
    let J : Ideal (ProductZeroPolynomialRing k) :=
      MvPolynomial.vanishingIdeal k ({zfun} : Set (Fin 2 → k))
    have hrelJ : MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1 ∈ J := by
      change MvPolynomial.X (R := k) 0 * MvPolynomial.X (R := k) 1 ∈
        MvPolynomial.vanishingIdeal k ({zfun} : Set (Fin 2 → k))
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simpa [zfun] using z.2
    have hIJ : I ≤ J := by
      change productZeroRelationIdeal k ≤ J
      rw [productZeroRelationIdeal]
      apply Ideal.span_le.mpr
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      exact hrelJ
    let qIdeal : Ideal (ProductZeroRing k) := Ideal.map mk J
    have hker : RingHom.ker mk ≤ J := by
      rw [Ideal.mk_ker]
      exact hIJ
    let : J.IsMaximal := inferInstance
    have hqmax : qIdeal.IsMaximal := by
      dsimp [qIdeal]
      exact Ideal.IsMaximal.map_of_surjective_of_ker_le
        Ideal.Quotient.mk_surjective hker
    let q : closedPoints (PrimeSpectrum (ProductZeroRing k)) :=
      ⟨⟨qIdeal, hqmax.isPrime⟩,
        mem_closedPoints_iff.mpr
          ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hqmax)⟩
    refine ⟨q, ?_⟩
    have hPq : P q = J := by
      change Ideal.comap mk (Ideal.map mk J) = J
      rw [Ideal.comap_map_of_surjective mk Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
    have hxx : x q = zfun := by
      apply hcoord (x q) zfun
      exact (hx q).symm.trans (hPq.trans rfl)
    apply Subtype.ext
    simp [f, zfun, hxx]
  exact ⟨Equiv.ofBijective f ⟨hf_inj, hf_surj⟩⟩

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
  let : IsAlgClosed k := hk
  obtain ⟨ePoly⟩ := closedPoints_mvPolynomial_equiv k (Fin 8)
  let idxX : Fin 2 → Fin 2 → Fin 8 :=
    Fin.cases (fun j => Fin.cases 0 (fun _ => 1) j)
      (fun _ => fun j => Fin.cases 2 (fun _ => 3) j)
  let idxY : Fin 2 → Fin 2 → Fin 8 :=
    Fin.cases (fun j => Fin.cases 4 (fun _ => 5) j)
      (fun _ => fun j => Fin.cases 6 (fun _ => 7) j)
  let toPair : (Fin 8 → k) → (Matrix2 k × Matrix2 k) := fun v =>
    (fun i j => v (idxX i j), fun i j => v (idxY i j))
  have htoPair_inj : Function.Injective toPair := by
    have hX00 : idxX 0 0 = 0 := by decide
    have hX01 : idxX 0 (Fin.succ 0) = 1 := by decide
    have hX10 : idxX (Fin.succ 0) 0 = 2 := by decide
    have hX11 : idxX (Fin.succ 0) (Fin.succ 0) = 3 := by decide
    have hY00 : idxY 0 0 = 4 := by decide
    have hY01 : idxY 0 (Fin.succ 0) = 5 := by decide
    have hY10 : idxY (Fin.succ 0) 0 = 6 := by decide
    have hY11 : idxY (Fin.succ 0) (Fin.succ 0) = 7 := by decide
    intro v w h
    funext n
    fin_cases n
    · have hh := congrArg (fun p : Matrix2 k × Matrix2 k => p.1 0 0) h
      change v (idxX 0 0) = w (idxX 0 0) at hh
      rw [hX00] at hh
      exact hh
    · have hh := congrArg (fun p : Matrix2 k × Matrix2 k => p.1 0 (Fin.succ 0)) h
      change v (idxX 0 (Fin.succ 0)) = w (idxX 0 (Fin.succ 0)) at hh
      rw [hX01] at hh
      exact hh
    · have hh := congrArg (fun p : Matrix2 k × Matrix2 k => p.1 (Fin.succ 0) 0) h
      change v (idxX (Fin.succ 0) 0) = w (idxX (Fin.succ 0) 0) at hh
      rw [hX10] at hh
      exact hh
    · have hh := congrArg
          (fun p : Matrix2 k × Matrix2 k => p.1 (Fin.succ 0) (Fin.succ 0)) h
      change v (idxX (Fin.succ 0) (Fin.succ 0)) =
        w (idxX (Fin.succ 0) (Fin.succ 0)) at hh
      rw [hX11] at hh
      exact hh
    · have hh := congrArg (fun p : Matrix2 k × Matrix2 k => p.2 0 0) h
      change v (idxY 0 0) = w (idxY 0 0) at hh
      rw [hY00] at hh
      exact hh
    · have hh := congrArg (fun p : Matrix2 k × Matrix2 k => p.2 0 (Fin.succ 0)) h
      change v (idxY 0 (Fin.succ 0)) = w (idxY 0 (Fin.succ 0)) at hh
      rw [hY01] at hh
      exact hh
    · have hh := congrArg (fun p : Matrix2 k × Matrix2 k => p.2 (Fin.succ 0) 0) h
      change v (idxY (Fin.succ 0) 0) = w (idxY (Fin.succ 0) 0) at hh
      rw [hY10] at hh
      exact hh
    · have hh := congrArg
          (fun p : Matrix2 k × Matrix2 k => p.2 (Fin.succ 0) (Fin.succ 0)) h
      change v (idxY (Fin.succ 0) (Fin.succ 0)) =
        w (idxY (Fin.succ 0) (Fin.succ 0)) at hh
      rw [hY11] at hh
      exact hh
  have htoPair_surj : Function.Surjective toPair := by
    have hX00 : idxX 0 0 = 0 := by decide
    have hX01 : idxX 0 (Fin.succ 0) = 1 := by decide
    have hX10 : idxX (Fin.succ 0) 0 = 2 := by decide
    have hX11 : idxX (Fin.succ 0) (Fin.succ 0) = 3 := by decide
    have hY00 : idxY 0 0 = 4 := by decide
    have hY01 : idxY 0 (Fin.succ 0) = 5 := by decide
    have hY10 : idxY (Fin.succ 0) 0 = 6 := by decide
    have hY11 : idxY (Fin.succ 0) (Fin.succ 0) = 7 := by decide
    intro p
    let v : Fin 8 → k :=
      ![p.1 0 0, p.1 0 1, p.1 1 0, p.1 1 1,
        p.2 0 0, p.2 0 1, p.2 1 0, p.2 1 1]
    refine ⟨v, ?_⟩
    apply Prod.ext
    · funext i j
      fin_cases i
      · fin_cases j
        · change v (idxX 0 0) = p.1 0 0
          rw [hX00]
          simp [v]
        · change v (idxX 0 (Fin.succ 0)) = p.1 0 (Fin.succ 0)
          rw [hX01]
          simp [v]
      · fin_cases j
        · change v (idxX (Fin.succ 0) 0) = p.1 (Fin.succ 0) 0
          rw [hX10]
          simp [v]
        · change v (idxX (Fin.succ 0) (Fin.succ 0)) =
            p.1 (Fin.succ 0) (Fin.succ 0)
          rw [hX11]
          simp [v]
    · funext i j
      fin_cases i
      · fin_cases j
        · change v (idxY 0 0) = p.2 0 0
          rw [hY00]
          simp [v]
        · change v (idxY 0 (Fin.succ 0)) = p.2 0 (Fin.succ 0)
          rw [hY01]
          simp [v]
      · fin_cases j
        · change v (idxY (Fin.succ 0) 0) = p.2 (Fin.succ 0) 0
          rw [hY10]
          simp [v]
        · change v (idxY (Fin.succ 0) (Fin.succ 0)) =
            p.2 (Fin.succ 0) (Fin.succ 0)
          rw [hY11]
          simp [v]
  let eCoord : (Fin 8 → k) ≃ (Matrix2 k × Matrix2 k) :=
    Equiv.ofBijective toPair ⟨htoPair_inj, htoPair_surj⟩
  exact ⟨ePoly.trans eCoord⟩

theorem matrixPair_closedPoints_are_product_zero_solutions
    (k : Type u) [Field k] (hk : IsAlgClosed k) :
    Nonempty
      (closedPoints (PrimeSpectrum (MatrixPairRing k)) ≃ MatrixPairSolution k) := by
  classical
  let I : Ideal (MatrixPairPolynomial k) := matrixProductIdeal (k := k)
  let mk : MatrixPairPolynomial k →+* MatrixPairRing k := Ideal.Quotient.mk I
  let P : closedPoints (PrimeSpectrum (MatrixPairRing k)) →
      Ideal (MatrixPairPolynomial k) := fun q =>
    Ideal.comap mk q.1.asIdeal
  have hPmax (q : closedPoints (PrimeSpectrum (MatrixPairRing k))) :
      (P q).IsMaximal := by
    have hqmax : q.1.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q.1).mp
        (mem_closedPoints_iff.mp q.2)
    let : q.1.asIdeal.IsMaximal := hqmax
    dsimp [P]
    exact Ideal.comap_isMaximal_of_surjective mk Ideal.Quotient.mk_surjective
  let x : closedPoints (PrimeSpectrum (MatrixPairRing k)) → Fin 8 → k := fun q =>
    Classical.choose
      (MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k (hPmax q))
  have hx (q : closedPoints (PrimeSpectrum (MatrixPairRing k))) :
      P q = MvPolynomial.vanishingIdeal k ({x q} : Set (Fin 8 → k)) :=
    Classical.choose_spec
      (MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k (hPmax q))
  have hIP (q : closedPoints (PrimeSpectrum (MatrixPairRing k))) : I ≤ P q := by
    intro r hr
    change mk r ∈ q.1.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact q.1.asIdeal.zero_mem
  let idxX : Fin 2 → Fin 2 → Fin 8 :=
    Fin.cases (fun j => Fin.cases 0 (fun _ => 1) j)
      (fun _ => fun j => Fin.cases 2 (fun _ => 3) j)
  let idxY : Fin 2 → Fin 2 → Fin 8 :=
    Fin.cases (fun j => Fin.cases 4 (fun _ => 5) j)
      (fun _ => fun j => Fin.cases 6 (fun _ => 7) j)
  have hX00 : idxX 0 0 = 0 := by decide
  have hX01 : idxX 0 1 = 1 := by decide
  have hX10 : idxX 1 0 = 2 := by decide
  have hX11 : idxX 1 1 = 3 := by decide
  have hY00 : idxY 0 0 = 4 := by decide
  have hY01 : idxY 0 1 = 5 := by decide
  have hY10 : idxY 1 0 = 6 := by decide
  have hY11 : idxY 1 1 = 7 := by decide
  have hcoord : ∀ a b : Fin 8 → k,
      MvPolynomial.vanishingIdeal k ({a} : Set (Fin 8 → k)) =
        MvPolynomial.vanishingIdeal k ({b} : Set (Fin 8 → k)) → a = b := by
    intro a b hab
    funext i
    let p := MvPolynomial.X i - MvPolynomial.C (a i)
    have hpb : p ∈ MvPolynomial.vanishingIdeal k ({b} : Set (Fin 8 → k)) := by
      rw [← hab, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp [p]
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hpb
    exact (sub_eq_zero.mp (by simpa [p] using hpb)).symm
  let f : closedPoints (PrimeSpectrum (MatrixPairRing k)) → MatrixPairSolution k :=
    fun q =>
      let Xq : Matrix2 k := fun i j => x q (idxX i j)
      let Yq : Matrix2 k := fun i j => x q (idxY i j)
      ⟨(Xq, Yq), by
        have h00 : x q (idxX 0 0) * x q (idxY 0 0) +
            x q (idxX 0 1) * x q (idxY 1 0) = 0 := by
          have hp : matrixPairX11 (k := k) * matrixPairY11 (k := k) +
              matrixPairX12 (k := k) * matrixPairY21 (k := k) ∈ P q := by
            apply hIP q
            exact Ideal.subset_span (by simp [matrixPairProductEquations])
          rw [hx q] at hp
          have heval := (MvPolynomial.mem_vanishingIdeal_singleton_iff (x q)
            (matrixPairX11 (k := k) * matrixPairY11 (k := k) +
              matrixPairX12 (k := k) * matrixPairY21 (k := k))).mp hp
          simpa [matrixPairX11, matrixPairX12, matrixPairY11, matrixPairY21,
            matrixPairVariable, idxX, idxY, hX00, hX01, hY00, hY10] using heval
        have h01 : x q (idxX 0 0) * x q (idxY 0 1) +
            x q (idxX 0 1) * x q (idxY 1 1) = 0 := by
          have hp : matrixPairX11 (k := k) * matrixPairY12 (k := k) +
              matrixPairX12 (k := k) * matrixPairY22 (k := k) ∈ P q := by
            apply hIP q
            exact Ideal.subset_span (by simp [matrixPairProductEquations])
          rw [hx q] at hp
          have heval := (MvPolynomial.mem_vanishingIdeal_singleton_iff (x q)
            (matrixPairX11 (k := k) * matrixPairY12 (k := k) +
              matrixPairX12 (k := k) * matrixPairY22 (k := k))).mp hp
          simpa [matrixPairX11, matrixPairX12, matrixPairY12, matrixPairY22,
            matrixPairVariable, idxX, idxY, hX00, hX01, hY01, hY11] using heval
        have h10 : x q (idxX 1 0) * x q (idxY 0 0) +
            x q (idxX 1 1) * x q (idxY 1 0) = 0 := by
          have hp : matrixPairX21 (k := k) * matrixPairY11 (k := k) +
              matrixPairX22 (k := k) * matrixPairY21 (k := k) ∈ P q := by
            apply hIP q
            exact Ideal.subset_span (by simp [matrixPairProductEquations])
          rw [hx q] at hp
          have heval := (MvPolynomial.mem_vanishingIdeal_singleton_iff (x q)
            (matrixPairX21 (k := k) * matrixPairY11 (k := k) +
              matrixPairX22 (k := k) * matrixPairY21 (k := k))).mp hp
          simpa [matrixPairX21, matrixPairX22, matrixPairY11, matrixPairY21,
            matrixPairVariable, idxX, idxY, hX10, hX11, hY00, hY10] using heval
        have h11 : x q (idxX 1 0) * x q (idxY 0 1) +
            x q (idxX 1 1) * x q (idxY 1 1) = 0 := by
          have hp : matrixPairX21 (k := k) * matrixPairY12 (k := k) +
              matrixPairX22 (k := k) * matrixPairY22 (k := k) ∈ P q := by
            apply hIP q
            exact Ideal.subset_span (by simp [matrixPairProductEquations])
          rw [hx q] at hp
          have heval := (MvPolynomial.mem_vanishingIdeal_singleton_iff (x q)
            (matrixPairX21 (k := k) * matrixPairY12 (k := k) +
              matrixPairX22 (k := k) * matrixPairY22 (k := k))).mp hp
          simpa [matrixPairX21, matrixPairX22, matrixPairY12, matrixPairY22,
            matrixPairVariable, idxX, idxY, hX10, hX11, hY01, hY11] using heval
        ext i j
        fin_cases i <;> fin_cases j
        · change (Xq * Yq) 0 0 = 0
          simpa [Matrix.mul_apply] using h00
        · change (Xq * Yq) 0 1 = 0
          simpa [Matrix.mul_apply] using h01
        · change (Xq * Yq) 1 0 = 0
          simpa [Matrix.mul_apply] using h10
        · change (Xq * Yq) 1 1 = 0
          simpa [Matrix.mul_apply] using h11⟩
  have hf_inj : Function.Injective f := by
    intro q r hqr
    have hxr : x q = x r := by
      funext i
      fin_cases i
      · have hh := congrArg (fun z : MatrixPairSolution k => z.1.1 0 0) hqr
        simpa [f, idxX, idxY, hX00, hY00] using hh
      · have hh := congrArg (fun z : MatrixPairSolution k => z.1.1 0 1) hqr
        simpa [f, idxX, idxY, hX01, hY01] using hh
      · have hh := congrArg (fun z : MatrixPairSolution k => z.1.1 1 0) hqr
        simpa [f, idxX, idxY, hX10, hY10] using hh
      · have hh := congrArg (fun z : MatrixPairSolution k => z.1.1 1 1) hqr
        simpa [f, idxX, idxY, hX11, hY11] using hh
      · have hh := congrArg (fun z : MatrixPairSolution k => z.1.2 0 0) hqr
        simpa [f, idxX, idxY, hX00, hY00] using hh
      · have hh := congrArg (fun z : MatrixPairSolution k => z.1.2 0 1) hqr
        simpa [f, idxX, idxY, hX01, hY01] using hh
      · have hh := congrArg (fun z : MatrixPairSolution k => z.1.2 1 0) hqr
        simpa [f, idxX, idxY, hX10, hY10] using hh
      · have hh := congrArg (fun z : MatrixPairSolution k => z.1.2 1 1) hqr
        simpa [f, idxX, idxY, hX11, hY11] using hh
    apply Subtype.ext
    apply PrimeSpectrum.ext
    apply Ideal.comap_injective_of_surjective mk Ideal.Quotient.mk_surjective
    change P q = P r
    rw [hx q, hx r, hxr]
  have hf_surj : Function.Surjective f := by
    intro z
    let zfun : Fin 8 → k :=
      ![z.1.1 0 0, z.1.1 0 1, z.1.1 1 0, z.1.1 1 1,
        z.1.2 0 0, z.1.2 0 1, z.1.2 1 0, z.1.2 1 1]
    let J : Ideal (MatrixPairPolynomial k) :=
      MvPolynomial.vanishingIdeal k ({zfun} : Set (Fin 8 → k))
    have hIJ : I ≤ J := by
      change matrixProductIdeal (k := k) ≤ J
      rw [matrixProductIdeal]
      apply Ideal.span_le.mpr
      intro p hp
      rw [matrixPairProductEquations] at hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · change matrixPairX11 (k := k) * matrixPairY11 (k := k) +
          matrixPairX12 (k := k) * matrixPairY21 (k := k) ∈ J
        change matrixPairX11 (k := k) * matrixPairY11 (k := k) +
          matrixPairX12 (k := k) * matrixPairY21 (k := k) ∈
          MvPolynomial.vanishingIdeal k ({zfun} : Set (Fin 8 → k))
        rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
        simpa [matrixPairX11, matrixPairX12, matrixPairY11, matrixPairY21,
          matrixPairVariable, zfun, Matrix.mul_apply] using
          congrArg (fun M : Matrix2 k => M 0 0) z.2
      · change matrixPairX11 (k := k) * matrixPairY12 (k := k) +
          matrixPairX12 (k := k) * matrixPairY22 (k := k) ∈ J
        change matrixPairX11 (k := k) * matrixPairY12 (k := k) +
          matrixPairX12 (k := k) * matrixPairY22 (k := k) ∈
          MvPolynomial.vanishingIdeal k ({zfun} : Set (Fin 8 → k))
        rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
        simpa [matrixPairX11, matrixPairX12, matrixPairY12, matrixPairY22,
          matrixPairVariable, zfun, Matrix.mul_apply] using
          congrArg (fun M : Matrix2 k => M 0 1) z.2
      · change matrixPairX21 (k := k) * matrixPairY11 (k := k) +
          matrixPairX22 (k := k) * matrixPairY21 (k := k) ∈ J
        change matrixPairX21 (k := k) * matrixPairY11 (k := k) +
          matrixPairX22 (k := k) * matrixPairY21 (k := k) ∈
          MvPolynomial.vanishingIdeal k ({zfun} : Set (Fin 8 → k))
        rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
        simpa [matrixPairX21, matrixPairX22, matrixPairY11, matrixPairY21,
          matrixPairVariable, zfun, Matrix.mul_apply] using
          congrArg (fun M : Matrix2 k => M 1 0) z.2
      · change matrixPairX21 (k := k) * matrixPairY12 (k := k) +
          matrixPairX22 (k := k) * matrixPairY22 (k := k) ∈ J
        change matrixPairX21 (k := k) * matrixPairY12 (k := k) +
          matrixPairX22 (k := k) * matrixPairY22 (k := k) ∈
          MvPolynomial.vanishingIdeal k ({zfun} : Set (Fin 8 → k))
        rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
        simpa [matrixPairX21, matrixPairX22, matrixPairY12, matrixPairY22,
          matrixPairVariable, zfun, Matrix.mul_apply] using
          congrArg (fun M : Matrix2 k => M 1 1) z.2
    let qIdeal : Ideal (MatrixPairRing k) := Ideal.map mk J
    have hker : RingHom.ker mk ≤ J := by
      rw [Ideal.mk_ker]
      exact hIJ
    let : J.IsMaximal := inferInstance
    have hqmax : qIdeal.IsMaximal := by
      dsimp [qIdeal]
      exact Ideal.IsMaximal.map_of_surjective_of_ker_le
        Ideal.Quotient.mk_surjective hker
    let q : closedPoints (PrimeSpectrum (MatrixPairRing k)) :=
      ⟨⟨qIdeal, hqmax.isPrime⟩,
        mem_closedPoints_iff.mpr
          ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hqmax)⟩
    refine ⟨q, ?_⟩
    have hPq : P q = J := by
      change Ideal.comap mk (Ideal.map mk J) = J
      rw [Ideal.comap_map_of_surjective mk Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
    have hxx : x q = zfun := by
      apply hcoord (x q) zfun
      exact (hx q).symm.trans (hPq.trans rfl)
    apply Subtype.ext
    apply Prod.ext
    · funext i j
      fin_cases i <;> fin_cases j <;>
        simp [f, zfun, hxx, hX00, hX01, hX10, hX11]
    · funext i j
      fin_cases i <;> fin_cases j <;>
        simp [f, zfun, hxx, hY00, hY01, hY10, hY11]
  exact ⟨Equiv.ofBijective f ⟨hf_inj, hf_surj⟩⟩

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
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Matrix.mul_apply] using congrArg (fun M : Matrix2 k => M 0 0) h
    · simpa [Matrix.mul_apply] using congrArg (fun M : Matrix2 k => M 0 1) h
    · simpa [Matrix.mul_apply] using congrArg (fun M : Matrix2 k => M 1 0) h
    · simpa [Matrix.mul_apply] using congrArg (fun M : Matrix2 k => M 1 1) h
  · rintro ⟨h00, h01, h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply] using h00
    · simpa [Matrix.mul_apply] using h01
    · simpa [Matrix.mul_apply] using h10
    · simpa [Matrix.mul_apply] using h11

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
  simp [matrixPairAction]

theorem matrixPairAction_mul (k : Type u) [Field k]
    (g h : Matrix.GeneralLinearGroup (Fin 2) k ×
      Matrix.GeneralLinearGroup (Fin 2) k × Matrix.GeneralLinearGroup (Fin 2) k)
    (P : Matrix2 k × Matrix2 k) :
    matrixPairAction (g * h) P = matrixPairAction g (matrixPairAction h P) := by
  simp [matrixPairAction, mul_assoc]

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
