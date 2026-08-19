import Formalization.Books.Algebra.Unit63.AssociatedPrimes
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Topology.GDelta.Basic

/-!
# Commutative Algebra, Chapter 67: embedded primes

The source's associated primes are represented by the exact-annihilator
`PrimeSpectrum` set from Chapter 63.  Localization uses Mathlib's canonical
`LocalizedModule.Away` construction.
-/

namespace Formalization.Books.Algebra.Unit67

open Set

universe u v

noncomputable section

/-! ## Embedded associated primes -/

/-- The associated primes which are not minimal among the associated primes. -/
def embeddedAssociatedPrimes
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] : Set (PrimeSpectrum R) :=
  {p | p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M ∧
    ¬ Minimal
      (fun q : PrimeSpectrum R =>
        q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) p}

/-- The embedded primes of a ring, viewed as an `R`-module. -/
abbrev embeddedPrimes (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  embeddedAssociatedPrimes (R := R) (M := R)

/-! ## Removing embedded primes -/

/-- A support is nowhere dense in `Supp M` when regarded as a subset of the
subspace `Supp M` of `PrimeSpectrum R`. -/
def supportNowhereDenseInSupport
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (K : Submodule R M) : Prop :=
  IsNowhereDense
    ({p : Module.support R M |
      (p : PrimeSpectrum R) ∈ Module.support R K} : Set (Module.support R M))

/-- The submodules considered when removing embedded primes. -/
def embeddedPrimeRemovalSubmodules
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] : Set (Submodule R M) :=
  {K | supportNowhereDenseInSupport (R := R) (M := M) K}

private lemma support_closed_in_support
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (K : Submodule R M) :
    IsClosed
      ({p : Module.support R M |
        (p : PrimeSpectrum R) ∈ Module.support R K} : Set (Module.support R M)) := by
  change IsClosed ((Subtype.val : Module.support R M → PrimeSpectrum R) ⁻¹'
    Module.support R K)
  rw [Module.support_eq_zeroLocus (M := K)]
  exact (PrimeSpectrum.isClosed_zeroLocus _).preimage continuous_subtype_val

private lemma module_support_closed_in_support
    {R : Type u} {M : Type v} {N : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] :
    IsClosed
      ({p : Module.support R M |
        (p : PrimeSpectrum R) ∈ Module.support R N} : Set (Module.support R M)) := by
  change IsClosed ((Subtype.val : Module.support R M → PrimeSpectrum R) ⁻¹'
    Module.support R N)
  rw [Module.support_eq_zeroLocus (M := N)]
  exact (PrimeSpectrum.isClosed_zeroLocus _).preimage continuous_subtype_val

private lemma support_sup_eq_union
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (K L : Submodule R M) :
    Module.support R (↥(K ⊔ L)) = Module.support R K ∪ Module.support R L := by
  rw [Module.support_eq_zeroLocus (M := ↥(K ⊔ L)),
    Module.support_eq_zeroLocus (M := K), Module.support_eq_zeroLocus (M := L)]
  change PrimeSpectrum.zeroLocus (Submodule.annihilator (K ⊔ L) : Set R) =
    PrimeSpectrum.zeroLocus (Submodule.annihilator K : Set R) ∪
      PrimeSpectrum.zeroLocus (Submodule.annihilator L : Set R)
  rw [Submodule.annihilator_sup, PrimeSpectrum.zeroLocus_inf]

private lemma nowhereDense_union_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAc : IsClosed A) (hBc : IsClosed B)
    (hA : IsNowhereDense A) (hB : IsNowhereDense B) :
    IsNowhereDense (A ∪ B) := by
  apply (hAc.union hBc).isNowhereDense_iff.mpr
  rw [interior_union_isClosed_of_interior_empty hAc
    (hBc.isNowhereDense_iff.mp hB)]
  exact hAc.isNowhereDense_iff.mp hA

private lemma support_sup_nowhereDense
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] {K L : Submodule R M}
    (hK : supportNowhereDenseInSupport (R := R) (M := M) K)
    (hL : supportNowhereDenseInSupport (R := R) (M := M) L) :
    supportNowhereDenseInSupport (R := R) (M := M) (K ⊔ L) := by
  rw [supportNowhereDenseInSupport, support_sup_eq_union]
  change IsNowhereDense
    (({p : Module.support R M |
      (p : PrimeSpectrum R) ∈ Module.support R K} : Set (Module.support R M)) ∪
      {p : Module.support R M |
        (p : PrimeSpectrum R) ∈ Module.support R L})
  exact nowhereDense_union_of_closed
    (support_closed_in_support (R := R) (M := M) K)
    (support_closed_in_support (R := R) (M := M) L) hK hL

private lemma minimal_support_not_mem_support
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (K : Submodule R M)
    (hK : supportNowhereDenseInSupport (R := R) (M := M) K)
    (q : PrimeSpectrum R)
    (hq : Minimal (fun p : PrimeSpectrum R => p ∈ Module.support R M) q) :
    q ∉ Module.support R K := by
  classical
  intro hqK
  have hqass : q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M :=
    Formalization.Books.Algebra.Unit63.ass_of_minimal_support q hq.prop hq
  let s : Finset (PrimeSpectrum R) :=
    (Formalization.Books.Algebra.Unit63.finite_ass (R := R) (M := M)).toFinset
  have hqs : q ∈ s := by
    exact (Formalization.Books.Algebra.Unit63.finite_ass (R := R) (M := M)).mem_toFinset.mpr hqass
  have hnotle : ∀ r ∈ s, r ≠ q → ¬ r.asIdeal ≤ q.asIdeal := by
    intro r hr hrq hle
    have hrass : r ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M :=
      (Formalization.Books.Algebra.Unit63.finite_ass (R := R) (M := M)).mem_toFinset.mp hr
    apply hrq
    apply PrimeSpectrum.ext
    exact le_antisymm hle (hq.2 (y := r)
      (Formalization.Books.Algebra.Unit63.ass_subset_support hrass) hle)
  let g : s → R := fun r =>
    if h : (r : PrimeSpectrum R) = q then 1 else
      Classical.choose (SetLike.not_le_iff_exists.mp
        (hnotle r r.property h))
  have hgnot : ∀ r : s, g r ∉ q.asIdeal := by
    intro r
    by_cases hrq : (r : PrimeSpectrum R) = q
    · rw [show g r = 1 by simp [g, hrq]]
      intro hone
      apply q.isPrime.ne_top
      apply le_antisymm le_top
      intro x _
      simpa using q.asIdeal.mul_mem_left x hone
    · simpa [g, hrq] using
        (Classical.choose_spec
          (SetLike.not_le_iff_exists.mp (hnotle r r.property hrq))).2
  have hgmem : ∀ r : s, (r : PrimeSpectrum R) ≠ q →
      g r ∈ (r : PrimeSpectrum R).asIdeal := by
    intro r hrq
    simpa [g, hrq] using
      (Classical.choose_spec
        (SetLike.not_le_iff_exists.mp (hnotle r r.property hrq))).1
  let f : R := Finset.univ.prod g
  have hfq : f ∉ q.asIdeal := by
    intro hf
    obtain ⟨r, hr, hrf⟩ :=
      (q.isPrime.prod_mem_iff (s := Finset.univ) (x := g)).mp hf
    exact hgnot r hrf
  have hfass : ∀ r ∈ s, r ≠ q → f ∈ r.asIdeal := by
    intro r hr hrq
    change Finset.univ.prod g ∈ r.asIdeal
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g (Finset.mem_univ ⟨r, hr⟩)
    rw [hc]
    rw [mul_comm]
    exact r.asIdeal.mul_mem_left c (hgmem ⟨r, hr⟩ hrq)
  have hopen :
      {p : Module.support R M |
        f ∉ (p : PrimeSpectrum R).asIdeal} ⊆
        {p : Module.support R M |
          (p : PrimeSpectrum R) ∈ Module.support R K} := by
    intro p hp
    obtain ⟨I, hI, hIp⟩ :=
      Ideal.exists_minimalPrimes_le
        (J := (p : PrimeSpectrum R).asIdeal)
        (Module.mem_support_iff_of_finite.mp p.property)
    let r : PrimeSpectrum R := ⟨I, hI.isPrime⟩
    have hrM : r ∈ Module.support R M := by
      rw [Module.support_eq_zeroLocus]
      exact hI.le
    have hrmin : Minimal (fun z : PrimeSpectrum R => z ∈ Module.support R M) r := by
      refine ⟨hrM, ?_⟩
      intro z hz hzr
      exact hI.2 ⟨z.isPrime, Module.mem_support_iff_of_finite.mp hz⟩ hzr
    have hrass : r ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M :=
      Formalization.Books.Algebra.Unit63.ass_of_minimal_support r hrmin.prop hrmin
    have hrs : r ∈ s :=
      (Formalization.Books.Algebra.Unit63.finite_ass (R := R) (M := M)).mem_toFinset.mpr hrass
    have hrq : r = q := by
      by_contra hrq
      have hfr : f ∈ r.asIdeal := hfass r hrs hrq
      exact hp (hIp hfr)
    have hKq : Module.annihilator R K ≤ q.asIdeal :=
      Module.mem_support_iff_of_finite.mp hqK
    change (p : PrimeSpectrum R) ∈ Module.support R K
    rw [Module.mem_support_iff_of_finite]
    have hIp' : (r : PrimeSpectrum R).asIdeal ≤ (p : PrimeSpectrum R).asIdeal := hIp
    rw [hrq] at hIp'
    exact hKq.trans hIp'
  have hclosed := support_closed_in_support (R := R) (M := M) K
  have hqinterior :
      (⟨q, hq.prop⟩ : Module.support R M) ∈
        interior ({p : Module.support R M |
          (p : PrimeSpectrum R) ∈ Module.support R K} : Set (Module.support R M)) := by
    apply mem_interior.mpr
    refine ⟨_, hopen, (PrimeSpectrum.isOpen_basicOpen (a := f)).preimage
      continuous_subtype_val, ?_⟩
    simpa [PrimeSpectrum.mem_basicOpen] using hfq
  have hempty := hclosed.isNowhereDense_iff.mp hK
  rw [hempty] at hqinterior
  exact hqinterior

private lemma support_eq_support_quotient_of_nowhereDense
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (K : Submodule R M)
    (hK : supportNowhereDenseInSupport (R := R) (M := M) K) :
    Module.support R M = Module.support R (M ⧸ K) := by
  have hsupp : Module.support R M =
      Module.support R K ∪ Module.support R (M ⧸ K) :=
    Module.support_of_exact (f := K.subtype) (g := Submodule.mkQ K)
      (LinearMap.exact_subtype_mkQ K) (Submodule.injective_subtype K)
      (Submodule.mkQ_surjective K)
  apply subset_antisymm
  · intro p hp
    obtain ⟨I, hI, hIp⟩ :=
      Ideal.exists_minimalPrimes_le
        (J := p.asIdeal) (Module.mem_support_iff_of_finite.mp hp)
    let q : PrimeSpectrum R := ⟨I, hI.isPrime⟩
    have hqM : q ∈ Module.support R M := by
      rw [Module.support_eq_zeroLocus]
      exact hI.le
    have hqmin : Minimal (fun z : PrimeSpectrum R => z ∈ Module.support R M) q := by
      refine ⟨hqM, ?_⟩
      intro z hz hzq
      exact hI.2 ⟨z.isPrime, Module.mem_support_iff_of_finite.mp hz⟩ hzq
    have hqnotK := minimal_support_not_mem_support K hK q hqmin
    have hqquot : q ∈ Module.support R (M ⧸ K) := by
      have hq' : q ∈ Module.support R K ∪ Module.support R (M ⧸ K) := by
        rw [← hsupp]
        exact hqM
      exact hq'.resolve_left hqnotK
    exact Module.mem_support_mono hIp hqquot
  · exact Module.support_subset_of_surjective (Submodule.mkQ K)
      (Submodule.mkQ_surjective K)

private lemma associated_subset_of_injective
    {R : Type u} {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (hg : Function.Injective g) :
    Formalization.Books.Algebra.Unit63.associatedPrimes R M ⊆
      Formalization.Books.Algebra.Unit63.associatedPrimes R N := by
  intro p hp
  change ∃ m, (⊥ : Submodule R N).colon ({m} : Set N) = p.asIdeal
  change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
  obtain ⟨m, hm⟩ := hp
  refine ⟨g m, ?_⟩
  ext r
  rw [Submodule.mem_colon_singleton, ← hm, Submodule.mem_colon_singleton]
  change r • g m = 0 ↔ r • m = 0
  rw [← g.map_smul, map_eq_zero_iff g hg]

private lemma exists_minimal_support_le
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : PrimeSpectrum R)
    (hp : p ∈ Module.support R M) :
    ∃ q : PrimeSpectrum R,
      Minimal (fun z : PrimeSpectrum R => z ∈ Module.support R M) q ∧ q ≤ p := by
  obtain ⟨I, hI, hIp⟩ :=
    Ideal.exists_minimalPrimes_le
      (J := p.asIdeal) (Module.mem_support_iff_of_finite.mp hp)
  let q : PrimeSpectrum R := ⟨I, hI.isPrime⟩
  have hqM : q ∈ Module.support R M := by
    rw [Module.support_eq_zeroLocus]
    exact hI.le
  refine ⟨q, ?_, hIp⟩
  refine ⟨hqM, ?_⟩
  intro z hz hzq
  exact hI.2 ⟨z.isPrime, Module.mem_support_iff_of_finite.mp hz⟩ hzq

private lemma zeroLocus_nowhereDense_of_no_minimal_support
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R)
    (hI : ∀ q : PrimeSpectrum R,
      Minimal (fun z : PrimeSpectrum R => z ∈ Module.support R M) q →
        ¬ I ≤ q.asIdeal) :
    IsNowhereDense
      ({p : Module.support R M |
        (p : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus I} :
          Set (Module.support R M)) := by
  let S : Set (Module.support R M) :=
    {p : Module.support R M |
      (p : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus I}
  have hclosed : IsClosed S := by
    change IsClosed ((Subtype.val : Module.support R M → PrimeSpectrum R) ⁻¹'
      PrimeSpectrum.zeroLocus I)
    exact (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).preimage
      continuous_subtype_val
  rw [show ({p : Module.support R M |
      (p : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus I} :
        Set (Module.support R M)) = S from rfl]
  apply hclosed.isNowhereDense_iff.mpr
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  rcases mem_interior.mp hp with ⟨U, hUsub, hUopen, hpU⟩
  rcases isOpen_induced_iff.mp hUopen with ⟨V, hVopen, hVU⟩
  have hpV : (p : PrimeSpectrum R) ∈ V := by
    have : p ∈ (Subtype.val : Module.support R M → PrimeSpectrum R) ⁻¹' V := by
      rw [hVU]
      exact hpU
    exact this
  obtain ⟨B, ⟨f, rfl⟩, hpB, hBV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      hpV hVopen
  obtain ⟨q, hqmin, hqp⟩ := exists_minimal_support_le (R := R) (M := M) p.1 p.2
  have hqB : (q : PrimeSpectrum R) ∈ PrimeSpectrum.basicOpen f := by
    rw [PrimeSpectrum.mem_basicOpen]
    intro hfq
    exact hpB (hqp hfq)
  have hqU : (⟨q, hqmin.prop⟩ : Module.support R M) ∈ U := by
    rw [← hVU]
    exact hBV hqB
  exact hI q hqmin (hUsub hqU)

private lemma support_nowhereDense_of_no_minimal_support
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (K : Submodule R M)
    (hK : ∀ q : PrimeSpectrum R,
      Minimal (fun z : PrimeSpectrum R => z ∈ Module.support R M) q →
        q ∉ Module.support R K) :
    supportNowhereDenseInSupport (R := R) (M := M) K := by
  rw [supportNowhereDenseInSupport, Module.support_eq_zeroLocus (M := K)]
  apply zeroLocus_nowhereDense_of_no_minimal_support (R := R) (M := M)
  intro q hqmin hq
  have hqK : q ∈ Module.support R K := by
    rw [Module.support_eq_zeroLocus]
    exact hq
  exact hK q hqmin hqK

private lemma sup_span_mem_removal
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (K : Submodule R M)
    (hK : supportNowhereDenseInSupport (R := R) (M := M) K)
    (m : M) (q : PrimeSpectrum R)
    (hann : (⊥ : Submodule R (M ⧸ K)).colon
      ({Submodule.mkQ K m} : Set (M ⧸ K)) = q.asIdeal)
    (hq : ∀ p : PrimeSpectrum R,
      Minimal (fun z : PrimeSpectrum R => z ∈ Module.support R M) p →
        ¬ q.asIdeal ≤ p.asIdeal) :
    supportNowhereDenseInSupport (R := R) (M := M)
      (K ⊔ Submodule.span R ({m} : Set M)) := by
  let L : Submodule R M := K ⊔ Submodule.span R ({m} : Set M)
  have hspan : Module.support R (Submodule.span R
      ({Submodule.mkQ K m} : Set (M ⧸ K))) =
      PrimeSpectrum.zeroLocus (q.asIdeal : Set R) := by
    rw [Module.support_eq_zeroLocus]
    congr 1
    ext r
    change r ∈ Submodule.annihilator
        (Submodule.span R ({Submodule.mkQ K m} : Set (M ⧸ K))) ↔
      r ∈ q.asIdeal
    rw [Submodule.mem_annihilator_span_singleton]
    rw [← hann, Submodule.mem_colon_singleton]
    simp
  let g₀ : L →ₗ[R] M ⧸ K :=
    (Submodule.mkQ K).comp L.subtype
  have hg₀_mem : ∀ y : L, g₀ y ∈
      Submodule.span R ({Submodule.mkQ K m} : Set (M ⧸ K)) := by
    intro y
    rcases Submodule.mem_sup.mp y.property with ⟨a, ha, b, hb, hy⟩
    let y' : L := ⟨a + b,
      add_mem ((show K ≤ L from le_sup_left) ha)
        ((show Submodule.span R ({m} : Set M) ≤ L from le_sup_right) hb)⟩
    have hy' : y' = y := by
      apply Subtype.ext
      exact hy
    rw [← hy']
    dsimp [y', g₀]
    rw [(Submodule.Quotient.mk_eq_zero K).mpr ha, zero_add]
    refine Submodule.span_induction (p := fun z _ =>
      Submodule.mkQ K z ∈ Submodule.span R ({Submodule.mkQ K m} : Set (M ⧸ K)))
      ?_ ?_ ?_ ?_ hb
    · rintro z rfl
      exact Submodule.subset_span (by simp)
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx
  let g₁ : L →ₗ[R] Submodule.span R
      ({Submodule.mkQ K m} : Set (M ⧸ K)) :=
    g₀.codRestrict _ hg₀_mem
  have hker₁ : LinearMap.ker g₁ = K.submoduleOf L := by
    apply le_antisymm
    · intro y hy
      have hy0 : g₀ y = 0 := by
        have hy' : g₁ y = 0 := LinearMap.mem_ker.mp hy
        change g₀ y = 0
        exact congrArg Subtype.val hy'
      change Submodule.mkQ K (y : M) = 0 at hy0
      exact (Submodule.Quotient.mk_eq_zero K).mp hy0
    · intro y hy
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change g₀ y = 0
      dsimp [g₀]
      exact (Submodule.Quotient.mk_eq_zero K).mpr hy
  let g : (L ⧸ K.submoduleOf L) →ₗ[R]
      Submodule.span R ({Submodule.mkQ K m} : Set (M ⧸ K)) :=
    (K.submoduleOf L).liftQ g₁ (le_of_eq hker₁.symm)
  have hgker : LinearMap.ker g = ⊥ := by
    rw [Submodule.ker_liftQ]
    rw [hker₁]
    apply le_antisymm
    · rintro z ⟨y, hy, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero (K.submoduleOf L)).mpr hy
    · exact bot_le
  have hginj : Function.Injective g := LinearMap.ker_eq_bot.mp hgker
  have hsupport_quot : Module.support R (L ⧸ K.submoduleOf L) ⊆
      PrimeSpectrum.zeroLocus (q.asIdeal : Set R) := by
    rw [← hspan]
    exact Module.support_subset_of_injective g hginj
  have hqnd : IsNowhereDense
      ({p : Module.support R M |
        (p : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus (q.asIdeal : Set R)} :
          Set (Module.support R M)) := by
    apply zeroLocus_nowhereDense_of_no_minimal_support (R := R) (M := M)
    exact hq
  have hqnd' : IsNowhereDense
      ({p : Module.support R M |
        (p : PrimeSpectrum R) ∈ Module.support R (L ⧸ K.submoduleOf L)} :
          Set (Module.support R M)) := by
    apply IsNowhereDense.mono
    · intro p hp
      exact hsupport_quot hp
    · exact hqnd
  have hLsupport : Module.support R L =
      Module.support R K ∪ Module.support R (L ⧸ K.submoduleOf L) :=
    Module.support_of_exact
      (f := Submodule.inclusion (show K ≤ L from le_sup_left))
      (g := Submodule.mkQ (K.submoduleOf L))
      (by
        rw [LinearMap.exact_iff]
        ext y
        constructor
        · intro hy
          have hyK : (y : M) ∈ K :=
            (Submodule.Quotient.mk_eq_zero (K.submoduleOf L)).mp hy
          refine ⟨⟨y, hyK⟩, ?_⟩
          apply Subtype.ext
          exact Submodule.coe_inclusion (show K ≤ L from le_sup_left) ⟨y, hyK⟩
        · rintro ⟨x, rfl⟩
          apply LinearMap.mem_ker.mpr
          apply (Submodule.Quotient.mk_eq_zero (K.submoduleOf L)).mpr
          change (x : M) ∈ K
          exact x.property)
      (Submodule.inclusion_injective (show K ≤ L from le_sup_left))
      (Submodule.mkQ_surjective (K.submoduleOf L))
  rw [supportNowhereDenseInSupport, hLsupport]
  exact nowhereDense_union_of_closed
    (support_closed_in_support (R := R) (M := M) K)
    (module_support_closed_in_support (R := R) (M := M)
      (N := L ⧸ K.submoduleOf L)) hK hqnd'

private lemma support_subset_zeroLocus_of_embedded_contains
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (K : Submodule R M)
    (hK : supportNowhereDenseInSupport (R := R) (M := M) K)
    (f : R)
    (hf : ∀ p : PrimeSpectrum R,
      p ∈ embeddedAssociatedPrimes (R := R) (M := M) → f ∈ p.asIdeal) :
    Module.support R K ⊆ PrimeSpectrum.zeroLocus ({f} : Set R) := by
  intro p hp
  obtain ⟨I, hI, hIp⟩ :=
    Ideal.exists_minimalPrimes_le
      (J := p.asIdeal) (Module.mem_support_iff_of_finite.mp hp)
  let q : PrimeSpectrum R := ⟨I, hI.isPrime⟩
  have hqK : q ∈ Module.support R K := by
    rw [Module.support_eq_zeroLocus]
    exact hI.le
  have hqminK : Minimal (fun z : PrimeSpectrum R => z ∈ Module.support R K) q := by
    refine ⟨hqK, ?_⟩
    intro z hz hzq
    exact hI.2 ⟨z.isPrime, Module.mem_support_iff_of_finite.mp hz⟩ hzq
  have hqassK : q ∈
      Formalization.Books.Algebra.Unit63.associatedPrimes R K :=
    Formalization.Books.Algebra.Unit63.ass_of_minimal_support q hqminK.prop hqminK
  have hqassM : q ∈
      Formalization.Books.Algebra.Unit63.associatedPrimes R M :=
    associated_subset_of_injective K.subtype (Submodule.injective_subtype K) hqassK
  have hqnotminM : ¬ Minimal
      (fun z : PrimeSpectrum R => z ∈ Module.support R M) q := by
    intro hqminM
    exact minimal_support_not_mem_support K hK q hqminM hqK
  have hqnotminAss : ¬ Minimal
      (fun z : PrimeSpectrum R =>
        z ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) q := by
    intro hqminAss
    apply hqnotminM
    refine ⟨Formalization.Books.Algebra.Unit63.ass_subset_support hqassM, ?_⟩
    intro z hz hzq
    obtain ⟨r, hrmin, hrz⟩ := exists_minimal_support_le (R := R) (M := M) z hz
    have hrass := Formalization.Books.Algebra.Unit63.ass_of_minimal_support
      r hrmin.prop hrmin
    exact (hqminAss.2 hrass (hrz.trans hzq)).trans hrz
  have hqembedded : q ∈ embeddedAssociatedPrimes (R := R) (M := M) := by
    exact ⟨hqassM, hqnotminAss⟩
  rw [PrimeSpectrum.mem_zeroLocus]
  have hqp : q.asIdeal ≤ p.asIdeal := hIp
  exact Set.singleton_subset_iff.mpr (hqp (hf q hqembedded))

private def awayPrimeOfNotMem
    {R : Type u} [CommRing R] (f : R) (p : PrimeSpectrum R)
    (hp : f ∉ p.asIdeal) : PrimeSpectrum (Localization.Away f) :=
  ⟨p.asIdeal.map (algebraMap R (Localization.Away f)),
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) _ p.isPrime (by
        apply Set.disjoint_left.2
        intro x hxS hxP
        rcases hxS with ⟨n, rfl⟩
        exact (p.asIdeal.primeCompl.pow_mem hp n) hxP)⟩

private lemma comap_awayPrimeOfNotMem
    {R : Type u} [CommRing R] (f : R) (p : PrimeSpectrum R)
    (hp : f ∉ p.asIdeal) :
    PrimeSpectrum.comap (algebraMap R (Localization.Away f))
        (awayPrimeOfNotMem f p hp) = p := by
  apply PrimeSpectrum.ext
  simpa [awayPrimeOfNotMem, PrimeSpectrum.comap_asIdeal, Ideal.under_def] using
    (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) p.isPrime (by
        apply Set.disjoint_left.2
        intro x hxS hxP
        rcases hxS with ⟨n, rfl⟩
        exact (p.asIdeal.primeCompl.pow_mem hp n) hxP))

private lemma comap_mem_support_of_localized
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (K : Submodule R M) (f : R)
    (q : PrimeSpectrum (Localization.Away f))
    (hq : q ∈ Module.support (Localization.Away f)
      (K.localized (Submonoid.powers f))) :
    PrimeSpectrum.comap (algebraMap R (Localization.Away f)) q ∈
      Module.support R K := by
  rw [Module.support_eq_zeroLocus] at hq ⊢
  intro r hr
  apply hq
  apply Module.mem_annihilator.mpr
  intro z
  have hz := z.property
  change (z : LocalizedModule.Away f M) ∈
    Submodule.localized' (Localization.Away f) (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) K at hz
  rw [Submodule.localized'_eq_span] at hz
  apply Subtype.ext
  refine Submodule.span_induction (p := fun w _ =>
      (algebraMap R (Localization.Away f) r) • w = 0) ?_ ?_ ?_ ?_ hz
  · rintro w ⟨m, hm, rfl⟩
    have hrm : r • m = 0 := by
      exact congrArg Subtype.val
        (Module.mem_annihilator.mp hr ⟨m, hm⟩)
    simp [algebraMap_smul, LocalizedModule.smul'_mk,
      LocalizedModule.mkLinearMap_apply,
      hrm]
  · simp
  · intro x y _ _ hx hy
    rw [smul_add]
    simp [hx, hy]
  · intro c x _ hx
    rw [smul_smul]
    rw [mul_comm, ← smul_smul]
    simp [hx]

private lemma localized_removal_nowhereDense
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (K : Submodule R M)
    (hK : supportNowhereDenseInSupport (R := R) (M := M) K)
    (f : R) :
    supportNowhereDenseInSupport (R := Localization.Away f)
      (M := LocalizedModule.Away f M) (K.localized (Submonoid.powers f)) := by
  apply support_nowhereDense_of_no_minimal_support
  intro q hqmin hqK
  have hqassK : q ∈
      Formalization.Books.Algebra.Unit63.associatedPrimes (Localization.Away f)
        (K.localized (Submonoid.powers f)) :=
    Formalization.Books.Algebra.Unit63.ass_of_minimal_support q hqK (by
      refine ⟨hqK, ?_⟩
      intro z hz hzq
      exact hqmin.2
        (Module.support_subset_of_injective (K.localized (Submonoid.powers f)).subtype
          (Submodule.injective_subtype _) hz) hzq)
  have hqassM : q ∈
      Formalization.Books.Algebra.Unit63.associatedPrimes (Localization.Away f)
        (LocalizedModule.Away f M) :=
    associated_subset_of_injective (K.localized (Submonoid.powers f)).subtype
      (Submodule.injective_subtype _) hqassK
  let cmod : Module R (LocalizedModule.Away f M) :=
    Module.compHom (LocalizedModule.Away f M)
      (algebraMap R (Localization.Away f))
  have hbridge :
      PrimeSpectrum.comap (algebraMap R (Localization.Away f)) ''
          Formalization.Books.Algebra.Unit63.associatedPrimes
            (Localization.Away f) (LocalizedModule.Away f M) =
        @Formalization.Books.Algebra.Unit63.associatedPrimes R
          (LocalizedModule.Away f M) _ _ cmod := by
    simpa [cmod] using
      (Formalization.Books.Algebra.Unit63.ass_localize_eq_over_localization
        (M := M) (Submonoid.powers f))
  let p : PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (Localization.Away f)) q
  have hpRloc : p ∈
      @Formalization.Books.Algebra.Unit63.associatedPrimes R
        (LocalizedModule.Away f M) _ _ cmod := by
    rw [← hbridge]
    exact ⟨q, hqassM, rfl⟩
  have hasslocal :=
    Formalization.Books.Algebra.Unit63.ass_localize_eq_of_noetherian
      (R := R) (M := M) (Submonoid.powers f)
  have hpint : p ∈
      Formalization.Books.Algebra.Unit63.associatedPrimes R M ∩
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
    rw [hasslocal]
    simpa [cmod] using hpRloc
  have hpM : p ∈ Module.support R M :=
    Formalization.Books.Algebra.Unit63.ass_subset_support hpint.1
  have hpK : p ∈ Module.support R K :=
    comap_mem_support_of_localized K f q hqK
  have hpnotmin : ¬ Minimal (fun z : PrimeSpectrum R => z ∈ Module.support R M) p := by
    intro hpmin
    exact minimal_support_not_mem_support K hK p hpmin hpK
  obtain ⟨r, hrmin, hrp⟩ := exists_minimal_support_le (R := R) (M := M) p hpM
  have hrlt : r < p := by
    refine lt_of_le_of_ne hrp ?_
    intro heq
    apply hpnotmin
    simpa [heq] using hrmin
  have hfnotp : f ∉ p.asIdeal := by
    intro hfp
    apply Ideal.notMem_of_isUnit q.asIdeal
      (IsLocalization.map_units (Localization.Away f) ⟨f, Submonoid.mem_powers f⟩)
    exact hfp
  let q' : PrimeSpectrum (Localization.Away f) := awayPrimeOfNotMem f r
    (by
      intro hfr
      apply hfnotp
      exact hrp hfr)
  have hqinj : Function.Injective
      (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) :=
    (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f).injective
  have hq'comap : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) q' = r :=
    comap_awayPrimeOfNotMem f r (by
      intro hfr
      apply hfnotp
      exact hrp hfr)
  have hqle : q' ≤ q := by
    change q'.asIdeal ≤ q.asIdeal
    change r.asIdeal.map (algebraMap R (Localization.Away f)) ≤ q.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    exact hrp
  have hq'lt : q' < q := by
    refine lt_of_le_of_ne hqle ?_
    intro heq
    apply hrlt.ne
    rw [← hq'comap, heq]
  have hrassoc : r ∈
      Formalization.Books.Algebra.Unit63.associatedPrimes R M :=
    Formalization.Books.Algebra.Unit63.ass_of_minimal_support r hrmin.prop hrmin
  have hrloc : r ∈
      Formalization.Books.Algebra.Unit63.associatedPrimes R
        (LocalizedModule.Away f M) := by
    rw [← hasslocal]
    exact ⟨hrassoc, ⟨q', by
      change PrimeSpectrum.comap (algebraMap R (Localization.Away f)) q' = r
      exact hq'comap⟩⟩
  have hq'ass : q' ∈
      Formalization.Books.Algebra.Unit63.associatedPrimes (Localization.Away f)
        (LocalizedModule.Away f M) := by
    rw [← hbridge] at hrloc
    rcases hrloc with ⟨q₀, hq₀, hq₀comap⟩
    have heq : q₀ = q' := hqinj (hq₀comap.trans hq'comap.symm)
    simpa [heq] using hq₀
  exact (not_le_of_gt hq'lt)
    (hqmin.2 (Formalization.Books.Algebra.Unit63.ass_subset_support hq'ass)
      (le_of_lt hq'lt))

private lemma localized_no_embedded_of_no_embedded
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hM : embeddedAssociatedPrimes (R := R) (M := M) = ∅) (f : R) :
    embeddedAssociatedPrimes (R := Localization.Away f)
      (M := LocalizedModule.Away f M) = ∅ := by
  let cmod : Module R (LocalizedModule.Away f M) :=
    Module.compHom (LocalizedModule.Away f M)
      (algebraMap R (Localization.Away f))
  have hbridge :
      PrimeSpectrum.comap (algebraMap R (Localization.Away f)) ''
          Formalization.Books.Algebra.Unit63.associatedPrimes
            (Localization.Away f) (LocalizedModule.Away f M) =
        @Formalization.Books.Algebra.Unit63.associatedPrimes R
          (LocalizedModule.Away f M) _ _ cmod := by
    simpa [cmod] using
      (Formalization.Books.Algebra.Unit63.ass_localize_eq_over_localization
        (M := M) (Submonoid.powers f))
  have hasslocal :=
    Formalization.Books.Algebra.Unit63.ass_localize_eq_of_noetherian
      (R := R) (M := M) (Submonoid.powers f)
  have hqinj : Function.Injective
      (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) :=
    (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f).injective
  rw [Set.eq_empty_iff_forall_notMem]
  intro q hq
  change q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes
      (Localization.Away f) (LocalizedModule.Away f M) ∧
      ¬ Minimal
        (fun p : PrimeSpectrum (Localization.Away f) =>
          p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes
            (Localization.Away f) (LocalizedModule.Away f M)) q at hq
  rcases hq with ⟨hqass, hqnotmin⟩
  let p : PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (Localization.Away f)) q
  have hp : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M := by
    have hpRloc : p ∈
        @Formalization.Books.Algebra.Unit63.associatedPrimes R
          (LocalizedModule.Away f M) _ _ cmod := by
      rw [← hbridge]
      exact ⟨q, hqass, rfl⟩
    have hpint : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M ∩
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
      rw [hasslocal]
      simpa [cmod] using hpRloc
    exact hpint.1
  have hpmin : Minimal
      (fun z : PrimeSpectrum R =>
        z ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) p := by
    by_contra hpnotmin
    exact (Set.eq_empty_iff_forall_notMem.mp hM p) ⟨hp, hpnotmin⟩
  apply hqnotmin
  refine ⟨hqass, ?_⟩
  intro q' hq'ass hq'le
  let p' : PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (Localization.Away f)) q'
  have hp' : p' ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M := by
    have hp'Rloc : p' ∈
        @Formalization.Books.Algebra.Unit63.associatedPrimes R
          (LocalizedModule.Away f M) _ _ cmod := by
      rw [← hbridge]
      exact ⟨q', hq'ass, rfl⟩
    have hp'int : p' ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M ∩
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
      rw [hasslocal]
      simpa [cmod] using hp'Rloc
    exact hp'int.1
  have hp'le : p' ≤ p := by
    change p'.asIdeal ≤ p.asIdeal
    exact Ideal.comap_mono hq'le
  have hpp' : p ≤ p' := hpmin.2 hp' hp'le
  have hpeq : p = p' := le_antisymm hpp' hp'le
  have hqeq : q = q' := hqinj (by simpa [p, p'] using hpeq)
  exact hqeq.le

/-- A greatest submodule with nowhere-dense support can be removed without
changing the support, and the resulting quotient has no embedded associated
primes.  The final clause records the localization statement in the source.
The source proof shows that the maximal element is in fact greatest. -/
theorem exists_embeddedPrimeRemoval
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ K : Submodule R M,
      K ∈ embeddedPrimeRemovalSubmodules (R := R) (M := M) ∧
        (∀ K' : Submodule R M,
          K' ∈ embeddedPrimeRemovalSubmodules (R := R) (M := M) → K' ≤ K) ∧
        Module.support R M = Module.support R (M ⧸ K) ∧
        embeddedAssociatedPrimes (R := R) (M := M ⧸ K) = ∅ ∧
        ∀ f : R,
          (∀ p : PrimeSpectrum R,
            p ∈ embeddedAssociatedPrimes (R := R) (M := M) → f ∈ p.asIdeal) →
          Nonempty
            (LocalizedModule.Away f M ≃ₗ[Localization.Away f]
              LocalizedModule.Away f (M ⧸ K)) := by
  let S : Set (Submodule R M) := embeddedPrimeRemovalSubmodules (R := R) (M := M)
  have hS : S.Nonempty := by
    refine ⟨⊥, ?_⟩
    change supportNowhereDenseInSupport (R := R) (M := M) (⊥ : Submodule R M)
    rw [supportNowhereDenseInSupport]
    have hbot : Module.support R (⊥ : Submodule R M) = ∅ := by
      have hsub : Subsingleton (⊥ : Submodule R M) := ⟨fun x y => Subtype.ext (by
        have hx : (x : M) = 0 := (Submodule.mem_bot R).mp x.property
        have hy : (y : M) = 0 := (Submodule.mem_bot R).mp y.property
        exact hx.trans hy.symm)⟩
      exact @Module.support_eq_empty R (⊥ : Submodule R M) _ _ _ hsub
    rw [hbot]
    change IsNowhereDense (∅ : Set (Module.support R M))
    exact isNowhereDense_empty
  obtain ⟨K, hKS, hKmax⟩ :=
    (set_has_maximal_iff_noetherian (R := R) (M := M)).mpr inferInstance S hS
  have hKgreatest : ∀ K' : Submodule R M,
      K' ∈ embeddedPrimeRemovalSubmodules (R := R) (M := M) → K' ≤ K := by
    intro K' hK'
    by_contra hnot
    exact hKmax (K ⊔ K')
      (support_sup_nowhereDense hKS hK')
      (lt_of_le_of_ne le_sup_left (by
        intro heq
        apply hnot
        rw [heq]
        exact le_sup_right))
  have hsupport : Module.support R M = Module.support R (M ⧸ K) :=
    support_eq_support_quotient_of_nowhereDense K hKS
  have hass : embeddedAssociatedPrimes (R := R) (M := M ⧸ K) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro q hq
    change q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R (M ⧸ K) ∧
      ¬ Minimal
        (fun p : PrimeSpectrum R =>
          p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R (M ⧸ K)) q at hq
    rcases hq with ⟨hqass, hqnotmin⟩
    have hqminSupport : ¬ Minimal
        (fun p : PrimeSpectrum R => p ∈ Module.support R M) q := by
      intro hqmin
      have hqM : q ∈ Module.support R M := by
        rw [hsupport]
        exact Formalization.Books.Algebra.Unit63.ass_subset_support hqass
      have hqminQ : Minimal
          (fun p : PrimeSpectrum R => p ∈ Module.support R (M ⧸ K)) q := by
        refine ⟨by simpa [hsupport] using hqM, ?_⟩
        intro p hp hpq
        exact hqmin.2 (by simpa [hsupport] using hp) hpq
      apply hqnotmin
      refine ⟨hqass, ?_⟩
      intro p hp hpq
      exact hqminQ.2 (Formalization.Books.Algebra.Unit63.ass_subset_support hp) hpq
    change ∃ m : M ⧸ K,
      (⊥ : Submodule R (M ⧸ K)).colon ({m} : Set (M ⧸ K)) = q.asIdeal at hqass
    obtain ⟨m, hm⟩ := Submodule.mkQ_surjective K (Classical.choose hqass)
    have hmann : (⊥ : Submodule R (M ⧸ K)).colon
        ({Submodule.mkQ K m} : Set (M ⧸ K)) = q.asIdeal := by
      simpa [hm] using (Classical.choose_spec hqass)
    have hqno : ∀ p : PrimeSpectrum R,
        Minimal (fun z : PrimeSpectrum R => z ∈ Module.support R M) p →
          ¬ q.asIdeal ≤ p.asIdeal := by
      intro p hp hle
      apply hqminSupport
      have hpq : p ≤ q := hp.2
        (by rw [hsupport]
            exact Formalization.Books.Algebra.Unit63.ass_subset_support hqass) hle
      have heq : q = p := PrimeSpectrum.ext (le_antisymm hle hpq)
      simpa [heq] using hp
    have hsup : supportNowhereDenseInSupport (R := R) (M := M)
        (K ⊔ Submodule.span R ({m} : Set M)) :=
      sup_span_mem_removal K hKS m q hmann hqno
    have hle := hKgreatest _ hsup
    have hmL : m ∈ K ⊔ Submodule.span R ({m} : Set M) :=
      (show Submodule.span R ({m} : Set M) ≤
          K ⊔ Submodule.span R ({m} : Set M) from le_sup_right)
        (Submodule.subset_span (Set.mem_singleton m))
    have hmK : m ∈ K := hle hmL
    have htop : q.asIdeal = ⊤ := by
      rw [← hmann]
      simp [(Submodule.Quotient.mk_eq_zero K).mpr hmK]
    exact q.isPrime.ne_top htop
  refine ⟨K, hKS, hKgreatest, hsupport, hass, ?_⟩
  intro f hf
  have hKsupport := support_subset_zeroLocus_of_embedded_contains K hKS f hf
  have hzero : PrimeSpectrum.zeroLocus (Submodule.annihilator K) ⊆
      PrimeSpectrum.zeroLocus ({f} : Set R) := by
    rw [← Module.support_eq_zeroLocus (M := K)]
    exact hKsupport
  have hfroot : f ∈ (Submodule.annihilator K).radical := by
    have hzero' : PrimeSpectrum.zeroLocus (Submodule.annihilator K) ⊆
        PrimeSpectrum.zeroLocus ((Ideal.span ({f} : Set R)) : Set R) := by
      simpa only [PrimeSpectrum.zeroLocus_span] using hzero
    have hspanle : Ideal.span ({f} : Set R) ≤
        (Submodule.annihilator K).radical :=
      (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff
        (Submodule.annihilator K) (Ideal.span ({f} : Set R))).mp hzero'
    exact hspanle (Ideal.subset_span (by simp))
  obtain ⟨n, hn⟩ := hfroot
  have hKlocalized : K.localized (Submonoid.powers f) = ⊥ := by
    rw [Submodule.localized, Submodule.localized'_eq_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨m, hm, rfl⟩
      apply (LocalizedModule.mem_ker_mkLinearMap_iff).2
      refine ⟨f ^ n,
        Submonoid.pow_mem (Submonoid.powers f) (Submonoid.mem_powers f) n, ?_⟩
      exact congrArg Subtype.val (Module.mem_annihilator.mp hn ⟨m, hm⟩)
    · exact bot_le
  let e₀ :
      (LocalizedModule.Away f M ⧸ (⊥ : Submodule (Localization.Away f)
        (LocalizedModule.Away f M))) ≃ₗ[Localization.Away f]
        LocalizedModule.Away f M :=
    (LinearEquiv.ofBijective (⊥ : Submodule (Localization.Away f)
      (LocalizedModule.Away f M)).mkQ
      ⟨(fun x y h => by
        have hzero : (⊥ : Submodule (Localization.Away f)
            (LocalizedModule.Away f M)).mkQ (x - y) = 0 := by
          rw [map_sub, h, sub_self]
        have hxy : x - y ∈
            (⊥ : Submodule (Localization.Away f) (LocalizedModule.Away f M)) :=
          (Submodule.Quotient.mk_eq_zero (⊥ : Submodule (Localization.Away f)
            (LocalizedModule.Away f M))).mp hzero
        exact sub_eq_zero.mp hxy), Submodule.mkQ_surjective _⟩).symm
  refine ⟨((localizedQuotientEquiv (Submonoid.powers f) K).symm ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ hKlocalized) ≪≫ₗ e₀).symm⟩

/-- Localization of a greatest removal submodule is the greatest removal
submodule after localization.  The displayed linear equivalence is the
source's identification of `(M')_f` with `(M_f)'`. -/
theorem embeddedPrimeRemoval_localize
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (K : Submodule R M)
    (hK : K ∈ embeddedPrimeRemovalSubmodules (R := R) (M := M))
    (hKgreatest : ∀ K' : Submodule R M,
      K' ∈ embeddedPrimeRemovalSubmodules (R := R) (M := M) → K' ≤ K)
    (f : R) :
    K.localized (Submonoid.powers f) ∈
        embeddedPrimeRemovalSubmodules
          (R := Localization.Away f) (M := LocalizedModule.Away f M) ∧
      (∀ K' : Submodule (Localization.Away f) (LocalizedModule.Away f M),
        K' ∈ embeddedPrimeRemovalSubmodules
            (R := Localization.Away f) (M := LocalizedModule.Away f M) →
          K' ≤ K.localized (Submonoid.powers f)) ∧
      Nonempty
        (LocalizedModule.Away f (M ⧸ K) ≃ₗ[Localization.Away f]
          (LocalizedModule.Away f M ⧸ K.localized (Submonoid.powers f))) := by
  have hKloc : K.localized (Submonoid.powers f) ∈
      embeddedPrimeRemovalSubmodules
        (R := Localization.Away f) (M := LocalizedModule.Away f M) := by
    exact localized_removal_nowhereDense K hK f
  obtain ⟨K₀, hK₀, hK₀greatest, _, hass₀, _⟩ :=
    exists_embeddedPrimeRemoval (R := R) (M := M)
  have hKeq : K = K₀ := le_antisymm
    (hK₀greatest K hK) (hKgreatest K₀ hK₀)
  have hass : embeddedAssociatedPrimes (R := R) (M := M ⧸ K) = ∅ := by
    rw [hKeq]
    exact hass₀
  have hnoLocal := localized_no_embedded_of_no_embedded hass f
  let Kloc : Submodule (Localization.Away f) (LocalizedModule.Away f M) :=
    K.localized (Submonoid.powers f)
  let e : (LocalizedModule.Away f M ⧸ Kloc) ≃ₗ[Localization.Away f]
      LocalizedModule.Away f (M ⧸ K) :=
    localizedQuotientEquiv (Submonoid.powers f) K
  have hsupport_quot :
      Module.support (Localization.Away f) (LocalizedModule.Away f M) =
        Module.support (Localization.Away f)
          (LocalizedModule.Away f M ⧸ Kloc) := by
    exact support_eq_support_quotient_of_nowhereDense Kloc hKloc
  have hsupport_equiv :
      Module.support (Localization.Away f)
          (LocalizedModule.Away f M ⧸ Kloc) =
        Module.support (Localization.Away f)
          (LocalizedModule.Away f (M ⧸ K)) := by
    apply subset_antisymm
    · exact Module.support_subset_of_injective e.toLinearMap e.injective
    · exact Module.support_subset_of_surjective e.toLinearMap
        e.surjective
  have hsupport :
      Module.support (Localization.Away f) (LocalizedModule.Away f M) =
        Module.support (Localization.Away f) (LocalizedModule.Away f (M ⧸ K)) :=
    hsupport_quot.trans hsupport_equiv
  refine ⟨hKloc, ?_, ⟨e.symm⟩⟩
  intro K' hK'
  let g : LocalizedModule.Away f M →ₗ[Localization.Away f]
      LocalizedModule.Away f (M ⧸ K) :=
    e.toLinearMap.comp Kloc.mkQ
  let L : Submodule (Localization.Away f)
      (LocalizedModule.Away f (M ⧸ K)) := K'.map g
  have hgmem : ∀ x : K', g x ∈ L := by
    intro x
    exact Submodule.mem_map.mpr ⟨x, x.property, rfl⟩
  let gK : K' →ₗ[Localization.Away f] L :=
    (g.comp K'.subtype).codRestrict L hgmem
  have hgKsurj : Function.Surjective gK := by
    intro y
    rcases y.property with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxy
  have hLnd : supportNowhereDenseInSupport
      (R := Localization.Away f)
      (M := LocalizedModule.Away f (M ⧸ K)) L := by
    apply support_nowhereDense_of_no_minimal_support
    intro q hqmin hqL
    have hqK' : q ∈ Module.support (Localization.Away f) K' :=
      Module.support_subset_of_surjective gK hgKsurj hqL
    have hqLM : q ∈ Module.support (Localization.Away f)
        (LocalizedModule.Away f M) := by
      rw [hsupport]
      exact Module.support_subset_of_injective L.subtype
        (Submodule.injective_subtype L) hqL
    have hqminLM : Minimal
        (fun z : PrimeSpectrum (Localization.Away f) =>
          z ∈ Module.support (Localization.Away f)
            (LocalizedModule.Away f M)) q := by
      refine ⟨hqLM, ?_⟩
      intro z hz hzq
      apply hqmin.2
      rw [← hsupport]
      exact hz
      exact hzq
    exact minimal_support_not_mem_support K' hK' q hqminLM hqK'
  have hLsub : Subsingleton (↥L) := by
    apply (Formalization.Books.Algebra.Unit63.ass_eq_empty_iff_subsingleton
      (R := Localization.Away f) (M := ↥L)).mpr
    rw [Set.eq_empty_iff_forall_notMem]
    intro q hqass
    have hqassQ := associated_subset_of_injective L.subtype
      (Submodule.injective_subtype L) hqass
    have hqminAssoc : Minimal
        (fun z : PrimeSpectrum (Localization.Away f) =>
          z ∈ Formalization.Books.Algebra.Unit63.associatedPrimes
            (Localization.Away f) (LocalizedModule.Away f (M ⧸ K))) q := by
      by_contra hqnot
      exact (Set.eq_empty_iff_forall_notMem.mp hnoLocal q)
        ⟨hqassQ, hqnot⟩
    have hqminQ : Minimal
        (fun z : PrimeSpectrum (Localization.Away f) =>
          z ∈ Module.support (Localization.Away f)
            (LocalizedModule.Away f (M ⧸ K))) q := by
      refine ⟨Formalization.Books.Algebra.Unit63.ass_subset_support hqassQ, ?_⟩
      intro z hz hzq
      obtain ⟨r, hrmin, hrz⟩ := exists_minimal_support_le z hz
      have hrass := Formalization.Books.Algebra.Unit63.ass_of_minimal_support
        r hrmin.prop hrmin
      exact (hqminAssoc.2 hrass (hrz.trans hzq)).trans hrz
    exact minimal_support_not_mem_support L hLnd q hqminQ
      (Formalization.Books.Algebra.Unit63.ass_subset_support hqass)
  intro x hx
  have hxzero : gK ⟨x, hx⟩ = 0 := Subsingleton.elim _ _
  have hxq : Kloc.mkQ x = 0 := by
    have hgx : g x = 0 := by
      have hval := congrArg Subtype.val hxzero
      change g x = 0 at hval
      exact hval
    have heq : e.toLinearMap (Kloc.mkQ x) = 0 := by
      simpa [g] using hgx
    exact e.injective (by simpa using heq)
  exact (Submodule.Quotient.mk_eq_zero Kloc).mp hxq

/-! ## Endomorphisms and the annihilator quotient -/

/-- If a finite module over a Noetherian ring has no embedded associated
primes, its annihilator quotient ring has no embedded primes.  The ideal
`Module.annihilator R M` is the canonical form of the source's
`{x | xM = 0}`. -/
theorem quotient_by_annihilator_no_embedded_primes
    {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hM : embeddedAssociatedPrimes (R := R) (M := M) = ∅) :
    embeddedPrimes (R ⧸ Module.annihilator R M) = ∅ := by
  let I : Ideal R := Module.annihilator R M
  rw [Set.eq_empty_iff_forall_notMem]
  intro q hq
  change q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes
      (R ⧸ I) (R ⧸ I) ∧
      ¬ Minimal
        (fun p : PrimeSpectrum (R ⧸ I) =>
          p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes
            (R ⧸ I) (R ⧸ I)) q at hq
  rcases hq with ⟨hqass, hqnotmin⟩
  have hq0fail : ¬ ∀ p : PrimeSpectrum (R ⧸ I),
      p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes
        (R ⧸ I) (R ⧸ I) → p ≤ q → q ≤ p := by
    intro hq0
    apply hqnotmin
    exact ⟨hqass, hq0⟩
  push Not at hq0fail
  obtain ⟨q₀, hq₀ass, hq₀le, hq₀notle⟩ := hq0fail
  have hq₀lt : q₀ < q := lt_of_le_of_ne hq₀le (by
    intro heq
    exact hq₀notle heq.symm.le)
  change ∃ x : R ⧸ I,
      (⊥ : Submodule (R ⧸ I) (R ⧸ I)).colon ({x} : Set (R ⧸ I)) = q.asIdeal at hqass
  obtain ⟨x, hx⟩ := hqass
  have hxne : x ≠ 0 := by
    intro hx0
    apply q.isPrime.ne_top
    rw [← hx, hx0]
    ext a
    simp [Submodule.mem_colon_singleton]
  obtain ⟨r, hrx⟩ := Ideal.Quotient.mk_surjective x
  have hrnot : r ∉ I := by
    intro hr
    apply hxne
    rw [← hrx]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  have hrnotann : r ∉ Module.annihilator R M := by
    simpa [I] using hrnot
  have hrnonzero : ∃ m : M, r • m ≠ 0 := by
    rw [Module.mem_annihilator] at hrnotann
    simpa only [not_forall] using hrnotann
  obtain ⟨m, hm⟩ := hrnonzero
  let N : Submodule R M := LinearMap.range (LinearMap.lsmul R M r)
  have hNnontriv : ¬ Subsingleton N := by
    intro hsub
    apply hm
    have hy : (⟨r • m, ⟨m, rfl⟩⟩ : N) = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val hy
  have hassN : (Formalization.Books.Algebra.Unit63.associatedPrimes
      R N).Nonempty := by
    by_contra hnonempty
    have hsub : Subsingleton N :=
      (Formalization.Books.Algebra.Unit63.ass_eq_empty_iff_subsingleton
        (R := R) (M := N)).mpr
        (Set.eq_empty_iff_forall_notMem.mpr (by
          intro p hp
          exact hnonempty ⟨p, hp⟩))
    exact hNnontriv hsub
  obtain ⟨q₁, hq₁ass⟩ := hassN
  let p : PrimeSpectrum R := PrimeSpectrum.comap (Ideal.Quotient.mk I) q
  have hpannN : p.asIdeal ≤ Module.annihilator R N := by
    intro a ha
    apply Module.mem_annihilator.mpr
    intro y
    apply Subtype.ext
    rcases y.property with ⟨z, hy⟩
    change a • (y : M) = 0
    rw [← hy]
    change a • (r • z) = 0
    change Ideal.Quotient.mk I a ∈ q.asIdeal at ha
    have ha' : Ideal.Quotient.mk I a ∈
        (⊥ : Submodule (R ⧸ I) (R ⧸ I)).colon ({x} : Set (R ⧸ I)) := by
      rw [hx]
      exact ha
    rw [Submodule.mem_colon_singleton] at ha'
    have har : a * r ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← hrx] at ha'
      simpa using ha'
    have harann : a * r ∈ Module.annihilator R M := by
      simpa [I] using har
    rw [← mul_smul]
    exact Module.mem_annihilator.mp harann z
  have hpq₁ : p ≤ q₁ := by
    change p.asIdeal ≤ q₁.asIdeal
    exact hpannN.trans
      (Module.mem_support_iff_of_finite.mp
        (Formalization.Books.Algebra.Unit63.ass_subset_support hq₁ass))
  have hq₁assM : q₁ ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M :=
    (Formalization.Books.Algebra.Unit63.ass_subset_ass_of_short_exact
      N.subtype (Submodule.mkQ N) (Submodule.injective_subtype N)
      (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)).1 hq₁ass
  have hq₀support :
      PrimeSpectrum.comap (Ideal.Quotient.mk I) q₀ ∈ Module.support R M := by
    rw [Module.support_eq_zeroLocus]
    intro a ha
    change Ideal.Quotient.mk I a ∈ q₀.asIdeal
    have haI : a ∈ I := by simpa [I] using ha
    have hzero : Ideal.Quotient.mk I a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr haI
    rw [hzero]
    exact q₀.asIdeal.zero_mem
  obtain ⟨r₀, hr₀min, hr₀q₀⟩ :=
    exists_minimal_support_le (R := R) (M := M)
      (PrimeSpectrum.comap (Ideal.Quotient.mk I) q₀) hq₀support
  have hr₀ass : r₀ ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M :=
    Formalization.Books.Algebra.Unit63.ass_of_minimal_support r₀
      hr₀min.prop hr₀min
  have hcomap_inj : Function.Injective (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective
      (R ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).injective
  have hp₀ltp :
      PrimeSpectrum.comap (Ideal.Quotient.mk I) q₀ < p := by
    apply lt_of_le_of_ne
    · exact Ideal.comap_mono hq₀le
    · intro heq
      apply hq₀lt.ne
      apply hcomap_inj
      simpa [p] using heq
  have hr₀ltq₁ : r₀ < q₁ :=
    lt_of_lt_of_le (lt_of_le_of_lt hr₀q₀ hp₀ltp) hpq₁
  have hq₁notmin : ¬ Minimal
      (fun z : PrimeSpectrum R =>
        z ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) q₁ := by
    intro hq₁min
    exact (not_le_of_gt hr₀ltq₁)
      (hq₁min.2 hr₀ass hr₀ltq₁.le)
  exact (Set.eq_empty_iff_forall_notMem.mp hM q₁) ⟨hq₁assM, hq₁notmin⟩

end

end Formalization.Books.Algebra.Unit67
