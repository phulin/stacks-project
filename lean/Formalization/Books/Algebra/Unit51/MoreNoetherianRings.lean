import Formalization.Books.Algebra.Unit31.NoetherianRings
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Commutative Algebra, Chapter 51: More Noetherian rings

The source's module, ideal, and subalgebra intersections use Mathlib's
canonical submodule, ideal, localization, and finite-type interfaces.  The
Artin--Rees, Krull intersection, and Artin--Tate statements are recorded in
the form used by the corresponding Mathlib APIs.
-/

namespace Formalization.Books.Algebra.Unit51

open Set
open scoped Pointwise

universe u v w

noncomputable section

/-! ## Noetherian modules and Artin--Rees -/

/-- The three assertions in the source's basic Noetherian lemma. -/
theorem noetherian_basic
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R]
    [Module.Finite R M] :
    Module.FinitePresentation R M ∧
      (∀ N : Submodule R M, Module.Finite R N) ∧
        (∀ f : ℕ →o Submodule R M,
          ∃ n, ∀ m, n ≤ m → f n = f m) := by
  refine ⟨Module.finitePresentation_of_finite R M, ?_,
    monotone_stabilizes_iff_noetherian.mpr inferInstance⟩
  intro N
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)

/-- Artin--Rees for a submodule of a finite module, with `I ^ n M` written as
`I ^ n • ⊤`.  The finite hypothesis on `N` is explicit because it is part of
the source statement, although Noetherianity makes it redundant here. -/
theorem artin_rees
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R]
    [Module.Finite R M]
    (I : Ideal R) (N : Submodule R M) [Module.Finite R N] :
    ∃ c : ℕ, 0 < c ∧ ∀ n ≥ c,
      I ^ n • (⊤ : Submodule R M) ⊓ N =
        I ^ (n - c) • (I ^ c • (⊤ : Submodule R M) ⊓ N) := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul N
  refine ⟨k + 1, Nat.zero_lt_succ k, ?_⟩
  intro n hn
  rw [hk n (le_trans (Nat.le_succ k) hn), hk (k + 1) (Nat.le_succ k)]
  simp only [Nat.add_sub_cancel_left]
  rw [smul_smul, ← pow_add]
  congr 2
  omega

/-- Artin--Rees for an exact sequence `0 → K → M → N`, expressed using the
range of the left map and the canonical `map`/`comap` operations. -/
theorem map_artin_rees
    {R : Type u} {K : Type v} {M : Type w} {N : Type*}
    [CommRing R]
    [AddCommGroup K] [Module R K]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [IsNoetherianRing R]
    [Module.Finite R K] [Module.Finite R M] [Module.Finite R N]
    (I : Ideal R) (g : K →ₗ[R] M) (f : M →ₗ[R] N)
    (_hg : Function.Injective g) (hgf : Function.Exact g f) :
    ∃ c : ℕ, ∀ n ≥ c,
      Submodule.comap f (I ^ n • (⊤ : Submodule R N)) =
          LinearMap.range g ⊔
            I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)) ∧
        LinearMap.range f ⊓ (I ^ n • (⊤ : Submodule R N)) ≤
          Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M)) := by
  obtain ⟨c, hc_pos, hc⟩ := artin_rees I (LinearMap.range f)
  refine ⟨c, ?_⟩
  intro n hn
  have hmap :
      I ^ (n - c) • (I ^ c • (⊤ : Submodule R N) ⊓ LinearMap.range f) ≤
        Submodule.map f
          (I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N))) := by
    refine Submodule.smul_le.mpr ?_
    intro r hr x hx
    rcases hx.2 with ⟨y, hy⟩
    refine ⟨r • y, Submodule.smul_mem_smul hr ?_, ?_⟩
    · change f y ∈ I ^ c • (⊤ : Submodule R N)
      rw [hy]
      exact hx.1
    change f (r • y) = r • x
    rw [map_smul, hy]
  have hpow :
      I ^ (n - c) • (I ^ c • (⊤ : Submodule R N)) ≤
        I ^ n • (⊤ : Submodule R N) := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hn]
  constructor
  · apply le_antisymm
    · intro x hx
      have hfx : f x ∈ I ^ n • (⊤ : Submodule R N) := hx
      have hfx' : f x ∈ I ^ n • (⊤ : Submodule R N) ⊓ LinearMap.range f :=
        ⟨hfx, ⟨x, rfl⟩⟩
      rw [hc n hn] at hfx'
      rcases hmap hfx' with ⟨y, hy, hfy⟩
      have hker : x - y ∈ LinearMap.ker f := by
        change f (x - y) = 0
        rw [map_sub, hfy, sub_self]
      rw [hgf.linearMap_ker_eq] at hker
      rcases hker with ⟨z, hz⟩
      have hxy : x = g z + y := by
        rw [hz, sub_add_cancel]
      rw [hxy]
      exact add_mem
        ((le_sup_left : LinearMap.range g ≤
          LinearMap.range g ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)))
          ⟨z, rfl⟩)
        ((le_sup_right : I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)) ≤
          LinearMap.range g ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N))) hy)
    · refine sup_le
        (by
          intro x hx
          change f x ∈ I ^ n • (⊤ : Submodule R N)
          rcases hx with ⟨z, rfl⟩
          have hfg : f (g z) = 0 :=
            DFunLike.congr_fun hgf.linearMap_comp_eq_zero z
          rw [hfg]
          exact zero_mem _)
        (by
          refine Submodule.smul_le.mpr ?_
          intro r hr x hx
          change f (r • x) ∈ I ^ n • (⊤ : Submodule R N)
          rw [map_smul]
          change f x ∈ I ^ c • (⊤ : Submodule R N) at hx
          exact hpow (Submodule.smul_mem_smul hr hx))
  · intro x hx
    have hx' : x ∈ I ^ n • (⊤ : Submodule R N) ⊓ LinearMap.range f :=
      ⟨hx.2, hx.1⟩
    rw [hc n hn] at hx'
    exact (Submodule.map_mono
      (Submodule.smul_mono le_rfl le_top)) (hmap hx')

/-! ## Krull intersection and localization -/

/-- The intersection of all powers of an ideal acting on a module. -/
def powersIntersectionSubmodule
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) : Submodule R M :=
  ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)

/-- Krull's intersection theorem for a finite module over a Noetherian local
ring. -/
theorem krull_intersection
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (I : Ideal R) (hI : I ≠ ⊤) :
    powersIntersectionSubmodule (M := M) I = ⊥ := by
  exact Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hI

/-- If `I` is contained in the Jacobson radical, its power intersection on a
finite module is zero. -/
theorem powersIntersectionSubmodule_eq_bot_of_le_jacobson
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) :
    powersIntersectionSubmodule (M := M) I = ⊥ := by
  change (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)) = ⊥
  apply Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
  simpa only [Ideal.jacobson_bot] using hI

/-- For every prime containing `I`, some localization of the power
intersection vanishes. -/
theorem powersIntersectionSubmodule_localizes_to_bot
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    ∃ f : R, f ∉ p ∧
      (powersIntersectionSubmodule (M := M) I).localized (Submonoid.powers f) = ⊥ := by
  classical
  let N₀ : Submodule R M := powersIntersectionSubmodule (M := M) I
  let S := Localization.AtPrime p
  let q := p.primeCompl
  let J : Ideal S := I.map (algebraMap R S)
  let _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have hJ : J ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := IsLocalRing.maximalIdeal S)
    · exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    · simpa [J, S, Localization.AtPrime.map_eq_maximalIdeal] using
        (Ideal.map_mono hIp :
          I.map (algebraMap R S) ≤ p.map (algebraMap R S))
  have hkrull :
      (⨅ n : ℕ, J ^ n • (⊤ : Submodule S (LocalizedModule q M))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing J hJ
  have hfull (m : M) (hm : m ∈ N₀) :
      (LocalizedModule.mkLinearMap q M) m = 0 := by
    have hm_n : ∀ n : ℕ, m ∈ I ^ n • (⊤ : Submodule R M) := by
      intro n
      change m ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)) at hm
      rw [Submodule.mem_iInf] at hm
      exact hm n
    have hloc (n : ℕ) :
        (LocalizedModule.mkLinearMap q M) m ∈
          J ^ n • (⊤ : Submodule S (LocalizedModule q M)) := by
      have hloc' :
          (LocalizedModule.mkLinearMap q M) m ∈
            (I ^ n • (⊤ : Submodule R M)).localized' S q
              (LocalizedModule.mkLinearMap q M) := by
        rw [Submodule.mem_localized']
        exact ⟨m, hm_n n, 1, by simp⟩
      simpa only [J, Submodule.localized'_smul, Ideal.localized'_eq_map,
        Submodule.localized'_top, Ideal.map_pow] using hloc'
    have hm_int :
        (LocalizedModule.mkLinearMap q M) m ∈
          (⨅ n : ℕ, J ^ n • (⊤ : Submodule S (LocalizedModule q M))) := by
      rw [Submodule.mem_iInf]
      exact hloc
    rw [hkrull] at hm_int
    simpa using hm_int
  let f₀ : N₀ →ₗ[R] N₀.localized q := N₀.toLocalized q
  have hcomp : f₀.comp (LinearMap.id : N₀ →ₗ[R] N₀) =
      f₀.comp (0 : N₀ →ₗ[R] N₀) := by
    ext x
    have hx0 : f₀ x = 0 := by
      apply Subtype.ext
      dsimp [f₀, Submodule.toLocalized, Submodule.toLocalized',
        Submodule.toLocalized₀]
      exact hfull (x : M) x.property
    simpa [LinearMap.coe_comp, Function.comp_apply] using hx0
  obtain ⟨s, hs⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
      q f₀ (LinearMap.id : N₀ →ₗ[R] N₀) (0 : N₀ →ₗ[R] N₀) hcomp
  refine ⟨s, s.property, ?_⟩
  apply le_antisymm
  · intro x hx
    change x = 0
    rw [Submodule.mem_localized'] at hx
    rcases hx with ⟨m, hm, t, rfl⟩
    rw [IsLocalizedModule.mk'_eq_zero]
    apply (IsLocalizedModule.eq_zero_iff (Submonoid.powers (s : R))
      (LocalizedModule.mkLinearMap (Submonoid.powers (s : R)) M)).2
    refine ⟨⟨s, Submonoid.mem_powers _⟩, ?_⟩
    have hm0 := DFunLike.congr_fun hs (⟨m, hm⟩ : N₀)
    change (s : R) • m = 0
    simpa only [Submonoid.smul_def, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.zero_apply, Submodule.coe_smul, Submodule.coe_zero, smul_zero] using
      congrArg Subtype.val hm0
  · exact bot_le

/-! ## The ideal-intersection remark -/

/-- The intersection of all powers of an ideal in the regular module. -/
def powersIntersectionIdeal
    {R : Type u} [CommRing R] (I : Ideal R) : Ideal R :=
  ⨅ n : ℕ, I ^ n

/-- In a Noetherian local ring, the powers of a proper ideal have zero
intersection. -/
theorem powersIntersectionIdeal_eq_bot_of_isLocalRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) :
    powersIntersectionIdeal I = ⊥ := by
  exact Ideal.iInf_pow_eq_bot_of_isLocalRing I hI

/-- An element in the intersection of the powers of `I` vanishes after some
localization away from every prime containing `I`. -/
theorem powersIntersectionIdeal_mem_localizes_to_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {x : R} (hx : x ∈ powersIntersectionIdeal I)
    (p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    ∃ g : R, g ∉ p ∧ algebraMap R (Localization.Away g) x = 0 := by
  have hx' : x ∈ powersIntersectionSubmodule (M := R) I := by
    change x ∈ ⨅ n : ℕ, I ^ n • (⊤ : Submodule R R)
    rw [Submodule.mem_iInf]
    intro n
    simpa only [smul_eq_mul, Ideal.mul_top] using (Ideal.mem_iInf.mp hx n)
  obtain ⟨g, hg, hlocal⟩ :=
    powersIntersectionSubmodule_localizes_to_bot (M := R) I p hIp
  refine ⟨g, hg, ?_⟩
  have hxloc :
      (LocalizedModule.mkLinearMap (Submonoid.powers g) R) x ∈
        Submodule.localized (Submonoid.powers g)
          (powersIntersectionSubmodule (M := R) I) := by
    rw [Submodule.mem_localized']
    exact ⟨x, hx', 1, by simp⟩
  have hzero : (LocalizedModule.mkLinearMap (Submonoid.powers g) R) x = 0 := by
    rw [hlocal] at hxloc
    simpa using hxloc
  have hxann : ∃ s : Submonoid.powers g, (s : R) * x = 0 := by
    simpa only [Submonoid.smul_def, smul_eq_mul] using
      (IsLocalizedModule.eq_zero_iff (Submonoid.powers g)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) R)).mp hzero
  exact (IsLocalization.map_eq_zero_iff (Submonoid.powers g)
    (Localization.Away g) x).2 hxann

/-! ## Artin--Tate -/

/-- Artin--Tate: an `R`-subalgebra of a finite-type `R`-algebra over which the
ambient algebra is finite is itself of finite type over `R`. -/
theorem artin_tate
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S]
    (T : Subalgebra R S) [Module.Finite T S] :
    Algebra.FiniteType R T := by
  rw [← Subalgebra.fg_iff_finiteType, ← T.fg_top]
  exact fg_of_fg_of_fg R T S (inferInstance : Algebra.FiniteType R S).out
    (inferInstance : Module.Finite T S).fg_top Subtype.val_injective

end

end Formalization.Books.Algebra.Unit51
