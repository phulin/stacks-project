import Formalization.Books.Algebra.Unit31.NoetherianRings
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.Away.Basic

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
  sorry

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
    (hg : Function.Injective g) (hgf : Function.Exact g f) :
    ∃ c : ℕ, ∀ n ≥ c,
      Submodule.comap f (I ^ n • (⊤ : Submodule R N)) =
          LinearMap.range g ⊔
            I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)) ∧
        LinearMap.range f ⊓ (I ^ n • (⊤ : Submodule R N)) ≤
          Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M)) := by
  sorry

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
  sorry

/-- For every prime containing `I`, some localization of the power
intersection vanishes. -/
theorem powersIntersectionSubmodule_localizes_to_bot
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    ∃ f : R, f ∉ p ∧
      (powersIntersectionSubmodule (M := M) I).localized (Submonoid.powers f) = ⊥ := by
  sorry

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
  sorry

/-! ## Artin--Tate -/

/-- Artin--Tate: an `R`-subalgebra of a finite-type `R`-algebra over which the
ambient algebra is finite is itself of finite type over `R`. -/
theorem artin_tate
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S]
    (T : Subalgebra R S) [Module.Finite T S] :
    Algebra.FiniteType R T := by
  sorry

end

end Formalization.Books.Algebra.Unit51
