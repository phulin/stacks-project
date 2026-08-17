import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Commutative Algebra, Chapter 74: An application of Ext groups

The source's quotients `N / I^n N` and `M / I^n M` are represented by
submodule quotients.  Their induced map is Mathlib's canonical `Submodule.mapQ`,
and split injections are expressed by the categorical `IsSplitMono` predicate
in the module category.
-/

namespace Formalization.Books.Algebra.Unit74

open CategoryTheory

universe u

/-! ## Quotient maps modulo powers of an ideal -/

/-- The map induced by a module homomorphism on quotients modulo `I ^ n`. -/
def adicQuotientMap {R N M : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    (I : Ideal R) (φ : N →ₗ[R] M) (n : ℕ) :
    N ⧸ (I ^ n • (⊤ : Submodule R N)) →ₗ[R]
      M ⧸ (I ^ n • (⊤ : Submodule R M)) :=
  (I ^ n • (⊤ : Submodule R N)).mapQ
    (I ^ n • (⊤ : Submodule R M)) φ
    (Submodule.smul_top_le_comap_smul_top (I ^ n) φ)

/-! ## The application -/

/-- A module map that splits modulo arbitrarily large powers of a Jacobson-radical
ideal already splits. -/
theorem split_injection_after_completion
    {R N M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (φ : N →ₗ[R] M)
    (hφ : ∀ N₀ : ℕ, ∃ n ≥ N₀,
      IsSplitMono (ModuleCat.ofHom (adicQuotientMap I φ n))) :
    IsSplitMono (ModuleCat.ofHom φ) := by
  sorry

end Formalization.Books.Algebra.Unit74
