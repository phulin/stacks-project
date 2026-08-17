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
  sorry

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
  sorry

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
  sorry

end

end Formalization.Books.Algebra.Unit67
