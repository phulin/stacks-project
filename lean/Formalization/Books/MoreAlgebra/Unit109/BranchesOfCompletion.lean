import Formalization.Books.MoreAlgebra.Unit108.MiscellaneousOnBranches
import Formalization.Books.MoreAlgebra.Unit43.PermanenceCompletion
import Formalization.Books.MoreAlgebra.Unit45.PermanenceHenselization
import Formalization.Books.MoreAlgebra.Unit51
import Formalization.Books.MoreAlgebra.Unit52
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.Connected.Basic

/-!
# More on Algebra, Chapter 109: Branches of the completion

The source compares the branches of a Noetherian local ring with those of its
completion. Henselizations are represented by source-facing data and
completions by `ringCompletion`.
-/

namespace Formalization.Books.MoreAlgebra.Unit109

open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit155
open Formalization.Books.Algebra.Unit162
open Formalization.Books.MoreAlgebra.Unit107
open Formalization.Books.MoreAlgebra.Unit45
open Formalization.Books.MoreAlgebra.Unit51
open Formalization.Books.MoreAlgebra.Unit52

noncomputable section

universe u

/-! ## The completion map from a chosen henselization -/

/- The earlier henselization interface does not choose the map from a
  henselization to the completion. This structure records that map and its
  compatibility with the map from the original ring. -/
structure HenselizationCompletionMap
    (A : Type u) [CommRing A] [IsLocalRing A]
    (D : HenselizationData A) [IsNoetherianRing A] where
  toRingHom : D.carrier →+*
    ringCompletion (IsLocalRing.maximalIdeal A)
  commutes :
    toRingHom.comp D.map =
      algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A))

/-- The canonical map from the henselization to the completion exists. -/
theorem exists_henselizationCompletionMap
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D : HenselizationData A) :
    Nonempty (HenselizationCompletionMap A D) := by
  sorry

/-! ## Minimal primes and branch counts -/

/-- Minimal primes of the completion map onto minimal primes of the
henselization. -/
theorem minimalPrimes_completion_comap_surjective
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D : HenselizationData A) :
    ∃ M : HenselizationCompletionMap A D,
      ∃ f : MinimalPrimeSpectrum
          (ringCompletion (IsLocalRing.maximalIdeal A)) →
          MinimalPrimeSpectrum D.carrier,
        (∀ q, (f q).1 =
          PrimeSpectrum.comap M.toRingHom q.1) ∧
          Function.Surjective f := by
  sorry

/-- The map on minimal primes need not be bijective in general. -/
theorem minimalPrimes_completion_comap_not_always_bijective :
    ¬ (∀ (A : Type u) [CommRing A] [IsLocalRing A]
        [IsNoetherianRing A] (D : HenselizationData A),
      ∃ M : HenselizationCompletionMap A D,
        ∃ f : MinimalPrimeSpectrum
            (ringCompletion (IsLocalRing.maximalIdeal A)) →
            MinimalPrimeSpectrum D.carrier,
          (∀ q, (f q).1 =
            PrimeSpectrum.comap M.toRingHom q.1) ∧
            Function.Bijective f) := by
  sorry

/-- The branch count of the original ring is at most the completion count. -/
theorem numberOfBranches_le_completion_minimalPrimeCount
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D : HenselizationData A) :
    numberOfBranches A D ≤
      ENat.card (MinimalPrimeSpectrum
        (ringCompletion (IsLocalRing.maximalIdeal A))) := by
  sorry

/-- The corresponding inequality for geometric branches. -/
theorem numberOfGeometricBranches_le_completion
    {A K : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K)
    {K' : Type u} [Field K']
    [Algebra
      (IsLocalRing.ResidueField
        (ringCompletion (IsLocalRing.maximalIdeal A))) K']
    (D' : StrictHenselizationData
      (ringCompletion (IsLocalRing.maximalIdeal A)) K') :
    numberOfGeometricBranches A D ≤
      ENat.card (MinimalPrimeSpectrum D'.strictHenselization) := by
  sorry

/-! ## Equality of branch counts -/

/-- Equality of the branch count is equivalent to primality of the radicals
of all minimal primes extended to the completion. -/
theorem numberOfBranches_eq_completion_minimalPrimeCount_iff
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D : HenselizationData A)
    (M : HenselizationCompletionMap A D) :
    numberOfBranches A D =
        ENat.card (MinimalPrimeSpectrum
          (ringCompletion (IsLocalRing.maximalIdeal A))) ↔
      ∀ q : MinimalPrimeSpectrum D.carrier,
        (Ideal.radical
          (Ideal.map M.toRingHom q.1.asIdeal)).IsPrime := by
  sorry

/-! ## Glueing over a finitely generated ideal -/

/-- The localization map induced by a ring homomorphism. -/
noncomputable def awayMap
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) :
    Localization.Away a →+* Localization.Away (f a) :=
  IsLocalization.Away.map (Localization.Away a)
    (Localization.Away (f a)) f a

/-- A complementary quotient whose product with `C` agrees with `A` on the
open subsets determined by a finitely generated ideal. -/
structure GlueingComplement
    {A C : Type u} [CommRing A] [CommRing C]
    (I : Ideal A) (f : A →+* C) where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  map : A →+* carrier
  surjective : Function.Surjective map
  localized_bijective :
    ∀ a : A, a ∈ I →
      Function.Bijective
        (awayMap (f.prod map) a)

/-- The hypothesis that a localized map is localization at an idempotent of
the source localization. -/
def IsLocalizationAtIdempotent
    {A C : Type u} [CommRing A] [CommRing C]
    (f : A →+* C) (a : A) : Prop :=
  ∃ e : Localization.Away a, IsIdempotentElem e ∧
    letI : Algebra (Localization.Away a) (Localization.Away (f a)) :=
      (awayMap f a).toAlgebra
    IsLocalization (Submonoid.powers e) (Localization.Away (f a))

/-- The source's simple glueing lemma. -/
theorem exists_glueingComplement
    {A C : Type u} [CommRing A] [CommRing C]
    (I : Ideal A) (hI : I.FG) (f : A →+* C)
    (hlocal : ∀ a : A, a ∈ I → IsLocalizationAtIdempotent f a) :
    Nonempty (GlueingComplement I f) := by
  sorry

/-! ## Quotients of completions by idempotent components -/

/-- The ideal-theoretic form of “`J / J²` is annihilated by `K`”. -/
def Ideal.QuotientAnnihilated
    {R : Type u} [CommRing R] (K J : Ideal R) : Prop :=
  K * J ≤ J ^ 2

/-- A quotient of a completed finite type algebra whose conormal ideal is
killed by a power of the base ideal is again a completed finite type algebra.
-/
theorem quotient_completion_by_idempotent_component
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [IsNoetherianRing A] [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A)
    (q : ringCompletion (I.map (algebraMap A B)) →+* C)
    (hq : Function.Surjective q)
    (c : ℕ)
    (hann : Ideal.QuotientAnnihilated
      (Ideal.map
        (algebraMap B (ringCompletion (I.map (algebraMap A B))))
        ((I.map (algebraMap A B)) ^ c))
      (Ideal.comap q (⊥ : Ideal C))) :
    ∃ D : Type u, ∃ _ : CommRing D, ∃ _ : Algebra A D,
      ∃ _ : Algebra.FiniteType A D,
        Nonempty
          (ringCompletion (I.map (algebraMap A D)) ≃+* C) := by
  sorry

/-! ## One-dimensional formal branches -/

/-- Every one-dimensional minimal component of the completion is the radical
of the extension of a minimal component of the henselization. -/
theorem exists_minimalPrime_henselization_of_one_dimensional_completion_prime
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D : HenselizationData A)
    (M : HenselizationCompletionMap A D)
    (q : MinimalPrimeSpectrum
      (ringCompletion (IsLocalRing.maximalIdeal A)))
    (hq : ringKrullDim
      ((ringCompletion (IsLocalRing.maximalIdeal A)) ⧸ q.1.asIdeal) = 1) :
    ∃ qh : MinimalPrimeSpectrum D.carrier,
      q.1.asIdeal =
        Ideal.radical (Ideal.map M.toRingHom qh.1.asIdeal) := by
  sorry

/-! ## The punctured spectrum -/

/-- The closed point of a local ring's affine spectrum. -/
def closedPoint
    (R : Type u) [CommRing R] [IsLocalRing R] : PrimeSpectrum R :=
  ⟨IsLocalRing.maximalIdeal R, inferInstance⟩

/-- The spectrum with its closed point removed. -/
def puncturedSpectrum
    (R : Type u) [CommRing R] [IsLocalRing R] : Set (PrimeSpectrum R) :=
  Set.univ \ {closedPoint R}

/-- Disconnectedness of the punctured spectrum. -/
def PuncturedSpectrumDisconnected
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ¬ IsConnected (puncturedSpectrum R)

/-- The punctured spectrum is disconnected for the completion exactly when
it is disconnected for the henselization. -/
theorem puncturedSpectrum_completion_disconnected_iff
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D : HenselizationData A) :
    PuncturedSpectrumDisconnected
        (ringCompletion (IsLocalRing.maximalIdeal A)) ↔
      PuncturedSpectrumDisconnected D.carrier := by
  sorry

/-! ## One-dimensional and geometrically normal cases -/

/-- In dimension one, ordinary branch counts agree with the completion. -/
theorem numberOfBranches_eq_completion_of_dimension_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D : HenselizationData A)
    (hA : ringKrullDim A = 1) :
    numberOfBranches A D =
      ENat.card (MinimalPrimeSpectrum
        (ringCompletion (IsLocalRing.maximalIdeal A))) := by
  sorry

/-- In dimension one, geometric branch counts agree with the completion. -/
theorem numberOfGeometricBranches_eq_completion_of_dimension_one
    {A K : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    (D : StrictHenselizationData A K)
    (hA : ringKrullDim A = 1)
    {K' : Type u} [Field K']
    [Algebra
      (IsLocalRing.ResidueField
        (ringCompletion (IsLocalRing.maximalIdeal A))) K']
    (D' : StrictHenselizationData
      (ringCompletion (IsLocalRing.maximalIdeal A)) K') :
    numberOfGeometricBranches A D =
      numberOfGeometricBranches
        (ringCompletion (IsLocalRing.maximalIdeal A)) D' := by
  sorry

/-- Excellent and quasi-excellent local rings have geometrically normal
formal fibres, the example mentioned in the source. -/
theorem geometricallyNormalFormalFibres_of_isExcellent_or_isQuasiExcellent
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsExcellent A ∨ IsQuasiExcellent A) :
    HasFormalFibresProperty GeometricallyNormalProperty A := by
  sorry

/-- Geometrically normal formal fibres force the branch counts of a
Noetherian local ring and its completion to agree, and imply that the ring is
Nagata. -/
theorem branches_completion_of_geometricallyNormalFormalFibres
    {A K : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    (hA : HasFormalFibresProperty GeometricallyNormalProperty A)
    (D : HenselizationData A)
    (Ds : StrictHenselizationData A K)
    {K' : Type u} [Field K']
    [Algebra
      (IsLocalRing.ResidueField
        (ringCompletion (IsLocalRing.maximalIdeal A))) K']
    (D' : StrictHenselizationData
      (ringCompletion (IsLocalRing.maximalIdeal A)) K') :
    IsNagataRing A ∧
      numberOfBranches A D =
        ENat.card (MinimalPrimeSpectrum
          (ringCompletion (IsLocalRing.maximalIdeal A))) ∧
      numberOfGeometricBranches A Ds =
        numberOfGeometricBranches
          (ringCompletion (IsLocalRing.maximalIdeal A)) D' := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit109
