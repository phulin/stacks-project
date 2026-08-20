import Formalization.Books.Dpa.Unit08.LocalCompleteIntersectionRings
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Divided Power Algebra, Chapter 9: Local complete intersection maps

This file records the good-factorization definition and the comparison
statements for local complete-intersection homomorphisms.  Regular sequences,
Tor, completions, formal fibres, and the finite-type local-complete-
intersection predicate are the canonical interfaces from earlier chapters.
-/

namespace Formalization.Books.Dpa.Unit09

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dpa.Unit08
open Formalization.Books.Dpa.Unit07
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit83
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Good factorizations -/

/-- A good factorization of a local ring map in the sense of the source.

The intermediate ring is Noetherian and local, the two maps are local, the
second map is surjective, the first map is flat, and the fibre over the source
residue field is regular local.
-/
structure GoodFactorization
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) where
  S : Type u
  [commRingS : CommRing S]
  [noetherianS : IsNoetherianRing S]
  [localS : IsLocalRing S]
  toS : A →+* S
  toB : S →+* B
  commutes : toB.comp toS = f
  kernel : Ideal S
  kernel_eq_ker : kernel = RingHom.ker toB
  local_toS : IsLocalHom toS
  local_toB : IsLocalHom toB
  surjective : Function.Surjective toB
  flat_toS : RingHom.Flat toS
  fibre_regular :
    IsRegularLocalRing
      (S ⧸ Ideal.map toS (IsLocalRing.maximalIdeal A))

/-- The regular-sequence condition on the kernel carried by a factorization. -/
def GoodFactorization.kernelIsGeneratedByRegularSequence
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    {f : A →+* B} (F : GoodFactorization f) : Prop :=
  @IsGeneratedByRegularSequence F.S F.commRingS F.kernel

/-- The source's complete-intersection homomorphism predicate. -/
def IsCompleteIntersectionHomomorphism
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) : Prop :=
  ∃ F : GoodFactorization f,
    F.kernelIsGeneratedByRegularSequence

/-- The same predicate with the local-ring structures supplied as witnesses.
This is useful for completed rings, whose canonical local instances are not
always synthesized by Mathlib at the point where the source's map is used. -/
def IsCompleteIntersectionHomomorphismWithLocalStructures
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∃ (hA : IsLocalRing A) (hB : IsLocalRing B),
    @IsCompleteIntersectionHomomorphism A B inferInstance inferInstance hA hB f

/-- Complete Noetherian local ring maps admit a good factorization. -/
theorem exists_good_factorization
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) (hlocal : IsLocalHom f) :
    Nonempty (GoodFactorization f) := by
  sorry

/-- The kernel regular-sequence condition is independent of the good
factorization used to define a complete-intersection homomorphism. -/
theorem complete_intersection_homomorphism_iff_forall_good_factorizations
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) :
    IsCompleteIntersectionHomomorphism f ↔
      ∀ F : GoodFactorization f,
        F.kernelIsGeneratedByRegularSequence := by
  sorry

/-! ## Completions and Tor vanishing -/

/-- A map of rings has finite Tor dimension when its target, restricted to the
source, has finite Tor dimension. -/
def MapHasFiniteTorDimension
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  Formalization.Books.MoreAlgebra.Unit67.ModuleHasFiniteTorDimension A
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))

/-- The residue-field module of a local ring. -/
abbrev residueFieldModule
    (A : Type u) [CommRing A] [IsLocalRing A] : ModuleCat.{u} A :=
  ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A)

/-- Vanishing of the Tor groups with the source residue field above a finite
degree. -/
def TorWithResidueFieldVanishingAbove
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A]
    (f : A →+* B) : Prop :=
  ∃ N : ℕ, ∀ p : ℕ, N < p →
    IsZero
      (Formalization.Books.Algebra.Unit75.Tor
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))
        (residueFieldModule A) p)

/-- Finite Tor dimension implies the Tor vanishing condition used in the
source's Avramov criterion. -/
theorem tor_with_residue_field_vanishing_of_map_has_finite_tor_dimension
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A]
    (f : A →+* B) (hfd : MapHasFiniteTorDimension f) :
    TorWithResidueFieldVanishingAbove f := by
  sorry

/-- Flatness implies finite Tor dimension for a ring map. -/
theorem map_has_finite_tor_dimension_of_flat
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hflat : RingHom.Flat f) :
    MapHasFiniteTorDimension f := by
  sorry

/-- The condition that a completed map extends the original map. -/
def IsAdicCompletionLift
    {A B : Type u} [CommRing A] [CommRing B]
    (m : Ideal A) (n : Ideal B) (f : A →+* B)
    (fhat : AdicCompletion m A →+* AdicCompletion n B) : Prop :=
  fhat.comp (algebraMap A (AdicCompletion m A)) =
    (algebraMap B (AdicCompletion n B)).comp f

/-- The completed-map formulation of being a complete-intersection
homomorphism.  The extension equation makes the completion map explicit while
allowing the canonical completion map to be supplied by the adic-completion
universal property.
-/
def IsCompleteIntersectionAfterCompletion
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) : Prop :=
  ∃ fhat : AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
      AdicCompletion (IsLocalRing.maximalIdeal B) B,
    IsAdicCompletionLift
        (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B) f fhat ∧
      IsCompleteIntersectionHomomorphismWithLocalStructures fhat

/-- Avramov's criterion for local Noetherian ring maps, with the source's
completion map represented by its canonical extension property. -/
theorem avramov_map_iff
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hlocal : IsLocalHom f) :
    (IsCompleteIntersection B ∧
        TorWithResidueFieldVanishingAbove f) ↔
      (IsCompleteIntersection A ∧
        IsCompleteIntersectionAfterCompletion f) := by
  sorry

/-! ## The warning about general Noetherian rings

The source warns that formal fibres of arbitrary Noetherian local rings need
not be local complete intersections, so completion-based locality is not a
stable definition without additional hypotheses such as excellence.  The
remark gives no concrete counterexample or theorem interface; it is therefore
recorded here as a source-faithful warning rather than an artificial witness.
-/

/-! ## Comparison with the finite-type local-complete-intersection notion -/

/-- The good-factorization comparison lemma for a possibly noncomplete local
ring map. -/
theorem good_factorization_kernel_iff_completed_map
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (F : GoodFactorization f) :
    F.kernelIsGeneratedByRegularSequence ↔
      IsCompleteIntersectionAfterCompletion f := by
  sorry

/-- The induced local map on localizations at a prime and its contraction. -/
noncomputable def localizedRingHomAtPrime
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (q : PrimeSpectrum B) :
    Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal →+*
      Localization.AtPrime q.asIdeal :=
  Localization.localRingHom
    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl

/-- The completed local map at a prime of a finite-type target is a
complete-intersection homomorphism. -/
def IsCompleteIntersectionAfterCompletionAtPrime
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (q : PrimeSpectrum B) : Prop :=
  ∃ fhat :
      AdicCompletion
          (IsLocalRing.maximalIdeal
            (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal))
          (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal) →+*
      AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
          (Localization.AtPrime q.asIdeal),
    IsAdicCompletionLift
        (IsLocalRing.maximalIdeal
          (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal))
        (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
        (localizedRingHomAtPrime f q) fhat ∧
      IsCompleteIntersectionHomomorphismWithLocalStructures fhat

/-- For a finite-type map out of a Noetherian ring, the finite-type local
complete-intersection condition is equivalent to the completed local maps at
all primes being complete intersections. -/
theorem finite_type_lci_map_iff
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A]
    (f : A →+* B) (hfinite : RingHom.FiniteType f) :
    IsLocalCompleteIntersectionHom f ↔
      ∀ q : PrimeSpectrum B,
        IsCompleteIntersectionAfterCompletionAtPrime f q := by
  sorry

/-! ## The finite-type Avramov reformulation -/

/-- The image of `Spec B` contains every closed point of `Spec A`. -/
def ImageOfSpecContainsClosedPoints
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ m : MaximalSpectrum A,
    ∃ q : PrimeSpectrum B,
      PrimeSpectrum.comap f q = MaximalSpectrum.toPrimeSpectrum m

/-- The finite-type version of Avramov's criterion. -/
theorem finite_type_avramov_map_iff
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A]
    (f : A →+* B) (hfinite : RingHom.FiniteType f)
    (hclosed : ImageOfSpecContainsClosedPoints f) :
    (IsLocalCompleteIntersection B ∧ MapHasFiniteTorDimension f) ↔
      (IsLocalCompleteIntersection A ∧ IsLocalCompleteIntersectionHom f) := by
  sorry

end

end Formalization.Books.Dpa.Unit09
