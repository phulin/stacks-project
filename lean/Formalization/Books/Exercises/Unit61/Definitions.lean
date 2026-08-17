import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Topology.Constructible
import Mathlib.Topology.NoetherianSpace

/-!
# Exercises, Chapter 61: Definitions

The source asks for the standard definitions of constructible subsets,
localization at a prime, module length, projective modules, and
Cohen--Macaulay modules.  The first four are transparent names for the
canonical Mathlib notions.  The last definition uses the chapter's real
regular-sequence depth body together with Mathlib's support dimension.
-/

namespace Formalization.Books.Exercises.Unit61

open Set Topology TopologicalSpace
open scoped Pointwise

universe u v

noncomputable section

/-! ## Definitions from the first exercise -/

/-- A constructible subset of a Noetherian topological space. -/
abbrev IsConstructibleSubset
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X] (s : Set X) : Prop :=
  Topology.IsConstructible s

/-- The localization of a module at a prime of its base ring. -/
abbrev LocalizedModuleAtPrime
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (M : Type v) [AddCommGroup M] [Module R M] : Type (max u v) :=
  LocalizedModule p.asIdeal.primeCompl M

/-- The length of a module, with `⊤` denoting infinite length. -/
abbrev ModuleLength
    {R : Type u} [Ring R] (M : Type v) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R M

/-- Projectivity of a module, using Mathlib's canonical projective-module class. -/
abbrev IsProjectiveModule
    (R : Type u) (P : Type v) [Semiring R] [AddCommMonoid P] [Module R P] : Prop :=
  Module.Projective R P

/-! ## Depth and Cohen--Macaulay modules -/

/-- The depth of a finite module in an ideal, defined by regular sequences.

The first branch records the convention that an ideal acting surjectively on
the whole module gives depth `∞`; otherwise the supremum ranges over finite
regular sequences in the ideal.
-/
noncomputable def ModuleDepth
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] : ℕ∞ :=
  if _ : I • (⊤ : Submodule R M) = ⊤ then
    ⊤
  else
    sSup {n : ℕ∞ | ∃ rs : List R,
      n = (rs.length : ℕ∞) ∧
        (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs}

/-- Depth at the maximal ideal of a Noetherian local ring. -/
abbrev LocalModuleDepth
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : ℕ∞ :=
  ModuleDepth (IsLocalRing.maximalIdeal R) M

/-- A finite module over a Noetherian local ring is Cohen--Macaulay when its
local depth equals the dimension of its support. -/
def IsCohenMacaulayModule
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] : Prop :=
  ((LocalModuleDepth R M : ℕ∞) : WithBot ℕ∞) = Module.supportDim R M

end

end Formalization.Books.Exercises.Unit61
