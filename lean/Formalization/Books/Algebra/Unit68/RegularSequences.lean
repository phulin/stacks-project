import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative Algebra, Chapter 68: Regular sequences

The source uses the convention that the final quotient of a regular sequence is nonzero.
Mathlib's `RingTheory.Sequence.IsRegular` has exactly this convention, while
`RingTheory.Sequence.IsWeaklyRegular` is the corresponding predicate with that final
condition omitted.  We therefore use those canonical predicates directly instead of
introducing a parallel definition.
-/

namespace Formalization.Books.Algebra.Unit68

open Function
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Definition and examples -/

/-
The source's phrase “regular sequence in `I`” is the canonical regular-sequence predicate
together with the membership hypotheses `f ∈ I`; no additional predicate is needed.  The
order dependence is likewise already visible in the list argument of `IsRegular`.

The source warning about dropping the nonzero final quotient is represented by the distinction
between `IsRegular` and `IsWeaklyRegular` in the module API above.  The localization warning
concerns that convention and requires no separate declaration.
-/

abbrev globalExampleRing (k : Type u) [Field k] := MvPolynomial (Fin 3) k

def globalExampleSequence (k : Type u) [Field k] : List (globalExampleRing k) :=
  [ MvPolynomial.X 0,
    MvPolynomial.X 1 * (MvPolynomial.C 1 - MvPolynomial.X 0),
    MvPolynomial.X 2 * (MvPolynomial.C 1 - MvPolynomial.X 0) ]

def globalExampleReorderedSequence (k : Type u) [Field k] : List (globalExampleRing k) :=
  [ MvPolynomial.X 1 * (MvPolynomial.C 1 - MvPolynomial.X 0),
    MvPolynomial.X 2 * (MvPolynomial.C 1 - MvPolynomial.X 0),
    MvPolynomial.X 0 ]

theorem global_example_regular_sequence (k : Type u) [Field k] :
    RingTheory.Sequence.IsRegular (globalExampleRing k) (globalExampleSequence k) := by
  sorry

theorem global_example_reordered_not_regular (k : Type u) [Field k] :
    ¬ RingTheory.Sequence.IsRegular (globalExampleRing k)
        (globalExampleReorderedSequence k) := by
  sorry

inductive localExampleVariable
  | x
  | y
  | w (n : ℕ)
deriving DecidableEq

def localExampleX (k : Type u) [CommRing k] :
    MvPolynomial localExampleVariable k :=
  MvPolynomial.X .x

def localExampleY (k : Type u) [CommRing k] :
    MvPolynomial localExampleVariable k :=
  MvPolynomial.X .y

def localExampleW (k : Type u) [CommRing k] (n : ℕ) :
    MvPolynomial localExampleVariable k :=
  MvPolynomial.X (.w n)

def localExampleRelations (k : Type u) [CommRing k] :
    Set (MvPolynomial localExampleVariable k) :=
  Set.range (fun n : ℕ => localExampleY k * localExampleW k n) ∪
    Set.range (fun n : ℕ =>
      localExampleW k n - localExampleX k * localExampleW k (n + 1))

def localExampleIdeal (k : Type u) [CommRing k] :
    Ideal (MvPolynomial localExampleVariable k) :=
  Ideal.span (localExampleRelations k)

abbrev localExampleRing (k : Type u) [Field k] :=
  MvPolynomial localExampleVariable k ⧸ localExampleIdeal k

def localExampleXbar (k : Type u) [Field k] : localExampleRing k :=
  Ideal.Quotient.mk (localExampleIdeal k) (localExampleX k)

def localExampleYbar (k : Type u) [Field k] : localExampleRing k :=
  Ideal.Quotient.mk (localExampleIdeal k) (localExampleY k)

def localExampleWbar (k : Type u) [Field k] (n : ℕ) : localExampleRing k :=
  Ideal.Quotient.mk (localExampleIdeal k) (localExampleW k n)

def localExampleMaximalIdealGenerators (k : Type u) [Field k] :
    Set (localExampleRing k) :=
  {localExampleXbar k, localExampleYbar k} ∪ Set.range (localExampleWbar k)

def localExampleMaximalIdeal (k : Type u) [Field k] : Ideal (localExampleRing k) :=
  Ideal.span (localExampleMaximalIdealGenerators k)

theorem local_example_maximal_ideal_is_maximal (k : Type u) [Field k] :
    (localExampleMaximalIdeal k).IsMaximal := by
  sorry

/- The `letI` supplies the prime instance needed by the canonical `AtPrime` localization. -/
noncomputable abbrev localExampleLocalizedRing (k : Type u) [Field k] : Type _ :=
  letI : (localExampleMaximalIdeal k).IsMaximal :=
    local_example_maximal_ideal_is_maximal k
  Localization.AtPrime (localExampleMaximalIdeal k)

def localExampleLocalizedX (k : Type u) [Field k] :
    localExampleLocalizedRing k :=
  algebraMap (localExampleRing k) (localExampleLocalizedRing k) (localExampleXbar k)

def localExampleLocalizedY (k : Type u) [Field k] :
    localExampleLocalizedRing k :=
  algebraMap (localExampleRing k) (localExampleLocalizedRing k) (localExampleYbar k)

theorem local_example_regular_sequence (k : Type u) [Field k] :
    RingTheory.Sequence.IsRegular (localExampleRing k)
      [localExampleXbar k, localExampleYbar k] := by
  sorry

theorem local_example_y_is_zero_divisor (k : Type u) [Field k] :
    ¬ IsSMulRegular (localExampleRing k) (localExampleYbar k) := by
  sorry

theorem local_example_after_localization (k : Type u) [Field k] :
    RingTheory.Sequence.IsRegular (localExampleLocalizedRing k)
        [localExampleLocalizedX k, localExampleLocalizedY k] ∧
      ¬ IsSMulRegular (localExampleLocalizedRing k) (localExampleLocalizedY k) := by
  sorry

/-! ## Basic properties -/

theorem regular_sequence_permutation
    {R M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {xs ys : List R}
    (hxs : RingTheory.Sequence.IsRegular M xs)
    (hperm : xs.Perm ys) :
    RingTheory.Sequence.IsRegular M ys := by
  sorry

/- A flat local map is faithfully flat by the canonical local-flatness theorem.  The tensor
   product is written as `S ⊗[R] M`, the orientation for which Mathlib exposes the natural
   `S`-module structure; it is canonically equivalent to the source's `M ⊗[R] S` order. -/
theorem regular_sequence_flat_local
    {R S M : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M]
    (hflat : RingHom.Flat (algebraMap R S)) (xs : List R) :
    RingTheory.Sequence.IsRegular M xs ↔
      RingTheory.Sequence.IsRegular (S ⊗[R] M)
        (xs.map (algebraMap R S)) := by
  sorry

theorem regular_sequence_in_neighborhood
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] (xs : List R)
    (hp : RingTheory.Sequence.IsRegular
      (LocalizedModule.AtPrime p M)
      (xs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g : R, g ∉ p ∧
      RingTheory.Sequence.IsRegular
        (LocalizedModule (Submonoid.powers g) M)
        (xs.map (algebraMap R (Localization (Submonoid.powers g)))) := by
  sorry

theorem regular_sequence_join
    {A : Type*} [CommRing A] (I : Ideal A)
    {fs gs : List A}
    (hI : I = Ideal.ofList fs)
    (hfs : RingTheory.Sequence.IsRegular A fs)
    (hgs : RingTheory.Sequence.IsRegular (A ⧸ I)
      (gs.map (Ideal.Quotient.mk I))) :
    RingTheory.Sequence.IsRegular A (fs ++ gs) := by
  sorry

theorem regular_sequence_of_short_exact
    {R M₁ M₂ M₃ : Type*} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Injective f) (hfg : Exact f g) (hg : Surjective g)
    (xs : List R)
    (h₁ : RingTheory.Sequence.IsRegular M₁ xs)
    (h₃ : RingTheory.Sequence.IsRegular M₃ xs) :
    RingTheory.Sequence.IsRegular M₂ xs := by
  sorry

/- The source's first induction step uses the displayed short exact sequence
  `0 → M/fM → M/f^eM → M/f^(e-1)M → 0`; it is an intermediate proof interface, so the
  public chapter statement is the following powers equivalence and no duplicate auxiliary
  predicate is introduced. -/
theorem regular_sequence_powers_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (f : Fin n → R) (e : Fin n → ℕ)
    (he : ∀ i, 0 < e i) :
    RingTheory.Sequence.IsRegular M (List.ofFn f) ↔
      RingTheory.Sequence.IsRegular M
        (List.ofFn (fun i => f i ^ e i)) := by
  sorry

/- The source's polynomial proof uses the direct-sum decomposition indexed by multi-indices
  and the ideals `I_E`; these are proof-level bookkeeping for the final TFAE, not additional
  chapter-facing structures. -/
theorem regular_sequence_polynomial_iff
    {R : Type u} [CommRing R] (n : ℕ) (f : Fin n → R)
    (hnotunit : Ideal.ofList (List.ofFn f) ≠ (⊤ : Ideal R)) :
    List.TFAE
      [ (∀ ys : List R, List.Perm (List.ofFn f) ys →
            RingTheory.Sequence.IsRegular R ys),
        (∀ ys : List R, List.Sublist ys (List.ofFn f) →
            RingTheory.Sequence.IsRegular R ys),
        RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) R)
          (List.ofFn (fun i => MvPolynomial.C (f i) * MvPolynomial.X i)) ] := by
  sorry

end

end Formalization.Books.Algebra.Unit68
