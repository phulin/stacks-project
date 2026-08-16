import Mathlib.Algebra.Colimit.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Examples, Chapter 6: a connected scheme with domain local rings

This file formalizes the algebraic construction in the source section.  The
blowup discussion is motivation for the construction and is therefore not
duplicated as a second, unrelated formal model.
-/

noncomputable section

open AlgebraicGeometry

namespace Formalization.«Books.Examples».Unit06

universe u

/-! ## Connectedness, local domains, and affine spectra -/

/-- A commutative ring has no idempotents other than zero and one. -/
def NoNontrivialIdempotents (R : Type u) [MonoidWithZero R] : Prop :=
  ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1

/-- Every local ring of `X` is an integral domain. -/
def AllLocalRingsAreDomains (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x)

/-- The affine-local formulation of the vanishing condition used in the source.

The basic open `D(s)` is represented by `Localization.Away s`; the condition
`s ∉ x.asIdeal` says that it contains the point `x`.
-/
def LocalFactorVanishing (R : Type u) [CommRing R] : Prop :=
  ∀ (f g : R), f * g = 0 → ∀ x : PrimeSpectrum R,
    ∃ s : R, s ∉ x.asIdeal ∧
      (algebraMap R (Localization.Away s) f = 0 ∨
        algebraMap R (Localization.Away s) g = 0)

/-- Connectedness of an affine spectrum is the absence of nontrivial idempotents. -/
theorem spec_connected_iff_noNontrivialIdempotents (R : Type u) [CommRing R]
    [Nontrivial R] :
    ConnectedSpace (PrimeSpectrum R) ↔ NoNontrivialIdempotents R := by
  sorry

/-- The affine local-domain criterion used in the last part of the source. -/
theorem spec_allLocalRingsAreDomains_iff_localFactorVanishing
    (R : Type u) [CommRing R] :
    AllLocalRingsAreDomains (Spec (.of R)) ↔ LocalFactorVanishing R := by
  sorry

/-- A non-domain affine coordinate ring gives a non-integral affine scheme. -/
theorem spec_not_isIntegral_of_not_isDomain (R : Type u) [CommRing R]
    (hR : ¬ IsDomain R) : ¬ IsIntegral (Spec (.of R)) := by
  sorry

/-! ## The compatible polynomial chains -/

/-- The compatibility condition on a finite chain of copies of `ℂ[X]`. -/
def ChainCompatible (k : ℕ) (p : Fin (2 ^ k + 1) → Polynomial ℂ) : Prop :=
  ∀ i : Fin (2 ^ k),
    (p i.castSucc).eval 1 = (p i.succ).eval 0

/-- The subring of compatible polynomial chains defining `A_k`. -/
def chainSubring (k : ℕ) : Subring (Fin (2 ^ k + 1) → Polynomial ℂ) where
  carrier := {p | ChainCompatible k p}
  zero_mem' := by
    change ChainCompatible k 0
    intro i
    simp
  add_mem' := by
    intro p q hp hq
    change ChainCompatible k p at hp
    change ChainCompatible k q at hq
    change ChainCompatible k (p + q)
    intro i
    change (p i.castSucc + q i.castSucc).eval 1 =
      (p i.succ + q i.succ).eval 0
    rw [Polynomial.eval_add, Polynomial.eval_add, hp i, hq i]
  one_mem' := by
    change ChainCompatible k 1
    intro i
    simp
  mul_mem' := by
    intro p q hp hq
    change ChainCompatible k p at hp
    change ChainCompatible k q at hq
    change ChainCompatible k (p * q)
    intro i
    change (p i.castSucc * q i.castSucc).eval 1 =
      (p i.succ * q i.succ).eval 0
    rw [Polynomial.eval_mul, Polynomial.eval_mul, hp i, hq i]
  neg_mem' := by
    intro p hp
    change ChainCompatible k p at hp
    change ChainCompatible k (-p)
    intro i
    change (-p i.castSucc).eval 1 = (-p i.succ).eval 0
    rw [Polynomial.eval_neg, Polynomial.eval_neg, hp i]

/-- The ring `A_k` in the source. -/
abbrev ChainRing (k : ℕ) := ↥(chainSubring k)

/-! The source's description of `X_k` as a chain of affine lines is the
geometric interpretation of this explicit compatible-chain presentation.
The later declarations use the presentation itself, so no parallel ad hoc
component structure is introduced. -/

/-- The affine scheme `X_k = Spec(A_k)`. -/
abbrev ChainScheme (k : ℕ) : Scheme := Spec (.of (ChainRing k))

/-- The insertion of a chain into the next chain.

For an interior index, `finProdFinEquiv` separates the even/odd position and
the last position is the final polynomial.  The odd positions are constants
obtained by evaluating the preceding polynomial at `1`, exactly as in the
displayed map in the source.
-/
def chainInsertionPolynomial (k : ℕ) (p : ChainRing k)
    (j : Fin (2 ^ (k + 1) + 1)) : Polynomial ℂ := by
  let n := 2 ^ k
  let h : 2 * n + 1 = 2 ^ (k + 1) + 1 := by
    dsimp [n]
    rw [pow_succ, Nat.mul_comm]
  let j' : Fin (2 * n + 1) := Fin.cast h.symm j
  exact Fin.lastCases
    (Polynomial.C ((p.1 (Fin.last n)).eval 1))
    (fun i =>
      let ij := (finProdFinEquiv : Fin 2 × Fin n ≃ Fin (2 * n)).symm i
      if ij.1 = 0 then p.1 ij.2.castSucc
      else Polynomial.C ((p.1 ij.2.castSucc).eval 1))
    j'

/-- The polynomial family obtained by inserting constants at odd positions. -/
def chainInsertion (k : ℕ) : ChainRing k → (Fin (2 ^ (k + 1) + 1) → Polynomial ℂ) :=
  fun p => chainInsertionPolynomial k p

/-- The insertion formula preserves the chain compatibility equations. -/
theorem chainInsertion_compatible (k : ℕ) (p : ChainRing k) :
    ChainCompatible (k + 1) (chainInsertion k p) := by
  sorry

theorem chainInsertion_one (k : ℕ) :
    chainInsertion k (1 : ChainRing k) =
      (1 : Fin (2 ^ (k + 1) + 1) → Polynomial ℂ) := by
  sorry

theorem chainInsertion_zero (k : ℕ) :
    chainInsertion k (0 : ChainRing k) =
      (0 : Fin (2 ^ (k + 1) + 1) → Polynomial ℂ) := by
  sorry

theorem chainInsertion_add (k : ℕ) (p q : ChainRing k) :
    chainInsertion k (p + q) = chainInsertion k p + chainInsertion k q := by
  sorry

theorem chainInsertion_mul (k : ℕ) (p q : ChainRing k) :
    chainInsertion k (p * q) = chainInsertion k p * chainInsertion k q := by
  sorry

/-- The transition ring homomorphism `A_k → A_{k+1}`. -/
def chainTransition (k : ℕ) : ChainRing k →+* ChainRing (k + 1) where
  toFun p := ⟨chainInsertion k p, chainInsertion_compatible k p⟩
  map_one' := by
    apply Subtype.ext
    exact chainInsertion_one k
  map_mul' := by
    intro p q
    apply Subtype.ext
    exact chainInsertion_mul k p q
  map_zero' := by
    apply Subtype.ext
    exact chainInsertion_zero k
  map_add' := by
    intro p q
    apply Subtype.ext
    exact chainInsertion_add k p q

/-- The transition map is the source's inclusion of one chain into the next. -/
theorem chainTransition_injective (k : ℕ) :
    Function.Injective (chainTransition k) := by
  sorry

/-- Its range is the corresponding subring of the next stage. -/
def chainTransitionRange (k : ℕ) : Subring (ChainRing (k + 1)) :=
  (chainTransition k).range

/-- On the odd entries, the transition map is constant with the preceding
polynomial's value at `1`.  This is the algebraic form of the pullback
observation used in the local-domain argument. -/
theorem chainTransition_odd_entries_constant (k : ℕ) (p : ChainRing k) :
    ∀ i : Fin (2 ^ k),
      (chainTransition k p).1 (⟨2 * i + 1, by sorry⟩) =
        Polynomial.C ((p.1 i.castSucc).eval 1) := by
  sorry

/-! ## The direct limit and the induced affine scheme -/

/-- The map from `A_i` to `A_j`, obtained by iterating the adjacent maps. -/
def chainMapTo (i : ℕ) : ∀ j : ℕ, i ≤ j → ChainRing i →+* ChainRing j
  | 0, h => by
      have hi : i = 0 := Nat.eq_zero_of_le_zero h
      subst i
      exact RingHom.id _
  | j + 1, h => by
      by_cases hij : i = j + 1
      · subst i
        exact RingHom.id _
      · have hlt : i < j + 1 := lt_of_le_of_ne h hij
        exact (chainTransition j).comp (chainMapTo i j (Nat.le_of_lt_succ hlt))

/-- The iterated maps form the directed system used for the direct limit. -/
theorem chainMapTo_self (i : ℕ) :
    chainMapTo i i le_rfl = RingHom.id (ChainRing i) := by
  sorry

theorem chainMapTo_comp {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    (chainMapTo j l hjl).comp (chainMapTo i j hij) = chainMapTo i l (hij.trans hjl) := by
  sorry

/-- The sequential direct limit `A` of the rings `A_k`. -/
abbrev ChainDirectLimit : Type :=
  Ring.DirectLimit ChainRing (fun i j h => chainMapTo i j h)

/-- The canonical map `A_k → A`. -/
def chainLimitMap (k : ℕ) : ChainRing k →+* ChainDirectLimit :=
  Ring.DirectLimit.of ChainRing (fun i j h => chainMapTo i j h) k

@[simp]
theorem chainLimitMap_stage {i j : ℕ} (hij : i ≤ j) (p : ChainRing i) :
    chainLimitMap j (chainMapTo i j hij p) = chainLimitMap i p := by
  exact Ring.DirectLimit.of_f (G := ChainRing)
    (f := fun i j h => chainMapTo i j h) hij p

/-- The stage maps are embeddings, as in the source's union description of
the direct limit. -/
theorem chainLimitMap_injective (k : ℕ) :
    Function.Injective (chainLimitMap k) := by
  sorry

/-- Every element of the direct limit comes from one finite stage. -/
theorem chainLimit_exists_stage (a : ChainDirectLimit) :
    ∃ k : ℕ, ∃ p : ChainRing k, chainLimitMap k p = a := by
  simpa [chainLimitMap] using
    (Ring.DirectLimit.exists_of (G := ChainRing)
      (f := fun i j h => chainMapTo i j h) a)

/-- Two elements of `A` can be represented at one common stage.

This uses the stage index directly; it is the source's choice of `k - 1`
with `k` reindexed by one. -/
theorem chainLimit_pair_common_stage (f g : ChainDirectLimit) :
    ∃ k : ℕ, ∃ p q : ChainRing k,
      chainLimitMap k p = f ∧ chainLimitMap k q = g := by
  sorry

/-- The direct-limit scheme `X = Spec(A)`. -/
abbrev ChainLimitScheme : Scheme := Spec (.of ChainDirectLimit)

/-- The natural map `X → X_k` induced by `A_k → A`. -/
def chainSchemeMap (k : ℕ) : ChainLimitScheme ⟶ ChainScheme k :=
  Spec.map (CommRingCat.ofHom (chainLimitMap k))

/-- The image of a point of `X` in `X_k`. -/
def chainPointAt (k : ℕ) (x : ChainLimitScheme) : ChainScheme k :=
  chainSchemeMap k x

/-! ## The assertions about the example -/

/-- Each finite chain is connected in the idempotent sense and is not a domain. -/
theorem chainRing_connected_and_not_domain (k : ℕ) :
    NoNontrivialIdempotents (ChainRing k) ∧ ¬ IsDomain (ChainRing k) := by
  sorry

/-- The corresponding finite affine scheme is connected and nonintegral. -/
theorem chainScheme_connected_and_not_integral (k : ℕ) :
    ConnectedSpace (ChainScheme k) ∧ ¬ IsIntegral (ChainScheme k) := by
  sorry

/-- The direct limit is connected and is not a domain. -/
theorem chainLimit_connected_and_not_domain :
    NoNontrivialIdempotents ChainDirectLimit ∧ ¬ IsDomain ChainDirectLimit := by
  sorry

/-- The direct-limit affine scheme is connected and nonintegral. -/
theorem chainLimit_connected_and_not_integral :
    ConnectedSpace ChainLimitScheme ∧ ¬ IsIntegral ChainLimitScheme := by
  sorry

/-- The finite chain has the same local zero-product property used in the
source's smooth-point and singular-point case split. -/
theorem chainStage_localFactorVanishing (k : ℕ) :
    LocalFactorVanishing (ChainRing k) := by
  sorry

/-- The source's pointwise local-domain assertion, stated for the direct-limit
affine scheme. -/
theorem chainLimit_allLocalRingsAreDomains :
    AllLocalRingsAreDomains ChainLimitScheme := by
  sorry

/-- The equivalent zero-product/local-vanishing formulation for the direct
limit. -/
theorem chainLimit_localFactorVanishing :
    LocalFactorVanishing ChainDirectLimit := by
  sorry

end Formalization.«Books.Examples».Unit06
