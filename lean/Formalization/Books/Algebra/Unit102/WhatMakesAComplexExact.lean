import Formalization.Books.Algebra.Unit72
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Commutative Algebra, Chapter 102: What makes a complex exact?

The source works with finite complexes
`0 → R^{n_e} → ⋯ → R^{n_0}`.  A `FiniteFreeComplex` below records the
coordinate finite-free terms and extends the differentials by zero beyond the
last term.  This makes the source's indexing by positive integers explicit
while keeping the square-zero condition and exactness predicates usable.
-/

namespace Formalization.Books.Algebra.Unit102

open Set
open DirectSum
open scoped BigOperators

universe u

noncomputable section

/-! ## Finite free complexes and trivial summands -/

/-- A finite complex of finite free modules in the standard coordinate model.

`differential i` is the map from the term in degree `i + 1` to the term in
degree `i`.  The fields `termRank_zero` and `differential_zero` extend the
finite complex by zero in degrees beyond `length`; this is only bookkeeping
and does not add mathematical hypotheses to the source situation.
-/
structure FiniteFreeComplex (R : Type u) [CommRing R] (length : ℕ) where
  termRank : ℕ → ℕ
  termRank_zero : ∀ i, length < i → termRank i = 0
  differential : ∀ i : ℕ,
    (Fin (termRank (i + 1)) → R) →ₗ[R] (Fin (termRank i) → R)
  differential_zero : ∀ i, length ≤ i → differential i = 0
  differential_comp : ∀ i,
    (differential i).comp (differential (i + 1)) = 0

/-- The differential ending in degree `i`, with its source reindexed from
`i - 1 + 1` to `i`. -/
def FiniteFreeComplex.previousDifferential
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (i : ℕ) (hi : 0 < i) :
    (Fin (C.termRank i) → R) →ₗ[R] (Fin (C.termRank (i - 1)) → R) := by
  have h : i - 1 + 1 = i := Nat.sub_add_cancel hi
  exact h ▸ C.differential (i - 1)

private theorem transport_dependent
    {α : Type} {β : α → Type u} {a a' : α} (h : a = a')
    (f : ∀ n, β n) : h ▸ f a = f a' := by
  cases h
  rfl

private theorem transport_apply_symm
    {α : Type} {β γ : α → Type u} {a a' : α} (h : a = a')
    (f : ∀ n, β n → γ n) (x : β a') :
    f a (h.symm ▸ x) = h.symm ▸ ((h ▸ f a) x) := by
  cases h
  rfl

private theorem transport_apply_nested
    {α : Type} {β γ : α → Type u} {a a' : α} (h : a = a')
    (f : ∀ n, β n → γ n) (x : β a') :
    h.symm ▸ ((h ▸ f a) x) = f a (h.symm ▸ x) := by
  cases h
  rfl

private theorem transport_apply_fixed
    {α : Type} {β : α → Type u} {γ : Type u} {a a' : α} (h : a = a')
    (f : β a → γ) (x : β a') :
    f (h.symm ▸ x) = (h ▸ f) x := by
  cases h
  rfl

private theorem fin_function_transport
    {R : Type u} {m n : ℕ} (h : m = n) (x : Fin n → R) :
    h.symm ▸ x = fun z => x (Fin.cast h z) := by
  cases h
  rfl

private theorem transport_fin_linear_map_nested
    {R : Type u} [Semiring R] {rank : ℕ → ℕ} {a a' : ℕ} (h : a = a')
    (f : ∀ n, (Fin (rank (n + 1)) → R) →ₗ[R] (Fin (rank n) → R))
    (x : Fin (rank (a' + 1)) → R) :
    h.symm ▸ ((h ▸ f a) x) = f a (h.symm ▸ x) := by
  cases h
  rfl

private theorem transport_fin_linear_map_fixed
    {R : Type u} [Semiring R] {rank : ℕ → ℕ} {M : Type u}
    [AddCommMonoid M] [Module R M] {a a' : ℕ} (h : a = a')
    (f : (Fin (rank a) → R) →ₗ[R] M) (x : Fin (rank a') → R) :
    f (h.symm ▸ x) = (h ▸ f) x := by
  cases h
  rfl

private theorem transport_differential_fixed
    {R : Type u} [Semiring R] {rank : ℕ → ℕ} {n m : ℕ}
    (h : n + 1 = m) (hm : m - 1 = n) (d : ∀ k,
      (Fin (rank (k + 1)) → R) →ₗ[R] (Fin (rank k) → R))
    (x : Fin (rank m) → R) :
    hm ▸ ((@Eq.rec ℕ (n + 1)
      (fun k _ => (Fin (rank k) → R) →ₗ[R] (Fin (rank (k - 1)) → R))
      (d n) m h) x) =
      (@Eq.rec ℕ (n + 1)
        (fun k _ => (Fin (rank k) → R) →ₗ[R] (Fin (rank n) → R))
        (d n) m h) x := by
  cases h
  simp

/-- Exactness at one degree of a finite free complex.

Degree zero is the right endpoint and is not among the degrees at which the
source asks for exactness.  At the left endpoint exactness means injectivity;
at an interior positive degree it means `Function.Exact` for the two adjacent
differentials.
-/
def FiniteFreeComplex.IsExactAt
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (i : ℕ) : Prop :=
  if hi0 : i = 0 then
    True
  else if _hiL : i = length then
    length ≠ 0 ∧ Function.Injective
      (C.previousDifferential i (Nat.pos_of_ne_zero hi0))
  else if _hi_lt : i < length then
    Function.Exact (C.differential i)
      (C.previousDifferential i (Nat.pos_of_ne_zero hi0))
  else
    True

/-- Exactness at all positive terms of the displayed finite complex. -/
def FiniteFreeComplex.IsExact
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) : Prop :=
  ∀ i, C.IsExactAt i

/-- All matrix coefficients of all differentials lie in an ideal. -/
def FiniteFreeComplex.MatrixEntriesInIdeal
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (I : Ideal R) : Prop :=
  ∀ i, i < length →
    ∀ a b,
      (LinearMap.toMatrix' (C.differential i)) a b ∈ I

/-- The identity map between the two coordinate rank-one modules.

The heterogeneous equality records that the source and target have both been
identified with `R`, so the map is literally the identity after those
identifications.
-/
def IsIdentityMap
    {R : Type u} [CommRing R] {m n : ℕ}
    (f : (Fin m → R) →ₗ[R] (Fin n → R)) : Prop :=
  m = 1 ∧ n = 1 ∧
    HEq f (LinearMap.id : (Fin 1 → R) →ₗ[R] (Fin 1 → R))

/-- A complex of one of the two trivial forms in the source.

The first disjunct is an identity `R → R` in two adjacent degrees and zero
elsewhere.  The second is a single copy of `R` in degree zero and zero in all
positive degrees.
-/
def FiniteFreeComplex.IsTrivial
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) : Prop :=
  (∃ i : ℕ, ∃ hi : 1 ≤ i,
      i ≤ length ∧ C.termRank i = 1 ∧ C.termRank (i - 1) = 1 ∧
        (∀ j, j ≠ i → j ≠ i - 1 → C.termRank j = 0) ∧
        IsIdentityMap (C.previousDifferential i hi) ∧
        ∀ j, j ≠ i - 1 → C.differential j = 0) ∨
    (C.termRank 0 = 1 ∧
      (∀ j, 0 < j → C.termRank j = 0) ∧
      ∀ j, C.differential j = 0)

/-! The direct-sum interface is expressed using Mathlib's canonical direct sum
of modules.  This records an actual degreewise linear equivalence commuting
with the differentials, rather than introducing a second notion of a complex.
-/

/-- The differential on the direct sum of a finite family of complexes. -/
noncomputable def directSumDifferential
    {R : Type u} [CommRing R] {length k : ℕ}
    (T : Fin k → FiniteFreeComplex R length) (i : ℕ) :
    (⨁ j : Fin k, (Fin ((T j).termRank (i + 1)) → R)) →ₗ[R]
      (⨁ j : Fin k, (Fin ((T j).termRank i) → R)) :=
  DirectSum.lmap (fun j => (T j).differential i)

/-- A degreewise isomorphism from a complex to a direct sum of complexes. -/
structure DirectSumDecomposition
    {R : Type u} [CommRing R] {length k : ℕ}
    (C : FiniteFreeComplex R length)
    (T : Fin k → FiniteFreeComplex R length) where
  component : ∀ i,
    (Fin (C.termRank i) → R) ≃ₗ[R]
      (⨁ j : Fin k, (Fin ((T j).termRank i) → R))
  commute : ∀ i,
    (component i).toLinearMap.comp (C.differential i) =
      (directSumDifferential T i).comp (component (i + 1)).toLinearMap

/-- A finite free complex is a direct sum of trivial complexes. -/
def FiniteFreeComplex.IsDirectSumOfTrivial
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) : Prop :=
  ∃ k : ℕ, ∃ T : Fin k → FiniteFreeComplex R length,
    (∀ j, (T j).IsTrivial) ∧ Nonempty (DirectSumDecomposition C T)

/-- Prepend one complex to a family of summands. -/
def prependSummand
    {R : Type u} [CommRing R] {length k : ℕ}
    (D : FiniteFreeComplex R length)
    (T : Fin k → FiniteFreeComplex R length) :
    Fin (k + 1) → FiniteFreeComplex R length :=
  Fin.cases D (fun j => T j)

/-- Being isomorphic, up to adding trivial direct summands. -/
def IsomorphicUpToTrivialSummands
    {R : Type u} [CommRing R] {length : ℕ}
    (C D : FiniteFreeComplex R length) : Prop :=
  ∃ k : ℕ, ∃ T : Fin k → FiniteFreeComplex R length,
    (∀ j, (T j).IsTrivial) ∧
      Nonempty (DirectSumDecomposition C (prependSummand D T))

/-- The rank vector of the complex after removing an identity summand at `i`.

Only degrees at most `length` are relevant; the predicate is deliberately
stated as an equality of the displayed ranks, matching the source's
`n_i - 1` and `n_{i-1} - 1` notation.
-/
def IsReducedAt
    {R : Type u} [CommRing R] {length : ℕ}
    (C D : FiniteFreeComplex R length) (i : ℕ) : Prop :=
  ∀ j, j ≤ length →
    D.termRank j =
      C.termRank j - (if j = i then 1 else 0) -
        (if j = i - 1 then 1 else 0)

private def pivotLinearEquiv
    {R : Type u} [CommRing R] {n m : ℕ} (h : n + 1 = m) (p : Fin m) :
    (R × (Fin n → R)) ≃ₗ[R] (Fin m → R) := by
  let q : Fin (n + 1) := p.cast h.symm
  let e : (R × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R) :=
    { toFun := fun x => q.insertNth x.1 x.2
      invFun := fun x => (x q, q.removeNth x)
      left_inv := by
        intro x
        ext <;> simp [q]
      right_inv := by
        intro x
        ext j
        by_cases hj : j = q
        · subst hj
          simp [q, Fin.removeNth]
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
          simp [q, Fin.removeNth_apply]
      map_add' := by
        intro x y
        ext j
        by_cases hj : j = q
        · subst hj
          simp [q, Fin.removeNth_apply]
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
          simp [q, Fin.removeNth_apply]
      map_smul' := by
        intro r x
        ext j
        by_cases hj : j = q
        · subst hj
          simp [q]
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
          simp [q, Fin.removeNth] }
  exact e ≪≫ₗ LinearEquiv.piCongrLeft R (fun _ : Fin m => R) (finCongr h)

private def sourceShear
    {R X : Type u} [CommRing R] [AddCommGroup X] [Module R X]
    (v : R) (h : X →ₗ[R] R) : (R × X) ≃ₗ[R] (R × X) :=
  { toFun := fun z => (z.1 - v * h z.2, z.2)
    invFun := fun z => (z.1 + v * h z.2, z.2)
    left_inv := by
      intro z
      ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    right_inv := by
      intro z
      ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    map_add' := by
      intro x y
      ext
      · simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add, sub_eq_add_neg,
          neg_add]
        abel
      · simp
    map_smul' := by
      intro r x
      ext
      · simp [map_smul, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] <;> ring
      · simp }

private def targetShear
    {R Y : Type u} [CommRing R] [AddCommGroup Y] [Module R Y]
    (c v : R) (g : R →ₗ[R] Y) (hcv : c * v = 1) (hvc : v * c = 1) :
    (R × Y) ≃ₗ[R] (R × Y) :=
  { toFun := fun z => (c * z.1, g z.1 + z.2)
    invFun := fun z => (v * z.1, z.2 - g (v * z.1))
    left_inv := by
      intro z
      ext
      · calc
          v * (c * z.1) = (v * c) * z.1 := by ring
          _ = z.1 := by rw [hvc, one_mul]
      · change (g z.1 + z.2) - g (v * (c * z.1)) = z.2
        have hz : v * (c * z.1) = z.1 := by
          calc
            v * (c * z.1) = (v * c) * z.1 := by ring
            _ = z.1 := by rw [hvc, one_mul]
        rw [hz]
        simp
    right_inv := by
      intro z
      ext
      · calc
          c * (v * z.1) = (c * v) * z.1 := by ring
          _ = z.1 := by rw [hcv, one_mul]
      · simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    map_add' := by
      intro x y
      ext
      · simp only [Prod.fst_add, mul_add]
      · simp only [Prod.fst_add, Prod.snd_add, map_add]
        abel
    map_smul' := by
      intro r x
      ext
      · simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
      · change g (r • x.1) + r • x.2 = r • (g x.1 + x.2)
        simpa [smul_eq_mul] using g.map_smul r x.1 }

/-! An invertible matrix coefficient permits removal of an identity summand. -/
theorem lemma_add_trivial_complex
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) {i : ℕ}
    (hi : 1 ≤ i) (hi' : i ≤ length)
    (hunit : ∃ a : Fin (C.termRank (i - 1)),
      ∃ b : Fin (C.termRank i),
        IsUnit ((LinearMap.toMatrix'
          (C.previousDifferential i hi)) a b)) :
    ∃ D : FiniteFreeComplex R length,
      IsReducedAt C D i ∧
        ∃ T : FiniteFreeComplex R length,
          T.IsTrivial ∧
            Nonempty
              (DirectSumDecomposition C
                (prependSummand D (fun _ : Fin 1 => T))) := by
  classical
  rcases hunit with ⟨a, b, hab⟩
  have hma : 0 < C.termRank (i - 1) :=
    lt_of_le_of_lt (Nat.zero_le a.1) a.2
  have hmi : 0 < C.termRank i :=
    lt_of_le_of_lt (Nat.zero_le b.1) b.2
  have hma' : (C.termRank (i - 1) - 1) + 1 = C.termRank (i - 1) :=
    Nat.sub_add_cancel hma
  have hmi' : (C.termRank i - 1) + 1 = C.termRank i :=
    Nat.sub_add_cancel hmi
  let a' : Fin (C.termRank (i - 1) - 1 + 1) := a.cast hma'.symm
  let b' : Fin (C.termRank i - 1 + 1) := b.cast hmi'.symm
  let f := C.previousDifferential i hi
  let sp : (R × (Fin (C.termRank i - 1) → R)) ≃ₗ[R]
      (Fin (C.termRank i) → R) := pivotLinearEquiv hmi' b
  let tp : (R × (Fin (C.termRank (i - 1) - 1) → R)) ≃ₗ[R]
      (Fin (C.termRank (i - 1)) → R) := pivotLinearEquiv hma' a
  let f0 : (R × (Fin (C.termRank i - 1) → R)) →ₗ[R]
      (R × (Fin (C.termRank (i - 1) - 1) → R)) :=
    tp.symm.toLinearMap.comp (f.comp sp.toLinearMap)
  let f00 : R →ₗ[R] R :=
    (LinearMap.fst R R (Fin (C.termRank (i - 1) - 1) → R)).comp
      (f0.comp (LinearMap.inl R R (Fin (C.termRank i - 1) → R)))
  let f01 : (Fin (C.termRank i - 1) → R) →ₗ[R] R :=
    (LinearMap.fst R R (Fin (C.termRank (i - 1) - 1) → R)).comp
      (f0.comp (LinearMap.inr R R (Fin (C.termRank i - 1) → R)))
  let f10 : R →ₗ[R] (Fin (C.termRank (i - 1) - 1) → R) :=
    (LinearMap.snd R R (Fin (C.termRank (i - 1) - 1) → R)).comp
      (f0.comp (LinearMap.inl R R (Fin (C.termRank i - 1) → R)))
  let f11 : (Fin (C.termRank i - 1) → R) →ₗ[R]
      (Fin (C.termRank (i - 1) - 1) → R) :=
    (LinearMap.snd R R (Fin (C.termRank (i - 1) - 1) → R)).comp
      (f0.comp (LinearMap.inr R R (Fin (C.termRank i - 1) → R)))
  have hsp : sp (1, 0) = Pi.single b 1 := by
    simp [sp, pivotLinearEquiv, Fin.insertNth, Fin.removeNth,
      LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']
    ext j
    simp [Equiv.piCongrLeft', Pi.single_apply]
  have htpa (x : Fin (C.termRank (i - 1)) → R) :
      (tp.symm x).1 = x a := by
    simp [tp, pivotLinearEquiv, Fin.insertNth, Fin.removeNth,
      LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']
  have hf00 : f00 1 = LinearMap.toMatrix' f a b := by
    change (tp.symm (f (sp (1, 0)))).1 = f (Pi.single b 1) a
    rw [hsp, htpa]
  rcases hab with ⟨u, hu⟩
  have hcu : f00 1 = (u : R) := hf00.trans hu.symm
  let c : R := f00 1
  let v : R := (↑(u⁻¹) : R)
  have hc : c = (u : R) := hcu
  have hcv : c * v = 1 := by
    rw [hc]
    simpa [v] using congrArg (fun z : Rˣ => (z : R)) (mul_inv_cancel u)
  have hvc : v * c = 1 := by
    rw [hc]
    simpa [v] using congrArg (fun z : Rˣ => (z : R)) (inv_mul_cancel u)
  let ss := sourceShear v f01
  let ts := targetShear c v f10 hcv hvc
  let srcPre : ((Fin (C.termRank i - 1) → R) × (Fin 1 → R)) ≃ₗ[R]
      (R × (Fin (C.termRank i - 1) → R)) :=
    ((LinearEquiv.refl R (Fin (C.termRank i - 1) → R)).prodCongr
      (LinearEquiv.piUnique R (fun _ : Fin 1 => R))) ≪≫ₗ
        LinearEquiv.prodComm R (Fin (C.termRank i - 1) → R) R
  let tgtPre : ((Fin (C.termRank (i - 1) - 1) → R) × (Fin 1 → R)) ≃ₗ[R]
      (R × (Fin (C.termRank (i - 1) - 1) → R)) :=
    ((LinearEquiv.refl R (Fin (C.termRank (i - 1) - 1) → R)).prodCongr
      (LinearEquiv.piUnique R (fun _ : Fin 1 => R))) ≪≫ₗ
        LinearEquiv.prodComm R (Fin (C.termRank (i - 1) - 1) → R) R
  let coordI : ((Fin (C.termRank i - 1) → R) × (Fin 1 → R)) ≃ₗ[R]
      (Fin (C.termRank i) → R) := srcPre ≪≫ₗ ss ≪≫ₗ sp
  let coordIm1 : ((Fin (C.termRank (i - 1) - 1) → R) × (Fin 1 → R)) ≃ₗ[R]
      (Fin (C.termRank (i - 1)) → R) := tgtPre ≪≫ₗ ts ≪≫ₗ tp
  let dRank : ℕ → ℕ := fun j =>
    if j = i then C.termRank j - 1
    else if j = i - 1 then C.termRank j - 1
    else C.termRank j
  let tRank : ℕ → ℕ := fun j => if j = i then 1 else if j = i - 1 then 1 else 0
  have hi_ne_prev : i ≠ i - 1 := by omega
  have hprev_ne_i : i - 1 ≠ i := by omega
  let coord : ∀ j, ((Fin (dRank j) → R) × (Fin (tRank j) → R)) ≃ₗ[R]
      (Fin (C.termRank j) → R) := fun j => by
    by_cases hji : j = i
    · subst j
      have hd : dRank i = C.termRank i - 1 := by simp [dRank, hi_ne_prev]
      have ht : tRank i = 1 := by simp [tRank]
      let ed : (Fin (dRank i) → R) ≃ₗ[R]
          (Fin (C.termRank i - 1) → R) :=
        LinearEquiv.piCongrLeft R (fun _ : Fin (C.termRank i - 1) => R)
          (finCongr hd)
      let et : (Fin (tRank i) → R) ≃ₗ[R] (Fin 1 → R) :=
        LinearEquiv.piCongrLeft R (fun _ : Fin 1 => R) (finCongr ht)
      exact ed.prodCongr et ≪≫ₗ coordI
    · by_cases hjp : j = i - 1
      · subst j
        have hd : dRank (i - 1) = C.termRank (i - 1) - 1 := by
          simp [dRank, hprev_ne_i]
        have ht : tRank (i - 1) = 1 := by simp [tRank, hprev_ne_i]
        let ed : (Fin (dRank (i - 1)) → R) ≃ₗ[R]
            (Fin (C.termRank (i - 1) - 1) → R) :=
          LinearEquiv.piCongrLeft R
            (fun _ : Fin (C.termRank (i - 1) - 1) => R) (finCongr hd)
        let et : (Fin (tRank (i - 1)) → R) ≃ₗ[R] (Fin 1 → R) :=
          LinearEquiv.piCongrLeft R (fun _ : Fin 1 => R) (finCongr ht)
        exact ed.prodCongr et ≪≫ₗ coordIm1
      · have hd : dRank j = C.termRank j := by simp [dRank, hji, hjp]
        have ht : tRank j = 0 := by simp [tRank, hji, hjp]
        let ed : (Fin (dRank j) → R) ≃ₗ[R] (Fin (C.termRank j) → R) :=
          LinearEquiv.piCongrLeft R (fun _ : Fin (C.termRank j) => R)
            (finCongr hd)
        let et : (Fin (tRank j) → R) ≃ₗ[R] (Fin 0 → R) :=
          LinearEquiv.piCongrLeft R (fun _ : Fin 0 => R) (finCongr ht)
        exact ed.prodCongr et ≪≫ₗ
          LinearEquiv.prodUnique (R := R) (M := (Fin (C.termRank j) → R))
            (M₂ := (Fin 0 → R))
  let tDiff : ∀ j, (Fin (tRank (j + 1)) → R) →ₗ[R]
      (Fin (tRank j) → R) := fun j => by
    by_cases hj : j = i - 1
    · subst j
      have hplus : i - 1 + 1 = i := Nat.sub_add_cancel hi
      have hs : tRank (i - 1 + 1) = 1 := by rw [hplus]; simp [tRank]
      have ht : tRank (i - 1) = 1 := by simp [tRank, hprev_ne_i]
      let es : (Fin (tRank (i - 1 + 1)) → R) ≃ₗ[R] (Fin 1 → R) :=
        LinearEquiv.piCongrLeft R (fun _ : Fin 1 => R) (finCongr hs)
      let et : (Fin (tRank (i - 1)) → R) ≃ₗ[R] (Fin 1 → R) :=
        LinearEquiv.piCongrLeft R (fun _ : Fin 1 => R) (finCongr ht)
      exact et.symm.toLinearMap.comp es.toLinearMap
    · exact 0
  let g : ∀ j, ((Fin (dRank (j + 1)) → R) × (Fin (tRank (j + 1)) → R)) →ₗ[R]
      ((Fin (dRank j) → R) × (Fin (tRank j) → R)) := fun j => by
    by_cases hj : j = i - 1
    · subst j
      have hplus' : i - 1 + 1 = i := Nat.sub_add_cancel hi
      exact hplus'.symm ▸
        ((coord (i - 1)).symm.toLinearMap.comp
          (f.comp (coord i).toLinearMap))
    · exact (coord j).symm.toLinearMap.comp
        ((C.differential j).comp (coord (j + 1)).toLinearMap)
  let dDiff : ∀ j, (Fin (dRank (j + 1)) → R) →ₗ[R]
      (Fin (dRank j) → R) := fun j =>
    (LinearMap.fst R (Fin (dRank j) → R) (Fin (tRank j) → R)).comp
      ((g j).comp (LinearMap.inl R (Fin (dRank (j + 1)) → R)
        (Fin (tRank (j + 1)) → R)))
  have hfdiff : f.comp (C.differential i) = 0 := by
    apply LinearMap.ext
    intro x
    have hI : i - 1 + 1 = i := Nat.sub_add_cancel hi
    have hmap : (hI ▸ C.differential (i - 1 + 1)) = C.differential i :=
      transport_dependent hI C.differential
    have hmapx := congrArg (fun q => q x) hmap
    have hx := congrArg
      (fun q => q (hI.symm ▸ x))
      (C.differential_comp (i - 1))
    have hnest := transport_fin_linear_map_nested (rank := C.termRank) hI
      C.differential x
    have hzero : C.differential (i - 1)
        (hI.symm ▸ ((hI ▸ C.differential (i - 1 + 1)) x)) = 0 := by
      rw [hnest]
      simpa [LinearMap.comp_apply] using hx
    have hfixed := transport_fin_linear_map_fixed (rank := C.termRank)
      hI (C.differential (i - 1))
        ((hI ▸ C.differential (i - 1 + 1)) x)
    have htrans : f ((hI ▸ C.differential (i - 1 + 1)) x) = 0 := by
      dsimp [f, FiniteFreeComplex.previousDifferential]
      exact (transport_differential_fixed (rank := C.termRank) hI
        (rfl : i - 1 = i - 1) C.differential
          ((hI ▸ C.differential (i - 1 + 1)) x)).trans
        (hfixed.symm.trans hzero)
    change f (C.differential i x) = 0
    rw [← hmapx]
    exact htrans
  have hgcomp (j : ℕ) : (g j).comp (g (j + 1)) = 0 := by
    by_cases h1 : j = i - 1
    · subst j
      have hplus : i - 1 + 1 = i := Nat.sub_add_cancel hi
      have transport_gcomp : ∀ (n m : ℕ) (h : n = m)
          (L : ((Fin (dRank m) → R) × (Fin (tRank m) → R)) →ₗ[R]
            ((Fin (dRank (i - 1)) → R) × (Fin (tRank (i - 1)) → R)))
          (K : ((Fin (dRank (m + 1)) → R) × (Fin (tRank (m + 1)) → R)) →ₗ[R]
            ((Fin (dRank m) → R) × (Fin (tRank m) → R))),
          L.comp K = 0 →
          (h.symm ▸ L).comp
              (show ((Fin (dRank (n + 1)) → R) × (Fin (tRank (n + 1)) → R)) →ₗ[R]
                ((Fin (dRank n) → R) × (Fin (tRank n) → R)) from h.symm ▸ K) = 0 := by
        intro n m h L K hL
        cases h
        exact hL
      have hbase :
          (((coord (i - 1)).symm.toLinearMap.comp
            (f.comp (coord i).toLinearMap)).comp
            ((coord i).symm.toLinearMap.comp
              ((C.differential i).comp (coord (i + 1)).toLinearMap))) = 0 := by
        apply LinearMap.ext
        intro x
        change (coord (i - 1)).symm
          (f ((coord i) ((coord i).symm
            (C.differential i ((coord (i + 1)) x))))) = 0
        rw [LinearEquiv.apply_symm_apply]
        have hzero := congrArg
          (fun q => (coord (i - 1)).symm (q ((coord (i + 1)) x))) hfdiff
        simpa [LinearMap.comp_apply] using hzero
      have htransport := transport_gcomp (i - 1 + 1) i hplus
        ((coord (i - 1)).symm.toLinearMap.comp
          (f.comp (coord i).toLinearMap))
        ((coord i).symm.toLinearMap.comp
          ((C.differential i).comp (coord (i + 1)).toLinearMap)) hbase
      have transport_generic : ∀ (n m : ℕ) (h : n = m),
          (coord n).symm.toLinearMap.comp
              ((C.differential n).comp (coord (n + 1)).toLinearMap) =
            h.symm ▸
              ((coord m).symm.toLinearMap.comp
                ((C.differential m).comp (coord (m + 1)).toLinearMap)) := by
        intro n m h
        cases h
        rfl
      have hgi :
          g (i - 1 + 1) =
            show ((Fin (dRank (i - 1 + 1 + 1)) → R) ×
                (Fin (tRank (i - 1 + 1 + 1)) → R)) →ₗ[R]
              ((Fin (dRank (i - 1 + 1)) → R) ×
                (Fin (tRank (i - 1 + 1)) → R)) from
            hplus.symm ▸
              ((coord i).symm.toLinearMap.comp
                ((C.differential i).comp (coord (i + 1)).toLinearMap)) := by
        have hne : i - 1 + 1 ≠ i - 1 := by omega
        rw [show g (i - 1 + 1) =
            (coord (i - 1 + 1)).symm.toLinearMap.comp
              ((C.differential (i - 1 + 1)).comp
                (coord (i - 1 + 1 + 1)).toLinearMap) by simp [g, hne]]
        exact transport_generic (i - 1 + 1) i hplus
      have hgj :
          g (i - 1) = hplus.symm ▸
            ((coord (i - 1)).symm.toLinearMap.comp
              (f.comp (coord i).toLinearMap)) := by
        simp [g, hplus]
      rw [hgi, hgj]
      exact htransport
    · by_cases h2 : j + 1 = i - 1
      · have hj : j = i - 2 := by omega
        subst j
        have hpos : 0 < i - 1 := by omega
        have hleft :
            (C.previousDifferential (i - 1) hpos).comp f = 0 := by
          apply LinearMap.ext
          intro x
          have hC : i - 2 + 1 + 1 = i := by omega
          have hC' : C.termRank (i - 2 + 1 + 1) = C.termRank i :=
            congrArg C.termRank hC
          have hx := congrArg
            (fun q => q (fun z => x (Fin.cast hC' z)))
            (C.differential_comp (i - 2))
          simpa [f, FiniteFreeComplex.previousDifferential,
            LinearMap.comp_apply] using hx
        apply LinearMap.ext
        intro x
        simp [g, h1, h2, f, FiniteFreeComplex.previousDifferential,
          LinearMap.comp_apply, hleft]
      · apply LinearMap.ext
        intro x
        have hzero := congrArg
          (fun q => (coord j).symm (q ((coord (j + 1 + 1)) x)))
          (C.differential_comp j)
        simpa [g, h1, h2, LinearMap.comp_apply] using hzero
  have hti0 : tRank i = 1 := by simp [tRank]
  have hf010 : f01 (0 : Fin (C.termRank i - 1) → R) = 0 := by
    change (f0 (0, 0)).1 = 0
    have hzero : f0 (0 : R × (Fin (C.termRank i - 1) → R)) = 0 :=
      f0.map_zero
    calc
      (f0 (0, 0)).1 = (f0 (0 : R × (Fin (C.termRank i - 1) → R))).1 := by
        rfl
      _ = (0 : R × (Fin (C.termRank (i - 1) - 1) → R)).1 := by rw [hzero]
      _ = 0 := rfl
  have hf010' : f01 (fun _ => 0) = 0 := by
    change f01 (0 : Fin (C.termRank i - 1) → R) = 0
    exact hf010
  have hcoord_inr :
      coord i (0, Pi.single (Fin.cast hti0.symm (0 : Fin 1)) 1) =
        Pi.single b 1 := by
    simp [coord, coordI, srcPre, ss, sp, sourceShear, hsp, hf010, hf010', dRank, tRank,
      hi_ne_prev, hprev_ne_i, Nat.sub_add_cancel hi, pivotLinearEquiv,
      Fin.insertNth, Fin.removeNth, LinearEquiv.piCongrLeft,
      LinearEquiv.piCongrLeft', Equiv.piCongrLeft', Pi.single_apply]
    ext x
    by_cases hx : x = b
    · subst x
      simp [Fin.succAboveCases, Pi.single_apply]
    · simp [Fin.succAboveCases, Pi.single_apply, hx]
  have htarget_pivot :
      coordIm1.symm (f (Pi.single b 1)) =
        (0, Pi.single (0 : Fin 1) 1) := by
    rw [← hsp]
    change tgtPre.symm (ts.symm (tp.symm (f (sp (1, 0))))) = _
    change tgtPre.symm (ts.symm (f0 (1, 0))) = _
    have hf0pivot : f0 (1, 0) = (c, f10 1) := by
      apply Prod.ext
      · change f00 1 = c
        rfl
      · change f10 1 = f10 1
        rfl
    rw [hf0pivot]
    simp [tgtPre, ts, targetShear, hcv, hvc, c, v]
    ext x
    fin_cases x
    simp
  have htarget_first :
      ((coord (i - 1)).symm (f (Pi.single b 1))).1 = 0 := by
    simp [coord, dRank, tRank, hi_ne_prev, hprev_ne_i,
      LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
      Equiv.piCongrLeft', Pi.single_apply, htarget_pivot]
    ext x
    simp
  have hg_firstzero :
      (LinearMap.fst R (Fin (dRank (i - 1)) → R) (Fin (tRank (i - 1)) → R)).comp
          ((g (i - 1)).comp (LinearMap.inr R (Fin (dRank (i - 1 + 1)) → R)
            (Fin (tRank (i - 1 + 1)) → R))) = 0 := by
    have hplus : i - 1 + 1 = i := Nat.sub_add_cancel hi
    have transport_firstzero : ∀ (n m : ℕ) (h : n = m)
        (L : ((Fin (dRank m) → R) × (Fin (tRank m) → R)) →ₗ[R]
          ((Fin (dRank (i - 1)) → R) × (Fin (tRank (i - 1)) → R))),
        (((LinearMap.fst R (Fin (dRank (i - 1)) → R)
            (Fin (tRank (i - 1)) → R)).comp
          (L.comp (LinearMap.inr R (Fin (dRank m) → R) (Fin (tRank m) → R)))) = 0) →
        (((LinearMap.fst R (Fin (dRank (i - 1)) → R)
            (Fin (tRank (i - 1)) → R)).comp
          ((h.symm ▸ L).comp
            (LinearMap.inr R (Fin (dRank n) → R) (Fin (tRank n) → R)))) = 0) := by
      intro n m h L hL
      cases h
      exact hL
    have hmap :
        (((LinearMap.fst R (Fin (dRank (i - 1)) → R) (Fin (tRank (i - 1)) → R)).comp
            ((coord (i - 1)).symm.toLinearMap.comp
          (f.comp (coord i).toLinearMap))).comp
          (LinearMap.inr R (Fin (dRank i) → R) (Fin (tRank i) → R))) = 0 := by
      have hti : tRank i = 1 := by simp [tRank]
      apply LinearMap.ext
      intro z
      have hz : z = z (Fin.cast hti.symm (0 : Fin 1)) •
          Pi.single (Fin.cast hti.symm (0 : Fin 1)) 1 := by
        funext q
        have hq : q = Fin.cast hti.symm (0 : Fin 1) := by
          apply Fin.ext
          omega
        subst q
        simp
      rw [hz]
      simp only [map_smul]
      have hb :
          (((LinearMap.fst R (Fin (dRank (i - 1)) → R)
              (Fin (tRank (i - 1)) → R)).comp
            ((coord (i - 1)).symm.toLinearMap.comp
              (f.comp (coord i).toLinearMap))).comp
          (LinearMap.inr R (Fin (dRank i) → R) (Fin (tRank i) → R)))
            (Pi.single (Fin.cast hti.symm (0 : Fin 1)) 1) = 0 := by
        simp [LinearMap.comp_apply]
        change
          ((coord (i - 1)).symm
            (f (coord i (0, Pi.single (Fin.cast hti.symm (0 : Fin 1)) 1)))).1 = 0
        rw [hcoord_inr]
        exact htarget_first
      rw [hb]
      simp
    have htransport := transport_firstzero (i - 1 + 1) i hplus
      ((coord (i - 1)).symm.toLinearMap.comp
        (f.comp (coord i).toLinearMap)) hmap
    simpa [g, hplus] using htransport
  have hplus0 : i - 1 + 1 = i := Nat.sub_add_cancel hi
  have hg_secondid :
      (LinearMap.snd R (Fin (dRank (i - 1)) → R) (Fin (tRank (i - 1)) → R)).comp
          ((g (i - 1)).comp (LinearMap.inr R (Fin (dRank (i - 1 + 1)) → R)
            (Fin (tRank (i - 1 + 1)) → R))) =
        hplus0.symm ▸ tDiff (i - 1) := by
    ext x
    have hti : tRank (i - 1 + 1) = 1 := by
      rw [Nat.sub_add_cancel hi]
      simp [tRank]
    have htm : tRank (i - 1) = 1 := by simp [tRank, hprev_ne_i]
    rw [hti, htm] at x ⊢
    fin_cases x
    simp [g, coord, coordI, coordIm1, srcPre, tgtPre, ss, ts,
      sourceShear, targetShear, sp, tp, f0, f01, f10, dRank, tRank,
      hi_ne_prev, hprev_ne_i, Nat.sub_add_cancel hi, hc, hcv, hvc, c, v,
      pivotLinearEquiv,
      Fin.insertNth, Fin.removeNth, LinearEquiv.piCongrLeft,
      LinearEquiv.piCongrLeft', Equiv.piCongrLeft', Pi.single_apply] <;> ring
  let D : FiniteFreeComplex R length :=
    { termRank := dRank
      termRank_zero := by
        intro j hj
        have hz := C.termRank_zero j hj
        by_cases hji : j = i <;> by_cases hjp : j = i - 1 <;>
          simp [dRank, hji, hjp, hz] <;> omega
      differential := dDiff
      differential_zero := by
        intro j hj
        simp [dDiff, g, C.differential_zero j hj]
      differential_comp := by
        intro j
        sorry }
  let T : FiniteFreeComplex R length :=
    { termRank := tRank
      termRank_zero := by
        intro j hj
        by_cases hji : j = i <;> by_cases hjp : j = i - 1 <;>
          simp [tRank, hji, hjp] <;> omega
      differential := tDiff
      differential_zero := by
        intro j hj
        by_cases h : j = i - 1
        · subst j
          omega
        · simp [tDiff, h]
      differential_comp := by
        intro j
        by_cases h : j = i - 1
        · subst j
          have hne : i ≠ i - 1 := hi_ne_prev
          simp [tDiff, hne, Nat.sub_add_cancel hi]
        · simp [tDiff, h] }
  sorry

/-- Repeatedly removing unit coefficients leaves a representative whose
differentials have all coefficients in the maximal ideal, up to trivial
summands. -/
theorem local_reduction_to_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    {length : ℕ} (C : FiniteFreeComplex R length) :
    ∃ D : FiniteFreeComplex R length,
      D.MatrixEntriesInIdeal (IsLocalRing.maximalIdeal R) ∧
        IsomorphicUpToTrivialSummands C D := by
  sorry

/-! ## Depth-zero and Artinian local complexes -/

/-- In a local Noetherian ring, the maximal ideal is associated to `R` exactly
when the local depth of `R` is zero. -/
theorem maximalIdeal_mem_associatedPrimes_iff_localDepth_eq_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsLocalRing.maximalIdeal R ∈ _root_.associatedPrimes R R ↔
      Formalization.Books.Algebra.Unit72.localDepth R R = 0 := by
  rw [Formalization.Books.Algebra.Unit72.depth_eq_zero_iff]
  constructor
  · intro hm
    rcases subsingleton_or_nontrivial R with hsub | hnontr
    · exfalso
      have hprime : (IsLocalRing.maximalIdeal R).IsPrime :=
        (AssociatedPrimes.mem_iff.mp hm).isPrime
      apply hprime.ne_top
      ext x
      have hx : x = 0 := @Subsingleton.elim R hsub _ _
      simp [hx]
    · refine ⟨hnontr, ?_⟩
      intro hreg
      rcases hreg with ⟨x, hx, hxr⟩
      have hx' : x ∈ ((⋃ p ∈ _root_.associatedPrimes R R, (p : Set R)) : Set R) := by
        exact Set.mem_iUnion_of_mem (IsLocalRing.maximalIdeal R)
          (Set.mem_iUnion_of_mem hm hx)
      rw [biUnion_associatedPrimes_eq_compl_regular R R] at hx'
      exact hx' hxr
  · rintro ⟨hnontr, hno⟩
    have hmem_union :
        ((IsLocalRing.maximalIdeal R : Set R) ⊆
          ⋃ p ∈ _root_.associatedPrimes R R, (p : Set R)) ↔
          IsLocalRing.maximalIdeal R ∈ _root_.associatedPrimes R R := by
      apply (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
        (M := IsLocalRing.maximalIdeal R)
        (S := _root_.associatedPrimes R R)
        (_root_.associatedPrimes.finite R R) (⊥ : Ideal R) (⊥ : Ideal R)
        ?_ bot_ne_top bot_ne_top)
      intro I hI _ _
      exact (AssociatedPrimes.mem_iff.mp hI).isPrime
    apply hmem_union.mp
    rw [biUnion_associatedPrimes_eq_compl_regular R R]
    intro x hx
    have hxr : ¬ IsSMulRegular R x := by
      intro hxr
      exact hno ⟨x, hx, hxr⟩
    exact hxr

/-- An exact finite free complex over a local Noetherian ring of depth zero
is a direct sum of trivial complexes. -/
theorem lemma_exact_depth_zero_local
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {length : ℕ} (C : FiniteFreeComplex R length)
    (hmax : IsLocalRing.maximalIdeal R ∈ _root_.associatedPrimes R R)
    (hC : C.IsExact) :
    C.IsDirectSumOfTrivial := by
  sorry

/-- A local Artinian ring has depth zero. -/
theorem artinian_local_depth_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R] :
    Formalization.Books.Algebra.Unit72.localDepth R R = 0 := by
  rw [Formalization.Books.Algebra.Unit72.depth_eq_zero_iff]
  refine ⟨inferInstance, ?_⟩
  rintro ⟨f, hf, hreg⟩
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hmax : IsLocalRing.maximalIdeal R = Ideal.jacobson (⊥ : Ideal R) := by
    exact (Ideal.jacobson_bot.trans
      (IsLocalRing.ringJacobson_eq_maximalIdeal R)).symm
  have hfn : f ^ n = 0 := by
    have hmem : f ^ n ∈ (Ideal.jacobson (⊥ : Ideal R)) ^ n := by
      rw [← hmax]
      exact Ideal.pow_mem_pow hf n
    rw [hn] at hmem
    exact hmem
  have hnilpow : ∀ m : ℕ, f ^ m = 0 → False := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hzero : (1 : R) = 0 := by
          simpa only [pow_zero] using hm
        exact one_ne_zero hzero
    | succ m ih =>
        intro hm
        apply ih
        apply hreg.right_eq_zero_of_smul
        simpa [smul_eq_mul, pow_succ, mul_comm] using hm
  exact hnilpow n hfn

/-- An exact finite free complex over an Artinian local ring is a direct sum
of trivial complexes. -/
theorem lemma_exact_artinian_local
    {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {length : ℕ} (C : FiniteFreeComplex R length)
    (hC : C.IsExact) :
    C.IsDirectSumOfTrivial := by
  apply lemma_exact_depth_zero_local C ?_ hC
  exact (maximalIdeal_mem_associatedPrimes_iff_localDepth_eq_zero (R := R)).mpr
    artinian_local_depth_zero

/-! ## Rank and the ideal of maximal minors -/

/-- The source's rank: the largest exterior power on which a map is nonzero. -/
noncomputable def rank
    {R : Type u} [CommRing R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) : ℕ :=
  sSup {r : ℕ | exteriorPower.map r φ ≠ 0}

/-- The ideal generated by the maximal minors of a coordinate matrix. -/
noncomputable def rankIdeal
    {R : Type u} [CommRing R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) : Ideal R :=
  Ideal.span (Set.range fun p :
      (Fin (rank φ) ↪ Fin n) × (Fin (rank φ) ↪ Fin m) =>
    ((LinearMap.toMatrix' φ).submatrix p.1 p.2).det)

/-- The rank-zero assertion and the associated unit ideal at rank zero. -/
theorem rank_eq_zero_iff
    {R : Type u} [CommRing R] [Nontrivial R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    rank φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    have hbounded : BddAbove {r : ℕ | exteriorPower.map r φ ≠ 0} := by
      refine ⟨n, ?_⟩
      intro r hr
      by_contra hnr
      have hlt : n < r := Nat.lt_of_not_ge hnr
      have hfin : Module.finrank R (⋀[R]^r (Fin n → R)) = 0 := by
        rw [exteriorPower.finrank_eq, Module.finrank_fin_fun,
          Nat.choose_eq_zero_of_lt hlt]
      let : Subsingleton (⋀[R]^r (Fin n → R)) :=
        (Module.finrank_eq_zero_iff_of_free R _).mp hfin
      exact hr (Subsingleton.elim _ _)
    have hmap : exteriorPower.map 1 φ = 0 := by
      by_contra hne
      have hmem : 1 ∈ {r : ℕ | exteriorPower.map r φ ≠ 0} := hne
      have hle := le_csSup hbounded hmem
      change 1 ≤ rank φ at hle
      rw [h] at hle
      exact Nat.not_succ_le_zero 0 hle
    apply LinearMap.ext
    intro x
    have hn := exteriorPower.oneEquiv_naturality
      (R := R) (M := Fin m → R) (N := Fin n → R) φ
    have hx := congrArg
      (fun f => f ((exteriorPower.oneEquiv R (Fin m → R)).symm x)) hn
    rw [hmap] at hx
    simpa using hx.symm
  · intro h
    subst φ
    rw [rank]
    apply le_antisymm
    · apply csSup_le
      · refine ⟨0, ?_⟩
        intro hzero
        have hn := exteriorPower.zeroEquiv_naturality
          (R := R) (M := Fin m → R) (N := Fin n → R)
          (0 : (Fin m → R) →ₗ[R] (Fin n → R))
        rw [hzero] at hn
        have hone := congrArg
          (fun f : (⋀[R]^0 (Fin m → R)) →ₗ[R] R =>
            f (exteriorPower.ιMulti R 0 (fun _ => (0 : Fin m → R)))) hn
        simp at hone
      · intro r hr
        by_contra hpos
        have hrne : r ≠ 0 := by
          intro hr0
          apply hpos
          simp [hr0]
        have hrpos : 0 < r := Nat.pos_of_ne_zero hrne
        apply hr
        apply exteriorPower.linearMap_ext
        ext v
        cases r with
        | zero => simp at hrpos
        | succ r =>
          simp
    · exact Nat.zero_le _

theorem rankIdeal_eq_top_of_rank_eq_zero
    {R : Type u} [CommRing R] [Nontrivial R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hφ : rank φ = 0) :
    rankIdeal φ = ⊤ := by
  have hzero : φ = 0 := (rank_eq_zero_iff φ).mp hφ
  subst φ
  have h1 : (1 : R) ∈ rankIdeal (0 : (Fin m → R) →ₗ[R] (Fin n → R)) := by
    rw [rankIdeal]
    rw [hφ]
    apply Ideal.subset_span
    refine ⟨⟨⟨fun i => Fin.elim0 i, fun i j _ => Fin.elim0 i⟩,
      ⟨fun i => Fin.elim0 i, fun i j _ => Fin.elim0 i⟩⟩, ?_⟩
    simp [Matrix.det_fin_zero]
  apply le_antisymm
  · exact le_top
  · rw [← Ideal.span_univ]
    apply Ideal.span_le.2
    intro x hx
    change x ∈ rankIdeal (0 : (Fin m → R) →ₗ[R] (Fin n → R))
    simpa only [mul_one] using
      Ideal.mul_mem_left (rankIdeal (0 : (Fin m → R) →ₗ[R] (Fin n → R))) x h1

/-- The alternating sum occurring in the source's rank formula. -/
def alternatingRank
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (i : ℕ) : ℕ :=
    Int.toNat
      (Finset.sum (Finset.Icc i length)
        (fun j => (-1 : ℤ) ^ (j - i) * (C.termRank j : ℤ)))

/-- The rank formula in the Buchsbaum--Eisenbud criterion. -/
def BuchsbaumEisenbudRankCondition
    {R : Type u} [CommRing R] {length : ℕ}
  (C : FiniteFreeComplex R length) : Prop :=
  ∀ i, ∀ (hi : 1 ≤ i), i ≤ length →
    rank (C.previousDifferential i hi) = alternatingRank C i

/-- An ideal contains a regular sequence of the indicated length. -/
def ContainsRegularSequence
    {R : Type u} [CommRing R] (I : Ideal R) (length : ℕ) : Prop :=
  ∃ xs : List R,
    xs.length = length ∧
      (∀ x ∈ xs, x ∈ I) ∧
        RingTheory.Sequence.IsRegular R xs

/-- The grade/minors condition in the source's criterion. -/
def BuchsbaumEisenbudIdealCondition
    {R : Type u} [CommRing R] {length : ℕ}
  (C : FiniteFreeComplex R length) : Prop :=
  ∀ i, ∀ (hi : 1 ≤ i), i ≤ length →
    rankIdeal (C.previousDifferential i hi) = (⊤ : Ideal R) ∨
      ContainsRegularSequence (rankIdeal (C.previousDifferential i hi)) i

/-- The two conditions in the Buchsbaum--Eisenbud exactness criterion. -/
def BuchsbaumEisenbudConditions
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) : Prop :=
  BuchsbaumEisenbudRankCondition C ∧ BuchsbaumEisenbudIdealCondition C

/-- For a direct sum of trivial complexes, the ranks and maximal-minor ideals
have the values listed in the source. -/
theorem lemma_trivial_case_exact
    {R : Type u} [CommRing R] [Nontrivial R] {length : ℕ}
    (C : FiniteFreeComplex R length)
    (hC : C.IsDirectSumOfTrivial) :
      (BuchsbaumEisenbudRankCondition C) ∧
      (∀ i, ∀ (hi : 1 ≤ i), i < length →
        rank (C.differential i) + rank (C.previousDifferential i hi) =
          C.termRank i) ∧
      (∀ i, ∀ (hi : 1 ≤ i), i ≤ length →
        rankIdeal (C.previousDifferential i hi) = (⊤ : Ideal R)) := by
  sorry

/-! ## Quotienting by a nonzerodivisor -/

/-- Scalar extension of a coordinate linear map along a ring homomorphism. -/
noncomputable def mapCoordinateLinearMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (Fin m → S) →ₗ[S] (Fin n → S) :=
  Matrix.toLin' ((LinearMap.toMatrix' φ).map f)

/-- The differential of the complex after quotienting by `xR`. -/
noncomputable def quotientDifferential
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (x : R) (i : ℕ) :
    (Fin (C.termRank (i + 1)) → R ⧸ Ideal.span ({x} : Set R)) →ₗ[
      R ⧸ Ideal.span ({x} : Set R)]
        (Fin (C.termRank i) → R ⧸ Ideal.span ({x} : Set R)) :=
  mapCoordinateLinearMap (Ideal.Quotient.mk (Ideal.span ({x} : Set R)))
    (C.differential i)

/-- The quotient differential ending in a positive degree. -/
noncomputable def quotientPreviousDifferential
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (x : R) (i : ℕ) (hi : 0 < i) :
    (Fin (C.termRank i) → R ⧸ Ideal.span ({x} : Set R)) →ₗ[
      R ⧸ Ideal.span ({x} : Set R)]
        (Fin (C.termRank (i - 1)) → R ⧸ Ideal.span ({x} : Set R)) := by
  have h : i - 1 + 1 = i := Nat.sub_add_cancel hi
  exact h ▸ quotientDifferential C x (i - 1)

/-- The quotient differentials still form a complex. -/
theorem quotientDifferential_comp
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (x : R) (i : ℕ) :
    (quotientDifferential C x i).comp (quotientDifferential C x (i + 1)) = 0 := by
  sorry

/-- Exactness at a positive degree after quotienting by `xR`. -/
def IsExactAtAfterQuotient
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (x : R) (i : ℕ) : Prop :=
  if hi0 : i = 0 then
    True
  else if _hiL : i = length then
    length ≠ 0 ∧ Function.Injective
      (quotientPreviousDifferential C x i (Nat.pos_of_ne_zero hi0))
  else if _hi_lt : i < length then
    Function.Exact (quotientDifferential C x i)
      (quotientPreviousDifferential C x i (Nat.pos_of_ne_zero hi0))
  else
    True

/-- Quotienting an exact complex by a nonzerodivisor lowers the range of
degrees in which exactness is asserted by one. -/
theorem lemma_div_x_exact_one_less
    {R : Type u} [CommRing R] [IsLocalRing R]
    {length : ℕ} (C : FiniteFreeComplex R length)
    (hC : C.IsExact) (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : x ∈ nonZeroDivisors R) :
    ∀ i, 2 ≤ i → i ≤ length → IsExactAtAfterQuotient C x i := by
  sorry

/-! ## The acyclicity lemma -/

/-- A finite complex of finite modules, represented in the module category. -/
structure FiniteModuleComplex (R : Type u) [CommRing R] (length : ℕ) where
  term : ℕ → ModuleCat.{u} R
  term_finite : ∀ i, Module.Finite R (term i)
  differential : ∀ i, term (i + 1) ⟶ term i
  differential_zero : ∀ i, length ≤ i → differential i = 0
  differential_comp : ∀ i,
    (differential i).hom.comp (differential (i + 1)).hom = 0

/-- The differential ending in degree `i` for a finite module complex. -/
def FiniteModuleComplex.previousDifferential
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteModuleComplex R length) (i : ℕ) (hi : 0 < i) :
    (↑(C.term i)) →ₗ[R] (↑(C.term (i - 1))) := by
  have h : i - 1 + 1 = i := Nat.sub_add_cancel hi
  exact h ▸ (C.differential (i - 1)).hom

/-- Exactness at one degree of a finite module complex. -/
def FiniteModuleComplex.IsExactAt
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteModuleComplex R length) (i : ℕ) : Prop :=
  if hi0 : i = 0 then
    True
  else if _hiL : i = length then
    length ≠ 0 ∧ Function.Injective
      (C.previousDifferential i (Nat.pos_of_ne_zero hi0))
  else if _hi_lt : i < length then
    Function.Exact (C.differential i).hom
      (C.previousDifferential i (Nat.pos_of_ne_zero hi0))
  else
    True

/-- The local depth of a finite term. -/
noncomputable def FiniteModuleComplex.termDepth
    {R : Type u} [CommRing R] [IsLocalRing R] {length : ℕ}
    (C : FiniteModuleComplex R length) (i : ℕ) : ℕ∞ :=
  letI : Module.Finite R (C.term i) := C.term_finite i
  Formalization.Books.Algebra.Unit72.depth
    (IsLocalRing.maximalIdeal R) (C.term i)

/-- The kernel/image quotient at a positive term of a module complex. -/
noncomputable def FiniteModuleComplex.homologyModule
    {R : Type u} [CommRing R] {length : ℕ}
  (C : FiniteModuleComplex R length) (i : ℕ) (hi : 0 < i) : Type u :=
  let K : Submodule R (C.term i) := (C.previousDifferential i hi).ker
  K ⧸ (LinearMap.range (C.differential i).hom).comap K.subtype

/-- The local depth of the kernel/image quotient. -/
noncomputable def FiniteModuleComplex.homologyDepth
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {length : ℕ} (C : FiniteModuleComplex R length) (i : ℕ) (hi : 0 < i) : ℕ∞ :=
  letI : Module.Finite R (C.term i) := C.term_finite i
  let K : Submodule R (C.term i) :=
    (C.previousDifferential i hi).ker
  letI : IsNoetherian R (C.term i) := inferInstance
  letI : IsNoetherian R K :=
    isNoetherian_of_submodule_of_noetherian R (C.term i) K inferInstance
  letI : Module.Finite R K := inferInstance
  let L : Submodule R K :=
    (LinearMap.range (C.differential i).hom).comap K.subtype
  letI : Module.Finite R (K ⧸ L) := Module.Finite.quotient R L
  Formalization.Books.Algebra.Unit72.depth
    (IsLocalRing.maximalIdeal R) (K ⧸ L)

/-- **Acyclicity lemma.**  If the term depths dominate the indices, the
largest non-exact positive term has a kernel/image quotient of depth at least
one. -/
theorem lemma_acyclic
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {length : ℕ} (C : FiniteModuleComplex R length)
    (hdepth : ∀ j, C.termDepth j ≥ (j : ℕ∞))
    (i : ℕ) (hi : 0 < i) (hi' : i ≤ length)
    (hnot : ¬ C.IsExactAt i)
    (hmax : ∀ j, i < j → C.IsExactAt j) :
    C.homologyDepth i hi ≥ 1 := by
  sorry

/-! ## The Buchsbaum--Eisenbud criterion -/

/-- **What makes a complex exact?**  The source's rank and regular-sequence
conditions are equivalent to exactness of the finite free complex. -/
theorem proposition_what_exact
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {length : ℕ} (C : FiniteFreeComplex R length) :
    C.IsExact ↔ BuchsbaumEisenbudConditions C := by
  sorry

/-- If the equivalent conditions hold, the ideals of maximal minors become
the unit ideal at a threshold and remain the unit ideal afterwards. -/
theorem remark_what_exact
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {length : ℕ} (C : FiniteFreeComplex R length)
    (h : C.IsExact ∧ BuchsbaumEisenbudConditions C) :
    ∃ j : ℕ, ∀ i, ∀ (hi : 1 ≤ i), i ≤ length →
      (rankIdeal (C.previousDifferential i hi) = (⊤ : Ideal R) ↔ j ≤ i) := by
  sorry

end

end Formalization.Books.Algebra.Unit102
