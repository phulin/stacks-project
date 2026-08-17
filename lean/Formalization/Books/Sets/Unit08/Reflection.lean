import Formalization.Books.Sets.Unit05.Hierarchy
import Mathlib.ModelTheory.Semantics

/-!
# Set Theory, Chapter 8: Reflection principle

The source speaks about formulas of the first-order language of set theory.
Mathlib already supplies the locally nameless first-order syntax and its
semantics, so this file specializes that API to the relational language with
one binary membership symbol.  A formula with `n` free variables is written
with free variables indexed by `Fin n`.

The relativization of a formula has one additional free variable.  Index `0`
of that new context is the set being relativized to, and the old variable
`i` is sent to `i.succ`.  The recursive construction below inserts a
membership antecedent at every universal quantifier and a membership
conjunct at every existential quantifier (the latter is represented by
Mathlib's derived existential connective).  Thus the displayed formula
`φ^M` is an actual first-order formula, rather than an informal predicate
standing beside the syntax.

The source's warning that the metatheorem is awkward to use in ordinary
mathematics is accounted for by exposing both the actual relativized formula
and the semantic predicate `Reflects`; it is not an additional object-level
assertion.
-/

universe u

namespace Formalization.Books.Sets.Unit08

open FirstOrder
open FirstOrder.Language

/-! ### The first-order language of set theory -/

/-- The only nonlogical symbol in set theory is binary membership. -/
inductive SetTheoryRelation : ℕ → Type
  | membership : SetTheoryRelation 2
  deriving DecidableEq

/-- The relational first-order language with one binary membership relation. -/
def setTheoryLanguage : FirstOrder.Language :=
  ⟨fun _ => Empty, SetTheoryRelation⟩
  deriving FirstOrder.Language.IsRelational

/-- The membership relation symbol of `setTheoryLanguage`. -/
abbrev membershipRelation : setTheoryLanguage.Relations 2 := .membership

/-! ### The ambient set-theoretic structure -/

/-- Interpret the membership symbol on Mathlib's model of ZFC. -/
instance zfSetStructure : setTheoryLanguage.Structure (ZFSet.{u}) where
  RelMap | .membership => fun x => x 0 ∈ x 1

/-- Set-theoretic formulas with at most `n` designated free variables. -/
abbrev SetTheoryFormula (n : ℕ) := setTheoryLanguage.Formula (Fin n)

/-! ### Relativization -/

/-- Shift a term's free variables while leaving its in-scope bound variables fixed. -/
def shiftFreeTerm {n k : ℕ}
    (t : setTheoryLanguage.Term (Fin n ⊕ Fin k)) :
    setTheoryLanguage.Term (Fin (n + 1) ⊕ Fin k) :=
  t.relabel (Sum.map Fin.succ id)

/-- Relativize a bounded formula, with the set parameter inserted among its free variables. -/
def relativizeBounded (n : ℕ) :
    ∀ {k : ℕ}, setTheoryLanguage.BoundedFormula (Fin n) k →
      setTheoryLanguage.BoundedFormula (Fin (n + 1)) k
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (shiftFreeTerm t₁) (shiftFreeTerm t₂)
  | _, .rel R ts => .rel R (fun i => shiftFreeTerm (ts i))
  | _, .imp φ ψ => .imp (relativizeBounded n φ) (relativizeBounded n ψ)
  | k, .all φ =>
      .all
        (FirstOrder.Language.BoundedFormula.imp
          (membershipRelation.boundedFormula₂
            (Term.var (Sum.inr (Fin.last k)))
            (Term.var (Sum.inl (0 : Fin (n + 1)))))
          (relativizeBounded n φ))

/-- The source's formula `φ^M`, with `M` occupying free-variable index `0`. -/
def relativize {n : ℕ} (φ : SetTheoryFormula n) : SetTheoryFormula (n + 1) :=
  relativizeBounded n φ

/-! ### The displayed example -/

/-- The formula `∃ x (x ∈ x₁ ∧ x ∈ x₂)` from the source. -/
def commonElementFormula : SetTheoryFormula 2 :=
  (membershipRelation.boundedFormula₂
      (Term.var (Sum.inr 0)) (Term.var (Sum.inl 0)) ⊓
    membershipRelation.boundedFormula₂
      (Term.var (Sum.inr 0)) (Term.var (Sum.inl 1))).ex

theorem commonElementFormula_realize (x₁ x₂ : ZFSet.{u}) :
    commonElementFormula.Realize ![x₁, x₂] ↔
      ∃ x : ZFSet.{u}, x ∈ x₁ ∧ x ∈ x₂ := by
  simp only [FirstOrder.Language.Formula.Realize, commonElementFormula,
    FirstOrder.Language.BoundedFormula.realize_ex,
    FirstOrder.Language.BoundedFormula.realize_inf,
    FirstOrder.Language.BoundedFormula.realize_rel₂]
  change (∃ x : ZFSet.{u}, x ∈ x₁ ∧ x ∈ x₂) ↔ _
  rfl

theorem commonElementFormula_relativize_realize (M x₁ x₂ : ZFSet.{u}) :
    (relativize commonElementFormula).Realize ![M, x₁, x₂] ↔
      ∃ x ∈ M, x ∈ x₁ ∧ x ∈ x₂ := by
  dsimp [relativize, relativizeBounded, commonElementFormula,
    FirstOrder.Language.BoundedFormula.ex,
    FirstOrder.Language.BoundedFormula.not, Min.min,
    FirstOrder.Language.Relations.boundedFormula₂,
    FirstOrder.Language.Relations.boundedFormula,
    FirstOrder.Language.Formula.Realize,
    FirstOrder.Language.BoundedFormula.Realize]
  simp [shiftFreeTerm, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.Structure.RelMap, Fin.snoc_zero]

/-! ### Finite collections and reflection -/

/-- The conjunction of a finite list of formulas, with the empty conjunction true. -/
def conjunction {n : ℕ} (Φ : List (SetTheoryFormula n)) : SetTheoryFormula n :=
  Φ.foldr (· ⊓ ·) ⊤

theorem realize_conjunction {n : ℕ} (Φ : List (SetTheoryFormula n))
    (ρ : Fin n → ZFSet.{u}) :
    (conjunction Φ).Realize ρ ↔ ∀ φ ∈ Φ, φ.Realize ρ := by
  induction Φ with
  | nil => simp [conjunction]
  | cons φ Φ ih =>
      change (φ ⊓ conjunction Φ).Realize ρ ↔ _
      rw [FirstOrder.Language.Formula.realize_inf]
      constructor
      · rintro ⟨hφ, hΦ⟩ ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hφ
        · exact (ih.mp hΦ) ψ hψ
      · intro h
        refine ⟨h φ (by simp), ?_⟩
        exact ih.mpr (fun ψ hψ => h ψ (by simp [hψ]))

/-- A finite list of formulas is reflected in `M` when all its free-variable
instances in `M` agree with their relativizations to `M`. -/
def Reflects {n : ℕ} (M : ZFSet.{u}) (Φ : List (SetTheoryFormula n)) : Prop :=
  ∀ (ρ : Fin n → ZFSet.{u}),
    (∀ i, ρ i ∈ M) →
      ∀ φ ∈ Φ,
        φ.Realize ρ ↔ (relativize φ).Realize (Fin.cons M ρ)

/-- The reflection principle for a finite collection of set-theoretic formulas.

The witness is chosen as a von Neumann level indexed by a limit ordinal, as
in the strengthened form stated in the source. -/
theorem reflection_principle {n : ℕ} (Φ : List (SetTheoryFormula n))
    (M₀ : ZFSet.{u}) :
    ∃ α : Ordinal.{u},
      Order.IsSuccLimit α ∧
        M₀ ⊆ ZFSet.vonNeumann α ∧
          Reflects (ZFSet.vonNeumann α) Φ := by
  classical
  let w : ∀ (β : Ordinal.{u}) (q : Σ n : ℕ, Σ k : ℕ,
      setTheoryLanguage.BoundedFormula (Fin n) (k + 1) ×
        ((Fin n → {x : ZFSet.{u} // x ∈ ZFSet.vonNeumann β}) ×
          (Fin k → {x : ZFSet.{u} // x ∈ ZFSet.vonNeumann β}))), ZFSet.{u} := fun β q =>
    if h : (q.2.2.1.ex).Realize
        (fun i => (q.2.2.2.1 i).1)
        (fun i => (q.2.2.2.2 i).1) then
      Classical.choose ((FirstOrder.Language.BoundedFormula.realize_ex).mp h)
    else ∅
  let W : ∀ β : Ordinal.{u}, ZFSet.{u} := fun β =>
    ZFSet.range (w β)
  have hW_next : ∀ β : Ordinal.{u},
      W β ⊆ ZFSet.vonNeumann (max (β + 1) (ZFSet.rank (W β) + 1)) := by
    intro β y hy
    rw [ZFSet.mem_vonNeumann]
    exact (ZFSet.rank_lt_of_mem hy).trans
      (lt_max_of_lt_right (lt_add_one _))
  have hRangeLt :
      ∀ {α : Ordinal.{u}} (hα : Order.IsSuccLimit α) {m : ℕ}
        (f : Fin m → ZFSet.{u}),
        (∀ i, f i ∈ ZFSet.vonNeumann α) →
          ZFSet.rank (ZFSet.range f) < α := by
    intro α hα m
    induction m with
    | zero =>
        intro f hf
        have hr : ZFSet.range f = ∅ := by
          ext x
          simp
        rw [hr, ZFSet.rank_empty]
        exact hα.bot_lt
    | succ m ih =>
        intro f hf
        have hr : ZFSet.range f =
            insert (f 0) (ZFSet.range (fun i : Fin m => f i.succ)) := by
          ext x
          simp only [ZFSet.mem_range, ZFSet.mem_insert_iff]
          constructor
          · rintro ⟨i, rfl⟩
            refine Fin.cases (Or.inl rfl) ?_ i
            intro j
            exact Or.inr ⟨j, rfl⟩
          · rintro (rfl | ⟨i, rfl⟩)
            · exact ⟨0, rfl⟩
            · exact ⟨i.succ, rfl⟩
        rw [hr, ZFSet.rank_insert]
        apply max_lt
        · exact hα.succ_lt (ZFSet.mem_vonNeumann.mp (hf 0))
        · apply ih
          intro i
          exact hf i.succ
  let next : Ordinal.{u} → Ordinal.{u} :=
    fun β => max (β + 1) (ZFSet.rank (W β) + 1)
  let beta : ℕ → Ordinal.{u} :=
    fun j => Nat.rec (ZFSet.rank M₀ + 1) (fun _ b => next b) j
  let alpha : Ordinal.{u} := ⨆ j, beta j
  have hbeta_succ : ∀ j, beta j < beta (j + 1) := by
    intro j
    change beta j < max (beta j + 1) (ZFSet.rank (W (beta j)) + 1)
    exact lt_max_of_lt_left (lt_add_one _)
  have hbeta_le : ∀ j, beta j ≤ alpha := by
    intro j
    exact Ordinal.le_iSup beta j
  have hbeta_lt : ∀ j, beta j < alpha := by
    intro j
    exact (hbeta_succ j).trans_le (hbeta_le (j + 1))
  have halpha : Order.IsSuccLimit alpha := by
    rw [Ordinal.isSuccLimit_iff]
    refine ⟨?_, ?_⟩
    · have h0 : 0 < beta 0 := by
        simp [beta]
      exact ne_of_gt (h0.trans (hbeta_lt 0))
    · rw [Order.isSuccPrelimit_iff_succ_lt]
      intro γ hγ
      obtain ⟨j, hj⟩ := (Ordinal.lt_iSup_iff).mp hγ
      exact (Order.succ_le_of_lt hj).trans_lt (hbeta_lt j)
  have hW_stage : ∀ j, W (beta j) ⊆
      ZFSet.vonNeumann (beta (j + 1)) := by
    intro j
    simpa [beta, next] using hW_next (beta j)
  have hclosed :
      ∀ {n k : ℕ} (θ : setTheoryLanguage.BoundedFormula (Fin n) (k + 1))
        (ρ : Fin n → ZFSet.{u}) (xs : Fin k → ZFSet.{u}),
        (∀ i, ρ i ∈ ZFSet.vonNeumann alpha) →
        (∀ i, xs i ∈ ZFSet.vonNeumann alpha) →
        (θ.ex).Realize ρ xs →
        ∃ x, x ∈ ZFSet.vonNeumann alpha ∧
          θ.Realize ρ (Fin.snoc xs x) := by
    intro n k θ ρ xs hρ hxs hθ
    let f : Fin (n + k) → ZFSet.{u} := Fin.append ρ xs
    have hf : ∀ i, f i ∈ ZFSet.vonNeumann alpha := by
      intro i
      cases i using Fin.addCases with
      | left i => simp [f, Fin.append, hρ i]
      | right i => simp [f, Fin.append, hxs i]
    have hfrank : ZFSet.rank (ZFSet.range f) < alpha :=
      hRangeLt halpha f hf
    have hfrank' : ZFSet.rank (ZFSet.range f) < ⨆ j, beta j := by
      simpa [alpha] using hfrank
    obtain ⟨j, hj⟩ := (Ordinal.lt_iSup_iff).mp hfrank'
    have hρj : ∀ i, ρ i ∈ ZFSet.vonNeumann (beta j) := by
      intro i
      rw [ZFSet.mem_vonNeumann]
      have hi : ρ i ∈ ZFSet.range f := by
        rw [ZFSet.mem_range]
        exact ⟨Fin.castAdd k i, by simp [f]⟩
      exact (ZFSet.rank_lt_of_mem hi).trans hj
    have hxsj : ∀ i, xs i ∈ ZFSet.vonNeumann (beta j) := by
      intro i
      rw [ZFSet.mem_vonNeumann]
      have hi : xs i ∈ ZFSet.range f := by
        rw [ZFSet.mem_range]
        exact ⟨Fin.natAdd n i, by simp [f]⟩
      exact (ZFSet.rank_lt_of_mem hi).trans hj
    let q : Σ n : ℕ, Σ k : ℕ,
        setTheoryLanguage.BoundedFormula (Fin n) (k + 1) ×
          ((Fin n → {x : ZFSet.{u} // x ∈ ZFSet.vonNeumann (beta j)}) ×
            (Fin k → {x : ZFSet.{u} // x ∈ ZFSet.vonNeumann (beta j)})) :=
      ⟨n, k, θ, (fun i => ⟨ρ i, hρj i⟩), (fun i => ⟨xs i, hxsj i⟩)⟩
    have hq :
        (q.2.2.1.ex).Realize
            (fun i => (q.2.2.2.1 i).1)
            (fun i => (q.2.2.2.2 i).1) := by
      simpa [q] using hθ
    have hwq :
        (q.2.2.1).Realize
          (fun i => (q.2.2.2.1 i).1)
          (Fin.snoc (fun i => (q.2.2.2.2 i).1) (w (beta j) q)) := by
      dsimp [w]
      rw [dif_pos hq]
      exact Classical.choose_spec
        ((FirstOrder.Language.BoundedFormula.realize_ex).mp hq)
    refine ⟨w (beta j) q, ?_, ?_⟩
    · have hxstage : w (beta j) q ∈ ZFSet.vonNeumann (beta (j + 1)) := by
        apply hW_stage j
        change w (beta j) q ∈ ZFSet.range (w (beta j))
        exact ZFSet.mem_range_self q
      exact (ZFSet.vonNeumann_subset_of_le (hbeta_le (j + 1))) hxstage
    · simpa [q] using hwq
  have hshift : ∀ {n k : ℕ}
      (t : setTheoryLanguage.Term (Fin n ⊕ Fin k))
      (M : ZFSet.{u}) (ρ : Fin n → ZFSet.{u}) (xs : Fin k → ZFSet.{u}),
      (shiftFreeTerm t).realize (Sum.elim (Fin.cons M ρ) xs) =
        t.realize (Sum.elim ρ xs) := by
    intro n k t M ρ xs
    simp only [shiftFreeTerm, FirstOrder.Language.Term.realize_relabel]
    cases t with
    | var a =>
        rcases a with a | a <;> simp
    | func f ts =>
        exact isEmptyElim f
  have hSem :
      ∀ {n k : ℕ} (φ : setTheoryLanguage.BoundedFormula (Fin n) k)
        (M : ZFSet.{u}) (ρ : Fin n → ZFSet.{u}) (xs : Fin k → ZFSet.{u}),
        (∀ i, ρ i ∈ M) →
        (∀ i, xs i ∈ M) →
        (∀ {n k : ℕ}
          (θ : setTheoryLanguage.BoundedFormula (Fin n) (k + 1))
          (ρ : Fin n → ZFSet.{u}) (xs : Fin k → ZFSet.{u}),
          (∀ i, ρ i ∈ M) →
          (∀ i, xs i ∈ M) →
          (θ.ex).Realize ρ xs →
          ∃ x, x ∈ M ∧ θ.Realize ρ (Fin.snoc xs x)) →
        (φ.Realize ρ xs ↔
          (relativizeBounded n φ).Realize (Fin.cons M ρ) xs) := by
    intro n k φ
    induction φ with
    | falsum =>
        intro M ρ xs hρ hxs hclosed
        rfl
    | equal t₁ t₂ =>
        intro M ρ xs hρ hxs hclosed
        simp only [FirstOrder.Language.BoundedFormula.Realize, relativizeBounded,
          hshift t₁ M ρ xs, hshift t₂ M ρ xs]
    | rel R ts =>
        intro M ρ xs hρ hxs hclosed
        cases R with
        | membership =>
            simp only [FirstOrder.Language.BoundedFormula.Realize, relativizeBounded]
            simp only [hshift]
    | imp φ ψ ihφ ihψ =>
        intro M ρ xs hρ hxs hclosed
        simp only [FirstOrder.Language.BoundedFormula.Realize, relativizeBounded]
        rw [ihφ M ρ xs hρ hxs hclosed, ihψ M ρ xs hρ hxs hclosed]
    | all φ ih =>
        intro M ρ xs hρ hxs hclosed
        simp only [FirstOrder.Language.BoundedFormula.Realize, relativizeBounded]
        simp only [FirstOrder.Language.BoundedFormula.realize_rel₂,
          FirstOrder.Language.Term.realize_var,
          FirstOrder.Language.Structure.RelMap,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        simp only [Sum.elim_inr, Sum.elim_inl, Fin.snoc_last, Fin.cons_zero]
        constructor
        · intro h x hx
          exact (ih M ρ (Fin.snoc xs x) hρ
            (by
              intro i
              refine Fin.lastCases ?_ (fun i => by simpa using hxs i) i
              simpa using hx)
            hclosed).mp (h x)
        · intro h x
          classical
          by_contra hnot
          have hex : (φ.not.ex).Realize ρ xs := by
            simp only [FirstOrder.Language.BoundedFormula.realize_ex,
              FirstOrder.Language.BoundedFormula.realize_not]
            exact ⟨x, hnot⟩
          obtain ⟨y, hy, hyfalse⟩ :=
            hclosed (θ := φ.not) ρ xs hρ hxs hex
          exact hyfalse ((ih M ρ (Fin.snoc xs y) hρ
            (by
              intro i
              refine Fin.lastCases ?_ (fun i => by simpa using hxs i) i
              simpa using hy)
            hclosed).mpr (h y hy))
  have hM0 : M₀ ⊆ ZFSet.vonNeumann alpha := by
    exact (ZFSet.subset_vonNeumann_self M₀).trans
      (ZFSet.vonNeumann_subset_of_le (by
        exact ((by simp [beta]) : ZFSet.rank M₀ ≤ beta 0).trans (hbeta_le 0)))
  refine ⟨alpha, halpha, hM0, ?_⟩
  unfold Reflects
  intro ρ hρ φ hφ
  let xs : Fin 0 → ZFSet.{u} := Fin.elim0
  have hxs : ∀ i, xs i ∈ ZFSet.vonNeumann alpha := by
    intro i
    exact Fin.elim0 i
  have htop := hSem φ (ZFSet.vonNeumann alpha) ρ xs hρ hxs hclosed
  have hxeq : xs = (default : Fin 0 → ZFSet.{u}) := Subsingleton.elim _ _
  rw [hxeq] at htop
  unfold relativize FirstOrder.Language.Formula.Realize
  have hdefault :
      (@default (Fin 0 → ZFSet.{u}) Unique.instInhabited) =
        (@default (Fin 0 → ZFSet.{u}) Pi.instInhabited) :=
    Subsingleton.elim _ _
  rw [hdefault]
  exact htop

/-! ### The finite-list reformulation -/

/-- The conjunction form of the reflection principle, phrased with an
arbitrary reflected set as in the source's meta-theorem reformulation. -/
theorem reflection_principle_meta {n : ℕ}
    (Φ : List (SetTheoryFormula n)) :
    ∀ M₀ : ZFSet.{u},
      ∃ M : ZFSet.{u},
        M₀ ⊆ M ∧
          ∀ (ρ : Fin n → ZFSet.{u}),
            (∀ i, ρ i ∈ M) →
              (conjunction Φ).Realize ρ ↔
                (conjunction (Φ.map (fun φ => relativize φ))).Realize
                  (Fin.cons M ρ) := by
  sorry

end Formalization.Books.Sets.Unit08
