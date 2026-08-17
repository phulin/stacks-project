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
  sorry

theorem commonElementFormula_relativize_realize (M x₁ x₂ : ZFSet.{u}) :
    (relativize commonElementFormula).Realize ![M, x₁, x₂] ↔
      ∃ x ∈ M, x ∈ x₁ ∧ x ∈ x₂ := by
  sorry

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
  sorry

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
