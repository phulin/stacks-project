import Formalization.Books.Algebra.Unit71
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exercises, Chapter 11: Ext over a regular ring

The source uses `k[x,y]` and identifies `k` with the residue ring at the
origin.  The latter is represented by the canonical ideal quotient; the
evaluation map and the quotient-to-`k` identification are recorded
separately so that the exact sequence uses Mathlib's standard module object.
-/

namespace Formalization.Books.Exercises.Unit11

open CategoryTheory
open Formalization.Books.Algebra.Unit71
open scoped ZeroObject

universe u

noncomputable section

/-! ## The polynomial ring and its residue field at the origin -/

abbrev twoVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

def originIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
      Set (twoVariablePolynomialRing k))

/-- Evaluation at `(0, 0)`, the last nonzero map in the displayed complex. -/
def originEvaluationAtZero (k : Type u) [Field k] :
    twoVariablePolynomialRing k →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : Fin 2 => 0)

/-- The canonical residue ring `k[x,y]/(x,y)`, used as an `R`-module. -/
abbrev originResidueRing (k : Type u) [Field k] :=
  twoVariablePolynomialRing k ⧸ originIdeal k

abbrev originResidueModule (k : Type u) [Field k] :
    ModuleCat (twoVariablePolynomialRing k) :=
  ModuleCat.of (twoVariablePolynomialRing k) (originResidueRing k)

/-- The quotient model of the source's coefficient field is canonically `k`. -/
theorem origin_residue_ring_isomorphic_to_field (k : Type u) [Field k] :
    Nonempty (originResidueRing k ≃+* k) := by
  sorry

/-! ## The displayed Koszul complex -/

/-- The column map `f ↦ (y f, -x f)`. -/
def koszulFirstDifferential (k : Type u) [Field k] :
    twoVariablePolynomialRing k →ₗ[twoVariablePolynomialRing k]
      twoVariablePolynomialRing k × twoVariablePolynomialRing k :=
  (LinearMap.mulLeft (twoVariablePolynomialRing k)
      (MvPolynomial.X (1 : Fin 2))).prod
    (LinearMap.mulLeft (twoVariablePolynomialRing k)
      (-MvPolynomial.X (0 : Fin 2)))

/-- The row map `(x, y)`. -/
def koszulSecondDifferential (k : Type u) [Field k] :
    (twoVariablePolynomialRing k × twoVariablePolynomialRing k) →ₗ[
      twoVariablePolynomialRing k] twoVariablePolynomialRing k :=
  (LinearMap.mulLeft (twoVariablePolynomialRing k)
      (MvPolynomial.X (0 : Fin 2))).comp
      (LinearMap.fst (twoVariablePolynomialRing k)
        (twoVariablePolynomialRing k) (twoVariablePolynomialRing k)) +
    (LinearMap.mulLeft (twoVariablePolynomialRing k)
      (MvPolynomial.X (1 : Fin 2))).comp
      (LinearMap.snd (twoVariablePolynomialRing k)
        (twoVariablePolynomialRing k) (twoVariablePolynomialRing k))

/-- The quotient map `R → R/(x,y)`, corresponding to evaluation at the origin. -/
def koszulAugmentation (k : Type u) [Field k] :
    twoVariablePolynomialRing k →ₗ[twoVariablePolynomialRing k]
      originResidueRing k :=
  (Ideal.Quotient.mkₐ (twoVariablePolynomialRing k) (originIdeal k)).toLinearMap

/-- The six objects and five arrows in the source's Koszul complex. -/
def koszulComplex (k : Type u) [Field k] :
    ComposableArrows (ModuleCat (twoVariablePolynomialRing k)) 5 :=
  ComposableArrows.mk₅
    (0 : (0 : ModuleCat (twoVariablePolynomialRing k)) ⟶
      ModuleCat.of (twoVariablePolynomialRing k) (twoVariablePolynomialRing k))
    (ModuleCat.ofHom (koszulFirstDifferential k))
    (ModuleCat.ofHom (koszulSecondDifferential k))
    (ModuleCat.ofHom (koszulAugmentation k))
    (0 : originResidueModule k ⟶ (0 : ModuleCat (twoVariablePolynomialRing k)))

/-- The displayed Koszul complex is exact. -/
theorem koszulComplex_exact (k : Type u) [Field k] :
    (koszulComplex k).Exact := by
  sorry

/-! ## The Ext computation -/

/-- For `R = k[x,y]` and `k = R/(x,y)`, the Ext groups are `k`, `k²`,
`k`, and zero in degrees `0`, `1`, `2`, and at least `3`, respectively. -/
theorem regular_ring_ext_computation (k : Type u) [Field k] :
    Nonempty (ExtGroup (originResidueModule k) (originResidueModule k) 0 ≃+ k) ∧
      Nonempty (ExtGroup (originResidueModule k) (originResidueModule k) 1 ≃+
        (k × k)) ∧
      Nonempty (ExtGroup (originResidueModule k) (originResidueModule k) 2 ≃+ k) ∧
      ∀ i : ℕ, 3 ≤ i →
        Nonempty (ExtGroup (originResidueModule k) (originResidueModule k) i ≃+
          (Fin 0 → k)) := by
  sorry

end

end Formalization.Books.Exercises.Unit11
