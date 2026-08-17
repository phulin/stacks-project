import Mathlib.RingTheory.Nakayama

/-!
# Exercises, Chapter 8: Nakayama's Lemma

The source exercise is expressed using Mathlib's canonical finitely generated
module, ideal action on a submodule, quotient map, and Jacobson radical APIs.
-/

noncomputable section

universe u v

namespace Formalization.Books.Exercises.Unit08

/-! ## Nakayama's lemma for a finite generating family -/

/-- If a finite family generates `M / IM` and `I` is contained in the
Jacobson radical of `A`, then it generates `M`. -/
theorem generators_of_quotient_generators
    {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) (x : Fin n → M)
    [Module.Finite A M]
    (hx : Submodule.span A
      (Set.range (fun i => (I • (⊤ : Submodule A M)).mkQ (x i))) = ⊤)
    (hI : I ≤ Ring.jacobson A) :
    Submodule.span A (Set.range x) = ⊤ := by
  sorry

end Formalization.Books.Exercises.Unit08
