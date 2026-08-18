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
  apply le_antisymm le_top
  apply Submodule.le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot
    (N := (⊤ : Submodule A M))
    (N' := Submodule.span A (Set.range x))
    Module.Finite.fg_top
    (by simpa only [Ideal.jacobson_bot] using hI)
  have hmap :
      Submodule.map (I • (⊤ : Submodule A M)).mkQ
        (Submodule.span A (Set.range x)) = ⊤ := by
    rw [Submodule.map_span]
    have hset :
        (I • (⊤ : Submodule A M)).mkQ '' Set.range x =
          Set.range (fun i => (I • (⊤ : Submodule A M)).mkQ (x i)) := by
      ext z
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
    rw [hset]
    exact hx
  rw [hmap]
  exact le_top

end Formalization.Books.Exercises.Unit08
