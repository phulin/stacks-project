import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeCompare

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section

/-! ## Base change -/

/-- The degreewise isomorphism of de Rham complexes after arbitrary base
change. -/
noncomputable def deRhamBaseChangeIso
    {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] :
    ∀ p : ℕ,
      deRhamBaseChangeTerm A A' B p ≃ₗ[A']
        deRhamTerm A' (deRhamBaseChangeRing A A' B) p :=
  deRhamBaseChangeRawEquiv (A := A) (A' := A') (B := B)

theorem deRhamBaseChangeIso_commutes
    {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B]
    (p : ℕ) (x : deRhamBaseChangeTerm A A' B p) :
    deRhamBaseChangeIso (A := A) (A' := A') (B := B) (p + 1)
        (deRhamBaseChangeDifferential (A := A) (A' := A') (B := B) p x) =
      deRhamDifferential (A := A')
        (B := deRhamBaseChangeRing A A' B) p
        (deRhamBaseChangeIso (A := A) (A' := A') (B := B) p x) := by
  exact deRhamBaseChangeRawEquiv_commutes
    (A := A) (A' := A') (B := B) p x

theorem deRhamBaseChangeIso_exists
    {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] :
    Nonempty
      {e : ∀ p : ℕ,
          deRhamBaseChangeTerm A A' B p ≃ₗ[A']
            deRhamTerm A' (deRhamBaseChangeRing A A' B) p //
        ∀ (p : ℕ) (x : deRhamBaseChangeTerm A A' B p),
          e (p + 1)
              (deRhamBaseChangeDifferential (A := A) (A' := A') (B := B) p x) =
            deRhamDifferential (A := A')
              (B := deRhamBaseChangeRing A A' B) p (e p x)} :=
  ⟨⟨deRhamBaseChangeIso (A := A) (A' := A') (B := B),
    deRhamBaseChangeIso_commutes (A := A) (A' := A') (B := B)⟩⟩

end
end Formalization.Books.Algebra.Unit132
