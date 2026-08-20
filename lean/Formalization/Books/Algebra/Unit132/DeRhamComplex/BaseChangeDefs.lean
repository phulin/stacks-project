import Formalization.Books.Algebra.Unit132.DeRhamComplex.Core

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open scoped TensorProduct

noncomputable section

/-- Mathlib's tensor-product convention for the source's `B ⊗[A] A'` is
`A' ⊗[A] B`. -/
abbrev deRhamBaseChangeRing (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A B] :=
  A' ⊗[A] B

abbrev deRhamBaseChangeTerm
    (A A' B : Type*) [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] (p : ℕ) :=
  A' ⊗[A] deRhamTerm A B p

/-- The differential obtained by tensoring a de Rham differential with the
base-change algebra. -/
noncomputable def deRhamBaseChangeDifferential
    {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] (p : ℕ) :
    deRhamBaseChangeTerm A A' B p →ₗ[A'] deRhamBaseChangeTerm A A' B (p + 1) :=
  (TensorProduct.AlgebraTensorModule.lTensor (R := A) A' A')
    (deRhamDifferential (A := A) (B := B) p)

end
end Formalization.Books.Algebra.Unit132
