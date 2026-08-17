import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Exercises, Chapter 5: Flat ring maps

This file records the residue-field extension exercise.  The source's field
`k` is represented by Mathlib's canonical residue field
`IsLocalRing.ResidueField A`, so the final equivalence is explicitly an
equivalence of residue-field algebras.
-/

universe u v w

namespace Formalization.Books.Exercises.Unit05

/-! ## Flat local maps with prescribed residue field -/

/-- A flat local `A`-algebra whose residue field is the prescribed extension
`K` of the residue field of `A`. -/
def IsFlatLocalResidueFieldExtension
    {A : Type u} {B : Type v} {K : Type w}
    [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [Field K] [Algebra (A ⧸ IsLocalRing.maximalIdeal A) K] : Prop :=
  IsLocalHom (algebraMap A B) ∧
    Module.Flat A B ∧
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal B ∧
        Nonempty
          ((B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))
            ≃ₐ[A ⧸ IsLocalRing.maximalIdeal A] K)

/-- A finite residue-field extension is realized by a flat local map with the
prescribed residue field. -/
theorem exists_flat_local_residueField_extension
    {A : Type u} [CommRing A] [IsLocalRing A]
    {K : Type v} [Field K]
    [Algebra (A ⧸ IsLocalRing.maximalIdeal A) K]
    [Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) K] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : IsLocalRing B)
      (_ : Algebra A B),
      IsFlatLocalResidueFieldExtension (A := A) (B := B) (K := K) := by
  sorry

/-- The same construction exists without a finiteness hypothesis on the field
extension. -/
theorem exists_flat_local_residueField_extension_of_arbitrary
    {A : Type u} [CommRing A] [IsLocalRing A]
    {K : Type v} [Field K]
    [Algebra (A ⧸ IsLocalRing.maximalIdeal A) K] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : IsLocalRing B)
      (_ : Algebra A B),
      IsFlatLocalResidueFieldExtension (A := A) (B := B) (K := K) := by
  sorry

end Formalization.Books.Exercises.Unit05
