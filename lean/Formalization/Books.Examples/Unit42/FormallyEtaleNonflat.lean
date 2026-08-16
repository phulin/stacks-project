import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Examples, Chapter 42: A formally étale non-flat ring map

This file records the quotient construction, the square-zero lifting
interface, and the existence statement from the source section.  The
proposition proofs belong to the proving stage.
-/

namespace Formalization.«Books.Examples».Unit42

universe u

/-! ## The local-ring quotient setup -/

/-- A nonzero proper ideal whose square is itself. -/
def NonzeroProperIdempotentIdeal (A : Type u) [CommRing A] (J : Ideal A) : Prop :=
  J ≠ ⊥ ∧ J ≠ ⊤ ∧ J ^ 2 = J

/-- A nonzero proper idempotent ideal in a local ring is not finitely generated. -/
theorem nonzeroProperIdempotentIdeal_not_finitelyGenerated
    (A : Type u) [CommRing A] [IsLocalRing A] (J : Ideal A)
    (hJ : NonzeroProperIdempotentIdeal A J) :
    ¬ J.FG := by
  sorry

/-! ## The quotient map -/

/-- The quotient map associated to the ideal in the example. -/
def quotientByIdealMap {A : Type u} [CommRing A] (J : Ideal A) :
    A →+* A ⧸ J :=
  Ideal.Quotient.mk J

/-- A quotient map is of finite type because it is surjective. -/
theorem quotientByIdealMap_finiteType
    (A : Type u) [CommRing A] (J : Ideal A) :
    RingHom.FiniteType (quotientByIdealMap J) := by
  exact RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective

/-- A quotient by a non-finitely-generated ideal is not finitely presented. -/
theorem quotientByIdealMap_not_finitePresentation_of_not_finitelyGenerated
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : ¬ J.FG) :
    ¬ RingHom.FinitePresentation (quotientByIdealMap J) := by
  sorry

/-- The quotient in the example is finite type but not finitely presented. -/
theorem quotientByIdealMap_finiteType_not_finitePresentation_of_nonzeroProperIdempotentIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] (J : Ideal A)
    (hJ : NonzeroProperIdempotentIdeal A J) :
    RingHom.FiniteType (quotientByIdealMap J) ∧
      ¬ RingHom.FinitePresentation (quotientByIdealMap J) := by
  exact ⟨quotientByIdealMap_finiteType A J,
    quotientByIdealMap_not_finitePresentation_of_not_finitelyGenerated A J
      (nonzeroProperIdempotentIdeal_not_finitelyGenerated A J hJ)⟩

/-- The quotient map by an idempotent ideal is formally étale. -/
theorem quotientByIdealMap_formallyEtale_of_idempotent
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : J ^ 2 = J) :
    RingHom.FormallyEtale (quotientByIdealMap J) := by
  sorry

/-- The quotient map by a nonzero proper idempotent ideal in a local ring is not flat. -/
theorem quotientByIdealMap_not_flat_of_nonzeroProperIdempotentIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] (J : Ideal A)
    (hJ : NonzeroProperIdempotentIdeal A J) :
    ¬ RingHom.Flat (quotientByIdealMap J) := by
  sorry

/-- The displayed quotient map is formally étale but non-flat. -/
theorem quotientByIdealMap_formallyEtale_not_flat
    (A : Type u) [CommRing A] [IsLocalRing A] (J : Ideal A)
    (hJ : NonzeroProperIdempotentIdeal A J) :
    RingHom.FormallyEtale (quotientByIdealMap J) ∧
      ¬ RingHom.Flat (quotientByIdealMap J) := by
  exact ⟨quotientByIdealMap_formallyEtale_of_idempotent A J hJ.2.2,
    quotientByIdealMap_not_flat_of_nonzeroProperIdempotentIdeal A J hJ⟩

/-! ## Factoring through the quotient in a square-zero diagram -/

/-- The unique map induced by a ring homomorphism annihilating an ideal. -/
def quotientFactor {A R : Type*} [CommRing A] [CommRing R] (J : Ideal A)
    (φ : A →+* R) (hφ : J ≤ RingHom.ker φ) : A ⧸ J →+* R :=
  Ideal.Quotient.lift J φ (fun _a ha => hφ ha)

@[simp]
theorem quotientFactor_comp_quotientByIdealMap
    {A R : Type*} [CommRing A] [CommRing R] (J : Ideal A)
    (φ : A →+* R) (hφ : J ≤ RingHom.ker φ) :
    (quotientFactor J φ hφ).comp (quotientByIdealMap J) = φ := by
  rfl

/-- In the source diagram, the image of `J` in `R` is zero.

This is the ideal-theoretic form of the displayed chain
`φ(J) = φ(J²) ⊆ (Ideal.map φ J)² ⊆ I² = 0`.
-/
theorem quotientDiagram_mapIdeal_eq_bot
    {A R : Type*} [CommRing A] [CommRing R] (J : Ideal A)
    (hJ : J ^ 2 = J) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (φ : A →+* R) (ψ : A ⧸ J →+* R ⧸ I)
    (hcomm : ψ.comp (quotientByIdealMap J) = (Ideal.Quotient.mk I).comp φ) :
    Ideal.map φ J = ⊥ := by
  sorry

/-- The map `A → R` in a square-zero diagram factors uniquely through `A ⧸ J`. -/
theorem quotientDiagram_factorization_unique
    {A R : Type*} [CommRing A] [CommRing R] (J : Ideal A)
    (hJ : J ^ 2 = J) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (φ : A →+* R) (ψ : A ⧸ J →+* R ⧸ I)
    (hcomm : ψ.comp (quotientByIdealMap J) = (Ideal.Quotient.mk I).comp φ) :
    ∃! f : A ⧸ J →+* R, f.comp (quotientByIdealMap J) = φ := by
  sorry

/-! ## The existence statement -/

/-- There is a local ring with a nonzero proper idempotent ideal. -/
theorem exists_localRing_nonzeroProperIdempotentIdeal :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (J : Ideal A),
      NonzeroProperIdempotentIdeal A J := by
  sorry

/-- There exist formally étale non-flat quotient ring maps. -/
theorem exists_formallyEtale_nonflat_quotient_map :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (J : Ideal A),
      NonzeroProperIdempotentIdeal A J ∧
        RingHom.FormallyEtale (quotientByIdealMap J) ∧
          ¬ RingHom.Flat (quotientByIdealMap J) := by
  sorry

/-- There exist formally étale non-flat ring maps. -/
theorem exists_formallyEtale_nonflat_ring_map :
    ∃ (A B : Type) (_ : CommRing A) (_ : CommRing B) (f : A →+* B),
      RingHom.FormallyEtale f ∧ ¬ RingHom.Flat f := by
  sorry

end Formalization.«Books.Examples».Unit42
