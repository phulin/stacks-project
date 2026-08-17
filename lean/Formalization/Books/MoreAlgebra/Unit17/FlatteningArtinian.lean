import Formalization.Books.MoreAlgebra.Unit16.FlatteningStratification
import Formalization.Books.Algebra.Unit101.FlatnessCriteriaArtinian
import Mathlib.RingTheory.Ideal.Maps

/-!
# More on Algebra, Chapter 17: Flattening over an Artinian ring

The source's quotient `M / IM` is represented by the canonical quotient module
`M ⧸ (I • ⊤)`, and the condition `φ(I) = 0` is represented by
`I.map φ = ⊥`.
-/

namespace Formalization.Books.MoreAlgebra.Unit17

open scoped TensorProduct

noncomputable section

/-! ## Flattening over an Artinian ring -/

/- The opening discussion is accounted for by the stronger result below for
   every Artinian ring and every module.  The final scheme-theoretic
   consequence, concerning a base that is the spectrum of an Artinian local
   ring, is a roadmap to the later flattening-stratification sections rather
   than a separate algebraic declaration in this section. -/

/-- The ideals whose quotient makes `M` flat over the corresponding quotient
ring. -/
def flatQuotientIdeals
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] : Set (Ideal R) :=
  {I | Module.Flat (R ⧸ I)
    (M ⧸ (I • (⊤ : Submodule R M)))}

/-- The least ideal in `flatQuotientIdeals`, once existence is known. -/
def flatteningIdeal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] : Ideal R :=
  sInf (flatQuotientIdeals (R := R) (M := M))

/-- A base change of `M` along `φ` is flat over its target ring. -/
def IsFlatAfterBaseChange
    {R R' M : Type*} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] (φ : R →+* R') : Prop :=
  letI : Algebra R R' := φ.toAlgebra
  Module.Flat R' (R' ⊗[R] M)

/- The proof of the source lemma uses the preceding intersection lemma to show
   that the relevant set of ideals is closed under intersections, together
   with the Artinian minimum principle. -/

/-- Over an Artinian ring, there is a smallest ideal whose quotient makes the
module flat over the quotient ring. -/
theorem exists_isLeast_flatQuotientIdeal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] :
    ∃ I : Ideal R, IsLeast (flatQuotientIdeals (R := R) (M := M)) I := by
  sorry

/-- The canonical infimum construction is the smallest flatness ideal over an
Artinian ring. -/
theorem flatteningIdeal_isLeast
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] :
    IsLeast (flatQuotientIdeals (R := R) (M := M))
      (flatteningIdeal (R := R) (M := M)) := by
  sorry

/- The forward implication in the source is flatness after base change; the
   reverse implication uses the kernel quotient and the Artinian descent
   theorem `descent_flatness_injective_map_artinian_rings`. -/

/-- The smallest flatness ideal is characterized by the universal property of
the flattening over every ring map out of the Artinian base. -/
theorem flatteningIdeal_universal_property
    {R R' M : Type*} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] [IsArtinianRing R]
    (I : Ideal R)
    (hI : IsLeast (flatQuotientIdeals (R := R) (M := M)) I)
    (φ : R →+* R') :
    IsFlatAfterBaseChange (M := M) φ ↔ I.map φ = ⊥ := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit17
