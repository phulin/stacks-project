import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exercises, Chapter 63: Ideals

The quotient ring and its six ideals are kept explicit. The classification
theorem below records that this named finite set is the complete list.
-/

namespace Formalization.Books.Exercises.Unit63

open Set

universe u

noncomputable section

abbrev IdealsExamPolynomialRing := MvPolynomial (Fin 2) (ZMod 2)

def idealsExamRelationIdeal : Ideal IdealsExamPolynomialRing :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2) ^ 2,
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2),
      MvPolynomial.X (1 : Fin 2) ^ 2} : Set IdealsExamPolynomialRing)

/-- The ring `𝔽₂[x,y]/(x²,xy,y²)`. -/
abbrev IdealsExamRing :=
  IdealsExamPolynomialRing ⧸ idealsExamRelationIdeal

/-- The images of `x` and `y` in the quotient ring. -/
def idealsExamX : IdealsExamRing :=
  Ideal.Quotient.mk idealsExamRelationIdeal (MvPolynomial.X (0 : Fin 2))

def idealsExamY : IdealsExamRing :=
  Ideal.Quotient.mk idealsExamRelationIdeal (MvPolynomial.X (1 : Fin 2))

def idealsExamIdealList : Set (Ideal IdealsExamRing) :=
  {⊥,
    Ideal.span ({idealsExamX} : Set IdealsExamRing),
    Ideal.span ({idealsExamY} : Set IdealsExamRing),
    Ideal.span ({idealsExamX + idealsExamY} : Set IdealsExamRing),
    Ideal.span ({idealsExamX, idealsExamY} : Set IdealsExamRing),
    ⊤}

/-- Every ideal of the exam ring is one of the six displayed ideals. -/
theorem idealsExam_ideal_mem_list (I : Ideal IdealsExamRing) :
    I ∈ idealsExamIdealList := by
  sorry

/-- The displayed set is exactly the set of all ideals of the exam ring. -/
theorem idealsExam_complete_ideal_list :
    (Set.univ : Set (Ideal IdealsExamRing)) = idealsExamIdealList := by
  ext I
  constructor
  · intro
    exact idealsExam_ideal_mem_list I
  · intro
    trivial

end

end Formalization.Books.Exercises.Unit63
