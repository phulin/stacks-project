import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.Flat
import Formalization.Books.Algebra.Unit147.IntegralClosureSmoothBaseChange
import Formalization.Books.Smoothing.Unit03

/-!
# Smoothing Ring Maps, Chapter 5: The lifting problem

The source proves that filtered colimits of smooth algebras are stable under
nilpotent flat deformations.  The factorization data below records the two
lifting lemmas in a form that can be used by the later lifting-lemma chapter;
the filtered-colimit notion itself is the established interface from Algebra
Chapter 147.
-/

namespace Formalization.Books.Smoothing.Unit05

open Formalization.Books.Algebra.Unit147

noncomputable section

universe u

/-! ## Quotients of the base and target -/

/- The ideal denoted `IΛ` in the source. -/
abbrev extendedIdeal
    {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) : Ideal Λ :=
  Ideal.map (algebraMap R Λ) I

/- The quotient algebra `Λ / IΛ` over `R / I` used throughout the section. -/
abbrev infinitesimalTarget
    {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) : Type u :=
  Λ ⧸ extendedIdeal I

noncomputable instance infinitesimalTarget.algebraQuotient
    {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) : Algebra (R ⧸ I) (infinitesimalTarget (Λ := Λ) I) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (R := R) (A := Λ) (p := I) (P := extendedIdeal (Λ := Λ) I) Ideal.le_comap_map

/-! ## The first lifting lemma -/

/-- The factorization `A → B/J → Λ` from the once-lifting lemma, including
the smoothness, containment, and finite-generation properties of `J`. -/
structure LiftOnceFactorization
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ]
    (I : Ideal R) (φ : A →ₐ[R] Λ) where
  B : Type u
  [commRingB : CommRing B]
  [algebraRB : Algebra R B]
  smoothB : Algebra.Smooth R B
  J : Ideal B
  J_le : J ≤ Ideal.map (algebraMap R B) I
  J_fg : J.FG
  factor : A →ₐ[R] (B ⧸ J)
  target : (B ⧸ J) →ₐ[R] Λ
  factorization : target.comp factor = φ

/-- If `I² = 0` and the reduction of `Λ` is a filtered colimit of smooth
`R/I`-algebras, every finitely presented map into `Λ` factors through a smooth
algebra modulo a finitely generated ideal inside `I`. -/
theorem lift_once
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ]
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hquot : Nonempty (FilteredSmoothAlgebraColimit
      (R ⧸ I) (infinitesimalTarget (Λ := Λ) I)))
    [Algebra.FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    Nonempty (LiftOnceFactorization I φ) := by
  sorry

/-! ## The second lifting lemma -/

/-- The two smooth maps `B → B' → Λ` from the twice-lifting lemma, together
with the assertion that the first map kills the specified ideal. -/
structure LiftTwiceFactorization
    {R B Λ : Type u} [CommRing R] [CommRing B] [CommRing Λ]
    [Algebra R B] [Algebra R Λ]
    (J : Ideal B) (φ : B →ₐ[R] Λ) where
  B' : Type u
  [commRingB' : CommRing B']
  [algebraRB' : Algebra R B']
  smoothB' : Algebra.Smooth R B'
  α : B →ₐ[R] B'
  β : B' →ₐ[R] Λ
  kills : Ideal.map α.toRingHom J = ⊥
  factorization : β.comp α = φ

/-- Under the square-zero, filtered-smooth, and flatness hypotheses, a smooth
algebra map whose finitely generated ideal in `I B` vanishes in the target can
be refactored through another smooth algebra in which that ideal is killed. -/
theorem lift_twice
    {R B Λ : Type u} [CommRing R] [CommRing B] [CommRing Λ]
    [Algebra R B] [Algebra R Λ]
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hquot : Nonempty (FilteredSmoothAlgebraColimit
      (R ⧸ I) (infinitesimalTarget (Λ := Λ) I)))
    (hflat : RingHom.Flat (algebraMap R Λ))
    (hB : Algebra.Smooth R B)
    (φ : B →ₐ[R] Λ) (J : Ideal B)
    (hJ_le : J ≤ Ideal.map (algebraMap R B) I)
    (hJ_fg : J.FG)
    (hJ_map : Ideal.map φ.toRingHom J = ⊥) :
    Nonempty (LiftTwiceFactorization J φ) := by
  sorry

/-! ## Stability under infinitesimal deformations -/

/- The source's displayed lifting diagram is the commutativity field in
`LiftTwiceFactorization`; no separate diagram type is needed. -/

/-- Filtered colimits of smooth algebras are stable under nilpotent flat
deformations. -/
theorem filteredSmooth_of_nilpotent_quotient
    {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (hI : IsNilpotent I)
    (hquot : Nonempty (FilteredSmoothAlgebraColimit
      (R ⧸ I) (infinitesimalTarget (Λ := Λ) I)))
    (hflat : RingHom.Flat (algebraMap R Λ)) :
    Nonempty (FilteredSmoothAlgebraColimit R Λ) := by
  sorry

end

end Formalization.Books.Smoothing.Unit05
