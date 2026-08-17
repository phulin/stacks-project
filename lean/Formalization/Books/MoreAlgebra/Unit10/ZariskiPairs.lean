import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Integral
import Formalization.Books.Algebra.Unit32.LocallyNilpotent
import Formalization.Books.Algebra.Unit138.FormallySmoothMaps
import Formalization.Books.MoreAlgebra.Unit09.Lifting

/-!
# More on Algebra, Chapter 10: Zariski pairs

This file records the pair conventions and the theorem interfaces in the
section on Zariski pairs.  Quotients, idempotents, finiteness properties of
ring maps, and Jacobson rings use the canonical Mathlib constructions.
-/

namespace Formalization.Books.MoreAlgebra.Unit10

universe u v

noncomputable section

/-! ## Pairs and the Zariski-pair condition -/

/-- A pair `(A, I)` consisting of a commutative ring and an ideal of it. -/
structure Pair (A : Type u) [CommRing A] where
  ideal : Ideal A

/-- A morphism of pairs is a ring map carrying the source ideal into the
target ideal.  `Ideal.map` is equivalent to the elementwise containment used
in the source because the target is an ideal. -/
def PairHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (P : Pair A) (Q : Pair B) (f : A →+* B) : Prop :=
  Ideal.map f P.ideal ≤ Q.ideal

/-- The condition that an ideal is contained in the Jacobson radical. -/
def ZariskiPair {A : Type u} [CommRing A] (I : Ideal A) : Prop :=
  I ≤ Ring.jacobson A

/-! ## Idempotents modulo a Jacobson-radical ideal -/

/-- Idempotents are determined by their reductions modulo a Jacobson-radical
ideal. -/
theorem idempotents_determined_modulo_radical
    {A : Type u} [CommRing A] (I : Ideal A) (hI : ZariskiPair I) :
    Function.Injective
      (Formalization.Books.Algebra.Unit32.quotientIdempotentMap I) := by
  sorry

/-! ## Checking an isomorphism from the quotient -/

/-- A flat, integral, finitely presented map which is an isomorphism after
reduction modulo a Zariski-pair ideal is already an isomorphism. -/
theorem check_isomorphism_zariski
    {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (hI : ZariskiPair I)
    (f : A →+* B) (hflat : f.Flat) (hintegral : f.IsIntegral)
    (hfp : f.FinitePresentation)
    (hquot : Function.Bijective
      (Formalization.Books.Algebra.Unit138.quotientBaseChangeRingMap f I)) :
    Function.Bijective f := by
  sorry

/-! ## The finite-helper factorization data -/

/-- Data for the product decomposition used in the finite helper lemma.

The factors are presented as `A ⧸ I`-algebras, so their reductions by the
induced ideal `I` are canonically the factors themselves.  The displayed
condition `A ⧸ I → B₁/IB₁` is therefore represented by surjectivity of the
canonical algebra map to `B₁`. -/
def FiniteHelperFactorization
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A)
    (B₁ B₂ : Type v) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (b : B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra (A ⧸ I) (B ⧸ Ideal.map f I) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (p := I) (P := Ideal.map f I) Ideal.le_comap_map
  ∃ e : (B ⧸ Ideal.map f I) ≃ₐ[A ⧸ I] B₁ × B₂,
    Function.Surjective (algebraMap (A ⧸ I) B₁) ∧
      e (Ideal.Quotient.mk (Ideal.map f I) b) = (1, 0)

/- The étale base extension, product splitting, faithful-flatness descent, and
local-rank arguments in the source are proof steps for the theorem below;
the factorization data records the externally visible product and reduction
hypotheses. -/

/-- For a finite map, a product decomposition modulo a Zariski-pair ideal and
the distinguished element `(1, 0)` produce a monic annihilating polynomial
whose reduction is `(X - 1) X^d` for some positive `d`. -/
theorem helper_finite
    {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (hI : ZariskiPair I)
    (f : A →+* B) (hfinite : RingHom.Finite f)
    (B₁ B₂ : Type v) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (b : B) (hfactor : FiniteHelperFactorization f I B₁ B₂ b) :
    ∃ p : Polynomial A, p.Monic ∧ Polynomial.eval₂ f b p = 0 ∧
      ∃ d : ℕ, 1 ≤ d ∧
        Polynomial.map (Ideal.Quotient.mk I) p =
          (Polynomial.X - Polynomial.C (1 : A ⧸ I)) * Polynomial.X ^ d := by
  sorry

/-! ## Jacobson complements -/

/-- In a Noetherian Zariski pair, inverting an element of the distinguished
ideal produces a Jacobson ring. -/
theorem noetherian_zariski_jacobson_complement
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : ZariskiPair I) (f : A) (hf : f ∈ I) :
    IsJacobsonRing (Localization.Away f) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit10
