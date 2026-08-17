import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Commutative Algebra, Chapter 147: Integral closure and smooth base change

The integral closures in this section use Mathlib's canonical
integralClosure subalgebras. The comparison map is Mathlib's
TensorProduct.toIntegralClosure; the source-facing equivalences below are
constructed from its canonical bijectivity theorem.
-/

namespace Formalization.Books.Algebra.Unit147

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21
open scoped BigOperators TensorProduct

noncomputable section

universe u

/-! ## The derivative trick -/

/-- The canonical model of B[X]/(f) for a polynomial f over R. -/
abbrev IntegralPolynomialQuotient
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (f : Polynomial R) : Type u :=
  AdjoinRoot (f.map (algebraMap R B))

/-- The quotient map from B[X] to B[X]/(f). -/
def integralPolynomialQuotientMk
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (f : Polynomial R) :
    Polynomial B →+* IntegralPolynomialQuotient R B f :=
  AdjoinRoot.mk (f.map (algebraMap R B))

/- The source's f' h = sum b_i x^i formulation is represented by a
   polynomial representative whose coefficients are all integral. This is
   the specialization of Mathlib's more general quotient-algebra lemma. -/
theorem lemma_trick
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {f : Polynomial R} (hf : f.Monic)
    (h : IntegralPolynomialQuotient R B f) (hh : IsIntegral R h) :
    ∃ g : Polynomial B,
      integralPolynomialQuotientMk R B f
          (f.derivative.map (algebraMap R B)) * h =
        integralPolynomialQuotientMk R B f g ∧
      ∀ i, IsIntegral R (g.coeff i) := by
  sorry

/-! ## The etale comparison -/

/-- The canonical comparison map for integral closures is bijective after an
etale base change. -/
theorem integralClosure_baseChange_of_etale
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Etale R S] :
    Function.Bijective
      (TensorProduct.toIntegralClosure R S B) := by
  exact TensorProduct.toIntegralClosure_bijective_of_smooth

/-- The canonical isomorphism asserted by the etale integral-closure lemma. -/
noncomputable def integralClosureEtaleBaseChangeEquiv
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Etale R S] :
    S ⊗[R] integralClosure R B ≃ₐ[S]
      integralClosure S (S ⊗[R] B) :=
  AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R S B)
    (integralClosure_baseChange_of_etale R S B)

/-! ## The cyclotomic example -/

/-- The localization Z[1/p] used in the Fourier example. -/
abbrev fourierBaseRing (p : ℕ) : Type :=
  Localization.Away (p : ℤ)

/-- The canonical cyclotomic presentation of the polynomial appearing in the
Fourier example. -/
def fourierPolynomial (p : ℕ) (R : Type u) [CommRing R] : Polynomial R :=
  Polynomial.cyclotomic p R

/-- The extension Z[1/p][x]/(x^(p-1) + ... + x + 1). -/
abbrev fourierExtension (p : ℕ) : Type :=
  AdjoinRoot (fourierPolynomial p (fourierBaseRing p))

/-- The class of x in the Fourier extension. -/
def fourierRoot (p : ℕ) : fourierExtension p :=
  AdjoinRoot.root (fourierPolynomial p (fourierBaseRing p))

/-- The Vandermonde product of a finite list of elements. -/
def vandermondeProduct {A : Type u} [CommRing A] {d : ℕ}
    (α : Fin d → A) : A :=
  ∏ i : Fin d, ∏ j ∈ Finset.univ.filter (fun j : Fin d => i < j),
    (α i - α j)

/-- The explicit roots used in the source example. -/
def fourierRoots (p d : ℕ) : Fin d → fourierExtension p :=
  fun i => fourierRoot p ^ (i : ℕ)

/-- The Vandermonde product of the first d explicit Fourier roots. -/
def fourierVandermondeProduct (p d : ℕ) : fourierExtension p :=
  vandermondeProduct (fourierRoots p d)

/-- The full factorization product over the p explicit roots. -/
def fourierFactorizationProduct (p : ℕ) : Polynomial (fourierExtension p) :=
  ∏ i : Fin p,
    (Polynomial.X - Polynomial.C (fourierRoot p ^ (i : ℕ)))

/-- The rational cyclotomic quotient used to justify distinctness of the
roots. -/
abbrev fourierRationalExtension (p : ℕ) : Type :=
  AdjoinRoot (fourierPolynomial p ℚ)

/-- For a prime index, the cyclotomic polynomial is the displayed geometric
sum. -/
theorem fourierPolynomial_eq_geometric_sum
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] :
    fourierPolynomial p R =
      ∑ i ∈ Finset.range p, (Polynomial.X : Polynomial R) ^ i := by
  simpa [fourierPolynomial] using Polynomial.cyclotomic_prime R p

/-- The rational polynomial in the Fourier example is irreducible. -/
theorem fourierPolynomial_rat_irreducible
    (p : ℕ) (hp : Nat.Prime p) :
    Irreducible (fourierPolynomial p ℚ) := by
  simpa [fourierPolynomial] using Polynomial.cyclotomic.irreducible_rat hp.pos

/-- The rational cyclotomic quotient is a field. -/
theorem fourierRationalExtension_isField
    (p : ℕ) (hp : Nat.Prime p) :
    IsField (fourierRationalExtension p) := by
  let _ : Fact (Irreducible (fourierPolynomial p ℚ)) :=
    ⟨fourierPolynomial_rat_irreducible p hp⟩
  exact Field.toIsField _

/-- Each explicit Fourier root is a root of T^p - 1. -/
theorem fourier_root_is_root
    (p : ℕ) (hp : Nat.Prime p) (i : Fin p) :
    Polynomial.IsRoot
      (Polynomial.X ^ p - Polynomial.C (1 : fourierExtension p))
      (fourierRoot p ^ (i : ℕ)) := by
  sorry

/-- The explicit roots are pairwise distinct. -/
theorem fourier_roots_injective
    (p : ℕ) (hp : Nat.Prime p) :
    Function.Injective (fourierRoots p p) := by
  sorry

/-- The factorization of T^p - 1 in the Fourier extension. -/
theorem fourier_factorization
    (p : ℕ) (hp : Nat.Prime p) :
    (Polynomial.X ^ p - Polynomial.C (1 : fourierExtension p)) =
      fourierFactorizationProduct p := by
  sorry

/-- Differentiating the Fourier factorization at an explicit root gives the
product of all its pairwise differences. -/
theorem fourier_derivative_at_root
    (p : ℕ) (hp : Nat.Prime p) (i : Fin p) :
    (p : fourierExtension p) * (fourierRoot p ^ (p - 1)) =
      ∏ j ∈ Finset.univ.erase i,
        (fourierRoot p ^ (i : ℕ) - fourierRoot p ^ (j : ℕ)) := by
  sorry

/-- The derivative product in the source proof is a unit. -/
theorem fourier_derivative_product_isUnit
    (p : ℕ) (hp : Nat.Prime p) (i : Fin p) :
    IsUnit
      (∏ j ∈ Finset.univ.erase i,
        (fourierRoot p ^ (i : ℕ) - fourierRoot p ^ (j : ℕ))) := by
  sorry

/-- The explicit Fourier roots give a unit Vandermonde product whenever
d < p. -/
theorem fourier_vandermonde_isUnit
    (p d : ℕ) (hp : Nat.Prime p) (hd : d < p) :
    IsUnit (fourierVandermondeProduct p d) := by
  sorry

/-- The existence statement in the source example, with Fin d indexing. -/
theorem exists_fourier_vandermonde_unit
    (p d : ℕ) (hp : Nat.Prime p) (hd : d < p) :
    ∃ α : Fin d → fourierExtension p, IsUnit (vandermondeProduct α) := by
  refine ⟨fourierRoots p d, ?_⟩
  exact fourier_vandermonde_isUnit p d hp hd

/-! ## Smooth base change -/

/- The polynomial-ring reduction in the source is already Mathlib's
   coefficientwise characterization of integral elements. -/
attribute [local instance] Polynomial.algebra in
theorem polynomial_isIntegral_iff_coefficients
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (f : Polynomial B) :
    IsIntegral (Polynomial R) f ↔ ∀ i, IsIntegral R (f.coeff i) :=
  Polynomial.isIntegral_iff_isIntegral_coeff

/-- The canonical comparison map for integral closures is bijective after a
smooth base change. -/
theorem integralClosure_baseChange_of_smooth
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Smooth R S] :
    Function.Bijective
      (TensorProduct.toIntegralClosure R S B) :=
  TensorProduct.toIntegralClosure_bijective_of_smooth

/-- The canonical isomorphism asserted by the smooth integral-closure lemma. -/
noncomputable def integralClosureSmoothBaseChangeEquiv
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Smooth R S] :
    S ⊗[R] integralClosure R B ≃ₐ[S]
      integralClosure S (S ⊗[R] B) :=
  AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R S B)
    (integralClosure_baseChange_of_smooth R S B)

/-! ## Filtered colimits of smooth algebras -/

/-- A chosen directed filtered-colimit presentation of an R-algebra whose
stages are smooth over R. The directed-system and colimit interfaces are
reused from Chapter 127. -/
structure FilteredSmoothAlgebraColimit
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] extends
    Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit
      (algebraMap R S) where
  smooth :
    ∀ i,
      letI : Algebra R (toDirectedAlgebraColimit.diagram.obj i).right :=
        (toDirectedAlgebraColimit.diagram.obj i).hom.hom.toAlgebra
      Algebra.Smooth R (toDirectedAlgebraColimit.diagram.obj i).right

/-- Integral closure commutes with the filtered smooth base change described
in the source. -/
theorem integralClosure_baseChange_of_filtered_smooth
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B]
    (D : FilteredSmoothAlgebraColimit R S) :
    Function.Bijective
      (TensorProduct.toIntegralClosure R S B) := by
  sorry

/-- The canonical isomorphism in the filtered-colimit statement. -/
noncomputable def integralClosureFilteredSmoothBaseChangeEquiv
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B]
    (D : FilteredSmoothAlgebraColimit R S) :
    S ⊗[R] integralClosure R B ≃ₐ[S]
      integralClosure S (S ⊗[R] B) :=
  AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R S B)
    (integralClosure_baseChange_of_filtered_smooth R S B D)

end

end Formalization.Books.Algebra.Unit147
