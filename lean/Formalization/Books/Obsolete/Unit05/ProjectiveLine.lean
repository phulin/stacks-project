import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Module

/-!
# Obsolete, Chapter 5: the projective-line lemmas

The source writes `R[X, Y]`; this is represented by
`MvPolynomial (Fin 2) R`.  The quotient and its degree pieces use the
canonical homogeneous submodules and the canonical algebra quotient map.
-/

namespace Formalization.Books.Obsolete.Unit05

open Set

universe u v

noncomputable section

/-! ## The homogeneous quotient of the binary polynomial ring -/

abbrev BinaryPolynomial (R : Type u) [CommSemiring R] := MvPolynomial (Fin 2) R

def projectiveLineQuotientIdeal
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) : Ideal (BinaryPolynomial R) :=
  Ideal.span ({F} : Set (BinaryPolynomial R))

abbrev projectiveLineQuotient
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) :=
  BinaryPolynomial R ⧸ projectiveLineQuotientIdeal F

/- The degree-`n` part of the quotient is the image of the homogeneous degree
   `n` submodule under the quotient algebra map. -/
def projectiveLineQuotientComponent
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) (n : ℕ) :
    Submodule R (projectiveLineQuotient F) :=
  Submodule.map
    (Ideal.Quotient.mkₐ R (projectiveLineQuotientIdeal F)).toLinearMap
    (MvPolynomial.homogeneousSubmodule (Fin 2) R n)

/- The homogeneous equation gives the quotient the expected graded-ring
   structure.  The component family is the one used above. -/
theorem projectiveLineQuotient_graded
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    Nonempty (GradedRing (fun n : ℕ =>
      (projectiveLineQuotientComponent F n).toAddSubgroup)) := by
  sorry

theorem projectiveLine_finite_locally_free
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) (d : ℕ)
    (hF : F.IsHomogeneous d)
    (hF_coeff : ∀ p : PrimeSpectrum R, ∃ m : Fin 2 →₀ ℕ,
      F.coeff m ∉ p.asIdeal) (n : ℕ) (hn : d ≤ n) :
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R
      (projectiveLineQuotientComponent F n : Type u) d := by
  sorry

/-! ## Relative primeness and multiplication -/

/- Multiplication by a homogeneous quotient element on the ambient quotient
   ring. -/
def projectiveLineMultiplication
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R) :
    projectiveLineQuotient F →ₗ[R] projectiveLineQuotient F :=
  LinearMap.mulLeft R (Ideal.Quotient.mk (projectiveLineQuotientIdeal F) G)

theorem rel_prime_pols
    {k : Type u} [Field k] (F G : BinaryPolynomial k)
    (hcop : IsRelPrime F G) :
    Function.Injective (projectiveLineMultiplication F G) := by
  sorry

/- The homogeneous product of a degree-`e` element with a degree-`n`
   component element lies in degree `n + e`. -/
theorem projectiveLine_multiplication_mem_component
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (e n : ℕ) (hG : G.IsHomogeneous e)
    (x : projectiveLineQuotientComponent F n) :
    projectiveLineMultiplication F G x.1 ∈
      projectiveLineQuotientComponent F (n + e) := by
  sorry

/- The component map induced by multiplication by `G`. -/
def projectiveLineComponentMultiplication
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (e n : ℕ) (hG : G.IsHomogeneous e) :
    projectiveLineQuotientComponent F n →ₗ[R]
      projectiveLineQuotientComponent F (n + e) :=
  ((projectiveLineMultiplication F G).comp
      (projectiveLineQuotientComponent F n).subtype).codRestrict
    (projectiveLineQuotientComponent F (n + e))
    (projectiveLine_multiplication_mem_component F G e n hG)

theorem projectiveLine_localize
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) (d : ℕ)
    (hF : F.IsHomogeneous d)
    (p : PrimeSpectrum R)
    (hp : ∃ m : Fin 2 →₀ ℕ, F.coeff m ∉ p.asIdeal) :
    ∃ f : R, f ∉ p.asIdeal ∧ ∃ e : ℕ, ∃ G : BinaryPolynomial R,
      ∃ hG : G.IsHomogeneous e,
        ∀ n : ℕ, d ≤ n →
          Function.Bijective
            (LocalizedModule.map (Submonoid.powers f)
              (projectiveLineComponentMultiplication F G e n hG)) := by
  sorry

/-! ## The finite algebra in the periodic case -/

def projectiveLineHomogeneousElement
    {R : Type u} [CommRing R] (F P : BinaryPolynomial R)
    (n : ℕ) (hP : P.IsHomogeneous n) :
    projectiveLineQuotientComponent F n :=
  ⟨Ideal.Quotient.mk (projectiveLineQuotientIdeal F) P,
    Submodule.mem_map.mpr ⟨P, hP, by
      simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.toLinearMap_apply]⟩⟩

theorem projectiveLine_component_product_mem
    {R : Type u} [CommRing R] (F : BinaryPolynomial R)
    (m n : ℕ) (x : projectiveLineQuotientComponent F m)
    (y : projectiveLineQuotientComponent F n) :
    x.1 * y.1 ∈ projectiveLineQuotientComponent F (m + n) := by
  sorry

def projectiveLineComponentProductLeft
    {R : Type u} [CommRing R] (F : BinaryPolynomial R)
    (m n : ℕ) (x : projectiveLineQuotientComponent F m) :
    projectiveLineQuotientComponent F n →ₗ[R]
      projectiveLineQuotientComponent F (m + n) :=
  ((LinearMap.mulLeft R x.1).comp
      (projectiveLineQuotientComponent F n).subtype).codRestrict
    (projectiveLineQuotientComponent F (m + n))
    (projectiveLine_component_product_mem F m n x)

def projectiveLinePowerElement
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (e d : ℕ) (hG : G.IsHomogeneous e) :
    projectiveLineQuotientComponent F (e * d) :=
  projectiveLineHomogeneousElement F (G ^ d) (e * d) (hG.pow d)

def projectiveLinePowerMultiplication
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (e d : ℕ) (hG : G.IsHomogeneous e) :
    projectiveLineQuotientComponent F (e * d) →ₗ[R]
      projectiveLineQuotientComponent F ((e * d) + (e * d)) :=
  projectiveLineComponentProductLeft F (e * d) (e * d)
    (projectiveLinePowerElement F G e d hG)

theorem projectiveLine_power_multiplication_bijective
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (d e : ℕ) (hG : G.IsHomogeneous e)
    (hmul : ∀ n : ℕ, d ≤ n →
      Function.Bijective (projectiveLineComponentMultiplication F G e n hG)) :
    Function.Bijective (projectiveLinePowerMultiplication F G e d hG) := by
  sorry

/- The following structure records the output of the source's transported
   multiplication.  The ring and algebra structures are fields so the
   construction does not install a competing global instance on the
   component subtype. -/
structure ProjectiveLineFiniteAlgebraConstruction
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (d e : ℕ) (hG : G.IsHomogeneous e) where
  F_homogeneous : F.IsHomogeneous d
  ring : CommRing (projectiveLineQuotientComponent F (e * d) : Type u)
  algebra : letI := ring
    Algebra R (projectiveLineQuotientComponent F (e * d) : Type u)
  finite_locally_free :
    letI := ring
    letI := algebra
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R
      (projectiveLineQuotientComponent F (e * d) : Type u) d
  multiplication :
    projectiveLineQuotientComponent F (e * d) →
      projectiveLineQuotientComponent F (e * d) →
        projectiveLineQuotientComponent F (e * d)
  one : projectiveLineQuotientComponent F (e * d)
  multiplication_eq_ring_mul :
    letI := ring
    ∀ H₁ H₂, multiplication H₁ H₂ = H₁ * H₂
  multiplication_rule :
    ∀ H₁ H₂ H₃,
      multiplication H₁ H₂ = H₃ ↔
        (projectiveLinePowerElement F G e d hG).1 * H₃.1 = H₁.1 * H₂.1
  one_eq_power : one = projectiveLinePowerElement F G e d hG

theorem projectiveLine_finite_algebra_construction
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (d e : ℕ) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (hfinite : ∀ n : ℕ, d ≤ n →
      Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R
        (projectiveLineQuotientComponent F n : Type u) d)
    (hmul : ∀ n : ℕ, d ≤ n →
      Function.Bijective (projectiveLineComponentMultiplication F G e n hG)) :
    Nonempty (ProjectiveLineFiniteAlgebraConstruction F G d e hG) := by
  sorry

end

end Formalization.Books.Obsolete.Unit05
