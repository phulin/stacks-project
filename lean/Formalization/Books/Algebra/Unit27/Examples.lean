import Formalization.Books.Algebra.Unit17.Spectrum
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Commutative Algebra, Chapter 27: Examples of spectra of rings

This file formalizes the four examples in the source section.  The concrete
rings and maps use Mathlib's canonical polynomial, quotient, subalgebra,
localization, ideal, and prime-spectrum constructions.  The long
classification and topology arguments are theorem interfaces; their proofs
belong to the proving stage.
-/

namespace Formalization.Books.Algebra.Unit27

open Set
open Topology

open scoped Polynomial

noncomputable section

/-! ## `Spec(ℤ[x]/(x^2 - 4))` -/

abbrev IntPolynomial := Polynomial ℤ

/-- The relation defining the ring `ℤ[x]/(x^2 - 4)`. -/
def intQuadraticRelation : Ideal IntPolynomial :=
  Ideal.span {Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)}

/-- The ring in the first example. -/
abbrev IntQuadraticRing := IntPolynomial ⧸ intQuadraticRelation

/-- The quotient map from `ℤ[x]` to the quadratic ring. -/
def intQuadraticQuotientMap : IntPolynomial →+* IntQuadraticRing :=
  Ideal.Quotient.mk intQuadraticRelation

/-- The structure map `ℤ → ℤ[x]/(x^2 - 4)`. -/
def intQuadraticStructureMap : ℤ →+* IntQuadraticRing :=
  intQuadraticQuotientMap.comp Polynomial.C

/-- The ideal `(x - r)` in the quadratic quotient. -/
def intQuadraticRootIdeal (r : ℤ) : Ideal IntQuadraticRing :=
  Ideal.span {intQuadraticQuotientMap (Polynomial.X - Polynomial.C r)}

/-- The ideal `(q, x - r)` in the quadratic quotient. -/
def intQuadraticPrimeIdeal (q : ℕ) (r : ℤ) : Ideal IntQuadraticRing :=
  Ideal.span
    {intQuadraticQuotientMap (Polynomial.C (q : ℤ)),
      intQuadraticQuotientMap (Polynomial.X - Polynomial.C r)}

theorem int_quadratic_factorization :
    Polynomial.X ^ 2 - Polynomial.C (4 : ℤ) =
      (Polynomial.X - Polynomial.C 2) * (Polynomial.X + Polynomial.C 2) := by
  simp [sub_eq_add_neg]
  ring

theorem int_quadratic_prime_contraction_isPrime (p : PrimeSpectrum IntQuadraticRing) :
    (p.asIdeal.comap intQuadraticStructureMap).IsPrime := by
  exact Ideal.comap_isPrime intQuadraticStructureMap p.asIdeal

theorem int_quadratic_reduction_mod_prime (q : ℕ) :
    Nonempty
      ((IntQuadraticRing ⧸
            Ideal.span {intQuadraticQuotientMap (Polynomial.C (q : ℤ))}) ≃+*
          (Polynomial (ℤ ⧸ Ideal.span {(q : ℤ)}) ⧸
            Ideal.span {Polynomial.X ^ 2 - Polynomial.C (4 : ℤ ⧸ Ideal.span {(q : ℤ)})})) := by
  let I : Ideal ℤ := Ideal.span {(q : ℤ)}
  let M : Ideal IntPolynomial := Ideal.map Polynomial.C I
  let K : Ideal IntPolynomial := intQuadraticRelation
  let Kq : Ideal (Polynomial (ℤ ⧸ I)) :=
    Ideal.span {Polynomial.X ^ 2 - Polynomial.C (4 : ℤ ⧸ I)}
  let ePoly := I.polynomialQuotientEquivQuotientPolynomial
  have hsource :
      Ideal.span {intQuadraticQuotientMap (Polynomial.C (q : ℤ))} =
        M.map (Ideal.Quotient.mk K) := by
    simp [I, M, K, intQuadraticQuotientMap, Ideal.map_span]
  have hgen :
      ePoly (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ ⧸ I)) =
        Ideal.Quotient.mk M (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)) := by
    calc
      ePoly (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ ⧸ I)) =
          ePoly ((Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)).map
            (Ideal.Quotient.mk I)) := by
        congr 1
        simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_C]
        congr 2
      _ = Ideal.Quotient.mk M (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)) := by
        exact Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk I
          (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ))
  have hmapideal :
      (intQuadraticRelation.map (Ideal.Quotient.mk M)) =
        Kq.map (ePoly : (Polynomial (ℤ ⧸ I)) →+* (IntPolynomial ⧸ M)) := by
    simp only [intQuadraticRelation, Kq, Ideal.map_span, Set.image_singleton]
    change Ideal.span {Ideal.Quotient.mk M (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ))} =
      Ideal.span {ePoly (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ ⧸ I))}
    rw [hgen]
  have e0 :
      (IntQuadraticRing ⧸ Ideal.span
          {intQuadraticQuotientMap (Polynomial.C (q : ℤ))}) ≃+*
        IntPolynomial ⧸ (K ⊔ M) := by
    rw [hsource]
    exact DoubleQuot.quotQuotEquivQuotSup K M
  have e1 : IntPolynomial ⧸ (K ⊔ M) ≃+* IntPolynomial ⧸ (M ⊔ K) :=
    Ideal.quotEquivOfEq (sup_comm K M)
  have e2 :
      IntPolynomial ⧸ (M ⊔ K) ≃+*
        (IntPolynomial ⧸ M) ⧸ intQuadraticRelation.map (Ideal.Quotient.mk M) :=
    (DoubleQuot.quotQuotEquivQuotSup M K).symm
  have e3 :
      ((IntPolynomial ⧸ M) ⧸ intQuadraticRelation.map (Ideal.Quotient.mk M)) ≃+*
        (Polynomial (ℤ ⧸ I) ⧸ Kq) :=
    (Ideal.quotientEquiv Kq (intQuadraticRelation.map (Ideal.Quotient.mk M))
      ePoly hmapideal).symm
  exact ⟨e0.trans (e1.trans (e2.trans e3))⟩

theorem int_quadratic_reduction_mod_two :
    Nonempty
      ((IntQuadraticRing ⧸
            Ideal.span {intQuadraticQuotientMap (Polynomial.C (2 : ℤ))}) ≃+*
          (Polynomial (ℤ ⧸ Ideal.span {(2 : ℤ)}) ⧸
            Ideal.span
              ({Polynomial.X ^ 2} : Set (Polynomial (ℤ ⧸ Ideal.span {(2 : ℤ)}))))) := by
  let I : Ideal ℤ := Ideal.span {(2 : ℤ)}
  let M : Ideal IntPolynomial := Ideal.map Polynomial.C I
  let K : Ideal IntPolynomial := intQuadraticRelation
  let Kq : Ideal (Polynomial (ℤ ⧸ I)) :=
    Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial (ℤ ⧸ I)))
  let ePoly := I.polynomialQuotientEquivQuotientPolynomial
  have h4map : (Ideal.Quotient.mk I) (4 : ℤ) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨2, by norm_num⟩
  have hsource :
      Ideal.span {intQuadraticQuotientMap (Polynomial.C (2 : ℤ))} =
        M.map (Ideal.Quotient.mk K) := by
    simp [I, M, K, intQuadraticQuotientMap, Ideal.map_span]
  have hgen :
      ePoly Polynomial.X ^ 2 =
        Ideal.Quotient.mk M (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)) := by
    calc
      ePoly Polynomial.X ^ 2 =
          ePoly ((Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)).map
            (Ideal.Quotient.mk I)) := by
        simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_C]
        rw [h4map]
        simp
      _ = Ideal.Quotient.mk M (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)) := by
        exact Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk I
          (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ))
  have hmapideal :
      (intQuadraticRelation.map (Ideal.Quotient.mk M)) =
        Kq.map (ePoly : (Polynomial (ℤ ⧸ I)) →+* (IntPolynomial ⧸ M)) := by
    simp only [intQuadraticRelation, Kq, Ideal.map_span, Set.image_singleton]
    apply congrArg Ideal.span
    simpa using congrArg (fun z => ({z} : Set (IntPolynomial ⧸ M))) hgen.symm
  have e0 :
      (IntQuadraticRing ⧸ Ideal.span
          {intQuadraticQuotientMap (Polynomial.C (2 : ℤ))}) ≃+*
        IntPolynomial ⧸ (K ⊔ M) := by
    rw [hsource]
    exact DoubleQuot.quotQuotEquivQuotSup K M
  have e1 : IntPolynomial ⧸ (K ⊔ M) ≃+* IntPolynomial ⧸ (M ⊔ K) :=
    Ideal.quotEquivOfEq (sup_comm K M)
  have e2 :
      IntPolynomial ⧸ (M ⊔ K) ≃+*
        (IntPolynomial ⧸ M) ⧸ intQuadraticRelation.map (Ideal.Quotient.mk M) :=
    (DoubleQuot.quotQuotEquivQuotSup M K).symm
  have e3 :
      ((IntPolynomial ⧸ M) ⧸ intQuadraticRelation.map (Ideal.Quotient.mk M)) ≃+*
        (Polynomial (ℤ ⧸ I) ⧸ Kq) :=
    (Ideal.quotientEquiv Kq (intQuadraticRelation.map (Ideal.Quotient.mk M))
      ePoly hmapideal).symm
  exact ⟨e0.trans (e1.trans (e2.trans e3))⟩

theorem int_quadratic_prime_spectra_reduction_correspondence (q : ℕ) :
    Nonempty
      (PrimeSpectrum
          (IntQuadraticRing ⧸
            Ideal.span {intQuadraticQuotientMap (Polynomial.C (q : ℤ))}) ≃
        PrimeSpectrum
          (Polynomial (ℤ ⧸ Ideal.span {(q : ℤ)}) ⧸
            Ideal.span {Polynomial.X ^ 2 -
              Polynomial.C (4 : ℤ ⧸ Ideal.span {(q : ℤ)})})) := by
  exact Nonempty.map (fun e => (PrimeSpectrum.comapEquiv e).toEquiv)
    (int_quadratic_reduction_mod_prime q)

theorem int_polynomial_root_quotient_equiv (r : ℤ) :
    Nonempty ((IntPolynomial ⧸
      Ideal.span {Polynomial.X - Polynomial.C r}) ≃+* ℤ) := by
  exact ⟨(Polynomial.quotientSpanXSubCAlgEquiv r).toRingEquiv⟩

theorem int_quadratic_root_ideals_isPrime :
    (intQuadraticRootIdeal 2).IsPrime ∧
      (intQuadraticRootIdeal (-2)).IsPrime := by
  have hprime (r : ℤ) :
      (Ideal.span ({Polynomial.X - Polynomial.C r} : Set IntPolynomial)).IsPrime := by
    exact Ideal.isPrime_span_singleton_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Polynomial.irreducible_X_sub_C r))
  have hle2 : intQuadraticRelation ≤
      Ideal.span ({Polynomial.X - Polynomial.C (2 : ℤ)} : Set IntPolynomial) := by
    change Ideal.span ({Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)} : Set IntPolynomial) ≤ _
    rw [int_quadratic_factorization]
    rw [Ideal.span_singleton_le_iff_mem]
    exact (Ideal.span ({Polynomial.X - Polynomial.C (2 : ℤ)} : Set IntPolynomial)).mul_mem_right
      (Polynomial.X + Polynomial.C 2) (Ideal.subset_span (by simp))
  have hleNeg2 : intQuadraticRelation ≤
      Ideal.span ({Polynomial.X - Polynomial.C (-2 : ℤ)} : Set IntPolynomial) := by
    change Ideal.span ({Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)} : Set IntPolynomial) ≤ _
    rw [int_quadratic_factorization]
    rw [Ideal.span_singleton_le_iff_mem]
    exact (Ideal.span ({Polynomial.X - Polynomial.C (-2 : ℤ)} : Set IntPolynomial)).mul_mem_left
      (Polynomial.X - Polynomial.C 2) (Ideal.subset_span (by simp [sub_eq_add_neg]))
  have hmap2 : (intQuadraticRootIdeal 2).IsPrime := by
    let := hprime 2
    have hk : RingHom.ker intQuadraticQuotientMap ≤
        Ideal.span ({Polynomial.X - Polynomial.C (2 : ℤ)} : Set IntPolynomial) := by
      change RingHom.ker (Ideal.Quotient.mk intQuadraticRelation) ≤ _
      rw [Ideal.mk_ker]
      exact hle2
    have hm := Ideal.map_isPrime_of_surjective
      (f := intQuadraticQuotientMap) Ideal.Quotient.mk_surjective hk
    simpa [intQuadraticRootIdeal, Ideal.map_span] using hm
  have hmapNeg2 : (intQuadraticRootIdeal (-2)).IsPrime := by
    let := hprime (-2)
    have hk : RingHom.ker intQuadraticQuotientMap ≤
        Ideal.span ({Polynomial.X - Polynomial.C (-2 : ℤ)} : Set IntPolynomial) := by
      change RingHom.ker (Ideal.Quotient.mk intQuadraticRelation) ≤ _
      rw [Ideal.mk_ker]
      exact hleNeg2
    have hm := Ideal.map_isPrime_of_surjective
      (f := intQuadraticQuotientMap) Ideal.Quotient.mk_surjective hk
    simpa [intQuadraticRootIdeal, Ideal.map_span] using hm
  exact ⟨hmap2, hmapNeg2⟩

theorem int_quadratic_prime_ideal_at_two_isPrime :
    (intQuadraticPrimeIdeal 2 0).IsPrime := by
  let J : Ideal IntPolynomial :=
    Ideal.span {Polynomial.C (2 : ℤ), Polynomial.X - Polynomial.C (0 : ℤ)}
  have hcoeff : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime := by
    let : Fact (Nat.Prime 2) := ⟨by decide⟩
    exact (Int.ideal_span_isMaximal_of_prime 2).isPrime
  have hcoeffDomain : IsDomain (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hcoeff
  have hJdomain : IsDomain (IntPolynomial ⧸ J) := by
    let := hcoeffDomain
    change IsDomain (IntPolynomial ⧸
      Ideal.span {Polynomial.C (2 : ℤ), Polynomial.X - Polynomial.C (0 : ℤ)})
    apply (Polynomial.quotientSpanCXSubCAlgEquiv (2 : ℤ) 0).toMulEquiv.isDomain
  have hJprime : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp hJdomain
  have hrel : intQuadraticRelation ≤ J := by
    have hX : Polynomial.X - Polynomial.C (0 : ℤ) ∈ J :=
      Ideal.subset_span (by simp)
    have hC : Polynomial.C (2 : ℤ) ∈ J := Ideal.subset_span (by simp)
    have hxm : Polynomial.X - Polynomial.C (2 : ℤ) ∈ J := by
      simpa using J.sub_mem hX hC
    change Ideal.span ({Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)} : Set IntPolynomial) ≤ J
    rw [int_quadratic_factorization]
    rw [Ideal.span_singleton_le_iff_mem]
    exact J.mul_mem_right (Polynomial.X + Polynomial.C 2) hxm
  let := hJprime
  have hk : RingHom.ker intQuadraticQuotientMap ≤ J := by
    change RingHom.ker (Ideal.Quotient.mk intQuadraticRelation) ≤ J
    rw [Ideal.mk_ker]
    exact hrel
  have hm := Ideal.map_isPrime_of_surjective
    (f := intQuadraticQuotientMap) Ideal.Quotient.mk_surjective hk
  have hmap : Ideal.map intQuadraticQuotientMap J = intQuadraticPrimeIdeal 2 0 := by
    rw [Ideal.map_span]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_image]
    constructor
    · rintro ⟨x, (rfl | rfl), h⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact ⟨Polynomial.C 2, Or.inl rfl, h.symm⟩
      · exact ⟨Polynomial.X - Polynomial.C 0, Or.inr rfl, h.symm⟩
  rw [← hmap]
  exact hm

theorem int_quadratic_prime_ideals_isPrime (q : ℕ) (hq : Nat.Prime q) :
      (intQuadraticPrimeIdeal q 2).IsPrime ∧
      (intQuadraticPrimeIdeal q (-2)).IsPrime := by
  have hcoeff : (Ideal.span ({(q : ℤ)} : Set ℤ)).IsPrime := by
    have : Fact (Nat.Prime q) := ⟨hq⟩
    exact (Int.ideal_span_isMaximal_of_prime q).isPrime
  have hcoeffDomain : IsDomain (ℤ ⧸ Ideal.span ({(q : ℤ)} : Set ℤ)) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hcoeff
  let J (r : ℤ) : Ideal IntPolynomial :=
    Ideal.span {Polynomial.C (q : ℤ), Polynomial.X - Polynomial.C r}
  have hJdomain (r : ℤ) : IsDomain (IntPolynomial ⧸ J r) := by
    let := hcoeffDomain
    exact (Polynomial.quotientSpanCXSubCAlgEquiv (q : ℤ) r).toMulEquiv.isDomain
  have hJprime (r : ℤ) : (J r).IsPrime := by
    exact (Ideal.Quotient.isDomain_iff_prime _).mp (hJdomain r)
  have hrel2 : intQuadraticRelation ≤ J 2 := by
    have hX : Polynomial.X - Polynomial.C (2 : ℤ) ∈ J 2 :=
      Ideal.subset_span (by simp)
    change Ideal.span ({Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)} : Set IntPolynomial) ≤ J 2
    rw [int_quadratic_factorization]
    rw [Ideal.span_singleton_le_iff_mem]
    exact (J 2).mul_mem_right (Polynomial.X + Polynomial.C 2) hX
  have hrelNeg2 : intQuadraticRelation ≤ J (-2) := by
    have hX : Polynomial.X - Polynomial.C (-2 : ℤ) ∈ J (-2) :=
      Ideal.subset_span (by simp)
    have hfac : Polynomial.X + Polynomial.C (2 : ℤ) ∈ J (-2) := by
      simpa [sub_eq_add_neg] using hX
    change Ideal.span ({Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)} : Set IntPolynomial) ≤ J (-2)
    rw [int_quadratic_factorization]
    rw [Ideal.span_singleton_le_iff_mem]
    exact (J (-2)).mul_mem_left (Polynomial.X - Polynomial.C 2) hfac
  have hmap (r : ℤ) :
      Ideal.map intQuadraticQuotientMap (J r) = intQuadraticPrimeIdeal q r := by
    rw [Ideal.map_span]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro ⟨x, (rfl | rfl), h⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact ⟨Polynomial.C q, Or.inl rfl, h.symm⟩
      · exact ⟨Polynomial.X - Polynomial.C r, Or.inr rfl, h.symm⟩
  have hprime (r : ℤ) (hr : intQuadraticRelation ≤ J r) :
      (intQuadraticPrimeIdeal q r).IsPrime := by
    have hk : RingHom.ker intQuadraticQuotientMap ≤ J r := by
      change RingHom.ker (Ideal.Quotient.mk intQuadraticRelation) ≤ J r
      rw [Ideal.mk_ker]
      exact hr
    have hm := @Ideal.map_isPrime_of_surjective IntPolynomial IntQuadraticRing
      (IntPolynomial →+* IntQuadraticRing) _ _ _ _ intQuadraticQuotientMap
      Ideal.Quotient.mk_surjective (J r) (hJprime r) hk
    rw [← hmap r]
    exact hm
  exact ⟨hprime 2 hrel2, hprime (-2) hrelNeg2⟩

/-- The complete list of prime ideals in the first example.

The two roots over odd residue fields are separated by the explicit
assumption `2 < q`; the ramified prime over `2` is listed separately. -/
theorem prime_spectrum_int_quadratic_cases (p : PrimeSpectrum IntQuadraticRing) :
    p.asIdeal = intQuadraticRootIdeal 2 ∨
      p.asIdeal = intQuadraticRootIdeal (-2) ∨
      p.asIdeal = intQuadraticPrimeIdeal 2 0 ∨
      ∃ q : ℕ, Nat.Prime q ∧ 2 < q ∧
        (p.asIdeal = intQuadraticPrimeIdeal q 2 ∨
          p.asIdeal = intQuadraticPrimeIdeal q (-2)) := by
  let Q : Ideal IntPolynomial := p.asIdeal.comap intQuadraticQuotientMap
  have hQprime : Q.IsPrime := by
    exact Ideal.comap_isPrime intQuadraticQuotientMap p.asIdeal
  have hconQ : Q.comap Polynomial.C =
      p.asIdeal.comap intQuadraticStructureMap := by
    change (p.asIdeal.comap intQuadraticQuotientMap).comap Polynomial.C = _
    rw [Ideal.comap_comap]
    rfl
  have hrelQ : intQuadraticRelation ≤ Q := by
    change intQuadraticRelation ≤ p.asIdeal.comap intQuadraticQuotientMap
    unfold intQuadraticRelation
    apply Ideal.span_le.2
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    change intQuadraticQuotientMap
      (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)) ∈ p.asIdeal
    have hzero : intQuadraticQuotientMap
        (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)) = 0 := by
      change Ideal.Quotient.mk intQuadraticRelation
        (Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
    rw [hzero]
    exact p.asIdeal.zero_mem
  have hfactor_mem :
      (Polynomial.X - Polynomial.C (2 : ℤ)) *
          (Polynomial.X + Polynomial.C (2 : ℤ)) ∈ Q := by
    rw [← int_quadratic_factorization]
    exact hrelQ (Ideal.subset_span (by simp))
  have hQeqroot (r : ℤ) (hroot : Polynomial.X - Polynomial.C r ∈ Q)
      (hcon : Q.comap Polynomial.C = ⊥) :
      Q = Ideal.span ({Polynomial.X - Polynomial.C r} : Set IntPolynomial) := by
    apply le_antisymm
    · intro f hf
      have hmul : (Polynomial.X - Polynomial.C r) *
          (f /ₘ (Polynomial.X - Polynomial.C r)) ∈ Q :=
        Q.mul_mem_right _ hroot
      have hdecomp : Polynomial.C (f.eval r) +
          (Polynomial.X - Polynomial.C r) *
            (f /ₘ (Polynomial.X - Polynomial.C r)) = f := by
        rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval f r]
        exact Polynomial.modByMonic_add_div f (Polynomial.X - Polynomial.C r)
      have hconst : Polynomial.C (f.eval r) ∈ Q := by
        have hsub := Q.sub_mem hf hmul
        have heq : f - (Polynomial.X - Polynomial.C r) *
            (f /ₘ (Polynomial.X - Polynomial.C r)) = Polynomial.C (f.eval r) := by
          calc
            f - (Polynomial.X - Polynomial.C r) *
                (f /ₘ (Polynomial.X - Polynomial.C r)) =
                (Polynomial.C (f.eval r) +
                  (Polynomial.X - Polynomial.C r) *
                    (f /ₘ (Polynomial.X - Polynomial.C r))) -
                  (Polynomial.X - Polynomial.C r) *
                    (f /ₘ (Polynomial.X - Polynomial.C r)) :=
              congrArg (fun t : IntPolynomial => t -
                (Polynomial.X - Polynomial.C r) *
                  (f /ₘ (Polynomial.X - Polynomial.C r))) hdecomp.symm
            _ = Polynomial.C (f.eval r) := add_sub_cancel_right _ _
        rw [heq] at hsub
        exact hsub
      have heval : f.eval r = 0 := by
        have heval' : f.eval r ∈ Q.comap Polynomial.C := by
          exact hconst
        rw [hcon] at heval'
        simpa using heval'
      have hdecomp' := hdecomp
      rw [heval] at hdecomp'
      have hmulJ : (Polynomial.X - Polynomial.C r) *
          (f /ₘ (Polynomial.X - Polynomial.C r)) ∈
            Ideal.span ({Polynomial.X - Polynomial.C r} : Set IntPolynomial) :=
        (Ideal.span ({Polynomial.X - Polynomial.C r} : Set IntPolynomial)).mul_mem_right _
          (Ideal.subset_span (by simp))
      have hf_eq : f = (Polynomial.X - Polynomial.C r) *
          (f /ₘ (Polynomial.X - Polynomial.C r)) := by
        calc
          f = Polynomial.C 0 + (Polynomial.X - Polynomial.C r) *
              (f /ₘ (Polynomial.X - Polynomial.C r)) := hdecomp'.symm
          _ = (Polynomial.X - Polynomial.C r) *
              (f /ₘ (Polynomial.X - Polynomial.C r)) := by simp
      rw [hf_eq]
      exact hmulJ
    · apply Ideal.span_le.2
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hroot
  have hQeqprime (q : ℕ) (r : ℤ)
      (hroot : Polynomial.X - Polynomial.C r ∈ Q)
      (hcon : Q.comap Polynomial.C = Ideal.span {(q : ℤ)}) :
      Q = Ideal.span {Polynomial.C (q : ℤ), Polynomial.X - Polynomial.C r} := by
    let M : Ideal IntPolynomial :=
      Ideal.span {Polynomial.C (q : ℤ), Polynomial.X - Polynomial.C r}
    apply le_antisymm
    · intro f hf
      have hmul : (Polynomial.X - Polynomial.C r) *
          (f /ₘ (Polynomial.X - Polynomial.C r)) ∈ Q :=
        Q.mul_mem_right _ hroot
      have hdecomp : Polynomial.C (f.eval r) +
          (Polynomial.X - Polynomial.C r) *
            (f /ₘ (Polynomial.X - Polynomial.C r)) = f := by
        rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval f r]
        exact Polynomial.modByMonic_add_div f (Polynomial.X - Polynomial.C r)
      have hconst : Polynomial.C (f.eval r) ∈ Q := by
        have hsub := Q.sub_mem hf hmul
        have heq : f - (Polynomial.X - Polynomial.C r) *
            (f /ₘ (Polynomial.X - Polynomial.C r)) = Polynomial.C (f.eval r) := by
          calc
            f - (Polynomial.X - Polynomial.C r) *
                (f /ₘ (Polynomial.X - Polynomial.C r)) =
                (Polynomial.C (f.eval r) +
                  (Polynomial.X - Polynomial.C r) *
                    (f /ₘ (Polynomial.X - Polynomial.C r))) -
                  (Polynomial.X - Polynomial.C r) *
                    (f /ₘ (Polynomial.X - Polynomial.C r)) :=
              congrArg (fun t : IntPolynomial => t -
                (Polynomial.X - Polynomial.C r) *
                  (f /ₘ (Polynomial.X - Polynomial.C r))) hdecomp.symm
            _ = Polynomial.C (f.eval r) := add_sub_cancel_right _ _
        rw [heq] at hsub
        exact hsub
      have heval : f.eval r ∈ Ideal.span {(q : ℤ)} := by
        rw [← hcon]
        exact hconst
      have hconstM : Polynomial.C (f.eval r) ∈ M := by
        rcases Ideal.mem_span_singleton.mp heval with ⟨c, hc⟩
        rw [hc, map_mul]
        exact M.mul_mem_right _ (Ideal.subset_span (by simp))
      have hmulM : (Polynomial.X - Polynomial.C r) *
          (f /ₘ (Polynomial.X - Polynomial.C r)) ∈ M := by
        exact M.mul_mem_right _ (Ideal.subset_span (by simp))
      rw [← hdecomp]
      exact M.add_mem hconstM hmulM
    · apply Ideal.span_le.2
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · have hqmem : (q : ℤ) ∈ Q.comap Polynomial.C := by
          rw [hcon]
          exact Ideal.subset_span (by simp)
        exact hqmem
      · exact hroot
  have hmaproot (r : ℤ) :
      Ideal.map intQuadraticQuotientMap
          (Ideal.span ({Polynomial.X - Polynomial.C r} : Set IntPolynomial)) =
        intQuadraticRootIdeal r := by
    simp [intQuadraticRootIdeal, Ideal.map_span]
  have hmapprime (q : ℕ) (r : ℤ) :
      Ideal.map intQuadraticQuotientMap
          (Ideal.span {Polynomial.C (q : ℤ), Polynomial.X - Polynomial.C r}) =
        intQuadraticPrimeIdeal q r := by
    rw [Ideal.map_span]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro ⟨x, (rfl | rfl), h⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact ⟨Polynomial.C q, Or.inl rfl, h.symm⟩
      · exact ⟨Polynomial.X - Polynomial.C r, Or.inr rfl, h.symm⟩
  rcases (Ideal.isPrime_int_iff.mp (by
    simpa [hconQ] using hQprime.comap Polynomial.C)) with hzero | ⟨q, hq, hqcon⟩
  · have hcon : Q.comap Polynomial.C = ⊥ := hconQ.trans hzero
    rcases hQprime.mem_or_mem hfactor_mem with hroot | hroot
    · left
      calc
        p.asIdeal = Ideal.map intQuadraticQuotientMap Q :=
          (Ideal.map_comap_of_surjective intQuadraticQuotientMap
            Ideal.Quotient.mk_surjective p.asIdeal).symm
        _ = intQuadraticRootIdeal 2 := by rw [hQeqroot 2 hroot hcon, hmaproot]
    · right
      left
      have hroot' : Polynomial.X - Polynomial.C (-2 : ℤ) ∈ Q := by
        simpa [sub_eq_add_neg] using hroot
      calc
        p.asIdeal = Ideal.map intQuadraticQuotientMap Q :=
          (Ideal.map_comap_of_surjective intQuadraticQuotientMap
            Ideal.Quotient.mk_surjective p.asIdeal).symm
        _ = intQuadraticRootIdeal (-2) := by
          rw [hQeqroot (-2) hroot' hcon, hmaproot]
  · have hcon : Q.comap Polynomial.C = Ideal.span {(q : ℤ)} := hconQ.trans hqcon
    by_cases hq2 : q = 2
    · subst q
      have hroot0 : Polynomial.X - Polynomial.C (0 : ℤ) ∈ Q := by
        have hC : Polynomial.C (2 : ℤ) ∈ Q := by
          have hqmem : (2 : ℤ) ∈ Q.comap Polynomial.C := by
            rw [hcon]
            exact Ideal.subset_span (by simp)
          exact hqmem
        rcases hQprime.mem_or_mem hfactor_mem with hroot | hroot
        · have := Q.add_mem hroot hC
          have heq : (Polynomial.X - Polynomial.C (2 : ℤ)) +
              Polynomial.C (2 : ℤ) = Polynomial.X := by ring
          rw [heq] at this
          simpa using this
        · have := Q.sub_mem hroot hC
          have heq : (Polynomial.X + Polynomial.C (2 : ℤ)) -
              Polynomial.C (2 : ℤ) = Polynomial.X := by ring
          rw [heq] at this
          simpa using this
      right
      right
      left
      calc
        p.asIdeal = Ideal.map intQuadraticQuotientMap Q :=
          (Ideal.map_comap_of_surjective intQuadraticQuotientMap
            Ideal.Quotient.mk_surjective p.asIdeal).symm
        _ = intQuadraticPrimeIdeal 2 0 := by
          rw [hQeqprime 2 0 hroot0 hcon, hmapprime]
    · right
      right
      right
      refine ⟨q, hq, ?_, ?_⟩
      · exact lt_of_le_of_ne hq.two_le (Ne.symm hq2)
      rcases hQprime.mem_or_mem hfactor_mem with hroot | hroot
      · left
        calc
          p.asIdeal = Ideal.map intQuadraticQuotientMap Q :=
            (Ideal.map_comap_of_surjective intQuadraticQuotientMap
              Ideal.Quotient.mk_surjective p.asIdeal).symm
          _ = intQuadraticPrimeIdeal q 2 := by
            rw [hQeqprime q 2 hroot hcon, hmapprime]
      · right
        have hroot' : Polynomial.X - Polynomial.C (-2 : ℤ) ∈ Q := by
          simpa [sub_eq_add_neg] using hroot
        calc
          p.asIdeal = Ideal.map intQuadraticQuotientMap Q :=
            (Ideal.map_comap_of_surjective intQuadraticQuotientMap
              Ideal.Quotient.mk_surjective p.asIdeal).symm
          _ = intQuadraticPrimeIdeal q (-2) := by
            rw [hQeqprime q (-2) hroot' hcon, hmapprime]

/-! ## `Spec(ℤ[x])` -/

abbrev IntPolynomialMod (q : ℕ) := ℤ ⧸ Ideal.span {(q : ℤ)}

/-- Reduction of an integer polynomial modulo the principal ideal `(q)`. -/
def intPolynomialReduction (q : ℕ) (f : IntPolynomial) : Polynomial (IntPolynomialMod q) :=
  Polynomial.map (Ideal.Quotient.mk (Ideal.span {(q : ℤ)})) f

/-- The prime ideal `(q)` in `ℤ[x]`. -/
def intPolynomialPrimeIdeal (q : ℕ) : Ideal IntPolynomial :=
  Ideal.span {Polynomial.C (q : ℤ)}

/-- The ideal `(q, f)` in `ℤ[x]`. -/
def intPolynomialPrimeAt (q : ℕ) (f : IntPolynomial) : Ideal IntPolynomial :=
  Ideal.span {Polynomial.C (q : ℤ), f}

/-- The condition on a polynomial lift used in the residue-characteristic case. -/
def IsIntegerPolynomialLift (q : ℕ) (f : IntPolynomial) : Prop :=
  Irreducible f ∧ Irreducible (intPolynomialReduction q f)

theorem int_polynomial_isUFD : UniqueFactorizationMonoid IntPolynomial := by
  infer_instance

theorem int_polynomial_isNoetherian : IsNoetherianRing IntPolynomial := by
  infer_instance

theorem int_polynomial_irreducible_maps_to_ratios
    (f : IntPolynomial) (hfdeg : 0 < f.natDegree) (hf : Irreducible f) :
    Irreducible (Polynomial.map (Int.castRingHom ℚ) f) := by
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (hf.isPrimitive (Nat.ne_of_gt hfdeg))).mp hf

theorem int_polynomial_prime_contraction_isPrime (P : Ideal IntPolynomial)
    (hP : P.IsPrime) :
    (P.comap Polynomial.C).IsPrime := by
  exact Ideal.comap_isPrime Polynomial.C P

theorem int_polynomial_irreducible_span_isPrime (f : IntPolynomial)
    (hf : Irreducible f) :
    (Ideal.span {f}).IsPrime := by
  exact (Ideal.span_singleton_prime hf.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)

theorem int_polynomial_prime_ideal_candidates_isPrime (q : ℕ) (hq : Nat.Prime q) :
    (intPolynomialPrimeIdeal q).IsPrime ∧
      ∀ f : IntPolynomial, IsIntegerPolynomialLift q f →
        (intPolynomialPrimeAt q f).IsPrime := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  constructor
  · let I : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
    have hI : I.IsMaximal := by
      exact Int.ideal_span_isMaximal_of_prime q
    have hmap :
        Ideal.map Polynomial.C I = intPolynomialPrimeIdeal q := by
      simp [I, intPolynomialPrimeIdeal, Ideal.map_span]
    have hdom :
        IsDomain (IntPolynomial ⧸ Ideal.map Polynomial.C I) :=
      Ideal.isDomain_map_C_quotient hI.isPrime
    rw [hmap] at hdom
    exact (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  · intro f hf
    rcases hf with ⟨hf, hfred⟩
    let I : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
    have hI : I.IsMaximal := by
      exact Int.ideal_span_isMaximal_of_prime q
    let : I.IsMaximal := hI
    let : Field (ℤ ⧸ I) := Ideal.Quotient.field I
    let M : Ideal IntPolynomial := Ideal.map Polynomial.C I
    let ePoly := I.polynomialQuotientEquivQuotientPolynomial
    have hfred' : (Ideal.span {intPolynomialReduction q f}).IsPrime := by
      exact (Ideal.span_singleton_prime hfred.ne_zero).mpr
        (UniqueFactorizationMonoid.irreducible_iff_prime.mp hfred)
    have hmap :
        Ideal.map (ePoly : Polynomial (ℤ ⧸ I) →+* (IntPolynomial ⧸ M))
            (Ideal.span {intPolynomialReduction q f}) =
          Ideal.span {Ideal.Quotient.mk M f} := by
      rw [Ideal.map_span, Set.image_singleton]
      have hgen : (ePoly : Polynomial (ℤ ⧸ I) →+* (IntPolynomial ⧸ M))
          (intPolynomialReduction q f) =
          Ideal.Quotient.mk M f := by
        change ePoly (Polynomial.map (Ideal.Quotient.mk I) f) =
          Ideal.Quotient.mk M f
        exact Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk I f
      simp only [hgen]
    have hKprime :
        (Ideal.span {Ideal.Quotient.mk M f}).IsPrime := by
      rw [← hmap]
      exact Ideal.map_isPrime_of_surjective ePoly.surjective
        (by simp)
    let : IsDomain ((IntPolynomial ⧸ M) ⧸
        Ideal.span {Ideal.Quotient.mk M f}) :=
      (Ideal.Quotient.isDomain_iff_prime _).mpr hKprime
    have hKmap :
        Ideal.map (Ideal.Quotient.mk M) (Ideal.span {f}) =
          Ideal.span {Ideal.Quotient.mk M f} := by
      rw [Ideal.map_span]
      simp
    let : IsDomain ((IntPolynomial ⧸ M) ⧸
        Ideal.map (Ideal.Quotient.mk M) (Ideal.span {f})) := by
      rw [hKmap]
      infer_instance
    have hdom : IsDomain (IntPolynomial ⧸ (M ⊔ Ideal.span {f})) := by
      exact (DoubleQuot.quotQuotEquivQuotSup M (Ideal.span {f})).symm.toMulEquiv.isDomain _
    have hsup : M ⊔ Ideal.span {f} = intPolynomialPrimeAt q f := by
      simp only [M, intPolynomialPrimeAt, I, Ideal.map_span, Set.image_singleton]
      change (Submodule.span IntPolynomial {Polynomial.C (q : ℤ)} ⊔
          Submodule.span IntPolynomial {f}) =
          Submodule.span IntPolynomial {Polynomial.C (q : ℤ), f}
      rw [← Submodule.span_union]
      apply congrArg (Submodule.span IntPolynomial)
      ext z
      simp [or_comm]
    rw [hsup] at hdom
    exact (Ideal.Quotient.isDomain_iff_prime _).mp hdom

/-- The source classification, corrected to include the zero prime in each
PID fiber and the zero prime over the generic point. -/
theorem prime_ideal_int_polynomial_cases (P : Ideal IntPolynomial) (hP : P.IsPrime) :
    ((P.comap Polynomial.C = ⊥ ∧
        (P = ⊥ ∨ ∃ f : IntPolynomial, 0 < f.natDegree ∧ Irreducible f ∧
          P = Ideal.span {f})) ∨
      (∃ q : ℕ, Nat.Prime q ∧ P.comap Polynomial.C = Ideal.span {(q : ℤ)} ∧
        (P = intPolynomialPrimeIdeal q ∨
          ∃ f : IntPolynomial, 0 < f.natDegree ∧ IsIntegerPolynomialLift q f ∧
            P = intPolynomialPrimeAt q f))) := by
  letI : UniqueFactorizationMonoid IntPolynomial := int_polynomial_isUFD
  have hfinite : P ≠ (⊥ : Ideal IntPolynomial) →
      ∃ n : ℕ, ∃ f : Fin n → IntPolynomial,
        (∀ i, Irreducible (f i)) ∧ P = Ideal.span (Set.range f) := by
    intro hPbot
    have hfactor : ∀ a : IntPolynomial, a ∈ P → a ≠ 0 →
        ∃ z : IntPolynomial, z ∈ P ∧ Irreducible z ∧ z ∣ a := by
      intro a
      refine WfDvdMonoid.induction_on_irreducible a ?_ ?_ ?_
      · intro _ ha
        exact (ha rfl).elim
      · intro u hu hmem _
        exact (hP.ne_top (P.eq_top_of_isUnit_mem hmem hu)).elim
      · intro b i hb0 hi ih hmem _
        rcases hP.mem_or_mem hmem with hiP | hbP
        · exact ⟨i, hiP, hi, ⟨b, rfl⟩⟩
        · obtain ⟨z, hzP, hz, hzb⟩ := ih hbP hb0
          rcases hzb with ⟨c, hc⟩
          exact ⟨z, hzP, hz, ⟨i * c, by
            rw [hc]
            simp [mul_assoc, mul_left_comm, mul_comm]⟩⟩
    obtain ⟨n, s, hs⟩ :=
      (Submodule.fg_iff_exists_fin_generating_family.mp
        (Ideal.fg_of_isNoetherianRing P))
    have hsmem : ∀ i, s i ∈ P := by
      intro i
      rw [← hs]
      exact Ideal.subset_span ⟨i, rfl⟩
    have hnonzero : ∃ a : IntPolynomial, a ∈ P ∧ a ≠ 0 := by
      by_contra h
      apply hPbot
      apply le_antisymm
      · intro a ha
        by_contra ha0
        exact h ⟨a, ha, ha0⟩
      · exact bot_le
    obtain ⟨a, haP, ha0⟩ := hnonzero
    have hchoose : ∀ i : Fin n, ∃ z : IntPolynomial, z ∈ P ∧ Irreducible z ∧
        (z ∣ s i ∨ (s i = 0 ∧ z ∣ a)) := by
      intro i
      by_cases hi : s i = 0
      · obtain ⟨z, hzP, hz, hza⟩ := hfactor a haP ha0
        exact ⟨z, hzP, hz, Or.inr ⟨hi, hza⟩⟩
      · obtain ⟨z, hzP, hz, hzs⟩ := hfactor (s i) (hsmem i) hi
        exact ⟨z, hzP, hz, Or.inl hzs⟩
    let f : Fin n → IntPolynomial := fun i => (hchoose i).choose
    have hf_spec (i : Fin n) : f i ∈ P ∧ Irreducible (f i) ∧
        (f i ∣ s i ∨ (s i = 0 ∧ f i ∣ a)) :=
      (hchoose i).choose_spec
    refine ⟨n, f, fun i => (hf_spec i).2.1, ?_⟩
    apply le_antisymm
    · rw [← hs]
      apply Ideal.span_le.2
      rintro _ ⟨i, rfl⟩
      rcases (hf_spec i).2.2 with hdiv | ⟨hi, _⟩
      · rcases hdiv with ⟨c, hc⟩
        rw [hc]
        exact (Ideal.span (Set.range f)).mul_mem_right c
          (Ideal.subset_span ⟨i, rfl⟩)
      · simp [hi]
    · apply Ideal.span_le.2
      rintro _ ⟨i, rfl⟩
      exact (hf_spec i).1
  have hconprime : (P.comap Polynomial.C).IsPrime :=
    int_polynomial_prime_contraction_isPrime P hP
  have hpair (f g : IntPolynomial) (hfdeg : 0 < f.natDegree)
      (hgdeg : 0 < g.natDegree) (hf : Irreducible f) (hg : Irreducible g)
      (hnassoc : ¬Associated f g) :
      ∃ m : ℤ, m ≠ 0 ∧ Polynomial.C m ∈ Ideal.span {f, g} := by
    let fQ : Polynomial ℚ := Polynomial.map (Int.castRingHom ℚ) f
    let gQ : Polynomial ℚ := Polynomial.map (Int.castRingHom ℚ) g
    have hfQ : Irreducible fQ := by
      change Irreducible (Polynomial.map (Int.castRingHom ℚ) f)
      exact int_polynomial_irreducible_maps_to_ratios f hfdeg hf
    have hgQ : Irreducible gQ := by
      change Irreducible (Polynomial.map (Int.castRingHom ℚ) g)
      exact int_polynomial_irreducible_maps_to_ratios g hgdeg hg
    have hassocQ : ¬Associated (Polynomial.map (Int.castRingHom ℚ) f)
        (Polynomial.map (Int.castRingHom ℚ) g) := by
      intro h
      apply hnassoc
      apply associated_of_dvd_dvd
      · exact (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast f g
          (hf.isPrimitive (Nat.ne_of_gt hfdeg))).mpr h.dvd
      · exact (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast g f
          (hg.isPrimitive (Nat.ne_of_gt hgdeg))).mpr h.dvd'
    have hcopQ : IsCoprime fQ gQ := by
      rcases hfQ.isCoprime_or_dvd gQ with h | h
      · exact h
      · exact (hassocQ (hfQ.associated_of_dvd hgQ h)).elim
    have hresQ0 : Polynomial.resultant fQ gQ ≠ 0 :=
      Polynomial.resultant_ne_zero fQ gQ hcopQ
    have hresQ : Polynomial.resultant fQ gQ f.natDegree g.natDegree ≠ 0 := by
      simpa [fQ, gQ, Polynomial.natDegree_map_eq_of_injective
        (f := Int.castRingHom ℚ) Int.cast_injective] using hresQ0
    have hresZ : Polynomial.resultant f g f.natDegree g.natDegree ≠ 0 := by
      intro hres
      apply hresQ
      rw [Polynomial.resultant_map_map, hres]
      simp
    obtain ⟨a, b, ha, hb, hab⟩ :=
      Polynomial.exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl
        (Or.inl (Nat.ne_of_gt hfdeg))
    refine ⟨Polynomial.resultant f g f.natDegree g.natDegree, hresZ, ?_⟩
    rw [← hab]
    exact (Ideal.span {f, g}).add_mem
      ((Ideal.span {f, g}).mul_mem_right _ (Ideal.subset_span (by simp)))
      ((Ideal.span {f, g}).mul_mem_right _ (Ideal.subset_span (by simp)))
  rcases Ideal.isPrime_int_iff.mp hconprime with hzero | ⟨q, hq, hqcon⟩
  · by_cases hPbot : P = ⊥
    · exact Or.inl ⟨hzero, Or.inl hPbot⟩
    · obtain ⟨n, f, hf, hPspan⟩ := hfinite hPbot
      have hmem : ∀ i, f i ∈ P := by
        intro i
        rw [hPspan]
        exact Ideal.subset_span ⟨i, rfl⟩
      have hdeg : ∀ i, 0 < (f i).natDegree := by
        intro i
        by_contra hi
        have hi0 : (f i).natDegree = 0 := Nat.eq_zero_of_not_pos hi
        have hfC : f i = Polynomial.C ((f i).coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero hi0
        have hc : (f i).coeff 0 ∈ P.comap Polynomial.C := by
          change Polynomial.C ((f i).coeff 0) ∈ P
          rw [← hfC]
          exact hmem i
        rw [hzero] at hc
        have hc0 : (f i).coeff 0 = 0 := by simpa using hc
        have hfi0 : f i = 0 := by
          calc
            f i = Polynomial.C ((f i).coeff 0) := hfC
            _ = Polynomial.C 0 := by rw [hc0]
            _ = 0 := Polynomial.C_0
        exact (hf i).ne_zero hfi0
      have hn : 0 < n := by
        by_contra hn
        have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        apply hPbot
        haveI : IsEmpty (Fin n) := hn0 ▸ inferInstance
        have hrange : Set.range f = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro x hx
          rcases hx with ⟨i, rfl⟩
          exact isEmptyElim i
        rw [hPspan, hrange]
        exact Ideal.span_empty
      let i₀ : Fin n := ⟨0, hn⟩
      have hassoc : ∀ i, Associated (f i₀) (f i) := by
        intro i
        by_contra hna
        obtain ⟨m, hm0, hmp⟩ := hpair (f i₀) (f i) (hdeg i₀) (hdeg i)
          (hf i₀) (hf i) hna
        have hspan : Ideal.span {f i₀, f i} ≤ P := by
          apply Ideal.span_le.2
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact hmem i₀
          · exact hmem i
        have hmp' : m ∈ P.comap Polynomial.C := by
          change Polynomial.C m ∈ P
          exact hspan hmp
        rw [hzero] at hmp'
        exact hm0 (by simpa using hmp')
      have hPprincipal : P = Ideal.span {f i₀} := by
        apply le_antisymm
        · rw [hPspan]
          apply Ideal.span_le.2
          rintro _ ⟨i, rfl⟩
          exact Ideal.mem_span_singleton.mpr (hassoc i).dvd
        · apply Ideal.span_le.2
          intro z hz
          rw [Set.mem_singleton_iff.mp hz]
          exact hmem i₀
      exact Or.inl ⟨hzero, Or.inr ⟨f i₀, hdeg i₀, hf i₀, hPprincipal⟩⟩
  · let I : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
    letI : Fact (Nat.Prime q) := ⟨hq⟩
    have hI : I.IsMaximal := by
      exact Int.ideal_span_isMaximal_of_prime q
    let : I.IsMaximal := hI
    let : Field (ℤ ⧸ I) := Ideal.Quotient.field I
    let M : Ideal IntPolynomial := Ideal.map Polynomial.C I
    have hM : M = Ideal.span {Polynomial.C (q : ℤ)} := by
      simp [M, I, Ideal.map_span]
    have hqmem : Polynomial.C (q : ℤ) ∈ P := by
      have hqmem' : (q : ℤ) ∈ P.comap Polynomial.C := by
        rw [hqcon]
        exact Ideal.subset_span (by simp)
      change Polynomial.C (q : ℤ) ∈ P at hqmem'
      exact hqmem'
    have hMle : M ≤ P := by
      rw [hM]
      apply Ideal.span_le.2
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hqmem
    let π : IntPolynomial →+* (IntPolynomial ⧸ M) := Ideal.Quotient.mk M
    let Pbar : Ideal (IntPolynomial ⧸ M) := Ideal.map π P
    have hPbarprime : Pbar.IsPrime := by
      letI : P.IsPrime := hP
      apply Ideal.map_isPrime_of_surjective (f := π) π.surjective
      change RingHom.ker π ≤ P
      change RingHom.ker (Ideal.Quotient.mk M) ≤ P
      rw [Ideal.mk_ker]
      exact hMle
    let ePoly := I.polynomialQuotientEquivQuotientPolynomial
    let Pfield : Ideal (Polynomial (ℤ ⧸ I)) :=
      Pbar.comap (ePoly : Polynomial (ℤ ⧸ I) →+* (IntPolynomial ⧸ M))
    have hPfield : Pfield.IsPrime := by
      exact Ideal.comap_isPrime (ePoly : Polynomial (ℤ ⧸ I) →+*
        (IntPolynomial ⧸ M)) Pbar
    by_cases hPfieldbot : Pfield = ⊥
    · have hPbarbot : Pbar = ⊥ := by
        calc
          Pbar = Ideal.map (ePoly : Polynomial (ℤ ⧸ I) →+*
              (IntPolynomial ⧸ M)) Pfield :=
            (Ideal.map_comap_of_surjective (ePoly : Polynomial (ℤ ⧸ I) →+*
              (IntPolynomial ⧸ M)) ePoly.surjective Pbar).symm
          _ = ⊥ := by rw [hPfieldbot]; simp
      have hPM : P = M := by
        apply le_antisymm
        · intro x hx
          have hxbar : π x ∈ Pbar := Ideal.mem_map_of_mem π hx
          rw [hPbarbot] at hxbar
          have hxzero : π x = 0 := by simpa using hxbar
          exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero
        · exact hMle
      exact Or.inr ⟨q, hq, hqcon, Or.inl (by
        calc
          P = M := hPM
          _ = intPolynomialPrimeIdeal q := by
            simpa [intPolynomialPrimeIdeal] using hM)⟩
    · obtain ⟨g, hg, hPg⟩ :=
        (Ideal.isPrime_iff_of_isPrincipalIdealRing hPfieldbot).mp hPfield
      have hLc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg.ne_zero
      let g' : Polynomial (ℤ ⧸ I) := Polynomial.C (g.leadingCoeff)⁻¹ * g
      have hg'monic : g'.Monic := by
        apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
        exact inv_mul_cancel₀ hLc
      have hgg' : Associated g g' := by
        apply associated_unit_mul_right g
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hLc))
      have hg'prime : Prime g' := hgg'.prime hg
      have hg'irr : Irreducible g' := hg'prime.irreducible
      have hPfieldspan : Pfield = Ideal.span {g'} := by
        calc
          Pfield = Ideal.span {g} := hPg
          _ = Ideal.span {g'} :=
            Ideal.span_singleton_eq_span_singleton.mpr hgg'
      have hglifts : g' ∈ Polynomial.lifts (Ideal.Quotient.mk I) := by
        exact Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective g'
      obtain ⟨f, hmapf, hdegf, hfmonic⟩ :=
        Polynomial.lifts_and_natDegree_eq_and_monic hglifts hg'monic
      have hfprime : Irreducible f := by
        apply Polynomial.Monic.irreducible_of_irreducible_map
          (Ideal.Quotient.mk I) f hfmonic
        rw [hmapf]
        exact hg'irr
      have hfdeg : 0 < f.natDegree := by
        rw [hdegf]
        exact Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_irreducible hg'irr)
      have hfred : Irreducible (intPolynomialReduction q f) := by
        change Irreducible (Polynomial.map (Ideal.Quotient.mk I) f)
        rw [hmapf]
        exact hg'irr
      have heq : (ePoly : Polynomial (ℤ ⧸ I) →+* (IntPolynomial ⧸ M)) g' = π f := by
        rw [← hmapf]
        exact Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk I f
      have hPbarspan : Pbar = Ideal.span {π f} := by
        calc
          Pbar = Ideal.map (ePoly : Polynomial (ℤ ⧸ I) →+*
              (IntPolynomial ⧸ M)) Pfield :=
            (Ideal.map_comap_of_surjective (ePoly : Polynomial (ℤ ⧸ I) →+*
              (IntPolynomial ⧸ M)) ePoly.surjective Pbar).symm
          _ = Ideal.map (ePoly : Polynomial (ℤ ⧸ I) →+*
              (IntPolynomial ⧸ M)) (Ideal.span {g'}) := by rw [hPfieldspan]
          _ = Ideal.span {(ePoly : Polynomial (ℤ ⧸ I) →+*
              (IntPolynomial ⧸ M)) g'} := by simp [Ideal.map_span]
          _ = Ideal.span {π f} := by rw [heq]
      let Cnd : Ideal IntPolynomial := intPolynomialPrimeAt q f
      have hmapCnd : Ideal.map π Cnd = Ideal.span {π f} := by
        change Ideal.map π (intPolynomialPrimeAt q f) = Ideal.span {π f}
        rw [intPolynomialPrimeAt, Ideal.map_span]
        have hCzero : π (Polynomial.C (q : ℤ)) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem]
          rw [hM]
          exact Ideal.subset_span (by simp)
        have himage : π '' ({Polynomial.C (q : ℤ), f} : Set IntPolynomial) =
            ({0, π f} : Set (IntPolynomial ⧸ M)) := by
          ext z
          simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨x, (rfl | rfl), h⟩
            · rw [hCzero] at h
              exact Or.inl h.symm
            · exact Or.inr h.symm
          · intro hz
            rcases hz with hz | hz
            · exact ⟨Polynomial.C (q : ℤ), Or.inl rfl, by rw [hCzero]; exact hz.symm⟩
            · exact ⟨f, Or.inr rfl, hz.symm⟩
        rw [himage]
        exact Ideal.span_insert_zero
      have hCndM : M ≤ Cnd := by
        rw [hM]
        apply Ideal.span_le.2
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact Ideal.subset_span (by simp [Cnd, intPolynomialPrimeAt])
      have hmap_eq : Ideal.map π P = Ideal.map π Cnd := by
        calc
          Ideal.map π P = Pbar := rfl
          _ = Ideal.span {π f} := hPbarspan
          _ = Ideal.map π Cnd := hmapCnd.symm
      have hker : RingHom.ker π = M := by
        change RingHom.ker (Ideal.Quotient.mk M) = M
        exact Ideal.mk_ker
      have hsups :=
        (Ideal.map_eq_iff_sup_ker_eq_of_surjective π π.surjective).mp hmap_eq
      have hkP : RingHom.ker π ≤ P := by rw [hker]; exact hMle
      have hkCnd : RingHom.ker π ≤ Cnd := by rw [hker]; exact hCndM
      have hPCnd : P = Cnd := by
        calc
          P = P ⊔ RingHom.ker π := (sup_eq_left.mpr hkP).symm
          _ = Cnd ⊔ RingHom.ker π := hsups
          _ = Cnd := sup_eq_left.mpr hkCnd
      exact Or.inr ⟨q, hq, hqcon, Or.inr ⟨f, hfdeg,
        ⟨hfprime, hfred⟩, hPCnd⟩⟩

theorem int_polynomial_prime_ideal_is_zero_or_principal (P : Ideal IntPolynomial)
    (hP : P.IsPrime) (hcontraction : P.comap Polynomial.C = ⊥) :
    P = ⊥ ∨ ∃ f : IntPolynomial, 0 < f.natDegree ∧ Irreducible f ∧
      P = Ideal.span {f} := by
  rcases prime_ideal_int_polynomial_cases P hP with hzero | hq
  · exact hzero.2
  · rcases hq with ⟨q, hq, hqcon, hcases⟩
    exfalso
    have hspan : (Ideal.span {(q : ℤ)} : Ideal ℤ) = ⊥ := by
      rw [← hqcon, hcontraction]
    exact (Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast hq.ne_zero)) hspan

theorem int_polynomial_prime_ideal_over_prime_is_zero_or_principal
    (P : Ideal IntPolynomial) (hP : P.IsPrime) (q : ℕ) (hq : Nat.Prime q)
    (hcontraction : P.comap Polynomial.C = Ideal.span {(q : ℤ)}) :
    P = intPolynomialPrimeIdeal q ∨
      ∃ f : IntPolynomial, 0 < f.natDegree ∧ IsIntegerPolynomialLift q f ∧
        P = intPolynomialPrimeAt q f := by
  rcases prime_ideal_int_polynomial_cases P hP with hzero | hq'
  · exfalso
    have hspan : (⊥ : Ideal ℤ) = Ideal.span {(q : ℤ)} :=
      hzero.1.symm.trans hcontraction
    have hqmem : (q : ℤ) ∈ (⊥ : Ideal ℤ) := by
      rw [hspan]
      exact Ideal.subset_span (by simp)
    have hqzero : (q : ℤ) = 0 := by simpa using hqmem
    have hqne : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
    exact hqne hqzero
  · obtain ⟨q', hq', hqcon', hcases⟩ := hq'
    have hqeq : q' = q := by
      have hspan : Ideal.span {(q' : ℤ)} = Ideal.span {(q : ℤ)} :=
        hqcon'.symm.trans hcontraction
      have hq'mem : (q' : ℤ) ∈ Ideal.span {(q : ℤ)} := by
        rw [← hspan]
        exact Ideal.subset_span (by simp)
      have hqmem : (q : ℤ) ∈ Ideal.span {(q' : ℤ)} := by
        rw [hspan]
        exact Ideal.subset_span (by simp)
      have hdiv : q ∣ q' := Int.natCast_dvd_natCast.mp
        (Ideal.mem_span_singleton.mp hq'mem)
      have hdiv' : q' ∣ q := Int.natCast_dvd_natCast.mp
        (Ideal.mem_span_singleton.mp hqmem)
      exact Nat.dvd_antisymm hdiv' hdiv
    subst q'
    exact hcases

/-! ## `Spec(k[x,y])` -/

/-- A concrete nested-polynomial model of the bivariate polynomial ring `k[x,y]`. -/
abbrev BivariatePolynomial (k : Type*) [Field k] := Polynomial (Polynomial k)

def bivariateX {k : Type*} [Field k] : BivariatePolynomial k :=
  Polynomial.C Polynomial.X

def bivariateY {k : Type*} [Field k] : BivariatePolynomial k :=
  Polynomial.X

def bivariateUnivariateIdeal {k : Type*} [Field k] (p : Polynomial k) :
    Ideal (BivariatePolynomial k) :=
  Ideal.span {Polynomial.C p}

abbrev BivariateQuotient {k : Type*} [Field k] (p : Polynomial k) :=
  BivariatePolynomial k ⧸ bivariateUnivariateIdeal p

def bivariateTwoGeneratorIdeal {k : Type*} [Field k]
    (f g : BivariatePolynomial k) : Ideal (BivariatePolynomial k) :=
  Ideal.span {f, g}

def BivariateQuotientIrreducible {k : Type*} [Field k]
    (p : Polynomial k) (f : BivariatePolynomial k) : Prop :=
  Irreducible (Ideal.Quotient.mk (bivariateUnivariateIdeal p) f)

theorem bivariate_zero_isPrime (k : Type*) [Field k] :
    (⊥ : Ideal (BivariatePolynomial k)).IsPrime := by
  infer_instance

theorem bivariate_isNoetherian (k : Type*) [Field k] :
    IsNoetherianRing (BivariatePolynomial k) := by
  infer_instance

theorem bivariate_isUFD (k : Type*) [Field k] :
    UniqueFactorizationMonoid (BivariatePolynomial k) := by
  infer_instance

theorem bivariate_irreducible_span_isPrime (k : Type*) [Field k]
    (f : BivariatePolynomial k) (hf : Irreducible f) :
    (Ideal.span {f}).IsPrime := by
  exact (Ideal.span_singleton_prime hf.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)

theorem bivariate_univariate_span_isPrime (k : Type*) [Field k]
    (p : Polynomial k) (hp : Irreducible p) :
    (bivariateUnivariateIdeal p).IsPrime := by
  apply (Ideal.span_singleton_prime (by simp [hp.ne_zero])).mpr
  exact Polynomial.prime_C_iff.mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp)

theorem bivariate_prime_has_finite_irreducible_generators
    (k : Type*) [Field k] (P : Ideal (BivariatePolynomial k)) (hP : P.IsPrime)
    (hnprincipal : ∀ f, P ≠ Ideal.span ({f} : Set (BivariatePolynomial k))) :
    ∃ n : ℕ, ∃ f : Fin n → BivariatePolynomial k,
      (∀ i, Irreducible (f i)) ∧ P = Ideal.span (Set.range f) := by
  let R := BivariatePolynomial k
  letI : UniqueFactorizationMonoid R := bivariate_isUFD k
  have hPbot : P ≠ (⊥ : Ideal R) := by
    intro h
    apply hnprincipal 0
    simpa [h]
  have hfactor : ∀ a : R, a ∈ P → a ≠ 0 →
      ∃ z : R, z ∈ P ∧ Irreducible z ∧ z ∣ a := by
    intro a
    refine WfDvdMonoid.induction_on_irreducible a ?_ ?_ ?_
    · intro _ ha
      exact (ha rfl).elim
    · intro u hu hmem _
      exact (hP.ne_top (P.eq_top_of_isUnit_mem hmem hu)).elim
    · intro b i hb0 hi ih hmem _
      rcases hP.mem_or_mem hmem with hiP | hbP
      · exact ⟨i, hiP, hi, ⟨b, rfl⟩⟩
      · obtain ⟨z, hzP, hz, hzb⟩ := ih hbP hb0
        rcases hzb with ⟨c, hc⟩
        exact ⟨z, hzP, hz, ⟨i * c, by rw [hc]; simp [mul_assoc, mul_left_comm, mul_comm]⟩⟩
  obtain ⟨n, s, hs⟩ :=
    (Submodule.fg_iff_exists_fin_generating_family.mp
      (Ideal.fg_of_isNoetherianRing P))
  have hsmem : ∀ i, s i ∈ P := by
    intro i
    rw [← hs]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hnonzero : ∃ a : R, a ∈ P ∧ a ≠ 0 := by
    by_contra h
    apply hPbot
    apply le_antisymm
    · intro a ha
      by_contra ha0
      exact h ⟨a, ha, ha0⟩
    · exact bot_le
  obtain ⟨a, haP, ha0⟩ := hnonzero
  have hchoose : ∀ i : Fin n, ∃ z : R, z ∈ P ∧ Irreducible z ∧
      (z ∣ s i ∨ (s i = 0 ∧ z ∣ a)) := by
    intro i
    by_cases hi : s i = 0
    · obtain ⟨z, hzP, hz, hza⟩ := hfactor a haP ha0
      exact ⟨z, hzP, hz, Or.inr ⟨hi, hza⟩⟩
    · obtain ⟨z, hzP, hz, hzs⟩ := hfactor (s i) (hsmem i) hi
      exact ⟨z, hzP, hz, Or.inl hzs⟩
  let f : Fin n → R := fun i => (hchoose i).choose
  have hf_spec (i : Fin n) : f i ∈ P ∧ Irreducible (f i) ∧
      (f i ∣ s i ∨ (s i = 0 ∧ f i ∣ a)) :=
    (hchoose i).choose_spec
  refine ⟨n, f, fun i => (hf_spec i).2.1, ?_⟩
  apply le_antisymm
  · rw [← hs]
    apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    rcases (hf_spec i).2.2 with hdiv | ⟨hi, _⟩
    · rcases hdiv with ⟨c, hc⟩
      rw [hc]
      exact (Ideal.span (Set.range f)).mul_mem_right c
        (Ideal.subset_span ⟨i, rfl⟩)
    · simp [hi]
  · apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    exact (hf_spec i).1

theorem bivariate_pair_intersects_univariate
    (k : Type*) [Field k] (f g : BivariatePolynomial k)
    (hf : Irreducible f) (hg : Irreducible g) (hnassoc : ¬Associated f g) :
    ∃ p : Polynomial k, p ≠ 0 ∧ Polynomial.C p ∈ bivariateTwoGeneratorIdeal f g := by
  let R := Polynomial k
  let K := FractionRing R
  have hres : Polynomial.resultant f g ≠ 0 := by
    intro hres
    have hzero :
        Polynomial.resultant (f.map (algebraMap R K))
          (g.map (algebraMap R K)) = 0 := by
      simpa [Polynomial.resultant_map_map,
        Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R K)] using
        congrArg (algebraMap R K) hres
    by_cases hfd : f.natDegree = 0
    · by_cases hgd : g.natDegree = 0
      · obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hfd
        obtain ⟨b, rfl⟩ := Polynomial.natDegree_eq_zero.mp hgd
        have ha : Irreducible a := by
          rw [irreducible_iff]
          constructor
          · intro ha
            exact hf.not_isUnit (Polynomial.isUnit_C.mpr ha)
          · intro x y hxy
            have hfac : Polynomial.C a = Polynomial.C x * Polynomial.C y := by
              simpa only [Polynomial.C_mul] using congrArg Polynomial.C hxy
            rcases hf.isUnit_or_isUnit hfac with hx | hy
            · exact Or.inl (Polynomial.isUnit_C.mp hx)
            · exact Or.inr (Polynomial.isUnit_C.mp hy)
        have hb : Irreducible b := by
          rw [irreducible_iff]
          constructor
          · intro hb
            exact hg.not_isUnit (Polynomial.isUnit_C.mpr hb)
          · intro x y hxy
            have hfac : Polynomial.C b = Polynomial.C x * Polynomial.C y := by
              simpa only [Polynomial.C_mul] using congrArg Polynomial.C hxy
            rcases hg.isUnit_or_isUnit hfac with hx | hy
            · exact Or.inl (Polynomial.isUnit_C.mp hx)
            · exact Or.inr (Polynomial.isUnit_C.mp hy)
        have hab : IsCoprime a b := by
          apply (ha.coprime_iff_not_dvd).2
          intro hab
          rcases hab with ⟨c, hc⟩
          apply hnassoc
          apply hf.associated_of_dvd hg
          exact ⟨Polynomial.C c, by rw [← Polynomial.C_mul, hc]⟩
        obtain ⟨u, v, huv⟩ := hab
        have hcop :
            IsCoprime (Polynomial.C a : Polynomial R)
              (Polynomial.C b : Polynomial R) := by
          refine ⟨Polynomial.C u, Polynomial.C v, ?_⟩
          simpa only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_1] using
            congrArg Polynomial.C huv
        exact (Polynomial.resultant_eq_zero_iff.mp hzero).2
          (hcop.map (Polynomial.mapRingHom (algebraMap R K)))
      · have hgprim : g.IsPrimitive := hg.isPrimitive hgd
        have hgmap : Irreducible (g.map (algebraMap R K)) :=
          hgprim.irreducible_iff_irreducible_map_fraction_map.mp hg
        have hnotcop :
            ¬ IsCoprime (g.map (algebraMap R K))
              (f.map (algebraMap R K)) := by
          intro hcop
          exact (Polynomial.resultant_eq_zero_iff.mp hzero).2 hcop.symm
        have hdiv : g.map (algebraMap R K) ∣ f.map (algebraMap R K) :=
          (hgmap.dvd_iff_not_isCoprime).2 hnotcop
        have hdiv' : g ∣ f := hgprim.dvd_of_fraction_map_dvd_fraction_map hdiv
        exact hnassoc (hg.associated_of_dvd hf hdiv').symm
    · have hfprim : f.IsPrimitive := hf.isPrimitive hfd
      have hfmap : Irreducible (f.map (algebraMap R K)) :=
        hfprim.irreducible_iff_irreducible_map_fraction_map.mp hf
      have hnotcop :
          ¬ IsCoprime (f.map (algebraMap R K))
            (g.map (algebraMap R K)) := by
        intro hcop
        exact (Polynomial.resultant_eq_zero_iff.mp hzero).2 hcop
      have hdiv : f.map (algebraMap R K) ∣ g.map (algebraMap R K) :=
        (hfmap.dvd_iff_not_isCoprime).2 hnotcop
      have hdiv' : f ∣ g := hfprim.dvd_of_fraction_map_dvd_fraction_map hdiv
      exact hnassoc (hf.associated_of_dvd hg hdiv')
  by_cases hfd : f.natDegree = 0
  · by_cases hgd : g.natDegree = 0
    · obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hfd
      obtain ⟨b, rfl⟩ := Polynomial.natDegree_eq_zero.mp hgd
      have ha : Irreducible a := by
        rw [irreducible_iff]
        constructor
        · intro ha
          exact hf.not_isUnit (Polynomial.isUnit_C.mpr ha)
        · intro x y hxy
          have hfac : Polynomial.C a = Polynomial.C x * Polynomial.C y := by
            simpa only [Polynomial.C_mul] using congrArg Polynomial.C hxy
          rcases hf.isUnit_or_isUnit hfac with hx | hy
          · exact Or.inl (Polynomial.isUnit_C.mp hx)
          · exact Or.inr (Polynomial.isUnit_C.mp hy)
      have hb : Irreducible b := by
        rw [irreducible_iff]
        constructor
        · intro hb
          exact hg.not_isUnit (Polynomial.isUnit_C.mpr hb)
        · intro x y hxy
          have hfac : Polynomial.C b = Polynomial.C x * Polynomial.C y := by
            simpa only [Polynomial.C_mul] using congrArg Polynomial.C hxy
          rcases hg.isUnit_or_isUnit hfac with hx | hy
          · exact Or.inl (Polynomial.isUnit_C.mp hx)
          · exact Or.inr (Polynomial.isUnit_C.mp hy)
      have hab : IsCoprime a b := by
        apply (ha.coprime_iff_not_dvd).2
        intro hab
        rcases hab with ⟨c, hc⟩
        apply hnassoc
        apply hf.associated_of_dvd hg
        exact ⟨Polynomial.C c, by rw [← Polynomial.C_mul, hc]⟩
      obtain ⟨u, v, huv⟩ := hab
      refine ⟨1, one_ne_zero, ?_⟩
      rw [bivariateTwoGeneratorIdeal]
      apply Ideal.mem_span_pair.mpr
      refine ⟨Polynomial.C u, Polynomial.C v, ?_⟩
      simpa only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_1] using
        congrArg Polynomial.C huv
    · obtain ⟨a, b, ha, hb, hab⟩ :=
        Polynomial.exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (Or.inr hgd)
      refine ⟨Polynomial.resultant f g, hres, ?_⟩
      rw [bivariateTwoGeneratorIdeal]
      rw [← hab]
      exact add_mem ((Ideal.span {f, g}).mul_mem_right a
        (Ideal.subset_span (by simp)))
        ((Ideal.span {f, g}).mul_mem_right b
          (Ideal.subset_span (by simp)))
  · obtain ⟨a, b, ha, hb, hab⟩ :=
      Polynomial.exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (Or.inl hfd)
    refine ⟨Polynomial.resultant f g, hres, ?_⟩
    rw [bivariateTwoGeneratorIdeal]
    rw [← hab]
    exact add_mem ((Ideal.span {f, g}).mul_mem_right a
      (Ideal.subset_span (by simp)))
      ((Ideal.span {f, g}).mul_mem_right b
        (Ideal.subset_span (by simp)))

theorem bivariate_prime_contains_univariate_irreducible
    (k : Type*) [Field k] (P : Ideal (BivariatePolynomial k)) (hP : P.IsPrime)
    (hnprincipal : ∀ f, P ≠ Ideal.span ({f} : Set (BivariatePolynomial k))) :
    ∃ p : Polynomial k, Irreducible p ∧ Polynomial.C p ∈ P := by
  obtain ⟨n, f, hf, hPspan⟩ := bivariate_prime_has_finite_irreducible_generators
    k P hP hnprincipal
  have hpair : ∃ i j : Fin n, ¬Associated (f i) (f j) := by
    by_contra h
    push Not at h
    by_cases hn : n = 0
    · apply hnprincipal 0
      subst n
      simp [hPspan]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let i₀ : Fin n := ⟨0, hnpos⟩
      have hspan : Ideal.span (Set.range f) =
          Ideal.span ({f i₀} : Set (BivariatePolynomial k)) := by
        apply le_antisymm
        · apply Ideal.span_le.2
          rintro _ ⟨i, rfl⟩
          exact Ideal.mem_span_singleton.mpr (h i₀ i).dvd
        · apply Ideal.span_le.2
          intro x hx
          rw [Set.mem_singleton_iff.mp hx]
          exact Ideal.subset_span (s := Set.range f) (Set.mem_range_self i₀)
      apply hnprincipal (f i₀)
      exact hPspan.trans hspan
  obtain ⟨i, j, hij⟩ := hpair
  obtain ⟨p, hp0, hpP⟩ := bivariate_pair_intersects_univariate k (f i) (f j)
    (hf i) (hf j) hij
  have hpP' : Polynomial.C p ∈ P := by
    rw [hPspan]
    apply (Ideal.span_le.2 (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Ideal.subset_span ⟨i, rfl⟩
      · exact Ideal.subset_span ⟨j, rfl⟩)) hpP
  have hfactor : ∀ q : Polynomial k, Polynomial.C q ∈ P → q ≠ 0 →
      ∃ r : Polynomial k, Irreducible r ∧ Polynomial.C r ∈ P := by
    intro q
    refine WfDvdMonoid.induction_on_irreducible q ?_ ?_ ?_
    · intro hq hq0
      exact (hq0 rfl).elim
    · intro u hu hmem _
      exact (hP.ne_top
        (P.eq_top_of_isUnit_mem hmem (Polynomial.isUnit_C.mpr hu))).elim
    · intro q r hq0 hr ih hmem _
      have hmem' : Polynomial.C r * Polynomial.C q ∈ P := by
        simpa only [Polynomial.C_mul] using hmem
      rcases hP.mem_or_mem hmem' with hrP | hqP
      · exact ⟨r, hr, hrP⟩
      · exact ih hqP hq0
  exact hfactor p hpP' hp0

theorem bivariate_univariate_quotient_isPID
    (k : Type*) [Field k] (p : Polynomial k) (hp : Irreducible p) :
    IsDomain (BivariateQuotient p) ∧ IsPrincipalIdealRing (BivariateQuotient p) := by
  let P : Ideal (Polynomial k) := Ideal.span {p}
  have hP : P.IsMaximal := by
    exact PrincipalIdealRing.isMaximal_of_irreducible hp
  let : P.IsMaximal := hP
  let : Field (Polynomial k ⧸ P) := Ideal.Quotient.field P
  have hdom :
      IsDomain (BivariatePolynomial k ⧸ Ideal.map Polynomial.C P) :=
    Ideal.isDomain_map_C_quotient hP.isPrime
  have hpid :
      IsPrincipalIdealRing (BivariatePolynomial k ⧸ Ideal.map Polynomial.C P) :=
    IsPrincipalIdealRing.of_surjective
      (Ideal.polynomialQuotientEquivQuotientPolynomial P).toRingHom
      (Ideal.polynomialQuotientEquivQuotientPolynomial P).surjective
  have hmap : Ideal.map Polynomial.C P = bivariateUnivariateIdeal p := by
    change Ideal.map Polynomial.C (Ideal.span ({p} : Set (Polynomial k))) =
      Ideal.span ({Polynomial.C p} : Set (BivariatePolynomial k))
    rw [Ideal.map_span]
    simp
  rw [hmap] at hdom hpid
  exact ⟨hdom, hpid⟩

/-- Prime ideals of the bivariate ring, with the zero ideal included. -/
theorem prime_ideal_bivariate_cases (k : Type*) [Field k]
    (P : Ideal (BivariatePolynomial k)) (hP : P.IsPrime) :
    P = ⊥ ∨
      (∃ f : BivariatePolynomial k, Irreducible f ∧ P = Ideal.span {f}) ∨
      (∃ p : Polynomial k, Irreducible p ∧
        (P = bivariateUnivariateIdeal p ∨
            ∃ f : BivariatePolynomial k, BivariateQuotientIrreducible p f ∧
            P = bivariateTwoGeneratorIdeal (Polynomial.C p) f)) := by
  have : UniqueFactorizationMonoid (BivariatePolynomial k) := bivariate_isUFD k
  by_cases hzero : P = ⊥
  · exact Or.inl hzero
  by_cases hprincipal : ∃ f : BivariatePolynomial k,
      P = Ideal.span ({f} : Set (BivariatePolynomial k))
  · rcases hprincipal with ⟨f, hfP⟩
    refine Or.inr (Or.inl ⟨f, ?_, hfP⟩)
    have hf0 : f ≠ 0 := by
      intro hf0
      apply hzero
      rw [hfP, hf0]
      simp
    apply UniqueFactorizationMonoid.irreducible_iff_prime.mpr
    apply (Ideal.span_singleton_prime hf0).mp
    rw [← hfP]
    exact hP
  · obtain ⟨p, hp, hpP⟩ := bivariate_prime_contains_univariate_irreducible
      k P hP (by
        intro f hf
        exact hprincipal ⟨f, hf⟩)
    let I : Ideal (BivariatePolynomial k) := bivariateUnivariateIdeal p
    let qmk : BivariatePolynomial k →+* BivariateQuotient p := Ideal.Quotient.mk I
    have hI : I ≤ P := by
      intro x hx
      change x ∈ bivariateUnivariateIdeal p at hx
      rw [bivariateUnivariateIdeal] at hx
      rcases (Ideal.mem_span_singleton.mp hx) with ⟨c, hc⟩
      rw [hc]
      exact P.mul_mem_right c hpP
    have : P.IsPrime := hP
    have hQ : (P.map qmk).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hI
    obtain ⟨hdom, hpid⟩ := bivariate_univariate_quotient_isPID k p hp
    have : IsDomain (BivariateQuotient p) := hdom
    have : IsPrincipalIdealRing (BivariateQuotient p) := hpid
    rcases (Ideal.isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors
      (P := P.map qmk)).mp hQ with
      hQbot | ⟨q, hq, hQq⟩
    · refine Or.inr (Or.inr ⟨p, hp, Or.inl ?_⟩)
      have hcomap : (P.map qmk).comap qmk = P := Ideal.comap_map_mk hI
      rw [hQbot] at hcomap
      calc
        P = (⊥ : Ideal (BivariateQuotient p)).comap qmk := hcomap.symm
        _ = RingHom.ker qmk := (RingHom.ker_eq_comap_bot qmk).symm
        _ = I := by
          change RingHom.ker (Ideal.Quotient.mk I) = I
          exact Ideal.mk_ker
    · obtain ⟨f, hfq⟩ := Ideal.Quotient.mk_surjective q
      have hfq' : qmk f = q := by simpa [qmk, I] using hfq
      have hEq : (P.map qmk).comap qmk =
          Ideal.span ({Polynomial.C p, f} : Set (BivariatePolynomial k)) := by
        rw [hQq, ← hfq']
        ext x
        constructor
        · intro hx
          change qmk x ∈ Ideal.span ({qmk f} : Set (BivariateQuotient p)) at hx
          have hdiv : qmk f ∣ qmk x :=
            (Ideal.mem_span_singleton (α := BivariateQuotient p)).mp hx
          rcases hdiv with ⟨c, hc⟩
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
          have hxy : x - f * y ∈ I := by
            rw [← Ideal.Quotient.eq_zero_iff_mem]
            have hc' : qmk x = qmk f * qmk y := by simpa [qmk] using hc
            rw [map_sub, map_mul, hc']
            change qmk f * qmk y - qmk f * qmk y = 0
            simp
          have hxy' : x - f * y ∈
              Ideal.span ({Polynomial.C p} : Set (BivariatePolynomial k)) := by
            simpa [I, bivariateUnivariateIdeal] using hxy
          rcases Ideal.mem_span_singleton.mp hxy' with ⟨z, hz⟩
          apply Ideal.mem_span_pair.mpr
          exact ⟨z, y, by
            calc
              z * Polynomial.C p + y * f = Polynomial.C p * z + f * y := by ring
              _ = (x - f * y) + f * y := by rw [hz]
              _ = x := sub_add_cancel x (f * y)⟩
        · intro hx
          change qmk x ∈ Ideal.span ({qmk f} : Set (BivariateQuotient p))
          rcases (Ideal.mem_span_pair (α := BivariatePolynomial k)).mp hx with
            ⟨a, b, hab⟩
          rw [← hab, map_add, map_mul]
          apply add_mem
          · have hcp : qmk (Polynomial.C p) = 0 := by
              apply Ideal.Quotient.eq_zero_iff_mem.mpr
              change Polynomial.C p ∈ bivariateUnivariateIdeal p
              exact Ideal.subset_span (Set.mem_singleton _)
            rw [hcp]
            exact (Ideal.span ({qmk f} : Set (BivariateQuotient p))).mul_mem_left
              (qmk a) (Ideal.span ({qmk f} : Set (BivariateQuotient p))).zero_mem
          · exact (Ideal.span ({qmk f} : Set (BivariateQuotient p))).mul_mem_left
              (qmk b) (Ideal.subset_span (Set.mem_singleton (qmk f)))
      refine Or.inr (Or.inr ⟨p, hp, Or.inr ⟨f, ?_, ?_⟩⟩)
      · unfold BivariateQuotientIrreducible
        rw [hfq]
        exact hq.irreducible
      · have hcomap : (P.map qmk).comap qmk = P := Ideal.comap_map_mk hI
        rw [hEq] at hcomap
        exact hcomap.symm

/-! ## The affine open which is not a standard localization -/

/-- The subring `R = {f ∈ ℚ[z] | f(0) = f(1)}` as an equalizer subalgebra. -/
def affineBaseSubalgebra : Subalgebra ℚ (Polynomial ℚ) :=
  AlgHom.equalizer (Polynomial.aeval (0 : ℚ)) (Polynomial.aeval (1 : ℚ))

def affineBaseElement (f : Polynomial ℚ)
    (hf : Polynomial.aeval (0 : ℚ) f = Polynomial.aeval (1 : ℚ) f) :
    affineBaseSubalgebra :=
  ⟨f, hf⟩

def affineA : affineBaseSubalgebra :=
  affineBaseElement (Polynomial.X ^ 2 - Polynomial.X) (by simp)

def affineB : affineBaseSubalgebra :=
  affineBaseElement (Polynomial.X ^ 3 - Polynomial.X ^ 2) (by simp)

def affineBZero : affineBaseSubalgebra :=
  affineBaseElement (Polynomial.X ^ 3 - Polynomial.X) (by simp)

theorem affine_base_isDomain : IsDomain affineBaseSubalgebra := by
  infer_instance

theorem affine_base_is_generated_by_A_and_B :
    affineBaseSubalgebra =
      Algebra.adjoin ℚ ({(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)} :
        Set (Polynomial ℚ)) := by
  let S : Subalgebra ℚ (Polynomial ℚ) :=
    Algebra.adjoin ℚ ({(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)} :
      Set (Polynomial ℚ))
  have hA : (affineA : Polynomial ℚ) ∈ S :=
    Algebra.subset_adjoin (by simp)
  have hB : (affineB : Polynomial ℚ) ∈ S :=
    Algebra.subset_adjoin (by simp)
  have hAmonic : (affineA : Polynomial ℚ).Monic := by
    change (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℚ).Monic
    simpa using (Polynomial.monic_X_pow_sub (p := Polynomial.X) (n := 2) (by simp))
  have hAq : ∀ q : Polynomial ℚ,
      (affineA : Polynomial ℚ) * q ∈ S := by
    intro q
    induction hq : q.natDegree using Nat.strong_induction_on generalizing q with
    | h n ih =>
        by_cases hsmall : q.natDegree ≤ 1
        · obtain ⟨c₁, c₀, hqform⟩ :=
            Polynomial.exists_eq_X_add_C_of_natDegree_le_one hsmall
          have hident :
              (affineA : Polynomial ℚ) * q =
                Polynomial.C c₁ * (affineB : Polynomial ℚ) +
                  Polynomial.C c₀ * (affineA : Polynomial ℚ) := by
            rw [hqform]
            simp [affineA, affineB, affineBaseElement]
            ring
          rw [hident]
          apply S.add_mem
          · apply S.mul_mem
            · simpa only [Polynomial.C_eq_algebraMap] using S.algebraMap_mem c₁
            · exact hB
          · apply S.mul_mem
            · simpa only [Polynomial.C_eq_algebraMap] using S.algebraMap_mem c₀
            · exact hA
        · have hquot :
              (q /ₘ (affineA : Polynomial ℚ)).natDegree < q.natDegree := by
            have hAnat : (affineA : Polynomial ℚ).natDegree = 2 := by
              change (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℚ).natDegree = 2
              rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp)]
              simp
            rw [Polynomial.natDegree_divByMonic q hAmonic, hAnat, hq]
            omega
          have hquot' :
              (q /ₘ (affineA : Polynomial ℚ)).natDegree < n := by
            simpa [hq] using hquot
          have hih := ih _ hquot' (q /ₘ (affineA : Polynomial ℚ)) rfl
          have hrem :
              (affineA : Polynomial ℚ) * (q %ₘ (affineA : Polynomial ℚ)) ∈ S := by
            have hremdeg : (q %ₘ (affineA : Polynomial ℚ)).natDegree ≤ 1 := by
              have hlt := Polynomial.degree_modByMonic_lt q hAmonic
              change (q %ₘ (affineA : Polynomial ℚ)).degree <
                (affineA : Polynomial ℚ).degree at hlt
              have hAdeg : (affineA : Polynomial ℚ).degree = (2 : WithBot ℕ) := by
                rw [Polynomial.degree_eq_natDegree hAmonic.ne_zero]
                have hAnat : (affineA : Polynomial ℚ).natDegree = 2 := by
                  change (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℚ).natDegree = 2
                  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp)]
                  simp
                rw [hAnat]
                norm_num
              rw [hAdeg] at hlt
              have hle : (q %ₘ (affineA : Polynomial ℚ)).degree ≤ (1 : WithBot ℕ) := by
                by_cases hbot : (q %ₘ (affineA : Polynomial ℚ)).degree = ⊥
                · rw [hbot]
                  exact bot_le
                · obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hbot
                  rw [← hn]
                  apply WithBot.coe_le_coe.mpr
                  rw [← hn] at hlt
                  have hn' : n < 2 := WithBot.coe_lt_coe.mp hlt
                  omega
              exact Polynomial.natDegree_le_of_degree_le hle
            obtain ⟨c₁, c₀, hremform⟩ :=
              Polynomial.exists_eq_X_add_C_of_natDegree_le_one hremdeg
            have hident :
                (affineA : Polynomial ℚ) * (q %ₘ (affineA : Polynomial ℚ)) =
                  Polynomial.C c₁ * (affineB : Polynomial ℚ) +
                    Polynomial.C c₀ * (affineA : Polynomial ℚ) := by
              rw [hremform]
              simp [affineA, affineB, affineBaseElement]
              ring
            rw [hident]
            apply S.add_mem
            · apply S.mul_mem
              · simpa only [Polynomial.C_eq_algebraMap] using S.algebraMap_mem c₁
              · exact hB
            · apply S.mul_mem
              · simpa only [Polynomial.C_eq_algebraMap] using S.algebraMap_mem c₀
              · exact hA
          have hqdecomp := Polynomial.modByMonic_add_div q (affineA : Polynomial ℚ)
          rw [← hqdecomp]
          rw [mul_add]
          exact S.add_mem hrem (S.mul_mem hA hih)
  have hgen : ∀ f : Polynomial ℚ,
      Polynomial.aeval (0 : ℚ) f = Polynomial.aeval (1 : ℚ) f → f ∈ S := by
    intro f hf
    let r : Polynomial ℚ := f %ₘ (affineA : Polynomial ℚ)
    let q : Polynomial ℚ := f /ₘ (affineA : Polynomial ℚ)
    have hdecomp : r + (affineA : Polynomial ℚ) * q = f := by
      simpa [r, q] using Polynomial.modByMonic_add_div f (affineA : Polynomial ℚ)
    have hrEq : Polynomial.aeval (0 : ℚ) r = Polynomial.aeval (1 : ℚ) r := by
      have h := hf
      rw [← hdecomp] at h
      simpa [r, q, affineA, affineBaseElement] using h
    have hrdeg : r.natDegree ≤ 1 := by
      have hlt := Polynomial.degree_modByMonic_lt f hAmonic
      change r.degree < (affineA : Polynomial ℚ).degree at hlt
      have hAdeg : (affineA : Polynomial ℚ).degree = (2 : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hAmonic.ne_zero]
        have hAnat : (affineA : Polynomial ℚ).natDegree = 2 := by
          change (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℚ).natDegree = 2
          rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp)]
          simp
        rw [hAnat]
        norm_num
      rw [hAdeg] at hlt
      have hle : r.degree ≤ (1 : WithBot ℕ) := by
        by_cases hbot : r.degree = ⊥
        · rw [hbot]
          exact bot_le
        · obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hbot
          rw [← hn]
          apply WithBot.coe_le_coe.mpr
          rw [← hn] at hlt
          have hn' : n < 2 := WithBot.coe_lt_coe.mp hlt
          omega
      exact Polynomial.natDegree_le_of_degree_le hle
    obtain ⟨c₁, c₀, hremform⟩ :=
      Polynomial.exists_eq_X_add_C_of_natDegree_le_one hrdeg
    have hc₁ : c₁ = 0 := by
      rw [hremform] at hrEq
      have : c₀ = c₁ + c₀ := by simpa using hrEq
      linarith
    have hrconst : r = Polynomial.C c₀ := by
      rw [hremform, hc₁]
      simp
    have hfdecomp : f = Polynomial.C c₀ +
        (affineA : Polynomial ℚ) * q := by
      rw [← hdecomp, hrconst]
    rw [hfdecomp]
    apply S.add_mem
    · simpa only [Polynomial.C_eq_algebraMap] using S.algebraMap_mem c₀
    · exact hAq q
  change affineBaseSubalgebra = S
  apply le_antisymm
  · intro f hf
    change Polynomial.aeval (0 : ℚ) f = Polynomial.aeval (1 : ℚ) f at hf
    exact hgen f hf
  · apply Algebra.adjoin_le
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact affineA.property
    · have hf' : f = (affineB : Polynomial ℚ) := by simpa using hf
      subst f
      exact affineB.property

theorem affine_base_isFiniteType : Algebra.FiniteType ℚ affineBaseSubalgebra := by
  rw [affine_base_is_generated_by_A_and_B]
  exact Algebra.FiniteType.adjoin_of_finite (by simp)

theorem affine_base_z_mul_A_eq_B :
    Polynomial.X * (affineA : Polynomial ℚ) = (affineB : Polynomial ℚ) := by
  simp [affineA, affineB, affineBaseElement]
  ring

def affinePolynomialF1 (a : ℚ) : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C (1 - a)) * (Polynomial.X - Polynomial.C a)

def affinePolynomialF2AtA (a : ℚ) : Polynomial ℚ :=
  (Polynomial.X ^ 2 - Polynomial.C (1 - a)) * (Polynomial.X - Polynomial.C a)

def affinePolynomialF2AtOneMinusA (a : ℚ) : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C (1 - a)) * (Polynomial.X ^ 2 - Polynomial.C a)

def affineQuadratic (a : ℚ) : Polynomial ℚ :=
  Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (2 * a - 2)

def affinePolynomialG (a : ℚ) : Polynomial ℚ :=
  affineQuadratic a * (Polynomial.X - Polynomial.C a)

theorem affinePolynomialF1_mem_equalizer (a : ℚ) :
    Polynomial.aeval (0 : ℚ) (affinePolynomialF1 a) =
      Polynomial.aeval (1 : ℚ) (affinePolynomialF1 a) := by
  simp [affinePolynomialF1, Polynomial.aeval_def]
  ring

theorem affinePolynomialF2AtA_mem_equalizer (a : ℚ) :
    Polynomial.aeval (0 : ℚ) (affinePolynomialF2AtA a) =
      Polynomial.aeval (1 : ℚ) (affinePolynomialF2AtA a) := by
  simp [affinePolynomialF2AtA, Polynomial.aeval_def]
  ring

theorem affinePolynomialF2AtOneMinusA_mem_equalizer (a : ℚ) :
    Polynomial.aeval (0 : ℚ) (affinePolynomialF2AtOneMinusA a) =
      Polynomial.aeval (1 : ℚ) (affinePolynomialF2AtOneMinusA a) := by
  simp [affinePolynomialF2AtOneMinusA, Polynomial.aeval_def]
  ring

theorem affinePolynomialG_mem_equalizer (a : ℚ) :
    Polynomial.aeval (0 : ℚ) (affinePolynomialG a) =
      Polynomial.aeval (1 : ℚ) (affinePolynomialG a) := by
  simp [affinePolynomialG, affineQuadratic, Polynomial.aeval_def]
  ring

def affineF1 (a : ℚ) : affineBaseSubalgebra :=
  affineBaseElement (affinePolynomialF1 a) (affinePolynomialF1_mem_equalizer a)

def affineF2AtA (a : ℚ) : affineBaseSubalgebra :=
  affineBaseElement (affinePolynomialF2AtA a) (affinePolynomialF2AtA_mem_equalizer a)

def affineF2AtOneMinusA (a : ℚ) : affineBaseSubalgebra :=
  affineBaseElement (affinePolynomialF2AtOneMinusA a)
    (affinePolynomialF2AtOneMinusA_mem_equalizer a)

def affineG (a : ℚ) : affineBaseSubalgebra :=
  affineBaseElement (affinePolynomialG a) (affinePolynomialG_mem_equalizer a)

/-- The presentation ring `ℚ[A,B]` and its two coordinate variables. -/
abbrev AffinePresentation := MvPolynomial (Fin 2) ℚ

def affinePresentationA : AffinePresentation := MvPolynomial.X 0

def affinePresentationB : AffinePresentation := MvPolynomial.X 1

def affinePresentationRelation : AffinePresentation :=
  affinePresentationA ^ 3 - affinePresentationB ^ 2 +
    affinePresentationA * affinePresentationB

def affinePresentationValues : Fin 2 → affineBaseSubalgebra := fun i =>
  if i = 0 then affineA else affineB

def affinePresentationMap : AffinePresentation →ₐ[ℚ] affineBaseSubalgebra :=
  MvPolynomial.aeval affinePresentationValues

theorem affine_presentation_relation_mem_kernel :
    affinePresentationRelation ∈ RingHom.ker affinePresentationMap.toRingHom := by
  change affinePresentationMap affinePresentationRelation = 0
  simp [affinePresentationRelation, affinePresentationMap, affinePresentationValues,
    affinePresentationA, affinePresentationB]
  apply Subtype.ext
  simp [affineA, affineB, affineBaseElement]
  ring

theorem affine_presentation_surjective : Function.Surjective affinePresentationMap := by
  have hgen := affine_base_is_generated_by_A_and_B
  have hsurj :
      ∀ y : Polynomial ℚ,
        y ∈ Algebra.adjoin ℚ ({(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)} :
          Set (Polynomial ℚ)) →
          ∃ q : AffinePresentation, (affinePresentationMap q : Polynomial ℚ) = y := by
    intro y hy
    refine Algebra.adjoin_induction (R := ℚ) (A := Polynomial ℚ)
      (s := {(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)})
      (p := fun y _ =>
        ∃ q : AffinePresentation, (affinePresentationMap q : Polynomial ℚ) = y) ?_ ?_ ?_ ?_ hy
    · intro y hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · refine ⟨affinePresentationA, ?_⟩
        simp [affinePresentationMap, affinePresentationValues, affinePresentationA]
      · have hy' : y = (affineB : Polynomial ℚ) := by simpa using hy
        subst y
        refine ⟨affinePresentationB, ?_⟩
        simp [affinePresentationMap, affinePresentationValues, affinePresentationB]
    · intro r
      refine ⟨MvPolynomial.C r, ?_⟩
      simp [affinePresentationMap]
    · intro x y hx hy hx' hy'
      rcases hx' with ⟨p, hp⟩
      rcases hy' with ⟨q, hq⟩
      refine ⟨p + q, ?_⟩
      simpa [map_add] using
        congrArg₂ (fun u v : Polynomial ℚ => u + v) hp hq
    · intro x y hx hy hx' hy'
      rcases hx' with ⟨p, hp⟩
      rcases hy' with ⟨q, hq⟩
      refine ⟨p * q, ?_⟩
      simpa [map_mul] using
        congrArg₂ (fun u v : Polynomial ℚ => u * v) hp hq
  intro x
  have hx : (x : Polynomial ℚ) ∈
      Algebra.adjoin ℚ ({(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)} :
        Set (Polynomial ℚ)) := by
    rw [← hgen]
    exact x.property
  obtain ⟨q, hq⟩ := hsurj (x : Polynomial ℚ) hx
  refine ⟨q, ?_⟩
  apply Subtype.ext
  exact hq

theorem affine_base_not_isField : ¬ IsField affineBaseSubalgebra := by
  intro h
  let := h
  let := h.toField
  have hA : affineA ≠ 0 := by
    intro hA
    have hp : (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℚ) = 0 :=
      congrArg Subtype.val hA
    have he := congrArg (fun p : Polynomial ℚ => Polynomial.eval 2 p) hp
    norm_num at he
  have hu : IsUnit affineA :=
    (isUnit_iff_ne_zero (G₀ := affineBaseSubalgebra) (a := affineA)).mpr hA
  let e0 : affineBaseSubalgebra →+* ℚ :=
    (Polynomial.evalRingHom 0).comp affineBaseSubalgebra.val.toRingHom
  have hu0 : IsUnit (e0 affineA) := RingHom.isUnit_map e0 hu
  have hz : e0 affineA = 0 := by
    simp [e0, affineA, affineBaseElement]
  rw [hz] at hu0
  exact not_isUnit_zero hu0

theorem affine_presentation_relation_irreducible :
    Irreducible affinePresentationRelation := by
  let x : MvPolynomial (Fin 1) ℚ := MvPolynomial.X 0
  have hno_root : ∀ r : MvPolynomial (Fin 1) ℚ,
      r ^ 3 + x * r - x ^ 2 ≠ 0 := by
    intro r
    by_cases hd0 : r.totalDegree = 0
    · have hc : r = MvPolynomial.C (MvPolynomial.coeff 0 r) :=
        (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hd0
      rw [hc]
      intro hz
      have hsdeg :
          ((MvPolynomial.C (MvPolynomial.coeff 0 r)) ^ 3 +
            x * MvPolynomial.C (MvPolynomial.coeff 0 r)).totalDegree ≤ 1 := by
        calc
          ((MvPolynomial.C (MvPolynomial.coeff 0 r)) ^ 3 +
              x * MvPolynomial.C (MvPolynomial.coeff 0 r)).totalDegree ≤
              max ((MvPolynomial.C (MvPolynomial.coeff 0 r)) ^ 3).totalDegree
                (x * MvPolynomial.C (MvPolynomial.coeff 0 r)).totalDegree :=
            MvPolynomial.totalDegree_add _ _
          _ ≤ 1 := by
            exact max_le
              (by
                calc
                  ((MvPolynomial.C (MvPolynomial.coeff 0 r)) ^ 3).totalDegree ≤
                      3 * (MvPolynomial.C (MvPolynomial.coeff 0 r)).totalDegree :=
                    MvPolynomial.totalDegree_pow _ _
                  _ ≤ 1 := by simp)
              (by
                calc
                  (x * MvPolynomial.C (MvPolynomial.coeff 0 r)).totalDegree ≤
                      x.totalDegree + (MvPolynomial.C (MvPolynomial.coeff 0 r)).totalDegree :=
                    MvPolynomial.totalDegree_mul _ _
                  _ ≤ 1 := by simp [x])
      have heq :
          (MvPolynomial.C (MvPolynomial.coeff 0 r)) ^ 3 +
              x * MvPolynomial.C (MvPolynomial.coeff 0 r) = x ^ 2 :=
        sub_eq_zero.mp hz
      rw [heq, show (x ^ 2).totalDegree = 2 by simp [x]] at hsdeg
      omega
    · have hdpos : 0 < r.totalDegree := Nat.pos_of_ne_zero hd0
      have hr0 : r ≠ 0 := by
        intro hr
        apply hd0
        simp [hr]
      have hpow :
          (r ^ 3).totalDegree =
            r.totalDegree + r.totalDegree + r.totalDegree := by
        rw [show r ^ 3 = r * r * r by ring]
        rw [MvPolynomial.totalDegree_mul_of_isDomain (mul_ne_zero hr0 hr0) hr0,
          MvPolynomial.totalDegree_mul_of_isDomain hr0 hr0]
      have hxr :
          (x * r).totalDegree = x.totalDegree + r.totalDegree :=
        MvPolynomial.totalDegree_mul_of_isDomain (by simp [x]) hr0
      have hlt : (x * r).totalDegree < (r ^ 3).totalDegree := by
        rw [hpow, hxr]
        simp [x]
        omega
      have hsum :
          (r ^ 3 + x * r).totalDegree =
            r.totalDegree + r.totalDegree + r.totalDegree := by
        calc
          (r ^ 3 + x * r).totalDegree = (r ^ 3).totalDegree :=
            MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt hlt
          _ = r.totalDegree + r.totalDegree + r.totalDegree := hpow
      have hx2 : (x ^ 2).totalDegree = 2 := by simp [x]
      have hlt2 : (x ^ 2).totalDegree < (r ^ 3 + x * r).totalDegree := by
        rw [hx2, hsum]
        omega
      have hfinal :
          (r ^ 3 + x * r - x ^ 2).totalDegree =
            r.totalDegree + r.totalDegree + r.totalDegree := by
        calc
          (r ^ 3 + x * r - x ^ 2).totalDegree =
              (r ^ 3 + x * r).totalDegree := by
            rw [sub_eq_add_neg]
            apply MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt
            rw [MvPolynomial.totalDegree_neg, hx2, hsum]
            omega
          _ = r.totalDegree + r.totalDegree + r.totalDegree := hsum
      intro hz
      rw [hz] at hfinal
      simp at hfinal
      omega
  let e : AffinePresentation ≃ₐ[ℚ]
      Polynomial (MvPolynomial (Fin 1) ℚ) :=
    MvPolynomial.finSuccEquiv ℚ 1
  have he : e affinePresentationRelation =
      Polynomial.X ^ 3 +
        Polynomial.C (MvPolynomial.X 0) * Polynomial.X -
          Polynomial.C (MvPolynomial.X 0) ^ 2 := by
    simp only [affinePresentationRelation, map_sub, map_add, map_pow, map_mul]
    have hA : e affinePresentationA = Polynomial.X := by
      simp [e, affinePresentationA, MvPolynomial.finSuccEquiv_X_zero]
    have hB : e affinePresentationB =
        Polynomial.C (MvPolynomial.X 0) := by
      change MvPolynomial.finSuccEquiv ℚ 1
          (MvPolynomial.X (0 : Fin 1).succ) =
        Polynomial.C (MvPolynomial.X 0)
      exact MvPolynomial.finSuccEquiv_X_succ
    rw [hA, hB]
    ring
  let q : Polynomial (MvPolynomial (Fin 1) ℚ) :=
    Polynomial.C x * Polynomial.X - Polynomial.C (x ^ 2)
  have hmul : (Polynomial.C x * Polynomial.X).natDegree ≤
      (Polynomial.C x).natDegree + Polynomial.X.natDegree :=
    Polynomial.natDegree_mul_le
  have hqdeg : q.natDegree ≤ 1 := by
    have hsub := Polynomial.natDegree_sub_le_of_le
      (p := Polynomial.C x * Polynomial.X) (q := Polynomial.C (x ^ 2))
      (m := 1) (n := 1) (by simpa using hmul) (by simp)
    simpa [q] using hsub
  have hqdegree : q.degree < 3 := by
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hqdeg) (by norm_num)
  have hp_monic : (Polynomial.X ^ 3 + q).Monic := by
    exact Polynomial.monic_X_pow_add hqdegree
  have hpdeg : (Polynomial.X ^ 3 + q).natDegree = 3 := by
    have h := Polynomial.natDegree_add_eq_left_of_natDegree_lt
      (p := Polynomial.X ^ 3) (q := q)
      (lt_of_le_of_lt hqdeg (by norm_num))
    simpa only [Polynomial.natDegree_X_pow, Nat.mul_one] using h
  have hp0 : Polynomial.X ^ 3 + q ≠ 0 := hp_monic.ne_zero
  have hroots : (Polynomial.X ^ 3 + q).roots = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro r hr
    have hroot := (Polynomial.mem_roots hp0).mp hr
    change Polynomial.eval r (Polynomial.X ^ 3 + q) = 0 at hroot
    have hroot' : r ^ 3 + x * r - x ^ 2 = 0 := by
      convert hroot using 1
      simp [q, x, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul]
      ring
    exact hno_root r hroot'
  have hp : Irreducible (Polynomial.X ^ 3 + q) := by
    have hp2 : 2 ≤ (Polynomial.X ^ 3 + q).natDegree := by omega
    have hp3 : (Polynomial.X ^ 3 + q).natDegree ≤ 3 := by omega
    exact
      (hp_monic.irreducible_iff_roots_eq_zero_of_degree_le_three hp2 hp3).mpr
        hroots
  have hpm : Irreducible (e affinePresentationRelation) := by
    rw [he]
    convert hp using 1
    simp [q, x]
    ring
  exact (MulEquiv.irreducible_iff e.toRingEquiv.toMulEquiv).mp hpm

theorem affine_presentation_primes_containing_relation
    (P : Ideal AffinePresentation) (hP : P.IsPrime)
    (hrel : Ideal.span {affinePresentationRelation} ≤ P) :
    P = Ideal.span {affinePresentationRelation} ∨ P.IsMaximal := by
  let I : Ideal AffinePresentation :=
    Ideal.span {affinePresentationRelation}
  let f : AffinePresentation →+* (AffinePresentation ⧸ I) :=
    Ideal.Quotient.mk I
  have hrel0 : affinePresentationRelation ≠ 0 :=
    affine_presentation_relation_irreducible.ne_zero
  have hIprime : I.IsPrime := by
    apply (Ideal.span_singleton_prime hrel0).mpr
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp
      affine_presentation_relation_irreducible
  let := hIprime
  have hdim :
      ringKrullDim (AffinePresentation ⧸ I) + 1 ≤
        ringKrullDim AffinePresentation := by
    apply ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    exact mem_nonZeroDivisors_iff_ne_zero.mpr hrel0
  have hdim' : ringKrullDim (AffinePresentation ⧸ I) + 1 ≤ 2 := by
    simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field ℚ] using hdim
  have hdim1 : ringKrullDim (AffinePresentation ⧸ I) ≤ 1 := by
    induction hq : ringKrullDim (AffinePresentation ⧸ I) using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe a =>
      induction a using ENat.recTopCoe with
      | top =>
        rw [hq] at hdim'
        have hdim'' : (⊤ : ℕ∞) + 1 ≤ 2 :=
          WithBot.coe_le_coe.mp hdim'
        simp at hdim''
      | coe n =>
        rw [hq] at hdim'
        have hdim'' : (n : ℕ∞) + 1 ≤ 2 :=
          WithBot.coe_le_coe.mp hdim'
        have hlt : (n : ℕ∞) < 2 :=
          ENat.add_one_le_natCast_iff.mp hdim''
        have hnat : n < 2 :=
          ENat.natCast_lt_natCast.mp hlt
        have hnat' : n ≤ 1 := by omega
        exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hnat')
  let := (Ring.krullDimLE_iff.mpr hdim1)
  have hPbar : (P.map f).IsPrime := by
    let := hP
    apply Ideal.map_isPrime_of_surjective (f := f) Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact hrel
  have hcomap : (P.map f).comap f = P := by
    rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective]
    have hk : Ideal.comap f (⊥ : Ideal (AffinePresentation ⧸ I)) = I := by
      rw [← RingHom.ker_eq_comap_bot]
      simp [f]
    rw [hk, sup_eq_left.mpr hrel]
  by_cases hPI : P = I
  · exact Or.inl hPI
  · right
    have hPbar_ne_bot : P.map f ≠ ⊥ := by
      intro hzero
      apply hPI
      calc
        P = (P.map f).comap f := hcomap.symm
        _ = (⊥ : Ideal (AffinePresentation ⧸ I)).comap f := by rw [hzero]
        _ = I := by
          rw [← RingHom.ker_eq_comap_bot]
          simp [f]
    have hPbarmax : (P.map f).IsMaximal :=
      Ideal.IsPrime.isMaximal_of_ne_bot (R := AffinePresentation ⧸ I)
        hPbar hPbar_ne_bot
    have hPmax : P.IsMaximal := by
      simpa only [hcomap] using
        (Ideal.comap_isMaximal_of_surjective
          (f := f) (K := P.map f) (H := hPbarmax)
          Ideal.Quotient.mk_surjective)
    exact hPmax

theorem affine_presentation_kernel :
    RingHom.ker affinePresentationMap.toRingHom =
      Ideal.span {affinePresentationRelation} := by
  have hrelker :
      Ideal.span {affinePresentationRelation} ≤
        RingHom.ker affinePresentationMap.toRingHom := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact affine_presentation_relation_mem_kernel
  have hkerprime :
      (RingHom.ker affinePresentationMap.toRingHom).IsPrime :=
    RingHom.ker_isPrime _
  rcases affine_presentation_primes_containing_relation
      (RingHom.ker affinePresentationMap.toRingHom) hkerprime hrelker with hEq | hMax
  · exact hEq
  · exfalso
    apply affine_base_not_isField
    have hfield :
        IsField (AffinePresentation ⧸ RingHom.ker affinePresentationMap.toRingHom) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient
        (RingHom.ker affinePresentationMap.toRingHom)).mp hMax
    let e := RingHom.quotientKerEquivOfSurjective
      (f := affinePresentationMap.toRingHom) affine_presentation_surjective
    exact e.symm.toMulEquiv.isField hfield

/-- The induced presentation isomorphism has the direction determined by the
surjective map `ℚ[A,B] → R`: the quotient is isomorphic to `R`. -/
theorem affine_presentation_quotient_equiv :
    Nonempty ((AffinePresentation ⧸ Ideal.span {affinePresentationRelation}) ≃+*
      affineBaseSubalgebra) := by
  refine ⟨?_⟩
  rw [← affine_presentation_kernel]
  exact
    (Ideal.quotientKerAlgEquivOfSurjective
      affine_presentation_surjective).toRingEquiv

/-- The ambient ring `ℚ[z, 1/(z-a)]`. -/
abbrev AffineAmbient (a : ℚ) :=
  Localization.Away (Polynomial.X - Polynomial.C a)

def affineLocalizationMap (a : ℚ) : Polynomial ℚ →+* AffineAmbient a :=
  algebraMap _ _

def affineBaseImage (a : ℚ) : affineBaseSubalgebra →+* AffineAmbient a :=
  (affineLocalizationMap a).comp affineBaseSubalgebra.val.toRingHom

/-- The third generator used for `Rₐ`. -/
noncomputable def affineDenominatorInverse (a : ℚ) : AffineAmbient a :=
  ↑((IsLocalization.Away.algebraMap_isUnit
    (R := Polynomial ℚ) (S := AffineAmbient a)
    (Polynomial.X - Polynomial.C a)).unit⁻¹)

def affineOpenThirdGenerator (a : ℚ) : AffineAmbient a :=
  affineLocalizationMap a (Polynomial.C (a ^ 2 - a)) *
      affineDenominatorInverse a +
    affineLocalizationMap a Polynomial.X

/-- The subalgebra generated by the image of `R` and the third generator. -/
def affineOpenSubalgebra (a : ℚ) : Subalgebra ℚ (AffineAmbient a) :=
  Algebra.adjoin ℚ
    (Set.range (affineBaseImage a) ∪ {affineOpenThirdGenerator a})

abbrev AffineOpenRing (a : ℚ) := affineOpenSubalgebra a

noncomputable def affineAmbientEvaluation (a r : ℚ) (har : r ≠ a) :
    AffineAmbient a →ₐ[ℚ] ℚ :=
  IsLocalization.Away.liftAlgHom (f := Polynomial.aeval r)
    (Polynomial.X - Polynomial.C a) (by
    rw [isUnit_iff_ne_zero]
    simpa using sub_ne_zero.mpr har)

def affineOpenEqualizer (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    Subalgebra ℚ (AffineAmbient a) :=
  AlgHom.equalizer (affineAmbientEvaluation a 0 ha0.symm)
    (affineAmbientEvaluation a 1 ha1.symm)

def affineBaseToOpen (a : ℚ) : affineBaseSubalgebra →+* AffineOpenRing a :=
  RingHom.codRestrict (affineBaseImage a) (affineOpenSubalgebra a)
    (fun x => Algebra.subset_adjoin (Or.inl ⟨x, rfl⟩))

theorem affine_localization_map_injective (a : ℚ) :
    Function.Injective (affineLocalizationMap a) := by
  simpa [affineLocalizationMap] using
    (IsLocalization.injective (R := Polynomial ℚ)
      (Localization.Away (Polynomial.X - Polynomial.C a))
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (x := Polynomial.X - Polynomial.C a) (Polynomial.X_sub_C_ne_zero a)))

theorem affine_base_to_open_injective (a : ℚ) :
    Function.Injective (affineBaseToOpen a) := by
  intro x y h
  apply Subtype.ext
  apply affine_localization_map_injective a
  exact congrArg (fun z : AffineOpenRing a => (z : AffineAmbient a)) h

def affineOpenThird (a : ℚ) : AffineOpenRing a :=
  ⟨affineOpenThirdGenerator a,
    Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))⟩

def affineOpenA (a : ℚ) : AffineOpenRing a :=
  affineBaseToOpen a affineA

def affineOpenF1 (a : ℚ) : AffineOpenRing a :=
  affineBaseToOpen a (affineF1 a)

def affineOpenG (a : ℚ) : AffineOpenRing a :=
  affineBaseToOpen a (affineG a)

theorem affine_open_is_generated_by_three (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    affineOpenSubalgebra a =
      Algebra.adjoin ℚ
        {affineLocalizationMap a (Polynomial.X ^ 2 - Polynomial.X),
          affineLocalizationMap a (Polynomial.X ^ 3 - Polynomial.X),
          affineOpenThirdGenerator a} := by
  by_cases h : a = 0
  · exact (ha0 h).elim
  by_cases h' : a = 1
  · exact (ha1 h').elim
  by_cases h'' : a = 1 / 2
  · exact (haHalf h'').elim
  let S : Subalgebra ℚ (AffineAmbient a) :=
    Algebra.adjoin ℚ
      {affineLocalizationMap a (Polynomial.X ^ 2 - Polynomial.X),
        affineLocalizationMap a (Polynomial.X ^ 3 - Polynomial.X),
        affineOpenThirdGenerator a}
  apply le_antisymm
  · change Algebra.adjoin ℚ
      (Set.range (affineBaseImage a) ∪ {affineOpenThirdGenerator a}) ≤ S
    apply Algebra.adjoin_le
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨y, rfl⟩
      have hy : (y : Polynomial ℚ) ∈
          Algebra.adjoin ℚ ({(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)} :
            Set (Polynomial ℚ)) := by
        rw [← affine_base_is_generated_by_A_and_B]
        exact y.property
      refine Algebra.adjoin_induction (R := ℚ) (A := Polynomial ℚ)
        (s := {(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)})
        (p := fun z _ => affineLocalizationMap a z ∈ S) ?_ ?_ ?_ ?_ hy
      · intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · change affineLocalizationMap a (Polynomial.X ^ 2 - Polynomial.X) ∈ S
          change affineLocalizationMap a (Polynomial.X ^ 2 - Polynomial.X) ∈
            Algebra.adjoin ℚ
              {affineLocalizationMap a (Polynomial.X ^ 2 - Polynomial.X),
                affineLocalizationMap a (Polynomial.X ^ 3 - Polynomial.X),
                affineOpenThirdGenerator a}
          exact Algebra.subset_adjoin (by simp)
        · have hz' : z = (affineB : Polynomial ℚ) := by
            exact Set.mem_singleton_iff.mp hz
          subst z
          have hB : (affineB : Polynomial ℚ) =
              (Polynomial.X ^ 3 - Polynomial.X) - (Polynomial.X ^ 2 - Polynomial.X) := by
            simp [affineB, affineBaseElement]
          rw [hB, map_sub]
          exact S.sub_mem (Algebra.subset_adjoin (by simp))
            (Algebra.subset_adjoin (by simp))
      · intro r
        change affineLocalizationMap a (Polynomial.C r) ∈ S
        rw [show Polynomial.C r = algebraMap ℚ (Polynomial ℚ) r by simp]
        change algebraMap ℚ (AffineAmbient a) r ∈ S
        exact S.algebraMap_mem r
      · intro x y hx hy hx' hy'
        simpa only [map_add] using S.add_mem hx' hy'
      · intro x y hx hy hx' hy'
        simpa only [map_mul] using S.mul_mem hx' hy'
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact Algebra.subset_adjoin (by simp)
  · apply Algebra.adjoin_le
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · have h :
          affineLocalizationMap a (affineA : Polynomial ℚ) ∈
            affineOpenSubalgebra a :=
        Algebra.subset_adjoin (Or.inl ⟨affineA, rfl⟩)
      simpa [affineA, affineBaseElement] using h
    · rcases Set.mem_insert_iff.mp hx with rfl | hx
      · have h :
            affineLocalizationMap a (affineBZero : Polynomial ℚ) ∈
              affineOpenSubalgebra a :=
          Algebra.subset_adjoin (Or.inl ⟨affineBZero, rfl⟩)
        simpa [affineBZero, affineBaseElement] using h
      · rcases Set.mem_singleton_iff.mp hx with rfl
        exact Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))

theorem affine_open_is_equalizer (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    affineOpenSubalgebra a = affineOpenEqualizer a ha0 ha1 := by
  apply le_antisymm
  · change Algebra.adjoin ℚ
      (Set.range (affineBaseImage a) ∪ {affineOpenThirdGenerator a}) ≤
        affineOpenEqualizer a ha0 ha1
    apply Algebra.adjoin_le
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨y, rfl⟩
      change affineAmbientEvaluation a 0 ha0.symm
          (affineLocalizationMap a (y : Polynomial ℚ)) =
        affineAmbientEvaluation a 1 ha1.symm
          (affineLocalizationMap a (y : Polynomial ℚ))
      simp [affineAmbientEvaluation, affineBaseSubalgebra, affineLocalizationMap]
      exact y.property
    · rcases Set.mem_singleton_iff.mp hx with rfl
      change affineAmbientEvaluation a 0 ha0.symm
          (affineOpenThirdGenerator a) =
        affineAmbientEvaluation a 1 ha1.symm
          (affineOpenThirdGenerator a)
      simp [affineAmbientEvaluation, affineOpenThirdGenerator,
        affineDenominatorInverse, affineLocalizationMap]
      ring_nf
      calc
        a * a⁻¹ - a ^ 2 * a⁻¹ = 1 - a := by
          rw [show a ^ 2 * a⁻¹ = a * (a * a⁻¹) by ring,
            mul_inv_cancel₀ ha0]
          ring
        _ = 1 - a * (1 - a)⁻¹ + a ^ 2 * (1 - a)⁻¹ := by
          calc
            1 - a = 1 - a * ((1 - a) * (1 - a)⁻¹) := by
              rw [mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm ha1))]
              ring
            _ = 1 - a * (1 - a)⁻¹ + a ^ 2 * (1 - a)⁻¹ := by ring
  · change ∀ z, z ∈ affineOpenEqualizer a ha0 ha1 →
      z ∈ affineOpenSubalgebra a
    have hu : affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
        affineDenominatorInverse a = 1 := by
      change
        (↑((IsLocalization.Away.algebraMap_isUnit (R := Polynomial ℚ)
          (S := AffineAmbient a) (Polynomial.X - Polynomial.C a)).unit) :
            AffineAmbient a) *
          ↑((IsLocalization.Away.algebraMap_isUnit (R := Polynomial ℚ)
            (S := AffineAmbient a) (Polynomial.X - Polynomial.C a)).unit⁻¹) = 1
      simp
    have hc : a ^ 2 - a ≠ 0 := by
      simpa [show a ^ 2 - a = a * (a - 1) by ring] using
        (mul_ne_zero ha0 (sub_ne_zero.mpr ha1))
    let q : Polynomial ℚ :=
      Polynomial.X * (Polynomial.X - Polynomial.C a) +
        Polynomial.C (a ^ 2 - a)
    have hq : affineLocalizationMap a q * affineDenominatorInverse a =
        affineOpenThirdGenerator a := by
      dsimp [q, affineOpenThirdGenerator]
      rw [map_add, map_mul]
      change
        (affineLocalizationMap a Polynomial.X *
            affineLocalizationMap a (Polynomial.X - Polynomial.C a) +
          affineLocalizationMap a (Polynomial.C (a ^ 2 - a))) *
            affineDenominatorInverse a =
          affineLocalizationMap a (Polynomial.C (a ^ 2 - a)) *
            affineDenominatorInverse a + affineLocalizationMap a Polynomial.X
      rw [add_mul, mul_assoc, hu, mul_one]
      ring
    have hgen :
        affineAmbientEvaluation a 0 ha0.symm (affineOpenThirdGenerator a) =
          affineAmbientEvaluation a 1 ha1.symm (affineOpenThirdGenerator a) := by
      simp [affineAmbientEvaluation, affineOpenThirdGenerator,
        affineDenominatorInverse, affineLocalizationMap]
      ring_nf
      calc
        a * a⁻¹ - a ^ 2 * a⁻¹ = 1 - a := by
          rw [show a ^ 2 * a⁻¹ = a * (a * a⁻¹) by ring,
            mul_inv_cancel₀ ha0]
          ring
        _ = 1 - a * (1 - a)⁻¹ + a ^ 2 * (1 - a)⁻¹ := by
          calc
            1 - a = 1 - a * ((1 - a) * (1 - a)⁻¹) := by
              rw [mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm ha1))]
              ring
            _ = 1 - a * (1 - a)⁻¹ + a ^ 2 * (1 - a)⁻¹ := by ring
    have hmain : ∀ (n : ℕ) (z : AffineAmbient a),
        z ∈ affineOpenEqualizer a ha0 ha1 →
        ∀ f : Polynomial ℚ,
          z * affineLocalizationMap a (Polynomial.X - Polynomial.C a) ^ n =
            affineLocalizationMap a f →
          z ∈ affineOpenSubalgebra a := by
      intro n
      induction n with
      | zero =>
          intro z hz f hf
          have hz' : z = affineLocalizationMap a f := by
            simpa using hf
          rw [hz']
          have hfeq : Polynomial.aeval (0 : ℚ) f = Polynomial.aeval (1 : ℚ) f := by
            change affineAmbientEvaluation a 0 ha0.symm z =
              affineAmbientEvaluation a 1 ha1.symm z at hz
            rw [hz'] at hz
            simpa [affineAmbientEvaluation, affineLocalizationMap] using hz
          let y : affineBaseSubalgebra := affineBaseElement f hfeq
          have hy : affineBaseImage a y ∈ affineOpenSubalgebra a :=
            Algebra.subset_adjoin (Or.inl ⟨y, rfl⟩)
          change affineLocalizationMap a (y : Polynomial ℚ) ∈
            affineOpenSubalgebra a at hy
          dsimp [y] at hy
          change affineLocalizationMap a f ∈ affineOpenSubalgebra a at hy
          exact hy
      | succ n ih =>
          intro z hz f hf
          let k : ℚ := f.eval a / (a ^ 2 - a) ^ (n + 1)
          have hroot :
              Polynomial.IsRoot (f -
                Polynomial.C k * q ^ (n + 1)) a := by
            rw [Polynomial.IsRoot]
            simp [q, k, hc]
          rcases (Polynomial.dvd_iff_isRoot).2 hroot with ⟨f₁, hf₁⟩
          have hfeq : f =
              (Polynomial.X - Polynomial.C a) * f₁ +
                Polynomial.C k * q ^ (n + 1) := by
            simpa [add_comm] using (sub_eq_iff_eq_add.mp hf₁)
          let z₁ : AffineAmbient a :=
            affineLocalizationMap a f₁ *
              affineDenominatorInverse a ^ n
          have hzrep : z = affineLocalizationMap a f *
              affineDenominatorInverse a ^ (n + 1) := by
            have hpow :
                affineLocalizationMap a (Polynomial.X - Polynomial.C a) ^ (n + 1) *
                    affineDenominatorInverse a ^ (n + 1) = 1 := by
              rw [← mul_pow, hu, one_pow]
            calc
              z = z * 1 := (mul_one z).symm
              _ = z *
                  (affineLocalizationMap a (Polynomial.X - Polynomial.C a) ^ (n + 1) *
                    affineDenominatorInverse a ^ (n + 1)) := by rw [hpow]
              _ = (z * affineLocalizationMap a
                    (Polynomial.X - Polynomial.C a) ^ (n + 1)) *
                    affineDenominatorInverse a ^ (n + 1) := by ring
              _ = affineLocalizationMap a f *
                    affineDenominatorInverse a ^ (n + 1) := by rw [hf]
          have hzsum :
              z = z₁ +
                algebraMap ℚ (AffineAmbient a) k *
                  (affineOpenThirdGenerator a) ^ (n + 1) := by
            rw [hzrep, hfeq, map_add, map_mul, map_mul, map_pow, add_mul]
            calc
              (affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
                    affineLocalizationMap a f₁) *
                  affineDenominatorInverse a ^ (n + 1) +
                affineLocalizationMap a (Polynomial.C k) *
                    affineLocalizationMap a q ^ (n + 1) *
                  affineDenominatorInverse a ^ (n + 1) =
                  affineLocalizationMap a f₁ *
                      affineDenominatorInverse a ^ n *
                      (affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
                        affineDenominatorInverse a) +
                    affineLocalizationMap a (Polynomial.C k) *
                      (affineLocalizationMap a q *
                        affineDenominatorInverse a) ^ (n + 1) := by
                congr 1
                · rw [pow_succ]
                  ring
                · calc
                    affineLocalizationMap a (Polynomial.C k) *
                          affineLocalizationMap a q ^ (n + 1) *
                        affineDenominatorInverse a ^ (n + 1) =
                      affineLocalizationMap a (Polynomial.C k) *
                        (affineLocalizationMap a q ^ (n + 1) *
                          affineDenominatorInverse a ^ (n + 1)) := by ring
                    _ = affineLocalizationMap a (Polynomial.C k) *
                        (affineLocalizationMap a q *
                          affineDenominatorInverse a) ^ (n + 1) := by
                      rw [← mul_pow]
              _ = affineLocalizationMap a f₁ *
                      affineDenominatorInverse a ^ n +
                    algebraMap ℚ (AffineAmbient a) k *
                      (affineLocalizationMap a q *
                        affineDenominatorInverse a) ^ (n + 1) := by
                rw [hu, mul_one]
                congr 1
              _ = z₁ +
                    algebraMap ℚ (AffineAmbient a) k *
                      (affineOpenThirdGenerator a) ^ (n + 1) := by
                dsimp [z₁]
                simpa only [hq]
          have hz₁ : z₁ ∈ affineOpenEqualizer a ha0 ha1 := by
            change affineAmbientEvaluation a 0 ha0.symm z₁ =
              affineAmbientEvaluation a 1 ha1.symm z₁
            change affineAmbientEvaluation a 0 ha0.symm z =
              affineAmbientEvaluation a 1 ha1.symm z at hz
            rw [hzsum] at hz
            simp only [map_add, map_mul, map_pow] at hz
            rw [hgen] at hz
            simpa [affineAmbientEvaluation] using hz
          have hf₁' :
              z₁ * affineLocalizationMap a (Polynomial.X - Polynomial.C a) ^ n =
                affineLocalizationMap a f₁ := by
            dsimp [z₁]
            have huv : affineDenominatorInverse a *
                affineLocalizationMap a (Polynomial.X - Polynomial.C a) = 1 := by
              rw [mul_comm, hu]
            calc
              affineLocalizationMap a f₁ * affineDenominatorInverse a ^ n *
                  affineLocalizationMap a (Polynomial.X - Polynomial.C a) ^ n =
                affineLocalizationMap a f₁ *
                  (affineDenominatorInverse a ^ n *
                    affineLocalizationMap a (Polynomial.X - Polynomial.C a) ^ n) := by
                      ring
              _ = affineLocalizationMap a f₁ *
                  (affineDenominatorInverse a *
                    affineLocalizationMap a (Polynomial.X - Polynomial.C a)) ^ n := by
                      rw [← mul_pow]
              _ = affineLocalizationMap a f₁ := by rw [huv, one_pow, mul_one]
          have hz₁' := ih z₁ hz₁ f₁ hf₁'
          rw [hzsum]
          exact (affineOpenSubalgebra a).add_mem hz₁'
            ((affineOpenSubalgebra a).mul_mem
              ((affineOpenSubalgebra a).algebraMap_mem k)
              ((affineOpenSubalgebra a).pow_mem
                (Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))) (n + 1)))
    intro z hz
    obtain ⟨n, f, hf⟩ := IsLocalization.Away.surj
      (R := Polynomial ℚ) (S := AffineAmbient a)
      (x := Polynomial.X - Polynomial.C a) z
    exact hmain n z hz f hf

theorem affine_open_isFiniteType (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    Algebra.FiniteType ℚ (AffineOpenRing a) := by
  change Algebra.FiniteType ℚ (affineOpenSubalgebra a)
  rw [affine_open_is_generated_by_three a ha0 ha1 haHalf]
  exact Algebra.FiniteType.adjoin_of_finite (by simp)

theorem affine_localization_evaluation_exists (a r : ℚ) (har : r ≠ a) :
    ∃ e : AffineAmbient a →+* ℚ,
      e.comp (affineLocalizationMap a) = Polynomial.evalRingHom r := by
  let e : AffineAmbient a →+* ℚ :=
    IsLocalization.Away.lift (g := Polynomial.evalRingHom r)
      (x := Polynomial.X - Polynomial.C a) (by
        rw [isUnit_iff_ne_zero]
        simpa using sub_ne_zero.mpr har)
  refine ⟨e, ?_⟩
  simp [e, affineLocalizationMap]

def affineEvaluation (r : ℚ) : affineBaseSubalgebra →+* ℚ :=
  (Polynomial.evalRingHom r).comp affineBaseSubalgebra.val.toRingHom

def affineMaximalIdeal (r : ℚ) : Ideal affineBaseSubalgebra :=
  RingHom.ker (affineEvaluation r)

theorem affineMaximalIdeal_isMaximal (r : ℚ) :
    (affineMaximalIdeal r).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective (affineEvaluation r)
  intro q
  refine ⟨algebraMap ℚ affineBaseSubalgebra q, ?_⟩
  simp [affineEvaluation]

def affinePoint (r : ℚ) : PrimeSpectrum affineBaseSubalgebra :=
  ⟨affineMaximalIdeal r, (affineMaximalIdeal_isMaximal r).isPrime⟩

abbrev affineM0 : Ideal affineBaseSubalgebra := affineMaximalIdeal 0

def affineMa (a : ℚ) : Ideal affineBaseSubalgebra := affineMaximalIdeal a

def affineMOneMinusA (a : ℚ) : Ideal affineBaseSubalgebra :=
  affineMaximalIdeal (1 - a)

private theorem affine_base_subtract_eval_mem
    (r : ℚ) (J : Ideal affineBaseSubalgebra)
    (hA : affineA -
        algebraMap ℚ affineBaseSubalgebra (affineEvaluation r affineA) ∈ J)
    (hB : affineB -
        algebraMap ℚ affineBaseSubalgebra (affineEvaluation r affineB) ∈ J)
    (z : Polynomial ℚ)
    (hz : z ∈ Algebra.adjoin ℚ
      ({(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)} :
        Set (Polynomial ℚ)))
    (heq : Polynomial.aeval (0 : ℚ) z = Polynomial.aeval (1 : ℚ) z) :
    affineBaseElement z heq -
        algebraMap ℚ affineBaseSubalgebra
          (affineEvaluation r (affineBaseElement z heq)) ∈ J := by
  refine Algebra.adjoin_induction (R := ℚ) (A := Polynomial ℚ)
    (s := {(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)})
    (p := fun z _ => ∀ heq : Polynomial.aeval (0 : ℚ) z =
        Polynomial.aeval (1 : ℚ) z,
      affineBaseElement z heq -
          algebraMap ℚ affineBaseSubalgebra
            (affineEvaluation r (affineBaseElement z heq)) ∈ J) ?_ ?_ ?_ ?_ hz heq
  · intro z hz' heq
    have hzcases : z = (affineA : Polynomial ℚ) ∨
        z = (affineB : Polynomial ℚ) := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz'
    rcases hzcases with rfl | rfl
    · have h : affineBaseElement (affineA : Polynomial ℚ) heq = affineA := by
        apply Subtype.ext
        rfl
      rw [h]
      exact hA
    · have h : affineBaseElement (affineB : Polynomial ℚ) heq = affineB := by
        apply Subtype.ext
        rfl
      rw [h]
      exact hB
  · intro c heq
    have h : affineBaseElement ((algebraMap ℚ (Polynomial ℚ)) c) heq =
        algebraMap ℚ affineBaseSubalgebra c := by
      apply Subtype.ext
      simp [affineBaseElement]
    rw [h]
    have heval : affineEvaluation r
        (algebraMap ℚ affineBaseSubalgebra c) = c := by
      simp [affineEvaluation]
    rw [heval]
    simpa only [sub_self] using J.zero_mem
  · intro x y hx hy hx' hy' heq
    have hxbase : x ∈ affineBaseSubalgebra := by
      rw [affine_base_is_generated_by_A_and_B]
      exact hx
    have hybase : y ∈ affineBaseSubalgebra := by
      rw [affine_base_is_generated_by_A_and_B]
      exact hy
    change Polynomial.aeval (0 : ℚ) x = Polynomial.aeval (1 : ℚ) x at hxbase
    change Polynomial.aeval (0 : ℚ) y = Polynomial.aeval (1 : ℚ) y at hybase
    have h : affineBaseElement (x + y) heq =
        affineBaseElement x hxbase + affineBaseElement y hybase := by
      apply Subtype.ext
      rfl
    rw [h, map_add, map_add]
    have hm := J.add_mem (hx' hxbase) (hy' hybase)
    convert hm using 1 <;> ring
  · intro x y hx hy hx' hy' heq
    have hxbase : x ∈ affineBaseSubalgebra := by
      rw [affine_base_is_generated_by_A_and_B]
      exact hx
    have hybase : y ∈ affineBaseSubalgebra := by
      rw [affine_base_is_generated_by_A_and_B]
      exact hy
    change Polynomial.aeval (0 : ℚ) x = Polynomial.aeval (1 : ℚ) x at hxbase
    change Polynomial.aeval (0 : ℚ) y = Polynomial.aeval (1 : ℚ) y at hybase
    have h : affineBaseElement (x * y) heq =
        affineBaseElement x hxbase * affineBaseElement y hybase := by
      apply Subtype.ext
      rfl
    rw [h, map_mul, map_mul]
    have h1 := J.mul_mem_left (affineBaseElement x hxbase) (hy' hybase)
    have h2 := J.mul_mem_right
      (algebraMap ℚ affineBaseSubalgebra
        (affineEvaluation r (affineBaseElement y hybase))) (hx' hxbase)
    have hm := J.add_mem h1 h2
    convert hm using 1 <;> ring

theorem affine_evaluation_kernel_formulas (a : ℚ) :
    affineM0 = Ideal.span {affineA, affineBZero} ∧
      affineMa a = Ideal.span {affineF1 a, affineF2AtA a} ∧
      affineMOneMinusA a =
        Ideal.span {affineF1 a, affineF2AtOneMinusA a} := by
  have hkernel :
      ∀ (r : ℚ) (J : Ideal affineBaseSubalgebra),
        J ≤ RingHom.ker (affineEvaluation r) →
        (affineA -
            algebraMap ℚ affineBaseSubalgebra
              (affineEvaluation r affineA) ∈ J) →
        (affineB -
            algebraMap ℚ affineBaseSubalgebra
              (affineEvaluation r affineB) ∈ J) →
        RingHom.ker (affineEvaluation r) = J := by
    intro r J hJ hA hB
    apply le_antisymm
    · intro y hy
      have hz : (y : Polynomial ℚ) ∈
          Algebra.adjoin ℚ ({(affineA : Polynomial ℚ), (affineB : Polynomial ℚ)} :
            Set (Polynomial ℚ)) := by
        rw [← affine_base_is_generated_by_A_and_B]
        exact y.property
      have heq : Polynomial.aeval (0 : ℚ) (y : Polynomial ℚ) =
          Polynomial.aeval (1 : ℚ) (y : Polynomial ℚ) := y.property
      have h := affine_base_subtract_eval_mem r J hA hB
        (y : Polynomial ℚ) hz heq
      have hy' : affineEvaluation r y = 0 := hy
      have hsub : affineBaseElement (y : Polynomial ℚ) y.property = y := by
        apply Subtype.ext
        rfl
      rw [hsub] at h
      simpa [hy'] using h
    · exact hJ
  have hM0 : affineM0 = Ideal.span {affineA, affineBZero} := by
    let J : Ideal affineBaseSubalgebra := Ideal.span {affineA, affineBZero}
    change RingHom.ker (affineEvaluation 0) = J
    refine hkernel 0 J ?_ ?_ ?_
    · apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · apply RingHom.mem_ker.mpr
        simp [affineEvaluation, affineA, affineBaseElement]
      · rcases Set.mem_singleton_iff.mp hx with rfl
        apply RingHom.mem_ker.mpr
        simp [affineEvaluation, affineBZero, affineBaseElement]
    · change affineA -
          algebraMap ℚ affineBaseSubalgebra
            (affineEvaluation 0 affineA) ∈ Ideal.span {affineA, affineBZero}
      simpa [affineEvaluation, affineA, affineBaseElement] using
        (Ideal.subset_span (s := ({affineA, affineBZero} :
          Set affineBaseSubalgebra)) (by simp) :
          affineA ∈ Ideal.span {affineA, affineBZero})
    · have hB0 : affineBZero - affineA ∈ J :=
        J.sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
      have heq : affineB -
            algebraMap ℚ affineBaseSubalgebra
              (affineEvaluation 0 affineB) = affineBZero - affineA := by
        apply Subtype.ext
        simp [affineEvaluation, affineB, affineBZero, affineA, affineBaseElement]
      rw [heq]
      exact hB0
  have hMa : affineMa a = Ideal.span {affineF1 a, affineF2AtA a} := by
    let J : Ideal affineBaseSubalgebra := Ideal.span {affineF1 a, affineF2AtA a}
    change RingHom.ker (affineEvaluation a) = J
    refine hkernel a J ?_ ?_ ?_
    · apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · apply RingHom.mem_ker.mpr
        simp [affineEvaluation, affineF1, affinePolynomialF1, affineBaseElement]
      · rcases Set.mem_singleton_iff.mp hx with rfl
        apply RingHom.mem_ker.mpr
        simp [affineEvaluation, affineF2AtA, affinePolynomialF2AtA,
          affineBaseElement]
    · have hF1 : affineF1 a ∈ J := Ideal.subset_span (by simp)
      have heq : affineA -
            algebraMap ℚ affineBaseSubalgebra
              (affineEvaluation a affineA) = affineF1 a := by
        apply Subtype.ext
        simp [affineEvaluation, affineA, affineF1, affinePolynomialF1,
          affineBaseElement]
        ring
      rw [heq]
      exact hF1
    · have hF1 : affineF1 a ∈ J := Ideal.subset_span (by simp)
      have hF2 : affineF2AtA a ∈ J := Ideal.subset_span (by simp)
      have hm := J.add_mem hF2
        (J.mul_mem_left (algebraMap ℚ affineBaseSubalgebra (a - 1)) hF1)
      have heq : affineB -
            algebraMap ℚ affineBaseSubalgebra
              (affineEvaluation a affineB) =
          affineF2AtA a +
            algebraMap ℚ affineBaseSubalgebra (a - 1) * affineF1 a := by
        apply Subtype.ext
        simp [affineEvaluation, affineB, affineF1, affineF2AtA,
          affinePolynomialF1, affinePolynomialF2AtA, affineA,
          affineBaseElement]
        ring
      rw [heq]
      exact hm
  have hMOneMinusA :
      affineMOneMinusA a = Ideal.span {affineF1 a, affineF2AtOneMinusA a} := by
    let J : Ideal affineBaseSubalgebra :=
      Ideal.span {affineF1 a, affineF2AtOneMinusA a}
    change RingHom.ker (affineEvaluation (1 - a)) = J
    refine hkernel (1 - a) J ?_ ?_ ?_
    · apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · apply RingHom.mem_ker.mpr
        simp [affineEvaluation, affineF1, affinePolynomialF1, affineBaseElement]
      · rcases Set.mem_singleton_iff.mp hx with rfl
        apply RingHom.mem_ker.mpr
        simp [affineEvaluation, affineF2AtOneMinusA,
          affinePolynomialF2AtOneMinusA, affineBaseElement]
    · have hF1 : affineF1 a ∈ J := Ideal.subset_span (by simp)
      have heq : affineA -
            algebraMap ℚ affineBaseSubalgebra
              (affineEvaluation (1 - a) affineA) = affineF1 a := by
        apply Subtype.ext
        simp [affineEvaluation, affineA, affineF1, affinePolynomialF1,
          affineBaseElement]
        ring
      rw [heq]
      exact hF1
    · have hF1 : affineF1 a ∈ J := Ideal.subset_span (by simp)
      have hF2 : affineF2AtOneMinusA a ∈ J := Ideal.subset_span (by simp)
      have hm := J.add_mem hF2
        (J.mul_mem_left (algebraMap ℚ affineBaseSubalgebra (-a)) hF1)
      have heq : affineB -
            algebraMap ℚ affineBaseSubalgebra
              (affineEvaluation (1 - a) affineB) =
          affineF2AtOneMinusA a -
            algebraMap ℚ affineBaseSubalgebra a * affineF1 a := by
        apply Subtype.ext
        simp [affineEvaluation, affineB, affineF1, affineF2AtOneMinusA,
          affinePolynomialF1, affinePolynomialF2AtOneMinusA, affineA,
          affineBaseElement]
        ring
      rw [heq]
      convert hm using 1
      rw [map_neg]
      ring
  exact ⟨hM0, hMa, hMOneMinusA⟩

theorem affine_evaluation_at_zero_extends (a : ℚ) (ha0 : a ≠ 0) :
    ∃ e : AffineOpenRing a →+* ℚ,
      e.comp (affineBaseToOpen a) = affineEvaluation 0 := by
  obtain ⟨e, he⟩ := affine_localization_evaluation_exists a 0 ha0.symm
  refine ⟨e.comp (affineOpenSubalgebra a).val.toRingHom, ?_⟩
  ext x
  change e (affineLocalizationMap a (x : Polynomial ℚ)) = Polynomial.eval 0 (x : Polynomial ℚ)
  simpa using congrArg (fun f : Polynomial ℚ →+* ℚ => f (x : Polynomial ℚ)) he

theorem affine_evaluation_at_one_minus_a_extends (a : ℚ) (haHalf : a ≠ 1 / 2) :
    ∃ e : AffineOpenRing a →+* ℚ,
      e.comp (affineBaseToOpen a) = affineEvaluation (1 - a) := by
  have har : 1 - a ≠ a := by
    intro h
    apply haHalf
    linarith
  obtain ⟨e, he⟩ := affine_localization_evaluation_exists a (1 - a) har
  refine ⟨e.comp (affineOpenSubalgebra a).val.toRingHom, ?_⟩
  ext x
  change e (affineLocalizationMap a (x : Polynomial ℚ)) =
    Polynomial.eval (1 - a) (x : Polynomial ℚ)
  simpa using congrArg (fun f : Polynomial ℚ →+* ℚ => f (x : Polynomial ℚ)) he

theorem affine_evaluation_at_a_does_not_extend (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ¬ ∃ e : AffineOpenRing a →+* ℚ,
      e.comp (affineBaseToOpen a) = affineEvaluation a := by
  rintro ⟨e, he⟩
  have hidentity :
      affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
          affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
            affineOpenThirdGenerator a =
        affineLocalizationMap a
            ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * Polynomial.C (a ^ 2 - a)) +
          affineLocalizationMap a
            ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 *
              (Polynomial.X - Polynomial.C a) * Polynomial.X) := by
    have hu : affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
        affineDenominatorInverse a = 1 := by
      change
        (↑((IsLocalization.Away.algebraMap_isUnit (R := Polynomial ℚ)
          (S := AffineAmbient a) (Polynomial.X - Polynomial.C a)).unit) :
            AffineAmbient a) *
          ↑((IsLocalization.Away.algebraMap_isUnit (R := Polynomial ℚ)
            (S := AffineAmbient a) (Polynomial.X - Polynomial.C a)).unit⁻¹) = 1
      simp
    rw [affineOpenThirdGenerator]
    calc
      affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
            affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
          (affineLocalizationMap a (Polynomial.C (a ^ 2 - a)) *
              affineDenominatorInverse a + affineLocalizationMap a Polynomial.X) =
        (affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
            affineLocalizationMap a (Polynomial.C (a ^ 2 - a))) *
            (affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
              affineDenominatorInverse a) +
          affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
            affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
              affineLocalizationMap a Polynomial.X := by ring
      _ = affineLocalizationMap a
            ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * Polynomial.C (a ^ 2 - a)) +
          affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
            affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
              affineLocalizationMap a Polynomial.X := by
        rw [hu, mul_one, map_mul]
      _ = _ := by
        congr 1
        rw [map_mul, map_mul]
  let pL : affineBaseSubalgebra :=
    affineBaseElement
      ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * (Polynomial.X - Polynomial.C a)) (by
        change Polynomial.aeval (0 : ℚ)
            ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * (Polynomial.X - Polynomial.C a)) =
          Polynomial.aeval (1 : ℚ)
            ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * (Polynomial.X - Polynomial.C a))
        simp only [map_mul, map_pow]
        simp)
  let pR : affineBaseSubalgebra :=
    affineBaseElement
      ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * Polynomial.C (a ^ 2 - a)) (by
        change Polynomial.aeval (0 : ℚ)
            ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * Polynomial.C (a ^ 2 - a)) =
          Polynomial.aeval (1 : ℚ)
            ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * Polynomial.C (a ^ 2 - a))
        simp only [map_mul, map_pow]
        simp)
  let pS : affineBaseSubalgebra :=
    affineBaseElement
      ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 *
        (Polynomial.X - Polynomial.C a) * Polynomial.X) (by
        change Polynomial.aeval (0 : ℚ)
            ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 *
              (Polynomial.X - Polynomial.C a) * Polynomial.X) =
          Polynomial.aeval (1 : ℚ)
            ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 *
              (Polynomial.X - Polynomial.C a) * Polynomial.X)
        simp only [map_mul, map_pow]
        simp)
  have hid :
      affineBaseToOpen a pL * affineOpenThird a =
        affineBaseToOpen a pR + affineBaseToOpen a pS := by
    apply Subtype.ext
    change affineLocalizationMap a
          ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * (Polynomial.X - Polynomial.C a)) *
        affineOpenThirdGenerator a =
      affineLocalizationMap a
          ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * Polynomial.C (a ^ 2 - a)) +
        affineLocalizationMap a
          ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 *
            (Polynomial.X - Polynomial.C a) * Polynomial.X)
    simpa only [map_mul] using hidentity
  have heval (p : affineBaseSubalgebra) :
      e (affineBaseToOpen a p) = affineEvaluation a p := by
    exact congrArg (fun f : affineBaseSubalgebra →+* ℚ => f p) he
  have hval := congrArg (fun z : AffineOpenRing a => e z) hid
  rw [map_mul, map_add, heval, heval, heval] at hval
  have hzero : affineEvaluation a pL = 0 := by
    change Polynomial.eval a
      ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * (Polynomial.X - Polynomial.C a)) = 0
    simp
  have hright : affineEvaluation a pR ≠ 0 := by
    change Polynomial.eval a
      ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * Polynomial.C (a ^ 2 - a)) ≠ 0
    simp
    intro hzero
    have hfactor : a * (a - 1) = 0 := by nlinarith [hzero]
    rcases mul_eq_zero.mp hfactor with h0 | h1
    · exact ha0 h0
    · exact ha1 (sub_eq_zero.mp h1)
  have hszero : affineEvaluation a pS = 0 := by
    change Polynomial.eval a
      ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 *
        (Polynomial.X - Polynomial.C a) * Polynomial.X) = 0
    simp
  rw [hzero, hszero, zero_mul, add_zero] at hval
  exact hright hval.symm

def affineOpenSpectrumMap (a : ℚ) :
    PrimeSpectrum (AffineOpenRing a) → PrimeSpectrum affineBaseSubalgebra :=
  PrimeSpectrum.comap (affineBaseToOpen a)

theorem affine_m_a_not_in_spectrum_image (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    ∀ I : Ideal (AffineOpenRing a),
      I.comap (affineBaseToOpen a) ≠ affineMa a := by
  sorry

theorem affine_obstruction_identity (a : ℚ) :
    affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
        affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
          affineOpenThirdGenerator a =
      affineLocalizationMap a
          ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * Polynomial.C (a ^ 2 - a)) +
        affineLocalizationMap a
          ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 *
            (Polynomial.X - Polynomial.C a) * Polynomial.X) := by
  have hu : affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
      affineDenominatorInverse a = 1 := by
    change
      (↑((IsLocalization.Away.algebraMap_isUnit (R := Polynomial ℚ)
        (S := AffineAmbient a) (Polynomial.X - Polynomial.C a)).unit) : AffineAmbient a) *
        ↑((IsLocalization.Away.algebraMap_isUnit (R := Polynomial ℚ)
          (S := AffineAmbient a) (Polynomial.X - Polynomial.C a)).unit⁻¹) = 1
    simp
  rw [affineOpenThirdGenerator]
  calc
    affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
          affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
        (affineLocalizationMap a (Polynomial.C (a ^ 2 - a)) *
            affineDenominatorInverse a + affineLocalizationMap a Polynomial.X) =
      (affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
          affineLocalizationMap a (Polynomial.C (a ^ 2 - a))) *
          (affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
            affineDenominatorInverse a) +
        affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
          affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
            affineLocalizationMap a Polynomial.X := by ring
    _ = affineLocalizationMap a
          ((Polynomial.X ^ 2 - Polynomial.X) ^ 2 * Polynomial.C (a ^ 2 - a)) +
        affineLocalizationMap a ((Polynomial.X ^ 2 - Polynomial.X) ^ 2) *
          affineLocalizationMap a (Polynomial.X - Polynomial.C a) *
            affineLocalizationMap a Polynomial.X := by
      rw [hu, mul_one, map_mul]
    _ = _ := by
      congr 1
      rw [map_mul, map_mul]

theorem affine_m_a_obstruction (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    (affineOpenA a) ^ 2 ∈
      Ideal.map (affineBaseToOpen a) (affineMa a) := by
  sorry

theorem affine_base_basic_open_f1_complement (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    (PrimeSpectrum.basicOpen (affineF1 a) : Set (PrimeSpectrum affineBaseSubalgebra))ᶜ =
      {affinePoint a, affinePoint (1 - a)} := by
  sorry

abbrev AffineBaseAway (a : ℚ) := Localization.Away (affineF1 a)

abbrev AffineOpenAway (a : ℚ) := Localization.Away (affineOpenF1 a)

theorem affine_away_rings_equivalent (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    Nonempty (AffineBaseAway a ≃+* AffineOpenAway a) := by
  sorry

theorem affine_first_basic_open_homeomorph (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    ∃ e :
        {p : PrimeSpectrum (AffineOpenRing a) //
            p ∈ (PrimeSpectrum.basicOpen (affineOpenF1 a) :
              Set (PrimeSpectrum (AffineOpenRing a)))} ≃ₜ
          {p : PrimeSpectrum affineBaseSubalgebra //
            p ∈ (PrimeSpectrum.basicOpen (affineF1 a) :
              Set (PrimeSpectrum affineBaseSubalgebra))},
      ∀ p, (e p).1 = affineOpenSpectrumMap a p.1 := by
  sorry

theorem affine_quadratic_at_one_minus_a (a : ℚ) :
    (affineQuadratic a).eval (1 - a) = 0 ↔ a = 0 ∨ a = 1 := by
  norm_num [affineQuadratic, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  constructor
  case mp =>
    intro h
    have h' : a * (a - 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp h' with h0 | h1
    · left
      exact h0
    · right
      linarith
  case mpr =>
    intro h
    rcases h with h0 | h1
    · subst a
      norm_num [affineQuadratic, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    · subst a
      norm_num [affineQuadratic, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

theorem affine_second_basic_open_complement (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    ∃ s : Finset (PrimeSpectrum affineBaseSubalgebra), 0 < s.card ∧ s.card ≤ 2 ∧
      (∀ p ∈ s,
        p.asIdeal.IsMaximal ∧ p ≠ affinePoint a ∧ affineG a ∈ p.asIdeal) ∧
      (PrimeSpectrum.basicOpen (affineG a) : Set (PrimeSpectrum affineBaseSubalgebra))ᶜ =
        {affinePoint a} ∪ (s : Set (PrimeSpectrum affineBaseSubalgebra)) := by
  sorry

theorem affine_second_basic_open_homeomorph (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    ∃ e :
        {p : PrimeSpectrum (AffineOpenRing a) //
            p ∈ (PrimeSpectrum.basicOpen (affineOpenG a) :
              Set (PrimeSpectrum (AffineOpenRing a)))} ≃ₜ
          {p : PrimeSpectrum affineBaseSubalgebra //
            p ∈ (PrimeSpectrum.basicOpen (affineG a) :
              Set (PrimeSpectrum affineBaseSubalgebra))},
      ∀ p, (e p).1 = affineOpenSpectrumMap a p.1 := by
  sorry

theorem affine_open_distinguished_opens_cover (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    Ideal.span {affineOpenF1 a, affineOpenG a} = (⊤ : Ideal (AffineOpenRing a)) := by
  sorry

theorem affine_second_open_avoids_one_minus_a (a : ℚ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (haHalf : a ≠ 1 / 2) :
    affinePoint (1 - a) ∈
      (PrimeSpectrum.basicOpen (affineG a) : Set (PrimeSpectrum affineBaseSubalgebra)) := by
  simp [PrimeSpectrum.basicOpen, affinePoint, affineMaximalIdeal, affineEvaluation,
    affineG, affinePolynomialG, affineQuadratic, affineBaseElement,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  constructor
  · intro h
    have h' : a * (a - 1) = 0 := by
      nlinarith [h]
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact ha0 h0
    · exact ha1 (by linarith)
  · intro h
    apply haHalf
    linarith

theorem affine_open_spectrum_range (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    Set.range (affineOpenSpectrumMap a) =
      ({affinePoint a} : Set (PrimeSpectrum affineBaseSubalgebra))ᶜ := by
  sorry

theorem affine_open_spectrum_homeomorph_complement (a : ℚ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (haHalf : a ≠ 1 / 2) :
    ∃ e : PrimeSpectrum (AffineOpenRing a) ≃ₜ
        {p : PrimeSpectrum affineBaseSubalgebra // p ≠ affinePoint a},
      ∀ p, (e p).1 = affineOpenSpectrumMap a p := by
  sorry

/-- The statement that all units are scalar units from `ℚ`. -/
def UnitsAreRationalScalars {A : Type*} [CommRing A] [Algebra ℚ A] : Prop :=
  ∀ u : Aˣ, ∃ q : ℚˣ, u = Units.map (algebraMap ℚ A) q

theorem affine_base_units_are_rational_scalars :
    UnitsAreRationalScalars (A := affineBaseSubalgebra) := by
  sorry

theorem affine_open_units_are_rational_scalars (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (haHalf : a ≠ 1 / 2) :
    UnitsAreRationalScalars (A := AffineOpenRing a) := by
  sorry

noncomputable def affineDenominatorUnit (a : ℚ) : (AffineAmbient a)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (Polynomial.X - Polynomial.C a)).unit

theorem affine_ambient_units_description (a : ℚ) (u : (AffineAmbient a)ˣ) :
    ∃ c : ℚˣ, ∃ n : ℤ,
      u = Units.map (algebraMap ℚ (AffineAmbient a)) c *
        affineDenominatorUnit a ^ n := by
  sorry

def IsLocalizationAlong {R A : Type*} [CommRing R] [CommRing A]
    (M : Submonoid R) (f : R →+* A) : Prop :=
  @IsLocalization R _ M A _ f.toAlgebra

theorem localization_inverts_denominators {R : Type*} [CommRing R]
    (M : Submonoid R) (s : M) :
    IsUnit (algebraMap R (Localization M) (s : R)) := by
  exact IsLocalization.map_units (Localization M) s

theorem affine_open_is_not_a_localization (a : ℚ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (haHalf : a ≠ 1 / 2) :
  ∀ M : Submonoid affineBaseSubalgebra,
      ¬ IsLocalizationAlong M (affineBaseToOpen a) := by
  sorry

theorem affine_half_denominator_power_mem_base (n : ℕ) :
    (Polynomial.X - Polynomial.C (1 / 2 : ℚ)) ^ n ∈ affineBaseSubalgebra ↔
      Even n := by
  change Polynomial.eval (0 : ℚ)
      ((Polynomial.X - Polynomial.C (1 / 2 : ℚ)) ^ n) =
        Polynomial.eval (1 : ℚ) ((Polynomial.X - Polynomial.C (1 / 2 : ℚ)) ^ n) ↔ _
  simp [Polynomial.eval_pow, Polynomial.eval_sub]
  constructor
  case mp =>
    intro h
    have hh : (-1 : ℚ) ^ n * (2⁻¹ : ℚ) ^ n = (2⁻¹ : ℚ) ^ n := by
      calc
        (-1 : ℚ) ^ n * (2⁻¹ : ℚ) ^ n = (-2⁻¹ : ℚ) ^ n := by
          rw [← mul_pow]
          congr 1
          ring
        _ = (1 - 2⁻¹ : ℚ) ^ n := h
        _ = (2⁻¹ : ℚ) ^ n := by norm_num
    have h' : (-1 : ℚ) ^ n = 1 := by
      apply (mul_right_cancel₀ (pow_ne_zero n (by norm_num : (2⁻¹ : ℚ) ≠ 0)))
      simpa using hh
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℚ) ≠ 1)).mp h'
  case mpr =>
    intro h
    have hh : (-1 : ℚ) ^ n = 1 :=
      (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℚ) ≠ 1)).mpr h
    calc
      (-2⁻¹ : ℚ) ^ n = ((-1 : ℚ) * 2⁻¹) ^ n := by
        congr 1
        ring
      _ = (-1 : ℚ) ^ n * (2⁻¹ : ℚ) ^ n := by rw [mul_pow]
      _ = (2⁻¹ : ℚ) ^ n := by rw [hh, one_mul]
      _ = (1 - 2⁻¹ : ℚ) ^ n := by norm_num

end

end Formalization.Books.Algebra.Unit27
