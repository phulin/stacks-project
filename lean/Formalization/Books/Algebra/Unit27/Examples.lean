import Formalization.Books.Algebra.Unit17.Spectrum
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Ideal.Int
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

theorem int_quadratic_reduction_mod_prime (q : ℕ) (hq : Nat.Prime q) :
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
        congr 1
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

theorem int_quadratic_prime_spectra_reduction_correspondence (q : ℕ) (hq : Nat.Prime q) :
    Nonempty
      (PrimeSpectrum
          (IntQuadraticRing ⧸
            Ideal.span {intQuadraticQuotientMap (Polynomial.C (q : ℤ))}) ≃
        PrimeSpectrum
          (Polynomial (ℤ ⧸ Ideal.span {(q : ℤ)}) ⧸
            Ideal.span {Polynomial.X ^ 2 -
              Polynomial.C (4 : ℤ ⧸ Ideal.span {(q : ℤ)})})) := by
  exact Nonempty.map (fun e => (PrimeSpectrum.comapEquiv e).toEquiv)
    (int_quadratic_reduction_mod_prime q hq)

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
    letI := hprime 2
    have hk : RingHom.ker intQuadraticQuotientMap ≤
        Ideal.span ({Polynomial.X - Polynomial.C (2 : ℤ)} : Set IntPolynomial) := by
      change RingHom.ker (Ideal.Quotient.mk intQuadraticRelation) ≤ _
      rw [Ideal.mk_ker]
      exact hle2
    have hm := Ideal.map_isPrime_of_surjective
      (f := intQuadraticQuotientMap) Ideal.Quotient.mk_surjective hk
    simpa [intQuadraticRootIdeal, Ideal.map_span] using hm
  have hmapNeg2 : (intQuadraticRootIdeal (-2)).IsPrime := by
    letI := hprime (-2)
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
    letI : Fact (Nat.Prime 2) := ⟨by decide⟩
    exact (Int.ideal_span_isMaximal_of_prime 2).isPrime
  have hcoeffDomain : IsDomain (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hcoeff
  have hJdomain : IsDomain (IntPolynomial ⧸ J) := by
    letI := hcoeffDomain
    change IsDomain (IntPolynomial ⧸
      Ideal.span {Polynomial.C (2 : ℤ), Polynomial.X - Polynomial.C (0 : ℤ)})
    apply (Polynomial.quotientSpanCXSubCAlgEquiv (2 : ℤ) 0).toMulEquiv.isDomain
  have hJprime : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp hJdomain
  have hrel : intQuadraticRelation ≤ J := by
    have hX : Polynomial.X - Polynomial.C (0 : ℤ) ∈ J :=
      Ideal.subset_span (by simp [J])
    have hC : Polynomial.C (2 : ℤ) ∈ J := Ideal.subset_span (by simp [J])
    have hxm : Polynomial.X - Polynomial.C (2 : ℤ) ∈ J := by
      simpa using J.sub_mem hX hC
    change Ideal.span ({Polynomial.X ^ 2 - Polynomial.C (4 : ℤ)} : Set IntPolynomial) ≤ J
    rw [int_quadratic_factorization]
    rw [Ideal.span_singleton_le_iff_mem]
    exact J.mul_mem_right (Polynomial.X + Polynomial.C 2) hxm
  letI := hJprime
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
    simp only [J, intQuadraticPrimeIdeal, Set.mem_insert_iff, Set.mem_singleton_iff,
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

theorem int_quadratic_prime_ideals_isPrime (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q) :
      (intQuadraticPrimeIdeal q 2).IsPrime ∧
      (intQuadraticPrimeIdeal q (-2)).IsPrime := by
  have hcoeff : (Ideal.span ({(q : ℤ)} : Set ℤ)).IsPrime := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    exact (Int.ideal_span_isMaximal_of_prime q).isPrime
  have hcoeffDomain : IsDomain (ℤ ⧸ Ideal.span ({(q : ℤ)} : Set ℤ)) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hcoeff
  let J (r : ℤ) : Ideal IntPolynomial :=
    Ideal.span {Polynomial.C (q : ℤ), Polynomial.X - Polynomial.C r}
  have hJdomain (r : ℤ) : IsDomain (IntPolynomial ⧸ J r) := by
    letI := hcoeffDomain
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
  sorry

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
  letI : Fact (Nat.Prime q) := ⟨hq⟩
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
    letI : I.IsMaximal := hI
    letI : Field (ℤ ⧸ I) := Ideal.Quotient.field I
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
      simpa only [hgen]
    have hKprime :
        (Ideal.span {Ideal.Quotient.mk M f}).IsPrime := by
      rw [← hmap]
      exact Ideal.map_isPrime_of_surjective ePoly.surjective
        (by simp)
    letI : IsDomain ((IntPolynomial ⧸ M) ⧸
        Ideal.span {Ideal.Quotient.mk M f}) :=
      (Ideal.Quotient.isDomain_iff_prime _).mpr hKprime
    have hKmap :
        Ideal.map (Ideal.Quotient.mk M) (Ideal.span {f}) =
          Ideal.span {Ideal.Quotient.mk M f} := by
      rw [Ideal.map_span]
      simp
    letI : IsDomain ((IntPolynomial ⧸ M) ⧸
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
  sorry

theorem int_polynomial_prime_ideal_is_zero_or_principal (P : Ideal IntPolynomial)
    (hP : P.IsPrime) (hcontraction : P.comap Polynomial.C = ⊥) :
    P = ⊥ ∨ ∃ f : IntPolynomial, 0 < f.natDegree ∧ Irreducible f ∧
      P = Ideal.span {f} := by
  sorry

theorem int_polynomial_prime_ideal_over_prime_is_zero_or_principal
    (P : Ideal IntPolynomial) (hP : P.IsPrime) (q : ℕ) (hq : Nat.Prime q)
    (hcontraction : P.comap Polynomial.C = Ideal.span {(q : ℤ)}) :
    P = intPolynomialPrimeIdeal q ∨
      ∃ f : IntPolynomial, 0 < f.natDegree ∧ IsIntegerPolynomialLift q f ∧
        P = intPolynomialPrimeAt q f := by
  sorry

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
  sorry

theorem bivariate_pair_intersects_univariate
    (k : Type*) [Field k] (f g : BivariatePolynomial k)
    (hf : Irreducible f) (hg : Irreducible g) (hnassoc : ¬Associated f g) :
    ∃ p : Polynomial k, p ≠ 0 ∧ Polynomial.C p ∈ bivariateTwoGeneratorIdeal f g := by
  sorry

theorem bivariate_prime_contains_univariate_irreducible
    (k : Type*) [Field k] (P : Ideal (BivariatePolynomial k)) (hP : P.IsPrime)
    (hnprincipal : ∀ f, P ≠ Ideal.span ({f} : Set (BivariatePolynomial k))) :
    ∃ p : Polynomial k, Irreducible p ∧ Polynomial.C p ∈ P := by
  sorry

theorem bivariate_univariate_quotient_isPID
    (k : Type*) [Field k] (p : Polynomial k) (hp : Irreducible p) :
    IsDomain (BivariateQuotient p) ∧ IsPrincipalIdealRing (BivariateQuotient p) := by
  let P : Ideal (Polynomial k) := Ideal.span {p}
  have hP : P.IsMaximal := by
    exact PrincipalIdealRing.isMaximal_of_irreducible hp
  letI : P.IsMaximal := hP
  letI : Field (Polynomial k ⧸ P) := Ideal.Quotient.field P
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
  sorry

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
  sorry

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
      simp [affinePresentationMap, affinePresentationValues]
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
  letI := h
  letI := h.toField
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
  sorry

theorem affine_presentation_primes_containing_relation
    (P : Ideal AffinePresentation) (hP : P.IsPrime)
    (hrel : Ideal.span {affinePresentationRelation} ≤ P) :
    P = Ideal.span {affinePresentationRelation} ∨ P.IsMaximal := by
  sorry

theorem affine_presentation_kernel :
    RingHom.ker affinePresentationMap.toRingHom =
      Ideal.span {affinePresentationRelation} := by
  sorry

/-- The induced presentation isomorphism has the direction determined by the
surjective map `ℚ[A,B] → R`: the quotient is isomorphic to `R`. -/
theorem affine_presentation_quotient_equiv :
    Nonempty ((AffinePresentation ⧸ Ideal.span {affinePresentationRelation}) ≃+*
      affineBaseSubalgebra) := by
  sorry

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
  sorry

theorem affine_open_is_equalizer (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    affineOpenSubalgebra a = affineOpenEqualizer a ha0 ha1 := by
  sorry

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
  simpa [e, affineLocalizationMap] using
    (IsLocalization.Away.lift_comp (S := AffineAmbient a)
      (x := Polynomial.X - Polynomial.C a) (g := Polynomial.evalRingHom r) _)

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

theorem affine_evaluation_kernel_formulas (a : ℚ) :
    affineM0 = Ideal.span {affineA, affineBZero} ∧
      affineMa a = Ideal.span {affineF1 a, affineF2AtA a} ∧
      affineMOneMinusA a =
        Ideal.span {affineF1 a, affineF2AtOneMinusA a} := by
  sorry

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
  sorry

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
