import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-!
# Commutative Algebra, Chapter 147: Integral closure and smooth base change

The integral closures in this section use Mathlib's canonical
integralClosure subalgebras. The comparison map is Mathlib's
TensorProduct.toIntegralClosure; the source-facing equivalences below are
constructed from its canonical bijectivity theorem.
-/

namespace Formalization.Books.Algebra.Unit147

open scoped BigOperators TensorProduct

noncomputable section

universe uR uS uB u

/-! ## The derivative trick -/

/-- The canonical model of B[X]/(f) for a polynomial f over R. -/
abbrev IntegralPolynomialQuotient
    (R : Type uR) (B : Type uB) [CommRing R] [CommRing B] [Algebra R B]
    (f : Polynomial R) : Type uB :=
  AdjoinRoot (f.map (algebraMap R B))

/-- The quotient map from B[X] to B[X]/(f). -/
def integralPolynomialQuotientMk
    (R : Type uR) (B : Type uB) [CommRing R] [CommRing B] [Algebra R B]
    (f : Polynomial R) :
    Polynomial B →+* IntegralPolynomialQuotient R B f :=
  AdjoinRoot.mk (f.map (algebraMap R B))

/- The source's f' h = sum b_i x^i formulation is represented by a
   polynomial representative whose coefficients are all integral. This is
   the specialization of Mathlib's more general quotient-algebra lemma. -/
theorem lemma_trick
    {R : Type uR} {B : Type uB} [CommRing R] [CommRing B] [Algebra R B]
    {f : Polynomial R} (hf : f.Monic)
    (h : IntegralPolynomialQuotient R B f) (hh : IsIntegral R h) :
    ∃ g : Polynomial B,
      integralPolynomialQuotientMk R B f
          (f.derivative.map (algebraMap R B)) * h =
        integralPolynomialQuotientMk R B f g ∧
      ∀ i, IsIntegral R (g.coeff i) := by
  let φ : Polynomial B →ₐ[R] IntegralPolynomialQuotient R B f :=
    { integralPolynomialQuotientMk R B f with
      commutes' := by
        intro r
        rw [AdjoinRoot.algebraMap_eq' R]
        rfl }
  have hmain :=
    exists_derivative_mul_eq_and_isIntegral_coeff (φ := φ)
      (f := f.map (algebraMap R B)) (y := h)
      (by exact AdjoinRoot.mk_surjective)
      (hf.map (algebraMap R B))
      (by
        intro i
        simp only [Polynomial.coeff_map]
        exact isIntegral_algebraMap)
      (by
        ext q
        simp [φ, integralPolynomialQuotientMk, AdjoinRoot.mk_eq_zero,
          Ideal.mem_span_singleton])
      hh
  simpa [φ, integralPolynomialQuotientMk, Polynomial.derivative_map] using hmain

/-! ## The etale comparison -/

/-- The canonical comparison map for integral closures is bijective after an
etale base change. -/
theorem integralClosure_baseChange_of_etale
    (R : Type uR) (S : Type uS) (B : Type uB) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Etale R S] :
    Function.Bijective
      (TensorProduct.toIntegralClosure R S B) := by
  exact TensorProduct.toIntegralClosure_bijective_of_smooth

/-- The canonical isomorphism asserted by the etale integral-closure lemma. -/
noncomputable def integralClosureEtaleBaseChangeEquiv
    (R : Type uR) (S : Type uS) (B : Type uB) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Etale R S] :
    S ⊗[R] integralClosure R B ≃ₐ[S]
      integralClosure S (S ⊗[R] B) :=
  AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R S B)
    (integralClosure_baseChange_of_etale R S B)

/-! ## The cyclotomic example -/

/-- The localization Z[1/p] used in the Fourier example. -/
abbrev fourierBaseRing (p : ℕ) : Type :=
  Localization.Away (p : ℤ)

/-- The geometric-sum polynomial appearing in the Fourier example.

For prime `p` this is the `p`-th cyclotomic polynomial, but the source
example is presented using the displayed geometric sum, so that is the
definition used here. -/
def fourierPolynomial (p : ℕ) (R : Type uR) [CommRing R] : Polynomial R :=
  ∑ i ∈ Finset.range p, (Polynomial.X : Polynomial R) ^ i

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

/-- The chosen presentation is the displayed geometric sum. -/
theorem fourierPolynomial_eq_geometric_sum
    (p : ℕ) (R : Type uR) [CommRing R] :
    fourierPolynomial p R =
      ∑ i ∈ Finset.range p, (Polynomial.X : Polynomial R) ^ i := by
  rfl

/-- The rational polynomial in the Fourier example is irreducible. -/
theorem fourierPolynomial_rat_irreducible
    (p : ℕ) (hp : Nat.Prime p) :
    Irreducible (fourierPolynomial p ℚ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hpoly : fourierPolynomial p ℚ = Polynomial.cyclotomic p ℚ := by
    rw [fourierPolynomial_eq_geometric_sum p ℚ]
    exact (Polynomial.cyclotomic_prime ℚ p).symm
  rw [hpoly]
  exact Polynomial.cyclotomic.irreducible_rat hp.pos

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
  let : Fact p.Prime := ⟨hp⟩
  have hpoly :
      fourierPolynomial p (fourierBaseRing p) *
          (Polynomial.X - 1) =
        Polynomial.X ^ p - 1 := by
    simpa [fourierPolynomial, Polynomial.cyclotomic_prime] using
      (Polynomial.cyclotomic_prime_mul_X_sub_one (fourierBaseRing p) p)
  have hpow : (fourierRoot p) ^ p = 1 := by
    have h := congrArg
      (fun q : Polynomial (fourierBaseRing p) =>
        q.eval₂ (AdjoinRoot.of (fourierPolynomial p (fourierBaseRing p)))
          (fourierRoot p)) hpoly
    simp [fourierRoot, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_one,
      AdjoinRoot.eval₂_root] at h
    exact sub_eq_zero.mp h.symm
  have hi_pow : (fourierRoot p ^ (i : ℕ)) ^ p = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hpow, one_pow]
  rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  simp [hi_pow]

private theorem fourier_root_is_primitive_root
    (p : ℕ) (hp : Nat.Prime p) :
    IsPrimitiveRoot (fourierRoot p) p := by
  let hfact : Fact p.Prime := ⟨hp⟩
  let f : Polynomial (fourierBaseRing p) :=
    fourierPolynomial p (fourierBaseRing p)
  have hpZ : (p : ℤ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hdom : IsDomain (fourierBaseRing p) :=
    Localization.Away.isDomain hpZ
  have hnontriv : Nontrivial (fourierBaseRing p) := hdom.toNontrivial
  have hfcycl : f = Polynomial.cyclotomic p (fourierBaseRing p) := by
    simpa [f, fourierPolynomial] using
      (@Polynomial.cyclotomic_prime (fourierBaseRing p) _ p hfact).symm
  have hfmonic : f.Monic := by
    rw [hfcycl]
    exact Polynomial.cyclotomic.monic p (fourierBaseRing p)
  have hfnat : f.natDegree = p - 1 := by
    calc
      f.natDegree = (Polynomial.cyclotomic p (fourierBaseRing p)).natDegree := by
        rw [hfcycl]
      _ = Nat.totient p :=
        @Polynomial.natDegree_cyclotomic p (fourierBaseRing p) _ hnontriv
      _ = p - 1 := Nat.totient_prime hp
  have hfd : f.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hfmonic.ne_zero, hfnat]
    exact_mod_cast (Nat.sub_pos_iff_lt.mpr hp.one_lt).ne'
  have hpow : fourierRoot p ^ p = 1 := by
    have hr := fourier_root_is_root p hp ⟨1, hp.one_lt⟩
    have hr' : fourierRoot p ^ p - 1 = 0 := by
      simpa [Polynomial.IsRoot] using hr
    exact sub_eq_zero.mp hr'
  have hne_one : fourierRoot p ≠ 1 := by
    intro hx
    let : IsDomain (fourierBaseRing p) := hdom
    have hof : Function.Injective (AdjoinRoot.of f) :=
      AdjoinRoot.of.injective_of_degree_ne_zero hfd
    have hroot := AdjoinRoot.eval₂_root f
    have hx' : AdjoinRoot.root f = 1 := by
      simpa [f, fourierRoot] using hx
    rw [hx'] at hroot
    have hsum : f = ∑ k ∈ Finset.range p,
        (Polynomial.X : Polynomial (fourierBaseRing p)) ^ k := by
      rfl
    have heval := congrArg
      (fun q : Polynomial (fourierBaseRing p) =>
        q.eval₂ (AdjoinRoot.of f) 1) hsum
    have hpq : AdjoinRoot.of f (p : fourierBaseRing p) = 0 := by
      have heval' :
          (∑ k ∈ Finset.range p,
            (Polynomial.X : Polynomial (fourierBaseRing p)) ^ k).eval₂
              (AdjoinRoot.of f) 1 = 0 := by
        rw [← heval, hroot]
      simpa [Polynomial.eval₂_finsetSum] using heval'
    have hmap : Function.Injective (algebraMap ℤ (fourierBaseRing p)) :=
      IsLocalization.injective (fourierBaseRing p)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hpZ)
    have hpne : (p : fourierBaseRing p) ≠ 0 := by
      intro hz
      have hz' : (p : ℤ) = 0 := by
        apply hmap
        simpa using hz
      exact hp.ne_zero (by exact_mod_cast hz')
    apply hpne
    apply hof
    simpa using hpq
  let : NeZero p := ⟨hp.ne_zero⟩
  refine IsPrimitiveRoot.mk_of_lt _ hp.pos hpow ?_
  intro l hl hlbound
  by_cases hlt : l < p - 1
  · have hq0 :
        (Polynomial.X : Polynomial (fourierBaseRing p)) ^ l -
            Polynomial.C 1 ≠ 0 :=
      @Polynomial.X_pow_sub_C_ne_zero (fourierBaseRing p) _ hnontriv l hl 1
    have hne := AdjoinRoot.mk_ne_zero_of_natDegree_lt hfmonic hq0
      (by rw [Polynomial.natDegree_X_pow_sub_C, hfnat]; exact hlt)
    intro hpow_l
    apply hne
    have hmk :
        AdjoinRoot.mk f
            ((Polynomial.X : Polynomial (fourierBaseRing p)) ^ l -
              Polynomial.C 1) =
          fourierRoot p ^ l - 1 := by
      simp [f, fourierRoot]
    rw [hmk, sub_eq_zero.mpr hpow_l]
  · have hl_eq : l = p - 1 := by omega
    subst l
    intro hlast
    apply hne_one
    calc
      fourierRoot p = fourierRoot p * 1 := (mul_one _).symm
      _ = fourierRoot p * fourierRoot p ^ (p - 1) := by rw [hlast]
      _ = fourierRoot p ^ p := by
        rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
      _ = 1 := hpow

/-- The explicit roots are pairwise distinct. -/
theorem fourier_roots_injective
    (p : ℕ) (hp : Nat.Prime p) :
    Function.Injective (fourierRoots p p) := by
  have hprim := fourier_root_is_primitive_root p hp
  intro i j hij
  exact Fin.ext (hprim.pow_inj i.isLt j.isLt hij)

/-- The factorization of T^p - 1 in the Fourier extension. -/
theorem fourier_factorization
    (p : ℕ) (hp : Nat.Prime p) :
    (Polynomial.X ^ p - Polynomial.C (1 : fourierExtension p)) =
      fourierFactorizationProduct p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hbase : IsDomain (fourierBaseRing p) :=
    Localization.Away.isDomain (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
  let : IsDomain (fourierBaseRing p) := hbase
  have hIC : IsIntegrallyClosed (fourierBaseRing p) :=
    isIntegrallyClosed_of_isLocalization (R := ℤ) (S := fourierBaseRing p)
      (Submonoid.powers (p : ℤ))
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero))
  let : IsIntegrallyClosed (fourierBaseRing p) := hIC
  let : Algebra ℤ ℚ := Ring.toIntAlgebra ℚ
  have hpQ : IsUnit ((algebraMap ℤ ℚ) (p : ℤ)) := by
    rw [isUnit_iff_ne_zero]
    intro hz
    apply hp.ne_zero
    have hz' : (p : ℚ) = 0 := by simpa using hz
    exact_mod_cast hz'
  let g : fourierBaseRing p →+* ℚ :=
    IsLocalization.Away.lift (p : ℤ) hpQ
  let : Algebra (fourierBaseRing p) ℚ := g.toAlgebra
  let : SMul ℤ (fourierBaseRing p) :=
    (inferInstance : Algebra ℤ (fourierBaseRing p)).toSMul
  let : SMul ℤ ℚ := (inferInstance : Algebra ℤ ℚ).toSMul
  have hscalar : IsScalarTower ℤ (fourierBaseRing p) ℚ :=
    IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := fourierBaseRing p) (A := ℚ) (by
      ext z
      change (algebraMap ℤ ℚ) z = g (algebraMap ℤ (fourierBaseRing p) z)
      simp [g])
  let : IsScalarTower ℤ (fourierBaseRing p) ℚ := hscalar
  let : IsFractionRing (fourierBaseRing p) ℚ :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (M := Submonoid.powers (p : ℤ)) (fourierBaseRing p) ℚ
  have hmonic : (fourierPolynomial p (fourierBaseRing p)).Monic := by
    rw [show fourierPolynomial p (fourierBaseRing p) =
        Polynomial.cyclotomic p (fourierBaseRing p) by
      simpa [fourierPolynomial] using
        (Polynomial.cyclotomic_prime (fourierBaseRing p) p).symm]
    exact Polynomial.cyclotomic.monic p (fourierBaseRing p)
  have hirr : Irreducible (fourierPolynomial p (fourierBaseRing p)) := by
    rw [hmonic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)]
    have hmap_poly :
        (fourierPolynomial p (fourierBaseRing p)).map
            (algebraMap (fourierBaseRing p) ℚ) =
          fourierPolynomial p ℚ := by
      simp only [fourierPolynomial, Polynomial.map_sum, Polynomial.map_pow,
        Polynomial.map_X]
    rw [hmap_poly]
    exact fourierPolynomial_rat_irreducible p hp
  have hprime : Prime (fourierPolynomial p (fourierBaseRing p)) :=
    hirr.prime
  let : IsDomain (fourierExtension p) :=
    AdjoinRoot.isDomain_of_prime hprime
  let : NeZero p := ⟨hp.ne_zero⟩
  have hprim := fourier_root_is_primitive_root p hp
  have hset :
      Finset.univ.image (fourierRoots p p) =
        Polynomial.nthRootsFinset p (1 : fourierExtension p) := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
      rw [Polynomial.mem_nthRootsFinset hp.pos]
      have hi := fourier_root_is_root p hp i
      have hi' :
          (fourierRoot p ^ (i : ℕ)) ^ p - 1 = 0 := by
        simpa [fourierRoots, Polynomial.IsRoot] using hi
      exact sub_eq_zero.mp hi'
    · intro x hx
      rw [Polynomial.mem_nthRootsFinset hp.pos] at hx
      obtain ⟨i, hi, hxi⟩ := hprim.eq_pow_of_pow_eq_one hx
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, by
        simpa [fourierRoots] using hxi⟩
  have hprod :
      (∏ x ∈ Finset.univ.image (fourierRoots p p),
        (Polynomial.X - Polynomial.C x)) =
        fourierFactorizationProduct p := by
    rw [Finset.prod_image]
    · rfl
    · intro i hi j hj hij
      exact fourier_roots_injective p hp hij
  calc
    Polynomial.X ^ p - Polynomial.C (1 : fourierExtension p) =
        Polynomial.X ^ p - 1 := by rfl
    _ = ∏ ζ ∈ Polynomial.nthRootsFinset p (1 : fourierExtension p),
        (Polynomial.X - Polynomial.C ζ) :=
      Polynomial.X_pow_sub_one_eq_prod hp.pos hprim
    _ = ∏ x ∈ Finset.univ.image (fourierRoots p p),
        (Polynomial.X - Polynomial.C x) := by rw [hset]
    _ = fourierFactorizationProduct p := hprod

/-- Differentiating the Fourier factorization at an explicit root gives the
product of all its pairwise differences. -/
theorem fourier_derivative_at_root
    (p : ℕ) (hp : Nat.Prime p) (i : Fin p) :
    (p : fourierExtension p) *
        (fourierRoot p ^ (i : ℕ)) ^ (p - 1) =
      ∏ j ∈ Finset.univ.erase i,
        (fourierRoot p ^ (i : ℕ) - fourierRoot p ^ (j : ℕ)) := by
  classical
  have hfac := fourier_factorization p hp
  have hder := congrArg Polynomial.derivative hfac
  have heval := congrArg
    (fun q : Polynomial (fourierExtension p) =>
      q.eval (fourierRoot p ^ (i : ℕ))) hder
  simp only [Polynomial.derivative_sub, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    fourierFactorizationProduct, Polynomial.derivative_prod_finset,
    Polynomial.eval_finsetSum, Polynomial.eval_prod] at heval
  simp only [Polynomial.eval_X, Polynomial.eval_X_pow, Polynomial.eval_one,
    Polynomial.eval_zero, sub_zero, mul_one] at heval
  have hsum :
      (∑ x : Fin p, ∏ y ∈ Finset.univ.erase x,
        (fourierRoot p ^ (i : ℕ) - fourierRoot p ^ (y : ℕ))) =
        ∏ y ∈ Finset.univ.erase i,
          (fourierRoot p ^ (i : ℕ) - fourierRoot p ^ (y : ℕ)) := by
    apply Finset.sum_eq_single i
    · intro a ha hai
      have hmem : i ∈ Finset.univ.erase a :=
        Finset.mem_erase.mpr ⟨hai.symm, Finset.mem_univ _⟩
      rw [Finset.prod_eq_zero hmem]
      exact sub_self _
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  calc
    ↑p * (fourierRoot p ^ (i : ℕ)) ^ (p - 1) =
        ∑ x : Fin p, ∏ y ∈ Finset.univ.erase x,
          (fourierRoot p ^ (i : ℕ) - fourierRoot p ^ (y : ℕ)) := heval
    _ = _ := hsum

/-- The derivative product in the source proof is a unit. -/
theorem fourier_derivative_product_isUnit
    (p : ℕ) (hp : Nat.Prime p) (i : Fin p) :
    IsUnit
      (∏ j ∈ Finset.univ.erase i,
        (fourierRoot p ^ (i : ℕ) - fourierRoot p ^ (j : ℕ))) := by
  classical
  rw [← fourier_derivative_at_root p hp i]
  apply IsUnit.mul
  · have hbase :
        IsUnit (algebraMap (ℤ) (fourierBaseRing p) (p : ℤ)) :=
      IsLocalization.Away.algebraMap_isUnit (R := ℤ)
        (S := fourierBaseRing p) p
    have htotal :
        IsUnit
          (algebraMap (fourierBaseRing p) (fourierExtension p)
            (algebraMap (ℤ) (fourierBaseRing p) (p : ℤ))) :=
      IsUnit.map (algebraMap (fourierBaseRing p) (fourierExtension p)) hbase
    simpa using htotal
  · have hpow : fourierRoot p ^ p = 1 := by
      have hr := fourier_root_is_root p hp ⟨1, hp.one_lt⟩
      have hr' : fourierRoot p ^ p - 1 = 0 := by
        simpa [Polynomial.IsRoot] using hr
      exact sub_eq_zero.mp hr'
    have hi_pow : (fourierRoot p ^ (i : ℕ)) ^ p = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hpow, one_pow]
    exact (IsUnit.of_pow_eq_one hi_pow hp.ne_zero).pow (p - 1)

/-- The explicit Fourier roots give a unit Vandermonde product whenever
d < p. -/
theorem fourier_vandermonde_isUnit
    (p d : ℕ) (hp : Nat.Prime p) (hd : d < p) :
    IsUnit (fourierVandermondeProduct p d) := by
  classical
  unfold fourierVandermondeProduct vandermondeProduct
  apply IsUnit.prod_iff.mpr
  intro i hi
  apply IsUnit.prod_iff.mpr
  intro j hj
  let ip : Fin p := ⟨(i : ℕ), lt_of_lt_of_le i.isLt hd.le⟩
  let jp : Fin p := ⟨(j : ℕ), lt_of_lt_of_le j.isLt hd.le⟩
  have hij : (i : ℕ) < (j : ℕ) := (Finset.mem_filter.mp hj).2
  have hne : ip ≠ jp := by
    intro h
    have hvals : (ip : ℕ) = (jp : ℕ) := congrArg Fin.val h
    exact (Nat.ne_of_lt hij) hvals
  have hmem : jp ∈ Finset.univ.erase ip :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  have hder := fourier_derivative_product_isUnit p hp ip
  have hdiff :
      ∀ k ∈ Finset.univ.erase ip,
        IsUnit (fourierRoot p ^ (ip : ℕ) - fourierRoot p ^ (k : ℕ)) :=
    (IsUnit.prod_iff.mp hder)
  simpa [fourierRoots, ip, jp] using hdiff jp hmem

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
    {R : Type uR} {B : Type uB} [CommRing R] [CommRing B] [Algebra R B]
    (f : Polynomial B) :
    IsIntegral (Polynomial R) f ↔ ∀ i, IsIntegral R (f.coeff i) :=
  Polynomial.isIntegral_iff_isIntegral_coeff

/-- The canonical comparison map for integral closures is bijective after a
smooth base change. -/
theorem integralClosure_baseChange_of_smooth
    (R : Type uR) (S : Type uS) (B : Type uB) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Smooth R S] :
    Function.Bijective
      (TensorProduct.toIntegralClosure R S B) :=
  TensorProduct.toIntegralClosure_bijective_of_smooth

/-- The canonical isomorphism asserted by the smooth integral-closure lemma. -/
noncomputable def integralClosureSmoothBaseChangeEquiv
    (R : Type uR) (S : Type uS) (B : Type uB) [CommRing R] [CommRing S] [CommRing B]
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
    (R S : Type u) (B : Type uB) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B]
    (D : FilteredSmoothAlgebraColimit R S) :
    Function.Bijective
  (TensorProduct.toIntegralClosure R S B) := by
  sorry

/-- The canonical isomorphism in the filtered-colimit statement. -/
noncomputable def integralClosureFilteredSmoothBaseChangeEquiv
    (R S : Type u) (B : Type uB) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B]
    (D : FilteredSmoothAlgebraColimit R S) :
    S ⊗[R] integralClosure R B ≃ₐ[S]
      integralClosure S (S ⊗[R] B) :=
  AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R S B)
    (integralClosure_baseChange_of_filtered_smooth R S B D)

end

end Formalization.Books.Algebra.Unit147
