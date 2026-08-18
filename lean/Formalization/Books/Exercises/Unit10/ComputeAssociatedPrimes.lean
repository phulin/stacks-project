import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Exercises, Chapter 10: associated primes

The first exercise asks for three explicit computations.  The associated-prime
sets below use Mathlib's canonical `associatedPrimes` definition; the rings
and quotient modules are kept in the same order as in the source.
-/

noncomputable section

universe u

namespace Formalization.Books.Exercises.Unit10

/-! ## `k[x,y]/(xy(x+y))` -/

/-- The two-variable polynomial ring in the first computation. -/
abbrev planePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

/-- The two coordinate variables. -/
def planeX (k : Type u) [Field k] : planePolynomialRing k :=
  MvPolynomial.X (0 : Fin 2)

def planeY (k : Type u) [Field k] : planePolynomialRing k :=
  MvPolynomial.X (1 : Fin 2)

/-- The displayed relation `xy(x+y)`. -/
def planeProductRelation (k : Type u) [Field k] : planePolynomialRing k :=
  planeX k * planeY k * (planeX k + planeY k)

/-- The principal relation ideal `(xy(x+y))`. -/
def planeProductIdeal (k : Type u) [Field k] : Ideal (planePolynomialRing k) :=
  Ideal.span ({planeProductRelation k} : Set (planePolynomialRing k))

/-- The quotient module in the first computation. -/
abbrev planeProductQuotient (k : Type u) [Field k] :=
  planePolynomialRing k ⧸ planeProductIdeal k

/-- The three candidate associated primes in `k[x,y]`. -/
def planeXPrimeIdeal (k : Type u) [Field k] : Ideal (planePolynomialRing k) :=
  Ideal.span ({planeX k} : Set (planePolynomialRing k))

def planeYPrimeIdeal (k : Type u) [Field k] : Ideal (planePolynomialRing k) :=
  Ideal.span ({planeY k} : Set (planePolynomialRing k))

def planeDiagonalPrimeIdeal (k : Type u) [Field k] : Ideal (planePolynomialRing k) :=
  Ideal.span ({planeX k + planeY k} : Set (planePolynomialRing k))

private theorem associated_primes_span_mul_subset_union
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    associatedPrimes R (R ⧸ Ideal.span ({a * b} : Set R)) ⊆
      associatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) ∪
        associatedPrimes R (R ⧸ Ideal.span ({b} : Set R)) := by
  let p : Ideal R := Ideal.span ({a} : Set R)
  let q : Ideal R := Ideal.span ({a * b} : Set R)
  let r : Ideal R := Ideal.span ({b} : Set R)
  have hpq : p ≤ Submodule.comap (LinearMap.lsmul R R b) (q : Submodule R R) := by
    change Ideal.span ({a} : Set R) ≤
      Submodule.comap (LinearMap.lsmul R R b) (Ideal.span ({a * b} : Set R))
    rw [Ideal.span_le]
    intro x hx
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst x
    change b * a ∈ Ideal.span ({a * b} : Set R)
    simpa [mul_comm] using
      (Ideal.subset_span (Set.mem_singleton (a * b)))
  have hqr : q ≤ r := by
    change Ideal.span ({a * b} : Set R) ≤ Ideal.span ({b} : Set R)
    rw [Ideal.span_le]
    intro x hx
    have hxab : x = a * b := Set.mem_singleton_iff.mp hx
    subst x
    simpa [mul_comm] using
      r.mul_mem_right a (Ideal.subset_span (Set.mem_singleton b))
  let f : (R ⧸ p) →ₗ[R] (R ⧸ q) :=
    Submodule.mapQ (p : Submodule R R) (q : Submodule R R)
      (LinearMap.lsmul R R b) hpq
  let g : (R ⧸ q) →ₗ[R] (R ⧸ r) :=
    Submodule.mapQ (q : Submodule R R) (r : Submodule R R) LinearMap.id hqr
  have hcomap : Submodule.comap (LinearMap.lsmul R R b) (q : Submodule R R) = p := by
    ext x
    constructor
    · intro hx
      change (LinearMap.lsmul R R b) x ∈ q at hx
      change b * x ∈ q at hx
      have hx' : b * x ∈ Ideal.span ({a * b} : Set R) := by
        simpa [q] using hx
      rcases Ideal.mem_span_singleton.mp hx' with ⟨c, hc⟩
      change x ∈ Ideal.span ({a} : Set R)
      rw [Ideal.mem_span_singleton]
      refine ⟨c, ?_⟩
      apply (mul_right_cancel₀ hb)
      simpa [mul_assoc, mul_comm, mul_left_comm] using hc
    · intro hx
      have hx' : x ∈ Ideal.span ({a} : Set R) := by simpa [p] using hx
      rcases Ideal.mem_span_singleton.mp hx' with ⟨c, hc⟩
      show (LinearMap.lsmul R R b) x ∈ q
      change b * x ∈ q
      simpa [q, hc, mul_assoc, mul_comm, mul_left_comm] using
        (Ideal.mul_mem_left (Ideal.span ({a * b} : Set R)) c
          (Ideal.subset_span (Set.mem_singleton (a * b))))
  have hf_injective : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  have hfg : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := q.mkQ_surjective y
      have hx : x ∈ r := by
        change r.mkQ x = 0 at hy
        exact (Submodule.Quotient.mk_eq_zero r).mp
          (by simpa only [Submodule.mkQ_apply] using hy)
      rcases Ideal.mem_span_singleton.mp hx with ⟨c, hc⟩
      refine ⟨p.mkQ c, ?_⟩
      simp only [f, Submodule.mapQ_apply, g, Submodule.mapQ_apply]
      apply congrArg q.mkQ
      simpa [mul_comm] using hc.symm
    · rintro ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := p.mkQ_surjective x
      simp only [f, g, Submodule.mapQ_apply]
      change (Submodule.Quotient.mk (b * z) : R ⧸ r) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simpa [mul_comm] using r.mul_mem_left z
        (Ideal.subset_span (Set.mem_singleton b))
  intro P hP
  exact (associatedPrimes.subset_union_of_exact hf_injective hfg) hP

private theorem associated_primes_span_mul_left_subset
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (a b : R) (hb : b ≠ 0) :
    associatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) ⊆
      associatedPrimes R (R ⧸ Ideal.span ({a * b} : Set R)) := by
  let p : Ideal R := Ideal.span ({a} : Set R)
  let q : Ideal R := Ideal.span ({a * b} : Set R)
  have hpq : p ≤ Submodule.comap (LinearMap.lsmul R R b) (q : Submodule R R) := by
    change Ideal.span ({a} : Set R) ≤
      Submodule.comap (LinearMap.lsmul R R b) (Ideal.span ({a * b} : Set R))
    rw [Ideal.span_le]
    intro x hx
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst x
    change b * a ∈ Ideal.span ({a * b} : Set R)
    simpa [mul_comm] using
      (Ideal.subset_span (Set.mem_singleton (a * b)))
  let f : (R ⧸ p) →ₗ[R] (R ⧸ q) :=
    Submodule.mapQ (p : Submodule R R) (q : Submodule R R)
      (LinearMap.lsmul R R b) hpq
  have hcomap : Submodule.comap (LinearMap.lsmul R R b) (q : Submodule R R) = p := by
    ext x
    constructor
    · intro hx
      change (LinearMap.lsmul R R b) x ∈ q at hx
      change b * x ∈ q at hx
      have hx' : b * x ∈ Ideal.span ({a * b} : Set R) := by
        simpa [q] using hx
      rcases Ideal.mem_span_singleton.mp hx' with ⟨c, hc⟩
      change x ∈ Ideal.span ({a} : Set R)
      rw [Ideal.mem_span_singleton]
      refine ⟨c, ?_⟩
      apply (mul_right_cancel₀ hb)
      simpa [mul_assoc, mul_comm, mul_left_comm] using hc
    · intro hx
      have hx' : x ∈ Ideal.span ({a} : Set R) := by simpa [p] using hx
      rcases Ideal.mem_span_singleton.mp hx' with ⟨c, hc⟩
      show (LinearMap.lsmul R R b) x ∈ q
      change b * x ∈ q
      simpa [q, hc, mul_assoc, mul_comm, mul_left_comm] using
        (Ideal.mul_mem_left (Ideal.span ({a * b} : Set R)) c
          (Ideal.subset_span (Set.mem_singleton (a * b))))
  have hf_injective : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  intro P hP
  exact associatedPrimes.subset_of_injective hf_injective hP

private theorem associated_primes_span_singleton_of_prime
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (a : R) (ha : (Ideal.span ({a} : Set R)).IsPrime) :
    associatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) =
      ({Ideal.span ({a} : Set R)} : Set (Ideal R)) := by
  simpa [ha.radical] using
    (associatedPrimes.eq_singleton_of_isPrimary ha.isPrimary)

private theorem associated_primes_quotient_of_prime
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I.IsPrime) :
    associatedPrimes R (R ⧸ I) = ({I} : Set (Ideal R)) := by
  simpa [hI.radical] using
    (associatedPrimes.eq_singleton_of_isPrimary hI.isPrimary)

private theorem associated_primes_quotient_mul_subset
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (a : R) (p q r : Ideal R)
    (hpq : p ≤ Submodule.comap (LinearMap.lsmul R R a) (q : Submodule R R))
    (hcomap : Submodule.comap (LinearMap.lsmul R R a) (q : Submodule R R) = p)
    (hqr : q ≤ r) (ha : a ∈ r)
    (hrange : ∀ z, z ∈ r → ∃ w, z - a * w ∈ q) :
    associatedPrimes R (R ⧸ p) ⊆ associatedPrimes R (R ⧸ q) ∧
      associatedPrimes R (R ⧸ q) ⊆
        associatedPrimes R (R ⧸ p) ∪ associatedPrimes R (R ⧸ r) := by
  let f : (R ⧸ p) →ₗ[R] (R ⧸ q) :=
    Submodule.mapQ (p : Submodule R R) (q : Submodule R R)
      (LinearMap.lsmul R R a) hpq
  let g : (R ⧸ q) →ₗ[R] (R ⧸ r) :=
    Submodule.mapQ (q : Submodule R R) (r : Submodule R R) LinearMap.id hqr
  have hf_injective : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  have hfg : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := q.mkQ_surjective y
      have hx : x ∈ r := by
        change r.mkQ x = 0 at hy
        exact (Submodule.Quotient.mk_eq_zero r).mp
          (by simpa only [Submodule.mkQ_apply] using hy)
      obtain ⟨w, hw⟩ := hrange x hx
      refine ⟨p.mkQ w, ?_⟩
      simp only [f, Submodule.mapQ_apply, g, Submodule.mapQ_apply]
      have hw' : q.mkQ (x - a * w) = 0 :=
        (Submodule.Quotient.mk_eq_zero q).mpr hw
      have hw'' : q.mkQ x = q.mkQ (a * w) := by
        exact sub_eq_zero.mp (by simpa only [map_sub] using hw')
      exact hw''.symm
    · rintro ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := p.mkQ_surjective x
      simp only [f, g, Submodule.mapQ_apply]
      change (Submodule.Quotient.mk (a * z) : R ⧸ r) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simpa [mul_comm] using r.mul_mem_left z ha
  constructor
  · intro P hP
    exact associatedPrimes.subset_of_injective hf_injective hP
  · intro P hP
    exact (associatedPrimes.subset_union_of_exact hf_injective hfg) hP

/-- The associated primes of `k[x,y]/(xy(x+y))`. -/
theorem associated_primes_plane_product_quotient (k : Type u) [Field k] :
    associatedPrimes (planePolynomialRing k) (planeProductQuotient k) =
      ({planeXPrimeIdeal k, planeYPrimeIdeal k, planeDiagonalPrimeIdeal k} :
        Set (Ideal (planePolynomialRing k))) := by
  have hx0 : planeX k ≠ 0 := by
    simp [planeX]
  have hy0 : planeY k ≠ 0 := by
    simp [planeY]
  have hdp : Prime (planeX k + planeY k) := by
    let e := MvPolynomial.finSuccEquiv k 1
    apply (MulEquiv.prime_iff e).mp
    have hp := Polynomial.prime_X_sub_C (R := MvPolynomial (Fin 1) k)
      (-(MvPolynomial.X (0 : Fin 1)))
    convert hp using 1
    simp [e, MvPolynomial.finSuccEquiv_apply, planeX, planeY, sub_eq_add_neg]
    rw [show (1 : Fin 2) = Fin.succ 0 by rfl]
    rfl
  have hd0 : planeX k + planeY k ≠ 0 := hdp.ne_zero
  have hxy0 : planeY k * (planeX k + planeY k) ≠ 0 := mul_ne_zero hy0 hd0
  have hprod := associated_primes_span_mul_subset_union
    (planeX k) (planeY k * (planeX k + planeY k)) hx0 hxy0
  have hyd := associated_primes_span_mul_subset_union
    (planeY k) (planeX k + planeY k) hy0 hd0
  have hleftx := associated_primes_span_mul_left_subset
    (planeX k) (planeY k * (planeX k + planeY k)) hxy0
  have hleftd := associated_primes_span_mul_left_subset
    (planeX k + planeY k) (planeX k * planeY k) (mul_ne_zero hx0 hy0)
  have hprod_eq : planeX k * (planeY k * (planeX k + planeY k)) =
      planeX k * planeY k * (planeX k + planeY k) := by ring
  rw [hprod_eq] at hprod hleftx
  have hleftd_eq : (planeX k + planeY k) * (planeX k * planeY k) =
      planeX k * planeY k * (planeX k + planeY k) := by ring
  rw [hleftd_eq] at hleftd
  have hx : (Ideal.span ({planeX k} : Set (planePolynomialRing k))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime
  have hy : (Ideal.span ({planeY k} : Set (planePolynomialRing k))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime
  have hd : (Ideal.span ({planeX k + planeY k} :
      Set (planePolynomialRing k))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hdp
  have ax := associated_primes_span_singleton_of_prime (planeX k) hx
  have ay := associated_primes_span_singleton_of_prime (planeY k) hy
  have ad := associated_primes_span_singleton_of_prime (planeX k + planeY k) hd
  have hprod' :
      associatedPrimes (planePolynomialRing k) (planeProductQuotient k) ⊆
        associatedPrimes (planePolynomialRing k)
            (planePolynomialRing k ⧸ Ideal.span ({planeX k} : Set _)) ∪
          associatedPrimes (planePolynomialRing k)
            (planePolynomialRing k ⧸
              Ideal.span ({planeY k * (planeX k + planeY k)} : Set _)) := by
    change associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸
            Ideal.span ({planeX k * planeY k * (planeX k + planeY k)} : Set _)) ⊆
      associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸ Ideal.span ({planeX k} : Set _)) ∪
        associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸
            Ideal.span ({planeY k * (planeX k + planeY k)} : Set _))
    exact hprod
  have hyd' :
      associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸
            Ideal.span ({planeY k * (planeX k + planeY k)} : Set _)) ⊆
        ({planeYPrimeIdeal k, planeDiagonalPrimeIdeal k} :
          Set (Ideal (planePolynomialRing k))) := by
    intro P hP
    rcases hyd hP with hP | hP
    · have hPY : P = planeYPrimeIdeal k := by
        rw [show associatedPrimes (planePolynomialRing k)
              (planePolynomialRing k ⧸ Ideal.span ({planeY k} : Set _)) =
              {planeYPrimeIdeal k} by simpa [planeYPrimeIdeal] using ay] at hP
        exact Set.mem_singleton_iff.mp hP
      exact Set.mem_insert_iff.mpr (Or.inl hPY)
    · have hPD : P = planeDiagonalPrimeIdeal k := by
        rw [show associatedPrimes (planePolynomialRing k)
              (planePolynomialRing k ⧸
                Ideal.span ({planeX k + planeY k} : Set _)) =
              {planeDiagonalPrimeIdeal k} by
                simpa [planeDiagonalPrimeIdeal] using ad] at hP
        exact Set.mem_singleton_iff.mp hP
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hPD))
  have hleftx' :
      associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸ Ideal.span ({planeX k} : Set _)) ⊆
        associatedPrimes (planePolynomialRing k) (planeProductQuotient k) := by
    change associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸
            Ideal.span ({planeX k} : Set _)) ⊆
      associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸
            Ideal.span ({planeX k * planeY k * (planeX k + planeY k)} : Set _))
    exact hleftx
  have hleftyprod :
      associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸ Ideal.span ({planeY k} : Set _)) ⊆
        associatedPrimes (planePolynomialRing k) (planeProductQuotient k) := by
    have h := associated_primes_span_mul_left_subset
      (planeY k) (planeX k * (planeX k + planeY k))
      (mul_ne_zero hx0 hd0)
    have heq : planeY k * (planeX k * (planeX k + planeY k)) =
        planeProductRelation k := by
      simp [planeProductRelation, mul_comm, mul_left_comm]
    rw [heq] at h
    change associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸ Ideal.span ({planeY k} : Set _)) ⊆
      associatedPrimes (planePolynomialRing k)
        (planePolynomialRing k ⧸
          Ideal.span ({planeProductRelation k} : Set _))
    exact h
  have hleftd' :
      associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸
            Ideal.span ({planeX k + planeY k} : Set _)) ⊆
        associatedPrimes (planePolynomialRing k) (planeProductQuotient k) := by
    change associatedPrimes (planePolynomialRing k)
          (planePolynomialRing k ⧸ Ideal.span ({planeX k + planeY k} : Set _)) ⊆
      associatedPrimes (planePolynomialRing k)
        (planePolynomialRing k ⧸
          Ideal.span ({planeProductRelation k} : Set _))
    exact hleftd
  apply Set.Subset.antisymm
  · intro P hP
    rcases hprod' hP with hP | hP
    · have hPX : P = planeXPrimeIdeal k := by
        rw [show associatedPrimes (planePolynomialRing k)
              (planePolynomialRing k ⧸ Ideal.span ({planeX k} : Set _)) =
              {planeXPrimeIdeal k} by simpa [planeXPrimeIdeal] using ax] at hP
        exact Set.mem_singleton_iff.mp hP
      exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mpr hPX))
    · exact Set.mem_insert_of_mem _ (hyd' hP)
  · intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl | rfl
    · apply hleftx'
      rw [show associatedPrimes (planePolynomialRing k)
            (planePolynomialRing k ⧸ Ideal.span ({planeX k} : Set _)) =
            {planeXPrimeIdeal k} by simpa [planeXPrimeIdeal] using ax]
      exact Set.mem_singleton _
    · apply hleftyprod
      rw [show associatedPrimes (planePolynomialRing k)
            (planePolynomialRing k ⧸ Ideal.span ({planeY k} : Set _)) =
            {planeYPrimeIdeal k} by simpa [planeYPrimeIdeal] using ay]
      exact Set.mem_singleton _
    · apply hleftd'
      rw [show associatedPrimes (planePolynomialRing k)
            (planePolynomialRing k ⧸
              Ideal.span ({planeX k + planeY k} : Set _)) =
            {planeDiagonalPrimeIdeal k} by
              simpa [planeDiagonalPrimeIdeal] using ad]
      exact Set.mem_singleton _

/-! ## `ℤ[x]/(300x+75)` -/

/-- The integer polynomial ring in the second computation. -/
abbrev integerPolynomialRing : Type := Polynomial ℤ

/-- The displayed relation `300x+75`. -/
def integerAssociatedRelation : integerPolynomialRing :=
  Polynomial.C (300 : ℤ) * Polynomial.X + Polynomial.C (75 : ℤ)

/-- The principal relation ideal `(300x+75)`. -/
def integerAssociatedIdeal : Ideal integerPolynomialRing :=
  Ideal.span ({integerAssociatedRelation} : Set integerPolynomialRing)

/-- The quotient module in the second computation. -/
abbrev integerAssociatedQuotient : Type :=
  integerPolynomialRing ⧸ integerAssociatedIdeal

/-- The three prime ideals generated by the irreducible factors of `300x+75`. -/
def integerPrimeThree : Ideal integerPolynomialRing :=
  Ideal.span ({Polynomial.C (3 : ℤ)} : Set integerPolynomialRing)

def integerPrimeFive : Ideal integerPolynomialRing :=
  Ideal.span ({Polynomial.C (5 : ℤ)} : Set integerPolynomialRing)

def integerPrimeLinear : Ideal integerPolynomialRing :=
  Ideal.span ({Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (1 : ℤ)} :
    Set integerPolynomialRing)

/-- The associated primes of `ℤ[x]/(300x+75)`. -/
theorem associated_primes_integer_quotient :
    associatedPrimes integerPolynomialRing integerAssociatedQuotient =
      ({integerPrimeThree, integerPrimeFive, integerPrimeLinear} :
        Set (Ideal integerPolynomialRing)) := by
  have h3p : Prime (Polynomial.C (3 : ℤ)) :=
    Polynomial.prime_C_iff.mpr Int.prime_three
  have h5p : Prime (Polynomial.C (5 : ℤ)) :=
    Polynomial.prime_C_iff.mpr (Int.prime_ofNat_iff.mpr Nat.prime_five)
  have hlinirr : Irreducible
      (Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (1 : ℤ)) :=
    Polynomial.irreducible_C_mul_X_add_C (by norm_num) isRelPrime_one_right
  have hlinp : Prime
      (Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (1 : ℤ)) :=
    irreducible_iff_prime.mp hlinirr
  let c3 : integerPolynomialRing := Polynomial.C (3 : ℤ)
  let c5 : integerPolynomialRing := Polynomial.C (5 : ℤ)
  let lin : integerPolynomialRing :=
    Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (1 : ℤ)
  have hc30 : c3 ≠ 0 := h3p.ne_zero
  have hc50 : c5 ≠ 0 := h5p.ne_zero
  have hlin0 : lin ≠ 0 := hlinp.ne_zero
  have hrel : c3 * (c5 * (c5 * lin)) = integerAssociatedRelation := by
    dsimp [c3, c5, lin, integerAssociatedRelation]
    norm_num
    ring
  have hrel5 : c5 * (c3 * (c5 * lin)) = integerAssociatedRelation := by
    dsimp [c3, c5, lin, integerAssociatedRelation]
    norm_num
    ring
  have hrelin : lin * (c3 * (c5 * c5)) = integerAssociatedRelation := by
    dsimp [c3, c5, lin, integerAssociatedRelation]
    norm_num
    ring
  have hprod := associated_primes_span_mul_subset_union
    c3 (c5 * (c5 * lin)) hc30 (mul_ne_zero hc50 (mul_ne_zero hc50 hlin0))
  have hmid := associated_primes_span_mul_subset_union
    c5 (c5 * lin) hc50 (mul_ne_zero hc50 hlin0)
  have hlast := associated_primes_span_mul_subset_union
    c5 lin hc50 hlin0
  have hleft3 := associated_primes_span_mul_left_subset
    c3 (c5 * (c5 * lin)) (mul_ne_zero hc50 (mul_ne_zero hc50 hlin0))
  have hleft5 := associated_primes_span_mul_left_subset
    c5 (c3 * (c5 * lin)) (mul_ne_zero hc30 (mul_ne_zero hc50 hlin0))
  have hleftlin := associated_primes_span_mul_left_subset
    lin (c3 * (c5 * c5)) (mul_ne_zero hc30 (mul_ne_zero hc50 hc50))
  rw [hrel] at hprod hleft3
  rw [hrel5] at hleft5
  rw [hrelin] at hleftlin
  have h3 : (Ideal.span ({c3} : Set integerPolynomialRing)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime h3p
  have h5 : (Ideal.span ({c5} : Set integerPolynomialRing)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime h5p
  have hlin : (Ideal.span ({lin} : Set integerPolynomialRing)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hlinp
  have a3 := associated_primes_span_singleton_of_prime c3 h3
  have a5 := associated_primes_span_singleton_of_prime c5 h5
  have alin := associated_primes_span_singleton_of_prime lin hlin
  have hlast' :
      associatedPrimes integerPolynomialRing
          (integerPolynomialRing ⧸ Ideal.span ({c5 * lin} : Set _)) ⊆
        ({integerPrimeFive, integerPrimeLinear} :
          Set (Ideal integerPolynomialRing)) := by
    intro P hP
    rcases hlast hP with hP | hP
    · have hP5 : P = integerPrimeFive := by
        rw [show associatedPrimes integerPolynomialRing
              (integerPolynomialRing ⧸ Ideal.span ({c5} : Set _)) =
              {integerPrimeFive} by simpa [integerPrimeFive, c5] using a5] at hP
        exact Set.mem_singleton_iff.mp hP
      exact Set.mem_insert_iff.mpr (Or.inl hP5)
    · have hPlin : P = integerPrimeLinear := by
        rw [show associatedPrimes integerPolynomialRing
              (integerPolynomialRing ⧸ Ideal.span ({lin} : Set _)) =
              {integerPrimeLinear} by simpa [integerPrimeLinear, lin] using alin] at hP
        exact Set.mem_singleton_iff.mp hP
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hPlin))
  have hmid' :
      associatedPrimes integerPolynomialRing
          (integerPolynomialRing ⧸ Ideal.span ({c5 * (c5 * lin)} : Set _)) ⊆
        ({integerPrimeFive, integerPrimeLinear} :
          Set (Ideal integerPolynomialRing)) := by
    intro P hP
    rcases hmid hP with hP | hP
    · have hP5 : P = integerPrimeFive := by
        rw [show associatedPrimes integerPolynomialRing
              (integerPolynomialRing ⧸ Ideal.span ({c5} : Set _)) =
              {integerPrimeFive} by simpa [integerPrimeFive, c5] using a5] at hP
        exact Set.mem_singleton_iff.mp hP
      exact Set.mem_insert_iff.mpr (Or.inl hP5)
    · exact hlast' hP
  have hprod' :
      associatedPrimes integerPolynomialRing integerAssociatedQuotient ⊆
        ({integerPrimeThree, integerPrimeFive, integerPrimeLinear} :
          Set (Ideal integerPolynomialRing)) := by
    intro P hP
    rcases hprod hP with hP | hP
    · have hP3 : P = integerPrimeThree := by
        rw [show associatedPrimes integerPolynomialRing
              (integerPolynomialRing ⧸ Ideal.span ({c3} : Set _)) =
              {integerPrimeThree} by simpa [integerPrimeThree, c3] using a3] at hP
        exact Set.mem_singleton_iff.mp hP
      exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mpr hP3))
    · exact Set.mem_insert_of_mem _ (hmid' hP)
  have hleft3' :
      associatedPrimes integerPolynomialRing
          (integerPolynomialRing ⧸ Ideal.span ({c3} : Set _)) ⊆
        associatedPrimes integerPolynomialRing integerAssociatedQuotient := by
    change associatedPrimes integerPolynomialRing
          (integerPolynomialRing ⧸ Ideal.span ({c3} : Set _)) ⊆
      associatedPrimes integerPolynomialRing
        (integerPolynomialRing ⧸ Ideal.span ({integerAssociatedRelation} : Set _))
    exact hleft3
  have hleft5' :
      associatedPrimes integerPolynomialRing
          (integerPolynomialRing ⧸ Ideal.span ({c5} : Set _)) ⊆
        associatedPrimes integerPolynomialRing integerAssociatedQuotient := by
    change associatedPrimes integerPolynomialRing
          (integerPolynomialRing ⧸ Ideal.span ({c5} : Set _)) ⊆
      associatedPrimes integerPolynomialRing
        (integerPolynomialRing ⧸ Ideal.span ({integerAssociatedRelation} : Set _))
    exact hleft5
  have hleftlin' :
      associatedPrimes integerPolynomialRing
          (integerPolynomialRing ⧸ Ideal.span ({lin} : Set _)) ⊆
        associatedPrimes integerPolynomialRing integerAssociatedQuotient := by
    change associatedPrimes integerPolynomialRing
          (integerPolynomialRing ⧸ Ideal.span ({lin} : Set _)) ⊆
      associatedPrimes integerPolynomialRing
        (integerPolynomialRing ⧸ Ideal.span ({integerAssociatedRelation} : Set _))
    exact hleftlin
  apply Set.Subset.antisymm
  · exact fun P hP => hprod' hP
  · intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl | rfl
    · apply hleft3'
      rw [show associatedPrimes integerPolynomialRing
            (integerPolynomialRing ⧸ Ideal.span ({c3} : Set _)) =
            {integerPrimeThree} by simpa [integerPrimeThree, c3] using a3]
      exact Set.mem_singleton _
    · apply hleft5'
      rw [show associatedPrimes integerPolynomialRing
            (integerPolynomialRing ⧸ Ideal.span ({c5} : Set _)) =
            {integerPrimeFive} by simpa [integerPrimeFive, c5] using a5]
      exact Set.mem_singleton _
    · apply hleftlin'
      rw [show associatedPrimes integerPolynomialRing
            (integerPolynomialRing ⧸ Ideal.span ({lin} : Set _)) =
            {integerPrimeLinear} by simpa [integerPrimeLinear, lin] using alin]
      exact Set.mem_singleton _

/-! ## `k[x,y,z]/(x³,x²y,xz)` -/

/-- The three-variable polynomial ring in the third computation. -/
abbrev spacePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 3) k

/-- The three coordinate variables. -/
def spaceX (k : Type u) [Field k] : spacePolynomialRing k :=
  MvPolynomial.X (0 : Fin 3)

def spaceY (k : Type u) [Field k] : spacePolynomialRing k :=
  MvPolynomial.X (1 : Fin 3)

def spaceZ (k : Type u) [Field k] : spacePolynomialRing k :=
  MvPolynomial.X (2 : Fin 3)

/-- The displayed monomial relation ideal `(x³,x²y,xz)`. -/
def spaceRelationIdeal (k : Type u) [Field k] : Ideal (spacePolynomialRing k) :=
  Ideal.span
    ({spaceX k ^ 3, spaceX k ^ 2 * spaceY k, spaceX k * spaceZ k} :
      Set (spacePolynomialRing k))

/-- The quotient module in the third computation. -/
abbrev spaceRelationQuotient (k : Type u) [Field k] :=
  spacePolynomialRing k ⧸ spaceRelationIdeal k

/-- The three associated primes of the monomial quotient. -/
def spaceXPrimeIdeal (k : Type u) [Field k] : Ideal (spacePolynomialRing k) :=
  Ideal.span ({spaceX k} : Set (spacePolynomialRing k))

def spaceXZPrimeIdeal (k : Type u) [Field k] : Ideal (spacePolynomialRing k) :=
  Ideal.span ({spaceX k, spaceZ k} : Set (spacePolynomialRing k))

def spaceMaximalIdeal (k : Type u) [Field k] : Ideal (spacePolynomialRing k) :=
  Ideal.span ({spaceX k, spaceY k, spaceZ k} : Set (spacePolynomialRing k))

/-- The associated primes of `k[x,y,z]/(x³,x²y,xz)`. -/
theorem associated_primes_space_relation_quotient (k : Type u) [Field k] :
    associatedPrimes (spacePolynomialRing k) (spaceRelationQuotient k) =
      ({spaceXPrimeIdeal k, spaceXZPrimeIdeal k, spaceMaximalIdeal k} :
        Set (Ideal (spacePolynomialRing k))) := by
  let R := spacePolynomialRing k
  let x : R := spaceX k
  let y : R := spaceY k
  let z : R := spaceZ k
  let e0 : Fin 3 →₀ ℕ := Finsupp.single 0 1
  let e1 : Fin 3 →₀ ℕ := Finsupp.single 1 1
  let e2 : Fin 3 →₀ ℕ := Finsupp.single 2 1
  let sK : Set (Fin 3 →₀ ℕ) := {2 • e0, e0 + e1, e2}
  let sM : Set (Fin 3 →₀ ℕ) := {e0, e1, e2}
  let K : Ideal R := Ideal.span ({x ^ 2, x * y, z} : Set R)
  let M : Ideal R := Ideal.span ({x, y, z} : Set R)
  have hx : x = MvPolynomial.monomial e0 (1 : k) := by
    change MvPolynomial.X (0 : Fin 3) = _
    simp [MvPolynomial.X, e0]
  have hy : y = MvPolynomial.monomial e1 (1 : k) := by
    change MvPolynomial.X (1 : Fin 3) = _
    simp [MvPolynomial.X, e1]
  have hx2 : x ^ 2 = MvPolynomial.monomial (2 • e0) (1 : k) := by
    change (MvPolynomial.X (0 : Fin 3)) ^ 2 = _
    rw [MvPolynomial.X_pow_eq_monomial]
    congr 1
    simp [e0, Finsupp.smul_single]
  have hxy : x * y = MvPolynomial.monomial (e0 + e1) (1 : k) := by
    rw [hx, hy, MvPolynomial.monomial_mul]
    simp
  have hz : z = MvPolynomial.monomial e2 (1 : k) := by
    change MvPolynomial.X (2 : Fin 3) = _
    simp [MvPolynomial.X, e2]
  have hKmon :
      K = Ideal.span ((fun d => MvPolynomial.monomial d (1 : k)) '' sK) := by
    apply congrArg Ideal.span
    ext p
    constructor
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · refine ⟨2 • e0, by simp [sK], ?_⟩
        exact hx2.symm
      · refine ⟨e0 + e1, by simp [sK], ?_⟩
        exact hxy.symm
      · refine ⟨e2, by simp [sK], ?_⟩
        exact hz.symm
    · intro hp
      rcases hp with ⟨d, hd, rfl⟩
      simp only [sK, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl | rfl
      · exact Set.mem_insert_iff.mpr (Or.inl hx2.symm)
      · exact Set.mem_insert_iff.mpr (Or.inr (Or.inl hxy.symm))
      · exact Set.mem_insert_iff.mpr (Or.inr (Or.inr hz.symm))
  have hMmon :
      M = Ideal.span ((fun d => MvPolynomial.monomial d (1 : k)) '' sM) := by
    apply congrArg Ideal.span
    ext p
    constructor
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · refine ⟨e0, by simp [sM], ?_⟩
        exact hx.symm
      · refine ⟨e1, by simp [sM], ?_⟩
        exact hy.symm
      · refine ⟨e2, by simp [sM], ?_⟩
        exact hz.symm
    · intro hp
      rcases hp with ⟨d, hd, rfl⟩
      simp only [sM, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl | rfl
      · exact Set.mem_insert_iff.mpr (Or.inl hx.symm)
      · exact Set.mem_insert_iff.mpr (Or.inr (Or.inl hy.symm))
      · exact Set.mem_insert_iff.mpr (Or.inr (Or.inr hz.symm))
  have hs0 (m : Fin 3 →₀ ℕ) (h : (2 • e0) ≤ m + e0) : e0 ≤ m := by
    intro i
    fin_cases i
    · have hi := h (0 : Fin 3)
      simp [e0] at hi ⊢
      omega
    · simp [e0]
    · simp [e0]
  have hs1 (m : Fin 3 →₀ ℕ) (h : e0 + e1 ≤ m + e0) : e1 ≤ m := by
    intro i
    fin_cases i
    · simp [e0, e1]
    · have hi := h (1 : Fin 3)
      simp [e0, e1] at hi ⊢
      exact hi
    · simp [e0, e1]
  have hs2 (m : Fin 3 →₀ ℕ) (h : e2 ≤ m + e0) : e2 ≤ m := by
    intro i
    fin_cases i
    · simp [e0, e2]
    · simp [e0, e2]
    · have hi := h (2 : Fin 3)
      simp [e0, e2] at hi ⊢
      exact hi
  have hb0 (m : Fin 3 →₀ ℕ) (h : e0 ≤ m) : (2 • e0) ≤ m + e0 := by
    intro i
    fin_cases i
    · have hi := h (0 : Fin 3)
      simp [e0] at hi ⊢
      omega
    · simp [e0]
    · simp [e0]
  have hb1 (m : Fin 3 →₀ ℕ) (h : e1 ≤ m) : e0 + e1 ≤ m + e0 := by
    intro i
    fin_cases i
    · simp [e0, e1]
    · have hi := h (1 : Fin 3)
      simp [e0, e1] at hi ⊢
      exact hi
    · simp [e0, e1]
  have hb2 (m : Fin 3 →₀ ℕ) (h : e2 ≤ m) : e2 ≤ m + e0 := by
    intro i
    fin_cases i
    · simp [e0, e2]
    · simp [e0, e2]
    · have hi := h (2 : Fin 3)
      simp [e0, e2] at hi ⊢
      exact hi
  have hcomapK : Submodule.comap (LinearMap.lsmul R R x) (K : Submodule R R) = M := by
    ext f
    constructor
    · intro hf
      change x * f ∈ K at hf
      rw [hKmon, MvPolynomial.mem_ideal_span_monomial_image] at hf
      rw [hMmon, MvPolynomial.mem_ideal_span_monomial_image]
      intro m hm
      have hxm : m + e0 ∈ (x * f).support := by
        change m + e0 ∈ (MvPolynomial.X (0 : Fin 3) * f).support
        rw [MvPolynomial.support_X_mul]
        refine Finset.mem_map.mpr ⟨m, hm, ?_⟩
        simp [addLeftEmbedding_apply, e0, add_comm]
      obtain ⟨d, hd, hde⟩ := hf (m + e0) hxm
      rcases (show d = 2 • e0 ∨ d = e0 + e1 ∨ d = e2 by
        simpa [sK] using hd) with rfl | rfl | rfl
      · exact ⟨e0, by simp [sM], hs0 m hde⟩
      · exact ⟨e1, by simp [sM], hs1 m hde⟩
      · exact ⟨e2, by simp [sM], hs2 m hde⟩
    · intro hf
      change f ∈ M at hf
      rw [hMmon, MvPolynomial.mem_ideal_span_monomial_image] at hf
      change x * f ∈ K
      rw [hKmon, MvPolynomial.mem_ideal_span_monomial_image]
      intro n hn
      rw [show x = MvPolynomial.X (0 : Fin 3) by rfl,
        MvPolynomial.support_X_mul] at hn
      obtain ⟨m, hm, hmn⟩ := Finset.mem_map.mp hn
      obtain ⟨d, hd, hde⟩ := hf m hm
      rcases (show d = e0 ∨ d = e1 ∨ d = e2 by
        simpa [sM] using hd) with rfl | rfl | rfl
      · refine ⟨2 • e0, by simp [sK], ?_⟩
        rw [← hmn]
        simpa [addLeftEmbedding_apply, e0, add_comm] using hb0 m hde
      · refine ⟨e0 + e1, by simp [sK], ?_⟩
        rw [← hmn]
        simpa [addLeftEmbedding_apply, e0, add_comm] using hb1 m hde
      · refine ⟨e2, by simp [sK], ?_⟩
        rw [← hmn]
        simpa [addLeftEmbedding_apply, e0, add_comm] using hb2 m hde
  let J : Ideal R := spaceRelationIdeal k
  let sJ : Set (Fin 3 →₀ ℕ) := {3 • e0, 2 • e0 + e1, e0 + e2}
  have hx3 : x ^ 3 = MvPolynomial.monomial (3 • e0) (1 : k) := by
    change (MvPolynomial.X (0 : Fin 3)) ^ 3 = _
    rw [MvPolynomial.X_pow_eq_monomial]
    congr 1
    simp [e0, Finsupp.smul_single]
  have hx2y : x ^ 2 * y =
      MvPolynomial.monomial (2 • e0 + e1) (1 : k) := by
    rw [hx2, hy, MvPolynomial.monomial_mul]
    simp [add_assoc]
  have hxz : x * z = MvPolynomial.monomial (e0 + e2) (1 : k) := by
    rw [hx, hz, MvPolynomial.monomial_mul]
    simp
  have hJmon : J = Ideal.span ((fun d => MvPolynomial.monomial d (1 : k)) '' sJ) := by
    apply congrArg Ideal.span
    ext p
    constructor
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨3 • e0, by simp [sJ], hx3.symm⟩
      · exact ⟨2 • e0 + e1, by simp [sJ], hx2y.symm⟩
      · exact ⟨e0 + e2, by simp [sJ], hxz.symm⟩
    · rintro ⟨d, hd, rfl⟩
      simp only [sJ, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl | rfl
      · exact Set.mem_insert_iff.mpr (Or.inl hx3.symm)
      · exact Set.mem_insert_iff.mpr (Or.inr (Or.inl hx2y.symm))
      · exact Set.mem_insert_iff.mpr (Or.inr (Or.inr hxz.symm))
  have hJs0 (m : Fin 3 →₀ ℕ) (h : (3 • e0) ≤ m + e0) :
      (2 • e0) ≤ m := by
    intro i
    fin_cases i
    · have hi := h (0 : Fin 3)
      simp [e0] at hi ⊢
      omega
    · simp [e0]
    · simp [e0]
  have hJs1 (m : Fin 3 →₀ ℕ) (h : 2 • e0 + e1 ≤ m + e0) :
      e0 + e1 ≤ m := by
    intro i
    fin_cases i
    · have hi := h (0 : Fin 3)
      simp [e0, e1] at hi ⊢
      omega
    · have hi := h (1 : Fin 3)
      simp [e0, e1] at hi ⊢
      exact hi
    · simp [e0, e1]
  have hJs2 (m : Fin 3 →₀ ℕ) (h : e0 + e2 ≤ m + e0) : e2 ≤ m := by
    intro i
    fin_cases i
    · simp [e0, e2]
    · simp [e0, e2]
    · have hi := h (2 : Fin 3)
      simp [e0, e2] at hi ⊢
      exact hi
  have hJb0 (m : Fin 3 →₀ ℕ) (h : (2 • e0) ≤ m) :
      (3 • e0) ≤ m + e0 := by
    intro i
    fin_cases i
    · have hi := h (0 : Fin 3)
      simp [e0] at hi ⊢
      omega
    · simp [e0]
    · simp [e0]
  have hJb1 (m : Fin 3 →₀ ℕ) (h : e0 + e1 ≤ m) :
      2 • e0 + e1 ≤ m + e0 := by
    intro i
    fin_cases i
    · have hi := h (0 : Fin 3)
      simp [e0, e1] at hi ⊢
      omega
    · have hi := h (1 : Fin 3)
      simp [e0, e1] at hi ⊢
      exact hi
    · simp [e0, e1]
  have hJb2 (m : Fin 3 →₀ ℕ) (h : e2 ≤ m) :
      e0 + e2 ≤ m + e0 := by
    intro i
    fin_cases i
    · simp [e0, e2]
    · simp [e0, e2]
    · have hi := h (2 : Fin 3)
      simp [e0, e2] at hi ⊢
      exact hi
  have hcomapJ : Submodule.comap (LinearMap.lsmul R R x) (J : Submodule R R) = K := by
    ext f
    constructor
    · intro hf
      change x * f ∈ J at hf
      rw [hJmon, MvPolynomial.mem_ideal_span_monomial_image] at hf
      rw [hKmon, MvPolynomial.mem_ideal_span_monomial_image]
      intro m hm
      have hxm : m + e0 ∈ (x * f).support := by
        change m + e0 ∈ (MvPolynomial.X (0 : Fin 3) * f).support
        rw [MvPolynomial.support_X_mul]
        refine Finset.mem_map.mpr ⟨m, hm, ?_⟩
        simp [addLeftEmbedding_apply, e0, add_comm]
      obtain ⟨d, hd, hde⟩ := hf (m + e0) hxm
      rcases (show d = 3 • e0 ∨ d = 2 • e0 + e1 ∨ d = e0 + e2 by
        simpa [sJ] using hd) with rfl | rfl | rfl
      · exact ⟨2 • e0, by simp [sK], hJs0 m hde⟩
      · exact ⟨e0 + e1, by simp [sK], hJs1 m hde⟩
      · exact ⟨e2, by simp [sK], hJs2 m hde⟩
    · intro hf
      change f ∈ K at hf
      rw [hKmon, MvPolynomial.mem_ideal_span_monomial_image] at hf
      change x * f ∈ J
      rw [hJmon, MvPolynomial.mem_ideal_span_monomial_image]
      intro n hn
      rw [show x = MvPolynomial.X (0 : Fin 3) by rfl,
        MvPolynomial.support_X_mul] at hn
      obtain ⟨m, hm, hmn⟩ := Finset.mem_map.mp hn
      obtain ⟨d, hd, hde⟩ := hf m hm
      rcases (show d = 2 • e0 ∨ d = e0 + e1 ∨ d = e2 by
        simpa [sK] using hd) with rfl | rfl | rfl
      · refine ⟨3 • e0, by simp [sJ], ?_⟩
        rw [← hmn]
        simpa [addLeftEmbedding_apply, e0, add_comm] using hJb0 m hde
      · refine ⟨2 • e0 + e1, by simp [sJ], ?_⟩
        rw [← hmn]
        simpa [addLeftEmbedding_apply, e0, add_comm] using hJb1 m hde
      · refine ⟨e0 + e2, by simp [sJ], ?_⟩
        rw [← hmn]
        simpa [addLeftEmbedding_apply, e0, add_comm] using hJb2 m hde
  let Xideal : Ideal R := Ideal.span ({x} : Set R)
  let P : Ideal R := Ideal.span ({x, z} : Set R)
  have hxX : x ∈ Xideal := Ideal.subset_span (Set.mem_singleton x)
  have hXprime : Xideal.IsPrime := by
    exact Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime
  have hJ_le_X : J ≤ Xideal := by
    change Ideal.span ({x ^ 3, x ^ 2 * y, x * z} : Set R) ≤ Xideal
    rw [Ideal.span_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · rw [show x ^ 3 = x ^ 2 * x by ring]
      exact Xideal.mul_mem_left (x ^ 2) hxX
    · rw [show x ^ 2 * y = (x * y) * x by ring]
      exact Xideal.mul_mem_left (x * y) hxX
    · rw [show x * z = z * x by ring]
      exact Xideal.mul_mem_left z hxX
  have hXrange : ∀ t, t ∈ Xideal → ∃ w, t - x * w ∈ J := by
    intro t ht
    change t ∈ Ideal.span ({x} : Set R) at ht
    rcases Ideal.mem_span_singleton.mp ht with ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    simp [mul_comm]
  have hxP : x ∈ P := Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inl rfl))
  have hzP : z ∈ P := Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
  have hK_le_P : K ≤ P := by
    change Ideal.span ({x ^ 2, x * y, z} : Set R) ≤ P
    rw [Ideal.span_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · rw [show x ^ 2 = x * x by ring]
      exact P.mul_mem_left x hxP
    · rw [show x * y = y * x by ring]
      exact P.mul_mem_left y hxP
    · exact hzP
  have hPrange : ∀ t, t ∈ P → ∃ w, t - x * w ∈ K := by
    intro t ht
    change t ∈ Ideal.span ({x, z} : Set R) at ht
    rcases Ideal.mem_span_pair.mp ht with ⟨a, b, hab⟩
    refine ⟨a, ?_⟩
    rw [← hab]
    rw [show a * x + b * z - x * a = b * z by ring]
    exact K.mul_mem_left b
      (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr (Or.inr rfl))))
  have hseqJ :
      associatedPrimes R (R ⧸ K) ⊆ associatedPrimes R (R ⧸ J) ∧
        associatedPrimes R (R ⧸ J) ⊆
          associatedPrimes R (R ⧸ K) ∪ associatedPrimes R (R ⧸ Xideal) :=
    associated_primes_quotient_mul_subset x K J Xideal
      (by rw [hcomapJ]) hcomapJ hJ_le_X hxX hXrange
  have hseqK :
      associatedPrimes R (R ⧸ M) ⊆ associatedPrimes R (R ⧸ K) ∧
        associatedPrimes R (R ⧸ K) ⊆
          associatedPrimes R (R ⧸ M) ∪ associatedPrimes R (R ⧸ P) :=
    associated_primes_quotient_mul_subset x M K P
      (by rw [hcomapK]) hcomapK hK_le_P hxP hPrange
  have hMvars : M = Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 3))) := by
    apply congrArg Ideal.span
    ext p
    constructor
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, Set.mem_univ _, rfl⟩
      · exact ⟨1, Set.mem_univ _, rfl⟩
      · exact ⟨2, Set.mem_univ _, rfl⟩
    · rintro ⟨i, -, rfl⟩
      fin_cases i
      · exact Set.mem_insert_iff.mpr (Or.inl rfl)
      · exact Set.mem_insert_iff.mpr (Or.inr (Or.inl rfl))
      · change spaceZ k ∈ {spaceX k, spaceY k, spaceZ k}
        simp
  let φ : R →+* k := MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
  have hMker : RingHom.ker φ = M := by
    ext p
    rw [hMvars, MvPolynomial.mem_ideal_span_X_image]
    constructor
    · intro hp
      have hp0 : p.coeff 0 = 0 := by
        have hp' : φ p = 0 := hp
        rw [show φ p = MvPolynomial.constantCoeff p by
          simp [φ], MvPolynomial.constantCoeff_eq] at hp'
        exact hp'
      intro m hm
      by_contra hno
      have hmzero : m = 0 := by
        ext i
        by_contra hi
        apply hno
        exact ⟨i, Set.mem_univ _, hi⟩
      subst m
      exact (MvPolynomial.mem_support_iff.mp hm) hp0
    · intro hp
      have hp0 : p.coeff 0 = 0 := by
        by_contra hne
        have hzero : (0 : Fin 3 →₀ ℕ) ∈ p.support :=
          MvPolynomial.mem_support_iff.mpr hne
        obtain ⟨i, hi, hmi⟩ := hp 0 hzero
        simp at hmi
      have hp' : MvPolynomial.constantCoeff p = 0 := by
        simpa only [MvPolynomial.constantCoeff_eq] using hp0
      simpa [φ] using hp'
  have hMprime : M.IsPrime := by
    rw [← hMker]
    exact RingHom.ker_isPrime φ
  let sP : Set (Fin 3 →₀ ℕ) := {e0, e2}
  have hPmon : P = Ideal.span ((fun d => MvPolynomial.monomial d (1 : k)) '' sP) := by
    apply congrArg Ideal.span
    ext p
    constructor
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact ⟨e0, by simp [sP], hx.symm⟩
      · exact ⟨e2, by simp [sP], hz.symm⟩
    · rintro ⟨d, hd, rfl⟩
      simp only [sP, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl
      · exact Set.mem_insert_iff.mpr (Or.inl hx.symm)
      · exact Set.mem_insert_iff.mpr (Or.inr hz.symm)
  let f : Fin 1 → Fin 3 := fun _ => 1
  have hf : Function.Injective f := by
    intro (a : Fin 1) (b : Fin 1) _
    exact Subsingleton.elim a b
  have h0not : (0 : Fin 3) ∉ Set.range f := by
    rintro ⟨i, hi⟩
    simpa [f] using hi
  have h2not : (2 : Fin 3) ∉ Set.range f := by
    rintro ⟨i, h⟩
    simpa [f] using h
  let ψ : R →+* MvPolynomial (Fin 1) k :=
    (MvPolynomial.killCompl hf).toRingHom
  have hψ0 : ψ x = 0 := by
    change MvPolynomial.killCompl hf (MvPolynomial.X (0 : Fin 3)) = 0
    simpa [MvPolynomial.X] using
      (MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range hf (1 : k)
        (by simp) h0not)
  have hψ2 : ψ z = 0 := by
    change MvPolynomial.killCompl hf (MvPolynomial.X (2 : Fin 3)) = 0
    simpa [MvPolynomial.X] using
      (MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range hf (1 : k)
        (by simp) h2not)
  have hPker : RingHom.ker ψ = P := by
    apply le_antisymm
    · intro p hp
      rw [hPmon, MvPolynomial.mem_ideal_span_monomial_image]
      intro m hm
      by_contra hnone
      have hsub : (m.support : Set (Fin 3)) ⊆ Set.range f := by
        intro i hi
        fin_cases i
        · exfalso
          apply hnone
          refine ⟨e0, by simp [sP], ?_⟩
          intro j
          fin_cases j
          · have hi' := Finsupp.mem_support_iff.mp hi
            simp [e0] at hi' ⊢
            omega
          · simp [e0]
          · simp [e0]
        · exact ⟨0, by simp [f]⟩
        · exfalso
          apply hnone
          refine ⟨e2, by simp [sP], ?_⟩
          intro j
          fin_cases j
          · simp [e2]
          · simp [e2]
          · have hi' := Finsupp.mem_support_iff.mp hi
            simp [e2] at hi' ⊢
            omega
      let s := m.comapDomain f hf.injOn
      have hmap : s.mapDomain f = m :=
        m.mapDomain_comapDomain f hf hsub
      have hcoeff : p.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
      have hp0 : (MvPolynomial.killCompl hf p).coeff s = 0 := by
        change (MvPolynomial.killCompl hf p).coeff s = 0
        exact congrArg (fun q : MvPolynomial (Fin 1) k => q.coeff s) hp
      rw [MvPolynomial.coeff_killCompl] at hp0
      rw [hmap] at hp0
      exact hcoeff hp0
    · rw [Ideal.span_le]
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hψ0
      · exact hψ2
  have hPprime : P.IsPrime := by
    rw [← hPker]
    exact RingHom.ker_isPrime ψ
  have hXmon : Xideal =
      Ideal.span ((fun d => MvPolynomial.monomial d (1 : k)) '' ({e0} : Set _)) := by
    apply congrArg Ideal.span
    ext p
    constructor
    · intro hp
      have hp' : p = x := Set.mem_singleton_iff.mp hp
      subst p
      exact ⟨e0, by simp, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      have hd' : d = e0 := by simpa using hd
      subst d
      exact Set.mem_singleton_iff.mpr hx.symm
  have hcolon (w : R) :
      (⊥ : Submodule R (R ⧸ J)).colon {J.mkQ w} =
        J.colon ({w} : Set R) := by
    ext r
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
    change (Submodule.Quotient.mk (r * w) : R ⧸ J) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
  have hmulZ (q : R) :
      MvPolynomial.support (q * z) = q.support.map (addRightEmbedding e2) := by
    change MvPolynomial.support (q * MvPolynomial.X (2 : Fin 3)) = _
    rw [MvPolynomial.support_mul_X]
  have hmulXY (q : R) :
      MvPolynomial.support (q * (x * y)) =
        (q.support.map (addRightEmbedding e0)).map (addRightEmbedding e1) := by
    change MvPolynomial.support
      (q * (MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (1 : Fin 3))) = _
    rw [← mul_assoc, MvPolynomial.support_mul_X, MvPolynomial.support_mul_X]
  have hmulX2 (q : R) :
      MvPolynomial.support (q * x ^ 2) =
        (q.support.map (addRightEmbedding e0)).map (addRightEmbedding e0) := by
    change MvPolynomial.support (q * ((MvPolynomial.X (0 : Fin 3)) ^ 2)) = _
    rw [pow_two, ← mul_assoc, MvPolynomial.support_mul_X,
      MvPolynomial.support_mul_X]
  have hcolonX : J.colon ({z} : Set R) = Xideal := by
    ext q
    simp only [Submodule.mem_colon_singleton, smul_eq_mul]
    rw [hJmon, MvPolynomial.mem_ideal_span_monomial_image,
      hXmon, MvPolynomial.mem_ideal_span_monomial_image]
    constructor
    · intro hq m hm
      have hs : (addRightEmbedding e2) m ∈ (q * z).support := by
        rw [hmulZ]
        exact Finset.mem_map.mpr ⟨m, hm, rfl⟩
      obtain ⟨d, hd, hde⟩ := hq (addRightEmbedding e2 m) hs
      have hde' : d ≤ m + e2 := by
        simpa [addRightEmbedding_apply, e2, add_comm] using hde
      rcases (show d = 3 • e0 ∨ d = 2 • e0 + e1 ∨ d = e0 + e2 by
        simpa [sJ] using hd) with rfl | rfl | rfl
      · refine ⟨e0, by simp, ?_⟩
        intro i
        fin_cases i
        · have hi := hde' (0 : Fin 3)
          simp [e0, e2] at hi ⊢
          omega
        · simp [e0]
        · simp [e0]
      · refine ⟨e0, by simp, ?_⟩
        intro i
        fin_cases i
        · have hi := hde' (0 : Fin 3)
          simp [e0, e1, e2] at hi ⊢
          omega
        · simp [e0]
        · simp [e0]
      · refine ⟨e0, by simp, ?_⟩
        intro i
        fin_cases i
        · have hi := hde' (0 : Fin 3)
          simp [e0, e2] at hi ⊢
          exact hi
        · simp [e0]
        · simp [e0]
    · intro hq n hn
      rw [hmulZ] at hn
      obtain ⟨m, hm, hmn⟩ := Finset.mem_map.mp hn
      obtain ⟨d, hd, hde⟩ := hq m hm
      have hd' : d = e0 := by simpa using hd
      subst d
      have hde' : e0 ≤ m := hde
      refine ⟨e0 + e2, by simp [sJ], ?_⟩
      rw [← hmn]
      intro i
      fin_cases i
      · have hi := hde' (0 : Fin 3)
        simp [e0, e2, addRightEmbedding_apply, add_comm] at hi ⊢
        omega
      · simp [e0, e2, addRightEmbedding_apply]
      · have hi := hde' (2 : Fin 3)
        simp [e0, e2, addRightEmbedding_apply] at hi ⊢
  have hcolonP : J.colon ({x * y} : Set R) = P := by
      ext q
      simp only [Submodule.mem_colon_singleton, smul_eq_mul]
      rw [hJmon, MvPolynomial.mem_ideal_span_monomial_image,
        hPmon, MvPolynomial.mem_ideal_span_monomial_image]
      constructor
      · intro hq m hm
        have hs : (addRightEmbedding e1) (addRightEmbedding e0 m) ∈
            (q * (x * y)).support := by
          rw [hmulXY]
          exact Finset.mem_map.mpr ⟨addRightEmbedding e0 m,
            Finset.mem_map.mpr ⟨m, hm, rfl⟩, rfl⟩
        obtain ⟨d, hd, hde⟩ := hq
          ((addRightEmbedding e1) (addRightEmbedding e0 m)) hs
        have hde' : d ≤ m + e0 + e1 := by
          simpa [addRightEmbedding_apply, e0, e1, add_comm, add_assoc] using hde
        rcases (show d = 3 • e0 ∨ d = 2 • e0 + e1 ∨ d = e0 + e2 by
          simpa [sJ] using hd) with rfl | rfl | rfl
        · refine ⟨e0, by simp [sP], ?_⟩
          intro i
          fin_cases i
          · have hi := hde' (0 : Fin 3)
            simp [e0, e1] at hi ⊢
            omega
          · simp [e0]
          · simp [e0]
        · refine ⟨e0, by simp [sP], ?_⟩
          intro i
          fin_cases i
          · have hi := hde' (0 : Fin 3)
            simp [e0, e1] at hi ⊢
            omega
          · simp [e0, e1]
          · simp [e0]
        · refine ⟨e2, by simp [sP], ?_⟩
          intro i
          fin_cases i
          · simp [e2]
          · simp [e2]
          · have hi := hde' (2 : Fin 3)
            simp [e0, e1, e2] at hi ⊢
            exact hi
      · intro hq n hn
        rw [hmulXY] at hn
        obtain ⟨m, hm, hmn⟩ := Finset.mem_map.mp hn
        obtain ⟨n0, hn0, hmn0⟩ := Finset.mem_map.mp hm
        obtain ⟨d, hd, hde⟩ := hq n0 hn0
        rcases (show d = e0 ∨ d = e2 by simpa [sP] using hd) with rfl | rfl
        · refine ⟨2 • e0 + e1, by simp [sJ], ?_⟩
          rw [← hmn, ← hmn0]
          intro i
          fin_cases i
          · have hi := hde (0 : Fin 3)
            simp [e0, e1, addRightEmbedding_apply, add_comm, add_assoc] at hi ⊢
            omega
          · simp [e0, e1, addRightEmbedding_apply]
          · simp [e0, e1, addRightEmbedding_apply]
        · refine ⟨e0 + e2, by simp [sJ], ?_⟩
          rw [← hmn, ← hmn0]
          intro i
          fin_cases i
          · simp [e0, e2, addRightEmbedding_apply]
            omega
          · simp [e0, e2, addRightEmbedding_apply]
          · have hi := hde (2 : Fin 3)
            simp [e0, e2, addRightEmbedding_apply, add_comm, add_assoc] at hi ⊢
            omega

  have hcolonM : J.colon ({x ^ 2} : Set R) = M := by
      ext q
      simp only [Submodule.mem_colon_singleton, smul_eq_mul]
      rw [hJmon, MvPolynomial.mem_ideal_span_monomial_image,
        hMmon, MvPolynomial.mem_ideal_span_monomial_image]
      constructor
      · intro hq m hm
        have hs : (addRightEmbedding e0) (addRightEmbedding e0 m) ∈
            (q * x ^ 2).support := by
          rw [hmulX2]
          exact Finset.mem_map.mpr ⟨addRightEmbedding e0 m,
            Finset.mem_map.mpr ⟨m, hm, rfl⟩, rfl⟩
        obtain ⟨d, hd, hde⟩ := hq
          ((addRightEmbedding e0) (addRightEmbedding e0 m)) hs
        have hde' : d ≤ m + e0 + e0 := by
          simpa [addRightEmbedding_apply, e0, add_comm, add_assoc] using hde
        rcases (show d = 3 • e0 ∨ d = 2 • e0 + e1 ∨ d = e0 + e2 by
          simpa [sJ] using hd) with rfl | rfl | rfl
        · refine ⟨e0, by simp [sM], ?_⟩
          intro i
          fin_cases i
          · have hi := hde' (0 : Fin 3)
            simp [e0] at hi ⊢
            omega
          · simp [e0]
          · simp [e0]
        · refine ⟨e1, by simp [sM], ?_⟩
          intro i
          fin_cases i
          · simp [e1]
          · have hi := hde' (1 : Fin 3)
            simp [e0, e1] at hi ⊢
            exact hi
          · simp [e1]
        · refine ⟨e2, by simp [sM], ?_⟩
          intro i
          fin_cases i
          · simp [e2]
          · simp [e2]
          · have hi := hde' (2 : Fin 3)
            simp [e0, e2] at hi ⊢
            exact hi
      · intro hq n hn
        rw [hmulX2] at hn
        obtain ⟨m, hm, hmn⟩ := Finset.mem_map.mp hn
        obtain ⟨n0, hn0, hmn0⟩ := Finset.mem_map.mp hm
        obtain ⟨d, hd, hde⟩ := hq n0 hn0
        rcases (show d = e0 ∨ d = e1 ∨ d = e2 by simpa [sM] using hd) with
          rfl | rfl | rfl
        · refine ⟨3 • e0, by simp [sJ], ?_⟩
          rw [← hmn, ← hmn0]
          intro i
          fin_cases i
          · have hi := hde (0 : Fin 3)
            simp [e0, addRightEmbedding_apply, add_comm, add_assoc] at hi ⊢
            omega
          · simp [e0, addRightEmbedding_apply]
          · simp [e0, addRightEmbedding_apply]
        · refine ⟨2 • e0 + e1, by simp [sJ], ?_⟩
          rw [← hmn, ← hmn0]
          intro i
          fin_cases i
          · simp [e0, e1, addRightEmbedding_apply]
          · have hi := hde (1 : Fin 3)
            simp [e0, e1, addRightEmbedding_apply, add_comm, add_assoc] at hi ⊢
            exact hi
          · simp [e0, e1, addRightEmbedding_apply]
        · refine ⟨e0 + e2, by simp [sJ], ?_⟩
          rw [← hmn, ← hmn0]
          intro i
          fin_cases i
          · simp [e0, e2, addRightEmbedding_apply]
          · simp [e0, e2, addRightEmbedding_apply]
          · have hi := hde (2 : Fin 3)
            simp [e0, e2, addRightEmbedding_apply, add_comm, add_assoc] at hi ⊢
            exact hi
  have hAX : Xideal ∈ associatedPrimes R (R ⧸ J) := by
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
    refine ⟨hXprime, ?_⟩
    refine ⟨J.mkQ z, ?_⟩
    rw [hcolon z, hcolonX]
  have hAP : P ∈ associatedPrimes R (R ⧸ J) := by
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
    refine ⟨hPprime, ?_⟩
    refine ⟨J.mkQ (x * y), ?_⟩
    rw [hcolon (x * y), hcolonP]
  have hAM : M ∈ associatedPrimes R (R ⧸ J) := by
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
    refine ⟨hMprime, ?_⟩
    refine ⟨J.mkQ (x ^ 2), ?_⟩
    rw [hcolon (x ^ 2), hcolonM]
  have aX := associated_primes_quotient_of_prime Xideal hXprime
  have aP := associated_primes_quotient_of_prime P hPprime
  have aM := associated_primes_quotient_of_prime M hMprime
  have hupper : associatedPrimes R (R ⧸ J) ⊆
      ({Xideal, P, M} : Set (Ideal R)) := by
    intro Q hQ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hseqJ.2 hQ with hK | hX
    · rcases hseqK.2 hK with hM | hP
      · rw [aM] at hM
        exact Or.inr (Or.inr (Set.mem_singleton_iff.mp hM))
      · rw [aP] at hP
        exact Or.inr (Or.inl (Set.mem_singleton_iff.mp hP))
    · rw [aX] at hX
      exact Or.inl (Set.mem_singleton_iff.mp hX)
  have hlower : ({Xideal, P, M} : Set (Ideal R)) ⊆
      associatedPrimes R (R ⧸ J) := by
    intro Q hQ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
    rcases hQ with rfl | rfl | rfl
    · exact hAX
    · exact hAP
    · exact hAM
  have htarget : associatedPrimes R (R ⧸ J) =
      ({Xideal, P, M} : Set (Ideal R)) :=
    Set.Subset.antisymm hupper hlower
  change associatedPrimes R (R ⧸ J) =
    ({Xideal, P, M} : Set (Ideal R))
  exact htarget

end Formalization.Books.Exercises.Unit10
