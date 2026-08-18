import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Exercises, Chapter 10: products of incomparable primes

The first result in this file is the general intersection statement.  The
second part records a concrete polynomial example where passing from an
intersection to a product creates an additional associated prime.
-/

noncomputable section

universe u

namespace Formalization.Books.Exercises.Unit10

/-! ## Intersections of incomparable primes -/

/-- The quotient by the intersection of two ideals.  The lattice meet is the
ideal-theoretic intersection. -/
abbrev intersectionPrimeQuotient {R : Type*} [CommRing R]
    (p q : Ideal R) := R ⧸ (p ⊓ q)

/-- In a Noetherian ring, incomparable prime ideals are exactly the associated
primes of the quotient by their intersection. -/
theorem associated_primes_intersection_prime_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) (hp : p.IsPrime) (hq : q.IsPrime)
    (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) :
    associatedPrimes R (intersectionPrimeQuotient p q) =
      ({p, q} : Set (Ideal R)) := by
  let s : Ideal R := p ⊓ q
  have hp_ass : associatedPrimes R (R ⧸ p) = ({p} : Set (Ideal R)) := by
    simpa [hp.radical] using
      (associatedPrimes.eq_singleton_of_isPrimary hp.isPrimary)
  have hq_ass : associatedPrimes R (R ⧸ q) = ({q} : Set (Ideal R)) := by
    simpa [hq.radical] using
      (associatedPrimes.eq_singleton_of_isPrimary hq.isPrimary)
  let f₁ : (R ⧸ s) →ₗ[R] (R ⧸ p) :=
    Submodule.mapQ (s : Submodule R R) (p : Submodule R R) LinearMap.id inf_le_left
  let f₂ : (R ⧸ s) →ₗ[R] (R ⧸ q) :=
    Submodule.mapQ (s : Submodule R R) (q : Submodule R R) LinearMap.id inf_le_right
  let f : (R ⧸ s) →ₗ[R] (R ⧸ p) × (R ⧸ q) := LinearMap.prod f₁ f₂
  have hf_injective : Function.Injective f := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := s.mkQ_surjective x
    obtain ⟨y, rfl⟩ := s.mkQ_surjective y
    change (p.mkQ x, q.mkQ x) = (p.mkQ y, q.mkQ y) at hxy
    apply (Submodule.Quotient.eq s).mpr
    exact ⟨(Submodule.Quotient.eq p).mp (congrArg Prod.fst hxy),
      (Submodule.Quotient.eq q).mp (congrArg Prod.snd hxy)⟩
  have hupper : associatedPrimes R (R ⧸ s) ⊆ ({p, q} : Set (Ideal R)) := by
    intro P hP
    have hP' : P ∈ associatedPrimes R ((R ⧸ p) × (R ⧸ q)) :=
      associatedPrimes.subset_of_injective hf_injective hP
    rw [associatedPrimes.prod, hp_ass, hq_ass] at hP'
    simpa only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff] using hP'
  have hqnot : ∃ a, a ∈ q ∧ a ∉ p := by
    by_contra h
    apply hqp
    intro x hx
    by_contra hxp
    exact h ⟨x, hx, hxp⟩
  obtain ⟨a, haq, hanp⟩ := hqnot
  have hpa : (p : Submodule R R) ≤
      Submodule.comap (LinearMap.lsmul R R a) (s : Submodule R R) := by
    intro x hx
    change a * x ∈ s
    exact ⟨p.mul_mem_left a hx, by simpa [mul_comm] using q.mul_mem_right x haq⟩
  have hcomap_a : Submodule.comap (LinearMap.lsmul R R a) (s : Submodule R R) = p := by
    ext x
    constructor
    · intro hx
      change a * x ∈ s at hx
      exact (hp.mem_or_mem hx.1).resolve_left hanp
    · exact fun hx => hpa hx
  let fa : (R ⧸ p) →ₗ[R] (R ⧸ s) :=
    Submodule.mapQ (p : Submodule R R) (s : Submodule R R)
      (LinearMap.lsmul R R a) hpa
  have hfa_injective : Function.Injective fa := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, hcomap_a, Submodule.mkQ_map_self]
  have hpnot : ∃ b, b ∈ p ∧ b ∉ q := by
    by_contra h
    apply hpq
    intro x hx
    by_contra hxq
    exact h ⟨x, hx, hxq⟩
  obtain ⟨b, hbp, hbnq⟩ := hpnot
  have hqb : (q : Submodule R R) ≤
      Submodule.comap (LinearMap.lsmul R R b) (s : Submodule R R) := by
    intro x hx
    change b * x ∈ s
    exact ⟨by simpa [mul_comm] using p.mul_mem_right x hbp, q.mul_mem_left b hx⟩
  have hcomap_b : Submodule.comap (LinearMap.lsmul R R b) (s : Submodule R R) = q := by
    ext x
    constructor
    · intro hx
      change b * x ∈ s at hx
      exact (hq.mem_or_mem hx.2).resolve_left hbnq
    · exact fun hx => hqb hx
  let fb : (R ⧸ q) →ₗ[R] (R ⧸ s) :=
    Submodule.mapQ (q : Submodule R R) (s : Submodule R R)
      (LinearMap.lsmul R R b) hqb
  have hfb_injective : Function.Injective fb := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, hcomap_b, Submodule.mkQ_map_self]
  have hp_mem : p ∈ associatedPrimes R (R ⧸ s) := by
    have hp_mem' : p ∈ associatedPrimes R (R ⧸ p) := by
      rw [hp_ass]
      simp
    exact associatedPrimes.subset_of_injective hfa_injective hp_mem'
  have hq_mem : q ∈ associatedPrimes R (R ⧸ s) := by
    have hq_mem' : q ∈ associatedPrimes R (R ⧸ q) := by
      rw [hq_ass]
      simp
    exact associatedPrimes.subset_of_injective hfb_injective hq_mem'
  apply Set.Subset.antisymm hupper
  simpa only [Set.insert_subset_iff, Set.singleton_subset_iff] using
    And.intro hp_mem hq_mem

/-! ## The product example in `k[x,y,z]` -/

/-- The three-variable polynomial ring used in the example. -/
abbrev productExamplePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 3) k

/-- The coordinate variables. -/
def productExampleX (k : Type u) [Field k] : productExamplePolynomialRing k :=
  MvPolynomial.X (0 : Fin 3)

def productExampleY (k : Type u) [Field k] : productExamplePolynomialRing k :=
  MvPolynomial.X (1 : Fin 3)

def productExampleZ (k : Type u) [Field k] : productExamplePolynomialRing k :=
  MvPolynomial.X (2 : Fin 3)

/-- The incomparable primes `p=(x,y)` and `q=(x,z)`. -/
def productExamplePrimeP (k : Type u) [Field k] :
    Ideal (productExamplePolynomialRing k) :=
  Ideal.span ({productExampleX k, productExampleY k} :
    Set (productExamplePolynomialRing k))

def productExamplePrimeQ (k : Type u) [Field k] :
    Ideal (productExamplePolynomialRing k) :=
  Ideal.span ({productExampleX k, productExampleZ k} :
    Set (productExamplePolynomialRing k))

/-- The product quotient `R/(p q)`. -/
abbrev productExampleQuotient (k : Type u) [Field k] :=
  productExamplePolynomialRing k ⧸
    (productExamplePrimeP k * productExamplePrimeQ k)

/-- The maximal ideal `m=(x,y,z)` which becomes an associated prime of the
product quotient. -/
def productExampleMaximalIdeal (k : Type u) [Field k] :
    Ideal (productExamplePolynomialRing k) :=
  Ideal.span ({productExampleX k, productExampleY k, productExampleZ k} :
    Set (productExamplePolynomialRing k))

/-- The displayed polynomial ring is Noetherian. -/
theorem product_example_ring_is_noetherian (k : Type u) [Field k] :
    IsNoetherianRing (productExamplePolynomialRing k) := by
  infer_instance

private theorem product_example_span_first_succ_prime (k : Type u) [Field k]
    (j : Fin 2) :
    (Ideal.span ({MvPolynomial.X (0 : Fin 3),
      MvPolynomial.X j.succ} : Set (MvPolynomial (Fin 3) k))).IsPrime := by
  let A := MvPolynomial (Fin 3) k
  let B := Polynomial (MvPolynomial (Fin 2) k)
  let C := MvPolynomial (Fin 2) k
  let I : Ideal A := Ideal.span
    ({MvPolynomial.X (0 : Fin 3), MvPolynomial.X j.succ} : Set A)
  let J : Ideal B := Ideal.span
    ({Polynomial.C (MvPolynomial.X j), Polynomial.X} : Set B)
  let K : Ideal C := Ideal.span ({MvPolynomial.X j} : Set C)
  let e := MvPolynomial.finSuccEquiv k 2
  have hmap : Ideal.map (e : A →+* B) I = J := by
    simp only [I, J]
    rw [Ideal.map_span]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, (rfl | rfl), rfl⟩
      · right
        simpa [e] using
          (MvPolynomial.finSuccEquiv_X_zero (R := k) (n := 2))
      · left
        simpa [e] using
          (MvPolynomial.finSuccEquiv_X_succ (R := k) (n := 2) (j := j))
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨_, Or.inr rfl,
          (MvPolynomial.finSuccEquiv_X_succ (R := k) (n := 2) (j := j))⟩
      · exact ⟨_, Or.inl rfl,
          (MvPolynomial.finSuccEquiv_X_zero (R := k) (n := 2))⟩
  have hJ : J = Ideal.span
      ({Polynomial.C (MvPolynomial.X j),
        Polynomial.X - Polynomial.C (0 : C)} : Set B) := by
    simp [J]
  have hKprime : K.IsPrime := by
    exact Ideal.isPrime_span_singleton_of_prime
      (MvPolynomial.X_prime : Prime (MvPolynomial.X j))
  let ep : (B ⧸ J) ≃ₐ[k] (C ⧸ K) :=
    hJ ▸ ((Polynomial.quotientSpanCXSubCAlgEquiv (MvPolynomial.X j) 0).restrictScalars k)
  let es : (A ⧸ I) ≃ₐ[k] (B ⧸ J) :=
    Ideal.quotientEquivAlg I J e hmap.symm
  letI : IsDomain (C ⧸ K) :=
    (Ideal.Quotient.isDomain_iff_prime K).mpr hKprime
  letI : IsDomain (A ⧸ I) :=
    (es.toRingEquiv.trans ep.toRingEquiv).toMulEquiv.isDomain (C ⧸ K)
  exact (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance

/-- The two displayed ideals are incomparable prime ideals. -/
theorem product_example_primes_incomparable (k : Type u) [Field k] :
    (productExamplePrimeP k).IsPrime ∧
      (productExamplePrimeQ k).IsPrime ∧
      ¬ productExamplePrimeP k ≤ productExamplePrimeQ k ∧
      ¬ productExamplePrimeQ k ≤ productExamplePrimeP k := by
  have hP : (productExamplePrimeP k).IsPrime := by
    simpa [productExamplePrimeP, productExampleX, productExampleY] using
      (product_example_span_first_succ_prime k (0 : Fin 2))
  have hQ : (productExamplePrimeQ k).IsPrime := by
    simpa [productExamplePrimeQ, productExampleX, productExampleZ] using
      (product_example_span_first_succ_prime k (1 : Fin 2))
  have hQset : productExamplePrimeQ k =
      Ideal.span (MvPolynomial.X '' ({0, 2} : Set (Fin 3))) := by
    rw [productExamplePrimeQ]
    change Ideal.span ({MvPolynomial.X (0 : Fin 3), MvPolynomial.X (2 : Fin 3)} :
      Set (MvPolynomial (Fin 3) k)) = _
    congr 1
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨2, by simp, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
  have hPset : productExamplePrimeP k =
      Ideal.span (MvPolynomial.X '' ({0, 1} : Set (Fin 3))) := by
    rw [productExamplePrimeP]
    change Ideal.span ({MvPolynomial.X (0 : Fin 3), MvPolynomial.X (1 : Fin 3)} :
      Set (MvPolynomial (Fin 3) k)) = _
    congr 1
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
  have hY_not_Q : productExampleY k ∉ productExamplePrimeQ k := by
    rw [hQset, MvPolynomial.mem_ideal_span_X_image]
    intro h
    obtain ⟨i, hi, hmi⟩ := h (Finsupp.single (1 : Fin 3) 1) (by
      simp [productExampleY])
    rcases hi with rfl | rfl <;> simp at hmi
  have hZ_not_P : productExampleZ k ∉ productExamplePrimeP k := by
    rw [hPset, MvPolynomial.mem_ideal_span_X_image]
    intro h
    obtain ⟨i, hi, hmi⟩ := h (Finsupp.single (2 : Fin 3) 1) (by
      simp [productExampleZ])
    rcases hi with rfl | rfl <;> simp at hmi
  refine ⟨hP, hQ, ?_, ?_⟩
  · intro h
    exact hY_not_Q (h (Ideal.subset_span (by simp)))
  · intro h
    exact hZ_not_P (h (Ideal.subset_span (by simp)))

/-- The maximal ideal is an associated prime of `R/(p q)` and is distinct from
both factors. -/
theorem product_example_has_extra_associated_prime (k : Type u) [Field k] :
    productExampleMaximalIdeal k ∈
        associatedPrimes (productExamplePolynomialRing k)
          (productExampleQuotient k) ∧
      productExampleMaximalIdeal k ≠ productExamplePrimeP k ∧
      productExampleMaximalIdeal k ≠ productExamplePrimeQ k := by
  let m : Ideal (productExamplePolynomialRing k) := productExampleMaximalIdeal k
  have hMset : m =
      Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 3))) := by
    dsimp [m, productExampleMaximalIdeal]
    congr 1
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Set.mem_univ,
      true_and]
    constructor
    · rintro (rfl | rfl | rfl) <;>
        simp [productExampleX, productExampleY, productExampleZ]
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [productExampleX, productExampleY, productExampleZ]
  let f : productExamplePolynomialRing k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : Fin 3 => 0)
  have hml : m ≤ Ideal.comap f (⊥ : Ideal k) := by
    rw [hMset]
    apply Ideal.span_le.2
    rintro t ⟨i, -, rfl⟩
    simp [f]
  have hker : Ideal.comap f (⊥ : Ideal k) = m := by
    apply le_antisymm
    · intro a ha
      rw [hMset, MvPolynomial.mem_ideal_span_X_image]
      intro d hd
      by_cases hd0 : d = 0
      · subst d
        exfalso
        have hne : a.coeff 0 ≠ 0 := MvPolynomial.mem_support_iff.mp hd
        exact hne (by simpa [f, MvPolynomial.constantCoeff_eq] using ha)
      · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
        exact ⟨i, Set.mem_univ _, Finsupp.mem_support_iff.mp hi⟩
    · exact hml
  have hmprime : m.IsPrime := by
    rw [← hker]
    infer_instance
  have hPm : productExamplePrimeP k ≤ m := by
    rw [productExamplePrimeP, hMset]
    apply Ideal.span_le.2
    rintro t (rfl | rfl) <;>
      exact Ideal.subset_span (by simp [productExampleX, productExampleY])
  have hQm : productExamplePrimeQ k ≤ m := by
    rw [productExamplePrimeQ, hMset]
    apply Ideal.span_le.2
    rintro t (rfl | rfl) <;>
      exact Ideal.subset_span (by simp [productExampleX, productExampleZ])
  have hPQm2 : productExamplePrimeP k * productExamplePrimeQ k ≤ m ^ 2 := by
    simpa [pow_two] using Ideal.mul_mono hPm hQm
  have hxP : productExampleX k ∈ productExamplePrimeP k := by
    rw [productExamplePrimeP]
    exact Ideal.subset_span (by simp [productExampleX])
  have hyP : productExampleY k ∈ productExamplePrimeP k := by
    rw [productExamplePrimeP]
    exact Ideal.subset_span (by simp [productExampleY])
  have hxQ : productExampleX k ∈ productExamplePrimeQ k := by
    rw [productExamplePrimeQ]
    exact Ideal.subset_span (by simp [productExampleX])
  have hzQ : productExampleZ k ∈ productExamplePrimeQ k := by
    rw [productExamplePrimeQ]
    exact Ideal.subset_span (by simp [productExampleZ])
  have hmx : m ≤
      Submodule.comap (LinearMap.lsmul (productExamplePolynomialRing k)
        (productExamplePolynomialRing k) (productExampleX k))
        (productExamplePrimeP k * productExamplePrimeQ k : Submodule
          (productExamplePolynomialRing k) (productExamplePolynomialRing k)) := by
    rw [hMset]
    apply Ideal.span_le.2
    rintro t ⟨i, -, rfl⟩
    fin_cases i
    · change productExampleX k * productExampleX k ∈
        productExamplePrimeP k * productExamplePrimeQ k
      exact Ideal.mul_mem_mul hxP hxQ
    · change productExampleX k * productExampleY k ∈
        productExamplePrimeP k * productExamplePrimeQ k
      simpa [mul_comm] using Ideal.mul_mem_mul hyP hxQ
    · change productExampleX k * productExampleZ k ∈
        productExamplePrimeP k * productExamplePrimeQ k
      exact Ideal.mul_mem_mul hxP hzQ
  have hmvars : m = MvPolynomial.idealOfVars (Fin 3) k := by
    simpa [MvPolynomial.idealOfVars, Set.image_univ] using hMset
  have hcomap :
      Submodule.comap (LinearMap.lsmul (productExamplePolynomialRing k)
        (productExamplePolynomialRing k) (productExampleX k))
        (productExamplePrimeP k * productExamplePrimeQ k : Submodule
          (productExamplePolynomialRing k) (productExamplePolynomialRing k)) = m := by
    apply le_antisymm
    · intro a ha
      change productExampleX k * a ∈
        productExamplePrimeP k * productExamplePrimeQ k at ha
      have ha2 : productExampleX k * a ∈ m ^ 2 := hPQm2 ha
      have ha2' : productExampleX k * a ∈
          MvPolynomial.idealOfVars (Fin 3) k ^ 2 := by
        simpa [hmvars] using ha2
      have hcoeff := (MvPolynomial.mem_pow_idealOfVars_iff' 2
        (productExampleX k * a)).mp ha2'
        (Finsupp.single (0 : Fin 3) 1) (by simp)
      have hconst : a.coeff 0 = 0 := by
        have hcoeff' : (productExampleX k * a).coeff
            (Finsupp.single (0 : Fin 3) 1) = 0 := hcoeff
        calc
          a.coeff 0 = (productExampleX k * a).coeff
              (Finsupp.single (0 : Fin 3) 1) := by
                simpa [productExampleX] using
                  (MvPolynomial.coeff_X_mul (R := k)
                    (0 : Fin 3 →₀ ℕ) (0 : Fin 3) a).symm
          _ = 0 := hcoeff'
      rw [hMset, MvPolynomial.mem_ideal_span_X_image]
      intro d hd
      by_cases hd0 : d = 0
      · subst d
        exfalso
        have hne : a.coeff 0 ≠ 0 := MvPolynomial.mem_support_iff.mp hd
        exact hne hconst
      · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
        exact ⟨i, Set.mem_univ _, Finsupp.mem_support_iff.mp hi⟩
    · exact hmx
  let fa : (productExamplePolynomialRing k ⧸ m) →ₗ[productExamplePolynomialRing k]
      (productExamplePolynomialRing k ⧸
        (productExamplePrimeP k * productExamplePrimeQ k)) :=
    Submodule.mapQ (m : Submodule (productExamplePolynomialRing k)
      (productExamplePolynomialRing k))
      (productExamplePrimeP k * productExamplePrimeQ k :
        Submodule (productExamplePolynomialRing k) (productExamplePolynomialRing k))
      (LinearMap.lsmul (productExamplePolynomialRing k)
        (productExamplePolynomialRing k) (productExampleX k)) hmx
  have hfa_injective : Function.Injective fa := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  have hass : m ∈ associatedPrimes (productExamplePolynomialRing k)
      (productExamplePolynomialRing k ⧸
        (productExamplePrimeP k * productExamplePrimeQ k)) := by
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff_exists_injective_linearMap]
    exact ⟨hmprime, fa, hfa_injective⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [m, productExampleQuotient] using hass
  · intro h
    apply (product_example_primes_incomparable k).2.2.2
    rw [← h]
    exact hQm
  · intro h
    apply (product_example_primes_incomparable k).2.2.1
    rw [← h]
    exact hPm

end Formalization.Books.Exercises.Unit10
