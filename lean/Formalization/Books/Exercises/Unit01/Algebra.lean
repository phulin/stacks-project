import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Exercises, Chapter 1: Algebra

This file records the definitions and theorem interfaces from the numbered
exercises in `books/exercises.tex`.  The propositions are intentionally left
unproved at this stage.
-/

noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.ShortComplex
open IsLocalRing
open scoped TensorProduct

namespace Formalization.Books.Exercises.Unit01

/-! ## Localization and coherent rings -/

/-- The ideal `(m, p)` in a polynomial ring, written using Mathlib's ideal maps. -/
def shiftedPolynomialIdeal {A : Type*} [CommRing A] (m : Ideal A) (p : Polynomial A) :
    Ideal (Polynomial A) :=
  Ideal.map (Polynomial.C : A →+* Polynomial A) m ⊔ Ideal.span {p}

/-- The localization at the complement of a specified prime ideal. -/
abbrev localizationAtPrime {R : Type v} [CommRing R] (P : Ideal R) (hP : P.IsPrime) : Type v :=
  Localization (M := R) (@Ideal.primeCompl R _ P hP)

/-- The two localizations at `(m, X)` and `(m, X - 1)` are isomorphic. -/
theorem polynomial_shifted_localizations_equiv {A : Type v} [CommRing A]
    (m : Ideal A) [m.IsMaximal] :
    (shiftedPolynomialIdeal m Polynomial.X).IsMaximal ∧
      (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)).IsMaximal ∧
      ∃ (h₁ : (shiftedPolynomialIdeal m Polynomial.X).IsPrime)
        (h₂ : (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)).IsPrime),
        Nonempty
          (localizationAtPrime (shiftedPolynomialIdeal m Polynomial.X) h₁ ≃+*
            localizationAtPrime (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)) h₂) := by
  sorry

/-- A commutative ring is coherent when finitely generated ideals are finitely presented. -/
def IsCoherentRing (R : Type*) [CommRing R] : Prop :=
  ∀ I : Ideal R, I.FG → Module.FinitePresentation R I

/-- There is a coherent ring which is not Noetherian. -/
theorem exists_coherent_non_noetherian_ring :
    ∃ R : CommRingCat.{u}, IsCoherentRing R ∧ ¬ IsNoetherianRing R := by
  sorry

/-! ## Minimal numbers of generators and flat ideals -/

/-- In a Noetherian local ring, the span rank of a finite module is its residue-field dimension. -/
theorem minimal_generators_eq_residue_field_dimension
    {A M : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (⊤ : Submodule A M).spanFinrank =
      Module.finrank (A ⧸ IsLocalRing.maximalIdeal A)
        ((⊤ : Submodule A M) ⧸
          (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (⊤ : Submodule A M))) ∧
      (⊤ : Submodule A M).spanFinrank =
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField A ⊗[A] M) := by
  sorry

/-- Minimal generator counts multiply under tensor products over a local ring. -/
theorem minimal_generators_tensorProduct_mul
    {A M N : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] :
    (⊤ : Submodule A (M ⊗[A] N)).spanFinrank =
      (⊤ : Submodule A M).spanFinrank * (⊤ : Submodule A N).spanFinrank := by
  sorry

/-- A non-principal ideal has strictly fewer generators after squaring than the naive bound. -/
theorem ideal_square_spanFinrank_lt
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : 1 < I.spanFinrank) :
    (I ^ 2).spanFinrank < I.spanFinrank ^ 2 := by
  sorry

/-- If every ideal is flat, a Noetherian local ring is a PID or a field. -/
theorem flat_ideals_imply_pid_or_field
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hflat : ∀ I : Ideal A, Module.Flat A I) :
    IsField A ∨ (IsDomain A ∧ IsPrincipalIdealRing A) := by
  sorry

/-! ## Non-isomorphic polynomial rings -/

/-- Polynomial rings in successive positive finite numbers of variables are not isomorphic. -/
theorem mvPolynomial_fin_not_ringEquiv {k : Type*} [Field k] (n : ℕ) (hn : 1 ≤ n) :
    ¬ Nonempty (MvPolynomial (Fin n) k ≃+* MvPolynomial (Fin (n + 1)) k) := by
  sorry

/-- The six-variable quadratic used in the two quotient-ring exercises. -/
def sixVariableQuadratic (k : Type*) [CommSemiring k] : MvPolynomial (Fin 6) k :=
  MvPolynomial.X (0 : Fin 6) * MvPolynomial.X (1 : Fin 6) +
    MvPolynomial.X (2 : Fin 6) * MvPolynomial.X (3 : Fin 6) +
    MvPolynomial.X (4 : Fin 6) * MvPolynomial.X (5 : Fin 6)

/-- The six-variable quadratic quotient is not a polynomial ring in five variables. -/
theorem sixVariableQuadratic_quotient_not_mvPolynomial_five
    {k : Type*} [Field k] :
    ¬ Nonempty
      ((MvPolynomial (Fin 6) k ⧸ Ideal.span {sixVariableQuadratic k}) ≃+*
        MvPolynomial (Fin 5) k) := by
  sorry

/-- The same quotient is not a polynomial ring in six variables. -/
theorem sixVariableQuadratic_quotient_not_mvPolynomial_six
    {k : Type*} [Field k] :
    ¬ Nonempty
      ((MvPolynomial (Fin 6) k ⧸ Ideal.span {sixVariableQuadratic k}) ≃+*
        MvPolynomial (Fin 6) k) := by
  sorry

/-! ## Short exact sequences -/

/-- A short exact sequence becomes split after faithfully flat base change. -/
def SplitsAfterFaithfullyFlatBaseChange {A B : CommRingCat.{u}} (f : A ⟶ B)
    (S : ShortComplex (ModuleCat A)) : Prop :=
  RingHom.FaithfullyFlat f.hom ∧
    (S.map (ModuleCat.extendScalars f.hom)).ShortExact ∧
      Nonempty (S.map (ModuleCat.extendScalars f.hom)).Splitting

/-- There is a nonsplit short exact sequence of modules over the integers. -/
theorem exists_nonsplit_short_exact_sequence :
    ∃ S : ShortComplex (ModuleCat ℤ), S.ShortExact ∧ ¬ Nonempty S.Splitting := by
  sorry

/-- There is a nonsplit sequence whose tensor sequence splits after a faithfully flat extension. -/
theorem exists_nonsplit_sequence_split_after_faithfullyFlat_baseChange :
    ∃ (A B : CommRingCat.{u}) (f : A ⟶ B) (S : ShortComplex (ModuleCat A)),
      S.ShortExact ∧ ¬ Nonempty S.Splitting ∧ SplitsAfterFaithfullyFlatBaseChange f S := by
  sorry

/-! ## Kummer extensions -/

/-- A primitive `n`th root of unity forces the characteristic to be coprime to `n`. -/
theorem primitive_root_characteristic_coprime
    {k : Type*} [Field k] {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) :
    ringChar k = 0 ∨ Nat.Coprime (ringChar k) n := by
  sorry

/-- The standard Kummer irreducibility criterion gives a field quotient. -/
theorem kummer_polynomial_quotient_is_field
    {k : Type*} [Field k] {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) (a : k)
    (ha : ∀ d : ℕ, d ∣ n → d ≤ n → 1 < d → ¬ ∃ b : k, b ^ d = a) :
    IsField (Polynomial k ⧸ Ideal.span {Polynomial.X ^ n - Polynomial.C a}) := by
  sorry

/-! ## Integer-valued valuations on `k[x]` -/

/-- The valuation axioms used in the exercise, restricted to nonzero polynomials. -/
structure PolynomialValuation (k : Type*) [Field k] where
  toFun : {f : Polynomial k // f ≠ 0} → ℤ
  map_mul' : ∀ {f g : Polynomial k} (hf : f ≠ 0) (hg : g ≠ 0),
    toFun ⟨f * g, mul_ne_zero hf hg⟩ = toFun ⟨f, hf⟩ + toFun ⟨g, hg⟩
  map_add_min' : ∀ {f g : Polynomial k} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0),
    min (toFun ⟨f, hf⟩) (toFun ⟨g, hg⟩) ≤ toFun ⟨f + g, hfg⟩
  map_C' : ∀ {c : k} (hc : c ≠ 0),
    toFun ⟨Polynomial.C c, Polynomial.C_ne_zero.mpr hc⟩ = 0

instance {k : Type*} [Field k] : CoeFun (PolynomialValuation k)
    (fun _ => {f : Polynomial k // f ≠ 0} → ℤ) :=
  ⟨PolynomialValuation.toFun⟩

/-- Evaluation of a valuation at a polynomial together with its nonvanishing proof. -/
def PolynomialValuation.value {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0) : ℤ :=
  ν.toFun ⟨f, hf⟩

/-- The value of `X`, used in the termwise lower bound. -/
def PolynomialValuation.xValue {k : Type*} [Field k] (ν : PolynomialValuation k) : ℤ :=
  ν.value Polynomial.X Polynomial.X_ne_zero

/-- The set which is asserted to be a prime ideal when `ν(X) ≥ 0`. -/
def PolynomialValuation.positiveSet {k : Type*} [Field k] (ν : PolynomialValuation k) :
    Set (Polynomial k) :=
  {f | f = 0 ∨ ∃ hf : f ≠ 0, 0 < ν.value f hf}

/-- The values of the monomials occurring in a polynomial. -/
def PolynomialValuation.termValues {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) : Finset ℤ :=
  f.support.image (fun i : ℕ => (i : ℤ) * ν.xValue)

/-- The minimum of the term values of a nonzero polynomial. -/
def PolynomialValuation.termMinimum {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0) : ℤ :=
  (ν.termValues f).min' (by
    change (f.support.image (fun i : ℕ => (i : ℤ) * ν.xValue)).Nonempty
    exact (Polynomial.support_nonempty.mpr hf).image _)

/-- Unequal values cannot cancel in a sum. -/
theorem polynomial_valuation_add_of_unequal_values
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    {f g : Polynomial k} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hneq : ν.value f hf ≠ ν.value g hg) :
    ν.value (f + g) hfg = min (ν.value f hf) (ν.value g hg) := by
  sorry

/-- Every nonzero coefficient term gives a lower bound on the value of a polynomial. -/
theorem polynomial_valuation_lower_bound
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0) :
    ν.value f hf ≥ ν.termMinimum f hf := by
  sorry

/-- A unique lowest-valued term forces equality in the lower bound. -/
theorem polynomial_valuation_eq_lower_bound_of_unique_min
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0)
    (hmin : ∃ i ∈ f.support,
      (∀ j ∈ f.support, (i : ℤ) * ν.xValue ≤ (j : ℤ) * ν.xValue) ∧
        (∀ j ∈ f.support, (i : ℤ) * ν.xValue = (j : ℤ) * ν.xValue → j = i)) :
    ν.value f hf = ν.termMinimum f hf := by
  sorry

/-- If `ν(X) ≠ 0`, the term minimum is attained uniquely and equality holds. -/
theorem polynomial_valuation_eq_lower_bound_of_xValue_ne_zero
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    {f : Polynomial k} (hf : f ≠ 0) (hx : ν.xValue ≠ 0) :
    ν.value f hf = ν.termMinimum f hf := by
  sorry

/-- A valuation which takes a negative value is a negative multiple of degree. -/
theorem polynomial_valuation_negative_is_negative_degree
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    (hneg : ∃ (f : Polynomial k) (hf : f ≠ 0), ν.value f hf < 0) :
    ∃ n : ℕ, 0 < n ∧
      ∀ (f : Polynomial k) (hf : f ≠ 0),
        ν.value f hf = -(n : ℤ) * (f.natDegree : ℤ) := by
  sorry

/-- For nonnegative `ν(X)`, the positive-value set is a prime ideal. -/
theorem polynomial_valuation_positiveSet_is_prime
    {k : Type*} [Field k] (ν : PolynomialValuation k) (hx : 0 ≤ ν.xValue) :
    ∃ I : Ideal (Polynomial k),
      (I : Set (Polynomial k)) = ν.positiveSet ∧ I.IsPrime := by
  sorry

/-- All such valuations are either trivial, degree valuations, or orders at an irreducible. -/
theorem polynomial_valuation_classification
    {k : Type*} [Field k] (ν : PolynomialValuation k) :
    (∀ (f : Polynomial k) (hf : f ≠ 0), ν.value f hf = 0) ∨
      (∃ n : ℕ, 0 < n ∧
        ∀ (f : Polynomial k) (hf : f ≠ 0),
          ν.value f hf = -(n : ℤ) * (f.natDegree : ℤ)) ∨
      (∃ (p : Polynomial k) (n : ℕ), Irreducible p ∧ 0 < n ∧
        ∀ (f : Polynomial k) (hf : f ≠ 0),
          ν.value f hf = (n : ℤ) * (multiplicity p f : ℤ)) := by
  sorry

/-! ## Idempotents and products -/

/-- The canonical idempotent elements `0` and `1`. -/
theorem zero_one_are_idempotent {A : Type*} [MonoidWithZero A] :
    IsIdempotentElem (0 : A) ∧ IsIdempotentElem (1 : A) := by
  exact ⟨IsIdempotentElem.zero, IsIdempotentElem.one⟩

/-- The corrected nontrivial-idempotent predicate needed for a product decomposition. -/
def IsNontrivialIdempotent {A : Type*} [MonoidWithZero A] (e : A) : Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1

/-- The pairwise notion of orthogonality is Mathlib's `OrthogonalIdempotents` on `Fin 2`. -/
theorem orthogonal_idempotents_pair_iff {A : Type*} [CommRing A] (e e' : A) :
    OrthogonalIdempotents ![e, e'] ↔
      IsIdempotentElem e ∧ IsIdempotentElem e' ∧ e * e' = 0 := by
  sorry

/-- A commutative ring is a product of two nonzero rings. -/
def IsProductOfTwoNonzeroRings (A : CommRingCat.{u}) : Prop :=
  ∃ B C : CommRingCat.{u}, Nontrivial B ∧ Nontrivial C ∧ Nonempty (A ≃+* (B × C))

/-- A product decomposition is equivalent to a nontrivial idempotent. -/
theorem product_ring_iff_nontrivial_idempotent (A : CommRingCat.{u}) :
    IsProductOfTwoNonzeroRings A ↔ ∃ e : A, IsNontrivialIdempotent e := by
  sorry

/-! ## Lifting idempotents -/

/-- The quotient map on the subtypes of idempotents. -/
def quotientIdempotentMap {A : Type*} [CommRing A] (I : Ideal A) :
    {e : A // IsIdempotentElem e} → {e : A ⧸ I // IsIdempotentElem e} :=
  fun e => ⟨Ideal.Quotient.mk I e.1, e.2.map (Ideal.Quotient.mk I)⟩

/-- Locally nilpotent ideals do not change the set of idempotents. -/
theorem quotient_idempotent_map_bijective {A : Type*} [CommRing A] (I : Ideal A)
    (hI : ∀ x ∈ I, IsNilpotent x) :
    Function.Bijective (quotientIdempotentMap I) := by
  sorry

end Formalization.Books.Exercises.Unit01
